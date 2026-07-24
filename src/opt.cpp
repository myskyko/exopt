#include <map>
#include <algorithm>
#include <fstream>

#include <cassert>

#include "opt.hpp"
#include "cut.hpp"
#include "sim.hpp"
#include "synth.hpp"
#include "ioutil.hpp"
#include "rel.hpp"

using namespace std;

OptMan::OptMan(aigman &aig, int cutsize, int windowsize, bool fAllDiv, int seed, bool fVerbose, int *nProblems): aig(aig), cutsize(cutsize), windowsize(windowsize), fAllDiv(fAllDiv), fVerbose(fVerbose), nProblems(nProblems) {
  // cut enumeration
  vector<vector<Cut> > cuts;
  CutEnumeration(aig, cuts, cutsize);
  //PrintVecWithIndex(cuts);
  // cut leaves to gates
  map<vector<int>, vector<int> > m;
  for(int i = 0; i < aig.nObjs; i++) {
    for(auto const &cut: cuts[i]) {
      if(cut.leaves.size() != 1) {
        m[cut.leaves].push_back(i);
      }
    }
  }
  for(auto it = m.begin(); it != m.end(); it++) {
    for(auto it2 = m.begin(); it2 != m.end(); it2++) {
      if(it == it2) {
        continue;
      }
      if(includes(it->first.begin(), it->first.end(), it2->first.begin(), it2->first.end())) {
        vector<int> dest(it->second.size() + it2->second.size());
        auto it3 = set_union(it->second.begin(), it->second.end(), it2->second.begin(), it2->second.end(), dest.begin());
        dest.resize(it3 - dest.begin());
        it->second = dest;
      }
    }
  }
  // windows
  for(auto it = m.begin(); it != m.end(); it++) {
    if((int)it->second.size() > windowsize || aig.reach(it->second, it->first)) {
      if(!fAllDiv) {
        vLarge.push_back(*it);
      }
      continue;
    }
    vector<unsigned> v(aig.nObjs);
    for(int i: it->second) {
      for(int ii = i + i; ii <= i + i + 1; ii++) {
        v[aig.vObjs[ii] >> 1]++;
      }
    }
    vector<int> outputs;
    for(auto it2 = it->second.begin(); it2 != it->second.end(); it2++) {
      if(aig.vvFanouts[*it2].size() != v[*it2]) {
        outputs.push_back(*it2);
      }
    }
    vWindows.push_back(make_tuple(it->first, it->second, outputs));
  }
  if(fAllDiv) {
    vector<int> inputs;
    for(int i = 0; i < aig.nPis; i++) {
      inputs.push_back(i + 1);
    }
    vector<int> gates;
    for(int i = aig.nPis + 1; i < aig.nObjs; i++) {
      gates.push_back(i);
    }
    vLarge.push_back(make_pair(inputs, gates));
  } else {
    RemoveIncluded(vLarge);
  }
  rg.seed(seed);
}

void OptMan::Randomize() {
  shuffle(vWindows.begin(), vWindows.end(), rg);
  if(!fAllDiv) {
    shuffle(vLarge.begin(), vLarge.end(), rg);
  }
}

bool OptMan::Synthesize(SynthMan<KissatSolver> &synthman, int nGates, vector<int> const & inputs, vector<int> const & outputs, string prefix) {
  if(fVerbose) {
    cout << prefix << "Synthesizing with less than " << nGates << " gates" << endl;
  }
  aigman *aig2;
#ifdef DEBUG
  aig2 = synthman.Synth(nGates);
  assert(aig2);
  delete aig2;
#endif
  if((aig2 = synthman.ExSynth(nGates))) {
    if(fVerbose) {
      cout << prefix << "Synthesized with " << aig2->nGates << " gates" << endl;
    }
    vector<int> outputs_shift;
    for(int i: outputs) {
      outputs_shift.push_back(i << 1);
    }
    int nGatesAll = aig.nGates;
    aig.insert(aig2, inputs, outputs_shift);
    if(fVerbose) {
      cout << prefix << "Replaced gates : ";
      string delim;
      for(int i = 0; i < aig.nObjs; i++) {
        if(aig.vDeads[i]) {
          cout << delim << i;
          delim = ", ";
        }
      }
      cout << endl;
    }
    assert(nGatesAll - aig.nGates >= nGates - aig2->nGates);
    delete aig2;
    aig.renumber();
    return true;
  }
  if(fVerbose) {
    cout << prefix << "* Synthesis failed" << endl;
  }
  return false;
}

template <typename T>
void OptMan::RemoveIncluded(T &s) {
  for(auto it = s.begin(); it != s.end();) {
    bool fIncluded = false;
    for(auto it2 = s.begin(); it2 != s.end(); it2++){
      if(it == it2) {
        continue;
      }
      if(includes(get<1>(*it2).begin(), get<1>(*it2).end(), get<1>(*it).begin(), get<1>(*it).end())) {
        fIncluded = true;
        break;
      }
    }
    if(fIncluded) {
      it = s.erase(it);
    } else {
      it++;
    }
  }
}

template <typename T>
void OptMan::RemoveIncluded(T &s, bool fNoNewFo) {
  for(auto it = s.begin(); it != s.end();) {
    bool fIncluded = false;
    for(auto it2 = s.begin(); it2 != s.end(); it2++){
      if(it == it2) {
        continue;
      }
      if(includes(get<1>(*it2).begin(), get<1>(*it2).end(), get<1>(*it).begin(), get<1>(*it).end())) {
        fIncluded = true;
        if(fNoNewFo) {
          for(int i: get<2>(*it2)) {
            if(!aig.reach(get<2>(*it), vector<int>{i})) {
              fIncluded = false;
              break;
            }
          }
        }
        break;
      }
    }
    if(fIncluded) {
      it = s.erase(it);
    } else {
      it++;
    }
  }
}

bool OptMan::OptWindows() {
  auto vWindows_ = vWindows;
  RemoveIncluded(vWindows_);
  for(auto const &p: vWindows_) {
    auto const &inputs = get<0>(p);
    auto const &gates = get<1>(p);
    auto const &outputs = get<2>(p);
    int nGates = gates.size();
    if(fVerbose) {
      cout << "Inputs : " << inputs << endl;
      cout << "Gates : " << gates << endl;
      cout << "Outputs : " << outputs << endl;
    }
    // get relation
    vector<vector<bool> > br;
    GetBooleanRelation(aig, inputs, outputs, br);
    //PrintVecWithIndex(br);
    if(nProblems) {
      string fname = "case" + to_string((*nProblems)++) + ".rel";
      WriteBooleanRelation(fname, br, NULL);
      ofstream f("list.txt", ios_base::app);
      f << fname << " " << nGates - 1 << endl;
    }
    // synthesis
    SynthMan<KissatSolver> synthman(br);
    if(Synthesize(synthman, nGates, inputs, outputs)) {
      return true;
    }
  }
  return false;
}

bool OptMan::OptLarge() {
  for(auto const &p: vLarge) {
    auto const &inputs = get<0>(p);
    auto const &gates = get<1>(p);
    int nGates = gates.size();
    if(fVerbose) {
      cout << "Inputs : " << inputs << endl;
      cout << "Gates : " << gates << endl;
    }
    // for each window
    vector<tuple<vector<int>, vector<int>, vector<int> > > vWindows_;
    for(auto const&q: vWindows) {
      auto const &gates2 = get<1>(q);
      auto const &outputs2 = get<2>(q);
      if(!includes(gates.begin(), gates.end(), gates2.begin(), gates2.end()) || aig.reach(outputs2, inputs)) {
        continue;
      }
      vWindows_.push_back(q);
    }
    RemoveIncluded(vWindows_, true);
    for(auto const&q: vWindows_) {
      auto const &inputs2 = get<0>(q);
      auto const &gates2 = get<1>(q);
      auto const &outputs2 = get<2>(q);
      int nGates2 = gates2.size();
      if(fVerbose) {
        cout << "\t\tInputs : " << inputs2 << endl;
        cout << "\t\tGates : " <<  gates2 << endl;
        cout << "\t\tOutputs : " <<  outputs2 << endl;
      }
      vector<int> v(nGates);
      v.resize(set_difference(gates.begin(), gates.end(), gates2.begin(), gates2.end(), v.begin()) - v.begin());
      vector<int> extra;
      for(auto it = v.begin(); it != v.end(); it++) {
        if(!aig.reach(outputs2, vector<int>{*it})) {
          extra.push_back(*it);
        }
      }
      if(fVerbose) {
        cout << "\t\tOutside gates : " << v << endl;
        cout << "\t\tExtra inputs : " << extra << endl;
      }
      vector<vector<bool> > br;
      GetBooleanRelation(aig, inputs, outputs2, br);
      //PrintVecWithIndex(br, "\t\t");
      vector<vector<bool> > sim;
      GetSim(aig, inputs, extra, sim);
      //PrintVecWithIndex(sim, "\t\t");
      if(nProblems) {
        string fname = "case" + to_string((*nProblems)++) + ".rel";
        WriteBooleanRelation(fname, br, &sim);
        ofstream f("list.txt", ios_base::app);
        f << fname << " " << nGates2 - 1 << endl;
      }
      // synthesis
      SynthMan<KissatSolver> synthman(br, &sim);
      extra.insert(extra.begin(), inputs.begin(), inputs.end());
      if(Synthesize(synthman, nGates2, extra, outputs2, "\t\t")) {
        return true;
      }
    }
  }
  return false;
}
