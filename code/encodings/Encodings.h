/*!
 * \author Ruben Martins - ruben@sat.inesc-id.pt
 *
 * @section LICENSE
 *
 * Open-WBO, Copyright (c) 2013-2017, Ruben Martins, Vasco Manquinho, Ines Lynce
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 *
 */

#ifndef Encodings_h
#define Encodings_h

#ifdef SIMP
#include "simp/SimpSolver.h"
#else
#include "core/Solver.h"
#endif

#include "../MaxTypes.h"
#include "core/SolverTypes.h"
#include <map>
#include <math.h>

using NSPACE::Lit;
using NSPACE::Solver;
using NSPACE::lit_Error;
using NSPACE::lit_Undef;
using NSPACE::mkLit;
using NSPACE::vec;

namespace openwbo {

struct less_than_map {
  inline bool operator()(const uint64_t &key1, const uint64_t &key2) const {
    return (key1 < key2);
  }
};

typedef std::map<uint64_t, Lit, less_than_map> wlit_mapt;

//=================================================================================================
class Encodings {

public:
  Encodings() { hasEncoding = countingOnlyMode = false; countedClss = 0; limitOnCountClss = INT_MAX; }
  ~Encodings() {}

  void implication(uint64_t, uint64_t);
  void implication(uint64_t, uint64_t, uint64_t);

  // Auxiliary methods for creating clauses
  //
  // Add a unit clause to a SAT solver
  void addUnitClause(Solver *S, Lit a, Lit blocking = lit_Undef);
  // Add a binary clause to a SAT solver
  void addBinaryClause(Solver *S, Lit a, Lit b, Lit blocking = lit_Undef);
  // Add a ternary clause to a SAT solver
  void addTernaryClause(Solver *S, Lit a, Lit b, Lit c,
                        Lit blocking = lit_Undef);
  // Add a quaternary clause to a SAT solver
  void addQuaternaryClause(Solver *S, Lit a, Lit b, Lit c, Lit d,
                           Lit blocking = lit_Undef);
  // Add an arbitrary clause to the SAT solver
  void addClause(Solver *S, const vec<Lit>& cls);

  // Creates a new variable in the SAT solver
  void newSATVariable(Solver *S) {
#ifdef SIMP
    ((NSPACE::SimpSolver *)S)->newVar();
#else
	if (countingOnlyMode) return;
    S->newVar();
#endif
  }

protected:
  vec<Lit> clause; // Temporary clause to be used while building the encodings.
  bool hasEncoding;
  
  bool countingOnlyMode;
  int countedClss;
  int limitOnCountClss;
  void StartCountingOnlyMode(int maxVal) { limitOnCountClss = maxVal; countingOnlyMode = true; countedClss = 0; }
  int StopCountingOnlyMode() { hasEncoding = countingOnlyMode = false; return countedClss; }
  bool CountedClssMaxExceeded() const { return countingOnlyMode && countedClss > limitOnCountClss; }
};
} // namespace openwbo

#endif
