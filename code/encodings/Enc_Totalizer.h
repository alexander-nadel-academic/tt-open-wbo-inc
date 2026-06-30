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

#ifndef Enc_Totalizer_h
#define Enc_Totalizer_h

#ifdef SIMP
#include "simp/SimpSolver.h"
#else
#include "core/Solver.h"
#endif

#include "Encodings.h"
#include "core/SolverTypes.h"
#include "../Torc.h"

#include <vector>

using namespace std;

namespace openwbo {

class Totalizer : public Encodings {

public:
  Totalizer(int strategy = _INCREMENTAL_NONE_) : lySolver(nullptr), lyLayersNum(0) {
    blocking = lit_Undef;
    hasEncoding = false;
    joinMode = false;
    current_cardinality_rhs = -1; // -1 corresponds to an unitialized value
    incremental_strategy = strategy;

    n_clauses = 0;
    n_variables = 0;
  }
  ~Totalizer() {}

  void build(Solver *S, vec<Lit> &lits, int64_t rhs);
  void join(Solver *S, vec<Lit> &lits, int64_t rhs);
  void update(Solver *S, int64_t rhs, vec<Lit> &lits, vec<Lit> &assumptions);
  void update(Solver *S, int64_t rhs) {
    vec<Lit> lits;
    vec<Lit> assumptions;
    update(S, rhs, lits, assumptions);
  }
  void add(Solver *S, Totalizer &tot, int64_t rhs);

  bool hasCreatedEncoding() { return hasEncoding; }
  void setIncremental(int incremental) { incremental_strategy = incremental; }
  int getIncremental() { return incremental_strategy; }

  int getNbClauses() { return n_clauses; }
  int getNbVariables() { return n_variables; }
  void resetCounters() {
    n_clauses = 0;
    n_variables = 0;
  }

  vec<Lit> &lits() { return ilits; }
  vec<Lit> &outputs() { return cardinality_outlits; }
  
  void LyInit(Solver *S, vec<Lit> &lits, int64_t rhs, Lit blocking = lit_Undef);
  bool LyGenNextLayerRetTrueIfNewLayer();
  const vector<vector<Lit>>& LyGetLastLayer() const { return lyLastLayer; }

protected:
  void encode(Solver *S, vec<Lit> &lits);
  void adder(Solver *S, vec<Lit> &left, vec<Lit> &right, vec<Lit> &output);
  void incremental(Solver *S, int64_t rhs);
  void toCNF(Solver *S, vec<Lit> &lits);

  vec<vec<Lit>> totalizerIterative_left;
  vec<vec<Lit>> totalizerIterative_right;
  vec<vec<Lit>> totalizerIterative_output;
  vec<int64_t> totalizerIterative_rhs;

  Lit blocking; // Controls the blocking literal for the incremental blocking.
  bool hasEncoding;

  // TEMP
  vec<Lit> ilits;
  vec<Lit> olits;

  vec<Lit> cardinality_inlits; // Stores the inputs of the cardinality
                               // constraint encoding for the totalizer encoding
  vec<Lit> cardinality_outlits; // Stores the outputs of the cardinality
                                // constraint encoding for incremental solving

  int incremental_strategy;
  int64_t current_cardinality_rhs;

  vec<Lit> disable_lits; // Contains a vector with a list of blocking literals.
  bool joinMode;

  int n_clauses;
  int n_variables;
  
  // Layered-sum-related
  Solver* lySolver;
  vector<vector<Lit>> lyLastLayer;
  int lyLayersNum;
  
  template <class TLitVector>
  void adder_basic(Solver *S, TLitVector &left, TLitVector &right,
                      TLitVector &output) {
  
	  // We only need to count the sums up to k.
	  for (int i = 0; i <= (int)left.size(); i++) {
		for (int j = 0; j <= (int)right.size(); j++) {
		  if (i == 0 && j == 0)
		  {
			if (Torc::Instance()->GetTotProp0s() > 0 && i + j < (int)output.size())
			{
				addTernaryClause(S, left[i], right[j], ~output[i + j], blocking);
				n_clauses++;
			}
			continue;
		  }

		  if (i + j > current_cardinality_rhs + 1)
			continue;

		  if (i == 0) {
			addBinaryClause(S, ~right[j - 1], output[j - 1], blocking);
		  } else if (j == 0) {
			addBinaryClause(S, ~left[i - 1], output[i - 1], blocking);
		  } else {
			addTernaryClause(S, ~left[i - 1], ~right[j - 1], output[i + j - 1], blocking);
		  }

		  n_clauses++;

		  if (Torc::Instance()->GetTotProp0s() > 0 && i + j < (int)output.size())
		  {
			  if (i == (int)left.size())
			  {
				  addBinaryClause(S, right[j], ~output[i + j], blocking);
			  }
			  else if (j == (int)right.size())
			  {
				  addBinaryClause(S, left[i], ~output[i + j], blocking);
			  }
			  else
			  {
				  addTernaryClause(S, left[i], right[j], ~output[i + j], blocking);
			  }
			  n_clauses++;
		  }
		}
	  }
  }


  // void enableConstraintBlocker(Solver* S)
  // {
  //   if (incremental_strategy == _INCREMENTAL_BLOCKING_)
  //   {
  //     printf("Error: Blocking incremental strategy does not support the "
  //            "use of constraint blockers.\n");
  //     printf("s UNKNOWN\n");
  //     exit(_ERROR_);
  //   }
  //   assert(!hasEncoding);
  //   if (blocking == lit_Undef)
  //   {
  //     Lit p = mkLit(S->nVars(), false);
  //     newSATVariable(S);
  //     blocking = p;
  //   }
  // }
  // Lit getConstraintBlocker() { return blocking; } // returns 'lit_Undef' if
  // constraint blockers are not enabled

};
} // namespace openwbo

#endif
