/*!
 * \author Ruben Martins - ruben@sat.inesc-id.pt
 *
 * @section LICENSE
 *
 * MiniSat,  Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
 *           Copyright (c) 2007-2010, Niklas Sorensson
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

#ifndef MaxSAT_h
#define MaxSAT_h

#ifdef SIMP
#include "simp/SimpSolver.h"
#else
#include "core/Solver.h"
#endif

#include "MaxSATFormula.h"
#include "MaxTypes.h"
#include "utils/System.h"
#include <algorithm>
#include <functional>
#include <map>
#include <set>
#include <utility>
#include <vector>
#include <string>
#include "MaxSATFormulaExtended.h"
#include "Torc.h"

using NSPACE::vec;
using NSPACE::Lit;
using NSPACE::lit_Undef;
using NSPACE::mkLit;
using NSPACE::lbool;
using NSPACE::Solver;
using NSPACE::cpuTime;

class Satlike;
struct lit;

namespace openwbo {

class Encoder;

template <class T>
class CSetInScope 
{
public:	
	CSetInScope(T& r, const T inScopeValue, const T outOfScopeValue) : m_Reference(r), m_OutOfScopeValue(outOfScopeValue)
	{
		m_Reference = inScopeValue;
	}

	CSetInScope(T& r, const T inScopeValue) : m_Reference(r), m_OutOfScopeValue(m_Reference)
	{
		m_Reference = inScopeValue;
	}

	CSetInScope(T& r) : m_Reference(r), m_OutOfScopeValue(r) {}

	const T& GetOutOfScopeVal() { return m_OutOfScopeValue; }

	~CSetInScope()
	{
		m_Reference = m_OutOfScopeValue;
	}
protected:
	T& m_Reference;
	const T m_OutOfScopeValue;
};

template <class T, class F>
class CApplyFuncOnExitFromScope
{
public:
	CApplyFuncOnExitFromScope(bool isReallyApply, T& i, F Func) : m_I(i), M_F(Func), m_IsExitVal(false), m_IsReallyApply(isReallyApply) {}
	CApplyFuncOnExitFromScope(T& i, F Func) : m_I(i), M_F(Func), m_IsExitVal(false), m_IsReallyApply(true) {}
	CApplyFuncOnExitFromScope(T& i, F Func, const T exitVal) : m_I(i), M_F(Func), m_ExitVal(exitVal), m_IsExitVal(true), m_IsReallyApply(true) {}
	void SetReallyApply(bool isReallyApply) { m_IsReallyApply = isReallyApply; }
	~CApplyFuncOnExitFromScope() 
	{ 
		if (m_IsReallyApply)
		{
			M_F(m_I);
			if (m_IsExitVal) m_I = m_ExitVal;
		}		
	}	
protected:
	T& m_I;
	F M_F;
	T m_ExitVal;
	bool m_IsExitVal;
	bool m_IsReallyApply;
};

template <class F>
class CApplyFuncOnExitFromScope<void, F>
{
public:
	CApplyFuncOnExitFromScope(bool isReallyApply, F Func) : M_F(Func), m_IsReallyApply(isReallyApply) {}
	CApplyFuncOnExitFromScope(F Func) : M_F(Func), m_IsReallyApply(true) {}
	void SetReallyApply(bool isReallyApply) { m_IsReallyApply = isReallyApply; }
	~CApplyFuncOnExitFromScope()
	{
		if (m_IsReallyApply)
		{
			M_F();
		}
	}
protected:
	F M_F;
	bool m_IsReallyApply;
};

class MaxSAT {

public:
  MaxSAT(MaxSATFormula *mx) : satlike_invs(0), satlike_solver(nullptr), oInLatestModel((uint64_t)-1), unsucSatInvocationsWithPolosatOff(0), prevSatlikeOriginalCost((uint64_t)-1) {
    maxsat_formula = mx;

    // 'ubCost' will be set to the sum of the weights of soft clauses
    //  during the parsing of the MaxSAT formula.
    ubCost = 0;
    lbCost = 0;

    off_set = 0;

    // Statistics
    nbSymmetryClauses = 0;
    nbCores = 0;
    nbSatisfiable = 0;
    sumSizeCores = 0;

    print_model = false;
    save_model_calls_last_polarity_update = save_model_calls = 0;      
  }

  MaxSAT() : satlike_invs(0), satlike_solver(nullptr), oInLatestModel((uint64_t)-1), prevSatlikeOriginalCost((uint64_t)-1) {
    maxsat_formula = NULL;

    // 'ubCost' will be set to the sum of the weights of soft clauses
    //  during the parsing of the MaxSAT formula.
    ubCost = 0;
    lbCost = 0;

    off_set = 0;

    // Statistics
    nbSymmetryClauses = 0;
    nbCores = 0;
    nbSatisfiable = 0;
    sumSizeCores = 0;

    print_model = false;
    
    save_model_calls_last_polarity_update = save_model_calls = 0;
  }

  virtual ~MaxSAT() {
    if (maxsat_formula != NULL)
      delete maxsat_formula;
  }

  void setInitialTime(double initial); // Set initial time.

  // Print configuration of the MaxSAT solver.
  // virtual void printConfiguration();
  void printConfiguration();

  // Encoding information.
  void print_AMO_configuration(int encoding);
  void print_PB_configuration(int encoding);
  void print_Card_configuration(int encoding);

  // Incremental information.
  void print_Incremental_configuration(int incremental);

  virtual void search();      // MaxSAT search.
  void printAnswer(int type); // Print the answer.

  // Tests if a MaxSAT formula has a lexicographical optimization criterion.
  bool isBMO(bool cache = true);

  void loadFormula(MaxSATFormula *maxsat) {
    maxsat_formula = maxsat;
    maxsat_formula->setInitialVars(maxsat_formula->nVars());

    if (maxsat_formula->getObjFunction() != NULL) {
      off_set = maxsat_formula->getObjFunction()->_const;
      maxsat_formula->convertPBtoMaxSAT();
    }

    ubCost = maxsat_formula->getSumWeights();
  }

  void blockModel(Solver *solver);

  // Get bounds methods
  uint64_t getUB();
  std::pair<uint64_t, int> getLB();

  Soft &getSoftClause(int i) { return maxsat_formula->getSoftClause(i); }
  Hard &getHardClause(int i) { return maxsat_formula->getHardClause(i); }
  Lit getAssumptionLit(int soft) {
    return maxsat_formula->getSoftClause(soft).assumption_var;
  }
  Lit getRelaxationLit(int soft, int i = 0) {
    return maxsat_formula->getSoftClause(soft).relaxation_vars[i];
  }

  int64_t getOffSet() { return off_set; }

  MaxSATFormula *getMaxSATFormula() { return maxsat_formula; }

  void setPrintModel(bool model) { print_model = model; }
  bool getPrintModel() { return print_model; }  
protected:
  void build_nuwls_clause_structure();
  void build_satlike_clause_structure();
  void InitSatLike();
  void SatLike(Solver *solver);
  int satlike_invs;
  Satlike* satlike_solver;
  lit **satlike_clause_lit;
  int *satlike_clause_lit_count;
  int satlike_nvars;
  int satlike_nclauses;
  uint64_t satlike_topclauseweight;
  long long *satlike_clause_weight;

  // Interface with the SAT solver
  //
  Solver *newSATSolver(); // Creates a SAT solver.
  // Solves the formula that is currently loaded in the SAT solver.
  lbool searchSATSolver(Solver *S, vec<Lit> &assumptions, bool pre = false);
  lbool searchSATSolver(Solver *S, bool pre = false);
  lbool polosat(Solver *S, vec<Lit> &assumptions, vec<Lit> &observables, std::function<bool()> StopAfterNewImprovingModel = nullptr);
  
  void newSATVariable(Solver *S); // Creates a new variable in the SAT solver.

  // Properties of the MaxSAT formula
  //
  vec<lbool> model; // Stores the best satisfying model.
  uint64_t oInLatestModel; // Stores the o value of the latest model
  
  // Statistics
  //
  int nbCores;           // Number of cores.
  int nbSymmetryClauses; // Number of symmetry clauses.
  uint64_t sumSizeCores; // Sum of the sizes of cores.
  int nbSatisfiable;     // Number of satisfiable calls.

  // Bound values
  //
  uint64_t ubCost; // Upper bound value.
  uint64_t lbCost; // Lower bound value.
  int64_t off_set; // Offset of the objective function for PB solving.

  MaxSATFormula *maxsat_formula;

  // Others
  // int currentWeight;  // Initialized to the maximum weight of soft clauses.
  double initialTime; // Initial time.
  int verbosity;      // Controls the verbosity of the solver.
  bool print_model;   // Controls if the model is printed at the end.

  // Different weights that corresponds to each function in the BMO algorithm.
  std::vector<uint64_t> orderWeights;

  // Utils for model management
  //
  void saveModel(vec<lbool> &currentModel, uint64_t optionalWeightForPrintOuts = (uint64_t)-1, Solver *sToBlockModel = NULL); // Saves a Model. The optional cost is used for calculating and storing the print-out string only. Optionally, if s != NULL, blocks it.
  bool isRealModel(vec<lbool> &currentModel);
  // Compute the cost of a model.
  uint64_t computeCostModel(vec<lbool> &currentModel,
                            uint64_t weight = UINT64_MAX);
                         
  uint64_t save_model_calls;
  uint64_t save_model_calls_last_polarity_update;
  // Utils for printing
  //
  void printModel(); // Print the best satisfying model.
  void printStats(); // Print search statistics.

  // Greater than comparator.
  bool static greaterThan(uint64_t i, uint64_t j) { return (i > j); }
  
  void printFormulaStats(Solver *S);
  
  void BumpTargets(const vec<Lit>& objFunction, const vec<uint64_t>& coeffs, Solver *solver);		
  
  int unsucSatInvocationsWithPolosatOff;
  
  std::chrono::high_resolution_clock::time_point startTimeForSatlikeReinvoke;
  uint64_t prevSatlikeOriginalCost;
  
  std::string statSolverStr = ""; 
  std::string statInitSatlikePolosatStr = ""; 
  std::string statOBVStr = ""; 
  std::string statLSUStr = ""; 
   
};
} // namespace openwbo

#endif
