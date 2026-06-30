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

#include "Alg_OBV.h"
#include "../Torc.h"
#include <cstdlib>
#include <ctime>     
#include <vector>
#include <algorithm>
#include <random>
#include <iostream> 
#include "../encodings/Enc_Totalizer.h"

using namespace openwbo;

uint64_t OBV::MrsBeaver(Solver * solver, int iterations, int conflicts){

  std::srand ( 1971603567 );
  std::vector<Lit> outputs;
  
  for (int i = 0; i < objFunction.size(); i++)
    outputs.push_back(objFunction[i]);
      
  vec<Lit> dummy;
  lbool res;
  bool turnedOffDueToSize = false;
  
  auto TurnOffDueToSmallSize = [&]()
  {
	  if (turnedOffDueToSize)
	  {
		  return true;
	  }
	  
	  if (Torc::Instance()->GetMrsBeaverSizeSwitchToComplete() == 0 || encoder.hasCardEncoding())
	  {
		  return false;
	  }
	  
	  auto predictedSize = encoder.predictCardinality(solver, objFunction, oInLatestModel-1, Torc::Instance()->GetMrsBeaverSizeSwitchToComplete());
	  printf("c Predicted size is %d vs. the size-based limit %d\n", predictedSize, Torc::Instance()->GetMrsBeaverSizeSwitchToComplete());
	  return turnedOffDueToSize = predictedSize >= 0 && predictedSize < Torc::Instance()->GetMrsBeaverSizeSwitchToComplete();	  
  };
  
  const bool satInvocation = Torc::Instance()->GetMsMaxEpochs() == 0;
  if (satInvocation)
  {
	  res = searchSATSolver(solver, dummy);
  }
  else
  {
	  res = Torc::Instance()->GetMrsBeaverApplySizeThrDuringInitialPolosat() ? polosat(solver, dummy, objFunction, TurnOffDueToSmallSize) : polosat(solver, dummy, objFunction);
  } 
  
  if (res != l_True)
    return 0;
    
  SatLike(solver);
    
   if (Torc::Instance()->GetMrsBeaverPolosatRegulateStrat() == 1 && Torc::Instance()->GetMsObvStrat() != 0)
   {
	  printf("c switched off ms_obs_strat\n"); 
	  Torc::Instance()->SetMsObvStrat(0);
   }
    

  uint64_t current_ub = computeCostModel(satInvocation ? solver->model : model);  
  
  if (satInvocation)
  {
	  saveModel(solver->model, current_ub, Torc::Instance()->GetBlockBestModel() ? solver : NULL);
	  if (!Torc::Instance()->GetPrintEveryModel()) printf("o %" PRId64 "\n", current_ub);
	  printf("c timeo %u %" PRId64 " \n", (unsigned)ceil(Torc::Instance()->WallTimePassed()), current_ub);		
  }
  
  const auto initCost = oInLatestModel;
  
  vec<lbool> original_model;
  model.copyTo(original_model);
  
  Totalizer tot;
  vector<vector<Lit>> outputsPerLayer;
  bool totInitialized = false;
  Lit totSelector = lit_Undef;
      
  mrsBeaverFailedSubsequentIters = 0;
  const auto obvt0 = Torc::Instance()->WallTimePassed();
  for (int t = 0; t < iterations; t++){
	
    if (TurnOffDueToSmallSize())
	{
		statOBVStr = "OBVT0 " + to_string(obvt0) + " OBVC0 " + to_string(initCost) + " OBVIters " + to_string(t) + " OBVT1 " + to_string(Torc::Instance()->WallTimePassed()) + " OBVC1 " + to_string(oInLatestModel) + " OBVStop 1 ";
		printf("c Turning Mrs. Beaver off\n");	  	
		if (statSolverStr != "") std::cout << "c " << statSolverStr;
		return current_ub;
	}
	else
	{
		statOBVStr = "OBVT0 " + to_string(obvt0) + " OBVC0 " + to_string(initCost) + " OBVIters " + to_string(t) + " OBVT1 " + to_string(Torc::Instance()->WallTimePassed()) + " OBVC1 " + to_string(oInLatestModel) + " OBVStop 0 ";
	}
	
    printf ("c Iteration #%d\n",t+1);
    model_all.clear();
    if (Torc::Instance()->GetMrsBeaverEachIterStartBestModel()){
	  model.copyTo(model_all);	
	} else {
	  original_model.copyTo(model_all);
	}

    auto new_current_ub = t % 4 == 0 || t % 4 == 1 ? ums_obv_bs(solver, outputs, current_ub, conflicts) : obv_bs(solver, outputs, current_ub, conflicts);    
    
    auto prev_smc = save_model_calls;
    SatLike(solver);
    if (save_model_calls > prev_smc)
    {
		new_current_ub = computeCostModel(model);
	}
        
    mrsBeaverFailedSubsequentIters = new_current_ub == current_ub ? mrsBeaverFailedSubsequentIters + 1 : 0;
    
    current_ub = new_current_ub;
    
    // Create totalizer layers, when required
    if (Torc::Instance()->GetPartialSumFailItersToSwitch() != 0 && mrsBeaverFailedSubsequentIters >= (unsigned)Torc::Instance()->GetPartialSumFailItersToSwitch() && !totInitialized)
    {
		 totSelector = mkLit(solver->nVars(), false);
         newSATVariable(solver);
  	     tot.LyInit(solver, objFunction, current_ub, totSelector);		 
		 
		 while ((int)outputsPerLayer.size() < Torc::Instance()->GetPartialSumLayersThr() && tot.LyGenNextLayerRetTrueIfNewLayer())
		 {
			 outputsPerLayer.push_back(vector<Lit>());
			 printf("c Partial sum inside: created layer number %zu\n", outputsPerLayer.size());
			 const vector<vector<Lit>>& currLayer = tot.LyGetLastLayer();		  
			 
			 for (const vector<Lit>& currNode : currLayer)
			 {
				outputsPerLayer.back().push_back(currNode.back());					  
				//outputsPerLayer.back().insert(outputsPerLayer.back().end(), currNode.begin(), currNode.end());					  
			 }
			 
		  }
		  totInitialized = true;
	 }
	 
	 if (!outputsPerLayer.empty())
	 {
		 int l = 0;
		 for (auto& currOutputs : outputsPerLayer)
		 {
			    printf ("c Iteration #%d; layer %d\n",t+1, ++l);
				model_all.clear();
				if (Torc::Instance()->GetMrsBeaverEachIterStartBestModel()){
				  model.copyTo(model_all);	
				} else {
				  original_model.copyTo(model_all);
				}

				auto new_current_ub = t % 4 == 0 || t % 4 == 1 ? ums_obv_bs(solver, currOutputs, current_ub, Torc::Instance()->GetPartialSumConflicts(), ~totSelector) : obv_bs(solver, currOutputs, current_ub, Torc::Instance()->GetPartialSumConflicts(), ~totSelector);    
				
				current_ub = new_current_ub;
				t % 4 == 0 && t > 0 ? std::shuffle(currOutputs.begin(), currOutputs.end(), std::mt19937{std::random_device{}()}) : std::reverse(currOutputs.begin(), currOutputs.end());
		 }
	 }


	t % 4 == 0 && t > 0 ? std::shuffle(outputs.begin(), outputs.end(), std::mt19937{std::random_device{}()}) : std::reverse(outputs.begin(), outputs.end());
  }
  
  solver->budgetOff();
    
  if (totSelector != lit_Undef)
  {
	solver->addClause(totSelector);  
  }
  
  return current_ub;

}

uint64_t OBV::obv_bs(Solver * solver, std::vector<Lit>& outputs, uint64_t ub, int conflicts, Lit addAssump){

  vec<Lit> assumptions;
  if (addAssump != lit_Undef)
  {
	  assumptions.push(addAssump);
  }
  
  vec<lbool> current_model;
  assert (model_all.size() != 0);
  model_all.copyTo(current_model);
    
  const int verbosity = Torc::Instance()->GetMsVerbosity();   
  
  uint64_t last_ub = ub;  
  uint64_t badOutputs = 0;
  
  for (size_t i =0; i < outputs.size(); i++){
    const bool skipPolosat = Torc::Instance()->GetMsMaxEpochs() == 0;
    if (var(outputs[i]) < current_model.size() && current_model[var(outputs[i])] == l_False){
      assumptions.push(~outputs[i]);
    } else {
      vec<Lit> current_assumptions;
      assumptions.copyTo(current_assumptions);
      current_assumptions.push(~outputs[i]);

      solver->setConfBudget2(conflicts);

	  lbool res;
	  if (skipPolosat)
	  {
		  res = searchSATSolver(solver, current_assumptions);
	  }
	  else
	  {
		  vec<Lit> remOuts;
		  for (size_t j = i+1; j < outputs.size(); ++j)
		  {
			  remOuts.push(outputs[j]);
		  }
		  res = polosat(solver, current_assumptions, remOuts);
	  }  
	  
	  solver->budgetOffConflict2();    
     
      if (res == l_True){
        assumptions.push(~outputs[i]);
        uint64_t newCost = computeCostModel(skipPolosat ? solver->model : model);
        if (verbosity > 2) printf("c OBV-BS new cost = %" PRId64 "\n", newCost);
        if (newCost < last_ub){
			if (skipPolosat)
			{
			  saveModel(solver->model, newCost, Torc::Instance()->GetBlockBestModel() ? solver : NULL);
			  if (!Torc::Instance()->GetPrintEveryModel()) printf("o %" PRId64 "\n", newCost);
			  printf("c timeo %u %" PRId64 " \n", (unsigned)ceil(Torc::Instance()->WallTimePassed()), newCost);
			}
          last_ub = newCost;
        }
        current_model.clear();
        solver->model.copyTo(current_model);
      } else {	
		assumptions.push(outputs[i]);
        ++badOutputs;
        if (badOutputs >= oInLatestModel)
		{
			if (verbosity > 2) printf("c Stopping OBV-BS, since the still-reachable-cost %" PRId64 " is greater than the cost of the best model %" PRId64 "\n", badOutputs, oInLatestModel);
			break;
		}
      }
    }
  }
  //solver->budgetOff();
  return last_ub;
}
  
uint64_t OBV::ums_obv_bs(Solver * solver, std::vector<Lit>& outputs, uint64_t ub, int conflicts, Lit addAssump){
  vec<Lit> assumptions;
  if (addAssump != lit_Undef)
  {
	  assumptions.push(addAssump);
  }
  vec<lbool> current_model;
  assert (model.size() != 0);
  model.copyTo(current_model);
  uint64_t last_ub = ub;  
  uint64_t badOutputs = 0;
  
  const int verbosity = Torc::Instance()->GetMsVerbosity();
  
  std::vector<Lit> outputs_mod;
  for (size_t i = 0; i < outputs.size(); i++){
    outputs_mod.push_back(outputs[i]);
  }

  for (size_t i =0; i < outputs_mod.size(); i++){
	const bool skipPolosat = Torc::Instance()->GetMsMaxEpochs() == 0;
    if (var(outputs_mod[i]) < current_model.size() && current_model[var(outputs_mod[i])] == l_False){
      assumptions.push(~outputs_mod[i]);
    } else {
      vec<Lit> current_assumptions;
      assumptions.copyTo(current_assumptions);
      current_assumptions.push(~outputs_mod[i]);

      solver->setConfBudget2(conflicts);

      lbool res;
	  if (skipPolosat)
	  {
		  res = searchSATSolver(solver, current_assumptions);
	  }
	  else
	  {
		  vec<Lit> remOuts;
		  for (size_t j = i+1; j < outputs.size(); ++j)
		  {
			  remOuts.push(outputs_mod[j]);
		  }
		  res = polosat(solver, current_assumptions, remOuts);
	  }

      solver->budgetOffConflict2();

      // move bits
      if (res == l_True){
        size_t k = i+1;
        for (size_t j = i+1; j < outputs_mod.size(); j++){
          if (solver->model[var(outputs_mod[j])] == l_False){
            if (k!=j){
              Lit a = outputs_mod[k];
              outputs_mod[k] = outputs_mod[j];
              outputs_mod[j] = a;
            }
            k++;
          }
        }
      }
      
      
      if (res == l_True){
        assumptions.push(~outputs_mod[i]);
        
         uint64_t newCost = computeCostModel(skipPolosat ? solver->model : model);
         if (verbosity > 2) printf("c UMS-OBV-BS new cost = %" PRId64 "\n", newCost);
		 if (newCost < last_ub) {
		 	if (skipPolosat)
			{
			  saveModel(solver->model, newCost, Torc::Instance()->GetBlockBestModel() ? solver : NULL);
			  if (!Torc::Instance()->GetPrintEveryModel()) printf("o %" PRId64 "\n", newCost);
			  printf("c timeo %u %" PRId64 " \n", (unsigned)ceil(Torc::Instance()->WallTimePassed()), newCost);
			}
		  last_ub = newCost;
		 }
		
	  
        current_model.clear();
        solver->model.copyTo(current_model);
      } else {
		assumptions.push(outputs_mod[i]);
        ++badOutputs;
        if (badOutputs >= oInLatestModel)
		{
			if (verbosity > 2) printf("c Stopping UMS-OBV-BS, since the still-reachable-cost %" PRId64 " is greater than the cost of the best model %" PRId64 "\n", badOutputs, oInLatestModel);
			break;
		}
      }
    }
  }
  //solver->budgetOff();
  return last_ub;
}

/*_________________________________________________________________________________________________
  |
  |  normalSearch : [void] ->  [void]
  |
  |  Description:
  |
  |    Linear search algorithm.
  |
  |  For further details see:
  |    *  Daniel Le Berre, Anne Parrain: The Sat4j library, release 2.2. JSAT
  |       7(2-3): 59-6 (2010)
  |    *  Miyuki Koshimura, Tong Zhang, Hiroshi Fujita, Ryuzo Hasegawa: QMaxSAT:
  |       A Partial Max-SAT Solver. JSAT 8(1/2): 95-100 (2012)
  |
  |  Post-conditions:
  |    * 'ubCost' is updated.
  |    * 'nbSatisfiable' is updated.
  |    * 'nbCores' is updated.
  |
  |________________________________________________________________________________________________@*/
void OBV::normalSearch() {

  lbool res = l_True;

  initRelaxation();
  solver = rebuildSolver();
  
  InitSatLike();  
  
  if (Torc::Instance()->GetPolOptimistic())
	{
		 if (Torc::Instance()->TargetIsVarTarget().size() == 0) {
			  Torc::Instance()->TargetIsVarTarget().growTo(solver->nVars(), false);
			  
			  for (int i = 0; i < objFunction.size(); i++) {
				  auto v = var(objFunction[i]);
				  assert(sign(objFunction[i]) == 0);
				  Torc::Instance()->TargetIsVarTarget()[v] = true;				  				  
			  }			  
		  }		
	}

	if (Torc::Instance()->GetTargetVarsBumpVal() != 0)
	{
		BumpTargets(objFunction, coeffs, solver);
	}
  
  uint64_t newCost = UINT64_MAX;
  bool mrsb = true;  
  uint64_t lsuIts = 0;

  while (res == l_True) {

	const bool satInvocation = Torc::Instance()->GetMsMaxEpochs() == 0;
    vec<Lit> dummy;
    // invoke Mrs. Beaver
    if (mrsb) {
          printf("c Mrs. Beaver incomplete stage\n");
          newCost = MrsBeaver(solver, _iterations, _limit);
          printf("c Mrs. Beaver ub %" PRId64 "\n", newCost);
          printf("c Warn: changing to LSU algorithm.\n"); 
          
          statOBVStr += "LSUT0 " + to_string(Torc::Instance()->WallTimePassed()) + " LSUC0 " + to_string(oInLatestModel);
          
          if (Torc::Instance()->GetMrsBeaverPolosatRegulateStrat() == 3 && Torc::Instance()->GetMsMaxEpochs() != 0)
		  {
			  printf("c switched off polosat forever before the complete part\n"); 
			  Torc::Instance()->SetMsMaxEpochs(0);
		  } else if (Torc::Instance()->GetMrsBeaverPolosatRegulateStrat() == 2 && Torc::Instance()->GetMsObvStrat() != 0)
		  {
			  printf("c switched off ms_obs_strat\n"); 
			  Torc::Instance()->SetMsObvStrat(0);
		  }
    } else {		
		if (satInvocation)
		  {
			  res = searchSATSolver(solver, dummy);
		  }
		  else
		  {
			  res = polosat(solver, dummy, objFunction);
		  }
		  SatLike(solver);
		  ++lsuIts;		  
    }

    if (model.size() == 0){
      printAnswer(_UNSATISFIABLE_);
      exit(_UNSATISFIABLE_);
    }
    
    // printf("c res = %s\n", (res == l_False ? "l_False" : res == l_True ? "l_True" : "l_Undef"));

    if (res == l_True) {
      nbSatisfiable++;
      if  (!mrsb){
        newCost = computeCostModel(satInvocation ? solver->model : model);
		// printf("newCost = %d\n", newCost);
        if (satInvocation)
		{
			saveModel(solver->model, newCost, Torc::Instance()->GetBlockBestModel() ? solver : NULL);
		}
		statLSUStr = "LSUIters " + to_string(lsuIts) + " LSUT1 " + to_string(Torc::Instance()->WallTimePassed()) + " LSUC1 " + to_string(oInLatestModel) + " ";
      } else {
        mrsb = false;
      }
      if (satInvocation)
	  {
		if (!Torc::Instance()->GetPrintEveryModel()) printf("o %" PRId64 "\n", newCost + off_set); 
		printf("c timeo %u %" PRId64 " \n", (unsigned)ceil(Torc::Instance()->WallTimePassed()), newCost + off_set);
	  }	
      
	  if (newCost == 0) {
        // If there is a model with value 0 then it is an optimal model
        ubCost = newCost;

        printAnswer(_OPTIMUM_);
        exit(_OPTIMUM_);

      } else {
          // Unweighted.
          if (!encoder.hasCardEncoding())
            encoder.encodeCardinality(solver, objFunction, newCost - 1);
          else
            encoder.updateCardinality(solver, newCost - 1);

        ubCost = newCost;
      }

    } else {
      nbCores++;
      if (model.size() == 0) {
        assert(nbSatisfiable == 0);
        // If no model was found then the MaxSAT formula is unsatisfiable
        printAnswer(_UNSATISFIABLE_);
        exit(_UNSATISFIABLE_);
      } else {
        printAnswer(_OPTIMUM_);
        exit(_OPTIMUM_);
      }
    }
  }
}

// Public search method
void OBV::search() {

  assert (maxsat_formula->getProblemType() == _UNWEIGHTED_);

  printConfiguration();
  normalSearch();
}

/************************************************************************************************
 //
 // Rebuild MaxSAT solver
 //
 ************************************************************************************************/

/*_________________________________________________________________________________________________
  |
  |  rebuildSolver : (minWeight : int)  ->  [Solver *]
  |
  |  Description:
  |
  |    Rebuilds a SAT solver with the current MaxSAT formula.
  |    If a weight is specified, then it only considers soft clauses with weight
  |    smaller than the specified weight.
  |    NOTE: a weight is specified in the 'bmo' approach.
  |
  |________________________________________________________________________________________________@*/
Solver *OBV::rebuildSolver(uint64_t min_weight) {

  vec<bool> seen;
  seen.growTo(maxsat_formula->nVars(), false);

  Solver *S = newSATSolver();
  
  S->confl_to_chrono = Torc::Instance()->GetConflToChrono();
  S->chrono = Torc::Instance()->GetChrono();

  for (int i = 0; i < maxsat_formula->nVars(); i++)
    newSATVariable(S);

  for (int i = 0; i < maxsat_formula->nHard(); i++)
    S->addClause(maxsat_formula->getHardClause(i).clause);

  for (int i = 0; i < maxsat_formula->nPB(); i++) {
    Encoder *enc = new Encoder(_INCREMENTAL_NONE_, _CARD_MTOTALIZER_,
                               _AMO_LADDER_, _PB_GTE_);

    // Make sure the PB is on the form <=
    // if (maxsat_formula->getPBConstraint(i)->_sign)
    //  maxsat_formula->getPBConstraint(i)->changeSign();
    assert(maxsat_formula->getPBConstraint(i)->_sign);

    enc->encodePB(S, maxsat_formula->getPBConstraint(i)->_lits,
                  maxsat_formula->getPBConstraint(i)->_coeffs,
                  maxsat_formula->getPBConstraint(i)->_rhs);

    delete enc;
  }

  for (int i = 0; i < maxsat_formula->nCard(); i++) {
    Encoder *enc = new Encoder(_INCREMENTAL_NONE_, _CARD_MTOTALIZER_,
                               _AMO_LADDER_, _PB_GTE_);

    if (maxsat_formula->getCardinalityConstraint(i)->_rhs == 1) {
      enc->encodeAMO(S, maxsat_formula->getCardinalityConstraint(i)->_lits);
    } else {

      enc->encodeCardinality(S,
                             maxsat_formula->getCardinalityConstraint(i)->_lits,
                             maxsat_formula->getCardinalityConstraint(i)->_rhs);
    }

    delete enc;
  }

  vec<Lit> clause;
  for (int i = 0; i < maxsat_formula->nSoft(); i++) {
    if (maxsat_formula->getSoftClause(i).weight < min_weight)
      continue;

    clause.clear();
    maxsat_formula->getSoftClause(i).clause.copyTo(clause);

    for (int j = 0; j < maxsat_formula->getSoftClause(i).relaxation_vars.size();
         j++) {
      clause.push(maxsat_formula->getSoftClause(i).relaxation_vars[j]);
    }

    S->addClause(clause);
  }

  return S;
}

/*_________________________________________________________________________________________________
  |
  |  rebuildBMO : (functions : int)  ->  [Solver *]
  |
  |  Description:
  |
  |    Rebuilds a SAT solver with the current MaxSAT formula.
  |    Only considers soft clauses with the weight of the current
  |    lexicographical optimization weight ('currentWeight')
  |    For each function already computed in the BMO algorithm it encodes the
  |    respective cardinality constraint.
  |
  |________________________________________________________________________________________________@*/
Solver *OBV::rebuildBMO(vec<vec<Lit>> &functions, vec<int> &rhs,
                             uint64_t currentWeight) {

  assert(functions.size() == rhs.size());

  Solver *S = rebuildSolver(currentWeight);

  objFunction.clear();
  coeffs.clear();
  for (int i = 0; i < maxsat_formula->nSoft(); i++) {
    if (maxsat_formula->getSoftClause(i).weight == currentWeight) {
      objFunction.push(maxsat_formula->getSoftClause(i).relaxation_vars[0]);
      coeffs.push(maxsat_formula->getSoftClause(i).weight);
    }
  }

  for (int i = 0; i < functions.size(); i++)
    encoder.encodeCardinality(S, functions[i], rhs[i]);

  return S;
}

/************************************************************************************************
 //
 // Other protected methods
 //
 ************************************************************************************************/

/*_________________________________________________________________________________________________
  |
  |  initRelaxation : (objective : vec<Lit>&) (weights : vec<int>&)  ->  [void]
  |
  |  Description:
  |
  |    Initializes the relaxation variables by adding a fresh variable to the
  |    'relaxationVars' of each soft clause.
  |
  |  Post-conditions:
  |    * 'objFunction' contains all relaxation variables that were added to soft
  |       clauses.
  |    * 'coeffs' contains the weights of all soft clauses.
  |
  |________________________________________________________________________________________________@*/
void OBV::initRelaxation() {
  for (int i = 0; i < maxsat_formula->nSoft(); i++) {
    Lit l = maxsat_formula->newLiteral();
    maxsat_formula->getSoftClause(i).relaxation_vars.push(l);
    objFunction.push(l);
    coeffs.push(maxsat_formula->getSoftClause(i).weight);
  }
}
