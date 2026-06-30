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

#include "Alg_LinearSU_Clustering.h"
#include "../MaxTypes.h"
#include "../Torc.h"
#include "../SATLike.h"
#include "algorithms/Alg_nuwls.h"


#include <algorithm>
#include <fstream>
#include <iostream>
#include <random>

#define MAX_CLAUSES 3000000

using namespace openwbo;
using namespace std;

/*_________________________________________________________________________________________________
  |
  |  initializeCluster : [void] -> [void]
  |
  |  Description:
  |
  |    Initializes cluster according to the algorithm specified.
  |
  |  Pre-conditions:
  |    * cluster_algo contains the clustering method
  |
  |  Post-conditions:
  |    * cluster is initialized
  |
  |________________________________________________________________________________________________@*/
void LinearSUClustering::initializeCluster() {	
  switch (cluster_algo) {
  case ClusterAlg::_DIVISIVE_:
    cluster = new Cluster_DivisiveMaxSeparate(
        static_cast<MaxSATFormulaExtended *>(maxsat_formula), cluster_stat);
    break;
  }
}

/*_________________________________________________________________________________________________
  |
  |  computeCostModel : (currentModel : vec<lbool>&) (weight : int) ->
  |                     [uint64_t]
  |
  |  Description:
  |
  |    Computes the cost of 'currentModel'. The cost of a model is the sum of
  |    the weights of the unsatisfied soft clauses.
  |    If a weight is specified, then it only considers the sum of the weights
  |    of the unsatisfied soft clauses with the specified weight.
  |
  |  Pre-conditions:
  |    * Assumes that 'currentModel' is not empty.
  |
  |________________________________________________________________________________________________@*/
uint64_t LinearSUClustering::computeCostModel(vec<lbool> &currentModel,
                                              uint64_t weight) {

  // printf("c LinearSUClustering::computeCostModel with weight %llu called\n", weight);
  assert(currentModel.size() != 0);
  uint64_t currentCost = 0;
  
  for (int i = 0; i < maxsat_formula->nSoft(); i++) {
    bool unsatisfied = true;
    for (int j = 0; j < maxsat_formula->getSoftClause(i).clause.size(); j++) {

      if (weight != UINT64_MAX &&
          maxsat_formula->getSoftClause(i).weight != weight) {
        unsatisfied = false;
        continue;
      }
	
      assert(var(maxsat_formula->getSoftClause(i).clause[j]) <
             currentModel.size());
      if ((sign(maxsat_formula->getSoftClause(i).clause[j]) &&
           currentModel[var(maxsat_formula->getSoftClause(i).clause[j])] ==
               l_False) ||
          (!sign(maxsat_formula->getSoftClause(i).clause[j]) &&
           currentModel[var(maxsat_formula->getSoftClause(i).clause[j])] ==
               l_True)) {
        unsatisfied = false;
        
        break;
      }
    }

    if (unsatisfied) {
      currentCost += maxsat_formula->getSoftClause(i).weight;      
    }        
	
  }

  return currentCost;
}

/*_________________________________________________________________________________________________
  |
  |  computeOriginalCost : (currentModel : vec<lbool>&) (weight : uint64_t) ->
  |                     [uint64_t]
  |
  |  Description:
  |
  |    Computes the cost of 'currentModel' as per the original weights.
  |    The cost of a model is the sum of the weights of the unsatisfied soft clauses.
  |    If a weight is specified, then it only considers the sum of the weights
  |    of the unsatisfied soft clauses with the specified weight.
  |
  |  Pre-conditions:
  |    * Assumes that 'currentModel' is not empty.
  |
  |________________________________________________________________________________________________@*/
uint64_t LinearSUClustering::computeOriginalCost(vec<lbool> &currentModel,
                                                 uint64_t weight) {

  assert(currentModel.size() != 0);
  uint64_t currentCost = 0;

  for (int i = 0; i < maxsat_formula->nSoft(); i++) {
    bool unsatisfied = true;
    for (int j = 0; j < maxsat_formula->getSoftClause(i).clause.size(); j++) {

      if (weight != UINT64_MAX &&
          maxsat_formula->getSoftClause(i).weight != weight) {
        unsatisfied = false;
        continue;
      }

      assert(var(maxsat_formula->getSoftClause(i).clause[j]) <
             currentModel.size());
      if ((sign(maxsat_formula->getSoftClause(i).clause[j]) &&
           currentModel[var(maxsat_formula->getSoftClause(i).clause[j])] ==
               l_False) ||
          (!sign(maxsat_formula->getSoftClause(i).clause[j]) &&
           currentModel[var(maxsat_formula->getSoftClause(i).clause[j])] ==
               l_True)) {
        unsatisfied = false;
        break;
      }
    }

    if (unsatisfied) {
      currentCost += cluster->getOriginalWeight(i);
    }
  }

  return currentCost;
}

/************************************************************************************************
 //
 // Incremental Linear Search Algorithm with Boolean Multilevel Optimization (BMO)
 //
 ************************************************************************************************/

/*_________________________________________________________________________________________________
  |
  |  bmoSearch : [void] ->  [void]
  |
  |  Description:
  |
  |    Incremental Linear search algorithm with lexicographical optimization modified for 
  |    incomplete weighted MaxSAT.
  |
  |  For further details see:
  |    * Joao Marques-Silva, Josep Argelich, Ana Graça, Ines Lynce: Boolean
  |      lexicographic optimization: algorithms & applications. Ann. Math.
  |      Artif. Intell. 62(3-4): 317-343 (2011)
  |
  |  Post-conditions:
  |    * 'lbCost' is updated.
  |    * 'ubCost' is updated.
  |    * 'nbSatisfiable' is updated.
  |    * 'nbCores' is updated.
  |
  |________________________________________________________________________________________________@*/
void LinearSUClustering::bmoSearch(){

  if (orderWeights.size() == 0)
	{
		// No soft clauses
		solver = rebuildSolver();
		auto res = searchSATSolver(solver);
    
     if (res == l_False) 
     {
		 printAnswer(_UNSATISFIABLE_);
          exit(_UNSATISFIABLE_);
	 }
	 else if (res == l_True) 
	 {
		  saveModel(solver->model, 0);
		  printAnswer(_SATISFIABLE_);
          exit(_SATISFIABLE_);
	 }
	 else
	 {
		 printAnswer(_UNKNOWN_);
          exit(_UNKNOWN_);
	 }
	}
  
  assert(orderWeights.size() > 0);
  lbool res = l_True;  
  const int verbosity = Torc::Instance()->GetMsVerbosity();

  initRelaxation();
  solver = rebuildSolver();
  
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
	
  vec<vec<Lit>> functions;
  vec<uint64_t> rhs;
  vec<uint64_t> ub_rhs;
  vec<uint64_t> best_rhs;
  uint64_t repair_cost = UINT64_MAX;
  std::vector<Encoder*> encoders;
  vec<Lit> encodingAssumptions;
  vec<Lit> current_assumptions;
  vec<vec<Lit>> functions_to_assumptions;
  vec<bool> encoder_created;
  encoder_created.growTo(orderWeights.size(), false);
  Encoder *pb = new Encoder();
  pb->setPBEncoding(_PB_GTE_);

  for (int j = 0; j < (int)orderWeights.size(); j++){
    functions.push();
    new (&functions[j]) vec<Lit>();
    functions_to_assumptions.push();
    new (&functions_to_assumptions[j]) vec<Lit>();

    for (int i = 0; i < maxsat_formula->nSoft(); i++) {
      if (maxsat_formula->getSoftClause(i).weight == orderWeights[j]) {
        functions[j].push(maxsat_formula->getSoftClause(i).relaxation_vars[0]);
      }
    }
    rhs.push(UINT64_MAX);
    ub_rhs.push(UINT64_MAX);
    best_rhs.push(UINT64_MAX);
    Encoder* enc = new Encoder();
    enc->setIncremental(_INCREMENTAL_ITERATIVE_);
    enc->setCardEncoding(_CARD_TOTALIZER_);
    encoders.push_back(enc);
  }

  int current_function_id = 0;
  vec<Lit> assumptions;
  if (verbosity > 2) printf("c objective function %d out of %zu\n",current_function_id,orderWeights.size());

  bool repair = false;

  vec<Lit> pb_function;
  vec<uint64_t> pb_coeffs;  
  vector<uint64_t> mutLitsScores;  
  unsigned mutationSamplingTimesInvoked = 0;
  
   auto StopDueToModelPerSecThr = [&](bool isModelPerSecThrApplied, unsigned improvingModelsSoFar, std::chrono::high_resolution_clock::time_point& start)
   {
	   return isModelPerSecThrApplied &&
			improvingModelsSoFar != 0 &&
			improvingModelsSoFar / std::chrono::duration<double>(std::chrono::high_resolution_clock::now()-start).count() < Torc::Instance()->GetMsModelPerSecThr();
	};
	
	auto StopDueToPropPerModelThr = [&](bool isPropPerModelThrApplied, unsigned improvingModelsSoFar, uint64_t startProp)
   {
	   return isPropPerModelThrApplied &&
			improvingModelsSoFar != 0 &&
			(double)(solver->propagations - startProp) / (double)improvingModelsSoFar > (double)Torc::Instance()->GetMsPropPerModelThr();				   
	};
	   
	auto ObvBs = [&](uint64_t& newCost)
    {
		 const bool isModelPerSecThrApplied = Torc::Instance()->GetMsModelPerSecThr() != 0.;
		 unsigned improvingModelsSoFar = 0;
		 std::chrono::high_resolution_clock::time_point start = std::chrono::high_resolution_clock::now();

		  if (verbosity > 1) printf("c Entered OBV-BS\n");
		  vector<Lit> outputs;
		   outputs.reserve(maxsat_formula->nSoft());
		   vector<uint64_t> weightPerOutput;
		   weightPerOutput.reserve(maxsat_formula->nSoft());
		   uint64_t overallWeight = 0;
		   uint64_t badWeight = 0;

		   for (int iCurrFuncId = current_function_id; iCurrFuncId <= (int)functions.size() - 1; ++iCurrFuncId)
		   {
			   for (int iRelVar = 0; iRelVar <= functions[iCurrFuncId].size() - 1; ++iRelVar)
			   {
				   outputs.push_back(functions[iCurrFuncId][iRelVar]);	
				   weightPerOutput.push_back(orderWeights[iCurrFuncId]);		   
				   overallWeight+=orderWeights[iCurrFuncId];
			   }			   		  		 
		   }
		   		   
		  vec<lbool> current_model;
		  assert (model.size() != 0);
		  model.copyTo(current_model);
		  vec<Lit> stored_assumptions;
		  assumptions.copyTo(stored_assumptions);
			
		  for (size_t i =0; i < outputs.size(); i++){
			if (current_model[var(outputs[i])] == l_False){
			  assumptions.push(~outputs[i]);
			} else {
			  assumptions.push(~outputs[i]);

			  solver->setConfBudget(Torc::Instance()->GetMsConflictsPerSatCall());

			  auto res = searchSATSolver(solver, assumptions);
			  
			  assumptions.pop();
			  
			  solver->budgetOffConflict();    
			 			  
				   
			  if (res == l_True) {
				solver->model.copyTo(current_model);
				uint64_t currOriginalCost = computeOriginalCost(solver->model); 						   
				if (currOriginalCost < best_cost) {	
				  ++improvingModelsSoFar;		
				  saveModel(solver->model, currOriginalCost);				  
				  best_cost = currOriginalCost;
				  if (verbosity > 0 && !Torc::Instance()->GetPrintEveryModel()) printf("o %" PRId64 " \n", currOriginalCost);        
				  if (verbosity > 0) printf("c timeo %u %" PRId64 " \n", (unsigned)ceil(Torc::Instance()->WallTimePassed()), currOriginalCost);
				  newCost = computeCostModel(solver->model, orderWeights[current_function_id])/orderWeights[current_function_id];    
				  if (verbosity > 2) printf("c newCost % " PRId64 "\n", newCost);				  
			    }
			    assumptions.push(~outputs[i]);
			  } else
			  {
				  badWeight+=weightPerOutput[i];
				  assumptions.push(outputs[i]);
			  }
			  
			  if (verbosity > 2) printf("c still-reachable-cost %" PRId64 "; the cost of the best model %" PRId64 "\n", overallWeight - badWeight, best_cost);
			  if (overallWeight - badWeight <= best_cost)
			  {
				  if (verbosity > 0) printf("c Stopping OBV-BS, since the still-reachable-cost %" PRId64 " is greater than or equal than the cost of the best model %" PRId64 "\n", overallWeight - badWeight, best_cost);
				  break;
			  }
			  
			  if (StopDueToModelPerSecThr(isModelPerSecThrApplied, improvingModelsSoFar, start))
			  {
				  if (Torc::Instance()->GetWobsAdaptiveStoppedStopMs() == 1 && Torc::Instance()->GetMsMaxEpochs() != 0)
				  {
					  Torc::Instance()->SetMsMaxEpochs(0);
					   if (verbosity > 1) printf("c Stopping OBV-BS and mutation-optimization (the last part was requested by the user, since wobs_adaptive_stopped_stop_ms=%d and ms_max_epochs!=0) forever due to low model-per-second threshold. Models = %u; Time passed = %f; Model-per-second = %f < user-threshold = %f\n", 
					     Torc::Instance()->GetWobsAdaptiveStoppedStopMs(), improvingModelsSoFar, std::chrono::duration<double>(std::chrono::high_resolution_clock::now()-start).count(), improvingModelsSoFar / std::chrono::duration<double>(std::chrono::high_resolution_clock::now()-start).count(), Torc::Instance()->GetMsModelPerSecThr());
				  }
				  else
				  {
					   if (verbosity > 1) printf("c Stopping OBV-BS due to low model-per-second threshold. Models = %u; Time passed = %f; Model-per-second = %f < user-threshold = %f\n", 
				    	improvingModelsSoFar, std::chrono::duration<double>(std::chrono::high_resolution_clock::now()-start).count(), improvingModelsSoFar / std::chrono::duration<double>(std::chrono::high_resolution_clock::now()-start).count(), Torc::Instance()->GetMsModelPerSecThr());
				  }
				  break;
			  }
			  
			
			}
		  }
		  
		  if (Torc::Instance()->GetMsMaxEpochs() != 0 && Torc::Instance()->GetMsModelPerSecThr() != 0 && Torc::Instance()->GetWobsAdaptiveNotStoppedMSThrMult() != 1 && !StopDueToModelPerSecThr(isModelPerSecThrApplied, improvingModelsSoFar, start))
		  {
			  const auto oldThr = Torc::Instance()->GetMsModelPerSecThr();
			  const auto newThr = Torc::Instance()->GetMsModelPerSecThr() * Torc::Instance()->GetWobsAdaptiveNotStoppedMSThrMult();
			  if (verbosity > 1) printf("c Changing the threshold of the adaptive strategy for MS from %f to %f (by multiplying by wobs_adaptive_not_stopped_ms_thr_mult=%f), since OBV-BS wasn't stopped by it\n", oldThr, newThr, Torc::Instance()->GetWobsAdaptiveNotStoppedMSThrMult());
			  Torc::Instance()->SetMsModelPerSecThr(newThr);
		  }
		  
		  stored_assumptions.copyTo(assumptions);		  
		  if (verbosity > 1) printf("c Finished OBV-BS\n");
	};
	
	auto MutationSampling = [&](uint64_t& newCost)
	{
	   CSetInScope<double> randFreqForMublox(solver->random_var_freq, Torc::Instance()->GetMsRndFreqForMublox());
	   CSetInScope<unsigned> minLBDFrozenClauseForMublox(solver->lbLBDFrozenClause, (unsigned)Torc::Instance()->GetMsMinLBDFrozenClauseForMublox());	   

	   std::chrono::high_resolution_clock::time_point msStart = std::chrono::high_resolution_clock::now();
	   unsigned improvingModelsSoFar = 0;
	   
	   const int msObvStrat = Torc::Instance()->GetMsObvStrat();
	   const int initAssumpsNum = assumptions.size();
	   const bool isModelPerSecThrApplied = Torc::Instance()->GetMsModelPerSecThr() != 0. && (mutationSamplingTimesInvoked == 0 || !Torc::Instance()->GetMsModelPerSecOnlyForFirstInv());
	   const bool isPropPerModelThrApplied = Torc::Instance()->GetMsPropPerModelThr() != 0;
	   uint64_t startProp = solver->propagations;
	   
	   if (verbosity > 1) printf("c Entering mutation sampling\n");	   
	   
	   auto polConservative = Torc::Instance()->GetPolConservative();
	   assert(polConservative);
	   auto polOptimistic = Torc::Instance()->GetPolOptimistic();
	   if (Torc::Instance()->GetMsDisableTorc())
	   {
		   Torc::Instance()->SetPolOptimistic(false);   
	   }		  		   
	   
	   vec<lbool> startingModel;
	   best_model.copyTo(startingModel);
	   if (Torc::Instance()->GetMsSortLitsStrat() >= 2 && mutLitsScores.empty())
	   {
		   mutLitsScores.resize(best_model.size(), 0);
	   }
	   
			
	   bool goodEpoch = true;		   
	   
	   vector<Lit> relLitsSortedIncreasing;
	   relLitsSortedIncreasing.reserve(maxsat_formula->nSoft());
	   
	   for (int iCurrFuncId = functions.size() - 1; iCurrFuncId >= current_function_id; --iCurrFuncId)
	   {
		   size_t szBefore = relLitsSortedIncreasing.size();
		   for (int iRelVar = functions[iCurrFuncId].size() - 1; iRelVar >= 0; --iRelVar)
		   {
			   relLitsSortedIncreasing.push_back(functions[iCurrFuncId][iRelVar]);			   
		   }
		   if (Torc::Instance()->GetMsSortLitsStrat() >= 1)
		   {
				std::shuffle(relLitsSortedIncreasing.begin() + szBefore, relLitsSortedIncreasing.end(), std::mt19937{std::random_device{}()});
				
				if (Torc::Instance()->GetMsSortLitsStrat() == 2)
				{
					std::sort(relLitsSortedIncreasing.begin() + szBefore, relLitsSortedIncreasing.end(), [&](const Lit& l1, const Lit& l2)
					{
						return mutLitsScores[var(l2)] < mutLitsScores[var(l1)];
					});   
				}
				if (Torc::Instance()->GetMsSortLitsStrat() == 3)
				{
					std::sort(relLitsSortedIncreasing.begin() + szBefore, relLitsSortedIncreasing.end(), [&](const Lit& l1, const Lit& l2)
					{
						return mutLitsScores[var(l2)] > mutLitsScores[var(l1)];
					});   
				}
				
		   }		  		  
	   }		 
	
	   vector<Lit> crossEpochBadLits;
	   crossEpochBadLits.reserve(maxsat_formula->nSoft());

	   for (int iEpoch = 0; iEpoch < Torc::Instance()->GetMsMaxEpochs() && goodEpoch && !StopDueToModelPerSecThr(isModelPerSecThrApplied, improvingModelsSoFar, msStart) && !StopDueToPropPerModelThr(isPropPerModelThrApplied, improvingModelsSoFar, startProp); ++iEpoch)
	   {			   
		   goodEpoch = false;
		   int satInvocationsPerEpoch = 0;
		   // The vector of optimizing mutations in this epoch
		   vector<vector<bool>> optMutations;
		   
		   vector<Lit> remainingRelLits;
		   remainingRelLits.reserve(maxsat_formula->nSoft());
		   
		   if (Torc::Instance()->GetMsInitBadStrat() != 0 || iEpoch == 0)
		   {
			   for (Lit relLit : relLitsSortedIncreasing)
			   {
				   // Assert the relaxation literal is positive
				   assert(sign(relLit) == false);
				   // With TORC, the soft clause is falsified iff the relaxation literal is true
				   bool isSoftClsFalsified = (Torc::Instance()->GetMsInitBadStrat() == 2 ? startingModel : best_model)[var(relLit)] == l_True;
				   if (isSoftClsFalsified)
				   {
					   remainingRelLits.push_back(relLit);
					   if (Torc::Instance()->GetMsInitBadStrat() == 0)
					   {
						   crossEpochBadLits.push_back(relLit);
					   }
					   
				   }				   
			   }
		   }
		   else
		   {
			   remainingRelLits = crossEpochBadLits;
		   }
		   
		   if (verbosity > 1) printf("c Mutation sampling: epoch %d < %d starting with %zu remaining literals\n", iEpoch, Torc::Instance()->GetMsMaxEpochs(), remainingRelLits.size());
		   
		   int statSat = 0;
		   int statUnsat = 0;
		   int statConfThr = 0;
		   
		   unsigned moUncheckedRelLitsInd = relLitsSortedIncreasing.size() - 1;
		   
		   while (!remainingRelLits.empty() && (satInvocationsPerEpoch < Torc::Instance()->GetMsSatCallsPerEpoch() || isModelPerSecThrApplied) && !StopDueToModelPerSecThr(isModelPerSecThrApplied, improvingModelsSoFar, msStart) && !StopDueToPropPerModelThr(isPropPerModelThrApplied, improvingModelsSoFar, startProp))
		   {				   				 			    
			   Lit relLit = remainingRelLits.back();
			   remainingRelLits.pop_back();
			   // Assert the relaxation literal is positive and its clause is falsified
			   assert((sign(relLit) == false && startingModel[var(relLit)] == l_True));
							   
			   solver->setConfBudget(Torc::Instance()->GetMsConflictsPerSatCall());
			   if (verbosity > 2) printf("c Calling SAT for %d time (out of %d allowed in one epoch) with %zu relaxation variables remaining\n", satInvocationsPerEpoch, Torc::Instance()->GetMsSatCallsPerEpoch(), remainingRelLits.size());
			   
			   if (Torc::Instance()->GetMsStayNearStartingModel())
			   {
				   // We want to stay near the starting model
				   Torc::Instance()->SkipFillingSolverPolarity() = true;
			   }
			   
			   if ((msObvStrat > 0 && msObvStrat <= 5) || msObvStrat == 10)
			   {
				   while (relLitsSortedIncreasing[moUncheckedRelLitsInd] != relLit)
				   {
					   const Lit& obvLit = relLitsSortedIncreasing[moUncheckedRelLitsInd];
					   // The literal must be positive
					   assert(sign(obvLit) == false);
					   assumptions.push(model[var(obvLit)] == l_True ? obvLit : ~obvLit); 
					   assert(moUncheckedRelLitsInd != 0);
					   --moUncheckedRelLitsInd;					   
				   }
				   
				   if (msObvStrat > 3)
				   {
					   for (unsigned i = moUncheckedRelLitsInd - 1; i != (unsigned)-1; --i)
					   {
						   const Lit& obvLit = relLitsSortedIncreasing[i];
							// The literal must be positive
						   assert(sign(obvLit) == false);
						   assumptions.push(model[var(obvLit)] == l_True ? obvLit : ~obvLit); 
					   }
				   }
			   }
			   
			   assumptions.push(~relLit); 
			   auto currRes = searchSATSolver(solver, assumptions);
			   assumptions.pop();	
			   
  	           if ((msObvStrat > 3 && msObvStrat <= 5) || msObvStrat == 10)
			   {
				   for (unsigned i = moUncheckedRelLitsInd - 1; i != (unsigned)-1; --i)
				   {
					   assumptions.pop(); 
				   }
			   }
			   
			   if (((msObvStrat == 2 || msObvStrat == 4) && currRes != l_True) ||
				   ((msObvStrat == 3 || msObvStrat == 5) && (currRes != l_True || computeOriginalCost(solver->model) >= best_cost)))
			   {
				   solver->setConfBudget(Torc::Instance()->GetMsConflictsPerSatCall());
				   vec<Lit> savedAssumps;
				   assumptions.copyTo(savedAssumps);		
				   assumptions.resize(initAssumpsNum);
				   				   
				   assumptions.push(~relLit); 
				   currRes = searchSATSolver(solver, assumptions);				   
				   
				   savedAssumps.moveTo(assumptions);				   
			   }
			   
			   if (((msObvStrat == 6 || msObvStrat == 8) && currRes != l_True) ||
				   ((msObvStrat == 7 || msObvStrat == 9) && (currRes != l_True || computeCostModel(solver->model) >= best_cost)))
			   {
				  solver->setConfBudget(Torc::Instance()->GetMsConflictsPerSatCall());
			      vec<Lit> savedAssumps;
			      assumptions.copyTo(savedAssumps);		
			      
				  while (relLitsSortedIncreasing[moUncheckedRelLitsInd] != relLit)
				  {
					  const Lit& obvLit = relLitsSortedIncreasing[moUncheckedRelLitsInd];
					  // The literal must be positive
					  assert(sign(obvLit) == false);
					  assumptions.push(model[var(obvLit)] == l_True ? obvLit : ~obvLit); 
					  --moUncheckedRelLitsInd;					   
				  }
				   
				  if (msObvStrat >= 8 && msObvStrat <= 9)
				  {
					  for (unsigned i = moUncheckedRelLitsInd - 1; i != (unsigned)-1; --i)
					  {
					      const Lit& obvLit = relLitsSortedIncreasing[i];
						  // The literal must be positive
						  assert(sign(obvLit) == false);
						  assumptions.push(model[var(obvLit)] == l_True ? obvLit : ~obvLit); 
					  }
				  }
				  
				  assumptions.push(~relLit); 	
				  searchSATSolver(solver, assumptions);
				  savedAssumps.moveTo(assumptions);

			      ++satInvocationsPerEpoch;
			   }
			   		   
			   
			   Torc::Instance()->SkipFillingSolverPolarity() = false;
			   
			   ++satInvocationsPerEpoch;
			   
			   if (currRes == l_True)
			   {				
				   ++statSat;		   
				   uint64_t currOriginalCost = computeOriginalCost(solver->model); 						   
				   if (verbosity > 2) printf("c SAT; cost % " PRId64 "\n", currOriginalCost);
				   
				   auto Sift = [&](vector<Lit>& toSift) 
					{
						toSift.erase(std::remove_if(toSift.begin(), 
							  toSift.end(),
							  [&](Lit& l){return solver->model[var(l)] != l_True; }), toSift.end());
					};
					
					if (currOriginalCost < best_cost) {			
					  ++improvingModelsSoFar;
					  saveModel(solver->model, currOriginalCost);
					  solver->model.copyTo(best_model);
					  best_cost = currOriginalCost;
					  if (verbosity > 0 && !Torc::Instance()->GetPrintEveryModel()) printf("o %" PRId64 " \n", currOriginalCost);        
					  if (verbosity > 0) printf("c timeo %u %" PRId64 " \n", (unsigned)ceil(Torc::Instance()->WallTimePassed()), currOriginalCost);
					  goodEpoch = true;        
					  newCost = computeCostModel(best_model, orderWeights[current_function_id])/orderWeights[current_function_id];    
					  if (verbosity > 2) printf("c newCost % " PRId64 "\n", newCost);
					  if (Torc::Instance()->GetMsMutationClasses() > 0) 
					  {
							vector<bool> currMutation(solver->model.size(), false);
							for (int i = 0; i < solver->model.size(); ++i)
							{
								if (solver->model[i] != startingModel[i])
								{
									currMutation[i] = true;
								}							
							}
							optMutations.emplace_back(move(currMutation));    
					  }
					  if (Torc::Instance()->GetMsSortLitsStrat() >= 2)
					  {
							mutLitsScores[var(relLit)]+=8;
					  }                    
					}
					
					if (Torc::Instance()->GetMsSiftRemaining() && (currOriginalCost < best_cost || !Torc::Instance()->GetMsSiftRemainingOnlyWhenOptimized()))
					{
						Sift(remainingRelLits);
					}
					
					if (Torc::Instance()->GetMsInitBadStrat() == 0)
					{
						Sift(crossEpochBadLits);						
					}
			   }
			   else if (currRes == l_False)
			   {		
   					if (Torc::Instance()->GetMsSortLitsStrat() >= 2)
					{
						++mutLitsScores[var(relLit)];
					}                    

				   ++statUnsat;						   
				   if (verbosity > 2) printf("c UNSAT\n");
			   }
			   else
			   {
   					if (Torc::Instance()->GetMsSortLitsStrat() >= 2)
					{
						++mutLitsScores[var(relLit)];
					}                    

				   ++statConfThr; 
				   if (verbosity > 2) printf("c Conflict threshold reached\n");
			   }			
		   }
		   
		   if (msObvStrat > 0)
		   {
			   assumptions.resize(initAssumpsNum);			    
		   }
		   
		   
		   if (verbosity > 1) printf("c Created close solutions: (sat,unsat,confthr)=(%d,%d,%d). Creating mutation combination classes\n", statSat, statUnsat, statConfThr);
		   
		   bool mutCombClassImproved = true;
		   for (int iMutClass = 0; iMutClass < Torc::Instance()->GetMsMutationClasses() && mutCombClassImproved && !StopDueToModelPerSecThr(isModelPerSecThrApplied, improvingModelsSoFar, msStart) && !StopDueToPropPerModelThr(isPropPerModelThrApplied, improvingModelsSoFar, startProp); ++iMutClass)
		   {
			   if (verbosity > 1) printf("c Class %d < %d starting. %d mutations.\n", iMutClass, Torc::Instance()->GetMsMutationClasses(), (int)optMutations.size());
			   
			   mutCombClassImproved = false;
			   vector<vector<bool>> mutCombs;
			   
			   for (int i = 0; i < (int)optMutations.size(); ++i)
			   {
				 for (int j = i + 1; j < (int)optMutations.size(); ++j)
				 { 
				   // Combine mutations i and j					   
				   vector<bool> combMut(best_model.size(), false);
				   vec<lbool> newModel;
				   for (int iVar = 0; iVar < best_model.size(); ++iVar)
				   {
					   combMut[iVar] = optMutations[i][iVar] | optMutations[j][iVar];
					   auto& mu0 = Torc::Instance()->GetMsMutCombUseBestModel() ? best_model : startingModel;
					   newModel.push(combMut[iVar] ? (mu0[iVar] == l_True ? l_False : l_True) : mu0[iVar]);
				   }
				   
				   uint64_t newModelOriginalCost = computeOriginalCost(newModel); 
				   
				   if (newModelOriginalCost < best_cost)
				   {
					   mutCombs.emplace_back(move(combMut));  
					   
					   bool betterModelFound = false;
					   if (Torc::Instance()->GetMsConflictsLookNearMutation() > 0)
					   {
							  vec<lbool> saved_user_phase_saving;
							  solver->_user_phase_saving.copyTo(saved_user_phase_saving);
							  
							  solver->_user_phase_saving.clear();
							  for (int i = 0; i < newModel.size(); i++){
								solver->_user_phase_saving.push(newModel[i]);		
							  } 
							  
							   solver->setConfBudget(Torc::Instance()->GetMsConflictsLookNearMutation());
							   
							   auto currRes = searchSATSolver(solver);
							   
							   if (currRes == l_True)
							   {
								   uint64_t currResCost = computeOriginalCost(solver->model);
								   if (currResCost < best_cost)
								   {
									   solver->model.copyTo(newModel);
									   newModelOriginalCost = computeOriginalCost(newModel); 
									   betterModelFound = true;
								   }								   
							   }
							   
							   if (!betterModelFound)
							   {
								   solver->_user_phase_saving.clear();
								   saved_user_phase_saving.moveTo(solver->_user_phase_saving);
							   }
													   
						}
						else
						{
						   betterModelFound = isRealModel(newModel);
						}
						   
						   
						if (betterModelFound)
						{
						   ++improvingModelsSoFar;
						   saveModel(newModel, newModelOriginalCost);
						   newModel.copyTo(best_model);
						   best_cost = newModelOriginalCost;
						   if (verbosity > 1) printf("c Real model (j,j)=(%d,%d) out of %d\n", i, j, (int)optMutations.size());
						   if (verbosity > 0 && !Torc::Instance()->GetPrintEveryModel()) printf("o %" PRId64 " \n", newModelOriginalCost);        
						   if (verbosity > 0) printf("c timeo %u %" PRId64 " \n", (unsigned)ceil(Torc::Instance()->WallTimePassed()), newModelOriginalCost);
						   goodEpoch = true; 
						   mutCombClassImproved = true;
						   newCost = computeCostModel(best_model, orderWeights[current_function_id])/orderWeights[current_function_id];
						}							
				   }					   				  
				 }  
			   }	
							   
			   optMutations = move(mutCombs);
			   mutCombs.clear();
		   }
		   
		   if (goodEpoch)
		   {
			   startingModel.clear();
			   best_model.copyTo(startingModel);
			   solver->_user_phase_saving.clear();
				for (int i = 0; i < best_model.size(); i++){
					solver->_user_phase_saving.push(best_model[i]);		
				}
		   }
	   }
	   
	   if (StopDueToModelPerSecThr(isModelPerSecThrApplied, improvingModelsSoFar, msStart))
	   {
		   if (verbosity > 1) printf("c Stopping mutation-optimization forever due to low model-per-second threshold. Models = %u; Time passed = %f; Model-per-second = %f < user-threshold = %f\n", 
				improvingModelsSoFar, std::chrono::duration<double>(std::chrono::high_resolution_clock::now()-msStart).count(), improvingModelsSoFar / std::chrono::duration<double>(std::chrono::high_resolution_clock::now()-msStart).count(), Torc::Instance()->GetMsModelPerSecThr());
		   Torc::Instance()->SetMsMaxEpochs(0);
	   }
	   
	  if (StopDueToPropPerModelThr(isPropPerModelThrApplied, improvingModelsSoFar, startProp))
	  {
		   if (verbosity > 1) printf("c Stopping mutation-optimization forever due to low propagation-per-model threshold. Models = %u; Propagations passed = %llu; Propagations-per-model = %f > user-threshold = %f\n",
			improvingModelsSoFar, (unsigned long long)(solver->propagations - startProp), (double)(solver->propagations - startProp) / (double)improvingModelsSoFar, Torc::Instance()->GetMsPropPerModelThr());
		   Torc::Instance()->SetMsMaxEpochs(0);	  				  
	  }

	    
	   Torc::Instance()->SetPolOptimistic(polOptimistic);
	   solver->budgetOff();
	   ++mutationSamplingTimesInvoked;
	   if (verbosity > 1) printf("c Mutation sampling done\n");
	};
		
		
  int modelCount = 0;
  bool obvbsInvoked = false;
  
  InitSatLike();  
  
  for(bool firstLoop = true; true; firstLoop = false){
    sat:

    res = searchSATSolver(solver, assumptions);
    
     if (firstLoop && res == l_False) 
     {
		 printAnswer(_UNSATISFIABLE_);
          exit(_UNSATISFIABLE_);
	 }
    
    if (Torc::Instance()->GetNuwlsMode() && res == l_True && maxsat_formula->using_nuwls == false && maxsat_formula->nTotalLitCount() < 350000000)
    {
      auto currCost = computeOriginalCost(solver->model);
      saveModel(solver->model, currCost);
      
      cout << "o " << currCost << endl;
      if (verbosity > 0) printf("c timeo %u %" PRId64 " \n", (unsigned)ceil(Torc::Instance()->WallTimePassed()), currCost);	
      //if (maxsat_formula->using_nuwls == false && maxsat_formula->nTotalLitCount() < 350000000)
      {
        maxsat_formula->using_nuwls = true;
        NUWLS nuwls_solver;
        nuwls_solver.problem_weighted = 1;
        build_nuwls_clause_structure();

        nuwls_solver.build_instance(maxsat_formula->nuwls_nvars, maxsat_formula->nuwls_nclauses, maxsat_formula->nuwls_topclauseweight,
                                      maxsat_formula->nuwls_clause_lit, maxsat_formula->nuwls_clause_lit_count, maxsat_formula->nuwls_clause_weight);

        cout << "c build NuWLS instance done!" << endl;
        cout << "c changing to NuWLS solver!!!" << endl;
        nuwls_solver.settings();
        
        vector<int> init_solu(maxsat_formula->nuwls_nvars + 1);
        for (int i = 0; i < maxsat_formula->nuwls_nvars; ++i)
        {
          if (solver->model[i] == l_False)
            init_solu[i + 1] = 0;
          else
            init_solu[i + 1] = 1;
        }
        
        nuwls_solver.init(init_solu);
        nuwls_solver.opt_unsat_weight = currCost;
        start_timing(); 
        
        const auto nuwlsTimeLimit = Torc::Instance()->GetNuwlsIsExternalTimeLimit() ? Torc::Instance()->GetNuwlsExternalTimeLimit() : nuwls_solver.NUWLS_TIME_LIMIT;
        cout << "c nuwlsTimeLimit = " << nuwlsTimeLimit << endl;
        
        int time_limit_for_ls = nuwlsTimeLimit;
        
        int step = 0;
        // if (nuwls_solver.if_using_neighbor)
        {
          for (step = 1; step < nuwls_solver.max_flips; ++step)
          {
            if (nuwls_solver.hard_unsat_nb == 0)
            {
              if (nuwls_solver.soft_unsat_weight < nuwls_solver.opt_unsat_weight)
              {
                nuwls_solver.best_soln_feasible = 1;
                nuwls_solver.local_soln_feasible = 1;
                nuwls_solver.max_flips = step + nuwls_solver.max_non_improve_flip;
                time_limit_for_ls = get_runtime() + nuwlsTimeLimit;

                nuwls_solver.opt_unsat_weight = nuwls_solver.soft_unsat_weight;
                cout << "o " << nuwls_solver.opt_unsat_weight << endl;
                if (verbosity > 0) printf("c timeo %u %" PRId64 " \n", (unsigned)ceil(Torc::Instance()->WallTimePassed()), nuwls_solver.opt_unsat_weight);	
                for (int v = 1; v <= nuwls_solver.num_vars; ++v)
                {
                  if (nuwls_solver.cur_soln[v] == 0)
                    solver->model[v - 1] = l_False;
                  else
                    solver->model[v - 1] = l_True;
                }
                //best_cost = nuwls_solver.opt_unsat_weight;
                uint64_t oriCost = nuwls_solver.opt_unsat_weight; // computeOriginalCost(solver->model);
                // cout << "o " << oriCost << endl;
                saveModel(solver->model, oriCost);
                // solver->model.copyTo(best_model);
				cout << "o " << nuwls_solver.opt_unsat_weight << endl;
                if (nuwls_solver.opt_unsat_weight == 0)
                  break;
              }
            }
            int flipvar = nuwls_solver.pick_var();
            nuwls_solver.flip(flipvar);
            nuwls_solver.time_stamp[flipvar] = step;
            if (step % 1000 == 0)
            {
              if (get_runtime() > time_limit_for_ls)
              {
                cout << "c " << get_runtime() << endl;
                break;
              }
            }
          }
        }
        nuwls_solver.free_memory();
        cout << "c nuwls search done!" << endl;
        cout << "c step " << step << " get_runtime " << get_runtime() << " time_limit_for_ls" << time_limit_for_ls << endl;
      }
    }
    
    if (res == l_True) {
	   SatLike(solver);
	     
       if (!repair){
        nbSatisfiable++;

		if (verbosity > 2) printf("c weight %llu with size %d\n",orderWeights[current_function_id],functions[current_function_id].size());
        uint64_t newCost = computeCostModel(solver->model, orderWeights[current_function_id])/orderWeights[current_function_id];
        uint64_t originalCost = computeOriginalCost(solver->model);
		if (verbosity > 2) printf("c objective function %d = o %" PRId64 " \n",current_function_id,newCost);
        if(best_cost > originalCost) {			
          saveModel(solver->model, originalCost);
          solver->model.copyTo(best_model);
          best_cost = originalCost;
          if (verbosity > 0 && !Torc::Instance()->GetPrintEveryModel()) printf("o %" PRId64 " \n", originalCost);
          if (verbosity > 0) printf("c timeo %u %" PRId64 " \n", (unsigned)ceil(Torc::Instance()->WallTimePassed()), originalCost);
          	      
		  ++modelCount;
		  
		  if (Torc::Instance()->GetWeightedObvBsFirstIterStrat() != 0 && !obvbsInvoked)
		  {
			  ObvBs(newCost);
			  obvbsInvoked = true;
		  }
		  else if (Torc::Instance()->GetMsMaxEpochs() > 0)
		  {
			  MutationSampling(newCost);
		  }
        }
			
        if (newCost < rhs[current_function_id])
          rhs[current_function_id] = newCost;

        if (newCost == 0){		  
    // no need for cardinality constraint
          goto unsat;

        } else {	
    // no cardinality constraint created
          if (!encoder_created[current_function_id]){
            if (newCost - 1 == 0){
              encodingAssumptions.clear();
              functions_to_assumptions[current_function_id].clear();
              for (int i = 0; i < functions[current_function_id].size(); i++){
                functions_to_assumptions[current_function_id].push(~functions[current_function_id][i]);
                encodingAssumptions.push(~functions[current_function_id][i]);
              }
            } else {
			  if (verbosity > 2) printf("c creating encoder with id = %d and value = %llu\n",current_function_id,(unsigned long long)rhs[current_function_id]);
              encoders[current_function_id]->buildCardinality(solver, functions[current_function_id], newCost-1);
              if (encoders[current_function_id]->hasCardEncoding()){
                encoder_created[current_function_id] = true;
                encoders[current_function_id]->incUpdateCardinality(solver, functions[current_function_id], newCost-1, encodingAssumptions);
                assert(encodingAssumptions.size() == 1);

                functions_to_assumptions[current_function_id].clear();
                functions_to_assumptions[current_function_id].push(encodingAssumptions[0]);
              }
            }
          } else {
			if (verbosity > 2) printf("c updating the cost to %llu\n",newCost-1);
            encodingAssumptions.clear();
            encoders[current_function_id]->incUpdateCardinality(solver, functions[current_function_id], newCost-1, encodingAssumptions);
            assert(encodingAssumptions.size() == 1);

            functions_to_assumptions[current_function_id].clear();
            functions_to_assumptions[current_function_id].push(encodingAssumptions[0]);
          }
        }

        
        assumptions.clear();
        for (int i = 0; i <= current_function_id; i++){
          for (int j = 0; j < functions_to_assumptions[i].size(); j++){
            assumptions.push(functions_to_assumptions[i][j]);
      //printf("z = %d\n",var(functions_to_assumptions[i][j]));
          }
        }

      } else {
  // perform a linear search by decreasing the repair_cost
        uint64_t newCost = computeCostModel(solver->model, orderWeights[current_function_id])/orderWeights[current_function_id];
        uint64_t originalCost = computeOriginalCost(solver->model);
  //printf("c o %" PRId64 " \n", originalCost);
  //printf("repair_cost = %llu\n",repair_cost);
        if(best_cost > originalCost) {
          saveModel(solver->model, originalCost);
          solver->model.copyTo(best_model);
          best_cost = originalCost;
          repair_cost = best_cost - 1;
          if (verbosity > 0 && !Torc::Instance()->GetPrintEveryModel()) printf("o %" PRId64 " \n", originalCost);
          if (verbosity > 0) printf("c timeo %u %" PRId64 " \n", (unsigned)ceil(Torc::Instance()->WallTimePassed()), originalCost);
          if (Torc::Instance()->GetMsMaxEpochs() > 0 && Torc::Instance()->GetMsAfterRepair())
		  {
			  MutationSampling(newCost);
		  }          
		  ++modelCount;
        } else {
          repair_cost -= 1;
        }

  // rescale
        for (int i = 0; i < rhs.size(); i++){
          uint64_t value = repair_cost/orderWeights[i];
          if (value > (uint64_t)functions[i].size())
            value = functions[i].size();
          if (value != ub_rhs[i]){
            ub_rhs[i] = value;
          }
        }

        if (!pb->hasPBEncoding()){
          pb->encodePB(solver, pb_function, pb_coeffs, repair_cost);
        }
        else
          pb->updatePB(solver, repair_cost);

        if (all_weights){
          for (int i = 0; i < functions_to_assumptions.size(); i++){
            functions_to_assumptions[i].clear();
            if (encoder_created[i]){
              if (ub_rhs[i] == 0){
                for (int j = 0; j < functions[i].size(); j++){
                  functions_to_assumptions[i].push(~functions[i][j]);
                }
              } else if ((uint64_t)functions[i].size() != ub_rhs[i]){
    //printf("encoding %lu\n",ub_rhs[i]);
                encoders[i]->incUpdateCardinality(solver, functions[i], ub_rhs[i], encodingAssumptions);
    //printf("encodingAssumptions.size() = %d\n",encodingAssumptions.size());
                assert(encodingAssumptions.size() == 1);
                functions_to_assumptions[i].push(encodingAssumptions[0]);
              } else {
    //printf("size if the same!\n");
              }
            } else {
        //printf("ERROR\n");
              encoders[i]->buildCardinality(solver, functions[i], ub_rhs[i]);
              if (encoders[i]->hasCardEncoding()){
                encoder_created[i] = true;
                encoders[i]->incUpdateCardinality(solver, functions[i], ub_rhs[i], encodingAssumptions);
                assert(encodingAssumptions.size() == 1);
                functions_to_assumptions[i].push(encodingAssumptions[0]);
              }
        //          assert(false);
            }
          }

          assumptions.clear();
          for (int i = 0; i < functions_to_assumptions.size(); i++){
            for (int j = 0; j < functions_to_assumptions[i].size(); j++){
              assumptions.push(functions_to_assumptions[i][j]);
        //printf("function i =%d assumption= %d\n",i,var(functions_to_assumptions[i][j]));
            }
          }
        } else
        assumptions.clear();

      }

    } else {
      unsat:
      //printf("c UNSATISFIABLE\n");
      if ((size_t)current_function_id == orderWeights.size()-1){
  // last function

        if (!complete){
          printAnswer(_SATISFIABLE_);
          exit(_SATISFIABLE_);
        }
        // ignore the complete part for now!
        if(repair){
          printAnswer(_SATISFIABLE_);
          exit(_SATISFIABLE_);
        }

        repair = true;

        if (verbosity > 1) printf("c Warn: changing to LSU algorithm.\n"); 

        if (best_cost < repair_cost){
          for (int i = 0; i < rhs.size(); i++){
            ub_rhs[i] = best_cost/orderWeights[i];
            //best_rhs[i] = rhs[i];
          }
          repair_cost = best_cost;
        }

        if (repair_cost == 0){
          printAnswer(_SATISFIABLE_);
          exit(_SATISFIABLE_);
        }

        if (all_weights){

          for (int i = 0; i < functions.size(); i++){
            for (int j =0; j < functions[i].size(); j++){
              pb_function.push(functions[i][j]);
              pb_coeffs.push(orderWeights[i]);
            }
          }

    // rescale
          for (int i = 0; i < rhs.size(); i++){
            ub_rhs[i] = repair_cost/orderWeights[i];
            if (ub_rhs[i] > (uint64_t)functions[i].size())
              ub_rhs[i] = functions[i].size();
      //printf("i = %d rhs= %lu size= %d weigth=%llu\n",i,ub_rhs[i],functions[i].size(),orderWeights[i]);
          }

          for (int i = 0; i < functions_to_assumptions.size(); i++){
            functions_to_assumptions[i].clear();
      //printf("rhs = %lu\n",ub_rhs[i]);
            if (encoder_created[i]){
              if (ub_rhs[i] == 0){
                for (int j = 0; j < functions[i].size(); j++){
                  functions_to_assumptions[i].push(~functions[i][j]);
                }
              } else if ((uint64_t)functions[i].size() != ub_rhs[i]){
                encoders[i]->incUpdateCardinality(solver, functions[i], ub_rhs[i], encodingAssumptions);
                assert(encodingAssumptions.size() == 1);
                functions_to_assumptions[i].push(encodingAssumptions[0]);
              }
            } else {
        //printf("ERROR\n");
              encoders[i]->buildCardinality(solver, functions[i], ub_rhs[i]);
              if (encoders[i]->hasCardEncoding()){
                encoder_created[i] = true;
                encoders[i]->incUpdateCardinality(solver, functions[i], ub_rhs[i], encodingAssumptions);
                assert(encodingAssumptions.size() == 1);
                functions_to_assumptions[i].push(encodingAssumptions[0]);
              }
            }
          }

          assumptions.clear();
          for (int i = 0; i < functions_to_assumptions.size(); i++){
            for (int j = 0; j < functions_to_assumptions[i].size(); j++){
              assumptions.push(functions_to_assumptions[i][j]);
            }
          }

          pb->setPBEncoding(_PB_GTE_);
          int expected_clauses = pb->predictPB(solver, pb_function, pb_coeffs, repair_cost-1);
          if (verbosity > 1) printf("c GTE auxiliary #clauses = %d\n",expected_clauses);
          if (expected_clauses >= MAX_CLAUSES) {
            if (verbosity > 1) printf("c Warn: changing to Adder encoding.\n");
            pb->setPBEncoding(_PB_ADDER_);
          }
          pb->encodePB(solver, pb_function, pb_coeffs, repair_cost-1);

        } else {

    // reverting to complete mode with original weights
          //printf("c reverting to original weights\n");
          assumptions.clear();
          pb_function.clear();
          pb_coeffs.clear();
          
          for (int i = 0; i < maxsat_formula->nSoft(); i++) {
            pb_function.push(maxsat_formula->getSoftClause(i).relaxation_vars[0]);
            pb_coeffs.push(cluster->getOriginalWeight(i));
          }

          pb->setPBEncoding(_PB_GTE_);
          int expected_clauses = pb->predictPB(solver, pb_function, pb_coeffs, repair_cost-1);
          if (verbosity > 1) printf("c GTE auxiliary #clauses = %d\n",expected_clauses);
          if (expected_clauses >= MAX_CLAUSES) {
            if (verbosity > 1) printf("c Warn: changing to Adder encoding\n");
            pb->setPBEncoding(_PB_ADDER_);
          }
          pb->encodePB(solver, pb_function, pb_coeffs, repair_cost-1);

        }

        goto sat;

      } else {
  // go to the next function
  //rhs[current_function_id];
        encodingAssumptions.clear();
        functions_to_assumptions[current_function_id].clear();
  //printf("c encoding created %d\n",encoder_created[current_function_id]);
  //printf("c objective function %d = best o %llu\n",current_function_id,rhs[current_function_id]);
        if (rhs[current_function_id] == 0){
          for (int i = 0; i < functions[current_function_id].size(); i++){
            functions_to_assumptions[current_function_id].push(~functions[current_function_id][i]);
            encodingAssumptions.push(~functions[current_function_id][i]);
          }
        } else if (encoder_created[current_function_id]){
    //printf("current function =%d\n",current_function_id);
    //    printf("c updating the cardinality to %llu\n",rhs[current_function_id]);
    //  printf("c size of function %d\n",functions[current_function_id].size());
          if ((uint64_t)functions[current_function_id].size() != rhs[current_function_id]){
            encoders[current_function_id]->incUpdateCardinality(solver, functions[current_function_id], rhs[current_function_id], encodingAssumptions);
            assert(encodingAssumptions.size() == 1);
            functions_to_assumptions[current_function_id].push(encodingAssumptions[0]);
          }
        } else {
      //printf("c creating encoder with id = %d and value = %d\n",current_function_id,rhs[current_function_id]);
          if ((uint64_t)functions[current_function_id].size() != rhs[current_function_id]){
            encoders[current_function_id]->buildCardinality(solver, functions[current_function_id], rhs[current_function_id]);
            if (encoders[current_function_id]->hasCardEncoding()){
              encoders[current_function_id]->incUpdateCardinality(solver, functions[current_function_id], rhs[current_function_id], encodingAssumptions);
              assert(encodingAssumptions.size() == 1);
              functions_to_assumptions[current_function_id].push(encodingAssumptions[0]);
              encoder_created[current_function_id] = true;
            }
          }
        }

        assumptions.clear();
        for (int i = 0; i <= current_function_id; i++){
          for (int j = 0; j < functions_to_assumptions[i].size(); j++){
            assumptions.push(functions_to_assumptions[i][j]);
      //printf("z = %d\n",var(functions_to_assumptions[i][j]));
          }
        }
        current_function_id++;
      }
    }
  }
}

// Public search method
void LinearSUClustering::search() {

  MaxSATFormulaExtended *maxsat_formula_extended =
      static_cast<MaxSATFormulaExtended *>(maxsat_formula);
  cluster->clusterWeights(maxsat_formula_extended, num_clusters);

  for (int i = 0; i < maxsat_formula_extended->getSoftClauses().size(); i++) {
    unique_weights.insert(maxsat_formula_extended->getSoftClauses()[i].weight);
  }

  std::set<uint64_t> originalWeights;
  for (int i = 0; i < maxsat_formula->nSoft(); i++) {
    originalWeights.insert(cluster->getOriginalWeight(i));
  }

  // considers the problem as a lexicographical problem using the clustering as
  // objective functions
  orderWeights.clear();
  for (std::set<uint64_t>::iterator it = unique_weights.begin();
       it != unique_weights.end(); ++it) {
    orderWeights.push_back(*it);
  }
  if (unique_weights.size() == originalWeights.size())
  {
    all_weights = true;
    printf("c all_weights = true;\n");
  }
  else
  {
	  printf("c all_weights = false;\n");
  }

  std::sort(orderWeights.begin(), orderWeights.end(), greaterThan);

  printf("c #Diff Weights= %lu | #Modified Weights= %lu\n",
         originalWeights.size(), orderWeights.size());

  //printConfiguration(is_bmo, maxsat_formula->getProblemType());
  bmoSearch();
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
Solver *LinearSUClustering::rebuildSolver(uint64_t min_weight) {

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
void LinearSUClustering::initRelaxation() {
  for (int i = 0; i < maxsat_formula->nSoft(); i++) {
    Lit l = maxsat_formula->newLiteral();
    maxsat_formula->getSoftClause(i).relaxation_vars.push(l);
    objFunction.push(l);
    coeffs.push(maxsat_formula->getSoftClause(i).weight);
  }
}

// Print LinearSU configuration.
void LinearSUClustering::print_LinearSU_configuration() {
  printf("c |  Algorithm: %23s                                             "
         "                      |\n",
         "LinearSU");

  if (maxsat_formula->getProblemType() == _WEIGHTED_) {
    if (bmoMode)
      printf("c |  BMO strategy: %20s                      "
             "                                             |\n",
             "On");
    else
      printf("c |  BMO strategy: %20s                      "
             "                                             |\n",
             "Off");

    if (bmoMode) {
      if (is_bmo)
        printf("c |  BMO search: %22s                      "
               "                                             |\n",
               "Yes");
      else
        printf("c |  BMO search: %22s                      "
               "                                             |\n",
               "No");
    }
  }
}
