#pragma once
#include <chrono>
#include <utility>
#include <vector>
#include <string>

using NSPACE::vec;

// A singleton which manages TorcOpenWbo's additional (w.r.t OpenWboInc) parameters and functionality
class Torc{
public:
   static Torc* Instance();
   
   void SetPolConservative(bool isConservative) { polIsConservative = isConservative; }
   void SetConservativeAllVars(bool isConservativeAllVars) { conservativeUseAllVars = isConservativeAllVars; }
   void SetPolOptimistic(bool isOptimistic) { polIsOptimistic = isOptimistic;}
   void SetTargetVarsBumpVal(int targetVarsBumpVal) { varTargetsBumpVal = targetVarsBumpVal; }   
   void SetBumpRelWeights(bool isBumpRelWeights) { bumpRelWeights = isBumpRelWeights; }   
   void SetTargetBumpMaxRandVal(int targetVarsBumpRandVal) { varTargetsBumpMaxRandVal = targetVarsBumpRandVal; }   
   void SetMsMutationClasses(int p) { msMutationClasses = p; }
   void SetMsConflictsPerSatCall(int p) { msConflictsPerSatCall = p; }
   void SetMsSatCallsPerEpoch(int p) { msSatCallsPerEpoch = p; }
   void SetMsMaxEpochs(int p) { msMaxEpochs = p; if (initMsMaxEpochs == -1) initMsMaxEpochs = p; }
   void SetMsMaxEpochsToInit() { msMaxEpochs = initMsMaxEpochs; }
   void SetMsDisableTorc(bool p) { msDisableTorc = p; }
   void SetMsStayNearStartingModel(bool p) { msStayNearStartingModel = p; }   
   void SetMsConflictsLookNearMutation(int p) { msConflictsLookNearMutation = p; }
   void SetMsSortLitsStrat(int p) { msSortLitsStrat = p; }
   void SetMsSiftRemainingOnlyWhenOptimized(bool p) { msSiftRemainingOnlyWhenOptimized = p; }
   void SetMsSiftRemaining(bool p) { msSiftRemaining = p; }
   void SetMsAfterRepair(bool p) { msAfterRepair = p; }
   void SetMsModelPerSecThr(double p) { msModelPerSecThr = p; }
   void SetMsPropPerModelThr(double p) { msPropPerModelThr = p; }
   void SetMsModelPerSecOnlyForFirstInv(bool p) { msModelPerSecOnlyForFirstInv = p; }
   void SetMsMutCombUseBestModel(bool p) { msMutCombUseBestModel = p; }
   void SetMsInitBadStrat(int p)  { msInitBadStrat = p; }
   void SetMsRndFreqForMublox(double p)  { msRndFreqForMublox = p; }
   void SetMsMinLBDFrozenClauseForMublox(int p)  { msMinLBDFrozenClauseForMublox = p; }
   void SetMsVerbosity(int p)  { msVerbosity = p; }   
   void SetConflToChrono(int p) { msConflToChrono = p; }
   void SetChrono(int p) { msChrono = p; }
   void SetPoContLocalImpr(int p) { poContLocalImpr = p; }
   void SetPartialSumFailItersToSwitch(int p) { partialSumFailItersToSwitch = p; }
   void SetPartialSumLayersThr(int p) { partialSumLayersThr = p; }
   void SetPartialSumConflicts(int p) { partialSumConflicts = p; }
   void SetPplcHolder(int p) { pplcHolder = p; }
   void SetMrsBeaverSizeSwitchToComplete(int p) { mrsBeaverSizeSwitchToComplete = p; }
   void SetMrsBeaverEachIterStartBestModel(int p) { mrsBeaverEachIterStartBestModel = p; }
   void SetBlockBestModel(int p) { blockBestModel = p; }
   void SetPolosatTurnOffHighLevelConfThrForIters(int p) { polosatTurnOffHighLevelConfThrForIters = p; }
   void SetOptimisticMaxSoftFraction(double p) { optimisticMaxSoftFraction = p; }
   void SetConservativeMaxSoftFraction(double p) { conservativeMaxSoftFraction = p; }
   void SetWeightedObvBsFirstIterStrat(int p) { weightedObvBsFirstIterStrat = p; }
   void SetWobsAdaptiveStoppedStopMs(int p) { wobsAdaptiveStoppedStopMs = p; }
   void SetWobsAdaptiveNotStoppedMSThrMult(double p) { wobsAdaptiveNotStoppedMSThrMult = p; }
   void SetMsObvStrat(int p) { msObvStrat = p; }
   void SetMrsBeaverPolosatRegulateStrat(int p) { mrsBeaverPolosatRegulateStrat = p; }
   void SetMrsBeaverApplySizeThrDuringInitialPolosat(int p) { mrsBeaverApplySizeThrDuringInitialPolosat = p; }
   void SetPrintEveryModel(int p) { printEveryModel = p; }
   void SetNuwlsMode(int p) { nuwlsMode = p; }   
   void SetNuwlsIsExternalTimeLimit(int p) { nuwlsIsExternalTimeLimit = p; }   
   void SetNuwlsExternalTimeLimit(int p) { nuwlsExternalTimeLimit = p; }   
   void SetSatlikeMode(int p) { satlikeMode = p; }
   void SetSatlikeInvsThr(int p) { satlikeInvsThr = p; }
   void SetSatlikeTimeThr(int p) { satlikeTimeThr = p; }
   void SetSatlikeInitTimeThr(int p) { satlikeInitTimeThr = p; }
   void SetSatlikePreInitTimeThr(int p) { satlikePreInitTimeThr = p; }
   void SetSatlikePreInitMaxClss(int p) { satlikePreInitMaxClss = p; }
   void SetSatlikeMaxFlips(int p) { satlikeMaxFlips = p; }
   void SetSatlikeMaxNonImproveFlip(int p) { satlikeMaxNonImproveFlip = p; }
   void SetSatlikeMaxFlipsReduceBeyondClsNum(int p) { satlikeMaxFlipsReduceBeyondClsNum = p; }
   void SetSatlikeReinvokeTimeThr(int p) { satlikeReinvokeTimeThr = p; }
   void SetSatlikeReinvokeMult(double p) { satlikeReinvokeMult = p; }
   void SetSatlikeMimicMse21(int p) { satlikeMimicMse21 = p; }
   void SetTotProp0s(int p) { totProp0s = p; }
   void SetTotBuildLayered(int p) { totBuildLayered = p; }
   void SetMsSatInvToReinvoke(int p) { msSatInvToReinvoke = p; }
   void SetMsSatInvToReinvokeMult(double p) { msSatInvToReinvokeMult = p; }
   void SetMsReinvokeMultThr(double p) { msReinvokeMultThr = p; }   
   void SetMsReinvokeMultThrMin(double p) { msReinvokeMultThrMin = p; }   
   
   bool GetPolConservative() const { return polIsConservative; }
   bool GetConservativeAllVars() const { return conservativeUseAllVars; } 
   bool GetPolOptimistic() const { return polIsOptimistic; }
   int GetTargetVarsBumpVal() const { return varTargetsBumpVal; }   
   bool GetBumpRelWeights() const { return bumpRelWeights; }
   int GetTargetBumpMaxRandVal() const { return varTargetsBumpMaxRandVal; }   
   int GetMsMutationClasses() const { return msMutationClasses; }
   int GetMsConflictsPerSatCall() const { return msConflictsPerSatCall; }
   int GetMsSatCallsPerEpoch() const { return msSatCallsPerEpoch; }
   int GetMsMaxEpochs() const { return msMaxEpochs; }
   bool GetMsDisableTorc() const { return msDisableTorc; }
   bool GetMsStayNearStartingModel() const { return msStayNearStartingModel; }   
   bool GetMsConflictsLookNearMutation() const { return msConflictsLookNearMutation; }   
   int GetMsSortLitsStrat() const { return msSortLitsStrat; }
   bool GetMsSiftRemainingOnlyWhenOptimized() const { return msSiftRemainingOnlyWhenOptimized; }
   bool GetMsSiftRemaining() const { return msSiftRemaining; }
   bool GetMsAfterRepair() const { return msAfterRepair; }
   double GetMsModelPerSecThr() const { return msModelPerSecThr; }
   double GetMsPropPerModelThr() const { return msPropPerModelThr; }
   bool GetMsModelPerSecOnlyForFirstInv() const { return msModelPerSecOnlyForFirstInv; }
   bool GetMsMutCombUseBestModel() const { return msMutCombUseBestModel; }
   int GetMsInitBadStrat() const  { return msInitBadStrat; }
   double GetMsRndFreqForMublox() const  { return msRndFreqForMublox; }
   int GetMsMinLBDFrozenClauseForMublox() const  { return msMinLBDFrozenClauseForMublox; }
   int GetMsVerbosity() const { return msVerbosity; }
   int GetConflToChrono() const { return msConflToChrono; }
   int GetChrono() const { return msChrono; }
   int GetPoContLocalImpr() const { return poContLocalImpr; }
   int GetPartialSumFailItersToSwitch() const { return partialSumFailItersToSwitch; }
   int GetPartialSumLayersThr() const { return partialSumLayersThr; }
   int GetPartialSumConflicts() const { return partialSumConflicts; }
   int GetPplcHolder() const { return pplcHolder; }
   int GetMrsBeaverSizeSwitchToComplete() const { return mrsBeaverSizeSwitchToComplete; }
   int GetMrsBeaverEachIterStartBestModel() const { return mrsBeaverEachIterStartBestModel; }
   int GetBlockBestModel() const { return blockBestModel; }
   int GetPolosatTurnOffHighLevelConfThrForIters() const { return polosatTurnOffHighLevelConfThrForIters; }
   double GetOptimisticMaxSoftFraction() const { return optimisticMaxSoftFraction; }
   double GetConservativeMaxSoftFraction() const { return conservativeMaxSoftFraction; }
   int GetWeightedObvBsFirstIterStrat() const { return weightedObvBsFirstIterStrat; }
   int GetWobsAdaptiveStoppedStopMs() const { return wobsAdaptiveStoppedStopMs; }
   double GetWobsAdaptiveNotStoppedMSThrMult() const { return wobsAdaptiveNotStoppedMSThrMult; }
   int GetMsObvStrat() const { return msObvStrat; }
   int GetMrsBeaverPolosatRegulateStrat() const { return mrsBeaverPolosatRegulateStrat; }
   int GetMrsBeaverApplySizeThrDuringInitialPolosat() const { return mrsBeaverApplySizeThrDuringInitialPolosat; }
   int GetPrintEveryModel() const { return printEveryModel; }
   int GetRandBump() const;
   int GetNuwlsMode() const { return nuwlsMode; }
   int GetNuwlsIsExternalTimeLimit() const { return nuwlsIsExternalTimeLimit; }   
   int GetNuwlsExternalTimeLimit() const { return nuwlsExternalTimeLimit; }   
   int GetSatlikeMode() const { return satlikeMode; }
   int GetSatlikeInvsThr() const { return satlikeInvsThr; }
   int GetSatlikeTimeThr() const { return satlikeTimeThr; }
   int GetSatlikeInitTimeThr() const { return satlikeInitTimeThr; }
   int GetSatlikePreInitTimeThr() const { return satlikePreInitTimeThr; }
   int GetSatlikePreInitMaxClss() const { return satlikePreInitMaxClss; }
   int GetSatlikeMaxFlips() const { return satlikeMaxFlips; }
   int GetSatlikeMaxNonImproveFlip() const { return satlikeMaxNonImproveFlip; }
   int GetSatlikeMaxFlipsReduceBeyondClsNum() const { return satlikeMaxFlipsReduceBeyondClsNum; }
   int GetSatlikeReinvokeTimeThr() const { return satlikeReinvokeTimeThr; }
   double GetSatlikeReinvokeMult() const { return satlikeReinvokeMult; }
   int GetSatlikeMimicMse21() const { return satlikeMimicMse21; }
   int GetTotProp0s() const { return totProp0s; }
   int GetTotBuildLayered() const { return totBuildLayered; }
   int GetMsSatInvToReinvoke() const { return msSatInvToReinvoke; }
   double GetMsSatInvToReinvokeMult() const { return msSatInvToReinvokeMult; }
   double GetMsReinvokeMultThr() const { return msReinvokeMultThr; }   
   double GetMsReinvokeMultThrMin() const { return msReinvokeMultThrMin; }   
   vec<bool>& TargetIsVarTarget() { return isVarTarget; }
   bool& SkipFillingSolverPolarity() { return skipFillingSolverPolarity; }
   
   double WallTimePassed() const;
   
   std::vector<std::pair<std::string, double>> toporParams;

private:
   Torc() : timeStart(std::chrono::high_resolution_clock::now()), polIsConservative(true), conservativeUseAllVars(true), polIsOptimistic(true), varTargetsBumpVal(113), bumpRelWeights(false), varTargetsBumpMaxRandVal(0), 	
	msMutationClasses(6), msConflictsPerSatCall(0), msSatCallsPerEpoch(0), msMaxEpochs(0), msDisableTorc(false), msStayNearStartingModel(false), msConflictsLookNearMutation(0), msSortLitsStrat(0), msSiftRemainingOnlyWhenOptimized(false), msSiftRemaining(true), msAfterRepair(false),
	msModelPerSecThr(0.), msPropPerModelThr(0.), msModelPerSecOnlyForFirstInv(true), msMutCombUseBestModel(false), msInitBadStrat(1), msRndFreqForMublox(0.), msMinLBDFrozenClauseForMublox(30), msConflToChrono(4000), msChrono(-1), poContLocalImpr(0), 
	partialSumFailItersToSwitch(0), partialSumLayersThr(10), partialSumConflicts(1000), pplcHolder(0), mrsBeaverSizeSwitchToComplete(1000000), mrsBeaverEachIterStartBestModel(0), blockBestModel(0), polosatTurnOffHighLevelConfThrForIters(0), optimisticMaxSoftFraction(1.), conservativeMaxSoftFraction(1.), 
	weightedObvBsFirstIterStrat(0), wobsAdaptiveStoppedStopMs(0), wobsAdaptiveNotStoppedMSThrMult(1.), msObvStrat(3), mrsBeaverPolosatRegulateStrat(0), mrsBeaverApplySizeThrDuringInitialPolosat(0),
	printEveryModel(0),
	nuwlsMode(0), nuwlsIsExternalTimeLimit(0), nuwlsExternalTimeLimit(0), satlikeMode(0), satlikeInvsThr(0), satlikeTimeThr(15), satlikeInitTimeThr(5), satlikePreInitTimeThr(1), satlikePreInitMaxClss(10000000), satlikeMaxFlips(10000000), satlikeMaxNonImproveFlip(10000000), satlikeMaxFlipsReduceBeyondClsNum(0), satlikeReinvokeTimeThr(60), satlikeMimicMse21(0), satlikeReinvokeMult(1.),
	totProp0s(0), totBuildLayered(0),
	msSatInvToReinvoke(0), msSatInvToReinvokeMult(1), msReinvokeMultThr(1.), initMsMaxEpochs(-1), msReinvokeMultThrMin(0.001),
	msVerbosity(1), skipFillingSolverPolarity(false) {};  // Private so that it can  not be called
   static Torc* m_pInstance;
   
   std::chrono::high_resolution_clock::time_point timeStart;
   
   bool polIsConservative;
   bool conservativeUseAllVars;
   bool polIsOptimistic;
   int varTargetsBumpVal;  
   bool bumpRelWeights;    
   int varTargetsBumpMaxRandVal;  
   
   // Mutation-based optimizing-sampling after each model
   int msMutationClasses;
   int msConflictsPerSatCall;
   int msSatCallsPerEpoch;
   int msMaxEpochs;
   bool msDisableTorc;
   bool msStayNearStartingModel;
   int msConflictsLookNearMutation;
   int msSortLitsStrat; 
   bool msSiftRemainingOnlyWhenOptimized;
   bool msSiftRemaining;
   bool msAfterRepair;
   // Stop mutation-optimization forever when the improving models-per-second threshold is too low
   double msModelPerSecThr;
   // Stop mutation-optimization forever when the improving propagation-per-model threshold is too high
   double msPropPerModelThr;
   bool msModelPerSecOnlyForFirstInv;
   bool msMutCombUseBestModel;
   int msInitBadStrat; 
   double msRndFreqForMublox;
   int msMinLBDFrozenClauseForMublox;
   int msConflToChrono;
   int msChrono;
   int poContLocalImpr;
   int partialSumFailItersToSwitch;
   int partialSumLayersThr;
   int partialSumConflicts;
   int pplcHolder;
   int mrsBeaverSizeSwitchToComplete;
   int mrsBeaverEachIterStartBestModel;   
   int blockBestModel;
   int polosatTurnOffHighLevelConfThrForIters;
   double optimisticMaxSoftFraction;
   double conservativeMaxSoftFraction;
   int weightedObvBsFirstIterStrat;
   int wobsAdaptiveStoppedStopMs;
   double wobsAdaptiveNotStoppedMSThrMult;
   int msObvStrat;
   int mrsBeaverPolosatRegulateStrat;
   int mrsBeaverApplySizeThrDuringInitialPolosat;
   int printEveryModel;
   int nuwlsMode;
   int nuwlsIsExternalTimeLimit;
   int nuwlsExternalTimeLimit;
   int satlikeMode;   
   int satlikeInvsThr;
   int satlikeTimeThr;
   int satlikeInitTimeThr;
   int satlikePreInitTimeThr;
   int satlikePreInitMaxClss;
   int satlikeMaxFlips;
   int satlikeMaxNonImproveFlip;
   int satlikeMaxFlipsReduceBeyondClsNum;
   int satlikeReinvokeTimeThr;
   int satlikeMimicMse21;
   double satlikeReinvokeMult;
   int totProp0s;
   int totBuildLayered;
   int msSatInvToReinvoke;
   double msSatInvToReinvokeMult;
   double msReinvokeMultThr;
   int initMsMaxEpochs;
   double msReinvokeMultThrMin;
   
   int msVerbosity;
   
   vec<bool> isVarTarget;
   bool skipFillingSolverPolarity;   
};


