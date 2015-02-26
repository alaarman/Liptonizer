/*
 * ReachPass.h
 *
 *  Created on: Feb 26, 2015
 *      Author: laarman
 */

#ifndef LIPTONBIN_LLVM_REACHPASS_H_
#define LIPTONBIN_LLVM_REACHPASS_H_

#include "util/SCCQuotientGraph.h"

#include <llvm/Analysis/CallGraphSCCPass.h>
#include <llvm/IR/BasicBlock.h>
#include <llvm/IR/Instruction.h>


namespace VVT {

class ReachPass : public CallGraphSCCPass {

public:
    static char ID;
    DenseMap<Instruction *, SCCI *> instructionMap;
    SCCQuotientGraph<BasicBlock> blockQuotient;

    ReachPass() : CallGraphSCCPass(ID) { }

    void printClosure();

private:
    int sccNum = 0;

    // getAnalysisUsage - This pass requires the CallGraph.
    virtual void getAnalysisUsage(AnalysisUsage &AU) const;
    bool runOnSCC(CallGraphSCC &SCC);

    void checkNode (CallGraphNode* const node, CallGraphSCC& SCC);
    void printNode (CallGraphNode* const node, CallGraphSCC& SCC);
    void addInstruction (SCCI *scc, Instruction *I);
};


}


#endif /* LIPTONBIN_LLVM_REACHPASS_H_ */
