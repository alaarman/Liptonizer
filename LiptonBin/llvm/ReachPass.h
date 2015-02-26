/*
 * ReachPass.h
 *
 *  Created on: Feb 26, 2015
 *      Author: laarman
 */

#ifndef LIPTONBIN_LLVM_REACHPASS_H_
#define LIPTONBIN_LLVM_REACHPASS_H_

#include <llvm/Pass.h>
#include <llvm/PassRegistry.h>
#include <llvm/PassSupport.h>
#include <llvm/Analysis/CallGraphSCCPass.h>
#include <llvm/IR/BasicBlock.h>
#include <llvm/IR/Instruction.h>


#include "../util/SCCQuotientGraph.h"

namespace VVT {

class ReachPass : public CallGraphSCCPass {

public:
    DenseMap<Instruction *, SCCX<BasicBlock> *> instructionMap;

    SCCQuotientGraph<BasicBlock> blockQuotient;

    ReachPass() : CallGraphSCCPass(ID) { }

    static char ID;

    void printClosure() {
        blockQuotient.print ();
    }

private:
    int sccNum = 0;

    bool runOnSCC(CallGraphSCC &SCC);

    // getAnalysisUsage - This pass requires the CallGraph.
    virtual void getAnalysisUsage(AnalysisUsage &AU) const {
        AU.setPreservesAll();
        AU.addRequired<CallGraphWrapperPass>();
    }

    void printNode (CallGraphNode* const node, CallGraphSCC& SCC);
    void addInstruction (SCCX<BasicBlock> *scc, Instruction *I);
};


}


#endif /* LIPTONBIN_LLVM_REACHPASS_H_ */
