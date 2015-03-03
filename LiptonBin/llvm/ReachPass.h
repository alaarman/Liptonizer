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
#include <llvm/IR/Function.h>
#include <llvm/IR/Instruction.h>

#include <vector>

namespace VVT {

class ReachPass : public CallGraphSCCPass {

public:
    typedef pair<Instruction *, Function *>         CallT;
    typedef vector<CallT>                           CallsT;
    typedef DenseMap<BasicBlock *, CallsT>          CallMapT;
    typedef pair<BasicBlock *, CallsT>              CallMapET;

    static char ID;
    DenseMap<Instruction *, unsigned>               instructionMap;
    SCCQuotientGraph<BasicBlock>                    blockQuotient;
    SCCQuotientGraph<Instruction>                   instrQuotient;
    vector<CallT>                                   entryPoints;

    ReachPass();

    void printClosure();
    void finalize();

private:
    int sccNum = 0;
    CallMapT calls;
    void reorder();

    // getAnalysisUsage - This pass requires the CallGraph.
    virtual void getAnalysisUsage(AnalysisUsage &AU) const;
    bool runOnSCC(CallGraphSCC &SCC);

    void checkNode (CallGraphNode* const node, CallGraphSCC& SCC);
    void printNode (CallGraphNode* const node, CallGraphSCC& SCC);
    void addInstruction (unsigned scc, Instruction *I);
};


}


#endif /* LIPTONBIN_LLVM_REACHPASS_H_ */
