/*
 * LiptonPass.h
 *
 *  Created on: Feb 26, 2015
 *      Author: laarman
 */

#ifndef LIPTONBIN_LLVM_LIPTONPASS_H_
#define LIPTONBIN_LLVM_LIPTONPASS_H_

#include <vector>

#include "llvm/ReachPass.h"

#include <llvm/Pass.h>
#include <llvm/IR/Instruction.h>
#include <llvm/Analysis/CallGraph.h>
#include <llvm/Analysis/AliasAnalysis.h>
#include <llvm/ADT/DenseMap.h>


using namespace llvm;

namespace VVT {

class LiptonPass : public ModulePass {

public:
    static char ID;
    LiptonPass();

    struct Processor {
        LiptonPass                 *Pass;
        Function                   *ThreadF;
        Processor(LiptonPass *L, Function *F, StringRef action) :
                Pass(L),
                ThreadF(F)
        {
            outs() << action <<" "<< F->getName() <<"\n";
        }
        virtual ~Processor() {}
        virtual void initialize() {}
        virtual Instruction *operator()(LiptonPass *pass, Instruction *I)
                                       { return nullptr; }
    };

    ReachPass::ThreadCreateT    TI;
    Function                   *Yield;
    AliasAnalysis              *AA;
    ReachPass                  *Reach;

private:
    // getAnalysisUsage - This pass requires the CallGraph.
    virtual void getAnalysisUsage(AnalysisUsage &AU) const;
    bool runOnModule(Module &M);

    Processor *process = nullptr;
    void walkGraph ( TerminatorInst *T );
    void walkGraph ( Instruction *I );
    void walkGraph ( BasicBlock &B );
    void walkGraph ( Function &F );
    void walkGraph ( CallGraphNode &N );
    template <typename ProcessorT>
    void walkGraph ( CallGraph &N );
};


}

#endif /* LIPTONBIN_LLVM_LIPTONPASS_H_ */
