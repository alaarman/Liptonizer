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

enum yield_loc_e {
    YIELD_BEFORE,
    YIELD_AFTER
};

enum mover_e {
    RightMover = 0,
    NoneMover,
    LeftMover,
    BothMover,
};

class LiptonPass : public ModulePass {

public:
    static char ID;
    LiptonPass();
    LiptonPass(ReachPass &RP);


    struct Processor {
        LiptonPass                 *Pass;
        Function                   *ThreadF = NULL;
        Processor(LiptonPass *L, StringRef action) : Pass(L) {  }
        virtual ~Processor() {}
        virtual Instruction *process (Instruction *I)
                                     { return nullptr; }
        virtual void yield (Instruction *I) { }
        virtual void thread (Function *F) {}
        virtual bool block (BasicBlock &B) { return false; }
        virtual void deblock (BasicBlock &B) {  }
    };

    ReachPass::ThreadCreateT        TI;
    Function                       *Yield;
    AliasAnalysis                  *AA;
    ReachPass                      *Reach;

    bool isYieldCall (Instruction *I);
    void insertYield (Instruction *I, yield_loc_e loc);
    mover_e movable(Instruction *I);

private:
    Processor                      *handle = nullptr;

    // getAnalysisUsage - This pass requires the CallGraph.
    virtual void getAnalysisUsage(AnalysisUsage &AU) const;
    bool runOnModule (Module &M);

    void walkGraph ( Instruction *I );
    void walkGraph ( BasicBlock &B );
    void walkGraph ( Function &F );
    template <typename ProcessorT>
    void walkGraph ();
};


}

#endif /* LIPTONBIN_LLVM_LIPTONPASS_H_ */
