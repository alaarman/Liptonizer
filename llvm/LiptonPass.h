/*
 * LiptonPass.h
 *
 *  Created on: Feb 26, 2015
 *      Author: laarman
 */

#ifndef LIPTONBIN_LLVM_LIPTONPASS_H_
#define LIPTONBIN_LLVM_LIPTONPASS_H_

#include <list>
#include <string>
#include <vector>

#include "llvm/ReachPass.h"

#include <llvm/Pass.h>
#include <llvm/IR/Instruction.h>
#include <llvm/Analysis/CallGraph.h>
#include <llvm/Analysis/AliasAnalysis.h>
#include <llvm/Analysis/AliasSetTracker.h>
#include <llvm/ADT/DenseMap.h>
#include <llvm/ADT/DenseSet.h>


using namespace llvm;

namespace VVT {

enum block_e {
    Static = 0,     // loop blocks
    PhaseDynamic,   // phase dynamic blocks
    CommDynamic,   // commutativity dynamic blocks
};

enum yield_loc_e {
    YIELD_BEFORE,
    YIELD_AFTER
};

enum mover_e {
    NoneMover   = 0,
    RightMover  = 1,
    LeftMover   = 2,
    BothMover   = 3,
};

class LiptonPass : public ModulePass {

public:
    static char         ID;
    string              Name;
    bool                verbose;
    bool                staticAll;  // no phase && dynamic commutativity
    bool                noDyn;      // no dynamic commutativity

    AliasAnalysis                  *AA = nullptr;
    ReachPass                      *Reach = nullptr;

    LiptonPass();
    LiptonPass(ReachPass &RP, string name, bool v, bool staticBlocks,
               bool phase);

    struct LLVMThread {
        LLVMThread(Function *F, int i, LiptonPass *Pass)
        :
            Function(*F),
            index(i)
        {
            Aliases = new AliasSetTracker(*Pass->AA);
            runs = &Pass->Reach->Threads[F];
        }

        DenseMap<Instruction *, pair<block_e, int>> BlockStarts;
        AliasSetTracker                            *Aliases;
        Function                                   &Function;
        AllocaInst                                 *PhaseVar = nullptr;
        int                                         index;
        vector<Instruction *>                      *runs;
    };

    struct Processor {
        LiptonPass                 *Pass;
        LLVMThread                 *ThreadF = nullptr;
        Processor(LiptonPass *L, StringRef action) : Pass(L) {  }
        virtual ~Processor() {}
        virtual Instruction *process (Instruction *I)
                                     { return nullptr; }
        virtual Instruction *handleCall (CallInst *call) { return nullptr; }
        virtual void thread (Function *F) {}
        virtual bool block (BasicBlock &B) { return false; }
        virtual void deblock (BasicBlock &B) {  }

        bool    isBlockStart (Instruction *I);
        int     insertBlock (Instruction *I, yield_loc_e loc, block_e yieldType);
    };

    //AliasSetTracker                            *AST;
    DenseSet<Instruction *>                     PTCreate;
    DenseMap<AliasSet *, list<Instruction *>>   AS2I;
    DenseMap<Function *, LLVMThread *>          Threads;
    DenseMap<Instruction *, LLVMThread *>         I2T;

private:
    Processor                      *handle = nullptr;

    void dynamicYield (Instruction *I, block_e type, int b);
    // getAnalysisUsage - This pass requires the CallGraph.
    virtual void getAnalysisUsage(AnalysisUsage &AU) const;
    bool runOnModule (Module &M);

    void walkGraph ( Instruction *I );
    void walkGraph ( BasicBlock &B );
    void walkGraph ( Function &F );
    void conflictingNonMovers (SmallVector<Value*, 8> &sv,
                               Instruction *I);
    void initialInstrument (Module &M);
    void finalInstrument (Module &M);
    template <typename ProcessorT>
    void walkGraph ();
};


}

#endif /* LIPTONBIN_LLVM_LIPTONPASS_H_ */
