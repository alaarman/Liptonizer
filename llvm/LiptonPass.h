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
    StartBlock  = 0,        // First in thread. May be overwritten (|= is used).
    YieldBlock  = 1 << 0,   // Real yield or phase shift needed
    LoopBlock   = 1 << 1,   // Breaks cycles.
    CoincidingBlock = LoopBlock|YieldBlock,
    // Both Yield and Cycle block (either yield should happen to break cycle)
};

enum mover_e {
    UnknownMover= -1,
    NoneMover   = 0,
    RightMover  = 1<<0,
    LeftMover   = 1<<1,
    BothMover   = LeftMover | RightMover,
};

// > 0 for Seen map
enum area_e {
    Unknown = 0,
    Bottom  = 1<<0,         // Think both-mover paths before/after static yields
    Pre     = 1<<1,         //
    Post    = 1<<2,         //
    Top     = Pre | Post    //
};

enum pt_e {
    ReadLock    = 1 << 0,
    TotalLock   = 1 << 1,
    ThreadStart = 1 << 2,
    AnyLock     = ReadLock | TotalLock
};

static AliasAnalysis                  *AA;


typedef pair<const AliasAnalysis::Location *, CallInst *> PTCallType;

// Copy-on-write (COW)
struct PThreadType {
    PThreadType () {}
    PThreadType (PThreadType *O) {
        ReadLocks = O->ReadLocks;
        WriteLocks = O->WriteLocks;
        Threads = O->Threads;
        CorrectThreads = O->CorrectThreads;
    }

    list<PTCallType>            WriteLocks;
    list<PTCallType>            ReadLocks;
    list<PTCallType>            Threads;
    bool                        CorrectThreads = true;
    bool                        Atomic = false;

public:
    bool operator<=(PThreadType &O);
    void print (bool read, bool write, bool threads);
    bool locks  ();

    PThreadType *overlap(pt_e kind, const AliasAnalysis::Location *Lock, CallInst *Call);
    PThreadType *add    (pt_e kind, const AliasAnalysis::Location *Lock, CallInst *Call);
    PThreadType *missed (pt_e kind, const AliasAnalysis::Location *Lock, CallInst *Call);
    PThreadType *eraseAlias     (pt_e kind, const AliasAnalysis::Location *Lock, CallInst *Call);

    // exception to COW (used to reduce lock set candidates):
    void eraseNonAlias  (pt_e kind, const AliasAnalysis::Location *Lock, CallInst *Call);

    int  findAlias   (pt_e kind, const AliasAnalysis::Location *Lock);
};

struct LLVMInstr {
    area_e          Area    = Unknown;
    mover_e         Mover   = UnknownMover;
    bool            Atomic  = false;
    bool            Loops   = false;
    PThreadType    *PT      = nullptr;

    bool
    singleThreaded ()
    {
        return PT->CorrectThreads && PT->Threads.empty();
    }
};

struct LLVMThread {
    Function                                   &F;
    int                                         index;
    int                                         Runs = -2;

    LLVMThread(Function *F, int i)
    :
        F(*F),
        index(i)
    {
        Aliases = new AliasSetTracker(*AA);
    }

    DenseMap<Instruction *, pair<block_e, int>> BlockStarts;
    AliasSetTracker                            *Aliases;
    AllocaInst                                 *PhaseVar = nullptr;
    DenseMap<Instruction *, LLVMInstr>          Instructions;

    bool isSingleton ();
};

class LiptonPass : public ModulePass {

public:
    static char         ID;
    string              Name;
    bool                verbose;
    bool                staticAll;  // no phase && dynamic commutativity
    bool                noDyn;      // no dynamic commutativity
    bool                NoLock;
    bool                AllYield;

    ReachPass                      *Reach = nullptr;

    LiptonPass();
    LiptonPass(ReachPass &RP, string name, bool v, bool staticBlocks,
               bool phase, bool noLock, bool allYield);

    DenseMap<AliasSet *, list<Instruction *>>       AS2I;
    DenseMap<Function *, LLVMThread *>              Threads;


    struct Processor {
        LiptonPass                 *Pass;
        LLVMThread                 *ThreadF = nullptr;

        Processor(LiptonPass *L) : Pass(L) {  }
        virtual ~Processor() {}

        virtual Instruction *process (Instruction *I)
                                     { return nullptr; }
        virtual Instruction *handleCall (CallInst *call) { return nullptr; }
        virtual void thread (Function *F) {}
        virtual bool block (BasicBlock &B) { return false; }
        virtual void deblock (BasicBlock &B) {  }
        bool isBlockStart (Instruction *I);
    };

private:
    Processor                      *handle = nullptr;

    void dynamicYield (LLVMThread *T, Instruction *I, block_e type, int b);
    void staticYield (LLVMThread *T, Instruction *I, block_e type, int b);
    // getAnalysisUsage - This pass requires the CallGraph.
    virtual void getAnalysisUsage(AnalysisUsage &AU) const;
    bool runOnModule (Module &M);

    void walkGraph ( Instruction *I );
    void walkGraph ( BasicBlock &B );
    void walkGraph ( Function &F );
    template <typename ProcessorT>
    void walkGraph (Module &M);

    bool conflictingNonMovers (SmallVector<Value*, 8> &sv,
                               Instruction *I, LLVMThread *T);
    void initialInstrument (Module &M);
    void finalInstrument (Module &M);
    void deduceInstances ();
    void refineAliasSets();
};


}

#endif /* LIPTONBIN_LLVM_LIPTONPASS_H_ */
