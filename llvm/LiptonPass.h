/*
 * LiptonPass.h
 *
 *  Created on: Feb 26, 2015
 *      Author: laarman
 */

#ifndef LIPTONBIN_LLVM_LIPTONPASS_H_
#define LIPTONBIN_LLVM_LIPTONPASS_H_

#include <iterator>
#include <list>
#include <string>
#include <vector>

#include <llvm/Pass.h>
#include <llvm/IR/Instruction.h>
#include <llvm/Analysis/CallGraph.h>
#include <llvm/Analysis/AliasAnalysis.h>
#include <llvm/Analysis/AliasSetTracker.h>
#include <llvm/ADT/DenseMap.h>
#include <llvm/ADT/DenseSet.h>
#include <llvm/Support/raw_os_ostream.h>


using namespace llvm;
using namespace std;

namespace VVT {

enum block_e {
	NoBlock		= -1,
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

struct Options {
    bool nolock = false;
    bool nodyn = false;
    bool allYield = false;
    bool staticAll = false;
    bool verbose = false;
    bool debug = false;
};

typedef pair<const AliasAnalysis::Location *, CallInst *> PTCallType;

// Copy-on-write (COW)
class PThreadType {
private:

    list<PTCallType>           *WriteLocks = nullptr;
    list<PTCallType>           *ReadLocks = nullptr;
    list<PTCallType>           *Threads = nullptr;
    bool                        CorrectThreads = true;
    bool                        Atomic = false;

    PThreadType (PThreadType *O, bool copy) {
        ReadLocks   = O->ReadLocks;
        WriteLocks  = O->WriteLocks;
        Threads     = O->Threads;
        CorrectThreads = O->CorrectThreads;
        Atomic = O->Atomic;
        assert (copy);
    }

public:
    PThreadType (bool threads) {
        WriteLocks = new list<PTCallType> ();
        ReadLocks = new list<PTCallType> ();
        Threads = new list<PTCallType> ();
        CorrectThreads = threads;
    }

    PThreadType (PThreadType *O) {
        ReadLocks = new list<PTCallType> (*O->ReadLocks);
        WriteLocks = new list<PTCallType> (*O->WriteLocks);
        if (O->CorrectThreads)
            Threads = new list<PTCallType> (*O->Threads);
        CorrectThreads = O->CorrectThreads;
        Atomic = O->Atomic;
    }


    bool operator<=(PThreadType &O);
    void print (bool read, bool write, bool threads);
    bool locks  ();

    PThreadType *overlap(pt_e kind, const AliasAnalysis::Location &Loc, CallInst *Call);
    PThreadType *add    (pt_e kind, const AliasAnalysis::Location &Loc, CallInst *Call);
    PThreadType *missed (pt_e kind, const AliasAnalysis::Location &Loc, CallInst *Call);
    PThreadType *eraseAlias     (pt_e kind, const AliasAnalysis::Location &Loc, CallInst *Call);

    // exception to COW (used to reduce lock set candidates):
    void eraseNonAlias  (pt_e kind, const AliasAnalysis::Location &Loc, CallInst *Call);
    void eraseNonAlias (pt_e kind, PThreadType *O);

    int  findAlias   (pt_e kind, const AliasAnalysis::Location &Loc);

    PThreadType *resizeReadLocks (int size);
    PThreadType *flipAtomic() {
        PThreadType *O = new PThreadType (this, true);
        O->Atomic = !Atomic;
        return O;
    }

    bool singleThreaded() { return CorrectThreads && Threads->empty(); }
    bool isAtomic() { return Atomic; }
    bool isCorrectThreads() { return CorrectThreads; }
};

struct LLVMInstr {
    area_e          Area    = Unknown;
    mover_e         Mover   = UnknownMover;
    bool            Atomic  = false;
    bool            Loops   = false;
    bool            FVS     = false; // member of feedback vertex set?
    PThreadType    *PT      = nullptr;

    bool
    singleThreaded ()
    {
        assert (PT != nullptr);
        return PT->singleThreaded();
    }
};

static Function *
getFF () {
    assert(false);
    return nullptr;
}

struct LLVMThread {
    Function                                   &F;
    vector<Instruction *>                       Starts;

    LLVMThread() : F(*getFF()) { assert(false);  }

    LLVMThread(Function *F)
    :
        F(*F)
    {
        Aliases = new AliasSetTracker(*AA);
    }

    int NrRuns ();

    DenseMap<Instruction *, pair<block_e, int>> BlockStarts;
    AliasSetTracker                            *Aliases = nullptr;
    AllocaInst                                 *PhaseVar = nullptr;
    DenseMap<Instruction *, LLVMInstr *>          Instructions;

    bool isSingleton ();

    LLVMInstr &getInstruction (Instruction* I);
};

class LiptonPass : public ModulePass {

public:
    static char         ID;
    string              Name;

    Options            &opts;

    //ReachPass                      *Reach = nullptr;

    LiptonPass();
    LiptonPass(string name, Options &opts);

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
        block_e isBlockStart (Instruction *I);
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
                               SmallVector<Instruction *, 8> *Is,
                               Instruction *I, LLVMThread *T);
    void initialInstrument (Module &M);
    void finalInstrument (Module &M);
    void deduceInstances (Module &M);
    void refineAliasSets();
};

}

#endif /* LIPTONBIN_LLVM_LIPTONPASS_H_ */
