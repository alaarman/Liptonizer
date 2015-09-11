
#include "util/BitMatrix.h"
#include "util/Util.h"
#include "llvm/LiptonPass.h"
#include "llvm/Util.h"

#include <algorithm>    // std::sort
#include <assert.h>
#include <iostream>
#include <list>
#include <set>
#include <string>

#include <llvm/Analysis/CFG.h>
#include <llvm/Analysis/Passes.h>
#include <llvm/Bitcode/ReaderWriter.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/BasicBlock.h>
#include <llvm/IR/DerivedTypes.h>
#include <llvm/IR/InstrTypes.h>
#include <llvm/IR/InstIterator.h>
#include <llvm/IR/Instruction.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/IntrinsicInst.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Metadata.h>
#include <llvm/IR/Type.h>
#include <llvm/Pass.h>
#include <llvm/PassAnalysisSupport.h>
#include <llvm/PassRegistry.h>
#include <llvm/PassSupport.h>
#include <llvm/Transforms/Utils/BasicBlockUtils.h>
#include <llvm/Transforms/Utils/Local.h>
#include <llvm/Transforms/Utils/ModuleUtils.h>

#include <llvm/ADT/DenseSet.h>
#include <llvm/ADT/SmallVector.h>
#include <llvm/IR/ValueMap.h>


using namespace llvm;
using namespace std;


namespace VVT {


static Constant *TRUE;
static Constant *FALSE;
static Constant *PRECOMMIT = FALSE;
static Constant *POSTCOMMIT = TRUE;

static const char *__YIELD          = "__yield";
static const char *__YIELD_LOCAL    = "__yield_local";
static const char *__ACT            = "__act";
static const char *PTHREAD_YIELD    = "pthread_yield";
static const char *PTHREAD_CREATE   = "pthread_create";
static const char *PTHREAD_JOIN     = "pthread_join";
static const char *PTHREAD_LOCK     = "pthread_mutex_lock";
static const char *PTHREAD_RLOCK    = "pthread_rwlock_rdlock";
static const char *PTHREAD_WLOCK    = "pthread_rwlock_wrlock";
static const char *PTHREAD_RW_UNLOCK= "pthread_rwlock_unlock";
static const char *PTHREAD_UNLOCK   = "pthread_mutex_unlock";
static const char *PTHREAD_MUTEX_INIT = "pthread_mutex_init";
static const char *ATOMIC_BEGIN     = "atomic_begin";
static const char *ATOMIC_END       = "atomic_end";

char LiptonPass::ID = 0;
static RegisterPass<LiptonPass> X("lipton", "Lipton reduction");

Function                       *YieldGlobal = nullptr;
Function                       *YieldLocal = nullptr;
Function                       *Act = nullptr;
Type                           *Int64 = nullptr;

int                             nextBlock = 0;

static const char *SINGLE_THREADED = "singleThreaded";
static const char *MOVER = "mover";
static const char *AREA = "area";

static void
addMetaData (Instruction *I, const char *type, const char *s)
{
    LLVMContext &Context = I->getContext ();
    MDString *str = MDString::get (Context, s);
    MDNode *N = MDNode::get (Context, str);
    I->setMetadata (type, N);
}

static const char *
name ( mover_e m )
{
    switch (m) {
    case RightMover: return "RightMover";
    case LeftMover:  return "LeftMover";
    case NoneMover:  return "NoneMover";
    case BothMover:  return "BothMover";
    default: ASSERT (false, "Missing case: "<< m); return 0;
    }
}

static const char *
name ( area_e m )
{
    switch (m) {
    case Bottom:return "Bottom";
    case Pre:   return "Pre";
    case Post:  return "Post";
    case Top:   return "Top";
    default: ASSERT (false, "Missing case: "<< m); return 0;
    }
}

static const char *
name ( block_e m )
{
    switch (m) {
    case StartBlock:        return "Start Yield";
    case YieldBlock:        return "Global Yield";
    case LoopBlock:         return "Cycle Yield";
    case LoopBlock2:         return "GlobalCycle Yield";
    case CoincidingBlock:   return "Global+Cycle Yield";
    default: ASSERT (false, "Missing case: "<< m); return 0;
    }
}

static const char *
name ( pt_e m, bool add )
{
    switch (m) {
    case ReadLock:      assert (add); return PTHREAD_RLOCK;
    case AnyLock:       assert (!add); return PTHREAD_RW_UNLOCK;
    case TotalLock:     return add ? PTHREAD_LOCK : PTHREAD_UNLOCK;
    case ThreadStart:   return add ? PTHREAD_CREATE : PTHREAD_JOIN;
    default: ASSERT (false, "Missing case: "<< m); return 0;
    }
}

LiptonPass::LiptonPass () : ModulePass(ID),
        Name ("out"),
        verbose(true),
        staticAll(false),
        noDyn(false),
        NoLock(false),
        AllYield(false),
        Reach (nullptr)
{ }

LiptonPass::LiptonPass (ReachPass &RP, string name, bool v, bool staticBlocks,
                        bool phase, bool nolock, bool allYield)
                                                            : ModulePass(ID),
        Name (name),
        verbose(v),
        staticAll(staticBlocks),
        noDyn(phase),
        NoLock(nolock),
        AllYield(allYield),
        Reach (&RP)
{ }

void
LiptonPass::getAnalysisUsage (AnalysisUsage &AU) const
{
    AU.setPreservesCFG();
    AU.addRequired<AliasAnalysis>();
    AU.addRequired<CallGraphWrapperPass>();
}

block_e
LiptonPass::Processor::isBlockStart (Instruction *I)
{
	auto Start = ThreadF->BlockStarts.find(I);
	if (Start != ThreadF->BlockStarts.end()) {
    	return Start->second.first;
    }
	return NoBlock;
}

bool
LLVMThread::isSingleton ()
{
    assert (Runs != -2);
    return Runs == 1;
}

// TODO: Left == Left | Bottom
//inline area_e
//operator< (area_e a, area_e b)
//{
//
//}

static bool
isCommutingAtomic (Instruction *I, Instruction *J)
{
    AtomicRMWInst *A = dyn_cast_or_null<AtomicRMWInst>(I);
    if (!A) return false;
    AtomicRMWInst *B = dyn_cast_or_null<AtomicRMWInst>(J);
    if (!B) return false;
    switch (A->getOperation()) {
    case AtomicRMWInst::BinOp::Add:
    case AtomicRMWInst::BinOp::Sub:
        switch (B->getOperation()) {
        case AtomicRMWInst::BinOp::Add:
        case AtomicRMWInst::BinOp::Sub:
            return true;
        default:
            return false;
        }
        break;
    case AtomicRMWInst::BinOp::Xchg:
    case AtomicRMWInst::BinOp::Nand:
        return false;
    default:
        return A->getOperation() == B->getOperation();
    }
}

static AliasSet *
FindAliasSetForUnknownInst(AliasSetTracker *AST, Instruction *Inst)
{
    for (AliasSet &AS : *AST) {
        if (AS.aliasesUnknownInst(Inst, AST->getAliasAnalysis()))
            return &AS; // Alias sets are guaranteed to be disjount
        // TODO: use instruction matrix to implement own alias set tracker
    }
    return nullptr;
}

static int
checkAlias (list<PTCallType> &List, const AliasAnalysis::Location &Loc)
{
    int matches = 0;
    for (PTCallType &L : List) {
        llvm::AliasAnalysis::AliasResult Alias = AA->alias (Loc, *L.first);
        if (Alias == AliasAnalysis::MustAlias) {
            matches++;
        } else if (Alias != AliasAnalysis::NoAlias) {
            return -1;
        }
    }
    return matches;
}

static bool
removeAlias (list<PTCallType> &List, const AliasAnalysis::Location *Lock)
{
    list<PTCallType>::iterator It = List.begin();
    while (It != List.end()) {
        if (AA->alias(*Lock, *It->first) == AliasAnalysis::MustAlias) {
            List.erase(It);
            return true;
        }
        It++;
    }
    return false;
}

static void
removeNonAlias (list<PTCallType> &List, const AliasAnalysis::Location &Lock)
{
    list<PTCallType>::iterator It = List.begin();
    while (It != List.end()) {
        if (AA->alias(Lock, *It->first) != AliasAnalysis::MustAlias) {
            It = List.erase(It);
        } else {
            It++;
        }
    }
}

enum state_e {
    Unvisited   = 0,
    Stacked     = 1,
    Visited     = 2,

    OnLoop          = 1 << 10,
    StackedOnLoop   = Stacked | OnLoop,
    VisitedOnLoop   = Visited | OnLoop,
};

/**
 * Thread / instruction reachability processor
 *
 * Complexity: P X N
 */
struct Collect : public LiptonPass::Processor {

    static StringRef                Action;

    vector<BasicBlock *>                        Stack;
    DenseMap<BasicBlock *, state_e>             Seen;

    Collect(LiptonPass *Pass) : LiptonPass::Processor(Pass) { }
    ~Collect() { }

    Instruction *
    handleCall (CallInst *Call)
    {
        return Call;
    }

    bool
    block ( BasicBlock &B )
    {
        state_e &seen = Seen[&B];
        if (Pass->verbose) errs() << Action << ": " << B << seen <<endll;
        if (seen == Unvisited) {
            seen = Stacked;
            Stack.push_back (&B);
            return true;
        } else if (seen == Stacked || seen == StackedOnLoop) {
            seen = (state_e) ((int)seen | (int)OnLoop);
            // mark all on stack s on-loop:
            for (BasicBlock *B : Stack) {
                state_e &Flag = Seen[B];
                if (Flag & OnLoop) break;
                Flag = (state_e) ((int)Flag | (int)OnLoop);
            }
        }
        return false;
    }

    void
    deblock ( BasicBlock &B )
    {
        state_e &Flag = Seen[&B];
        if (Flag & OnLoop) {
            Flag = VisitedOnLoop;
            for (Instruction &I : B) {
                ThreadF->Instructions[&I].Loops = true;
            }
        } else {
            Flag = Visited;
        }
    }

    void
    thread (Function *T)
    {
        ThreadF = Pass->Threads[T];
        Seen.clear();
    }

    Instruction *
    process (Instruction *I)
    {
        if (I->isTerminator() || !I->mayReadOrWriteMemory() ||
                isa<DbgInfoIntrinsic>(I)) {
            return I;
        }

        ThreadF->Aliases->add (I);

        AliasSet *AS = FindAliasSetForUnknownInst (ThreadF->Aliases, I);
        Pass->AS2I[AS].push_back(I);
        return I;
    }
};

bool
PThreadType::operator<=(PThreadType &O)
{
    for (PTCallType &Call : ReadLocks) {
        if (checkAlias(O.ReadLocks, *Call.first) != 1) {
            return false;
        }
    }
    for (PTCallType &Call : WriteLocks) {
        if (checkAlias(O.WriteLocks, *Call.first) != 1) {
            return false;
        }
    }
    if (!O.CorrectThreads) return true;
    if (!CorrectThreads) return false;
    for (PTCallType &Call : Threads) {
        if (checkAlias(O.Threads, *Call.first) != 1) {
            return false;
        }
    }
    return true;
}



void
PThreadType::print (bool read, bool write, bool threads)
{
    if (read) {
        errs () << "READ LOCKS: "<< endll;
        for (PTCallType X : ReadLocks) {
            errs () << *X.second << endll;
        }
    }
    if (write) {
        errs () << "WRITE LOCKS: "<< endll;
        for (PTCallType X : WriteLocks) {
            errs () << *X.second << endll;
        }
    }
    if (threads) {
        if (!CorrectThreads) {
            errs () << "THREADS Incorrect " << endll;
        } else {
            errs () << "THREADS seen: " << endll;
            for (PTCallType X : Threads) {
                errs () << *X.second << endll;
            }
        }
    }
}

bool
PThreadType::locks ()
{
    return !ReadLocks.empty() || !WriteLocks.empty();
}

int
PThreadType::findAlias (pt_e kind, const AliasAnalysis::Location &Loc)
{
    if (kind == ThreadStart) {
        return checkAlias (Threads, Loc);
    }
    if (kind & ReadLock) {
        return checkAlias (ReadLocks, Loc);
    }
    if (kind & TotalLock) {
        return checkAlias (WriteLocks, Loc);
    }
    assert (false); return -1;
}

PThreadType *
PThreadType::missed (pt_e kind, const AliasAnalysis::Location &Loc, CallInst *Call)
{
    errs () << "WARNING: missed "<< name(kind, false) <<" join/unlock: "<<*Loc.Ptr << endll << *Call << endll;
    PThreadType *PT = new PThreadType(this);
    if (kind == ThreadStart) {
        PT->CorrectThreads = false;
    } else {
        if (kind & ReadLock) {
            PT->ReadLocks.resize (0);
        }
        if (kind & TotalLock) {
            PT->WriteLocks.resize (0);
        }
    }
    return PT;
}

PThreadType *
PThreadType::eraseAlias (pt_e kind, const AliasAnalysis::Location &Loc, CallInst *Call)
{
    errs () << "END: tracking "<< name(kind, false) <<": "<< *Call << endll;
    PThreadType *PT = new PThreadType(this);
    if (kind == ThreadStart) {
        removeAlias (PT->Threads, &Loc);
    } else {
        int count = 0;
        if (kind & ReadLock) {
            count += removeAlias (PT->ReadLocks, &Loc);
        }
        if (kind & TotalLock) {
            count += removeAlias (PT->WriteLocks, &Loc);
        }
        assert (count == 1);
    }
    return PT;
}


void
PThreadType::eraseNonAlias (pt_e kind, const AliasAnalysis::Location &Loc, CallInst *Call)
{
    if (kind == ThreadStart) {
        removeNonAlias (Threads, Loc);
    } else if (kind == ReadLock) {
        removeNonAlias (ReadLocks, Loc);
    } else if (kind == TotalLock || kind == AnyLock) {
        removeNonAlias (WriteLocks, Loc);
    }
}

PThreadType *
PThreadType::add (pt_e kind, const AliasAnalysis::Location &Loc, CallInst *Call)
{
    errs () << "BEGIN: tracking "<< name(kind, true) <<": "<< *Call << endll;

    AliasAnalysis::Location *L = new AliasAnalysis::Location (Loc);
    PThreadType *PT = new PThreadType(this);
    assert (kind != AnyLock);
    if (kind == ThreadStart) {
        PT->Threads.push_back (make_pair(L, Call));
    } else if (kind & ReadLock) {
        PT->ReadLocks.push_back (make_pair(L, Call));
    } else if (kind & TotalLock) {
        PT->WriteLocks.push_back (make_pair(L, Call));
    } else {
        assert (false);
    }
    return PT;
}

PThreadType *
PThreadType::overlap (pt_e kind, const AliasAnalysis::Location &Loc, CallInst *Call)
{
    errs () << "WARNING: retracking (dropping) "<< name(kind, true) <<": "<<*Loc.Ptr << endll << *Call << endll;
    if (kind == ThreadStart) {
        PThreadType *PT = new PThreadType(this);
        PT->CorrectThreads = false;
        return PT;
    }
    return this; // locks can simply be dropped
}

/**
 * Find paths where locks are held
 */
struct LockSearch : public LiptonPass::Processor {

    static StringRef                Action;

    LockSearch(LiptonPass *Pass) : LiptonPass::Processor(Pass) { }
    ~LockSearch() {}

    struct LockVisited {
        state_e             State = Unvisited;
        PThreadType        *PT = nullptr;
    };

    DenseMap<BasicBlock *, LockVisited>     Seen;
    vector<BasicBlock *>                    Stack;

    // Will always point to the one on the top of the stack or an empty struct
    // Access policy: copy-on-write
    PThreadType                    *PT = nullptr;

    // block and deblock implement revisiting
    bool
    block ( BasicBlock &B )
    {
        LockVisited &V = Seen[&B];

        if (V.State != Unvisited && *V.PT <= *PT) {
            return false;
        }
        if (Pass->verbose) {
            errs() << B << "\n";
            if (V.State != Unvisited) {
                errs() << " --(lock revisit)--> "<<  B << "\n";
                errs () << "REVISITING A MONOTONICALLY DECREASING LOCK SECTION: "<< B << endll;
                PT->print (true, true, true);
            }
        }

        if (V.State == Stacked) { // rewind stack
            while (true) {
                BasicBlock *Old = Stack.back();
                Seen[Old].State = Visited;
                Stack.pop_back ();
                errs () << "Removing: " << *Old<< endll;
                if (Old == &B) break;
            }
        }

        Stack.push_back ( &B );
        V.PT = PT;
        V.State = Stacked;
        return true;
    }

    void
    deblock ( BasicBlock &B )
    {
        if (Pass->verbose) PT->print (true, true, false);

        LockVisited &V = Seen[&B];
        if (V.State != Stacked) return; // already popped in stack rewind

        PT = V.PT;
        V.State = Visited;
        Stack.pop_back();
    }

    void
    thread (Function *T)
    {
        assert (T != nullptr);
        errs() << "THREAD: "<< T->getName() << endll;
        assert (Stack.empty());
        Seen.clear();
        ThreadF = Pass->Threads[T];

        PT = new PThreadType(); //TODO: leak?
        if (!T->getName().equals("main")) { // Not single threaded from the start!
            PT->CorrectThreads = false;
        }
    }

    void
    addPThread (CallInst *Call, pt_e kind, bool add)
    {
        if (Pass->NoLock) return;
        if (kind == ThreadStart && !PT->CorrectThreads) return; // nothing to do

        AliasAnalysis::Location L;
        if (kind == ThreadStart && !add) { // PTHREAD_JOIN
            Value *Temp = Call->getArgOperand(0);
            LoadInst *Load = dyn_cast<LoadInst>(Temp);
            L = AA->getLocation(Load);
        } else {
            AliasAnalysis::ModRefResult Mask;
            L = AA->getArgLocation (Call, 0, Mask);
        }

        int matches = PT->findAlias (kind, L);
        if (add) {
            if (matches == 0) {
                PT = PT->add (kind, L, Call);
            } else { // Do not add (cannot determine region statically)
                PT = PT->overlap (kind, L, Call);
            }
        } else {
            if (matches == 1) {
                PT = PT->eraseAlias (kind, L, Call);
            } else { // Empty (Cannot determine end of locked region)
                PT = PT->missed (kind, L, Call);
            }
        }
    }

    Instruction *
    handleCall (CallInst *Call)
    {
        assert (Call && Call->getCalledFunction());
        doHandle (Call);

        if (Call->getCalledFunction()->getName().endswith(PTHREAD_YIELD)) {
        } else if (Call->getCalledFunction()->getName().endswith("__assert_rtn")) {
        } else if (Call->getCalledFunction()->getName().endswith("__assert")) {
        } else if (Call->getCalledFunction()->getName().endswith("llvm.expect.i64")) {
        } else if (Call->getCalledFunction()->getName().endswith(PTHREAD_LOCK)) {
            addPThread (Call, TotalLock, true);
        } else if (Call->getCalledFunction()->getName().endswith(PTHREAD_RLOCK)) {
            addPThread (Call, ReadLock, true);
        } else if (Call->getCalledFunction()->getName().endswith(PTHREAD_WLOCK)) {
            addPThread (Call, TotalLock, true);
        } else if (Call->getCalledFunction()->getName().endswith(PTHREAD_RW_UNLOCK)) {
            addPThread (Call, AnyLock, false);
        } else if (Call->getCalledFunction()->getName().endswith(PTHREAD_UNLOCK)) {
            addPThread (Call, TotalLock, false);
        } else if (Call->getCalledFunction()->getName().endswith(PTHREAD_CREATE)) {
            addPThread (Call, ThreadStart, true);
        } else if (Call->getCalledFunction()->getName().endswith(PTHREAD_JOIN)) {
            addPThread (Call, ThreadStart, false);
        } else if (Call->getCalledFunction()->getName().endswith(PTHREAD_MUTEX_INIT)) {
        } else if (Call->getCalledFunction()->getName().endswith(ATOMIC_BEGIN)) {
            LLASSERT (PT->Atomic == false, "Already "<< ATOMIC_BEGIN <<"encountered before: "<< Call << endll);
            PT = new PThreadType(PT); // optimize
            PT->Atomic = true;
        } else if (Call->getCalledFunction()->getName().endswith(ATOMIC_END)) {
            LLASSERT (PT->Atomic == true, "No "<< ATOMIC_BEGIN <<"encountered before: "<< Call << endll);
            PT = new PThreadType(PT); // optimize
            PT->Atomic = false;
        } else {
            return nullptr;
        }
        return Call;
    }

    Instruction *
    process (Instruction *I)
    {
        doHandle (I);

        return I;
    }

private:
    void
    doHandle (Instruction *I)
    {
        LLVMInstr &LI = ThreadF->Instructions[I];
        LI.Atomic = PT->Atomic;
        if (I->mayWriteToMemory()) {
            LI.PT = new PThreadType(PT);
            LI.PT->ReadLocks.resize (0);
        } else {
            LI.PT = PT;
        }
    }
};

/**
 * Marks instructions that can be (dynamic) atomic section starts.
 *
 * The current phase is statically over-estimated using a lattice of phase
 * states (area_e). If the search (re)encounters a visited/queud block with
 * a lower phase than it was preciously visited with, it is revisited with the
 * higher order phase and the block boundary is strengthened (made less dynamic).
 *
 * Complexity: N * |{Bottom, Pre, Post, Top}| + cost for aliasing analysis
 *
 */
struct Liptonize : public LiptonPass::Processor {

    static StringRef                Action;

    Liptonize(LiptonPass *Pass) : LiptonPass::Processor(Pass) { }
    ~Liptonize() { }

    struct StackElem {
        StackElem (area_e a, BasicBlock *B)
        :
            Area(a),
            Block(B)
        {  }
        area_e                  Area;
        BasicBlock             *Block;
    };

    union SeenType {
        int                     Index = 0;
        area_e                  Area;
    };

    DenseMap<BasicBlock *, SeenType>        Seen;
    vector<StackElem>                       Stack;
    area_e                                  Area = Bottom;

    // block and deblock implement revisiting
    bool
    block ( BasicBlock &B )
    {
        SeenType &V = Seen[&B];

        if (V.Index == 0) { // Unvisited
            if (Pass->verbose) errs() << name(Area)  <<": "<< B << "\n";


            if (Pass->NoInternal && hasIncomingBackEdge(B)) {
            	errs () << "INSERTING Static Loop Yield "<< endll;
				insertBlock (getFirstNonTerminal(&B), LoopBlock2); // Close cycle
            }

            Stack.push_back ( StackElem(Area, &B) );
            V.Index = -Stack.size();

            return true;
        } else if (V.Index < 0) { // Stack
            Instruction *Start = getFirstNonTerminal (B.getFirstNonPHI ());

            if (!Pass->NoInternal) {
            	insertBlock (Start, LoopBlock);                 // Close cycle
            }

            StackElem &Previous = Stack[-V.Index - 1];
            if (Previous.Area < Area) {
                if (Pass->verbose) errs() << name(Area)  <<" --(revisit)--> "<<  name(Previous.Area) <<": "<< B << "\n";
                while (true) { // rewind stack
                   StackElem &X = Stack.back ();
                   if (&X == &Previous) break;
                   Seen[X.Block].Area = X.Area;
                   Stack.pop_back ();
                }
                Previous.Area = Area;
                return true;
            }
        } else {
            if (V.Area < Area) {
                if (Pass->verbose) errs() << name(Area)  <<" --(revisit)--> "<<  name(V.Area) <<": "<< B << "\n";
                // re-explore visited blocks:
                Stack.push_back ( StackElem(Area, &B) );
                V.Index = -Stack.size();
                return true;
            }
        }

        return false;
    }

    // TODO: backtrack Bottom up
    void
    deblock ( BasicBlock &B )
    {
        SeenType &V = Seen[&B];
        if (V.Index > 0)
            return; // already backtracked in stack rewind
        StackElem &Pop = Stack.back();
        V.Area = Pop.Area;
        Area = Pop.Area;
        Stack.pop_back();
    }

    void
    thread (Function *T)
    {
        assert (T != nullptr);
        errs() << "THREAD: "<< T->getName() << endll;

        assert (Stack.empty());
        ThreadF = Pass->Threads[T];
        Area = Bottom; // We always start from a static yield

        Instruction *Start = getFirstNonTerminal (T->getEntryBlock().getFirstNonPHI());
        int b = insertBlock (Start, StartBlock);
        assert (b == 0); // start block

        Seen.clear();
    }

    Instruction *
    handleCall (CallInst *Call)
    {
        assert (Call && Call->getCalledFunction());

        LLVMInstr &LI = ThreadF->Instructions[Call];
        if (LI.singleThreaded ()) {
            doHandle (LI, Call, BothMover);
            return Call;
        }

        if (Call->getCalledFunction()->getName().endswith(PTHREAD_YIELD)) {
            errs () << "WARNING: pre-existing Yield call: "<< *Call <<"\n";
            Area = Bottom;
        } else if (Call->getCalledFunction()->getName().endswith(PTHREAD_LOCK)) {
            doHandle (LI, Call, RightMover);
        } else if (Call->getCalledFunction()->getName().endswith(PTHREAD_RLOCK)) {
            doHandle (LI, Call, RightMover);
        } else if (Call->getCalledFunction()->getName().endswith(PTHREAD_WLOCK)) {
            doHandle (LI, Call, RightMover);
        } else if (Call->getCalledFunction()->getName().endswith(PTHREAD_RW_UNLOCK)) {
            doHandle (LI, Call, LeftMover);
        } else if (Call->getCalledFunction()->getName().endswith(PTHREAD_UNLOCK)) {
            doHandle (LI, Call, LeftMover);
        } else if (Call->getCalledFunction()->getName().endswith(PTHREAD_CREATE)) {
            doHandle (LI, Call, LeftMover);
        } else if (Call->getCalledFunction()->getName().endswith(PTHREAD_JOIN)) {
            doHandle (LI, Call, RightMover);
        } else if (Call->getCalledFunction()->getName().endswith(PTHREAD_MUTEX_INIT)) {
        } else if (Call->getCalledFunction()->getName().endswith(ATOMIC_BEGIN)) {
            assert (!ThreadF->Instructions[Call].Atomic);
            doHandle (LI, Call, RightMover); // force (dynamic) yield (for Post/Top)
        } else if (Call->getCalledFunction()->getName().endswith(ATOMIC_END)) {
        } else if (Call->getCalledFunction()->getName().endswith("__assert_rtn")) {
        } else if (Call->getCalledFunction()->getName().endswith("__assert")) {
        } else if (Call->getCalledFunction()->getName().endswith("llvm.expect.i64")) {
        } else {
            return nullptr;
        }
        return Call;
    }


    Instruction *
    process (Instruction *I)
    {
        LLVMInstr &LI = ThreadF->Instructions[I];
        if ((LI.Area == Pre && Area == Post) ||
            (LI.Area == Post && Area == Pre)) // 0 iff undefined
            Area = Top;

        mover_e Mover = LI.Mover;

        if (LI.singleThreaded() || I->isTerminator() ||
        		dyn_cast_or_null<PHINode>(I) != nullptr) {
            Mover = BothMover;
        } else if (Mover == -1) {
            Mover = movable (LI, I);
        }

        return doHandle (LI, I, Mover);
    }

private:
    Instruction *
    doHandle (LLVMInstr &LI, Instruction *I, mover_e Mover) // may overwrite less dynamic blocks
    {
        if (Pass->verbose) errs () << name(Area) << *I << " -> \t"<< name(Mover) << "\n";

        if (Pass->NoInternal && isBlockStart(I) == LoopBlock2) {
        	Area = Bottom;
        }
        LI.Area = Area;
        LI.Mover = Mover;

        addMetaData (I, AREA, name(Area));
        if (Mover != BothMover) {
            addMetaData (I, MOVER, name(Mover));
        }
        if (LI.singleThreaded()) {
            addMetaData (I, SINGLE_THREADED, "");
        }

        if (Pass->AllYield && !I->isTerminator() && dyn_cast_or_null<PHINode>(I) == nullptr) {
            Instruction *Start = getFirstNonTerminal (I);
            insertBlock (Start, LoopBlock);
        }

        switch (Mover) {
        case RightMover:
            if (Area & Post) { // Post, Top
                insertBlock (I, YieldBlock);
            }
            if (LI.PT->Atomic) {
                if (Area == Bottom) Area = Pre;
            } else {
                Area = Pre;
            }
            break;
        case LeftMover:
            if (Area != Post) { // Bottom, Pre, Top
                insertBlock (I, YieldBlock);
            }
            Area = Post;
            break;
        case NoneMover:
            insertBlock (I, YieldBlock);
            Area = Area == Post ? Post : Top;
            break;
        case BothMover:
            break;
        default:
            ASSERT(false, "Missing case.");
        }

        return I;
    }

    // TODO: combine with getConflictingNonMovers
    mover_e
    movable (LLVMInstr &LI, Instruction *I)
    {
        LLVMThread *T = ThreadF;

        PThreadType *PT = nullptr; // will store lock set if necessary
        assert (LI.PT != nullptr);

        for (pair<Function *, LLVMThread *> &X : Pass->Threads) {
            LLVMThread *T2 = X.second;
            if (T == T2 && T->isSingleton())
                continue;

            AliasSet *AS = FindAliasSetForUnknownInst (T2->Aliases, I);
            if (AS == nullptr)  continue;
            if (hasOnlyCommutingAtomicOps(AS, I)) continue; // try next thread T2

            if (LI.PT->locks()) {
                if (PT == nullptr) {
                    PT = new PThreadType (LI.PT); // copy
                }

                for (Instruction *J : Pass->AS2I[AS]) {
                    if (isCommutingAtomic(I,J)) continue;

                    LLVMInstr &LJ = T2->Instructions[J];

                    for (PTCallType &LockJ : LJ.PT->ReadLocks) { // intersection:
                        PT->eraseNonAlias (ReadLock, *LockJ.first, LockJ.second);
                    }
                    for (PTCallType &LockJ : LJ.PT->WriteLocks) { // intersection:
                        PT->eraseNonAlias (TotalLock, *LockJ.first, LockJ.second);
                    }
                }
            }

            if (PT == nullptr || !PT->locks()) {
                return NoneMover;
            }
        }

        // If ri are the read locks for I and rj for J, and
        // if wi are the write locks for I and wj for J, then
        // at this point we have:
        // ( U_j : ri n rj u wi n wj ) != {} <==> PR->locks()
        //
        // Since if either I or J writes to memory, ri resp. rj is empty
        // (see LockSearch), this implies the necessary locks are held

        if (PT != nullptr && PT->locks()) {
            errs () << "NOTICE: Global instruction protected by lock: "<< endll << *I << endll;
            PT->print (true, true, false);
        }
        return BothMover;
    }

    /**
     * Creates a block for this instruction (yield / commit before instruction).
     */
    int
    insertBlock (Instruction *I, block_e yieldType)
    {
    	assert (yieldType != NoBlock);
        LLASSERT (dyn_cast_or_null<PHINode>(I) == nullptr,
                  "insertBlock("<< name(yieldType) <<") on PHI Instruction: "<< endll << *I);

        LLASSERT (!I->isTerminator() || // self-loop exception:
                  dyn_cast_or_null<TerminatorInst>(I)->getSuccessor (0)->getFirstNonPHI () == I,
                  "insertBlock "<< name(yieldType) <<". Instruction:" << *I);

        if (yieldType != StartBlock && ThreadF->Instructions[I].singleThreaded()) {
            return -1;
        }

        unsigned int blockID = ThreadF->BlockStarts.size ();

        block_e ExistingType = isBlockStart(I);
        if (ExistingType != NoBlock) {
            blockID = ThreadF->BlockStarts[I].second; // reuse block ID
        	if (ExistingType == yieldType || ExistingType == LoopBlock2)
        		return blockID;
            yieldType = (block_e) ((int)yieldType | (int)ExistingType);
            errs () << "WARNING: Overwriting dynamic block "<< name(ExistingType) <<" --> "<< name(yieldType) <<": " << *I << endll;
        }

        if (Pass->verbose) errs () << "New " << name(yieldType) << " block: " << *I << "\n";

        //assert (blockID < (1ULL << 16));
        //int globalBlockID = blockID + (1ULL << 16) * ThreadF->index;
        ThreadF->BlockStarts[I] = make_pair (yieldType, blockID);
        return blockID;
    }

    bool
    hasOnlyCommutingAtomicOps (AliasSet *AS, Instruction *I)
    {
        if (!dyn_cast_or_null<AtomicRMWInst>(I)) return false;
        for (Instruction* J : Pass->AS2I[AS]) {
            if (!isCommutingAtomic(I, J)) {
                return false;
                break;
            }
        }
        return true;
    }

    Instruction *
    getFirstNonTerminal (BasicBlock *B)
    {
        return getFirstNonTerminal(B->getFirstNonPHI());
    }

    Instruction *
    getFirstNonTerminal (Instruction *I)
    {
        // Skip empty blocks, as we do not want terminators in BlockStarts
        while (TerminatorInst *T = dyn_cast<TerminatorInst> (I)) {
            LLASSERT (T->getNumSuccessors () == 1, "No support for branching at loop head or thread start: "<< *I);
            Instruction *J = T->getSuccessor (0)->getFirstNonPHI ();
            if (I == J) {
                return J; // self loop
            }
            I = J;
        }
        return I;
    }

	bool
	hasIncomingBackEdge (BasicBlock &B)
	{
		StackElem *X = Stack.empty() ? nullptr : &Stack.back();
		for (pred_iterator PI = pred_begin(&B), E = pred_end(&B); PI != E; ++PI) {
			BasicBlock *Pred = *PI;
			if (Pred == X->Block)
				continue; // no cycle as B is new
			if (&B == Pred || isPotentiallyReachable(B.getTerminator(),
													 &Pred->front())) {
				return true;
			}
		}
		return false;
	}
};

StringRef Collect::Action = "Collecting";
StringRef  Liptonize::Action = "Liptonizing";
StringRef  LockSearch::Action = "LockSearching";

void
LiptonPass::walkGraph ( Instruction *I )
{
    if (TerminatorInst *T = dyn_cast<TerminatorInst> (I)) {
        handle->process (I);

        assert (I == I->getParent()->getTerminator());
        for (int i = 0, num = T->getNumSuccessors(); i < num; ++i) {
            BasicBlock *B = T->getSuccessor(i);
            walkGraph (*B);
        }
        return;
    }

    if (CallInst *call = dyn_cast<CallInst>(I)) {
        DenseMap<Instruction *, Function *> callRecords = Reach->callRecords;
        if (callRecords.find (call) != callRecords.end ()) {
            walkGraph (*callRecords[call]);
        } else if (call->getCalledFunction()) {
           Instruction *Next = handle->handleCall (call);
           if (Next == nullptr) {
               assert (call && call->getCalledFunction());
               errs() << "Handle library call: "<< call->getCalledFunction()->getName() <<"\n";
           } else {
               I = Next;
           }
        } else {
            errs() << "Indirect call: "<< call <<"\n";
        }
    } else {
        assert (!I->isTerminator());
        I = handle->process (I);
    }

    walkGraph (I->getNextNode());
}

void
LiptonPass::walkGraph ( BasicBlock &B )
{
    if (handle->block (B)) {
        assert (!B.empty());
        walkGraph (&B.front());
        handle->deblock (B);
    }
}

void
LiptonPass::walkGraph ( Function &F )
{
    assert (&F);
    if (verbose) errs() << F.getName() << "\n";
    walkGraph (F.getEntryBlock());
}


template <typename ProcessorT>
void
LiptonPass::walkGraph (Module &M)
{
    ProcessorT processor(this);
    handle = &processor;

    errs () <<" -------------------- "<< typeid(ProcessorT).name() <<" -------------------- "<< endll;
    for (pair<Function *, vector<Instruction *>> &X : Reach->Threads) {
        Function *T = X.first;

        // Create new LLVM thread if it doesn't exist
        if (Threads.find(T) == Threads.end()) {
            Threads[T] = new LLVMThread(T, Threads.size());
        }
        processor.thread (T);
        walkGraph (*T);
    }
}

/**
 * Fills the small vector with arguments for the '__pass' function call
 * The following format is used: '__act(t_1, n_11,..., t2, n_21,....  )',
 * where t_x is a function pointer to the thread's functions and
 * { n_xy | y in N } is the set of conflicting blocks in that thread
 */
bool
LiptonPass::conflictingNonMovers (SmallVector<Value *, 8> &sv,
                                  Instruction *I, LLVMThread *T)
{
    // for all other threads
    for (pair<Function *, LLVMThread *> &Thread : Threads) {
        LLVMThread *T2 = Thread.second;
        if (T2 == T && T->isSingleton())
            continue;

        AliasSet *AS = FindAliasSetForUnknownInst (T2->Aliases, I);
        if (AS == nullptr)
            continue;

        DenseSet<int> Blocks;

        // for all conflicting J
        for (Instruction *J : AS2I[AS]) {
            if (isCommutingAtomic(I, J)) continue;

            // for all Block starting points TODO: refine to exit points
            for (pair<Instruction *, pair<block_e, int> > X : T2->BlockStarts) {
                Instruction *R = X.first;
                int         blockID = X.second.second;
                //errs () << *I << endll <<*J << endll << *R <<" ++++++ "<< *R->getNextNode() << endll;

                // if Block is in same process as J, and block can reach J
                bool LReach = isPotentiallyReachable (R, J);
//                bool Own = Reach->stCon (R, J) || R == J;
//                if (Own != LReach) {
//                    errs () << "Missing reachable: "<< endll <<*R << endll << *J << endll << *R->getParent() <<endll << *J->getParent()<<endll;
//                }
                if (!LReach)
                    continue;

                // add block index to __act
                Value *num = Constant::getIntegerValue (Int64, APInt(64, blockID));
                if (Blocks.insert(blockID).second) { // new

                    if (Blocks.size() == 1) {
                        // this is the first R found that may not commute,
                        // first add function identifier for T2:
                        sv.push_back(&T2->F);
                    }

                    sv.push_back (num);
                }
            }
        }
        if (Blocks.size() == T2->BlockStarts.size()) {
            return true; // static yield
        }
    }

    return false;
}

static void
insertYield (Instruction* I, Function *YieldF, int block)
{
    Value *blockId = ConstantInt::get (YieldF->getFunctionType ()->getParamType (0), block);

    CallInst::Create (YieldF, blockId, "", I);
}

static TerminatorInst *
insertDynYield (Instruction* I, Instruction *Cond, block_e type, int block)
{
    TerminatorInst* ThenTerm;
    TerminatorInst* ElseTerm;
    if (type & LoopBlock) {
        SplitBlockAndInsertIfThenElse (Cond, I, &ThenTerm, &ElseTerm);
        insertYield (ElseTerm, YieldLocal, block);
    } else {
        ThenTerm = SplitBlockAndInsertIfThen (Cond, I, false);
    }
    return ThenTerm;
}

void
LiptonPass::dynamicYield (LLVMThread *T, Instruction *I, block_e type, int block)
{
    assert(POSTCOMMIT == TRUE);

    if (type == StartBlock) {
        return;
    } else if (type == LoopBlock) {
        insertYield (I, YieldLocal, block);
        return;
    }

    LLVMInstr &LI = T->Instructions[I];
    area_e Area = LI.Area;
    mover_e Mover = LI.Mover;
    AllocaInst *Phase = T->PhaseVar;

    if (type & LoopBlock2) {
    	assert (type == LoopBlock2);
    	errs () << "Static Loop Yield "<< *I << endll;
    	insertYield (I, YieldGlobal, block);
        if (Mover & RightMover) {
            new StoreInst (PRECOMMIT, Phase, I);
        } else {
        	new StoreInst (POSTCOMMIT, Phase, I);
        }
    	return;
    }

    SmallVector<Value*, 8> sv;

    if (LI.Atomic) { // no yields, just book keeping phase

        if (type & LoopBlock) { // highest change for still catch a Pre phase
            insertYield (I, YieldLocal, block);
        }

        switch (Mover) {
        case LeftMover:
            if (Area != Post) {
                new StoreInst(POSTCOMMIT, Phase, I);
            }
            break;
        case RightMover:
            break;
        case NoneMover: {
            // First collect conflicting non-movers from other threads
            bool staticNM = conflictingNonMovers (sv, I, T);
            LLASSERT (!sv.empty(), "Unexpected ("<< staticNM <<"), no conflicts found for: "<< *I);

            Instruction *ThenTerm = I;
            if (!staticNM) {
                Value *DynConflict = CallInst::Create(Act, sv, "", I);
                ThenTerm = SplitBlockAndInsertIfThen (DynConflict, I, false);
            }
            new StoreInst(POSTCOMMIT, Phase, ThenTerm);
            break;
        }
        default: { ASSERT (false, "Missing case: "<< Mover); }
        }

        return;
    }

    switch (Mover) {
    case LeftMover:
        if (type & LoopBlock)
            insertYield (I, YieldLocal, block);
        if (Area != Post)
            new StoreInst(POSTCOMMIT, Phase, I);
        break;
    case RightMover:
        if (Area == Post) {
            new StoreInst(PRECOMMIT, Phase, I);
            insertYield (I, YieldGlobal, block);
        } else if (Area == Top) {
            LoadInst *P = new LoadInst (Phase, "", I);
            Instruction *ThenTerm = insertDynYield (I, P, type, block);
            new StoreInst(PRECOMMIT, Phase, ThenTerm);
            insertYield (ThenTerm, YieldGlobal, block);
        }
        break;
    case NoneMover: {
        // First collect conflicting non-movers from other threads
        bool staticNM = conflictingNonMovers (sv, I, T);
        LLASSERT (!sv.empty(), "Unexpected("<< staticNM <<"), no conflicts found for: "<< *I);

        // if in dynamic conflict (non-commutativity)
        Instruction *NextTerm = I;
        if (!noDyn && !staticNM) {
            CallInst *ActCall = CallInst::Create(Act, sv, "", NextTerm);
            NextTerm = insertDynYield (NextTerm, ActCall, type, block);
        }
        switch (Area) {
        case Top: {
            LoadInst *P = new LoadInst (Phase, "", NextTerm);
            Instruction *PhaseTerm = insertDynYield (NextTerm, P, type, block);
            new StoreInst (PRECOMMIT, Phase, PhaseTerm); // Temporarily for yield
            insertYield (PhaseTerm, YieldGlobal, block);
            // in NextTerm:
            new StoreInst(POSTCOMMIT, Phase, NextTerm);
            break; }
        case Post:
            insertYield (NextTerm, YieldGlobal, block); // fallthrough:
        case Pre:
        case Bottom:
            new StoreInst(POSTCOMMIT, Phase, NextTerm);
            break;
        default: { ASSERT (false, "Missing case: "<< Area); }
        }

        break;
    }
    default: { ASSERT (false, "Missing case: "<< Mover); }
    }
}

void
LiptonPass::initialInstrument (Module &M)
{
    // Add '__act' and '__yield' functions
    Type *Int = Type::getInt32Ty (M.getContext ());
    Type *Void = FunctionType::getVoidTy (M.getContext ());
    Constant *C = M.getOrInsertFunction (__YIELD, Void, Int, (Type*)(0));
    YieldGlobal = cast<Function> (C);


    Constant *C3 = M.getOrInsertFunction (__YIELD_LOCAL, Void, Int, (Type*)(0));
    YieldLocal = cast<Function> (C3);

    Type *Bool = Type::getInt1Ty (M.getContext ());
    Constant *C2 = M.getOrInsertFunction (__ACT, FunctionType::get (Bool, true));
    Act = cast<Function> (C2);
    Int64 = Type::getInt64Ty(M.getContext());
}

void
LiptonPass::staticYield (LLVMThread *T, Instruction *I, block_e type, int block)
{
    if (type == StartBlock) {
        return;
    } else if (type == LoopBlock) {
        insertYield (I, YieldLocal, block);
    } else { // YieldBlock or combinations
        LLVMInstr &LI = T->Instructions[I];

        if (LI.Atomic) {
            if (type & LoopBlock)
                insertYield (I, YieldLocal, block);
            return;
        }
        if ((LI.Mover == RightMover || LI.Mover == NoneMover) && (LI.Area & Post)) {
            insertYield (I, YieldGlobal, block);
        } else if (type & LoopBlock) {
            insertYield (I, YieldLocal, block);
        }
    }
}

void
LiptonPass::finalInstrument (Module &M)
{
    Type *Bool = Type::getInt1Ty (M.getContext());
    TRUE = ConstantInt::get (Bool, 1);
    FALSE = ConstantInt::get (Bool, 0);
    PRECOMMIT = FALSE;
    POSTCOMMIT = TRUE;

    if (staticAll) {
        for (pair<Function *, LLVMThread *> X : Threads) {
            LLVMThread *T = X.second;

            for (pair<Instruction *, pair<block_e, int>> Y : T->BlockStarts) {
                int block = Y.second.second;
                Instruction *I = Y.first;
                block_e type = Y.second.first;

                staticYield (T, I, type, block);
            }
        }
    } else {
        // collect thread initial instructions (before instrumenting threads)
        DenseMap<Function *, Instruction *> Starts;
        for (pair<Function *, LLVMThread *> X : Threads) {
            Function *T = X.first;
            Instruction *Start = T->getEntryBlock().getFirstNonPHI();
            AllocaInst *Phase = new AllocaInst (Bool, "__phase", Start);
            new StoreInst (PRECOMMIT, Phase, Start);
            X.second->PhaseVar = Phase;
        }

        // instrument code with dynamic yields
        for (pair<Function *, LLVMThread *> X : Threads) {
            LLVMThread *T = X.second;

            for (pair<Instruction *, pair<block_e, int>> Y : T->BlockStarts) {
                int block = Y.second.second;
                Instruction *I = Y.first;
                block_e type = Y.second.first;
                dynamicYield (T, I, type, block);
            }
        }
    }
}

void
LiptonPass::deduceInstances ()
{
    for (pair<Function *, vector<Instruction *>> &X : Reach->Threads) {
        Function *T = X.first;
        LLVMThread *TT = Threads[T];

        TT->Runs = Reach->Threads[T].size ();
        for (Instruction *I : Reach->Threads[T]) {
            if (I == nullptr)
                break; // MAIN
            if (TT->Instructions[I].Loops) {
                TT->Runs = -1; // potentially infinite

                assert (T);
                errs () << "THREAD: " << T->getName ()
                        << " (Potentially infinite)" << endll << *I << endll;
                break;
            }
        }
    }
}

bool
LiptonPass::runOnModule (Module &M)
{
    AA = &getAnalysis<AliasAnalysis> ();

    // Statically find instructions for which invariantly a lock is held
    walkGraph<LockSearch> (M);

    // Collect thread reachability info +
    // Collect movability info
    walkGraph<Collect> (M);

    deduceInstances ();

    // Identify and number blocks statically
    // (assuming all dynamic non-movers are static non-movers)
    walkGraph<Liptonize> (M);

    errs () <<" -------------------- "<< "Instrumentation" <<" -------------------- "<< endll;

    // Add '__act' and '__yield' function definitions
    initialInstrument (M);

    // Insert dynamic yields
    finalInstrument (M);

    return true; // modified module by inserting yields
}

} // LiptonPass

