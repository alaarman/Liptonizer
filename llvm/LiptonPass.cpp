
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


static char PTHREAD_CREATE[100];
static int  PTHREAD_CREATE_F_IDX = 1;
static char PTHREAD_JOIN[100];
static char PTHREAD_KILL[100];

static const char *PTHREAD1_CREATE   = "__thread_spawn";
static const int   PTHREAD1_CREATE_F_IDX = 1;
static const char *PTHREAD1_JOIN     = "__thread_join";
static const char *PTHREAD1_KILL     = "__thread_kill";

static const char *PTHREAD2_CREATE   = "pthread_create";
static const int   PTHREAD2_CREATE_F_IDX = 2;
static const char *PTHREAD2_JOIN     = "pthread_join";
static const char *PTHREAD2_KILL     = "pthread_kill";


static const char *ASSERT           = "assert";
static const char *__YIELD          = "__yield";
static const char *__YIELD_LOCAL    = "__yield_local";
static const char *__ACT            = "__act";
static const char *PTHREAD_YIELD    = "pthread_yield";
static const char *PTHREAD_LOCK     = "pthread_mutex_lock";
static const char *PTHREAD_RLOCK    = "pthread_rwlock_rdlock";
static const char *PTHREAD_WLOCK    = "pthread_rwlock_wrlock";
static const char *PTHREAD_RW_UNLOCK= "pthread_rwlock_unlock";
static const char *PTHREAD_UNLOCK   = "pthread_mutex_unlock";
static const char *PTHREAD_MUTEX_INIT= "pthread_mutex_init";
static const char *PTHREAD_COND_REG = "__cond_register";
static const char *PTHREAD_COND_WAIT= "__cond_wait";
static const char *PTHREAD_COND_SGNL= "__cond_signal";
static const char *PTHREAD_COND_BCST= "__cond_broadcast";
static const char *ATOMIC_BEGIN     = "atomic_begin";
static const char *ATOMIC_END       = "atomic_end";

char LiptonPass::ID = 0;
static RegisterPass<LiptonPass> X("lipton", "Lipton reduction");

Function                       *YieldGlobal = nullptr;
Function                       *YieldLocal = nullptr;
Function                       *Assert = nullptr;
Function                       *Act = nullptr;
Type                           *Int64 = nullptr;

int                             nextBlock = 0;

static const char *SINGLE_THREADED = "singleThreaded";
static const char *DYN_YIELD_CONDITION = "DynamicYieldCondition";


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
        opts(*new Options())
{ }

LiptonPass::LiptonPass (string name, Options &opts)
                                                            : ModulePass(ID),
        Name (name),
        opts(opts)
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
    DenseMap<Instruction *, pair<block_e, int>>::iterator Start = ThreadF->BlockStarts.find(I);
	if (Start != ThreadF->BlockStarts.end()) {
	    pair<Instruction *, pair<block_e, int>>  &X = *Start;
	    return X.second.first;
    }
	return NoBlock;
}

LLVMInstr &
LLVMThread::getInstruction (Instruction *I)
{
    LLASSERT (&this->F == I->getParent()->getParent(),
              "Different thread: "<< this->F.getName() << " <> "<<
              I->getParent()->getParent()->getName());
    if (Instructions.find(I) == Instructions.end()) {
        Instructions.insert(make_pair(I, new LLVMInstr(I)));
    }
    return *(*Instructions.find(I)).second;
}

int
LLVMThread::NrRuns ()
{
    int Runs = Starts.size ();
    for (CallInst *C : Starts) {
        if (C == nullptr)
            break; // MAIN
        Function *Starter = C->getParent ()->getParent ();
        LLASSERT (Threads->find(Starter) != Threads->end(), "Thread created? "<< Starter->getName());
        if (Threads[0][Starter]->getInstruction(C).SCC->Loops) {
            Runs = -1; // potentially infinite
            errs () << "THREAD: " << F.getName () << " (Potentially infinite)" << endll << *C << endll;
            break;
        }
    }
    return Runs;
}

bool
LLVMThread::isSingleton ()
{
    return NrRuns() == 1;
}

static Instruction *
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

static bool
isCommutingAtomic (Instruction *I, Instruction *J)
{
    AtomicRMWInst *A = dyn_cast_or_null<AtomicRMWInst>(I);
    AtomicRMWInst *B = dyn_cast_or_null<AtomicRMWInst>(J);
    if ((A || B) && !(A && B)) {
        //errs () << "ATOMIC: "<< *I <<": "<< *J << endll;

        AtomicRMWInst *C = A ? A : B;
        switch (C->getOperation()) {
        case AtomicRMWInst::BinOp::Add:
        case AtomicRMWInst::BinOp::Sub:
            errs () << "WARNING: ATOMIC? "<< *I <<": "<< *J << endll;
            return true;
        default:
            break;
        }
    }
    if (!A) return false;
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

PTCallType *
PThreadType::merge1 (PThreadType *PT)
{
    for (PTCallType &CT2 : *PT->WriteLocks) {
        if (!findAlias(TotalLock, *CT2.first)) {
            WriteLocks->push_back(CT2);
            return &CT2;
        }
    }
    return nullptr;
}

bool
PThreadType::operator<=(PThreadType &O)
{
    for (PTCallType &Call : *ReadLocks) {
        if (checkAlias(*O.ReadLocks, *Call.first) != 1) {
            return false;
        }
    }
    for (PTCallType &Call : *WriteLocks) {
        if (checkAlias(*O.WriteLocks, *Call.first) != 1) {
            return false;
        }
    }
    if (!O.CorrectThreads) return true;
    if (!CorrectThreads) return false;
    for (PTCallType &Call : *Threads) {
        if (checkAlias(*O.Threads, *Call.first) != 1) {
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
        for (PTCallType X : *ReadLocks) {
            errs () << *X.second << endll;
        }
    }
    if (write) {
        errs () << "WRITE LOCKS: "<< endll;
        for (PTCallType X : *WriteLocks) {
            errs () << *X.second << endll;
        }
    }
    if (threads) {
        if (!CorrectThreads) {
            errs () << "THREADS Incorrect " << endll;
        } else {
            errs () << "THREADS seen: " << endll;
            for (PTCallType X : *Threads) {
                errs () << *X.second << endll;
            }
        }
    }
}

bool
PThreadType::locks ()
{
    return !ReadLocks->empty() || !WriteLocks->empty();
}

bool
PThreadType::locks1 ()
{
    return WriteLocks->size() == 1;
}

PTCallType *
PThreadType::get1Lock ()
{
    return &WriteLocks->front();
}

int
PThreadType::findAlias (pt_e kind, const AliasAnalysis::Location &Loc)
{
    if (kind == ThreadStart) {
        if (!CorrectThreads) return false;
        return checkAlias (*Threads, Loc);
    }
    if (kind & ReadLock) {
        return checkAlias (*ReadLocks, Loc);
    }
    if (kind & TotalLock) {
        return checkAlias (*WriteLocks, Loc);
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
            PT->ReadLocks->resize (0);
        }
        if (kind & TotalLock) {
            PT->WriteLocks->resize (0);
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
        removeAlias (*PT->Threads, &Loc);
    } else {
        int count = 0;
        if (kind & ReadLock) {
            count += removeAlias (*PT->ReadLocks, &Loc);
        }
        if (kind & TotalLock) {
            count += removeAlias (*PT->WriteLocks, &Loc);
        }
        assert (count == 1);
    }
    return PT;
}

PThreadType *
PThreadType::resizeReadLocks (int size)
{
    PThreadType *O = new PThreadType(this);
    O->ReadLocks->resize(0);
    return O;
}

void
PThreadType::eraseNonAlias (pt_e kind, PThreadType *O)
{
    if (kind == ThreadStart) {
        for (PTCallType &LockJ : *O->Threads) { // intersection:
            eraseNonAlias (ThreadStart, *LockJ.first, LockJ.second);
        }
    } else if (kind == ReadLock) {
        for (PTCallType &LockJ : *O->ReadLocks) { // intersection:
            eraseNonAlias (ReadLock, *LockJ.first, LockJ.second);
        }
    } else if (kind == TotalLock || kind == AnyLock) {
        for (PTCallType &LockJ : *O->WriteLocks) { // intersection:
            eraseNonAlias (TotalLock, *LockJ.first, LockJ.second);
        }
    }
}

void
PThreadType::eraseNonAlias (pt_e kind, const AliasAnalysis::Location &Loc, CallInst *Call)
{
    if (kind == ThreadStart) {
        removeNonAlias (*Threads, Loc);
    } else if (kind == ReadLock) {
        removeNonAlias (*ReadLocks, Loc);
    } else if (kind == TotalLock || kind == AnyLock) {
        removeNonAlias (*WriteLocks, Loc);
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
        PT->Threads->push_back (make_pair(L, Call));
    } else if (kind & ReadLock) {
        PT->ReadLocks->push_back (make_pair(L, Call));
    } else if (kind & TotalLock) {
        PT->WriteLocks->push_back (make_pair(L, Call));
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

enum state_e {
    Unvisited   = 0,
    Stacked     = 1,
    Visited     = 2,
};

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

    DenseMap<BasicBlock *, LockVisited *>   Seen;
    vector<BasicBlock *>                    Stack;

    // Will always point to the one on the top of the stack or an empty struct
    // Access policy: copy-on-write
    PThreadType                    *PT = nullptr;

    LockSearch::LockVisited &
    getBlock (BasicBlock &B)
    {
        if (Seen.find(&B) == Seen.end()) {
            Seen.insert(make_pair(&B, new LockVisited()));
        }
        return *(*Seen.find(&B)).second;
    }

    // block and deblock implement revisiting
    bool
    block ( BasicBlock &B )
    {
        LockVisited &V = getBlock (B);

        if (V.State != Unvisited && *V.PT <= *PT) {
            return false;
        }
        if (Pass->opts.verbose) {
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
                getBlock(*Old).State = Visited;
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
        if (Pass->opts.verbose) PT->print (true, true, false);

        LockVisited &V = getBlock (B);
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

        // Only main starts out single threaded
        PT = new PThreadType(T->getName().equals("main")); //TODO: could be more precize
    }

    void
    addPThread (CallInst *Call, pt_e kind, bool add)
    {
        if (Pass->opts.nolock && kind != ThreadStart) return;
        if (kind == ThreadStart && !PT->isCorrectThreads()) return; // nothing to do

        AliasAnalysis::Location L;
        AliasAnalysis::ModRefResult Mask;
//        if (kind == ThreadStart && !add) { // PTHREAD_JOIN
//            Value *Temp = Call->getArgOperand(0);
//            LoadInst *Load = dyn_cast<LoadInst>(Temp);
//            L = AA->getLocation(Load);
//        } else {
        if (Call->getCalledFunction()->getName().endswith(PTHREAD_COND_WAIT)) {
            if (LoadInst *Load = dyn_cast_or_null<LoadInst>(Call->getArgOperand(1))) {
                L = AA->getLocation(Load);
            } else {
                L = AA->getArgLocation (Call, 1, Mask);
            }
        } else {
            if (LoadInst *Load = dyn_cast_or_null<LoadInst>(Call->getArgOperand(0))) {
                L = AA->getLocation(Load);
            } else {
                L = AA->getArgLocation (Call, 0, Mask);
            }
        }
//        }

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
        doHandle (Call);

        if (Call->getCalledFunction()->getName().endswith(PTHREAD_YIELD)) {
        } else if (Call->getCalledFunction()->getName().endswith(ASSERT)) {
        } else if (Call->getCalledFunction()->getName().endswith("llvm.expect.i64")) {
        } else if (Call->getCalledFunction()->getName().endswith(PTHREAD_LOCK)) {
            addPThread (Call, TotalLock, true);
        } else if (Call->getCalledFunction()->getName().endswith(PTHREAD_RLOCK)) {
            addPThread (Call, ReadLock, true);
        } else if (Call->getCalledFunction()->getName().endswith(PTHREAD_WLOCK)) {
            addPThread (Call, TotalLock, true);
        } else if (Call->getCalledFunction()->getName().endswith(PTHREAD_RW_UNLOCK)) {
            addPThread (Call, AnyLock, false);
        } else if (Call->getCalledFunction()->getName().endswith(PTHREAD_COND_REG)) {
        } else if (Call->getCalledFunction()->getName().endswith(PTHREAD_COND_WAIT)) {
            addPThread (Call, TotalLock, true);
        } else if (Call->getCalledFunction()->getName().endswith(PTHREAD_COND_SGNL)) {
        } else if (Call->getCalledFunction()->getName().endswith(PTHREAD_COND_BCST)) {
        } else if (Call->getCalledFunction()->getName().endswith(PTHREAD_UNLOCK)) {
            addPThread (Call, TotalLock, false);
        } else if (Call->getCalledFunction()->getName().endswith(PTHREAD_CREATE)) {
            addPThread (Call, ThreadStart, true);
            ThreadF->getInstruction(Call).isPTCreate = true;
        } else if (Call->getCalledFunction()->getName().endswith(PTHREAD_JOIN)) {
            addPThread (Call, ThreadStart, false);
        } else if (Call->getCalledFunction()->getName().endswith(PTHREAD_MUTEX_INIT)) {
        } else if (Call->getCalledFunction()->getName().endswith(ATOMIC_BEGIN)) {
            LLASSERT (!PT->isAtomic(), "Already "<< ATOMIC_BEGIN <<"encountered before: "<< Call << endll);
            PT = PT->flipAtomic ();
        } else if (Call->getCalledFunction()->getName().endswith(ATOMIC_END)) {
            LLASSERT (PT->isAtomic(), "No "<< ATOMIC_BEGIN <<"encountered before: "<< Call << endll);
            PT = PT->flipAtomic ();
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
        LLVMInstr &LI = ThreadF->getInstruction(I);
        LI.Atomic = PT->isAtomic();
        if (I->mayWriteToMemory()) {
            LI.PT = PT->resizeReadLocks (0);
        } else {
            LI.PT = PT;
        }
    }
};


/**
 * Thread / instruction reachability processor
 *
 * Complexity: P X N
 */
struct Collect : public LiptonPass::Processor {

    static StringRef                Action;

    // See Gabow's SCC algorithm extended with stack identification
    int                                         scc = 0;
    vector<BasicBlock *>                        S;
    vector<int>                                 B;
    DenseMap<BasicBlock *, int>                 I;

    static inline bool New  (int i) { return i == 0; }
    static inline bool SCC  (int i) { return i < 0; }
    static inline bool Live (int i) { return i > 0; }
    inline bool Stack(int i) { return i > 0 && S[i] == nullptr; }

    Collect(LiptonPass *Pass) : LiptonPass::Processor(Pass) { }
    ~Collect() { }

    Instruction *
    handleCall (CallInst *Call)
    {
        return Call;
    }

    bool
    block ( BasicBlock &BB )
    {
        int         &IB = I[&BB];

        if (Pass->opts.verbose) errs() << Action << ": " << BB << IB <<endll;
        if (New(IB)) {
            IB = S.size();
            B.push_back (S.size());
            S.push_back (nullptr);      // indicates on-stack (null)
            return true;                // recurse
        } else if (Live(IB)) {
            if (Stack(IB)) {
                Instruction *I = getFirstNonTerminal(BB.getFirstNonPHI());
                ThreadF->getInstruction(I).FVS = true;
            }
            while (B.back() > IB) { B.pop_back(); }
        }
        return false;
    }

    void
    deblock ( BasicBlock &BB )
    {
        int         &IB = I[&BB];

        S[IB] = &BB;    // reinsert basic block when backtracking (off stack)

        if (IB == B.back()) {
            scc--;
            LLVMSCC     *SCC = new LLVMSCC (ThreadF); // record SCC
            while (IB <= S.size()) {
                BasicBlock *XX = S.back ();
                for (Instruction &II : *XX)
                    SCC->add (&II);
                assert (XX != nullptr);
                I[XX] = scc;
                S.pop_back ();
            }
            B.pop_back ();
        }
    }

    void
    thread (Function *T)
    {
        assert (S.empty() && B.empty());
        scc = 0;
        I.clear ();

        ThreadF = Pass->Threads[T];
    }

    Instruction *
    process (Instruction *I)
    {
        LLVMInstr &LI = ThreadF->getInstruction (I);
        if ( I->isTerminator() ||
                dyn_cast_or_null<PHINode>(I) != nullptr ||
                !I->mayReadOrWriteMemory() ||
                isa<DbgInfoIntrinsic>(I) ||
                LI.singleThreaded ()) {
            return I;
        }

        ThreadF->Aliases->add (I);

        AliasSet *AS = FindAliasSetForUnknownInst (ThreadF->Aliases, I);
        Pass->AS2I[AS].push_back(&LI);
        return I;
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
            if (Pass->opts.verbose) errs() << name(Area)  <<": "<< B << "\n";

            Stack.push_back ( StackElem(Area, &B) );
            V.Index = -Stack.size();

            return true;
        } else if (V.Index < 0) { // Stack

            Instruction *Start = getFirstNonTerminal (B.getFirstNonPHI());
            insertBlock (Start, LoopBlock);                 // Close cycle

            StackElem &Previous = Stack[-V.Index - 1];
            if (Previous.Area < Area) {
                if (Pass->opts.verbose) errs() << name(Area)  <<" --(revisit)--> "<<  name(Previous.Area) <<": "<< B << "\n";
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
                if (Pass->opts.verbose) errs() << name(Area)  <<" --(revisit)--> "<<  name(V.Area) <<": "<< B << "\n";
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
        (void) b;
    }

    Instruction *
    handleCall (CallInst *Call)
    {
        assert (Call && Call->getCalledFunction());

        LLVMInstr &LI = ThreadF->getInstruction(Call);

        mover_e Mover;
        if (LI.singleThreaded()) {
            Mover = BothMover;
        } else if (Call->getCalledFunction()->getName().endswith(PTHREAD_CREATE)) {
            Mover = LeftMover;
        } else if (Call->getCalledFunction()->getName().endswith(PTHREAD_YIELD)) {
            errs () << "WARNING: pre-existing Yield call: "<< *Call <<"\n";
            Area = Bottom;
            return Call;
        } else if (Call->getCalledFunction()->getName().endswith(PTHREAD_LOCK)) {
            Mover = RightMover;
        } else if (Call->getCalledFunction()->getName().endswith(PTHREAD_RLOCK)) {
            Mover = RightMover;
        } else if (Call->getCalledFunction()->getName().endswith(PTHREAD_WLOCK)) {
            Mover = RightMover;
        } else if (Call->getCalledFunction()->getName().endswith(PTHREAD_RW_UNLOCK)) {
            Mover = LeftMover;
        } else if (Call->getCalledFunction()->getName().endswith(PTHREAD_COND_REG)) {
            Mover = LeftMover;
        } else if (Call->getCalledFunction()->getName().endswith(PTHREAD_COND_WAIT)) {
            Mover = RightMover;
        } else if (Call->getCalledFunction()->getName().endswith(PTHREAD_COND_SGNL)) {
            Mover = BothMover;
        } else if (Call->getCalledFunction()->getName().endswith(PTHREAD_COND_BCST)) {
            Mover = BothMover;
        } else if (Call->getCalledFunction()->getName().endswith(PTHREAD_UNLOCK)) {
            Mover = LeftMover;
        } else if (Call->getCalledFunction()->getName().endswith(PTHREAD_JOIN)) {
            Mover = RightMover;
        } else if (Call->getCalledFunction()->getName().endswith(ATOMIC_BEGIN)) {
            assert (!ThreadF->getInstruction(Call).Atomic);
            Mover = RightMover; // force (dynamic) yield (for Post/Top)
        } else if (Call->getCalledFunction()->getName().endswith(ATOMIC_END)) {
            return Call;
        } else if (Call->getCalledFunction()->getName().endswith(PTHREAD_MUTEX_INIT)) {
            return Call;
        } else if (Call->getCalledFunction()->getName().endswith(ASSERT)) {
            return Call;
        } else if (Call->getCalledFunction()->getName().endswith("llvm.expect.i64")) {
            return Call;
        } else {
            return nullptr;
        }

        doHandle (LI, Call, Mover);

        return Call;
    }


    Instruction *
    process (Instruction *I)
    {
        LLVMInstr &LI = ThreadF->getInstruction(I);

        mover_e Mover = LI.Mover;
        if (Mover == -1) {
            Mover = movable (LI, I);
        }

        return doHandle (LI, I, Mover);
    }

private:
    Instruction *
    doHandle (LLVMInstr &LI, Instruction *I, mover_e Mover) // may overwrite less dynamic blocks
    {
        if (Pass->opts.verbose) errs () << name(Area) << *I << " -> \t"<< name(Mover) << "\n";

        if ((LI.Area == Pre && Area == Post) ||
            (LI.Area == Post && Area == Pre)) // 0 iff undefined
            Area = Top;
        LI.Area = Area;
        LI.Mover = Mover;

        addMetaData (I, name(Area), "");
        if (Mover != BothMover) {
            addMetaData (I, name(Mover), "");
        }
        if (LI.singleThreaded()) {
            addMetaData (I, SINGLE_THREADED, "");
        }

        if (Pass->opts.allYield && !I->isTerminator() && dyn_cast_or_null<PHINode>(I) == nullptr) {
            Instruction *Start = getFirstNonTerminal (I);
            insertBlock (Start, LoopBlock);
        }

        switch (Mover) {
        case RightMover:
            if (Area & Post) { // Post, Top
                insertBlock (I, YieldBlock);
            }
            if (LI.PT->isAtomic()) {
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

        bool conflict = false;
        PThreadType *PT = nullptr; // will store lock set if necessary
        assert (LI.PT != nullptr);

        for (pair<Function *, LLVMThread *> &X : Pass->Threads) {
            LLVMThread *T2 = X.second;
            if (T == T2 && T->isSingleton()) continue;

            AliasSet *AS = FindAliasSetForUnknownInst (T2->Aliases, I);
            if (AS == nullptr)  continue;
			for (LLVMInstr *LJ : Pass->AS2I[AS]) {
				if (isCommutingAtomic(I, LJ->I)) continue;
				if (!I->mayWriteToMemory() && !LJ->I->mayWriteToMemory()) continue;

				conflict = true;
	            if (!LI.PT->locks() || !LJ->PT->locks()) break;
				if (PT == nullptr) {
					PT = new PThreadType (LI.PT); // copy
				}
				PT->eraseNonAlias (ReadLock, LJ->PT);
				PT->eraseNonAlias (TotalLock, LJ->PT);
			}

            if (conflict && (PT == nullptr || !PT->locks())) {
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

        if (yieldType != StartBlock && ThreadF->getInstruction(I).singleThreaded()) {
            return -1;
        }

        unsigned int blockID = ThreadF->BlockStarts.size ();

        block_e ExistingType = isBlockStart(I);
        if (ExistingType != NoBlock) {
            blockID = ThreadF->BlockStarts[I].second; // reuse block ID
        	if (ExistingType == yieldType)
        		return blockID;
            yieldType = (block_e) ((int)yieldType | (int)ExistingType);
            errs () << "WARNING: Overwriting dynamic block "<< name(ExistingType) <<" --> "<< name(yieldType) <<": " << *I << endll;
        }

        if (Pass->opts.verbose) errs () << "New " << name(yieldType) << " block: " << *I << "\n";

        //assert (blockID < (1ULL << 16));
        //int globalBlockID = blockID + (1ULL << 16) * ThreadF->index;
        ThreadF->BlockStarts[I] = make_pair (yieldType, blockID);
        return blockID;
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
        for (int i = 0, num = T->getNumSuccessors(); i < num; ++i) {
            BasicBlock *B = T->getSuccessor(i);
            walkGraph (*B);
        }
        return;
    }

    if (CallInst *Call = dyn_cast<CallInst>(I)) {
        Function *Callee = Call->getCalledFunction ();
        if (!Callee->isIntrinsic() && !Callee->isDeclaration()) {
            walkGraph (*Callee);
        } else {
           Instruction *Next = handle->handleCall (Call);
           if (Next == nullptr) {
               errs() << "Handle library call: "<< Call->getCalledFunction()->getName() <<"\n";
           } else {
               I = Next;
           }
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
    if (opts.verbose) errs() << F.getName() << "\n";
    walkGraph (F.getEntryBlock());
}


template <typename ProcessorT>
void
LiptonPass::walkGraph (Module &M)
{
    ProcessorT processor(this);
    handle = &processor;

    for (pair<Function *, LLVMThread *> &X : Threads) { // TODO: extended while iterting
        Function *T = X.first;

        processor.thread (T);
        walkGraph (*T);
    }
}

Constant *
obtainFixedCasConstant (Instruction *I)
{
    AtomicCmpXchgInst *Cas = dyn_cast_or_null<AtomicCmpXchgInst>(I);
    if (Cas == nullptr) return nullptr;
    Value *op1 = Cas->getOperand(1);
    return dyn_cast_or_null<Constant> (op1);
}


/**
 * From all conflicting instructions, extract a list of all fixed CAS operations
 * iff they are the only conflicting instructions that write.
 *
 * A fixed CAS, checks for a constant value as swap condition.
 */
bool
obtainFixedCasValue (SmallVector<AtomicCmpXchgInst *, 8> &cs,
                     SmallVector<LLVMInstr *, 8> &Is,
                     Instruction *I, bool verbose)
{
    bool SeenI = false;
    if (I->mayWriteToMemory() && obtainFixedCasConstant(I) == nullptr) {
        return false;
    }

    if (verbose) errs () <<"Check CAS:"<< *I <<endll;
	for (LLVMInstr *LJ : Is) {
	    if (verbose) errs () <<"\t"<< * LJ->I <<endll;
	    if (obtainFixedCasConstant(LJ->I) != nullptr) {
	        if (I->getOperand(0)->getType() != LJ->I->getOperand(0)->getType()) {
	            if (verbose) errs () <<"CAS Type mismatch:"<< *I << "  --  "<< * LJ->I <<endll;
                return false;
            }
	        cs.push_back (dyn_cast<AtomicCmpXchgInst>(LJ->I));
	    } else if (LJ->I->mayWriteToMemory()) {
            if (verbose) errs () <<"CAS Type mismatch:"<< *I << "  --  "<< * LJ->I <<endll;
            return false;
        }
	    SeenI |= I == LJ->I;
	}
	if (!SeenI && obtainFixedCasConstant(I) != nullptr) {
	    cs.push_back (dyn_cast<AtomicCmpXchgInst>(I));
	}
	return !cs.empty();
}

/**
 * Fills the small vector with arguments for the '__pass' function call
 * The following format is used: '__act(t_1, n_11,..., t2, n_21,....  )',
 * where t_x is a function pointer to the thread's functions and
 * { n_xy | y in N } is the set of conflicting blocks in that thread
 */
bool
LiptonPass::conflictingNonMovers (SmallVector<Value *, 8> &sv,
                                  SmallVector<LLVMInstr *, 8> *Is,
                                  Instruction *I, LLVMThread *T)
{
    bool staticYield = false;
    // for all other threads
    for (pair<Function *, LLVMThread *> &Thread : Threads) {
        LLVMThread *T2 = Thread.second;
        if (T2 == T && T->isSingleton()) continue;

        AliasSet *AS = FindAliasSetForUnknownInst (T2->Aliases, I);
        if (AS == nullptr) continue;

        DenseSet<int> Blocks;
        // for all conflicting J
        for (LLVMInstr *LJ : AS2I[AS]) {
            if (isCommutingAtomic(I, LJ->I)) continue;
            if (!I->mayWriteToMemory() && !LJ->I->mayWriteToMemory()) continue;

            if (Is != nullptr) Is->push_back(LJ);

            // for all Block starting points TODO: refine to exit points
            for (pair<Instruction *, pair<block_e, int> > X : T2->BlockStarts) {
                Instruction *R = X.first;
                int         blockID = X.second.second;
                //errs () << *I << endll <<*J << endll << *R <<" ++++++ "<< *R->getNextNode() << endll;

                if (R != LJ->I && !isPotentiallyReachable(R, LJ->I)) continue;
                // if R = J or R can reach J

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
            staticYield = true; // static yield
        }
    }

    return staticYield;
}

static void
insertYield (Instruction* I, Function *YieldF, int block)
{
    Value *blockId = ConstantInt::get (YieldF->getFunctionType ()->getParamType (0), block);
    CallInst::Create (YieldF, blockId, "", I);
}

bool
leftMoverInSCC (LLVMSCC *SCC)
{
    for (LLVMInstr *LI : SCC->Insts) {
        if (LI->Mover == LeftMover) {
            return true;
        }
    }
    return false;
}

bool
LLVMSCC::hasLeftMovers ()
{
    if (hasLeft == -1)
        hasLeft = leftMoverInSCC (this);
    return hasLeft;
}

static void
insertLoopYields (LLVMInstr &NM, Instruction *I, int block,
                  AllocaInst* Phase)
{
    if (NM.Area == Top && NM.SCC->hasLeftMovers()) {
        TerminatorInst *ThenTerm;
        TerminatorInst *ElseTerm;
        LoadInst *P = new LoadInst (Phase, "", I);
        SplitBlockAndInsertIfThenElse (P, I, &ThenTerm, &ElseTerm);

        // then (post)
        new StoreInst (PRECOMMIT, Phase, ThenTerm);
        insertYield (ThenTerm, YieldGlobal, block);

        // else (pre)
        insertYield (ElseTerm, YieldLocal, block);
    } else if (NM.Area == Post) {
        new StoreInst (PRECOMMIT, Phase, I);
        insertYield (I, YieldGlobal, block);
    } else {
        insertYield (I, YieldLocal, block);
    }
}

static TerminatorInst *
insertDynYield (LLVMInstr &NM, Instruction *Before, Value *Cond,
                block_e type, int block, AllocaInst *Phase)
{
    TerminatorInst *ThenTerm;
    TerminatorInst *ElseTerm;
    if (type & LoopBlock) {
        SplitBlockAndInsertIfThenElse (Cond, Before, &ThenTerm, &ElseTerm);
        insertLoopYields (NM, ElseTerm, block, Phase);
    } else {
        ThenTerm = SplitBlockAndInsertIfThen (Cond, Before, false);
    }
    return ThenTerm;
}

void
checkAssert (bool v, Instruction *I, AllocaInst* Phase, area_e Area)
{
    if (!v) return;

    Instruction *P = new LoadInst (Phase, "", I);
    if (Area == Pre)
        P = new ICmpInst(I, CmpInst::Predicate::ICMP_EQ,  P, PRECOMMIT);
    CallInst::Create (Assert, P, "", I);
}

Instruction *
LiptonPass::addFixedCAS (LLVMInstr &LI, block_e type, int block,
                         Instruction *NextTerm, SmallVector<LLVMInstr *, 8> &Is,
                         AllocaInst *Phase)
{
    // First collect conflicting non-movers from other threads
    SmallVector<AtomicCmpXchgInst *, 8> cs;
    bool fixedCAS = obtainFixedCasValue (cs, Is, LI.I, opts.verbose);
    if (!opts.nodyn && fixedCAS) {
        Instruction *ValChecks = nullptr;
        Value *Ptr = LI.I->getOperand (0);
        LoadInst *PtrVal = new LoadInst (Ptr, "", NextTerm);
        for (AtomicCmpXchgInst* Cas : cs) {
            errs () << "CAS: " << *Cas << endll;
            Constant *C = obtainFixedCasConstant (Cas);
            Instruction *New = new ICmpInst (NextTerm, CmpInst::Predicate::ICMP_EQ,
                                             PtrVal, C);
            if (ValChecks == nullptr) {
                ValChecks = New;
            } else {
                ValChecks = BinaryOperator::Create (BinaryOperator::BinaryOps::Or,
                                                    ValChecks, New, "", NextTerm);
            }
            break;
        }
        NextTerm = insertDynYield (LI, NextTerm, ValChecks, type, block, Phase);
        addMetaData (ValChecks, DYN_YIELD_CONDITION, "");
    }
    return NextTerm;
}


Value *
LiptonPass::obtainFixedPtr (LLVMInstr &LI)
{
    Value *Ptr;
    if (LoadInst *L = dyn_cast_or_null<LoadInst>(LI.I)) {
       Ptr = L->getPointerOperand();
    } else if (StoreInst *S = dyn_cast_or_null<StoreInst>(LI.I)) {
        Ptr = S->getPointerOperand();
    } else if (CallInst *C = dyn_cast_or_null<CallInst>(LI.I)) { // lock
        Ptr = C->getOperand(0);
    } else {
        return nullptr;
    }
    SmallVector<Value *, 8> sv;
    SmallVector<LLVMInstr *, 8> Is;
    Instruction *P = dyn_cast_or_null<Instruction> (Ptr);

    if (!P) {
        errs () << "UNSUPPORTED DYNAMIC LOAD: "<< *Ptr <<endll;
        return nullptr;
    }
    LLVMThread *T = LI.SCC->T;
    bool staticNM = conflictingNonMovers (sv, &Is, P, T);
    if (staticNM || !sv.empty()) {
        if (opts.verbose) errs () <<"PTR no static ptr:"<< *LI.I  <<endll;
        for (LLVMInstr *LI : Is)
            if (opts.verbose) errs () <<"\t:"<< *LI->I  <<endll;
        return nullptr;
    }
    return Ptr;
}


/**
 * From all conflicting instructions, extract a list of all fixed pointer
 * ops.
 */
bool
LiptonPass::obtainFixedPtrValue (SmallVector<Value *, 8> &cs,
                     SmallVector<LLVMInstr *, 8> &Is,
                     LLVMInstr &LI, bool verbose)
{
    if (!obtainFixedPtr(LI)) return false;

    if (verbose) errs () <<"Check PTR:"<< *LI.I <<endll;
    for (LLVMInstr *LJ : Is) {
        if (LI.I == LJ->I) continue;
        if (verbose) errs () <<"\t"<< *LJ->I <<endll;

        if (Value *Ptr = obtainFixedPtr(*LJ)) {
            Value *G;
            if (LoadInst *L = dyn_cast_or_null<LoadInst>(Ptr)) {
               G = L->getPointerOperand();
            } else if (StoreInst *S = dyn_cast_or_null<StoreInst>(Ptr)) {
                G = S->getPointerOperand();
            } else {
                return false;
            }
            GlobalVariable *V = dyn_cast_or_null<GlobalVariable>(G);
            bool found = false;
            for (Value *GV2 : cs) {
                if (GV2 == V) { found = true; break; }
            }
            if (!found) cs.push_back (V);
        } else {
            if (verbose) errs () <<"\tPTR Type mismatch:"<< *LI.I << "  --  "<< * LJ->I <<endll;
            return false;
        }

    }
    return !cs.empty();
}

LLVMInstr *
LiptonPass::lockPointers (SmallVector<Value *, 8> &pts,
                          SmallVector<LLVMInstr *, 8> &Is, LLVMInstr &LI)
{
    LLVMThread *T = LI.SCC->T;

    PThreadType *PT = new PThreadType (true);
    assert (LI.PT != nullptr);

    if (!LI.PT->locks1()) return nullptr;

    for (LLVMInstr *LJ : Is) {
        if (LI.I == LJ->I) continue;

        LLVMThread *T2 = LJ->SCC->T;

        if (!LJ->PT->locks1()) return nullptr;

        if (PTCallType *CT = PT->merge1 (LJ->PT)) {
            LLVMInstr &Call = T2->getInstruction (CT->second);
            Value *V = obtainFixedPtr(Call);

            Value *G;
            if (LoadInst *L = dyn_cast_or_null<LoadInst>(V)) {
               G = L->getPointerOperand();
            } else if (StoreInst *S = dyn_cast_or_null<StoreInst>(V)) {
                G = S->getPointerOperand();
            } else {
                return nullptr;
            }
            GlobalVariable *GV = dyn_cast_or_null<GlobalVariable>(G);

            if (GV == nullptr) {
                errs () <<"NO LOCK PTR: " << *Call.I << endll;
                return nullptr;
            } else {
                errs () <<"FOUND LOCK PTR: " << *GV << endll;
            }
            bool found = false;
            for (Value *GV2 : pts) {
                if (GV2 == GV) {break; found = true; }
            }
            if (!found) pts.push_back (GV);
        }
    }
    delete PT;

    LLVMInstr &Call = T->getInstruction (LI.PT->get1Lock()->second);
    return &Call;
}



Instruction *
LiptonPass::addStaticPtr (LLVMInstr &LI, block_e type, int block,
                         Instruction *NextTerm, SmallVector<LLVMInstr *, 8> &Is,
                         AllocaInst *Phase)
{
    if (opts.nodyn) return NextTerm;

    // First collect conflicting non-movers from other threads
    SmallVector<Value *, 8> cs;
    bool fixedPTR = obtainFixedPtrValue (cs, Is, LI, opts.verbose);

    if (!fixedPTR) {
        if (opts.nolock) return NextTerm;

        SmallVector<LLVMInstr *, 8> pts;
        LLVMInstr *Ptr = lockPointers (cs, Is, LI);
        if (Ptr == nullptr) return NextTerm;

        Value *Ptr1 = obtainFixedPtr (*Ptr);

        Value       *ValChecks = FALSE;
        Instruction *PtrI1 = dyn_cast_or_null<Instruction>(Ptr1);
        for (Value *Ptr2 : cs) {
            GlobalVariable *V = dyn_cast_or_null<GlobalVariable>(Ptr2);
            assert (V);
            errs () << "LOCK PTR: " << *Ptr1 << " <--> " << *Ptr2 << endll;
            Instruction *Load = new LoadInst(V, "", PtrI1);
            Instruction *New = new ICmpInst (NextTerm, CmpInst::Predicate::ICMP_NE,
                                             Ptr1, Load);

            BinaryOperator *ValChecksB = BinaryOperator::Create (BinaryOperator::BinaryOps::Or,
                                                                 ValChecks, New, "", NextTerm);
            addMetaData (ValChecksB, DYN_YIELD_CONDITION, "");
            ValChecks = ValChecksB;
        }
        NextTerm = insertDynYield (LI, NextTerm, ValChecks, type, block, Phase);

        return NextTerm;
    }

    Instruction *ValChecks = nullptr;
    Value *Ptr1 = obtainFixedPtr (LI);
    Instruction *PtrI1 = dyn_cast_or_null<Instruction>(Ptr1);
    for (Value *Ptr2 : cs) {
        GlobalVariable *V = dyn_cast_or_null<GlobalVariable>(Ptr2);
        errs () << "PTR: " << *Ptr1 << " <--> " << *Ptr2 << endll;
        Instruction *Load = new LoadInst(V, "", PtrI1);
        Instruction *New = new ICmpInst (NextTerm, CmpInst::Predicate::ICMP_EQ,
                                         Ptr1, Load);
        if (ValChecks == nullptr) {
            ValChecks = New;
        } else {
            ValChecks = BinaryOperator::Create (BinaryOperator::BinaryOps::Or,
                                                ValChecks, New, "", NextTerm);
        }
    }
    NextTerm = insertDynYield (LI, NextTerm, ValChecks, type, block, Phase);
    addMetaData (ValChecks, DYN_YIELD_CONDITION, "");

    return NextTerm;
}

void
LiptonPass::dynamicYield (LLVMThread *T, Instruction *I, block_e type, int block)
{
    assert(POSTCOMMIT == TRUE);

    if (opts.verbose) errs () << "Dynamic Yield: "<< *I << endll;
    LLVMInstr &LI = T->getInstruction(I);
    area_e Area = LI.Area;
    mover_e Mover = LI.Mover;
    AllocaInst *Phase = T->PhaseVar;

    if (type == StartBlock) {
        return;
    } else if (type == LoopBlock) {
        insertLoopYields (LI, I, block, Phase);
        return;
    }

    SmallVector<Value *, 8> sv;

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
            bool staticNM = conflictingNonMovers (sv, nullptr, I, T);
            LLASSERT (!sv.empty(), "Unexpected ("<< staticNM <<"), no conflicts found for: "<< *I);

            Instruction *ThenTerm = I;
            if (!staticNM) {
                CallInst *DynConflict = CallInst::Create(Act, sv, "", I);
                ThenTerm = SplitBlockAndInsertIfThen (DynConflict, I, false);
                addMetaData (DynConflict, DYN_YIELD_CONDITION, "");
            }
            new StoreInst(POSTCOMMIT, Phase, ThenTerm);
            break;
        }
        default: { ASSERT (false, "Missing case: "<< Mover); }
        }

        return;
    }

    Instruction *NextTerm = I;
    switch (Mover) {
    case LeftMover:
        if (type & LoopBlock)
            insertLoopYields (LI, I, block, Phase);
        if (Area != Post)
            new StoreInst(POSTCOMMIT, Phase, I);
        checkAssert (opts.debug, NextTerm, Phase, Post);
        break;
    case RightMover:
        if (Area == Top) {
            LoadInst *P = new LoadInst (Phase, "", I);
            NextTerm = insertDynYield (LI, I, P, type, block, Phase);
        }
        if (Area & Post) {
            checkAssert (opts.debug, NextTerm, Phase, Post);
            new StoreInst(PRECOMMIT, Phase, NextTerm);
            insertYield (NextTerm, YieldGlobal, block);
        } else if (type & LoopBlock) {
            checkAssert (opts.debug, I, Phase, Pre);
            insertLoopYields (LI, I, block, Phase);
        }
        break;
    case NoneMover: {
        // First collect conflicting non-movers from other threads
        SmallVector<LLVMInstr *, 8> Is;
        bool staticNM = conflictingNonMovers (sv, &Is, I, T);

        NextTerm = addFixedCAS (LI, type, block, NextTerm, Is, Phase);

        NextTerm = addStaticPtr (LI, type, block, NextTerm, Is, Phase);

        LLASSERT(!sv.empty (),
                 "Unexpected("<< staticNM <<"), no conflicts found for: "<< *I);
        if (!opts.nodyn && !staticNM) { // if in dynamic conflict (non-commutativity)
            CallInst *ActCall = CallInst::Create(Act, sv, "", NextTerm);
            NextTerm = insertDynYield (LI, NextTerm, ActCall, type, block, Phase);
            addMetaData (ActCall, DYN_YIELD_CONDITION, "");
        }
        switch (Area) {
        case Top: {
            LoadInst *P = new LoadInst (Phase, "", NextTerm);
            Instruction *PhaseTerm = insertDynYield (LI, NextTerm, P, type, block, Phase);

            // then branch (post)
            checkAssert (opts.debug, PhaseTerm, Phase, Post);
            new StoreInst (PRECOMMIT, Phase, PhaseTerm); // Temporarily for yield
            insertYield (PhaseTerm, YieldGlobal, block);

            // merge branch (pre, because post was set to pre in then branch)
            checkAssert (opts.debug, NextTerm, Phase, Pre);
            new StoreInst(POSTCOMMIT, Phase, NextTerm);
            break; }
        case Post:
            checkAssert (opts.debug, NextTerm, Phase, Post);

            new StoreInst (PRECOMMIT, Phase, NextTerm); // Temporarily for yield
            insertYield (NextTerm, YieldGlobal, block);
            new StoreInst(POSTCOMMIT, Phase, NextTerm);
            break;
        case Pre:
        case Bottom:
            checkAssert (opts.debug, NextTerm, Phase, Pre);

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
    Type *Bool = Type::getInt1Ty (M.getContext ());
    Type *Void = FunctionType::getVoidTy (M.getContext ());
    Constant *C = M.getOrInsertFunction (__YIELD, Void, Int, (Type*)(0));
    assert (C);
    YieldGlobal = dyn_cast_or_null<Function> (C);
    LLASSERT (YieldGlobal, "Cast failed: "<< *C);

    Constant *C4 = M.getOrInsertFunction (ASSERT, Int, Bool, (Type*)(0));
    assert (C4);
    Assert = dyn_cast_or_null<Function> (C4);
    LLASSERT (Assert, "Cast failed: "<< *C4);

    Constant *C3 = M.getOrInsertFunction (__YIELD_LOCAL, Void, Int, (Type*)(0));
    assert (C3);
    YieldLocal = dyn_cast_or_null<Function> (C3);
    LLASSERT (YieldLocal, "Cast failed: "<< *C3);

    Constant *C2 = M.getOrInsertFunction (__ACT, FunctionType::get (Bool, true));
    assert (C2);
    Act = dyn_cast_or_null<Function> (C2);
    LLASSERT (Act, "Cast failed: "<< *C2);

    Int64 = Type::getInt64Ty(M.getContext());
}

void
LiptonPass::staticYield (LLVMThread *T, Instruction *I, block_e type, int block)
{
    LLVMInstr &LI = T->getInstruction(I);
    if (type == StartBlock) {
        return;
    } else if (type == LoopBlock) {
        if (LI.Area & Post) {
            insertYield (I, YieldGlobal, block);
        } else {
            insertYield (I, YieldLocal, block);
        }
    } else { // YieldBlock or combinations
        if (LI.Atomic) {
            if (type & LoopBlock)
                insertYield (I, YieldLocal, block);
            return;
        }
        if ((LI.Mover == RightMover || LI.Mover == NoneMover) && (LI.Area & Post)) {
            insertYield (I, YieldGlobal, block);
        } else if (type & LoopBlock) {
            if (LI.Area & Post) {
                insertYield (I, YieldGlobal, block);
            } else {
                insertYield (I, YieldLocal, block);
            }
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

    if (opts.staticAll) {
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
LiptonPass::deduceInstances (Module &M)
{
    Function *Main = M.getFunction ("main");
    ASSERT (Main, "No main function in module");
    LLVMThread *TT = new LLVMThread (Main, &Threads);
    Threads[Main] = TT;
    TT->Starts.push_back (nullptr);
    for (Function &F : M) {
        for (BasicBlock &B : F) {
            for (Instruction &I : B) {
                CallInst *Call = dyn_cast_or_null<CallInst>(&I);
                if (!Call) continue;
                Function *Callee = Call->getCalledFunction();
                if (!Callee) {
                    Type *Type = Call->getCalledValue()->getType();
                    FunctionType *FT = cast<FunctionType>(cast<PointerType>(Type)->getElementType());
                    LLASSERT (Callee, "Unexpected call by value! Undefined function? Handle: " << *Call << endll << *FT <<endll);
                    (void) FT;
                }
                if (Callee->getName() == PTHREAD_CREATE) {
                    Function *F = dyn_cast_or_null<Function> (Call->getOperand (PTHREAD_CREATE_F_IDX));
                    ASSERT (F, "Incorrect pthread_create argument?");
                    //Threads (threadF, callInstr); // add to threads (via functor)
                    if (Threads.find(F) == Threads.end()) {
                        Threads[F] = new LLVMThread (F, &Threads);
                        errs () << "ADDED thread: " << F->getName() <<endll;
                    }
                    Threads[F]->Starts.push_back (Call);
                }
            }
        }
    }
}

bool
LiptonPass::runOnModule (Module &M)
{
    if (opts.debug) {
        strncpy (PTHREAD_CREATE, PTHREAD2_CREATE, 100);
        strncpy (PTHREAD_JOIN, PTHREAD2_JOIN, 100);
        strncpy (PTHREAD_KILL, PTHREAD2_KILL, 100);
        PTHREAD_CREATE_F_IDX= PTHREAD2_CREATE_F_IDX;
    } else {
        strncpy (PTHREAD_CREATE, PTHREAD1_CREATE, 100);
        strncpy (PTHREAD_JOIN, PTHREAD1_JOIN, 100);
        strncpy (PTHREAD_KILL, PTHREAD1_KILL, 100);
        PTHREAD_CREATE_F_IDX = PTHREAD1_CREATE_F_IDX;
    }

    AA = &getAnalysis<AliasAnalysis> ();

    deduceInstances (M);

    errs () <<" -------------------- "<< "LockSearching" <<" -------------------- "<< endll;

    // Statically find instructions for which invariantly a lock is held
    walkGraph<LockSearch> (M);

//    int z = 0;
//    for (Function &F : M) {
//        if (Threads.find(&F) == Threads.end()) continue;
//        LLVMThread *T = Threads[&F];
//        for (BasicBlock &B : F) {
//            for (Instruction &I : B) {
//                z += (int) T->Instructions[&I].Area;
//                //errs () << T->Instructions[&I].PT <<"   "<< I << endll;
//            }
//        }
//    }

    errs () <<" -------------------- "<< "Collecting" <<" -------------------- "<< endll;
    // Collect thread reachability info +
    // Collect movability info
    walkGraph<Collect> (M);

    errs () <<" -------------------- "<< "Liptonizing" <<" -------------------- "<< endll;
    // Identify and number blocks statically
    // (assuming all dynamic non-movers are static non-movers)
    walkGraph<Liptonize> (M);

    errs () <<" -------------------- "<< "Instrumentation" <<" -------------------- "<< endll;

    // Add '__act' and '__yield' function definitions
    initialInstrument (M);

    errs () <<" -------------------- "<< "Instrumentation" <<" -------------------- "<< endll;
    // Insert dynamic yields
    finalInstrument (M);

    return true; // modified module by inserting yields
}

} // LiptonPass

