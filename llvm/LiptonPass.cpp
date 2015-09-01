
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
    default: ASSERT (false, "Missing case."); return 0;
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
    default: ASSERT (false, "Missing case."); return 0;
    }
}

static const char *
name ( block_e m )
{
    switch (m) {
    case YieldBlock:        return "Global Yield";
    case LoopBlock:         return "Local Yield";
    case CoincidingBlock:   return "Global+Local Yield";
    default: ASSERT (false, "Missing case."); return 0;
    }
}

LiptonPass::LiptonPass () : ModulePass(ID),
        Name ("out"),
        verbose(true),
        staticAll(false),
        noDyn(false),
        Reach (nullptr)
{ }

LiptonPass::LiptonPass (ReachPass &RP, string name, bool v, bool staticBlocks,
                        bool phase)
                                                            : ModulePass(ID),
        Name (name),
        verbose(v),
        staticAll(staticBlocks),
        noDyn(phase),
        Reach (&RP)
{ }

void
LiptonPass::getAnalysisUsage (AnalysisUsage &AU) const
{
    AU.setPreservesCFG();
    AU.addRequired<AliasAnalysis>();
    AU.addRequired<CallGraphWrapperPass>();
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
checkAlias (list<PTCallType> &List, const AliasAnalysis::Location *Lock)
{
    int matches = 0;
    for (PTCallType &Loc : List) {
        llvm::AliasAnalysis::AliasResult Alias = AA->alias (*Lock, *Loc.first);
        if (Alias != AliasAnalysis::NoAlias) {
            return -1;
        }
        if (Alias == AliasAnalysis::MustAlias) {
            matches++;
        }
    }
    return matches;
}

static void
removeAlias (list<PTCallType> &List, const AliasAnalysis::Location *Lock)
{
    list<PTCallType>::iterator It = List.begin();
    while (It != List.end()) {
        if (AA->alias(*Lock, *It->first) == AliasAnalysis::MustAlias) {
            List.erase(It);
            return;
        }
        It++;
    }
    assert (false);
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
    handleCall (CallInst *call)
    {
        return call;
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
    for (PTCallType &Call : Locks) {
        if (checkAlias(O.Locks, Call.first) != 1) {
            return false;
        }
    }
    if (!O.CorrectThreads) return true;
    if (!CorrectThreads) return false;
    for (PTCallType &Call : Threads) {
        if (checkAlias(O.Threads, Call.first) != 1) {
            return false;
        }
    }
    return true;
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
        PThreadType        *PT;
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
            errs () << "LOCKS: "<< B.getName()<< endll;
            for (PTCallType X : PT->Locks) {
                errs () << *X.second << endll;
            }
        }
        if (Pass->verbose) errs() << B << "\n";

        if (V.State == Stacked) { // rewind stack
            while (true) {
                BasicBlock *Old = Stack.back();
                Seen[Old].State = Visited;
                Stack.pop_back ();
                if (Old == &B) break;
            }
        }
        if (V.State != Unvisited) {
            if (Pass->verbose) errs() << " --(lock revisit)--> "<<  B << "\n";
            if (Pass->verbose) {
                errs () << "REVISITING A MONOTONICALLY DECREASING LOCK SECTION: "<< B << endll;
                errs () << "THREADS seen: " << V.PT->CorrectThreads << endll;
                for (PTCallType X : V.PT->Threads) {
                    errs () << *X.second << endll;
                }
                errs () << "THREADS now: " << PT->CorrectThreads << endll;
                for (PTCallType X : PT->Threads) {
                    errs () << *X.second << endll;
                }
                errs () << "LOCKS seen: "<< endll;
                for (PTCallType X : V.PT->Locks) {
                    errs () << *X.second << endll;
                }
                errs () << "LOCKS now: "<< endll;
                for (PTCallType X : PT->Locks) {
                    errs () << *X.second << endll;
                }
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
        if (Pass->verbose) {
            errs () << "BACK LOCKS: "<< endll;
            for (PTCallType X : PT->Locks) {
                errs () << *X.second << endll;
            }
        }

        LockVisited &V = Seen[&B];
        PT = V.PT;
        Stack.pop_back();
    }

    void
    thread (Function *T)
    {
        assert (Stack.empty());
        ThreadF = Pass->Threads[T];

        Seen.clear();

        PT = new PThreadType(); //TODO: leak?

        if (!T->getName().equals("main")) {
            PT->CorrectThreads = false;
        }

        errs() << "THREAD: "<< T->getName() << endll;
    }

    void
    addPThread (CallInst *Call, const char *str, bool add)
    {
        AliasAnalysis::ModRefResult Mask;
        AliasAnalysis::Location *Lock = new AliasAnalysis::Location(
                                AA->getArgLocation(Call, 0, Mask));

        if (str == PTHREAD_CREATE || str == PTHREAD_JOIN) {

            if (!PT->CorrectThreads) return;

            int matches = checkAlias (PT->Threads, Lock);
            if (add) { // PTHREAD_CREATE
                PT = new PThreadType(PT); // allocate new for search stack

                if (matches == 0) {
                    errs () << "BEGIN: tracking thread: "<< *Call << endll;
                    PT->Threads.push_back (make_pair (Lock, Call));
                } else {
                    PT->CorrectThreads = false;
                    errs () << "WARNING: Giving up on thread tracking: "<<
                            *Lock->Ptr << endll << *Call << endll;
                }
            } else { // PTHREAD_JOIN
                PT = new PThreadType(PT); // allocate new for search stack
                if (matches == 1) {
                    removeAlias (PT->Threads, Lock);
                    errs () << "END: tracking thread: "<< *Call << endll;
                } else {
                    errs () << "WARNING: Giving up on thread tracking: "<<
                            *Lock->Ptr << endll << *Call << endll;
                    PT->CorrectThreads = false;
                }
            }
            return;
        }

        int matches = checkAlias (PT->Locks, Lock);

        if (add) {
            if (matches == 0) {
                PT = new PThreadType(PT); // allocate new for search stack
                PT->Locks.push_back (make_pair (Lock, Call));
                errs () << "BEGIN: tracking lock: "<< *Call << endll;
            } else {
                errs () << "WARNING: "<< str <<" pointer overlaps: "<<
                        *Lock->Ptr << endll << *Call << endll;
                // Do not add (cannot determine region statically)
            }
        } else {
            PT = new PThreadType(PT); // allocate new for search stack
            if (matches == 1) {
                removeAlias (PT->Locks, Lock);
                errs () << "END: tracking lock: "<< *Call << endll;
            } else {
                errs () << "WARNING: "<< str <<" pointer not found: "<<
                        *Lock->Ptr << endll << *Call << endll;
                PT->Locks.resize(0);
                // Empty (Cannot determine end of locked region)
            }
        }
    }

    Instruction *
    handleCall (CallInst *Call)
    {
        doHandle (Call);

        if (Call->getCalledFunction ()->getName ().endswith(PTHREAD_YIELD)) {
        } else if (Call->getCalledFunction ()->getName ().endswith("__assert_rtn")) {
        } else if (Call->getCalledFunction ()->getName ().endswith("__assert")) {
        } else if (Call->getCalledFunction ()->getName ().endswith(PTHREAD_LOCK)) {
            addPThread (Call, PTHREAD_LOCK, true);
        } else if (Call->getCalledFunction ()->getName ().endswith(PTHREAD_RLOCK)) {
            addPThread (Call, PTHREAD_RLOCK, true);
        } else if (Call->getCalledFunction ()->getName ().endswith(PTHREAD_WLOCK)) {
            addPThread (Call, PTHREAD_WLOCK, true);
        } else if (Call->getCalledFunction ()->getName ().endswith(PTHREAD_RW_UNLOCK)) {
            addPThread (Call, PTHREAD_RW_UNLOCK, false);
        } else if (Call->getCalledFunction ()->getName ().endswith(PTHREAD_UNLOCK)) {
            addPThread (Call, PTHREAD_UNLOCK, false);
        } else if (Call->getCalledFunction ()->getName ().endswith(PTHREAD_CREATE)) {
            addPThread (Call, PTHREAD_CREATE, true);
        } else if (Call->getCalledFunction ()->getName ().endswith(PTHREAD_JOIN)) {
            addPThread (Call, PTHREAD_JOIN, false);
        } else if (Call->getCalledFunction ()->getName ().endswith(PTHREAD_MUTEX_INIT)) {
        } else if (Call->getCalledFunction ()->getName ().endswith(ATOMIC_BEGIN)) {
            LLASSERT (PT->Atomic == false, "Already "<< ATOMIC_BEGIN <<"encountered before: "<< Call << endll);
            PT = new PThreadType(PT); // optimize
            PT->Atomic = true;
        } else if (Call->getCalledFunction ()->getName ().endswith(ATOMIC_END)) {
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
    void doHandle (Instruction *I)
    {
        LLVMInstr &LI = ThreadF->Instructions[I];
        LI.Atomic = PT->Atomic;
        LI.PT = PT;
    }
};

// TODO: Left == Left | Bottom
//inline area_e
//operator< (area_e a, area_e b)
//{
//
//}

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

    mover_e
    movable (Instruction *I)
    {
        if (ThreadF->Instructions[I].singleThreaded()) {
            return BothMover;
        }

        LLVMThread *T = ThreadF;

        for (pair<Function *, LLVMThread *> &X : Pass->Threads) {
            LLVMThread *T2 = X.second;
            if (T == T2 && T->isSingleton())
                continue;

            AliasSet *AS = FindAliasSetForUnknownInst (T2->Aliases, I);
            if (AS != nullptr) {
                return NoneMover;
            }
        }
        return BothMover;
    }

    struct StackElem {
        StackElem (area_e a, BasicBlock *B)
        :
            Area(a),
            Seen(a),
            Block(B)
        {  }
        area_e                  Area;
        area_e                  Seen;
        int                     Last = -1;
        BasicBlock             *Block;
    };

    struct SeenType {
        int first;
    };

    DenseMap<BasicBlock *, SeenType>        Seen;
    vector<StackElem>                       Stack;
    area_e                                  Area = Bottom;

    // block and deblock implement revisiting
    bool
    block ( BasicBlock &B )
    {
        SeenType &seen = Seen[&B];

        if (seen.first == 0) {
            if (Pass->verbose) errs() << name(Area)  <<": "<< B << "\n";
            Stack.push_back ( StackElem(Area, &B) );
            seen.first = -Stack.size();
            return true;
        }

        if (seen.first < 0) { // stack

            Instruction *firstNonPhi = B.getFirstNonPHI ();
            LLASSERT (firstNonPhi, "No Instruction in " << B);
            insertBlock (firstNonPhi, LoopBlock);

            int Index = -seen.first - 1;
            StackElem Previous = Stack[Index];
            if (Previous.Seen < Area) {
                if (Pass->verbose) errs() << name(Area)  <<" --(revisit)--> "<<  name(Previous.Seen) <<": "<< B << "\n";

                // re-explore: make stack overlap:
                Previous.Seen = Area;
                StackElem Next = StackElem (Area, &B);
                Next.Last = Index;
                Stack.push_back (Next);
                seen.first = -Stack.size(); // update to highest on stack (Next)
                return true;
            }
        } else {
            if (seen.first < Area) {
                if (Pass->verbose) errs() << name(Area)  <<" --(revisit)--> "<<  name((area_e)seen.first) <<": "<< B << "\n";

                // re-explore visited blocks:
                Stack.push_back ( StackElem(Area, &B) );
                seen.first = -Stack.size();
                return true;
            }
        }

        return false;
    }

    // TODO: backtrack Bottom up
    void
    deblock ( BasicBlock &B )
    {
        SeenType &seen = Seen[&B];
        StackElem &Pop = Stack.back();

        if (Pop.Last != -1) { // overlapping stacks: revert Seen to underlying
            seen.first = Pop.Last;
            Stack[Pop.Last].Seen = Pop.Seen;
        } else {
            seen.first = Pop.Seen;
        }

        Area = Pop.Area;
        Stack.pop_back();
    }

    void
    thread (Function *T)
    {
        assert (Stack.empty());
        ThreadF = Pass->Threads[T];
        Area = Bottom; // We always start from a static yield

        Instruction *Start = T->getEntryBlock ().getFirstNonPHI ();
        // Skip empty blocks, as we do not want terminators in BlockStarts
        while (TerminatorInst *T = dyn_cast<TerminatorInst> (Start)) {
            assert (T->getNumSuccessors() == 1);
            Start = T->getSuccessor(0)->getFirstNonPHI();
        }
        int b = insertBlock (Start, LoopBlock);
        assert (b == 0); // start block

        Seen.clear();

        errs() << "THREAD: "<< T->getName() << endll;
    }

    Instruction *
    handleCall (CallInst *Call)
    {
        if (Call->getCalledFunction ()->getName ().endswith(PTHREAD_YIELD)) {
            errs () << "WARNING: pre-existing Yield call: "<< *Call <<"\n";
            Area = Bottom;
        } else if (Call->getCalledFunction ()->getName ().endswith(PTHREAD_LOCK)) {
            doHandle (Call, RightMover);
        } else if (Call->getCalledFunction ()->getName ().endswith(PTHREAD_RLOCK)) {
            doHandle (Call, RightMover);
        } else if (Call->getCalledFunction ()->getName ().endswith(PTHREAD_WLOCK)) {
            doHandle (Call, RightMover);
        } else if (Call->getCalledFunction ()->getName ().endswith(PTHREAD_RW_UNLOCK)) {
            doHandle (Call, LeftMover);
        } else if (Call->getCalledFunction ()->getName ().endswith(PTHREAD_UNLOCK)) {
            doHandle (Call, LeftMover);
        } else if (Call->getCalledFunction ()->getName ().endswith(PTHREAD_CREATE)) {
            doHandle (Call, LeftMover);
        } else if (Call->getCalledFunction ()->getName ().endswith(PTHREAD_JOIN)) {
            doHandle (Call, RightMover);
        } else if (Call->getCalledFunction ()->getName ().endswith(PTHREAD_MUTEX_INIT)) {
        } else if (Call->getCalledFunction ()->getName ().endswith(ATOMIC_BEGIN)) {
            assert (!ThreadF->Instructions[Call].Atomic);
            doHandle (Call, RightMover); // force (dynamic) yield (for Post/Top)
        } else if (Call->getCalledFunction ()->getName ().endswith(ATOMIC_END)) {
        } else if (Call->getCalledFunction ()->getName ().endswith("__assert_rtn")) {
        } else if (Call->getCalledFunction ()->getName ().endswith("__assert")) {

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

        if (I->isTerminator()) {
            return I;
        }

        mover_e Mover = LI.Mover;
        if (Mover == 0) {
            Mover = movable (I);
        }

        return doHandle (I, Mover);
    }

private:
    Instruction *
    doHandle (Instruction *I, mover_e Mover) // may overwrite less dynamic blocks
    {
        if (Pass->verbose) errs () << name(Area) << *I << " -> \t"<< name(Mover) << "\n";

        LLVMInstr &LI = ThreadF->Instructions[I];
        LI.Area = Area;
        LI.Mover = Mover;

        addMetaData (I, AREA, name(Area));
        if (Mover != BothMover) {
            addMetaData (I, MOVER, name(Mover));
        }
        if (ThreadF->Instructions[I].singleThreaded()) {
            addMetaData (I, SINGLE_THREADED, "");
        }

        bool atomic = LI.PT->Atomic;
        switch (Mover) {
        case RightMover:
            if (Area & Post) { // Post, Top
                insertBlock (I, YieldBlock);
            }
            if (atomic) {
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

    bool
    isBlockStart (Instruction *I)
    {
        return ThreadF->BlockStarts.find(I) != ThreadF->BlockStarts.end();
    }

    /**
     * Creates a block for this instruction (yield / commit before instruction).
     */
    int
    insertBlock (Instruction *I, block_e yieldType)
    {
        assert (!I->isTerminator());

        if (yieldType != LoopBlock && ThreadF->Instructions[I].singleThreaded()) {
            return -1; // TODO: precise pthread_create / join count
        }

        unsigned int blockID = ThreadF->BlockStarts.size ();

        if (isBlockStart(I)) {
            block_e ExistingType = ThreadF->BlockStarts[I].first;
            yieldType = (block_e) ((int)yieldType | (int)ExistingType);

            errs () << "WARNING: Overwriting dynamic block "<< name(ExistingType) <<" --> "<< name(yieldType) <<": " << *I << endll;
            blockID = ThreadF->BlockStarts[I].second; // reuse block ID
        }

        if (Pass->verbose) errs () << "New " << name(yieldType) << " block: " << *I << "\n";

        //assert (blockID < (1ULL << 16));
        //int globalBlockID = blockID + (1ULL << 16) * ThreadF->index;
        ThreadF->BlockStarts[I] = make_pair (yieldType, blockID);
        return blockID;
    }
};

StringRef Collect::Action = "Collecting";
StringRef  Liptonize::Action = "Liptonizing";

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
        } else {
           Instruction *Next = handle->handleCall (call);
           if (Next == nullptr) {
               errs() << "Handle library call: "<< call->getCalledFunction()->getName() <<"\n";
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
    if (verbose) errs() << F.getName() << "\n";
    walkGraph (F.getEntryBlock());
}


template <typename ProcessorT>
void
LiptonPass::walkGraph (Module &M)
{
    ProcessorT processor(this);
    handle = &processor;

    for (pair<Function *, vector<Instruction *>> &X : Reach->Threads) {
        Function *T = X.first;

        // Create new LLVM thread if it doesn't exist
        if (Threads.find(T) == Threads.end()) {

            int Runs = Reach->Threads[T].size();
            for (Instruction *I : Reach->Threads[T]) {
                if (Reach->stCon(I, I)) {
                    Runs = -1; // potentially infinite
                    break;
                }
            }

            Threads[T] = new LLVMThread(T, Threads.size(), Runs);
        }
        processor.thread (T);
        walkGraph (*T);
    }
}


static bool
isAtomicIncDec (Instruction *I)
{
    if (/*AtomicRMWInst *A = */dyn_cast_or_null<AtomicRMWInst>(I)) {
//        switch (A->getOperation()) {
//        case AtomicRMWInst::BinOp::Add;
//        case AtomicRMWInst::BinOp::Sub;
//        case AtomicRMWInst::BinOp::And;
//        case AtomicRMWInst::BinOp::Nand;
//        case AtomicRMWInst::BinOp::Or;
//        case AtomicRMWInst::BinOp::Xor;
//            return true;
//        default:
//            return false;
//        }
        return true;
    }
    return false;
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
        for (Instruction *I2 : AS2I[AS]) {
            if (isAtomicIncDec(I) && isAtomicIncDec(I2)) continue;

            // for all Block starting points TODO: refine to exit points
            for (pair<Instruction *, pair<block_e, int> > X : T2->BlockStarts) {
                Instruction *R = X.first;
                int         blockID = X.second.second;

                // if Block is in same process as J, and block can reach J
                if (Reach->stCon (R, I2)) {

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
        }
        if (Blocks.size() == T2->BlockStarts.size()) {
            return true; // static yield
        }
    }

    return false;
}

static void
insertYield (LLVMThread *T, Instruction* I, Function *YieldF, int block, bool HidePost)
{
    AllocaInst *Phase = T->PhaseVar;
    Value *blockId = ConstantInt::get (YieldF->getFunctionType ()->getParamType (0), block);

    if (HidePost) {
        new StoreInst(PRECOMMIT, Phase, I); // Post --> Pre (temporarily)
    }
    CallInst::Create (YieldF, blockId, "", I);
    if (HidePost) {
        new StoreInst(POSTCOMMIT, Phase, I); // Pre --> Post (for after I)
    }
}

static TerminatorInst *
insertDynYield (LLVMThread* T, Instruction* I, block_e type,
                int block)
{
    AllocaInst *Phase = T->PhaseVar;

    LoadInst* P = new LoadInst (Phase, "", I);
    assert(POSTCOMMIT == TRUE);
    TerminatorInst* ThenTerm;
    TerminatorInst* ElseTerm;
    if (type & LoopBlock) {
        SplitBlockAndInsertIfThenElse (P, I, &ThenTerm, &ElseTerm);
        insertYield (T, ElseTerm, YieldLocal, block, false);
    } else {
        ThenTerm = SplitBlockAndInsertIfThen (P, I, false);
    }
    insertYield (T, ThenTerm, YieldGlobal, block, true);
    return ThenTerm;
}

void
LiptonPass::dynamicYield (LLVMThread *T, Instruction *I, block_e type,
                          int block)
{
    AllocaInst *Phase = T->PhaseVar;

    if (block == 0) {
        return;
    }

    if (type == LoopBlock) {
        insertYield (T, I, YieldLocal, block, false);
        return;
    }

    SmallVector<Value*, 8> sv;

    LLVMInstr &LI = T->Instructions[I];
    area_e Area = LI.Area;
    mover_e Mover = LI.Mover;

    if (LI.Atomic) { // no yields, just bookkeep phase

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
            assert (!sv.empty());

            Instruction *ThenTerm = I;
            if (!staticNM) {
                Value *DynConflict = CallInst::Create(Act, sv, "", I);
                ThenTerm = SplitBlockAndInsertIfThen (DynConflict, I, false);
            }
            new StoreInst(POSTCOMMIT, Phase, ThenTerm);
            break;
        }
        default: { ASSERT (false, "Missing case: "<< type); }
        }

        if (type & LoopBlock) {
            insertYield (T, I, YieldLocal, block, false);
        }
        return;
    }

    switch (Mover) {
    case LeftMover:
        if (Area != Post) {
            new StoreInst(POSTCOMMIT, Phase, I);
        }
        if (type & LoopBlock) {
            insertYield (T, I, YieldLocal, block, false);
        }
        break;
    case RightMover:
        if (Area == Post) {
            new StoreInst(PRECOMMIT, Phase, I);
            insertYield (T, I, YieldGlobal, block, false);
        } else if (Area == Top) {
            Instruction *ThenTerm = insertDynYield (T, I, type, block);
            new StoreInst(PRECOMMIT, Phase, ThenTerm);
        }
        break;
    case NoneMover: {
        // First collect conflicting non-movers from other threads
        bool staticNM = conflictingNonMovers (sv, I, T);
        assert (!sv.empty());

        // if in dynamic conflict (non-commutativity)
        Instruction *ConflictTerm = I;

        if (!noDyn && !staticNM) {
            Value *DynConflict = CallInst::Create(Act, sv, "", I);
            TerminatorInst* ThenTerm;
            TerminatorInst* ElseTerm;
            if (type & LoopBlock) {
                SplitBlockAndInsertIfThenElse (DynConflict, I, &ThenTerm, &ElseTerm);
                insertYield (T, ElseTerm, YieldLocal, block, false);
            } else {
                ThenTerm = SplitBlockAndInsertIfThen (DynConflict, I, false);
            }
            ConflictTerm = ThenTerm;
        }

        if (Area & Post) {

            if (Area == Top) {
                insertDynYield (T, ConflictTerm, type, block);
            }

            insertYield (T, ConflictTerm, YieldGlobal, block, true);
        } else {

            new StoreInst(POSTCOMMIT, Phase, ConflictTerm);
        }

        break;
    }
    default: { ASSERT (false, "Missing case: "<< type); }
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
    AllocaInst *Phase = T->PhaseVar;

    if (block == 0) {
        return;
    }

    LLVMInstr &BlockType = T->Instructions[I];
    area_e Area = BlockType.Area;
    mover_e Mover = BlockType.Mover;

    if (type == LoopBlock) {
        insertYield (T, I, YieldLocal, block, false);
        return;
    } else {
        if (Mover == RightMover || Mover == NoneMover) {
            if (Area & Post) {
                insertYield (T, I, YieldGlobal, block, false);
                new StoreInst(PRECOMMIT, Phase, I);
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

bool
LiptonPass::runOnModule (Module &M)
{
    AA = &getAnalysis<AliasAnalysis> ();

    // Add '__act' and '__yield' function definitions
    initialInstrument (M);

    // Statically find instructions for which invariantly a lock is held
    walkGraph<LockSearch> (M);

    // Collect thread reachability info +
    // Collect movability info
    walkGraph<Collect> (M);

    // Identify and number blocks statically
    // (assuming all dynamic non-movers are static non-movers)
    walkGraph<Liptonize> (M);

    // Insert dynamic yields
    finalInstrument (M);

    return true; // modified module by inserting yields
}

} // LiptonPass

