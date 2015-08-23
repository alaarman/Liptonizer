
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
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
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

//TODO: locks are left movers!

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

Function                       *Yield = nullptr;
Function                       *YieldLocal = nullptr;
Function                       *Act = nullptr;
Type                           *Int64 = nullptr;

int                             nextBlock = 0;

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

bool
LiptonPass::Processor::isBlockStart (Instruction *I)
{
    return ThreadF->BlockStarts.find(I) != ThreadF->BlockStarts.end();
}

int
LiptonPass::Processor::insertBlock (Instruction *I,
                         yield_loc_e loc,
                         block_e yieldType)
{
    if (loc == YIELD_AFTER) {
        I = I->getNextNode();
    }
    if (isBlockStart(I)) {
        if (ThreadF->BlockStarts[I].first >= yieldType) {
            // a >= b = a is more dynamic than b
            return -1;
        } else { // we replace the dynamic bloch with a new static one!
            errs () << "WARNING: Overwriting dynamic block: " << *I;
        }
    }

    if (Pass->verbose) errs () << "New " <<
            (yieldType == Static ? "static" : "dynamic") << " block: " << *I << "\n";

    unsigned int blockID = ThreadF->BlockStarts.size ();
    //assert (blockID < (1ULL << 16));
    //int globalBlockID = blockID + (1ULL << 16) * ThreadF->index;
    ThreadF->BlockStarts[I] = make_pair (yieldType, blockID);
    return blockID;
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

/**
 * Thread / instruction reachability processor
 * Insert yields in loops.
 *
 * Complexity: P X N
 */
struct Collect : public LiptonPass::Processor {

    enum state_e {
        Unvisited = 0,
        Stacked,
        Visited,
    };

    static StringRef                Action;
    DenseMap<BasicBlock *, state_e> Seen;
    vector<BasicBlock *>            Stack;

    using Processor::Processor;
    ~Collect() { }

    Instruction *
    handleCall (CallInst *call)
    {
        Pass->I2T[call] = ThreadF;
        if (call->getCalledFunction ()->getName ().endswith(PTHREAD_YIELD)) {
        } else if (call->getCalledFunction ()->getName ().endswith(PTHREAD_LOCK)) {
        } else if (call->getCalledFunction ()->getName ().endswith(PTHREAD_RLOCK)) {
        } else if (call->getCalledFunction ()->getName ().endswith(PTHREAD_WLOCK)) {
        } else if (call->getCalledFunction ()->getName ().endswith(PTHREAD_RW_UNLOCK)) {
        } else if (call->getCalledFunction ()->getName ().endswith(PTHREAD_UNLOCK)) {
        } else if (call->getCalledFunction ()->getName ().endswith(PTHREAD_CREATE)) {
        } else if (call->getCalledFunction ()->getName ().endswith(PTHREAD_JOIN)) {
        } else if (call->getCalledFunction ()->getName ().endswith(PTHREAD_MUTEX_INIT)) {
        } else if (call->getCalledFunction ()->getName ().endswith(ATOMIC_BEGIN)) {
        } else if (call->getCalledFunction ()->getName ().endswith(ATOMIC_END)) {
        } else {
            return nullptr;
        }
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
        } else if (seen == Stacked) {
            Instruction *firstNonPhi = B.getFirstNonPHI ();
            LLASSERT (firstNonPhi, "No Instruction in " << B);
            insertBlock (firstNonPhi, YIELD_BEFORE, Static);
        }
        return false;
    }

    void
    deblock ( BasicBlock &B )
    {
        Seen[&B] = Visited;
    }

    void
    thread (Function *F)
    {
        ThreadF = Pass->Threads[F];
        Seen.clear(); // restart with exploration
        Instruction *Start = F->getEntryBlock ().getFirstNonPHI ();

        // Skip empty blocks, as we do not want terminators in BlockStarts
        while (TerminatorInst *T = dyn_cast<TerminatorInst> (Start)) {
            assert (T->getNumSuccessors() == 1);
            Start = T->getSuccessor(0)->getFirstNonPHI();
        }

        int b = insertBlock (Start, YIELD_BEFORE, Static);
        assert (b == 0); // start block
    }

    Instruction *
    process (Instruction *I)
    {
        LLASSERT (Pass->I2T.find(I) == Pass->I2T.end(),
                  "Instuction not allow twice in different threads: " << *I);

        Pass->I2T[I] = ThreadF;

        ThreadF->Aliases->add (I);

        AliasSet *AS = FindAliasSetForUnknownInst (ThreadF->Aliases, I);
        Pass->AS2I[AS].push_back(I);
        return I;
    }
};

/**
 *
 */
struct Liptonize : public LiptonPass::Processor {

    const char *
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

    enum area_e {
        Pre = 1,
        Post        // !staticAll => (Post => Pre)
    };

    mover_e
    movable(Instruction *I)
    {
        LiptonPass::LLVMThread *T = Pass->I2T[I];

        for (pair<Function *, LiptonPass::LLVMThread *> &X : Pass->Threads) {
            LiptonPass::LLVMThread *T2 = X.second;
            if (T == T2 && T->runs->size() == 1)
                continue;

            AliasSet *AS = FindAliasSetForUnknownInst (T2->Aliases, I);
            if (AS != nullptr) {
                return NoneMover;
            }
        }
        return BothMover;
    }


    struct StackElem {
        StackElem (area_e a, BasicBlock *B) : Area(a), Block(B) {  }
        area_e                  Area;
        BasicBlock             *Block;
    };

    static StringRef                Action;
    DenseMap<BasicBlock *, int>     Seen;
    area_e                          Area = Pre;
    int                             StackDepth = 0;
    vector<StackElem>               Stack;

    using Processor::Processor;
    ~Liptonize() { }

    bool
    block ( BasicBlock &B )
    {
        int &seen = Seen[&B];
        if (seen == 0) {
            if (Pass->verbose) errs() << (Area==Pre?"R ":"L ")<< B << "\n";
            Stack.push_back ( StackElem(Area, &B) );
            seen = --StackDepth;
            return true;
        }
        return false;
    }

    void
    deblock ( BasicBlock &B )
    {
        Seen[&B] = Area;
        Area = Stack.back().Area;
        Stack.pop_back();
        StackDepth++;
    }

    void
    thread (Function *T)
    {
        ThreadF = Pass->Threads[T];
        Area = Pre;
        //Seen.clear();  // TODO: overlapping threads!
    }

    Instruction *
    handleCall (CallInst *call)
    {
        if (call->getCalledFunction ()->getName ().endswith(PTHREAD_YIELD)) {
            errs () << "WARNING: pre-existing Yield call: "<< *call <<"\n";
            Area = Pre;
        } else if (call->getCalledFunction ()->getName ().endswith(PTHREAD_LOCK)) {
            doHandle (call, RightMover);
        } else if (call->getCalledFunction ()->getName ().endswith(PTHREAD_RLOCK)) {
            doHandle (call, RightMover);
        } else if (call->getCalledFunction ()->getName ().endswith(PTHREAD_WLOCK)) {
            doHandle (call, RightMover);
        } else if (call->getCalledFunction ()->getName ().endswith(PTHREAD_RW_UNLOCK)) {
            doHandle (call, LeftMover);
        } else if (call->getCalledFunction ()->getName ().endswith(PTHREAD_UNLOCK)) {
            doHandle (call, LeftMover);
        } else if (call->getCalledFunction ()->getName ().endswith(PTHREAD_CREATE)) {
            Pass->PTCreate.insert (call);
            doHandle (call, LeftMover);
        } else if (call->getCalledFunction ()->getName ().endswith(PTHREAD_JOIN)) {
            doHandle (call, RightMover);
        } else if (call->getCalledFunction ()->getName ().endswith(PTHREAD_MUTEX_INIT)) {

        } else if (call->getCalledFunction ()->getName ().endswith(ATOMIC_BEGIN)) {
            // merge statements in atomic block and only yield afterwards
            Instruction *Next = call;
            mover_e m = followBlock (&Next);
            doHandle (Next, m);
            return Next;
        } else if (call->getCalledFunction ()->getName ().endswith(ATOMIC_END)) {

        } else {
            return nullptr;
        }
        return call;
    }

    Instruction *
    process (Instruction *I)
    {
        mover_e m = movable (I);
        return doHandle (I, m);
    }

private:
    Instruction *
    doHandle (Instruction *I, mover_e m)
    {
        if (Pass->verbose)
        errs () << (Area == Pre ? "R " : "L ") << *I << " -> \t"<< name (m) << "\n";

        if (isBlockStart(I)) {
            if (Pass->staticAll) {
                Area = Pre;
                return I;
            }
        }

        if (singleThreaded(I)) {
            return I;
        }

        switch (m) {
        case RightMover:
            if (Area == Post) {
                insertBlock (I, YIELD_BEFORE, PhaseDynamic);
                if (Pass->staticAll) {
                    Area = Pre;
                }
            }
            break;
        case LeftMover:
            Area = Post;
            break;
        case NoneMover:
            if (Area == Post) {
                insertBlock (I, YIELD_BEFORE, CommDynamic);
            }
            Area = Post; // in both cases, after I is in post-commit

            // since Pre has the same meaning in all configurations
            // (staticAll or not), we do notneed separate cases here
            break;
        case BothMover:
            break;
        default:
            ASSERT(false, "Missing case.");
        }
        return I;
    }

    mover_e
    followBlock (Instruction **Next)
    {
        int m = NoneMover;
        Instruction *N = *Next;
        while (( N = N->getNextNode () )) {
            if (TerminatorInst *term = dyn_cast_or_null<TerminatorInst> (N)) {
                int num = term->getNumSuccessors();
                if (num == 0) break;

                for (int i = 1; i < num; i++) {
                    N = term->getSuccessor(i)->getFirstNonPHI();
                    m |= followBlock (&N);
                }
                N = term->getSuccessor(0)->getFirstNonPHI();
            }
            if (CallInst *c2 = dyn_cast_or_null<CallInst> (N)) {
                if (c2->getCalledFunction ()->getName ().endswith (ATOMIC_END)) {
                    Next = &N;
                    return mover_e(m);
                }
            }
            // movers are implicitly treated as lattice:
            m |= (int)movable(N);
        }
        ASSERT (false, "No matching atomic_end found!");
        return NoneMover;
    }

    bool
    singleThreaded (Instruction *I)
    {
        // avoid yield where there is no parallelism TODO: overestimation
        return ThreadF->Function.getName().equals("main") &&
               Pass->PTCreate.empty ();
        // TODO: remove limitation of necessary function inlining
    }
};

StringRef Collect::Action = "Collecting";
StringRef  Liptonize::Action = "Liptonizing";

void
LiptonPass::walkGraph ( Instruction *I )
{
    if (TerminatorInst *T = dyn_cast<TerminatorInst> (I)) {
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
LiptonPass::walkGraph ()
{
    ProcessorT processor(this, ProcessorT::Action);
    handle = &processor;

    for (pair<Function *, vector<Instruction *>> &X : Reach->Threads) {
        Function *T = X.first;

        // Create new LLVM thread if it doesn't exist
        if (Threads.find(T) == Threads.end()) {
            Threads[T] = new LLVMThread(T, Threads.size(), this);
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
void
LiptonPass::conflictingNonMovers (SmallVector<Value *, 8> &sv,
                                  Instruction *I)
{
    // First collect conflicting non-movers from other threads
    LLVMThread *T = I2T[I];
    unsigned TCount = T->runs->size();

    // for all other threads
    for (pair<Function *, LLVMThread *> &Thread : Threads) {
        LLVMThread *T2 = Thread.second;
        if (T2 == T && TCount == 1) // skip own thread function iff singleton
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
                            sv.push_back(&T2->Function);
                        }

                        sv.push_back (num);
                    }
                }
            }
        }
    }
}

void
LiptonPass::dynamicYield (Instruction *I, block_e type, int block)
{

    if (staticAll) {
        if (block != 0 /* type == Dynamic */) {
            Value *blockId = ConstantInt::get(Yield->getFunctionType()->getParamType(0), block);
            CallInst::Create(Yield, blockId, "", I);
        }
        return;
    }

    LLVMThread *T = I2T[I];
    if (!T) errs() << *I << "\n" << *I->getParent() << endll;
    AllocaInst *Phase = T->PhaseVar;

    if (type == Static) {
        if (block == 0) return;

        // Local:
        Value *blockId = ConstantInt::get(Yield->getFunctionType()->getParamType(0), block);
        CallInst::Create(YieldLocal, blockId, "", I);

        return; // that's all
    }

    Instruction *PhaseCheck = I;

    if (!noDyn && type == CommDynamic) {
        // First collect conflicting non-movers from other threads
        SmallVector<Value*, 8> sv;
        conflictingNonMovers (sv, I);

        if (!sv.empty()) {
            // if in dynamic conflict
            Value *DynConflict = CallInst::Create(Act, sv, "", I);
            PhaseCheck = SplitBlockAndInsertIfThen (DynConflict, I, false);
        }
    }

    LoadInst *P = new LoadInst(Phase, "", PhaseCheck);
    TerminatorInst *PostBranch;
    TerminatorInst *PreBranch;
    SplitBlockAndInsertIfThenElse (P, PhaseCheck, &PostBranch, &PreBranch);
    new StoreInst(POSTCOMMIT, Phase, PreBranch); // Pre --> Post (for after I)

    new StoreInst(PRECOMMIT, Phase, PostBranch); // Post --> Pre (temporarily)
    Value *blockId = ConstantInt::get(Yield->getFunctionType()->getParamType(0), block);
    CallInst::Create(Yield, blockId, "", PostBranch);
    new StoreInst(POSTCOMMIT, Phase, PostBranch); // Pre --> Post (for after I)
}

void
LiptonPass::initialInstrument (Module &M)
{
    // Add '__act' and '__yield' functions
    Type *Int = Type::getInt32Ty (M.getContext ());
    Type *Void = FunctionType::getVoidTy (M.getContext ());
    Constant *C = M.getOrInsertFunction (__YIELD, Void, Int, (Type*)(0));
    Yield = cast<Function> (C);


    Constant *C3 = M.getOrInsertFunction (__YIELD_LOCAL, Void, Int, (Type*)(0));
    YieldLocal = cast<Function> (C3);

    Type *Bool = Type::getInt1Ty (M.getContext ());
    Constant *C2 = M.getOrInsertFunction (__ACT, FunctionType::get (Bool, true));
    Act = cast<Function> (C2);
    Int64 = Type::getInt64Ty(M.getContext());
}

void
LiptonPass::finalInstrument (Module &M)
{
    Type *Bool = Type::getInt1Ty (M.getContext());
    TRUE = ConstantInt::get (Bool, 0);
    FALSE = ConstantInt::get (Bool, 1);
    PRECOMMIT = FALSE;
    POSTCOMMIT = TRUE;

    if (!staticAll) {
        // collect thread initial instructions (before instrumenting threads)
        DenseMap<Function *, Instruction *> Starts;
        for (pair<Function *, LLVMThread *> X : Threads) {
            Function *T = X.first;
            Instruction *Start = T->getEntryBlock().getFirstNonPHI();
            AllocaInst *Phase = new AllocaInst (Bool, "__phase", Start);
            new StoreInst (PRECOMMIT, Phase, Start);
            X.second->PhaseVar = Phase;
        }
    }

    // instrument code with dynamic yields
    for (pair<Function *, LLVMThread *> T : Threads) {
        for (pair<Instruction *, pair<block_e, int>> X : T.second->BlockStarts) {
            dynamicYield (X.first, X.second.first, X.second.second);
        }
    }
}

bool
LiptonPass::runOnModule (Module &M)
{
    AA = &getAnalysis<AliasAnalysis> ();

    // Add '__act' and '__yield' function definitions
    initialInstrument (M);

    // Collect thread reachability info +
    // Collect movability info          +
    // Break loops with static yields
    walkGraph<Collect> ();

    // Identify and number blocks statically
    // (assuming all dynamic non-movers are static non-movers)
    walkGraph<Liptonize> ();

    // Insert dynamic yields
    finalInstrument (M);

    return true; // modified module by inserting yields
}

} // LiptonPass

