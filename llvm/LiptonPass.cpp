
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

static StringRef
getMetaData (Instruction *I, const char *type)
{
    MDString *S = cast<MDString>(I->getMetadata(type)->getOperand(0));
    return S->getString();
}

enum area_e {
    Pre = 1<<0,    // > 0 for Seen map
    Post= 1<<1,    //
    Top = Pre | Post
};

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
    case NoBlock:       return "PhaseShift";
    case StaticLocal:   return "StaticLocal";
    case PhaseDynamic:  return "DynamicPhase";
    case CommDynamic:   return "DynamicComm";
    case Static:        return "Static";
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

bool
LiptonPass::Processor::isBlockStart (Instruction *I)
{
    return ThreadF->BlockStarts.find(I) != ThreadF->BlockStarts.end();
}

/**
 * Creates a block for this instruction.
 *
 * Block types come in four types:
 *
 * o NoBlock, indicates only that the instruction shifts phase form pre to post commit,
 * o Static, indicates that a loop has to be broken (yield_local suffices)
 * o PhaseDynamic, indicates that based on the phase variable a global yield may be necessary
 * o CommDynamic, indicates that the instruction might dynamically commute (check __act)
 *
 * In this order, one block start implies the other, meaning that we can always
 * safely replace more static blocks with more dynamic blocks (at the cost of
 * complicating the verification task).
 */
int
LiptonPass::Processor::insertBlock (Instruction *I,
                                    block_e yieldType)
{

    if (yieldType != StaticLocal && ThreadF->Function.getName().equals("main") &&
                               Pass->PTCreate.size() == 0) {
        return -1;
    }

    unsigned int blockID = ThreadF->BlockStarts.size ();

    if (isBlockStart(I)) {
        block_e ExistingType = ThreadF->BlockStarts[I].first;
        if (ExistingType >= yieldType) {
            // a >= b = a is more dynamic than b
            return -1;
        } else { // we replace the dynamic block with a new static one!

            if (ExistingType == StaticLocal) {
                yieldType = Static; // reuse block ID
                // TODO: could be dynamic if the loop already contains a static yield
            }

            errs () << "WARNING: Overwriting dynamic block "<< name(ExistingType) <<" --> "<< name(yieldType) <<": " << *I << endll;
            // TODO: in case paths up to yields are only non-movers (use Bottom == {})
            blockID = ThreadF->BlockStarts[I].second; // reuse block ID
        }
    }

    if (Pass->verbose) errs () << "New " << name(yieldType) << " block: " << *I << "\n";

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
        } else if (call->getCalledFunction ()->getName ().endswith("__assert_rtn")) {
        } else if (call->getCalledFunction ()->getName ().endswith("__assert")) {
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
            insertBlock (firstNonPhi, StaticLocal);
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

        int b = insertBlock (Start, StaticLocal);
        assert (b == 0); // start block
    }

    Instruction *
    process (Instruction *I)
    {
        LLASSERT (Pass->I2T.find(I) == Pass->I2T.end(),
                  "Instuction not allow twice in different threads: " << *I);

        Pass->I2T[I] = ThreadF;

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

/**
 *
 */
struct Liptonize : public LiptonPass::Processor {



    mover_e
    movable(Instruction *I)
    {
        if (singleThreaded(I)) {
            return BothMover;
        }

        LiptonPass::LLVMThread *T = Pass->I2T[I];

        for (pair<Function *, LiptonPass::LLVMThread *> &X : Pass->Threads) {
            LiptonPass::LLVMThread *T2 = X.second;
            if (T == T2 && T->Runs->size() == 1)
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

    static StringRef                Action;
    DenseMap<BasicBlock *, int>     Seen;
    area_e                          Area = Pre;
    vector<StackElem>               Stack;

    using Processor::Processor;
    ~Liptonize() { }

    bool
    block ( BasicBlock &B )
    {
        int &seen = Seen[&B];

        if (seen == 0) {
            if (Pass->verbose) errs() << name(Area)  <<": "<< B << "\n";
            Stack.push_back ( StackElem(Area, &B) );
            seen = -Stack.size();
            return true;
        }

        if (seen < 0) { // stack
            int Index = -seen - 1;
            StackElem Previous = Stack[Index];
            if (Previous.Seen < Area) {
                if (Pass->verbose) errs() << name(Area)  <<" --(revisit)--> "<<  name(Previous.Seen) <<": "<< B << "\n";

                if (Area != Pre && Previous.Seen != Post) { // Post --> Pre
                    insertBlock (B.getFirstNonPHI(), CommDynamic);
                }

                // re-explore: make stack overlap:
                Previous.Seen = Area;
                StackElem Next = StackElem (Area, &B);
                Next.Last = Index;
                Stack.push_back (Next);
                seen = -Stack.size(); // update to highest on stack (Next)
                return true;
            }
        } else {
            if (seen < Area) {
                if (Pass->verbose) errs() << name(Area)  <<" --(revisit)--> "<<  name((area_e)seen) <<": "<< B << "\n";
                if (Area != Pre && seen != Post) { // Post --> Pre
                    insertBlock (B.getFirstNonPHI(), CommDynamic);
                }

                // re-explore visited blocks:
                if (Pass->verbose) errs() << name(Area)  <<" (revisit): "<< B << "\n";
                Stack.push_back ( StackElem(Area, &B) );
                seen = -Stack.size();
                return true;
            }
        }
        //assert (seen < 0 ?  Stack[-seen - 1].Seen >= Area : (area_e &)seen) >= Area);

        return false;
    }

    void
    deblock ( BasicBlock &B )
    {
        StackElem &Pop = Stack.back();
        Area = Pop.Area;
        if (Pop.Last != -1) { // overlapping stacks: revert Seen to underlying
            Seen[&B] = Pop.Last;
            Stack[Pop.Last].Seen = Pop.Seen;
        } else {
            Seen[&B] = Pop.Seen;
        }
        Stack.pop_back();
    }

    void
    thread (Function *T)
    {
        assert (Stack.empty());
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
            assert (false); // record block
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

        } else if (call->getCalledFunction ()->getName ().endswith("__assert_rtn")) {
        } else if (call->getCalledFunction ()->getName ().endswith("__assert")) {

        } else {
            return nullptr;
        }
        return call;
    }

    Instruction *
    process (Instruction *I)
    {
        if (I->isTerminator()) {
            return I;
        }

        mover_e m = movable (I);
        return doHandle (I, m);
    }

private:
    Instruction *
    doHandle (Instruction *I, mover_e m) // may overwrite less dynamic blocks
    {
        if (Pass->verbose) errs () << name(Area) << *I << " -> \t"<< name(m) << "\n";

        addMetaData (I, AREA, name(Area));

        if (Pass->staticAll) {

            assert (Area != Top);
            if (isBlockStart(I) && ThreadF->BlockStarts[I].first == Static) {
                Area = Pre;
            }

            switch (m) {
            case RightMover:
                if (Area == Post) {
                    insertBlock (I, Static);
                    Area = Pre;
                }
                break;
            case LeftMover:
                Area = Post;
                break;
            case NoneMover:
                if (Area == Post) {
                    insertBlock (I, Static);
                }
                Area = Post; // in both cases, everything after I is a post-commit area
                break;
            case BothMover:
                return I; // no mover annotation!
            default:
                ASSERT(false, "Missing case.");
            }

        } else {

            switch (m) {
            case RightMover:
                if (Area != Pre) {
                    insertBlock (I, PhaseDynamic);
                    Area = Top;
                }
                break;
            case LeftMover:
                if (Area != Post) {
                    insertBlock (I, NoBlock);
                }
                Area = Post;
                break;
            case NoneMover:
                if (Area == Pre) {
                    insertBlock (I, NoBlock);
                } else {
                    insertBlock (I, CommDynamic);
                }
                Area = Post; // in both cases , everything after I is a post-commit area
                break;
            case BothMover:
                return I; // no mover annotation!
            default:
                ASSERT(false, "Missing case.");
            }

        }

        addMetaData (I, MOVER, name(m));

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
    ProcessorT processor(this, ProcessorT::Action);
    handle = &processor;

    // handle main first, as execution starts there
    Function *Main = M.getFunction("main");
    // Create new LLVM thread if it doesn't exist
    if (Threads.find(Main) == Threads.end()) {
        Threads[Main] = new LLVMThread(Main, Threads.size(), this);
    }
    processor.thread (Main);
    walkGraph (*Main);

    for (pair<Function *, vector<Instruction *>> &X : Reach->Threads) {
        Function *T = X.first;
        if (T->getName().equals("main")) continue; // skip main

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
    LLASSERT (I2T.find(I) != I2T.end(), "Missed: "<< *I << "\n Block: " << *I->getParent());
    LLVMThread *T = I2T[I];
    unsigned TCount = T->Runs->size();

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

enum local_e {
    Local,
    Global
};

static void
insertYield (Instruction* I, local_e type, int block)
{
    Value* blockId = ConstantInt::get (Yield->getFunctionType ()->getParamType (0), block);

    switch (type) {
    case Global:    CallInst::Create (Yield, blockId, "", I);       break;
    case Local:     CallInst::Create (YieldLocal, blockId, "", I);  break;
    }
}

void
LiptonPass::dynamicYield (Instruction *I, block_e type, int block)
{
    LLASSERT (I2T.find(I) != I2T.end(), "Missed: "<< *I << "\n Block: " << *I->getParent());
    LLVMThread *T = I2T[I];
    AllocaInst *Phase = T->PhaseVar;

    assert (!staticAll);

    if (!noDyn && type == CommDynamic) {
        type = PhaseDynamic;
    }

    Instruction *PhaseCheck = I;
    TerminatorInst *PostBranch;
    TerminatorInst *PreBranch;
    SmallVector<Value*, 8> sv;
    LoadInst *P;

    switch (type) {
    case NoBlock:
        new StoreInst(POSTCOMMIT, Phase, I); // ? --> Post (for after I)
        break;
    case Static:
        insertYield (I, Global, block);
        break;
    case StaticLocal:
        if (block == 0) return;
        insertYield (I, Local, block);
        break;
    case CommDynamic:
        // First collect conflicting non-movers from other threads
        conflictingNonMovers (sv, I);

        if (!sv.empty()) {
            // if in dynamic conflict
            Value *DynConflict = CallInst::Create(Act, sv, "", I);
            PhaseCheck = SplitBlockAndInsertIfThen (DynConflict, I, false);
        }
        [[clang::fallthrough]]; // fall through (dyn commutativity implies dyn phase):
    case PhaseDynamic:
        P = new LoadInst(Phase, "", PhaseCheck);
        SplitBlockAndInsertIfThenElse (P, PhaseCheck, &PostBranch, &PreBranch);
        new StoreInst(POSTCOMMIT, Phase, PreBranch); // Pre --> Post (for after I)

        new StoreInst(PRECOMMIT, Phase, PostBranch); // Post --> Pre (temporarily)
        insertYield (PostBranch, Global, block);
        new StoreInst(POSTCOMMIT, Phase, PostBranch); // Pre --> Post (for after I)
        break;
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
    Yield = cast<Function> (C);


    Constant *C3 = M.getOrInsertFunction (__YIELD_LOCAL, Void, Int, (Type*)(0));
    YieldLocal = cast<Function> (C3);

    Type *Bool = Type::getInt1Ty (M.getContext ());
    Constant *C2 = M.getOrInsertFunction (__ACT, FunctionType::get (Bool, true));
    Act = cast<Function> (C2);
    Int64 = Type::getInt64Ty(M.getContext());

    // fix meta data strings order
    Instruction *firstNonPhi =
            M.getFunctionList ().begin ()->getEntryBlock ().getFirstNonPHI ();
    addMetaData (firstNonPhi, MOVER, name(BothMover));
    addMetaData (firstNonPhi, MOVER, name(LeftMover));
    addMetaData (firstNonPhi, MOVER, name(RightMover));
    addMetaData (firstNonPhi, MOVER, name(NoneMover));

    addMetaData (firstNonPhi, AREA, name(Pre));
    addMetaData (firstNonPhi, AREA, name(Post));
    addMetaData (firstNonPhi, AREA, name(Top));
    getMetaData (firstNonPhi, AREA);
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
        for (pair<Function *, LLVMThread *> T : Threads) {
            for (pair<Instruction *, pair<block_e, int>> X : T.second->BlockStarts) {
                int block = X.second.second;
                Instruction *I = X.first;
                block_e type = X.second.first;
                assert (type == StaticLocal || type == Static);

                if (block != 0 && type != NoBlock) {
                    insertYield (I, type == StaticLocal ? Local : Global, block);
                }
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
                dynamicYield (I, type, block);
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

    // Collect thread reachability info +
    // Collect movability info          +
    // Break loops with static yields
    walkGraph<Collect> (M);

    // Identify and number blocks statically
    // (assuming all dynamic non-movers are static non-movers)
    walkGraph<Liptonize> (M);

    // Insert dynamic yields
    finalInstrument (M);

    return true; // modified module by inserting yields
}

} // LiptonPass

