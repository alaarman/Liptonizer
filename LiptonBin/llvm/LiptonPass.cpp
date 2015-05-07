
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

static Constant *PRECOMMIT;

static const char* __YIELD          = "__yield";
static const char* __ACT            = "__act";
static const char* PTHREAD_YIELD    = "pthread_yield";
static const char* PTHREAD_CREATE   = "pthread_create";
static const char* PTHREAD_JOIN     = "pthread_join";
static const char* PTHREAD_LOCK     = "pthread_mutex_lock";
static const char* PTHREAD_UNLOCK   = "pthread_mutex_unlock";
static const char* PTHREAD_MUTEX_INIT = "pthread_mutex_init";


char LiptonPass::ID = 0;
static RegisterPass<LiptonPass> X("lipton", "Lipton reduction");

LiptonPass::LiptonPass () : ModulePass(ID),
        Name ("out"),
        verbose(true),
        staticBlocks(false),
        Reach (nullptr)
{ }

LiptonPass::LiptonPass (ReachPass &RP, string name, bool v, bool staticBlocks)
                                                            : ModulePass(ID),
        Name (name),
        verbose(v),
        staticBlocks(staticBlocks),
        Reach (&RP)
{ }

void
LiptonPass::getAnalysisUsage (AnalysisUsage &AU) const
{
    AU.setPreservesCFG();
//    AU.addRequired<ReachPass>();
    AU.addRequired<AliasAnalysis>();
    AU.addRequired<CallGraphWrapperPass>();
}

bool
LiptonPass::isYieldCall (Instruction *I)
{
    if (CallInst *Call = dyn_cast_or_null<CallInst>(I)) {
        return Call->getCalledFunction() == Yield;
    }
    return false;
}

static bool
isFirstInBlock (Instruction *I)
{
    return &I->getParent ()->front () == I;
}

void
LiptonPass::insertYield (Instruction *I, yield_loc_e loc)
{
    if (loc == YIELD_AFTER) {
        I = I->getNextNode();
    }
    if (verbose) outs () << (loc == YIELD_BEFORE ? "before" : "after") << ": " << *I << "\n";
    if (isYieldCall(I) || (!isFirstInBlock(I) &&
                               isYieldCall(I->getPrevNode()))) {
        return;
    }

    // forced block (left to right) or loop, always static:
    BlockStarts[I] = make_pair (Static, Block);

    Value *num = ConstantInt::get(Yield->getFunctionType()->getParamType(0), Block++);
    CallInst::Create(Yield, num, "", I);
}

mover_e
LiptonPass::movable(Instruction *I)
{
    Function *F = I->getParent ()->getParent ();
    unsigned TCount = Reach->Threads[F].size ();
    for (pair<Function *, AliasSetTracker *> &X : ThreadAliases) {
        if (X.first == F && TCount == 1)
            continue;

        for (AliasSet &s : *X.second) {
            if (s.aliasesUnknownInst(I, *AA)) return NoneMover;
        }
    }
    return BothMover;
}


static AliasSet *
FindAliasSetForUnknownInst(AliasSetTracker *AST, Instruction *Inst)
{
    for (AliasSet &AS : *AST) {
        if (AS.aliasesUnknownInst(Inst, AST->getAliasAnalysis()))
            return &AS;
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
    AliasSetTracker                *AST;

    using Processor::Processor;
    ~Collect() { }

    bool
    yield (CallInst *call)
    {
        Pass->I2T[call] = ThreadF;
        if (call->getCalledFunction ()->getName ().endswith(PTHREAD_YIELD)) {
        } else if (call->getCalledFunction ()->getName ().endswith(PTHREAD_LOCK)) {
        } else if (call->getCalledFunction ()->getName ().endswith(PTHREAD_UNLOCK)) {
        } else if (call->getCalledFunction ()->getName ().endswith(PTHREAD_CREATE)) {
        } else if (call->getCalledFunction ()->getName ().endswith(PTHREAD_JOIN)) {
        } else if (call->getCalledFunction ()->getName ().endswith(PTHREAD_MUTEX_INIT)) {
        } else {
            return false;
        }
        return true;
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
            if (!Pass->isYieldCall(firstNonPhi)) {
                Pass->insertYield (firstNonPhi, YIELD_BEFORE);
            }
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
        //Pass->Block = 1; // TODO: Restart numbering for each thread
        ThreadF = F;
        AST = new AliasSetTracker (*Pass->AA);
        Pass->ThreadAliases.insert(make_pair(ThreadF, AST));

        //errs() << "*********************** "<< F->getName() << endll;
        Seen.clear(); // restart with exploration
        Instruction *Start = F->getEntryBlock ().getFirstNonPHI ();

        // Skip empty blocks, as we do not want terminators in BlockStarts
        while (TerminatorInst *T = dyn_cast<TerminatorInst> (Start)) {
            assert (T->getNumSuccessors() == 1);
            Start = T->getSuccessor(0)->getFirstNonPHI();
        }

        Pass->BlockStarts[Start] = make_pair (Static, 0); // TODO: unique?
    }

    Instruction *
    process (Instruction *I)
    {
        LLASSERT (Pass->I2T.find(I) == Pass->I2T.end(),
                  "Instuction not allow twice in different threads: " << *I);

        Pass->I2T[I] = ThreadF;

 //       bool harmless =
                AST->add (I);
 //       errs() << *I << " +++++" << ThreadF->getName() << "++++ --> " << harmless << endll;

        //if (!harmless) {
            AliasSet *AS = FindAliasSetForUnknownInst (AST, I);
            Pass->AS2I[AS].push_back(I);
        //}
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
        default: ASSERT (false, "Missing case.");
        }
    }

    enum area_e {
        RightArea = 1,
        LeftArea,
    };

    struct StackElem {
        StackElem (area_e a, BasicBlock *B) : Area(a), Block(B) {  }
        area_e                  Area;
        BasicBlock             *Block;
    };

    static StringRef                Action;
    DenseMap<BasicBlock *, int>     Seen;
    area_e                          Area = RightArea;
    int                             StackDepth = 0;
    vector<StackElem>               Stack;

    using Processor::Processor;
    ~Liptonize() { }

    bool
    block ( BasicBlock &B )
    {
        int &seen = Seen[&B];
        if (seen == 0) {
            if (Pass->verbose) errs() << (Area==RightArea?"R ":"L ")<< B << "\n";
            if (Pass->isYieldCall(B.getFirstNonPHI())) {
                // safe to enter B as left area now
                Stack.push_back ( StackElem(LeftArea, &B) );
            } else {
                Stack.push_back ( StackElem(Area, &B) );
            }
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
        ThreadF = T;
        Area = RightArea;
        //Seen.clear();  // TODO: overlapping threads!
    }

    bool
    yield (CallInst *call)
    {
        if (call->getCalledFunction ()->getName ().endswith(PTHREAD_YIELD)) {
            if (Pass->verbose) outs () << "Yield "<< *call <<"\n";
            Area = RightArea;
        } else if (call->getCalledFunction ()->getName ().endswith(PTHREAD_LOCK)) {
            doHandle (call, RightMover);
        } else if (call->getCalledFunction ()->getName ().endswith(PTHREAD_UNLOCK)) {
            doHandle (call, LeftMover);
        } else if (call->getCalledFunction ()->getName ().endswith(PTHREAD_CREATE)) {
            doHandle (call, LeftMover);
        } else if (call->getCalledFunction ()->getName ().endswith(PTHREAD_JOIN)) {
            doHandle (call, RightMover);
        } else if (call->getCalledFunction ()->getName ().endswith(PTHREAD_MUTEX_INIT)) {

        } else {
            return false;
        }
        return true;
    }

    Instruction *
    process (Instruction *I)
    {
        assert (!Pass->isYieldCall(I));
        mover_e m = Pass->movable (I);
        return doHandle (I, m);
    }

private:
    Instruction* doHandle (Instruction* I, mover_e m)
    {
        if (Pass->verbose)
        outs () << (Area == RightArea ? "R " : "L ") << *I << " -> \t"
                << name (m) << "\n";
        Instruction* Ret = I;

        switch (m) {
        case RightMover:
            if (Area == LeftArea) {
                Area = RightArea;
                assert(!I->isTerminator ());
                Pass->insertYield (I, YIELD_BEFORE);
            }
            break;
        case LeftMover:
            Area = LeftArea;
            break;
        case NoneMover:
            if (Area == LeftArea) {
                assert(!I->isTerminator ());
                Pass->BlockStarts[I] = make_pair (Dynamic, Pass->Block++);
            } else {
                Pass->BlockStarts[I] = make_pair (Dynamic, Pass->Block++);
                Area = LeftArea;
            }
            break;
        case BothMover:
            break;
        default:
            ASSERT(false, "Missing case.");
        }
        return Ret;
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
        } else if (!handle->yield (call)) {
           errs() << "Handle library call: "<<
                     call->getCalledFunction()->getName() <<"\n";
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
        processor.thread (X.first);
        walkGraph (*X.first);
    }
}

/**
 * Fills the small vector with arguments for the '__pass' function call
 * The following format is used: '__act(t_1, n_11,..., t2, n_21,....  )',
 * where t_x is a function pointer to the thread's functions and
 * { n_xy | y in N } is the set of conflicting blocks in that thread
 */
void
LiptonPass::conflictingNonMovers (SmallVector<Value *, 8> &sv,
                                  Instruction *I,
                                  DenseMap<Function *, Instruction *> &Starts)
{
    // First collect conflicting non-movers from other threads
    Function *F = I2T[I];
    unsigned TCount = Reach->Threads[F].size ();
    // for all other threads
    for (pair<Function *, AliasSetTracker *> &X : ThreadAliases) {
        Function *G = X.first;
        if (G == F && TCount == 1) // skip own thread function iff singleton
            continue;

        //errs() << F->getName() << "  <> "<< G->getName() <<endll;
        // Add thread identifier first
        //Instruction* si0 = Starts[G];
        sv.push_back(G);

        AliasSet* AS = FindAliasSetForUnknownInst (X.second, I);
        if (AS == nullptr)
            continue;

        DenseSet<int> Blocks;

        // for all conflicting J
        for (Instruction *J : AS2I[AS]) {
            //errs() << *I << "  <------------> "<< *J << endll;

            // for all Block starting points TODO: refine to exit points
            for (pair<Instruction *, pair<block_e, int> > X : BlockStarts) {
                Instruction* R = X.first;
                if (I2T[R] != G) continue;
                //outs () << *R  << " ---?---> " << *J;

                // if Block is in same process as J, and block can reach J
                if (//Reach->stCon (si0, R) &&
                     Reach->instructionMap[R] == Reach->instructionMap[J]  ||
                     Reach->stCon (R, J)) {

                    // add block index to __act
                    int b = X.second.second;
                    Value* num = Constant::getIntegerValue (Int64, APInt(64, b));
                    if (Blocks.insert(b).second)
                        sv.push_back (num);
                    //outs () <<" yes" << endll;
                } else {
                    //outs () <<" no" << endll;
                }
            }
        }

        // drop thread if it has no conflicting transitions
        if (sv.back() == G) {
            sv.pop_back();
        }
    }
}

void
LiptonPass::dynamicYield (DenseMap<Function *, Instruction *> &Starts,
                          Instruction *I, block_e type, int block)
{

    if (staticBlocks) {
        if (type == Dynamic) {
            Value *num = ConstantInt::get(Yield->getFunctionType()->getParamType(0), block);
            CallInst::Create(Yield, num, "", I);
        }
        return;
    }

    Function *T = I2T[I];
    if (!T) errs() << *I << "\n" << *I->getParent() << endll;
    AllocaInst *Phase = Phases[T];

    if (type == Static) {
        // set phase variable to true for static blocks
        new StoreInst(PRECOMMIT, Phase, I);
        return; // that's all
    }

//    outs () << T << "       "<<Phase  << " " << *I << endll;

    // First collect conflicting non-movers from other threads
    SmallVector<Value*, 8> sv;
    conflictingNonMovers (sv, I, Starts);

    // if in postcommit (!phase) and dynamic conflict
    LoadInst *P = new LoadInst(Phase, "", I);
    Value *C;
    if (sv.size() == 0) {
        //errs() << "Warning: non-mover without conflicts:\n"<< *I << endll;
        //errs() << endll;
        C = ConstantInt::get(Act->getFunctionType()->getReturnType(), 1);
    } else {
        //errs() <<"--"<< endll;
        //for (Value *V : sv)
        //    errs() << *V << endll;
        //errs() <<"--"<< endll;
        //errs() << endll;
        C = CallInst::Create(Act, sv, "", I);
    }
    Value *NP = BinaryOperator::CreateNot(P, "", I);
    Value *IfCond = BinaryOperator::CreateAnd(NP, C, "", I);

    // if in postcommit (!phase) and dynamic conflict, then yield
    TerminatorInst *term = SplitBlockAndInsertIfThen (IfCond, I, false, nullptr, nullptr);
    Value *num = ConstantInt::get(Yield->getFunctionType()->getParamType(0), block);
    CallInst::Create(Yield, num, "", term);

    // Phase' := Phase XOR Conflict
    Value *PP = BinaryOperator::CreateXor(P, C, "", I);
    new StoreInst(PP, Phase, I);
}

void
LiptonPass::initialInstrument (Module &M)
{
    // Add '__act' and '__yield' functions
    Type* Int = Type::getInt32Ty (M.getContext ());
    Type* Void = FunctionType::getVoidTy (M.getContext ());
    Constant* C = M.getOrInsertFunction (__YIELD, Void, Int, (Type*)(0));
    Yield = cast<Function> (C);
    Type* Bool = Type::getInt1Ty (M.getContext ());
    Constant* C2 = M.getOrInsertFunction (__ACT, FunctionType::get (Bool, true));
    Act = cast<Function> (C2);
    Int64 = Type::getInt64Ty(M.getContext());
}

void
LiptonPass::finalInstrument (Module &M)
{
    Type *Bool = Type::getInt1Ty (M.getContext());
    PRECOMMIT = ConstantInt::get (Bool, 1);

    // collect thread initial instructions (before instrumenting threads)
    DenseMap<Function *, Instruction *> Starts;
    for (pair<Function *, AliasSetTracker *> X : ThreadAliases) {
        Function *T = X.first;
        Instruction *Start = T->getEntryBlock().getFirstNonPHI();
        AllocaInst *Phase = new AllocaInst (Bool, "__phase", Start);
        //new StoreInst (PRECOMMIT, Phase, Start);
        Phases[T] = Phase;
        Starts[T] = Start;
    }

    // instrument code with dynamic yields
    for (pair<Instruction *, pair<block_e, int>> X : BlockStarts) {
        dynamicYield (Starts, X.first, X.second.first, X.second.second);
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

