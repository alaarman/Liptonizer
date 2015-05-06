
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
#include <llvm/BitCode/ReaderWriter.h>
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
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/Local.h"
#include "llvm/Transforms/Utils/ModuleUtils.h"

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
        Reach (nullptr)
{ }

LiptonPass::LiptonPass (ReachPass &RP, string name, bool v) : ModulePass(ID),
        Name (name),
        verbose(v),
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
        } // TODO: locks
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

    using Processor::Processor;
    ~Collect() { }

    bool
    yield (CallInst *call)
    {
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
        if (Pass->verbose) outs() << Action << ": " << B << seen <<endll;
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
        ThreadF = F;
        Seen.clear(); // restart with exploration
    }

    Instruction *
    process (Instruction *I)
    {
        Pass->Instructions[ThreadF].push_back(I);
        AliasSetTracker *AST = Pass->ThreadAliases[ThreadF];
        if (AST == nullptr)
            AST = Pass->ThreadAliases[ThreadF] = new AliasSetTracker (*Pass->AA);
        AST->add (I);

        AliasSet *AS = FindAliasSetForUnknownInst (AST, I);
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
            if (Pass->verbose) outs() << (Area==RightArea?"R ":"L ")<< B << "\n";
            if (Pass->isYieldCall(B.getFirstNonPHI())) {
                // safe to enter B as left area now
                Stack.push_back ( StackElem(LeftArea, &B) );
            } else {
                Stack.push_back ( StackElem(Area, &B) );
            }
            seen = --StackDepth;
            return true;
        } else if (seen < 0) {
        } else if (seen == RightArea) {
            if (false && Area == LeftArea) {  // TODO: Can be removed now that things are dynamic
                Instruction* firstNonPhi = B.getFirstNonPHI ();
                LLASSERT (firstNonPhi, "No Instruction in " << B);
                Pass->insertYield (firstNonPhi, YIELD_BEFORE);
                // safe to enter B as left area now
                seen = LeftArea;
            }
        } else {
            assert (seen == LeftArea);
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
        Pass->Block = 1;
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
        //if (Pass->verbose)
        outs () << (Area == RightArea ? "R " : "L ") << *I << " -> \t"
                << name (m) << "\n";
        Instruction* Ret = I;

        switch (m) {
        case RightMover:
            if (Area == LeftArea) {
                Area = RightArea;
                assert(!I->isTerminator ());
                Pass->insertYield (I, YIELD_BEFORE);
                //Pass->YieldBefore.insert(I);
            }
            break;
        case LeftMover:
            Area = Area == RightArea ? RightArea : LeftArea;
            break;
        case NoneMover:
            if (Area == LeftArea) {
                assert(!I->isTerminator ());
                //Pass->insertYield (I, YIELD_AFTER);
                //Ret = I->getNextNode ();
                outs () << *I << "  $$$$$$$$$$$$$$$$$  " << Pass->Block << endll;
                Pass->Movers[I] = make_pair(m, Pass->Block++);
                //Pass->YieldBefore.insert(I);
            } else {
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
           outs() << "Handle library call: "<<
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
    if (verbose) outs() << F.getName() << "\n";
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

void
LiptonPass::doYield (Instruction *I, int block)
{
    //ReachPass *Reach = cast<ReachPass>(&getAnalysis<ReachPass> ());

    SmallVector<Value*, 8> sv;

    Type* Ptr = Act->getFunctionType ()->getParamType (0);
    Function *F = I->getParent ()->getParent ();
    unsigned TCount = Reach->Threads[F].size ();
    for (pair<Function *, AliasSetTracker *> &X : ThreadAliases) {
        Function* G = X.first;
        if (G == F && TCount == 1)
            continue;

        Constant *FP = ConstantExpr::getBitCast (G, Ptr);
        sv.push_back(FP);
        AliasSet *AS = FindAliasSetForUnknownInst (X.second, I);
        if (AS == nullptr) continue;

        for (Instruction *J : AS2I[AS]) {
            if (J == I) continue;

            for (Instruction *R : Instructions[G]) {
                if (Reach->stCon(R, J)) {
                    int b = Movers[R].second;
                    Value *num = Constant::getIntegerValue (Ptr, APInt(64, b));
                    sv.push_back(num);
                }
            }
        }
    }

    // if in postcommit (!phase) and dynamic conflict
    LoadInst *P = new LoadInst(Phase, "", I);
    CallInst *C;
    if (sv.size() == 0) {
        Constant *True = ConstantInt::get(Act->getFunctionType()->getParamType(0), 1);
        C = CallInst::Create(Act, True, "", I);
    } else {
        C = CallInst::Create(Act, sv, "", I);
    }
    Value *NP = BinaryOperator::CreateNot(P, "", I);
    Value *IfCond = BinaryOperator::CreateAnd(NP, C, "", I);

    // if in postcommit (!phase) and dynamic conflict, then yield
    TerminatorInst *term = SplitBlockAndInsertIfThen (IfCond, I, false, nullptr, nullptr);
    Value *num = ConstantInt::get(Yield->getFunctionType()->getParamType(0), Block++);
    CallInst::Create(Yield, num, "", term);

    // Phase' := Phase XOR Conflict
    Value *PP = BinaryOperator::CreateXor(P, C, "", I);
    new StoreInst(PP, Phase, I);
}

bool
LiptonPass::runOnModule (Module &M)
{
    AA = &getAnalysis<AliasAnalysis> ();

    Type *Int = Type::getInt32Ty(M.getContext());

    Type *Void = FunctionType::getVoidTy (M.getContext());
    Constant *C = M.getOrInsertFunction (__YIELD, Void, Int, (Type *) 0);
    Yield = cast<Function> (C);
    //Yield->dump();

    Type *Bool = Type::getInt1Ty (M.getContext());
    Type *Ptr = Type::getInt64PtrTy(M.getContext(), 0);
    Constant *C2 = M.getOrInsertFunction (__ACT, FunctionType::get(Bool, Ptr, true));
    Act = cast<Function> (C2);

    Phase = (GlobalVariable *) M.getOrInsertGlobal("__phase", Bool);
    //Cond = (GlobalVariable *) M.getOrInsertGlobal("__cond", Bool);
    Phase->setThreadLocal(true);
    //Cond->setThreadLocal(true);
    PRECOMMIT = ConstantInt::get(Bool, 1);
    Phase->setInitializer(PRECOMMIT);

    walkGraph<Collect> ();
    walkGraph<Liptonize> (); // number static blocks

    for (pair<Instruction *, pair<mover_e, int>> X : Movers) {
        doYield(X.first, X.second.second);
    }

    //outs() << dynamic_cast<Pass*>(AA)->getPassName() << endll;

    return true;
}

} // VVT

