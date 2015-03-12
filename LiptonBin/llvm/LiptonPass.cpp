
#include "LiptonPass.h"
#include "util/BitMatrix.h"
#include "util/Util.h"
#include "llvm/Util.h"

#include <algorithm>    // std::sort
#include <assert.h>
#include <iostream>
#include <set>
#include <string>

#include <llvm/Pass.h>
#include <llvm/PassRegistry.h>
#include <llvm/PassSupport.h>
#include <llvm/Analysis/Passes.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/BasicBlock.h>
#include <llvm/IR/InstIterator.h>
#include <llvm/IR/Function.h>
#include <llvm/BitCode/ReaderWriter.h>

#include <llvm/ADT/DenseSet.h>
#include <llvm/IR/ValueMap.h>


using namespace llvm;
using namespace std;


namespace VVT {

//TODO: locks are left movers!

static const char* PTHREAD_YIELD    = "pthread_yield";
//static const char* PTHREAD_CREATE   = "pthread_create";
//static const char* PTHREAD_JOIN     = "pthread_join";


char LiptonPass::ID = 0;
static RegisterPass<LiptonPass> X("lipton", "Lipton reduction");

LiptonPass::LiptonPass () : ModulePass(ID),
        Name ("out"),
        Yield (nullptr),
        AA (nullptr),
        Reach (nullptr)
{ }

LiptonPass::LiptonPass (ReachPass &RP, string name) : ModulePass(ID),
        Name (name),
        Yield (nullptr),
        AA (nullptr),
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
    outs () << (loc == YIELD_BEFORE ? "before" : "after") << ": " << *I << "\n";
    if (isYieldCall(I) || (!isFirstInBlock(I) &&
                               isYieldCall(I->getPrevNode()))) {
        return;
    }
    CallInst::Create(Yield, "", I);
    //Call->set
}


mover_e
LiptonPass::movable(Instruction *I)
{
    Function* F = I->getParent ()->getParent ();
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

    void yield (Instruction *I) {}


    bool
    block ( BasicBlock &B )
    {
        state_e &seen = Seen[&B];
        outs() << Action << ": " << B << seen <<endll;
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
        AliasSetTracker *AST = Pass->ThreadAliases[ThreadF];
        if (AST == nullptr)
            AST = Pass->ThreadAliases[ThreadF] = new AliasSetTracker (*Pass->AA);
        AST->add (I);
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
            outs() << (Area==RightArea?"R ":"L ")<< B << "\n";
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
            if (Area == LeftArea) {
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
    }

    void
    yield (Instruction *I)
    {
        outs () << "Yield "<< *I <<"\n";
        Area = RightArea;
    }

    Instruction *
    process (Instruction *I)
    {
        assert (!Pass->isYieldCall(I));
        mover_e m = Pass->movable (I);

        outs () << (Area==RightArea?"R ":"L ") << *I << " -> \t"<< name(m) <<"\n";
        Instruction *Ret = I;
        switch (m) {
        case RightMover:
            if (Area == LeftArea) {
                Area = RightArea;
                assert (!I->isTerminator());
                Pass->insertYield (I, YIELD_AFTER);
                Ret = I->getNextNode ();
            }
            break;
        case LeftMover:
            Area = Area == RightArea ? RightArea : LeftArea;
            break;
        case NoneMover:
            if (Area == LeftArea) {
                assert (!I->isTerminator());
                Pass->insertYield (I, YIELD_AFTER);
                Ret = I->getNextNode ();
            } else {
                Area = LeftArea;
            }
            break;
        case BothMover: break;
        default:
            ASSERT (false, "Missing case.");
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
        } else if (call->getCalledFunction ()->getName () == PTHREAD_YIELD) {
            handle->yield (I);
        } else {
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
    outs() << F.getName() << "\n";
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

bool
LiptonPass::runOnModule (Module &M)
{
    AA = &getAnalysis<AliasAnalysis> ();
    Type* Void = FunctionType::getVoidTy (M.getContext ());
    FunctionType* FT = FunctionType::get (Void, false);
    Constant* C = M.getOrInsertFunction (PTHREAD_YIELD, FT);
    Yield = cast<Function> (C);

    walkGraph<Collect> ();
    walkGraph<Liptonize> ();

    outs() << dynamic_cast<Pass*>(AA)->getPassName() << endll;

    return true;
}

} // VVT































