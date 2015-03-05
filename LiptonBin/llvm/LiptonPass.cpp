
#include "LiptonPass.h"
#include "util/BitMatrix.h"
#include "util/Util.h"

#include <algorithm>    // std::sort
#include <assert.h>
#include <iostream>
#include <set>
#include <string>

#include <llvm/Pass.h>
#include <llvm/PassRegistry.h>
#include <llvm/PassSupport.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/BasicBlock.h>
#include <llvm/IR/Function.h>
#include <llvm/Support/raw_ostream.h>

#include <llvm/ADT/DenseSet.h>
#include <llvm/IR/ValueMap.h>


using namespace llvm;
using namespace std;


namespace VVT {

char LiptonPass::ID = 0;
static RegisterPass<LiptonPass> X("lipton", "Lipton reduction");

LiptonPass::LiptonPass() : ModulePass(ID),
        Yield (nullptr),
        AA (nullptr),
        Reach (nullptr)
{ }

void
LiptonPass::getAnalysisUsage(AnalysisUsage &AU) const
{
    AU.setPreservesCFG();
    //AU.addRequired<AliasAnalysis>();
    //AU.addRequired<CallGraphWrapperPass>();
    AU.addRequired<ReachPass>();
}

void
LiptonPass::walkGraph ( TerminatorInst *T )
{
    for (int i = 0, num = T->getNumSuccessors(); i < num; ++i) {
        BasicBlock *B = T->getSuccessor(i);
        walkGraph (*B);
    }
}

void
LiptonPass::walkGraph ( Instruction *I )
{
    CallInst *call;
    if ((call = dyn_cast<CallInst>(I))) {
        ReachPass &Reach = getAnalysis<ReachPass>();
        DenseMap<Instruction *, Function *> callRecords = Reach.callRecords;
        //DenseMap<Instruction *, Function *>::iterator rec = ;
        if (callRecords.find (call) != callRecords.end ()) {
            walkGraph (*callRecords[call]);
        } else {
            outs() << "Handle library call: "<< call->getCalledFunction()->getName() <<"\n";
        }
    } else {
        I = (*process) (this, I);
    }

    if (I->getNextNode() != nullptr) {
        walkGraph (I->getNextNode());
    } else {
        assert (I == I->getParent()->getTerminator());
        walkGraph (dyn_cast<TerminatorInst>(I));
    }
}

void
LiptonPass::walkGraph ( BasicBlock &B )
{
    walkGraph (&B.front());
}

void
LiptonPass::walkGraph ( Function &F )
{
    walkGraph (F.getEntryBlock());
}

void
LiptonPass::walkGraph ( CallGraphNode &N )
{
    walkGraph (*N.getFunction());
}

struct Collect : public LiptonPass::Processor {
    static StringRef Action;

    using Processor::Processor;
    ~Collect() { }

    vector<Instruction *> content;

    Instruction *
    operator()(Instruction *I)
    {
        Pass->TI[ThreadF].push_back (I);
        content.push_back (I);
        return I;
    }
};

struct Liptonize : public LiptonPass::Processor { // liptonize it, uhmmmhu

    enum mover_e {
        RightMover = 0,
        NoneMover,
        LeftMover,
        BothMover,
    };

    enum area_e {
        RightArea = 0,
        LeftArea,
    };

    static StringRef    Action;
    area_e              Area : 1;

    using Processor::Processor;
    ~Liptonize() { }

    void
    initialize()
    {
        Area = RightArea;
    }

    mover_e
    movable(Instruction *I)
    {
        Function* F = I->getParent ()->getParent ();
        unsigned TCount = Pass->Reach->Threads[F].size ();
        for (pair<Function *, vector<Instruction *>> &X : Pass->TI) {
            if (X.first == F && TCount == 1)
                continue;
            for (Instruction *J : X.second) {
                switch (Pass->AA->alias(J, I)) {
                case AliasAnalysis::MayAlias:
                case AliasAnalysis::PartialAlias:
                case AliasAnalysis::MustAlias:
                    return NoneMover;
                case AliasAnalysis::NoAlias:
                    break;
                default:
                    ASSERT (false, "Missing case.");
                }
            }
        }
        return BothMover;
    }

    // 0 == Right
    // 1 == None
    // 2 == Left
    Instruction *
    operator()(Instruction *I)
    {
        mover_e m = movable (I);
        switch (m) {
        case RightMover:
            if (Area == LeftArea) {
                assert (!dyn_cast<TerminatorInst>(I));
                I->insertAfter(CallInst::Create(Pass->Yield));
                return I->getNextNode();
            }
            Area = Area == LeftArea ? LeftArea : RightArea;
            break;
        case LeftMover:
            Area = Area == RightArea ? RightArea : LeftArea;
            break;
        case NoneMover:
            Area = LeftArea;
            break;
        case BothMover: break;
        default:
            ASSERT (false, "Missing case.");
        }
        return I;
    }
};

StringRef Collect::Action = "Collecting";
StringRef  Liptonize::Action = "Liptonizing";

template <typename ProcessorT>
void
LiptonPass::walkGraph ( CallGraph &CG )
{
    for (pair<Function *, vector<Instruction *>> &X : Reach->Threads) {

        Function* Thread = X.first;
        ProcessorT processor(this, Thread, ProcessorT::Action);
        processor.initialize();
        process = &processor;
        walkGraph (*CG[Thread]);
        delete process;

    }
}

bool
LiptonPass::runOnModule (Module &M)
{
    //AA = &getAnalysis<AliasAnalysis>();
    Reach = &getAnalysis<ReachPass>();
    Reach->finalize();
    CallGraph &CG = getAnalysis<CallGraphWrapperPass>().getCallGraph();
    Yield = CG.getModule().getFunction("pthread_yield");
    assert (Yield);


    walkGraph<Collect> ( CG );
    walkGraph<Liptonize> ( CG );

    return true;
}

} // VVT































