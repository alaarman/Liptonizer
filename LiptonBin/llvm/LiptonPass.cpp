
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

static const char* PTHREAD_YIELD    = "pthread_yield";
//static const char* PTHREAD_CREATE   = "pthread_create";
//static const char* PTHREAD_JOIN     = "pthread_join";


char LiptonPass::ID = 0;
static RegisterPass<LiptonPass> X("lipton", "Lipton reduction");

LiptonPass::LiptonPass () : ModulePass(ID),
        Yield (nullptr),
        AA (nullptr),
        Reach (nullptr)
{ }

LiptonPass::LiptonPass (ReachPass &RP) : ModulePass(ID),
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

void
LiptonPass::walkGraph ( Instruction *I )
{
    if (CallInst *call = dyn_cast<CallInst>(I)) {
        DenseMap<Instruction *, Function *> callRecords = Reach->callRecords;
        if (callRecords.find (call) != callRecords.end ()) {
            walkGraph (*callRecords[call]);
        } else if (call->getCalledFunction ()->getName () == PTHREAD_YIELD) {
            handle->yield (I);
        } else {
            outs() << "Handle library call: "<< call->getCalledFunction()->getName() <<"\n";
        }
    } else {
        I = handle[0] (I);
    }

    if (TerminatorInst *T = dyn_cast<TerminatorInst> (I)) {
        assert (I == I->getParent()->getTerminator());
        for (int i = 0, num = T->getNumSuccessors(); i < num; ++i) {
            BasicBlock *B = T->getSuccessor(i);
            walkGraph (*B);
        }
    } else {
        walkGraph (I->getNextNode());
    }
}

void
LiptonPass::walkGraph ( BasicBlock &B )
{
    int *seen = &Seen[&B];
    if (*seen == 0) {
        outs() << B << "\n";
        *seen = ++StackDepth;
        walkGraph (&B.front());
        StackDepth--;
        *seen = -1;
    } else {

    }
}

void
LiptonPass::walkGraph ( Function &F )
{
    outs() << F.getName() << "\n";
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

    void yield (Instruction *I) { }

    Instruction *
    operator() (Instruction *I)
    {
        Pass->TI[ThreadF].push_back (I);
        return I;
    }
};

struct Liptonize : public LiptonPass::Processor {

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

    void
    yield (Instruction *I)
    {
        Area = RightArea;
    }

    Instruction *
    operator()(Instruction *I)
    {
        mover_e m = movable (I);

        Instruction *Ret = I;
        switch (m) {
        case RightMover:
            if (Area == LeftArea) {
                Area = RightArea;
                assert (!I->isTerminator());
                I->insertAfter(CallInst::Create(Pass->Yield));
                Ret = I->getNextNode();
            }
            break;
        case LeftMover:
            Area = Area == RightArea ? RightArea : LeftArea;
            break;
        case NoneMover:
            if (Area == LeftArea) {
                assert (!I->isTerminator());
                I->insertAfter(CallInst::Create(Pass->Yield));
                Ret = I->getNextNode();
            }
            Area = LeftArea;
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

template <typename ProcessorT>
void
LiptonPass::walkGraph ( CallGraph &CG )
{
    for (pair<Function *, vector<Instruction *>> &X : Reach->Threads) {
        Function* Thread = X.first;
        ProcessorT processor(this, Thread, ProcessorT::Action);
        processor.initialize();
        handle = &processor;
        walkGraph (*CG[Thread]);
    }
}

bool
LiptonPass::runOnModule (Module &M)
{
    AA = &getAnalysis<AliasAnalysis>();
    //Reach = &getAnalysis<ReachPass>();
    Constant* C = M.getOrInsertFunction(PTHREAD_YIELD,
                                        Type::getVoidTy(M.getContext()), NULL);
    CallGraph &CG = getAnalysis<CallGraphWrapperPass>().getCallGraph();
    Yield = cast<Function>(C);//CG.getModule().getFunction(PTHREAD_YIELD);

    walkGraph<Collect> ( CG );
    walkGraph<Liptonize> ( CG );

    outs() << M << "\n";
    return true;
}

} // VVT































