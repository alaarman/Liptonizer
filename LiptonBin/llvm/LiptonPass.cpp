
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
        AA (getAnalysis<AliasAnalysis>()),
        Reach (getAnalysis<ReachPass>())
{ }

void
LiptonPass::getAnalysisUsage(AnalysisUsage &AU) const {
    AU.setPreservesAll();
    AU.addRequired<AliasAnalysis>();
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
        (*process) (this, I);
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

struct Collect : public LiptonPass::Process {
    ~Collect() { }

    vector<Instruction *> content;

    void
    operator()(LiptonPass *pass, Instruction *I)
    {
        content.push_back (I);
    }
};

struct Liptonize : public LiptonPass::Process { // liptonize it, uhmmmhu

    unsigned count : 2;

    ~Liptonize() { }
    Liptonize() : count(0) {}

    enum mover_e {
        NoneMover,
        LeftMover,
        RightMover,
        BothMover
    };

    mover_e
    movable(LiptonPass *pass, Instruction *I)
    {
        llvm::Function* F = I->getParent ()->getParent ();
        for (pair<Function *, vector<Instruction *>> &X : pass->Reach.Threads) {
            if (X.first == F && X.second.size() == 1)
                continue;
            for (Instruction *J : X.second) {
                switch (pass->AA.alias(J, I)) {
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
    operator()(LiptonPass *pass, Instruction *I)
    {
        mover_e m = movable (pass, I);
        switch (m) {
        case BothMover:
        case NoneMover:
            break;
        default:
            ASSERT (false, "Missing case.");
        }
    }
};

bool
LiptonPass::runOnModule (Module &M)
{
    CallGraph &CG = getAnalysis<CallGraphWrapperPass>().getCallGraph();
    CallGraphNode *external = CG.getExternalCallingNode();
    DenseMap<Function *, vector<Instruction *>> *T = &Reach.Threads;

    for (CallGraphNode::CallRecord rec : *external) {
        Function *entry = rec.second->getFunction ();
        if (entry->size() == 0) continue; // library function
        if (T->find(entry) == T->end()) continue; // not a thread

        outs() << "Collecting "<< entry->getName() <<"\n";
        process = new Collect();
        walkGraph ( *CG[entry] );
        TI.insert (make_pair(entry, &static_cast<Collect *>(process)->content));
        // leaks, but collect is just a list pointer.
    }

    process = new Liptonize();
    for (CallGraphNode::CallRecord rec : *external) {
        Function *entry = rec.second->getFunction ();
        if (entry->size() == 0) continue; // library function
        if (T->find(entry) == T->end()) continue; // not a thread

        outs() << "Liptonizing "<< entry->getName() <<"\n";
        walkGraph ( *CG[entry] );
    }
    return true;
}

} // VVT































