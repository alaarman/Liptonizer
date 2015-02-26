
#include <assert.h>
#include <iostream>
#include <string>

#include <llvm/IR/Module.h>
#include <llvm/IR/BasicBlock.h>
#include <llvm/IR/Function.h>
#include <llvm/Support/raw_ostream.h>

#include <llvm/ADT/SCCIterator.h>
#include <llvm/ADT/GraphTraits.h>
#include <llvm/Analysis/CFG.h>

#include <llvm/ADT/DenseMap.h>


#include "../util/BitMatrix.h"
#include "../util/Util.h"

#include "ReachPass.h"

using namespace llvm;
using namespace std;


static inline string
get_name(Function const *f)
{
    return f ? f->getName() : "external node";
}

namespace VVT {

char ReachPass::ID = 0;
static RegisterPass<ReachPass> X("reach", "Walk CFG");

void
ReachPass::addInstruction (SCCX<BasicBlock> *scc, Instruction *I)
{
    pair<Instruction *, SCCX<BasicBlock> *> makePair = make_pair (I, scc);
    if (!instructionMap.insert (makePair).second) {
        outs () << "Instruction added twice: " << I;
        exit (1);
    }
}

bool
ReachPass::runOnSCC(CallGraphSCC &SCC)
{
    //CallGraph &CG = getAnalysis<CallGraphWrapperPass>().getCallGraph();
    //Module & m = CG.getModule();

    if (SCC.size() == 0) return true;

    // SCC iterator (on function level)
    // Because we do not allow mutual recursion, this should be a tree of
    // trivial SCCs (loopless singleton SCCs)
    CallGraphNode* const node = *(SCC.begin());
    printNode (node, SCC);

    Function *F = node->getFunction ();
    if (!F || F->getBasicBlockList().empty()) return true;


    // SCC iterator (on block level) within function F
    for (scc_iterator<Function*> blocks = scc_begin(F); !blocks.isAtEnd(); ++blocks) {

        for (BasicBlock *bb : *blocks) {
            // All instructions in an SCC block have equivalent reachability
            // properties (Observation 2 in Purdom's Transitive Closure paper).
            SCCX<BasicBlock> *nSCC = blockQuotient.addBlock(bb, bb->size() > 1 || blocks.hasLoop());

            for (Instruction &I : *bb) {
                addInstruction(nSCC, &I);
            }
        }
    }

    // All SCCs below have been processed before and have unchanging reachability
    // properties (Observation 1 in Purdom's Transitive Closure paper).
    if (node->size() > 0)
    for (CallGraphNode::CallRecord rec : *node) {
        Function* callee = rec.second->getFunction ();
        if (callee->size() == 0) continue; //external library function
        BasicBlock &callee_block = callee->getEntryBlock();

        WeakVH first = rec.first;
        llvm::Value &valPtr = *first;

        Instruction *call_inst = dyn_cast<Instruction> (&valPtr);
        assert (call_inst != nullptr);
        BasicBlock *caller_block = call_inst->getParent();

        SCCX<BasicBlock> *callee_scc = blockQuotient[&callee_block];
        SCCX<BasicBlock> *caller_scc = blockQuotient[caller_block];
        blockQuotient.addLink (caller_scc, callee_scc);
    }

    // SCC iterator (on block level) within function F
    for (scc_iterator<Function*> blocks = scc_begin(F); !blocks.isAtEnd(); ++blocks) {

        // All SCCs below have been processed before and have unchanging reachability
        // properties (Observation 1 in Purdom's Transitive Closure paper).
        for (BasicBlock *bb : *blocks) {
            SCCX<BasicBlock> *bb_scc = blockQuotient[bb];
            for (int i = 0, num = bb->getTerminator()->getNumSuccessors(); i < num; ++i) {
                BasicBlock *succ = bb->getTerminator()->getSuccessor(i);
                SCCX<BasicBlock> *succ_scc = blockQuotient[succ];
                if (succ == bb) {
                    assert (bb_scc->loops);
                    continue;
                }

                blockQuotient.addLink (bb_scc, succ_scc);
            }
        }
    }

    return true;
}

void
ReachPass::printNode (CallGraphNode* const node, CallGraphSCC& SCC)
{
    Function* F = node->getFunction ();
    if (SCC.size () > 1) {
        outs () << "Mutual recursion not supported: " << get_name (F);
        exit (1);
    }
    outs () << get_name (F) << " calls: ";
    for (CallGraphNode::CallRecord rec : *node) {
        Function* callee = rec.second->getFunction ();
        outs () << get_name (callee) << ", ";
        if (get_name (callee) == get_name (F)) {
            outs () << "Mutual recursion not supported: " << get_name (F);
            exit (1);
        }
    }
    errs () << "\n";

    if (!F || F->getBasicBlockList().empty()) return;
    errs() << "SCCs for Function " <<  get_name (F) << " in PostOrder:";
    for (scc_iterator<Function *> SCCI = scc_begin(F); !SCCI.isAtEnd(); ++SCCI) {
        const std::vector<BasicBlock *> &nextSCC = *SCCI;
        errs() << "\nSCC #" << ++sccNum << " : ";

        for (BasicBlock *bb : nextSCC) {
            errs() << bb->getName() << ", ";
            for (Instruction &I : *bb) {
                errs() << I.getName() << ", ";
            }
        }

        if (nextSCC.size() == 1 && SCCI.hasLoop()) {
            errs() << " (Has self-loop).";
        }
    }
    errs () << "\n";
}

}

