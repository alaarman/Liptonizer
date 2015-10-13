
#include "ReachPass.h"

#include "util/BitMatrix.h"
#include "util/Util.h"

#include <algorithm>    // std::sort
#include <assert.h>
#include <iostream>
#include <string>

#include <llvm/Pass.h>
#include <llvm/PassRegistry.h>
#include <llvm/PassSupport.h>
#include <llvm/Analysis/AliasAnalysis.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/BasicBlock.h>
#include <llvm/IR/Function.h>
#include <llvm/Support/raw_ostream.h>

#include <llvm/ADT/SCCIterator.h>
#include <llvm/ADT/GraphTraits.h>
#include <llvm/Analysis/CFG.h>

#include <llvm/ADT/DenseMap.h>
#include <llvm/IR/ValueMap.h>

using namespace llvm;
using namespace std;


static inline string
get_name(Function const *f)
{
    return f ? f->getName() : "external node";
}

namespace VVT {

char ReachPass::ID = 0;
static RegisterPass<ReachPass> X("reach", "Reachability pass");

ReachPass::ReachPass() : CallGraphSCCPass(ID) { }

void
ReachPass::getAnalysisUsage(AnalysisUsage &AU) const {
    AU.setPreservesAll();
    AU.addRequired<CallGraphWrapperPass>();
}

void
ReachPass::addInstruction (unsigned index, Instruction *I)
{
    pair<Instruction *, unsigned> p = make_pair (I, index);
    bool added = instructionMap.insert (p).second;
    if (!added) {
        errs() << "Instruction added twice: " << *I <<"\n";
        assert(false);
    }
}

static Instruction *
getInstr(CallGraphNode::CallRecord &rec)
{
    Value &valPtr = *(rec.first);
    Instruction *I = dyn_cast<Instruction> (&valPtr);
    assert (I != nullptr);
    return I;
}

struct CompareFunctor {
    ReachPass *pass;
    CompareFunctor(ReachPass *pass) : pass(pass) { }

    bool
    operator()(ReachPass::CallT &l, ReachPass::CallT &r)
    {
        unsigned i = pass->instructionMap[l.first];
        unsigned j = pass->instructionMap[r.first];
        return i < j;
    }
};

void
ReachPass::reorder_calls()
{
    for (CallMapET call :  calls) {
        BasicBlock *bb = call.first;
        CallsT &second = call.second;
        sort (second.begin(), second.end(), CompareFunctor(this));
        Function *callee = bb->getTerminator()->getParent()->getParent();
        second.push_back (make_pair(bb->getTerminator(), callee));
    }
}

bool
ReachPass::runOnSCC(CallGraphSCC &SCC)
{
    if (SCC.size() == 0) return true;

    // SCC iterator (on function level)
    // Because we do not allow mutual recursion, this should be a tree of
    // trivial SCCs (loopless singleton SCCs)
    CallGraphNode* const node = *(SCC.begin());
    Function *F = node->getFunction ();
    if (!F || F->getBasicBlockList().empty()) return true;

    checkNode (node, SCC);

    // get instruction subblocks
    if (node->size() > 0)
    for (CallGraphNode::CallRecord rec : *node) {
        Function *callee = rec.second->getFunction ();
        Instruction *callInstr = getInstr (rec);
        if (callee == nullptr) {
            errs() << "XXXXXXXXXXXXXXXXXX" << callInstr;
            continue;
        }
        if (callee->getName() == "__thread_spawn") {
            Function *threadF = dyn_cast<Function> (callInstr->getOperand (1));
            ASSERT (threadF, "Incorrect __thread_spawn argument?");
            //Threads (threadF, callInstr); // add to threads (via functor)
            Threads[threadF].push_back (callInstr);
        }
        if (callee->size() == 0) continue; // library function

        callRecords.insert(make_pair (callInstr, callee));

        BasicBlock *callerBlock = callInstr->getParent ();
        calls[callerBlock].push_back (make_pair (callInstr, callee));
    }
    for (BasicBlock &B : *F) {
        unsigned index = 0;
        for (Instruction &I : B) {
            addInstruction (index++, &I);
        }
    }
    reorder_calls ();

    // SCC iterator (on block level) within function F
    for (scc_iterator<Function*> bSCC = scc_begin(F); !bSCC.isAtEnd(); ++bSCC) {

        SCCI<Instruction> *iq = instrQuotient.createSCC (bSCC.hasLoop());
        SCCI<BasicBlock>  *bq = blockQuotient.createSCC (bSCC.hasLoop());
        for (BasicBlock *bb : *bSCC) {
            // All instructions in an SCC block have equivalent reachability
            // properties (Observation 2 in Purdom's Transitive Closure paper).
            blockQuotient.addSCC (bq, bb);

            CallsT &instrs = calls[bb];
            if (bSCC.hasLoop() || instrs.size() == 0) {
                for (Instruction &I : *bb) {
                    instrQuotient.add (iq, &I);
                }
            } else {
                int i = 0;
                for (Instruction &I : *bb) {
                    instrQuotient.add (iq, &I);
                    if (i < instrs.size() && &I == instrs[i].first) {
                        i++;
                        SCCI<Instruction> *iq2 = iq;
                        iq = instrQuotient.createSCC (bSCC.hasLoop());
                        iq->parent = iq2;
                    }
                }
            }
        }
    }

    //printNode (node, SCC);

    // SCC iterator (on block level) within function F
    for (scc_iterator<Function *> bSCC = scc_begin(F); !bSCC.isAtEnd(); ++bSCC) {

        // All SCCs below have been processed before and have unchanging reachability
        // properties (Observation 1 in Purdom's Transitive Closure paper).
        for (BasicBlock *bb : *bSCC) {
            SCCI<BasicBlock> *bb_scc = blockQuotient[bb];


            CallsT &instrs = calls[bb];

            // calls
            //if (node->size() > 0)
            for (CallT &rec : instrs) {
                Function *callee = rec.second;
                Instruction *call_inst = rec.first;
                BasicBlock &callee_block = callee->getEntryBlock ();
                BasicBlock *caller_block = call_inst->getParent ();
                SCCI<BasicBlock> *callee_scc = blockQuotient[&callee_block];
                SCCI<BasicBlock> *caller_scc = blockQuotient[caller_block];
                blockQuotient.link (caller_scc, callee_scc);
            }

            for (int i = 0, num = bb->getTerminator()->getNumSuccessors(); i < num; ++i) {
                BasicBlock *succ = bb->getTerminator()->getSuccessor(i);
                SCCI<BasicBlock> *succ_scc = blockQuotient[succ];
                if (succ == bb) {
                    assert (bb_scc->nontrivial);
                    continue;
                }
                blockQuotient.link (bb_scc, succ_scc);
            }
        }
    }

    // SCC iterator (on instruction level) within blocks
    for (scc_iterator<Function *> bSCC = scc_begin(F); !bSCC.isAtEnd(); ++bSCC) {

        // All SCCs below have been processed before and have unchanging reachability
        // properties (Observation 1 in Purdom's Transitive Closure paper).
        for (BasicBlock *bb : *bSCC) {

            CallsT &instrs = calls[bb];

            // calls
            //if (node->size() > 0)
            for (CallT &rec : instrs) {
                Function *callee = rec.second;
                Instruction *call_inst = rec.first;

                // link instructions
                Instruction &entry = callee->getEntryBlock().front();
                instrQuotient.link (instrQuotient[call_inst], instrQuotient[&entry]);
            }

            Instruction *exit = bb->getTerminator();
            SCCI<llvm::Instruction>* last = instrQuotient[exit];
            for (int i = 0, num = bb->getTerminator()->getNumSuccessors(); i < num; ++i) {
                BasicBlock *succ = bb->getTerminator()->getSuccessor(i);
                if (succ == bb) continue;

                Instruction &entry = succ->front ();
                instrQuotient.link (last, instrQuotient[&entry]);
            }

            if (last->parent) {
                instrQuotient.link (last, last->parent);
            }
        }
    }

    return false; // no modification
}

static void printF (pair<Function *, std::vector<Instruction *>> &F) {
    errs () << F.first->getName() <<", ";
}

void
ReachPass::printClosure() {
    blockQuotient.print ();

    for_each (Threads.begin(), Threads.end(), printF);
    errs ()  << "\n";

    instrQuotient.print ();
}

bool
ReachPass::doFinalization(CallGraph &CG)
{
    Module &m = CG.getModule();
    Function *main = m.getFunction("main");
    ASSERT (main, "No main function in module");
    Threads[main].push_back((Instruction *)NULL);
    return false; // no modification
}

void
ReachPass::checkNode (CallGraphNode* const node, CallGraphSCC& SCC)
{
    Function* F = node->getFunction ();
    string fname = get_name(F);
    ASSERT (SCC.isSingular(), "Mutual recursion not supported: " << fname);

    for (CallGraphNode::CallRecord rec : *node) {
        Function* callee = rec.second->getFunction ();
        ASSERT (get_name(callee) != fname,
                "Mutual recursion not supported: " << fname);
    }
}

bool
ReachPass::stCon (Instruction *S, Instruction *T)
{
    return instrQuotient.stCon(S, T);
}

bool
ReachPass::stCon (BasicBlock *S, BasicBlock *T)
{
    return blockQuotient.stCon(S, T);
}

void
ReachPass::printNode (CallGraphNode* const node, CallGraphSCC& SCC)
{
    Function* F = node->getFunction ();

    errs () << get_name (F) << " calls: ";
    for (CallGraphNode::CallRecord rec : *node) {
        Function* callee = rec.second->getFunction ();
        errs () << get_name (callee) << ", ";
    }
    errs () << "\n";

    if (!F || F->getBasicBlockList().empty()) return;
    errs() << "SCCs for Function " <<  get_name (F) << " in PostOrder:";
    for (scc_iterator<Function *> cg_scc = scc_begin(F); !cg_scc.isAtEnd(); ++cg_scc) {
        const std::vector<BasicBlock *> &nextSCC = *cg_scc;
        errs() << "\nSCC #" << ++sccNum << " : ";

        for (BasicBlock *bb : nextSCC) {
            SCCI<BasicBlock> *scci = blockQuotient[bb];
            errs () << bb->getName () << "(" << scci->index << (scci->nontrivial?"+":"") <<"), ";
//            for (Instruction &I : *bb) {
//                errs() << I.getName() << ", ";
//            }
        }

        if (nextSCC.size() == 1 && cg_scc.hasLoop()) {
            errs() << " (Has self-loop).";
        }
    }
    errs () << "\n";
}

}

