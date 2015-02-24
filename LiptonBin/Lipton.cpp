

#include <assert.h>
#include <iostream>
#include <string>

//#include <llvm-c/Core.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/BasicBlock.h>
#include <llvm/Pass.h>
#include <llvm/PassRegistry.h>
#include <llvm/IR/Function.h>
#include <llvm/Support/raw_ostream.h>
#include <llvm/Support/ErrorOr.h>
#include <llvm/Support/MemoryBuffer.h>
#include <llvm/IRReader/IRReader.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/Bitcode/ReaderWriter.h>
#include <llvm/IRReader/IRReader.h>
#include <llvm/Support/SourceMgr.h>
//#include <llvm-c/Support.h>
//#include <llvm-c/BitReader.h>

#include <llvm/ADT/SCCIterator.h>
#include <llvm/ADT/GraphTraits.h>
#include <llvm/Analysis/CallGraph.h>
#include <llvm/Analysis/CallGraphSCCPass.h>
#include <llvm/Analysis/CFGPrinter.h>
#include <llvm/Analysis/CFG.h>
#include <llvm/Analysis/DependenceAnalysis.h>


#include <llvm/ADT/DenseMap.h>
#include <llvm/ADT/DenseSet.h>

#include <llvm/PassManager.h>

using namespace llvm;
using namespace std;

static inline bool
ends_with(string const & value, string const & ending)
{
    if (ending.size() > value.size()) return false;
    return equal(ending.rbegin(), ending.rend(), value.rbegin());
}

static inline string
get_name(Function const *f)
{
    return f ? f->getName() : "external node";
}

namespace VVT {

class BitMatrix {
    vector<char *> rows;
    int C,R;

public:
    BitMatrix(int init_cols, int init_rows) {
        C = init_cols;
        R = init_rows;
        int x = (init_cols + 7) >> 3;
        for (int row = 0; row < R; row++) {
            char* c = (char*)(calloc (x, 1));
            rows.push_back (c); // initialized to 0
        }
    }

    inline void copy (int row_to, int row) {
        assert (row_to < R && row < R);
        assert (row_to != row);
        int col_size = (R + 7) >> 3;
        for (int col_high = 0; col_high < col_size; col_high++) {
            rows[row_to][col_high] |= rows[row][col_high];
        }
    }

    inline bool set (int col, int row) {
        assert (col < C && row < R);

        int col_low = col & 7;
        int col_high = col >> 3;
        int res = rows[row][col_high] & (1 << col_low);
        rows[row][col_high] |= (1 << col_low);
        return res != 0;
    }

    inline bool get (int col, int row) {
        assert (col < C && row < R);

        int col_low = col & 7;
        int col_high = col >> 3;
        int res = rows[row][col_high] & (1<<col_low);
        return res != 0;
    }

    void grow (int new_cols, int new_rows) {
        assert (new_cols > C && new_rows > R);
        int col_size = (new_cols + 7) >> 3;

        for (int i = 0; i < R; i++) {
            char *m = rows[i];
            rows[i] = (char *)calloc(col_size, 1); // initialized to 0
            int Xb = (C + 7) >> 3;
            memcpy(rows[i], m, Xb);
            delete m;
        }
        for (int i = R; i < new_rows; i++) {
            char* c = (char*)(calloc (col_size, 1));
            rows.push_back (c); // initialized to 0
        }

        C = new_cols;
        R = new_rows;
    }

    void print () {
        for (int row = 0; row < R; row++) {
            for (int col = 0; col < C; col++) {
                outs() << (get(col, row) ? "1," : "0,");
            }
            outs() << "\n";
        }
        outs() << "\n\n";
    }
};

struct SCCI {
    SCCI(int i, bool l) :
        index(i),
        loops(l) {};

    int     index;
    bool    loops;
};


struct Reach : public CallGraphSCCPass {

public:
    DenseMap<Instruction *, SCCI *> instructionMap;
    DenseMap<BasicBlock *, SCCI *> blockMap;

    Reach() : CallGraphSCCPass(ID), reach(0,0) { }

    static char ID;

    void pouts() {
        reach.print();
    }

private:
    int indicesIndex = 0;
    BitMatrix reach;
    int sccNum = 0;

    //DenseSet<const Function *> functions;

    bool runOnSCC(CallGraphSCC &SCC);

    // getAnalysisUsage - This pass requires the CallGraph.
    virtual void getAnalysisUsage(AnalysisUsage &AU) const {
        AU.setPreservesAll();
        AU.addRequired<CallGraphWrapperPass>();
    }

    void printNode (CallGraphNode* const node, CallGraphSCC& SCC);

    SCCI *addSCC (bool loops);
    void addInstruction (SCCI *scc, Instruction& I);
    void addBlock (SCCI *scc, BasicBlock *I);
};


char Reach::ID = 0;
static RegisterPass<Reach> X("reach", "Walk CFG");

void
Reach::addBlock (SCCI *scc, BasicBlock *bb)
{
    if (!blockMap.insert( make_pair(bb, scc) ).second) {
        outs () << "Instruction added twice: " << *bb;
        exit (1);
    }
}

void
Reach::addInstruction (SCCI *scc, Instruction& I)
{
    if (!instructionMap.insert( make_pair(&I, scc) ).second) {
        outs () << "Instruction added twice: " << I;
        exit (1);
    }
}

SCCI *
Reach::addSCC (bool loops)
{
    SCCI *scci = new SCCI (indicesIndex++, loops);
    reach.grow(indicesIndex, indicesIndex);
    if (loops)
        reach.set (scci->index, scci->index); // reflexive reachability properties
    return scci;
}

void
Reach::printNode (CallGraphNode* const node, CallGraphSCC& SCC)
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

bool
Reach::runOnSCC(CallGraphSCC &SCC)
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
            SCCI *nSCC = addSCC((*blocks).size () > 1 || blocks.hasLoop ());

            addBlock(nSCC, bb);
            for (Instruction &I : *bb) {
                addInstruction(nSCC, I);
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

        SCCI *callee_scc = blockMap[&callee_block];
        SCCI *caller_scc = blockMap[caller_block];
        reach.set (caller_scc->index, callee_scc->index);
        reach.copy (caller_scc->index, callee_scc->index);
    }

    // SCC iterator (on block level) within function F
    for (scc_iterator<Function*> blocks = scc_begin(F); !blocks.isAtEnd(); ++blocks) {

        // All SCCs below have been processed before and have unchanging reachability
        // properties (Observation 1 in Purdom's Transitive Closure paper).
        for (BasicBlock *bb : *blocks) {
            SCCI *bb_scc = blockMap[bb];
            for (int i = 0, num = bb->getTerminator()->getNumSuccessors(); i < num; ++i) {
                BasicBlock *succ = bb->getTerminator()->getSuccessor(i);
                SCCI *succ_scc = blockMap[succ];
                if (succ == bb) {
                    assert (bb_scc->loops);
                    continue;
                }

                reach.set (bb_scc->index, succ_scc->index);
                reach.copy (bb_scc->index, succ_scc->index);
            }
        }
    }


    return true;
}
}

using namespace VVT;

int
main( int argc, const char* argv[] )
{
    if (argc != 2) {
        cout << "Require an argument. Pass a .ll or .bc file (argc = "<< argc <<").\n" ;
        exit(1);
    }

    string ll(argv[1]);
    Module *m;
    LLVMContext &context = getGlobalContext();
    if (ends_with(ll, ".bc")) {
        ErrorOr<unique_ptr<MemoryBuffer>>  buf = MemoryBuffer::getFileOrSTDIN(ll);
        ErrorOr<Module*> mod = parseBitcodeFile(buf->get(), context);
        if (!mod) {
            cout << argv[0] << mod.getError();
            return 1;
        }
        m = mod.get();
    } else if (ends_with(ll, ".ll")) {
        SMDiagnostic err;
        m = ParseIRFile(ll, err, context);
        if (!m) {
          err.print(argv[0], errs());
          return 1;
        }
    } else {
        cout << "Could not open file '"<< ll <<"'. Wrong extension.\n";
        exit(1);
    }

    //for (Function &f : m->getFunctionList()) {
        //cout << string(f.getName()) <<"\n";
    //}

    Function *main = m->getFunction("main");
    if (!main) {
        cout << "No 'main' function. Library?\n";
        exit(1);
    }

    PassManager PM;
    llvm::CallGraphWrapperPass* cfgpass = new CallGraphWrapperPass ();
    Reach* reach = new Reach ();
    PM.add (cfgpass);
    PM.add (reach);
    PM.run (*m);

    reach->pouts();

//    CallGraph &cfg = cfgpass->getCallGraph();

}

