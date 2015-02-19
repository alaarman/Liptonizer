

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




namespace {

class BitMatrix {
    vector<char *> content;
    int X,Y;

public:
    BitMatrix(int init_x, int init_y) {
        X = init_x;
        Y = init_y;
        int x = (init_x + 7) >> 3;
        for (int i = 0; i < Y; i++) {
            char* c = (char*)(calloc (x, 1));
            content.push_back (c); // initialized to 0
        }
    }

    inline bool set (int x, int y) {
        assert (x < X && y < Y);

        int xl = x & 7;
        int xh = x >> 3;
        char *c = content[y];
        int res = c[xh] & (1 << xl);
        content[y][xh] |= (1 << xl);
        return res != 0;
    }

    inline bool get (int x, int y) {
        assert (x < X && y < Y);

        int xl = x & 7;
        int xh = x >> 3;
        int res = content[y][xh] & (1<<xl);
        return res != 0;
    }

    void grow (int x, int y) {
        assert (x > X && y > Y);
        int xb = (x + 7) >> 3;

        for (int i = 0; i < Y; i++) {
            char *m = content[i];
            content[i] = (char *)calloc(xb, 1); // initialized to 0
            int Xb = (X + 7) >> 3;
            memcpy(content[i], m, Xb);
            delete m;
        }
        for (int i = Y; i < y; i++) {
            char* c = (char*)(calloc (xb, 1));
            content.push_back (c); // initialized to 0
        }

        X = x;
        Y = y;
    }

    void print () {
        for (int i = 0; i < Y; i++) {
            for (int j = 0; j < X; j++) {
                outs() << (get(j, i) ? "1," : "0,");
            }
            outs() << "\n";
        }
        outs() << "\n\n";
    }
};

struct Reach : public CallGraphSCCPass {

public:
    typedef DenseMap<Instruction *, int> IndexMapT;
    typedef pair<Instruction *, int> IndexKVT;

    Reach() : CallGraphSCCPass(ID), reach(0,0) { }

    static char ID;

    void pouts() {
        reach.print();
    }

private:
    IndexMapT indices;
    int indicesIndex = 0;
    BitMatrix reach;

    //DenseSet<const Function *> functions;

    bool runOnSCC(CallGraphSCC &SCC);

    // getAnalysisUsage - This pass requires the CallGraph.
    virtual void getAnalysisUsage(AnalysisUsage &AU) const {
        AU.setPreservesAll();
        AU.addRequired<CallGraphWrapperPass>();
    }

    void addInstruction (Instruction& I);
    Function* printNode (CallGraphNode* const node, CallGraphSCC& SCC);
};
}


char Reach::ID = 0;
static RegisterPass<Reach> X("reach", "Walk CFG");

void
Reach::addInstruction (Instruction& I)
{
    if (!indices.insert (IndexKVT (&I, indicesIndex++)).second) {
        outs () << "Instruction added twice: " << I;
        exit (1);
    }
}

void
Reach::printNode (CallGraphNode* const node, CallGraphSCC& SCC)
{
    Function* F = node->getFunction ();
    if (SCC.size () > 1) {
        outs () << "Mutual recursion nor supported: " << get_name (F);
        exit (1);
    }
    outs () << get_name (F) << " calls: ";
    for (CallGraphNode::CallRecord rec : *node) {
        Function* callee = rec.second->getFunction ();
        outs () << get_name (callee) << ", ";
        if (get_name (callee) == get_name (F)) {
            outs () << "Mutual recursion nor supported: " << get_name (F);
            exit (1);
        }
    }
    errs () << "\n";
}

bool
Reach::runOnSCC(CallGraphSCC &SCC)
{
    CallGraph &CG = getAnalysis<CallGraphWrapperPass>().getCallGraph();
    //Module & m = CG.getModule();
    int sccNum = 0;

    if (SCC.size() == 0) return true;

    CallGraphNode* const node = *(SCC.begin());
    printNode (node, SCC);

    Function* F = node->getFunction ();
    if (!F || F->getBasicBlockList().empty()) return true;

    errs() << "SCCs for Function " << F->getName() << " in PostOrder:";
    for (scc_iterator<Function*> SCCI = scc_begin(F); !SCCI.isAtEnd(); ++SCCI) {
        const std::vector<BasicBlock *> &nextSCC = *SCCI;
        errs() << "\nSCC #" << ++sccNum << " : ";

        int index_pre = indicesIndex;
        for (BasicBlock *bb : nextSCC) {
            errs() << bb->getName() << ", ";
            for (Instruction &I : *bb) {
                errs() << I.getName() << ", ";
                addInstruction (I);
            }
        }

        reach.grow(indicesIndex, indicesIndex);
        // All instructions in an SCC block have equivalent reachability
        // properties (Observation 2 in Purdom's Transitive Closure paper).
        for (int i = index_pre; i < indicesIndex; i++) {
            for (int j = index_pre; j < indicesIndex; j++) {
                reach.set(i, j);
            }
        }

        if (nextSCC.size() == 1 && SCCI.hasLoop()) {
            errs() << " (Has self-loop).";
        }
    }

    for (CallGraphNode::CallRecord rec : *node) {
        Function* callee = rec.second->getFunction ();
        CallGraphNode *calleeNode = CG[callee];
    }

    return true;
}

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
