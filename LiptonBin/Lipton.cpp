
#include "llvm/ReachPass.h"
#include "util/Util.h"

#include <iostream>
#include <string>

#include <llvm/LinkAllPasses.h>

#include <llvm/Analysis/Passes.h>

#include <llvm/Pass.h>
#include <llvm/PassRegistry.h>
#include <llvm/PassSupport.h>
#include <llvm/PassManager.h>
#include <llvm/InitializePasses.h>
#include <llvm/PassRegistry.h>
#include <llvm/PassAnalysisSupport.h>
#include <llvm/Analysis/CallGraph.h>
#include <llvm/PassInfo.h>
#include <llvm/Support/CodeGen.h>
#include <llvm/Analysis/AliasAnalysis.h>
#include <llvm/Analysis/AliasSetTracker.h>
#include <llvm/Bitcode/ReaderWriter.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/LegacyPassNameParser.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/Module.h>
#include <llvm/IRReader/IRReader.h>
#include <llvm/Support/ErrorOr.h>
#include <llvm/Support/MemoryBuffer.h>

#include <llvm/Support/SourceMgr.h>
#include <llvm/Support/raw_ostream.h>

using namespace llvm;
using namespace std;
using namespace VVT;

struct X : PassRegistrationListener {
    void passRegistered(const PassInfo *pi) {
        cout << pi->getPassName()<< "R,"<< endl;
    }

    void passEnumerate(const PassInfo *pi) {
        cout << pi->getPassName()<< ","<< endl;
    }
};

int
main( int argc, const char* argv[] )
{
    ASSERT (argc == 2, "Require an argument. Pass a .ll or .bc file (argc = "<< argc <<").\n");

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

    Function *main = m->getFunction("main");
    ASSERT (main, "No 'main' function. Library?\n");

    //initializeTypeBasedAliasAnalysisPass(*R);
    Pass *indvars = createIndVarSimplifyPass();
    Pass *lur = createLoopUnrollPass(); // from the planet ...
    //initializeScalarEvolutionAliasAnalysisPass(*R);

    PassManager pm;
    CallGraphWrapperPass *cfgpass = new CallGraphWrapperPass();
    ReachPass *reach = new ReachPass();
    pm.add (indvars);
    pm.add (lur);
    pm.add (cfgpass);
    pm.add (reach);
    pm.run (*m);

    reach->printClosure();
    //CallGraph &cfg = cfgpass->getCallGraph();

    //delete reach;
}


