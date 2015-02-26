
#include "llvm/ReachPass.h"
#include "util/Util.h"

#include <iostream>
#include <string>

#include <llvm/PassManager.h>
#include <llvm/Analysis/CallGraph.h>
#include <llvm/Bitcode/ReaderWriter.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IRReader/IRReader.h>
#include <llvm/Support/ErrorOr.h>
#include <llvm/Support/MemoryBuffer.h>
#include <llvm/Support/SourceMgr.h>
#include <llvm/Support/raw_ostream.h>

using namespace llvm;
using namespace std;
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

    Function *main = m->getFunction("main");
    ASSERT (main, "No 'main' function. Library?\n");

    PassManager pm;
    CallGraphWrapperPass *cfgpass = new CallGraphWrapperPass();
    ReachPass *reach = new ReachPass();
    pm.add (cfgpass);
    pm.add (reach);
    pm.run (*m);

    reach->printClosure();
    //CallGraph &cfg = cfgpass->getCallGraph();

    //delete reach;
}


