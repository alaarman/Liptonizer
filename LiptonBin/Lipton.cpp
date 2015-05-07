
#include "llvm/LiptonPass.h"
#include "llvm/ReachPass.h"
#include "llvm/Util.h"
#include "util/Util.h"

#include <iostream>
#include <string>

#include <Andersen.h>
#include <AndersenAA.h>
//#include <llvm/LinkAllPasses.h>
#include <llvm/Pass.h>
#include <llvm/PassSupport.h>
#include <llvm/PassManager.h>
#include <llvm/InitializePasses.h>
#include <llvm/PassRegistry.h>
#include <llvm/PassAnalysisSupport.h>
#include <llvm/Analysis/CallGraph.h>
#include <llvm/Support/CodeGen.h>
#include <llvm/Analysis/AliasAnalysis.h>
#include <llvm/Analysis/AliasSetTracker.h>
#include <llvm/Analysis/Passes.h>
#include <llvm/Bitcode/ReaderWriter.h>
#include <llvm/IR/DataLayout.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Verifier.h>
#include <llvm/IRReader/IRReader.h>
#include <llvm/Support/ErrorOr.h>
#include <llvm/Support/FileSystem.h>
#include <llvm/Support/MemoryBuffer.h>
#include <llvm/Support/SourceMgr.h>
#include <llvm/Support/raw_ostream.h>
#include <llvm/Transforms/Scalar.h>
//#include <llvm/Transforms/IPO/PassManagerBuilder.h>

using namespace llvm;
using namespace std;
using namespace VVT;

struct X : PassRegistrationListener {
    void passRegistered(const PassInfo *pi) {
        cerr << pi->getPassName()<< "R,"<< endl;
    }

    void passEnumerate(const PassInfo *pi) {
        cerr << pi->getPassName()<< ","<< endl;
    }
};

int
main( int argc, const char* argv[] )
{
    ASSERT (argc >= 2, "Require an argument. Pass a .ll or .bc file (argc = "<< argc <<").\n");

    string ll(argv[argc - 1]);
    Module *M;
    LLVMContext &context = getGlobalContext();
    if (ends_with(ll, ".bc")) {
        ErrorOr<unique_ptr<MemoryBuffer>> buf_ptr_ptr = MemoryBuffer::getFileOrSTDIN(ll);
        if (!buf_ptr_ptr) {
            cout << "Failed reading " << ll << ". Error: "<<buf_ptr_ptr.getError() << endl;
            return 1;
        }
        unique_ptr<MemoryBuffer> &bufptr = *buf_ptr_ptr;
        ErrorOr<Module*> mod = parseBitcodeFile(bufptr.get(), context);
        if (!mod) {
            cout << argv[0] << mod.getError();
            return 1;
        }
        M = mod.get();
    } else if (ends_with(ll, ".ll")) {
        SMDiagnostic err;
        M = ParseIRFile(ll, err, context);
        if (!M) {
          err.print(argv[0], errs());
          return 1;
        }
    } else {
        cout << "Could not open file '"<< ll <<"'. Wrong extension.\n";
        exit(1);
    }

    bool staticBlocks = false;
    bool verbose = false;
    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "-v") == 0) {
            verbose = true;
        }
        if (strcmp(argv[i], "-s") == 0) {
            staticBlocks = true;
        }
    }

    Function *main = M->getFunction("main");
    ASSERT (main, "No 'main' function. Library?\n");

    //initializeTypeBasedAliasAnalysisPass(*R);
    //Pass *indvars = createIndVarSimplifyPass();
    //Pass *lur = createLoopUnrollPass(); // from the planet ...
    //initializeScalarEvolutionAliasAnalysisPass(*R);

    PassRegistry *R = PassRegistry::getPassRegistry();
    //initializeIndVarSimplifyPass(*R);
    //initializeTypeBasedAliasAnalysisPass(*R);
    X L;
    R->enumerateWith(&L);

    PassManager pm;

//    PassManagerBuilder pmb;
//    pmb.OptLevel=0;
//    pmb.populateModulePassManager(pm);

    //Pass *aa1 = createAAEvalPass();
    //Pass *aa2 = createBasicAliasAnalysisPass();
    //Pass *aa3 = createTypeBasedAliasAnalysisPass();
    //Pass *aa4 = createObjCARCAliasAnalysisPass();
    //Pass *aa5 = createGlobalsModRefPass();
    //Pass *aac = createAliasAnalysisCounterPass();
    Pass *ba = createBasicAliasAnalysisPass();
    Pass *aae = createAAEvalPass();
    Pass *dlp = new DataLayoutPass(M);
    Pass *aaa = new AndersenAA();
    CallGraphWrapperPass *cfgpass = new CallGraphWrapperPass();
    ReachPass *reach = new ReachPass();

    string name(ll, 0 , ll.size() - 3);
    LiptonPass *lipton = new LiptonPass(*reach, name, verbose, staticBlocks);

    //pm.add (indvars);
    //pm.add (lur);
    pm.add (cfgpass);
    pm.add (reach);
    pm.add (dlp);
    if (staticBlocks)
        pm.add (ba);
    else
        pm.add (aaa);
    if (verbose)
        pm.add (aae);
    pm.add (lipton);

    pm.run (*M);

    if (verbose) reach->printClosure();

    // verify
    verifyModule (*M, &errs());

    size_t last = name.rfind('/');
    // write out
    string n(&name[last + 1]);
    n.append("-lipton.ll");
    const char* data = n.data ();
    std::string error = string ("ERROR");
    raw_fd_ostream file(data, error, sys::fs::OpenFlags::F_Text);

    file << *M << "\n";

    //errs() << dynamic_cast<Pass*>(&lipton->getAnalysis<AliasAnalysis> ())->getPassName() << endll;

    string n2(&name[last + 1]);
    n2.append("-lipton.bc");
    const char* data2 = n2.data ();
    raw_fd_ostream file2(data2, error, sys::fs::OpenFlags::F_RW);

    WriteBitcodeToFile(M, file2);
}
