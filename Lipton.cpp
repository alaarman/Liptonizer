
#include "llvm/LiptonPass.h"
#include "llvm/ReachPass.h"
#include "llvm/Util.h"
#include "util/Util.h"

#include <iostream>
#include <string>

#include <AndersenAA.h>
//#include <llvm/LinkAllPasses.h>
#include <llvm/Pass.h>
#include <llvm/PassSupport.h>
#include <llvm/PassManager.h>
#include <llvm/InitializePasses.h>
#include <llvm/PassRegistry.h>
#include <llvm/PassAnalysisSupport.h>
//#include <llvm/Analysis/AndersenPass.h>
#include <llvm/Analysis/CallGraph.h>
#include <llvm/Support/CodeGen.h>
#include <llvm/Analysis/AliasAnalysis.h>
#include <llvm/Analysis/AliasSetTracker.h>
#include <llvm/Analysis/Passes.h>
#include <llvm/Bitcode/ReaderWriter.h>
#include <llvm/IR/DataLayout.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/LLVMContext.h>
//#include <llvm/IR/PassManager.h>
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

static void
usage (const char *name)
{
    cerr << "" << name <<" [-v] [-n] [-s] < [in.bc] > [out.bc]" << endl;
    cerr << endl;
    cerr << "\t\t\t\t| phase var.\t| dyn. com.\t|"<< endl;
    cerr << "-------------------------------------------------------------"<< endl;
    cerr << "\t\t|\tnormal\t|\t+\t|\t+\t|"<< endl;
    cerr << "\t-n\t|\tno dyn\t|\t+\t|\t-\t|"<< endl;
    cerr << "\t-s\t|\tstatic\t|\t-\t|\t-\t|"<< endl;
    cerr << endl;
    cerr << "Select -l to disable static locked region identification" << endl;
    cerr << "(reductions as in Transactions for Software Model Checking by Qadeer/Flanagan)." << endll;
    cerr << "Select -y to insert local yields after each statement." << endl;
    cerr << endl;
    cerr << "Select one of -n and -s (either no dynamic commutativity or static blocks)." << endl;
    cerr << endl;
    exit (-1);
}

int
main( int argc, const char *argv[] )
{
    Module *M;
    LLVMContext &context = getGlobalContext();

    Options o;
    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "-v") == 0) {
            o.verbose = true;
        } else if (strcmp(argv[i], "-d") == 0) {
            o.debug = true;
        } else if (strcmp(argv[i], "-y") == 0) {
            o.allYield = true;
        } else if (strcmp(argv[i], "-s") == 0) {
            o.staticAll = true;
        } else if (strcmp(argv[i], "-n") == 0) {
            o.nodyn = true;
        } else if (strcmp(argv[i], "-l") == 0) {
            o.nolock = true;
        } else {
            usage (argv[0]);
        }
    }
    if ( o.nodyn && o.staticAll ) {
        usage (argv[0]);
    }

    ErrorOr<unique_ptr<MemoryBuffer>> buf_ptr_ptr = MemoryBuffer::getSTDIN();
    if (!buf_ptr_ptr) {
      cerr << "Failed reading LLVM code. Error: "<<buf_ptr_ptr.getError() << endl;
      return 1;
    }
    unique_ptr<MemoryBuffer> &bufptr = *buf_ptr_ptr;
    ErrorOr<Module*> mod = parseBitcodeFile(bufptr.get(), context);
    if (!mod) {
      cerr << argv[0] << mod.getError();
      return 1;
    }
    M = mod.get();

    Function *main = M->getFunction("main");
    ASSERT (main, "No 'main' function. Library?\n");

    //Pass *indvars = createIndVarSimplifyPass();
    //Pass *lur = createLoopUnrollPass(); // from the planet ...
    //initializeScalarEvolutionAliasAnalysisPass(*R);

    //PassRegistry *R = PassRegistry::getPassRegistry();
    //initializeIndVarSimplifyPass(*R);
    //initializeTypeBasedAliasAnalysisPass(*R);
    //initializeTypeBasedAliasAnalysisPass(*R);
    X L;
    //R->enumerateWith(&L);
    //R->addRegistrationListener(&L);
    //errs() <<" -------------- " <<endll;

    PassManager pm;

//    PassManagerBuilder pmb;
//    pmb.OptLevel=0;
//    pmb.populateModulePassManager(pm);

    //Pass *aa1 = createAAEvalPass();
    //Pass *aa2 = createBasicAliasAnalysisPass();
    Pass *tbaa = createTypeBasedAliasAnalysisPass();
    //Pass *aa4 = createObjCARCAliasAnalysisPass();
    //Pass *aa5 = createGlobalsModRefPass();
    //Pass *aaa = new AndersenPass();
    Pass *aaa = new AndersenAA();
    Pass *aac = createAliasAnalysisCounterPass();
    //Pass *ba = createBasicAliasAnalysisPass();
    Pass *aae = createAAEvalPass();
    Pass *dlp = new DataLayoutPass(M);
    CallGraphWrapperPass *cfgpass = new CallGraphWrapperPass();
    //ReachPass *reach = new ReachPass();

    LiptonPass *lipton = new LiptonPass("stdin", o);


    //pm.add (indvars);
    //pm.add (lur);
    pm.add (dlp);
    pm.add (tbaa);
    pm.add (aaa);
    pm.add (cfgpass);
    //pm.add (reach);
    if (o.verbose) {
        pm.add (aac);
        pm.add (aae);
    }
    //}
    pm.add (lipton);

    //errs() <<" -------------- " <<endll;
    //R->enumerateWith(&L);
    pm.run (*M);

    //if (o.verbose) reach->printClosure();

    // verify
    verifyModule (*M, &errs());

#undef outs // util/util.h
    WriteBitcodeToFile(M, outs());
    outs().flush();
}
