#ifndef LIPTONBIN_UTIL_SCCQUOTIENTGRAPH_H_
#define LIPTONBIN_UTIL_SCCQUOTIENTGRAPH_H_

#include <llvm/IR/BasicBlock.h>

#include <llvm/ADT/DenseMap.h>

#include "BitMatrix.h"

using namespace llvm;

namespace VVT {


struct SCCI {
    SCCI(int i, bool l) :
        index(i),
        loops(l) {};

    int             index;
    bool            loops;
    BasicBlock     *bb = NULL;
};

//template<class T>
class SCCQuotientGraph {

    DenseMap<BasicBlock *, SCCI *> blockMap;
    int indicesIndex = 0;
    BitMatrix reach;
    BitVector locked;

public:
    SCCQuotientGraph() :
        reach(1,1)
    { }


    SCCI *operator[](BasicBlock *bb) {
         return blockMap[bb];
    }

    void addLink (SCCI *x, SCCI *y);
    void addLink (BasicBlock *x, BasicBlock *y);
    void addLink (BasicBlock *x, SCCI *y);
    SCCI *addSCC (bool loops);
    //template<class T>
    SCCI *addBlock (BasicBlock *I, bool loops);
    void print();
};

}

#endif /* LIPTONBIN_UTIL_SCCQUOTIENTGRAPH_H_ */
