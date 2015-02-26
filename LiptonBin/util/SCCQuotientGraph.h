#ifndef LIPTONBIN_UTIL_SCCQUOTIENTGRAPH_H_
#define LIPTONBIN_UTIL_SCCQUOTIENTGRAPH_H_

#include <llvm/ADT/DenseMap.h>

#include "util/BitMatrix.h"

using namespace llvm;

namespace VVT {


template<typename T>
struct SCCX {
    SCCX(int i, bool l) :
        index(i),
        loops(l) {};

    int             index;
    bool            loops;
    T              *bb = NULL;
};

template<typename T>
class SCCQuotientGraph {

public:
    typedef SCCX<T> SCCI;

private:
    DenseMap<T *, SCCI *> blockMap;
    int indicesIndex = 0;
    BitMatrix reach;
    BitVector locked;

public:
    SCCQuotientGraph() :
        reach(1,1)
    { }

    SCCI *operator[] (T *bb);

    void addLink (SCCI *x, SCCI *y);
    void addLink (T *x, T *y);
    void addLink (T *x, SCCI *y);
    SCCI *addSCC (bool loops);
    SCCI *addBlock (T *I, bool loops);
    void print();
};

}

#endif /* LIPTONBIN_UTIL_SCCQUOTIENTGRAPH_H_ */
