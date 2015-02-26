#ifndef LIPTONBIN_UTIL_SCCQUOTIENTGRAPH_H_
#define LIPTONBIN_UTIL_SCCQUOTIENTGRAPH_H_


#include "util/BitMatrix.h"

#include <vector>

#include <llvm/ADT/DenseMap.h>


using namespace llvm;

namespace VVT {


template<typename T>
struct SCCX {
    SCCX(int i, bool l, T *t) :
        index(i),
        loops(l),
        object(t) {};

    int             index;
    bool            loops;
    T              *object;
};

template<typename T>
class SCCQuotientGraph {

public:
    typedef SCCX<T> SCCI;

private:
    DenseMap<T *, SCCI *> blockMap;
    vector<T *> objects;
    //int indicesIndex = 0;
    BitMatrix reach;
    BitVector locked;

    SCCI *createSCC (bool loops, T *t);

public:
    SCCQuotientGraph() :
        reach(1,1)
    { }

    SCCI *operator[] (T *bb);

    void link (SCCI *x, SCCI *y);
    void link (T *x, T *y);
    void link (T *x, SCCI *y);
    SCCI *add (T *t, bool loops);
    void print();
};

}

#endif /* LIPTONBIN_UTIL_SCCQUOTIENTGRAPH_H_ */
