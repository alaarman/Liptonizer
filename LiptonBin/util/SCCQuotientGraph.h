/**
 * SCC Quotiont graph
 *
 * Nodes and arcs can be added simultaneously, as long as the links are
 * added in post-order (keeping the complexity down by a linear factor).
 */

#ifndef LIPTONBIN_UTIL_SCCQUOTIENTGRAPH_H_
#define LIPTONBIN_UTIL_SCCQUOTIENTGRAPH_H_


#include "util/BitMatrix.h"

#include <vector>

#include <llvm/ADT/DenseMap.h>


using namespace llvm;

namespace VVT {


struct SCCI {
    SCCI(int i, bool l) :
        index(i),
        loops(l)
    { };

    int             index;
    bool            loops;
};

template<typename T>
class SCCQuotientGraph {

private:
    DenseMap<T *, SCCI *> blockMap;
    vector<T *> objects;
    BitMatrix reach;
    BitVector locked;

    SCCI *createSCC (T *t, bool loops);

public:
    SCCQuotientGraph() :
        reach(1,1)
    { }

    SCCI *operator[] (T *bb);
    T    *operator[] (SCCI *scc);
    T    *operator[] (int index);

    void link (SCCI *x, SCCI *y);
    void link (T *x, T *y);
    void link (T *x, SCCI *y);
    SCCI *add (T *t, bool loops);
    void print();
};

}

#endif /* LIPTONBIN_UTIL_SCCQUOTIENTGRAPH_H_ */
