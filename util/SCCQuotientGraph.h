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
#include <iterator>

#include <llvm/ADT/DenseMap.h>



namespace VVT {

template<typename T>
struct SCCI  {
    SCCI(int i, bool l) :
        index(i),
        nontrivial(l)
    { };
    int             index;
    bool            nontrivial;
    vector<T *>     elems;
    SCCI<T>        *parent = NULL;

//    union SCCContent {
//        T           *elem = NULL;
//    };
//    SCCContent      content;
//
//    void add(T *t) {
//        if (size == 0) {
//            content.elem = t;
//        } else {
//            content.elems = new vector<T>(2, content.elem);
//            content.elems[1] = t;
//            content.elem = NULL;
//        }
//        size++;
//    }
//
//    void *
//    begin()
//    {
//        return elems.begin();
//    }
//
//    iterator
//    end()
//    {
//        return content.elems->end();
//    }

};


template<typename T>
class SCCQuotientGraph {

private:
    llvm::DenseMap<T *, SCCI<T> *> blockMap;
    BitMatrix reach;
    BitVector locked;
    unsigned size = 0;

public:
    SCCQuotientGraph() :
        reach(1,1)
    { }

    SCCI<T>    *operator[] (T *bb);

    SCCI<T>    *createSCC (bool nontrivial);
    void        add (SCCI<T> *scc, T *t);       // add (non-SCC) sequences (one by one)
    void        addSCC (SCCI<T> *scc, T *t);    // add SCC sets (one by one)
    //SCCI<T>    *add (T *t, bool nontrivial);
    void        link (SCCI<T> *x, SCCI<T> *y);
    void        link (T *x, T *y);
    void        link (T *x, SCCI<T> *y);
    void        print();

    bool        stCon (SCCI<T>  *S, SCCI<T>  *TT);
    bool        stCon (T *S, T *TT);
};

}

#endif /* LIPTONBIN_UTIL_SCCQUOTIENTGRAPH_H_ */
