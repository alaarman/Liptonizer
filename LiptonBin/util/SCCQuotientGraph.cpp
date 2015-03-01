#include <assert.h>
#include <iostream>
#include <string>

#include "util/SCCQuotientGraph.h"
#include "util/Util.h"

using namespace std;


namespace VVT {

template<class T>
SCCI<T> *
SCCQuotientGraph<T>::operator[] (T *t) {
     return blockMap[t];
}

template<class T>
void
SCCQuotientGraph<T>::link (SCCI<T> *x, SCCI<T> *y)
{
    if (x == y) {
        ASSERT (reach.get(x->index, y->index), "Non trivial SCC not correctly initialized: "<< x->elems[0]);
        return;
    }
    ASSERT (!locked[x->index], "SCCs not linked in post-order: "<< x << " >< "<< y);

    reach.set  (x->index, y->index);
    reach.copy (x->index, y->index);
    locked[y->index];
}

template<class T>
void
SCCQuotientGraph<T>::link (T *x, T *y)
{
    SCCI<T> *xscc = blockMap[x];
    SCCI<T> *yscc = blockMap[y];
    link(xscc, yscc);
}

template<class T>
void
SCCQuotientGraph<T>::link (T *x, SCCI<T> *y)
{
    SCCI<T> *xscc = blockMap[x];
    link(xscc, y);
}

template<class T>
SCCI<T> *
SCCQuotientGraph<T>::createSCC (bool nontrivial)
{
    SCCI<T> *scci = new SCCI<T> (size++, nontrivial);
//errs () <<  indicesIndex << " << " << scci->index << "\n";
    reach.ensure(size, size);
    locked.ensure(size);
    if (nontrivial)
        reach.set (scci->index, scci->index); // reflexive reachability properties
    return scci;
}

template<class T>
void
SCCQuotientGraph<T>::add (SCCI<T> *scc, T *t, bool nontrivial)
{
    scc->elems.push_back (t);

    pair<T *, SCCI<T> *> p = make_pair (t, scc);
    bool seen = blockMap.insert( p ).second;
    ASSERT (seen, "Instruction added twice: " << t);
}

template<class T>
SCCI<T> *
SCCQuotientGraph<T>::add (T *t, bool nontrivial)
{
    SCCI<T> *scc = createSCC (nontrivial);

    add (scc, t, nontrivial);
}

template<class T>
void
SCCQuotientGraph<T>::print()
{
       reach.print(outs());
}

} // namespace VVT


// EXPLICIT TEMPLATE INSTANTIATION
#include <llvm/IR/BasicBlock.h>
#include <llvm/IR/Instruction.h>
using namespace llvm;

namespace VVT {
    template class SCCQuotientGraph<BasicBlock>;
    template class SCCQuotientGraph<Instruction>;
}
