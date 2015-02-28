#include <assert.h>
#include <iostream>
#include <string>

#include "util/SCCQuotientGraph.h"
#include "util/Util.h"

using namespace std;


namespace VVT {

template<class T>
SCCI *
SCCQuotientGraph<T>::operator[] (T *t) {
     return blockMap[t];
}

template<class T>
T *
SCCQuotientGraph<T>::operator[] (int index) {
     return objects[index];
}

template<class T>
T *
SCCQuotientGraph<T>::operator[] (SCCI *scc) {
     return objects[scc->index];
}

template<class T>
void
SCCQuotientGraph<T>::link (SCCI *x, SCCI *y)
{
    assert (x != y);
    ASSERT (!locked[x->index], "SCCs not linked in post-order: "<< (*this)[x] << " >< "<< (*this)[y]);

    reach.set  (x->index, y->index);
    reach.copy (x->index, y->index);
    locked[y->index];
}

template<class T>
void
SCCQuotientGraph<T>::link (T *x, T *y)
{
    SCCI *xscc = blockMap[x];
    SCCI *yscc = blockMap[y];
    link(xscc, yscc);
}

template<class T>
void
SCCQuotientGraph<T>::link (T *x, SCCI *y)
{
    SCCI *xscc = blockMap[x];
    link(xscc, y);
}

template<class T>
SCCI *
SCCQuotientGraph<T>::createSCC (T *t, bool nontrivial)
{
    SCCI *scci = new SCCI (objects.size(), nontrivial);
    objects.push_back(t);
    size_t next = objects.size();
//errs () <<  indicesIndex << " << " << scci->index << "\n";
    reach.ensure(next, next);
    locked.ensure(next);
    if (nontrivial)
        reach.set (scci->index, scci->index); // reflexive reachability properties
    return scci;
}

template<class T>
SCCI *
SCCQuotientGraph<T>::add (T *t, bool nontrivial)
{
    SCCI *scc = createSCC(t, nontrivial);
    pair<T *, SCCI *> p = make_pair (t, scc);

    bool seen = blockMap.insert( p ).second;
    ASSERT (seen, "Instruction added twice: " << t);

    return scc;
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
