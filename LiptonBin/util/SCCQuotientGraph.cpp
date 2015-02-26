#include <assert.h>
#include <iostream>
#include <string>

#include "util/SCCQuotientGraph.h"
#include "util/Util.h"

using namespace std;


namespace VVT {

template<class T>
typename SCCQuotientGraph<T>::SCCI *
SCCQuotientGraph<T>::operator[](T *bb) {
     return blockMap[bb];
}

template<class T>
void
SCCQuotientGraph<T>::link (SCCI *x, SCCI *y)
{
    assert (x != y);
    ASSERT (!locked[x->index], "SCCs not linked in post-order: "<< x->object << " >< "<< y->object);

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
typename SCCQuotientGraph<T>::SCCI *
SCCQuotientGraph<T>::createSCC (bool loops)
{
    SCCI *scci = new SCCI (objects.size(), loops);
    objects.push_back(t);
    size_t next = objects.size();
//errs () <<  indicesIndex << " << " << scci->index << "\n";
    reach.ensure(next, next);
    locked.ensure(next);
    if (loops)
        reach.set (scci->index, scci->index); // reflexive reachability properties
    return scci;
}

template<class T>
typename SCCQuotientGraph<T>::SCCI *
SCCQuotientGraph<T>::add (T *t, bool loops)
{
    SCCI *scc = createSCC(loops, t);
    pair<T *, SCCI *> p = make_pair (t, (SCCI *)scc);

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
