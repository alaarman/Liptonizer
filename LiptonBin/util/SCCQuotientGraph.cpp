#include <assert.h>
#include <iostream>
#include <string>

#include "SCCQuotientGraph.h"
#include "Util.h"

using namespace std;


namespace VVT {

template<class T>
typename SCCQuotientGraph<T>::SCCI *
SCCQuotientGraph<T>::operator[](T *bb) {
     return blockMap[bb];
}

template<class T>
void
SCCQuotientGraph<T>::addLink (SCCI *x, SCCI *y)
{
    assert (x != y);
    ASSERT (!locked[x->index], "SCCs not linked in post-order: "<< x->bb << " >< "<< y->bb);

    reach.set  (x->index, y->index);
    reach.copy (x->index, y->index);
    locked[y->index];
}

template<class T>
void
SCCQuotientGraph<T>::addLink (T *x, T *y)
{
    SCCI *xscc = blockMap[x];
    SCCI *yscc = blockMap[y];
    addLink(xscc, yscc);
}

template<class T>
void
SCCQuotientGraph<T>::addLink (T *x, SCCI *y)
{
    SCCI *xscc = blockMap[x];
    addLink(xscc, y);
}

template<class T>
typename SCCQuotientGraph<T>::SCCI *
SCCQuotientGraph<T>::addSCC (bool loops)
{
    SCCI *scci = new SCCI (indicesIndex++, loops);
//errs () <<  indicesIndex << " << " << scci->index << "\n";
    reach.ensure(indicesIndex, indicesIndex);
    locked.ensure(indicesIndex);
    if (loops)
        reach.set (scci->index, scci->index); // reflexive reachability properties
    return scci;
}

template<class T>
typename SCCQuotientGraph<T>::SCCI *
SCCQuotientGraph<T>::addBlock (T *bb, bool loops)
{
    SCCI *scc = addSCC(loops);
    scc->bb = bb;
    pair<T *, SCCI *> p = make_pair (bb, (SCCI *)scc);

    bool seen = blockMap.insert( p ).second;
    ASSERT (seen, "Instruction added twice: " << bb);

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
