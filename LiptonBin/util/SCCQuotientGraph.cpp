#include <assert.h>
#include <iostream>
#include <string>

#include "SCCQuotientGraph.h"
#include "Util.h"

using namespace llvm;
using namespace std;

namespace VVT {

void
SCCQuotientGraph::addLink (SCCI *x, SCCI *y)
{
    assert (x != y);
    ASSERT (!locked[x->index], "SCCs not linked in post-order: "<< x->bb << " >< "<< y->bb);

    reach.set  (x->index, y->index);
    reach.copy (x->index, y->index);
    locked[y->index];
}

void
SCCQuotientGraph::addLink (BasicBlock *x, BasicBlock *y)
{
    SCCI *xscc = blockMap[x];
    SCCI *yscc = blockMap[y];
    addLink(xscc, yscc);
}

void
SCCQuotientGraph::addLink (BasicBlock *x, SCCI *y)
{
    SCCI *xscc = blockMap[x];
    addLink(xscc, y);
}

SCCI *
SCCQuotientGraph::addSCC (bool loops)
{
    SCCI *scci = new SCCI (indicesIndex++, loops);
//errs () <<  indicesIndex << " << " << scci->index << "\n";
    reach.ensure(indicesIndex, indicesIndex);
    locked.ensure(indicesIndex);
    if (loops)
        reach.set (scci->index, scci->index); // reflexive reachability properties
    return scci;
}

SCCI *
SCCQuotientGraph::addBlock (BasicBlock *bb, bool loops)
{
    SCCI *scc = addSCC(loops);
    scc->bb = bb;
    pair<BasicBlock *, SCCI *> p = make_pair (bb, (SCCI *)scc);
    if (!blockMap.insert( p ).second) {
        outs () << "Instruction added twice: " << *bb;
        exit (1);
    }
    return scc;
}

void
SCCQuotientGraph::print()
{
       reach.print(outs());
}

}

