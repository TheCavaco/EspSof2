
include "Ex1.dfy"

class PriQueue {
  var fst : PVNode?; 

  ghost var pvs: multiset<(int,int)>;
  ghost var footprint : set<PVNode>;

  function ValidQ() : bool
    reads this, fst, if fst == null then {} else fst.footprint
  {
  }
  
  method enqueue (pri: int, v: int)
    requires pri >= 0 && ValidQ()
    ensures ValidQ()
    ensures pvs == old(pvs) + multiset{(pri,v)}
    modifies this, this.footprint
  {
  }

  method dequeue () returns (r : (int, int)) 
  {
  }
  
}