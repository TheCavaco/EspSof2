include "Ex1.dfy"

module Ex2 {
  import Ex1=Ex1

  class PriQueue {
    var fst : Ex1.PVNode?; 

    ghost var pvs: multiset<(int,int)>;
    ghost var footprint : set<Ex1.PVNode>;

    function ValidQ() : bool
      reads this, fst, if fst == null then {} else fst.footprint
    {
      (fst == null ==> (|pvs| == 0 && |footprint| == 0)) &&
      (fst != null ==> (fst.Valid() && fst.footprint == footprint && multiset(fst.list) == pvs))
    }
    
    method enqueue (pri: int, v: int)
      requires pri >= 0 && ValidQ() && pri >= 0
      ensures ValidQ()
      ensures pvs == old(pvs) + multiset{(pri,v)}
      modifies this, this.footprint
    {
      if (fst == null) {
        fst := new Ex1.PVNode(pri, v);
        footprint := {fst};
        pvs := multiset{(pri, v)};
        return;
      } else {
        var aux := fst.insertPVPair(pri, v);
        footprint := aux.footprint;
        pvs := pvs + multiset{(pri, v)};
        fst := aux;
        return;
      }
    }

    method dequeue () returns (r : (int, int))
      requires ValidQ() && fst != null
      ensures ValidQ()
      ensures (forall k :: k in pvs ==> k.0 <= r.0)
      ensures old(footprint) == footprint + {old(fst)}
      ensures old(fst) != null && old(fst).next == null ==> fst == null;
      modifies this, footprint
    {
      var aux := fst.next;
      r := (fst.pri, fst.data);
      if (aux == null) {
        fst := null;
        footprint := {};
        pvs := multiset{};
        return;
      } else {
        ghost var cur := fst; 
        assert aux.list == fst.list[1..];
        fst := aux;
        footprint := aux.footprint;
        pvs := multiset(aux.list);
        assert old(footprint) == footprint + {cur};
        return;
      }
    }
    
  }
}
