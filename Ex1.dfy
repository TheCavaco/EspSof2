
function sortedPVSeq(s : seq<(int,int)>) : bool {
  forall i :: 0 <= i < |s| ==> s[i].0 >= 0 
    && 
  forall i,j :: 0 <= i < j < |s| ==> s[i].0 >= s[j].0
}

function max(i : int, j : int) : int {
  if (i >= j)
    then i 
    else j 
}

class PVNode {
  ghost var list : seq<(int,int)>; 
  ghost var footprint : set<PVNode>;

  var data : int; 
  var pri : int; 
  var next : PVNode?; 

  function Valid() : bool 
    reads this, footprint
    decreases footprint;
  {
    (sortedPVSeq(this.list)) &&
    (this in footprint) &&
    (this.next == null ==> footprint == {this} && list == [(pri, data)]) &&
    (this.next != null ==>  (next in footprint && footprint == next.footprint + {this}
        && this !in next.footprint && list == [(pri, data)] + next.list
        && pri >= next.pri && next.Valid()))
  }

  constructor (i : int, p : int) 
    requires i >= 0
    ensures Valid() &&
    next == null && data == p && pri == i && list == [(i, p)] && footprint == {this}
    && (|this.list| > 0) && (|this.footprint| > 0)
  {
    next := null;
    data := p;
    pri := i;
    list := [(pri, data)];
    footprint := {this};

  }

 

  method insertPVPair (pri: int, v: int) returns (r : PVNode) 
    requires this.Valid()
    requires pri >= 0
    ensures r.Valid() 
    ensures r.list[0].0 <= max(old(this.list[0].0), pri)
    ensures multiset(r.list) == multiset(old(this.list)) + multiset{ (pri, v)}
    ensures fresh(r.footprint - old(this.footprint))
    modifies footprint, this
    decreases footprint
  {
    
    if(pri >= this.pri){
      var aux := new PVNode(pri, v);
      aux.next := this;
      aux.list := aux.list + this.list;
      aux.footprint := aux.footprint + this.footprint;
      r := aux;
      assert r.pri >= this.pri;
      assert sortedPVSeq(this.list);
      assert r.list == [(r.pri, r.data)] + this.list;
      allIsSorted(this.list, (r.pri, data));
      return;
    } else if (pri < this.pri){
      if(this.next == null){
        var aux := new PVNode(pri, v);
        this.next := aux;
        this.footprint := this.footprint + this.next.footprint;
        this.list := this.list + this.next.list;
        r := this;
        return;

      } else {
        var aux := this.next.insertPVPair(pri, v);
        this.footprint := {this} + aux.footprint;
        this.list := [(this.pri, this.data)] + aux.list;
        this.next := aux;
        r := this;
        return;

      }
    }
     
  }


  method removeNode(n : PVNode) returns (r: PVNode?) 
  requires Valid()
  ensures r != null ==> r.Valid()
  //ensures r != null ==> |r.list| == old(|this.list|) - 1
  ensures r != null ==> r.footprint <= old(this.footprint)
  ensures r == null ==> old(this.list[0].0) == n.pri

  decreases this.footprint
  modifies footprint
  {   
    if(this.next == null){
      if(this == n){
        r := null;
        return;
      } else {
        r := this;
        return;
      }
    } else {
      if(this == n){
        r := this.next;
        return;
      } else {
        assert this.next.Valid();

        ghost var old_list := this.list;
        ghost var old_next_list := this.next.list;
        assert this.list == [(this.pri, this.data)] + this.next.list;
        assert |old_list| == |old_next_list| + 1;
        assert |old_list| > 1;
        var aux := this.next.removeNode(n);
        if (aux != null){
          assert aux.Valid();
          assert this.pri >= aux.pri;
          this.next := aux;
          this.list := [(this.pri, this.data)] + aux.list;
          this.footprint := {this} + aux.footprint;
          r := this; return; 
        } else {
          this.next := null;
          this.list := [(this.pri, this.data)];
          this.footprint := {this};
          r := this; return; 
        }
      }
    }
  }

  lemma allIsSorted(s: seq<(int, int)> , r : (int,int))
    requires sortedPVSeq(s) 
    requires |s| > 0
    requires r.0 >= s[0].0
    ensures sortedPVSeq([r] + s)
  {

  }

  


}





