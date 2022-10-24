
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
    this.pri >= 0 &&
    |this.list| > 0 && |this.footprint| > 0 &&
    (this in footprint) &&
    next == null ==> footprint == {this} && list == [(pri, data)] &&
    next != null ==>  (next in footprint && footprint == next.footprint + {this}
        && this !in next.footprint && list == [(pri, data)] + next.list
        && pri >= next.pri && next.Valid())
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
    requires Valid()
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
        assert this.next != null;
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
        var aux := this.next.removeNode(n);
        if (aux != null){
          this.next := aux;
          this.list := [(this.pri, this.data)] + aux.list;
          this.footprint := {this} + aux.footprint;
          
        } else {
          this.next := null;
          this.list := [(this.pri, this.data)];
          this.footprint := {this};
        }
        r := this;
        return;
      }
    }
  }

}



