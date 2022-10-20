
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
    (this in footprint) &&
    pri >= 0 &&
    next == null ==> footprint == {this} && list == [(pri, data)] &&
    next != null ==>  (next in footprint && footprint == next.footprint + {this}
        && this !in next.footprint && list == [(pri, data)] + next.list
        && pri > next.pri && next.Valid())
  }

  constructor (i : int, p : int) 
  requires i >= 0
  ensures Valid() &&
  next == null && data == p && pri == i && list == [(i, p)] && footprint == {this}
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
    modifies footprint
    decreases footprint
  { 
  }


  method removeNode(n : PVNode) returns (r: PVNode?) 
  {   
  }

}


