
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
  }

  constructor (i : int, p : int) 
  {
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



