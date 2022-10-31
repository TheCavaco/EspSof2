sig Node {
	next: lone Node
}

sig Queue {
	fst: lone First,
	last: lone Last		
}

sig First in Node {}
sig Last in Node {}


fact allNodesBelongToSomeQueue {
	all n:Node | some q:Queue | n in q.fst.*next
}

fact lastBelongsToQueue{
	all q:Queue | one q.fst implies q.last in q.fst.^next and one q.last
}

fact p {
	all n : Node | n not in n.^next
	no next.First 
	no Last.next
	all n : Node - First | some next.n
	all q:Queue,f:First, l:Last | f in q.fst implies l in q.last
	all q:Queue,f:First, l:Last | l in q.last implies f in q.fst
	
}


run {} for exactly 10 Node, exactly 2 Queue
