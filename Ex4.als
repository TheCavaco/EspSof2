sig Node {
	next: lone Node,
	pri: Int,
	data: Int
}

sig Queue {
	fst: lone First,
	last: lone Last		
}

sig First in Node {}
sig Last in Node {}

// There can be no nodes that are not in a queue
fact allNodesBelongToSomeQueue {
	all n:Node | some q:Queue | n in q.fst.*next
}

fact allNodesBelongToOnlyOneQueue {
	all n:Node, q1:Queue, q2:Queue| q1 != q2 and n in q1.fst.*next implies n !in q2.fst.*next
}

// If a queue has a first node it has to have a last
fact lastBelongsToQueue{
	all q:Queue | one q.fst implies q.last in q.fst.*next and one q.last
}

fact NodePriority {
	all n:Node| one n.next implies n.pri < n.next.pri
}
fact AllPrioritiesAreBiggerThanZero {all n:Node | n.pri > 0}


fact p {
	all n : Node | n not in n.^next
	no next.First 
	no Last.next	
}


run {} for exactly 10 Node, exactly 2 Queue
