sig Node {
	next: lone Node,
	pri: Int,
	data: Int
}

sig Queue {
	fst: lone Node,
	last: lone Node,
	count: Int 
}


// There can be no nodes that are not in a queue
fact allNodesBelongToSomeQueue {
	all n:Node | some q:Queue | n in q.fst.*next
}

// All nodes belong to a Queue
fact allNodesBelongToOnlyOneQueue {
	all n:Node, q1:Queue, q2:Queue| q1 != q2 and n in q1.fst.*next implies n !in q2.fst.*next
}

// If a queue has a first node it has to have a last
fact lastBelongsToQueue{
	all q:Queue | one q.fst implies q.last in q.fst.*next and one q.last
}

// All nodes' priority is smaller than the next one's
fact NodePriority {
	all n:Node| one n.next implies n.pri > n.next.pri
}

// All priorities are bigger than 0
fact AllPrioritiesAreBiggerThanZero {
	all n:Node | n.pri >= 0
}

// Count is the size of the list
fact CountSize {
	all q:Queue | q.count = #(q.fst + q.fst.^next)
}

// No list repeats nodes (A->B->A)
fact NoRepeatLists {
	all n : Node | n not in n.^next	
}

// There can be no node whose next is a first node
fact FirstNodesAreNotNext {
	all q:Queue, n:Node | n.next != q.fst
}

// Nodes that are last in a queue have no next node
fact NoNextInLastNode {
	all q:Queue| one n:Node | n = q.last and no n.next  
}

run {} for exactly 10 Node, exactly 2 Queue
