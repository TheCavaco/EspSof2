sig Node {
	var next: lone Node,
	pri: Int,
	data: Int
}

sig Queue {
	var fst: lone Node,
	var last: lone Node,
	var count: Int 
}

fact allNodesNotInQueueHaveNoNext {
	always (all n:Node, q:Queue | n !in q.fst.^next implies #(n.(~next)) = 0)
}

// All nodes belong to a Queue
fact allNodesBelongToOnlyOneQueue {
	//all n:Node, q1:Queue, q2:Queue| q1 != q2 and n in q1.fst.*next implies n !in q2.fst.*next
	always(all q1:Queue, q2:Queue| q1 != q2 implies no (q1&q2))
}

// If a queue has a first node it has to have a last
fact lastBelongsToQueue{
	always (all q:Queue | one q.fst implies (one q.last and q.last in q.fst.*next ))
}

fact lastIsAlwaysLast {
	always (all q:Queue , n:Node | no n.next and n in (q.fst + q.fst.*next) implies n = q.last)
}

// All nodes' priority is smaller than the next one's
fact NodePriority {
	(all n:Node| one n.next implies n.pri >= n.next.pri)
}

// All priorities are bigger than 0
fact AllPrioritiesAreBiggerThanZero {
	all n:Node | n.pri >= 0
}

// Count is the size of the list
fact CountSize {
	always (all q:Queue | q.count = #(q.fst + q.fst.^next))
}

// No list repeats nodes (A->B->A)
fact NoRepeatLists {
	always (all n : Node | n not in n.^next)
}

// There can be no node whose next is a first node
fact FirstNodesAreNotNext {
	always (all q:Queue, n:Node | n.next != q.fst)
}

// Nodes that are last in a queue have no next node
fact NoNextInLastNode {
	all q:Queue, n:Node | n = q.last implies no n.next  
}

//
fact NodeIsOnlyNextOfOneNodeInSameQueue {
	always (all q:Queue, n:Node| n in (q.fst + q.fst.*next) implies #(n.(~next)) <= 1)
}

pred insertPVPair[n1:Node, n2:Node] {
	//pre
	no n1.next
	n1 != n2
	all q:Queue | n1 !in (q.fst + q.fst.*next)
	one q:Queue| n2 = q.fst
	
	//post
	all n:Node, q:Queue| (n.pri >= n1.pri and one n.next and n.next.pri < n1.pri and n in (q.fst + q.fst.*next) and n2 = q.fst) implies (n.next' = n1 and n1.next' = n.next and q.fst' = q.fst and q.last' = q.last )
	all n:Node, q:Queue| (n.pri >= n1.pri and no n.next and n in (n2 + n2.*next) and n2 = q.fst) implies (n.next' = n1 and q.fst' = q.fst and q.last' = n1)
	all q:Queue| (n2.pri < n1.pri and n2 = q.fst) implies (n1.next' = n2' and q.fst' = n1 and q.last' = q.last)

	//frame
	all n:Node| (n != n1 and (n !in (n2 +n2.*next))) implies (n.next' = n.next)
	all n:Node| ((n in (n2 +n2.*next) and one n.next and n.pri > n1.pri and n.next.pri > n1.pri)) implies (n.next' = n.next)
	all n:Node| ((n in (n2 +n2.*next) and one n.next and n.pri < n1.pri and n.next.pri < n1.pri)) implies (n.next' = n.next)
	all n:Node| ((n in (n2 +n2.*next) and no n.next and n.pri < n1.pri)) implies (n.next' = n.next)
	all q:Queue | (n2 !in (q.fst + q.fst.*next)) implies (q.fst' = q.fst and q.last' = q.last and q.count' = q.count)
}

pred enqueue[q:Queue, n:Node]{
	//pre
	n !in (q.fst + q.fst.*next)
	all q1:Queue | q1 != q implies n !in (q1.fst + q1.fst.*next)

	// post
	once insertPVPair[n, q.fst]

	//frame
}


pred stutter {
	Node.next' = Node.next
	fst' = fst
	last' = last
	count' = count
}

fact SystemFact {
	// possible events
	always ((some n1:Node, n2:Node | insertPVPair[n1,n2]) or stutter)
}

pred RunPred1 {
	(eventually always ((some Node.next) and (some fst) and (some last) and (some count)))
	and 
	(eventually once (some n1, n2: Node | insertPVPair[n1, n2]))
}

run {RunPred1} for 5 but 5 steps
