module orderings[Url] --[elem]

--open concreteUrl

open helpers

/*sig TestBrowser {
	var elements : set History 
}*/

sig History {
	var next : lone History,
	var prev : lone History,
	url : Url
}

fact {
	--all disj b, b1 : TestBrowser | all el : b.elements | el !in b1.elements
	--all b : TestBrowser | all el : b.elements | el.next + el.prev in b.elements
}

fact {
	always (all e : History | some e.next  implies e.next !in e.^prev )
	always (all e : History | e !in e.^prev)
	always (all e : History | some e.next implies e !in e.^next )
	always (all disj e, e1 : History | (some e.next and e1 = e.next) implies e !in e1.^next)
	always (all disj e, e1 : History | (some e.next and e1 = e.next) implies e = e1.prev)
	always (all disj e, e1 : History | e1 in e.^prev implies e1 !in e1.^prev)
	always (all disj e, e1 : History | (some e.prev and e1 = e.prev) implies e1.next = e)
	--all e, e1 : History | (some e.next and e.next = e1.next ) <=> e = e1
	--all e, e1 : History | e.prevs = e1.prevs <=> e = e1

}

fun history_first [e1 : set History] : one History {
	{e : e1 | 

		--(e in e1.^prev or e = e1) and no e.^prev
		/*some e1.prev implies (
			e in e1.^prev and no e.^prev
		) else (
			e = e1 and no e.^prev
		)*/
		no e.prev
	}
}

fun history_last [e1 : set History] : one History {
	{e: e1 |
		
		--(e in e1.^next or e = e1) and no e.^next

		/*some e1.next implies (
			e in e1.^next and no e.^next
		) else (
			e = e1 and no e.^next
		)*/
		no e.next
	}
}

pred history_append [elems : set History, elems2 : set History, te : History]  {
	

		/*one e : elems |  one e2 : elems2 |
			some e.history_last implies 
				e.history_last.next = te and 
				te.prev = e.history_last and 
				elems2 = elems + te and
				e2.history_last = te and 
				te.^prev = elems */

		/*one e : elems |
			elems2 = elems + te and 
			e.history_last.next' = te and 
			te.prev' = e.history_last and te.next' = none --and 
			--unchanged[History - e.history_last - te, (History <: next)] and 
			--unchanged[History - te, (History <: prev)]*/


		elems2 = elems + te --and
		elems.history_last.next' = te --and
		te.prev' = elems.history_last --and
		te.next' = none --and
		--elems2.history_last = te 
		--elems2.history_first = elems.history_first
		unchanged[History - elems.history_last - te, (History <: next)] --and
		unchanged[History - te, (History <: prev)]

}

pred history_append_first [elems : set History, elems2 : set History, te : History] {

	elems2 = elems + te --and 
	--elems2.history_last = te and 
	--elems2.history_first = te and
	no te.prev --and 
	no te.next --and 
	--unchanged[History, (History <: next)] --and 
	--unchanged[History, (History <: prev)]
}

pred related [e : History, te : History] {
	--one e: elems |
		e = te or te in e.^prev or te in e.^next

}
/*

run {


	some b : TestBrowser | some disj  e, e1, e2 : History |  
		related[e, e1] and 
		no e2.next and no e2.prev and e2 !in History.prev and e2 !in History.next and 
		e2 !in b.elements and some b.elements and (append[b.elements, b.elements', e2] implies b.elements' = b.elements + e2 )
	--some disj e, e1, e2, e3, e4 : History | !related[e, e1] and !related[e1,e2] and !related[e2, e3] and !related[e, e4] and !related[e1, e4] and !related[e2, e4] and !related[e3,e4]
} for 6


check {

	always (all b : TestBrowser | all disj e, e1, e2 : History |
		related[e, e1] and 
		no e2.next and no e2.prev and e2 !in History.prev and e2 !in History.next and
		e2 !in b.elements and some b.elements and append[b.elements, b.elements', e2] implies b.elements' = b.elements + e2
	)

} for 6
*/
