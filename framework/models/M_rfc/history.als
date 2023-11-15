module history[Url]


open helpers


sig History {
	var next : lone History,
	var prev : lone History,
	url : Url
}



fact {
	always (all e : History | some e.next  implies e.next !in e.^prev )
	always (all e : History | e !in e.^prev)
	always (all e : History | some e.next implies e !in e.^next )
	always (all disj e, e1 : History | (some e.next and e1 = e.next) implies e !in e1.^next)
	always (all disj e, e1 : History | (some e.next and e1 = e.next) implies e = e1.prev)
	always (all disj e, e1 : History | e1 in e.^prev implies e1 !in e1.^prev)
	always (all disj e, e1 : History | (some e.prev and e1 = e.prev) implies e1.next = e)


}

fun history_first [e1 : set History] : one History {
	{e : e1 | 

		no e.prev
	}
}

fun history_last [e1 : set History] : one History {
	{e: e1 |
		

		no e.next
	}
}

pred history_append [elems : set History, elems2 : set History, te : History]  {
	


		elems2 = elems + te --and
		elems.history_last.next' = te --and
		te.prev' = elems.history_last --and
		te.next' = none --and

		unchanged[History - elems.history_last - te, (History <: next)] --and
		unchanged[History - te, (History <: prev)]

}

pred history_append_init [elems : set History, elems2 : set History, te : History] {

	elems2 = elems + te --and 

	no te.prev --and 
	no te.next --and 

}

pred related [e : History, te : History] {
	--one e: elems |
		e = te or te in e.^prev or te in e.^next

}

