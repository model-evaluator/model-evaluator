module event

open call
open browser
open url

fact {

    always (all c : Call | exec[c.event, c])
}

let unchanged[s,r] = all x : s | x.(r)'= x.(r)


pred exec [f : Function, c : Call] {
	f in WindowOpen implies window_open[f, c]
	f in Navigate implies navigate[f, c]
	f in ResourceRequest implies render_resource[f, c]
	f in Popup implies popup[f, c]
	f in SharedArrayBufferAccess implies sharedArrayBufferAccess[f, c]
	f in Skip implies skip[]
}

pred window_open [f : Function, c : Call] {
	c.bcg !in Browser.bcgs
	c.bcg.bcs = none and
	Browser.bcgs' = Browser.bcgs + c.bcg 
	c.bcg.bcs' = c.bcg.bcs + c.bc
	--c.bc in c.bcg.bcs
	c.bc.html' = none
	c.bc.document' = none
	c.bc.document.(Document <: elements') = none
	c.bc.document.blocked' = none
	c.bc.opening' = none
	c.bc.origin' = none
	c.bc.rendered' = False
	unchanged[BrowsingContextGroup - c.bcg, bcs]
	unchanged[BrowsingContext - c.bc, (BrowsingContext <: html)]
	unchanged[BrowsingContext - c.bc, document]
	unchanged[BrowsingContext - c.bc, (BrowsingContext <: origin)]
	unchanged[BrowsingContext - c.bc, rendered]
	unchanged[BrowsingContext - c.bc, opening]
	unchanged[Document - c.bc.document, (Document <: elements)]
	unchanged[Document - c.bc.document, blocked]
	unchanged[Document, (Document <: policies)]
	unchanged[Document, sharedbuffer]
	unchanged[Script, (Script <: context)]
	unchanged[Script, sabAccess]
	unchanged[NonActive, (NonActive <: context)]
	unchanged[HtmlRaw, (HtmlRaw <: elements)]
}

pred navigateAction [nbc : BrowsingContext, h : HtmlRaw, u : Url, s : Server] {
	one d : Document |

		nbc.rendered = False and
		h = s.resources[u.path] and
		s in Dns.map[u.origin.domain] and
		nbc.html' = h and
		nbc.document' = d and
		d.(Document <: elements') = none and
		d.blocked' = none and
		--(nbc.document.elements & Script).sabAccess' = none and
		d.(Document <: policies') = s.policies[u.path][h] and
		nbc.origin' = u.origin and
		nbc.rendered' = False and
		h.src = u and
		d.src = u and

		unchanged[BrowsingContext - nbc, (BrowsingContext <: html)] and
		unchanged[BrowsingContext - nbc, document] and
		unchanged[BrowsingContext - nbc, (BrowsingContext <: origin)] and
		unchanged[BrowsingContext - nbc, rendered] and
		unchanged[Document - d, (Document <: elements)] and
		unchanged[Document - d, blocked] and
		unchanged[Document - d, (Document <: policies)] and
		unchanged[Document - d, sharedbuffer] and
		unchanged[Script, (Script <: context)] and
		unchanged[Script, sabAccess] and
		unchanged[NonActive, (NonActive <: context)] and
		unchanged[HtmlRaw, (HtmlRaw <: elements)]

}

pred navigate [f : Function, c : Call] {

	let nbc = c.bc | let u = f.(Navigate <: url) | let h = f.(Navigate <: html) |

		navigateAction[nbc, h, u, c.to ] and
		nbc.opening' = none and
		unchanged[BrowsingContext - nbc, opening] and
		unchanged[Browser, bcgs] and
		unchanged[BrowsingContextGroup, bcs]

}

pred render_allowed [nbc : BrowsingContext, el : Script + NonActive] {

	nbc.document.elements' = nbc.document.elements + el and

	unchanged[Document, blocked] and
	unchanged[Document - nbc.document, (Document <: elements)] and

	(el in Script implies (
		el.(Script <: context') = nbc.document and
		unchanged[Script - el, (Script <: context)] and
		unchanged[NonActive, (NonActive <: context)]
	)else (
		el.(NonActive <: context') = nbc.document and
		unchanged[Script, (Script <: context)] and
		unchanged[NonActive - el, (NonActive <: context)]
	)) 
}

pred render_blocked [nbc : BrowsingContext, el : Script + NonActive] {
	nbc.document.blocked' = nbc.document.blocked + el and

	unchanged[Document - nbc.document, blocked] and
	unchanged[Document, (Document <: elements)] and

	(el in Script implies (
		el.(Script <: context') = none and
		unchanged[Script - el, (Script <: context)] and
		unchanged[NonActive, (NonActive <: context)]
	)else (
		el.(NonActive <: context') = none and
		unchanged[Script, (Script <: context)] and
		unchanged[NonActive - el, (NonActive <: context)]
	)) 
}

pred render_resource [f : Function, c : Call ] {
	let nbc = c.bc | let u  = f.(ResourceRequest <: url) | let el = c.to.resources[u.path] | 
	--let dPol = d.(Document <: policies) & COEP | 
	let d = nbc.document |
	let elPolCORP = c.to.policies[u.path][el] & CORP |
	let elPolCORS = c.to.policies[u.path][el] & CORS |

		nbc.rendered = False and
		some nbc.html and
		some nbc.document and
		u in nbc.html.elements and
		f.body = el and
		some el and
		c.to in Dns.map[u.origin.domain] and
		--el in nbc.html and

		(el in Script implies (
			el.(Script <: src) = u
		)else (
			el.(NonActive <: src) = u
		)) and

		(u.origin != d.src.origin implies (
			(((some elPolCORP and elPolCORP.directive = CrossOrigin and no elPolCORS ) or 
				(some elPolCORP and elPolCORP.directive = CrossOrigin and some elPolCORS and d.src.origin in elPolCORS.allowedOrigins ) or 
				(no elPolCORP and some elPolCORS and d.src.origin in elPolCORS.allowedOrigins)) implies (
				render_allowed[nbc, el]
			)else (
				render_blocked[nbc, el]
			))
		)else (
			render_allowed[nbc, el]
		)) and

		unchanged[Browser, bcgs] and
		unchanged[BrowsingContextGroup, bcs] and
		unchanged[BrowsingContext, (BrowsingContext <: html)] and
		unchanged[BrowsingContext, document] and
		unchanged[BrowsingContext, (BrowsingContext <: origin)] and
		unchanged[BrowsingContext, opening] and
		unchanged[Document, sharedbuffer] and
		unchanged[Script, sabAccess] and
		unchanged[HtmlRaw - nbc.html, (HtmlRaw <: elements)] and

		nbc.html.elements' = nbc.html.elements - u and

		(nbc.html.elements' = none implies (
			nbc.rendered' = True and
			unchanged[BrowsingContext - nbc, rendered]
		)else (
			unchanged[BrowsingContext, rendered]
		))

}

pred popup [f : Function, c : Call] {
	let nbcGr = c.bcg | let nbc = c.bc | let u = f.(Popup <: url) | let h = f.(Popup <: html) |
	let newBc = f.newBc |
	let newBcGr = f.newBcGr |
	let openerCOOP = nbc.document.policies & COOP |
	let openingCOOP = newBc.document.policies' & COOP |

		nbc != newBc and

		newBc !in Browser.bcgs.bcs and

		navigateAction[newBc, h, u, c.to ] and
		nbc.opening' = nbc.opening + newBc and

		unchanged[BrowsingContext - nbc, opening] and

		some nbc.document and

		((no openerCOOP and no openingCOOP) implies (
			unchanged[Browser, bcgs] and
			nbcGr.bcs' = nbcGr.bcs + newBc and 
			nbcGr = newBcGr and 
			unchanged[BrowsingContextGroup - nbcGr, bcs]

		)else (

			((some openerCOOP and some openingCOOP and openerCOOP.directive = openingCOOP.directive and nbc.origin = newBc.origin' ) implies (
				unchanged[Browser, bcgs] and
				nbcGr.bcs' = nbcGr.bcs + newBc and 
				nbcGr = newBcGr and 
				unchanged[BrowsingContextGroup - nbcGr, bcs]
			)else (
				Browser.bcgs' = Browser.bcgs + newBcGr and 
				newBcGr.bcs' = newBcGr.bcs + newBc and 
				nbcGr !=  newBcGr and 
				unchanged[BrowsingContextGroup - newBcGr, bcs]
			))
			
		))

}

pred CrossOriginIsolatedState [nbc : BrowsingContext] {

	let coop = nbc.document.policies & COOP | 
	let coep = nbc.document.policies & COEP | 
		some nbc.document and
		some coop and
		some coep and 
		coop.directive = SameOrigin and 
		coep.directive = RequireCorp
}

pred sharedArrayBufferAccess [f : Function, c : Call ]{
	--let scr : f.script |

		f.script.sabAccess' = f.script.sabAccess + f.buffer 
		f.script in c.bcg.bcs.document.elements
		f.buffer in Document.sharedbuffer
		unchanged[Browser, bcgs]
		unchanged[BrowsingContextGroup, bcs]
		unchanged[BrowsingContext, (BrowsingContext <: html)]
		unchanged[BrowsingContext, document]
		unchanged[BrowsingContext, (BrowsingContext <: origin)]
		unchanged[BrowsingContext, rendered]
		unchanged[BrowsingContext, opening]
		unchanged[Document, (Document <: elements)]
		unchanged[Document, blocked]
		unchanged[Document, (Document <: policies)]
		unchanged[Document, sharedbuffer]
		unchanged[Script, (Script <: context)]
		unchanged[Script - f.script, sabAccess]
		unchanged[NonActive, (NonActive <: context)]
		unchanged[HtmlRaw, (HtmlRaw <: elements)]
}

pred legitScript [scr : Script] {
	let doc = scr.context |
	let nbc = doc.~document |
	let nbcg = nbc.~bcs |
		some nbc and
		some nbcg and
		scr !in doc.blocked and 
		scr in doc.elements and 
		nbcg in Browser.bcgs
}

pred canAccessSOP [scr : Script, doc : Document] {
	let nbc = doc.~document |
	let nbcg = nbc.~bcs |
		some nbc and 
		some nbcg and
		nbcg in Browser.bcgs and 
		legitScript[scr] and 
		scr.context.src.(Url <: origin) = doc.src.(Url <: origin) 
}

fact sabAccessFact {
	always (
		all f : SharedArrayBufferAccess |
		let scr = f.script | let b = f.buffer |
		let doc = b.~sharedbuffer |
			b in scr.sabAccess implies (
				--legitScript[scr] and 
				some doc and
				canAccessSOP[scr, doc]
			)
	)
}


fact COISharedBuffer {
	always (all d : Document | 
		(CrossOriginIsolatedState[d.~document] implies (
			some d.sharedbuffer
		) else (
			no d.sharedbuffer
		))
	)
}

pred skip {
	unchanged[Browser, bcgs]
	unchanged[BrowsingContextGroup, bcs]
	unchanged[BrowsingContext, (BrowsingContext <: html)]
	unchanged[BrowsingContext, document]
	unchanged[BrowsingContext, (BrowsingContext <: origin)]
	unchanged[BrowsingContext, rendered]
	unchanged[BrowsingContext, opening]
	unchanged[Document, (Document <: elements)]
	unchanged[Document, blocked]
	unchanged[Document, (Document <: policies)]
	unchanged[Document, sharedbuffer]
	unchanged[Script, (Script <: context)]
	unchanged[Script, sabAccess]
	unchanged[NonActive, (NonActive <: context)]
	unchanged[HtmlRaw, (HtmlRaw <: elements)]
}











