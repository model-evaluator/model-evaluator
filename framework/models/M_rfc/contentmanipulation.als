module contentmanipulation

open scmCallFunction
open browser


pred read_dom [f : Function, c : Call] {
	let nbc = f.bc |
	let d = nbc.currentDoc |
	let pbc = f.party |

		f.(ReadDom <: response) = d + (d.elements <: NonActive) + (d.elements <: Document) and

		pbc.accesses' = pbc.accesses + f.(ReadDom <: response) and

		unchanged[Browser, bcs] and
	    unchanged[Browser, blobs]  and
	    unchanged[BrowsingContext, (BrowsingContext <: origin)] and
	    unchanged[BrowsingContext, currentDoc] and
	    unchanged[BrowsingContext, nestedBcs] and
	    unchanged[BrowsingContext, sessionHistory] and
        unchanged[BrowsingContext, isSecureContext]  and
        unchanged[BrowsingContext, isSandboxed] and
	    unchanged[BrowsingContext, opening] and
        unchanged[BrowsingContext - pbc, accesses] and
	    unchanged[Document, (Document <: src)] and
	    unchanged[Document, elements] and 
	    unchanged[Script, (Script <: context)] and 
	    unchanged[NonActive, (NonActive <: context)]

}

pred write_dom [f : Function, c : Call] {
	let nbc = f.bc |
	let d = nbc.currentDoc |

		f.oldEl in d.elements and 
		f.(WriteDom <: newEl) !in Document.elements and 
		d.elements' = d.elements - f.oldEl + f.(WriteDom <: newEl) and

		((f.oldEl in Script and f.(WriteDom <: newEl) in Script) implies (
			f.oldEl.(Script <: context') = none and 
			f.(WriteDom <: newEl).(Script <: context') = d and 
			unchanged[Script - (f.oldEl + f.(WriteDom <: newEl)), (Script <: context) ] and 
			unchanged[NonActive, (NonActive <: context)] and 
			unchanged[BrowsingContext, nestedBcs] 

		)else (
			(f.oldEl in NonActive and f.(WriteDom <: newEl) in NonActive) implies (
				f.oldEl.(NonActive <: context') = none and 
				f.(WriteDom <: newEl).(NonActive <: context') = d and 
				unchanged[Script, (Script <: context) ] and 
				unchanged[NonActive - (f.oldEl + f.(WriteDom <: newEl)), (NonActive <: context)] and 
				unchanged[BrowsingContext, nestedBcs] 
			)else (
				f.oldEl in Script implies (
					f.oldEl.(Script <: context') = none and 
					f.(WriteDom <: newEl).(NonActive <: context') = d and
					unchanged[Script - f.oldEl, (Script <: context) ] and 
					unchanged[NonActive - f.(WriteDom <: newEl), (NonActive <: context) ] and 
					unchanged[BrowsingContext, nestedBcs] 
				) else (
					f.oldEl in NonActive implies (
						f.oldEl.(NonActive <: context') = none and 
						f.(WriteDom <: newEl).(Script <: context') = d and
						unchanged[Script - f.(WriteDom <: newEl), (Script <: context) ] and 
						unchanged[NonActive - f.oldEl, (NonActive <: context) ] and 
						unchanged[BrowsingContext, nestedBcs] 
					)else (
						--this means oldEl in Document
						nbc.nestedBcs' = nbc.nestedBcs - f.oldEl.~currentDoc and
						unchanged[BrowsingContext - nbc, nestedBcs] and
						f.(WriteDom <: newEl) in Script implies (
							f.(WriteDom <: newEl).(Script <: context') = d and
							unchanged[Script - f.(WriteDom <: newEl), (Script <: context) ] and 
							unchanged[NonActive, (NonActive <: context) ]
						)else (
							f.(WriteDom <: newEl).(NonActive <: context') = d and
							unchanged[Script, (Script <: context) ] and 
							unchanged[NonActive - f.(WriteDom <: newEl), (NonActive <: context) ]
						)

					)
				)


				

			)
		)) and



		unchanged[Browser, bcs] and
	    unchanged[Browser, blobs]  and
	    unchanged[BrowsingContext, (BrowsingContext <: origin)] and
	    unchanged[BrowsingContext, currentDoc] and
	    unchanged[BrowsingContext, sessionHistory] and
        unchanged[BrowsingContext, isSecureContext]  and
        unchanged[BrowsingContext, isSandboxed] and
	    unchanged[BrowsingContext, opening] and
        unchanged[BrowsingContext, accesses] and
	    unchanged[Document, (Document <: src)] and
	    unchanged[Document - d, elements] 

}

pred inject_script [f : Function, c : Call] {
	let nbc = f.bc |
	let d = nbc.currentDoc |

		some d and

		d = f.targetDoc and
		d.elements' = d.elements + f.newScr and

		f.newScr.context' = d and

		unchanged[Browser, bcs] and
	    unchanged[Browser, blobs]  and
	    unchanged[BrowsingContext, (BrowsingContext <: origin)] and
	    unchanged[BrowsingContext, currentDoc] and
	    unchanged[BrowsingContext, nestedBcs] and
	    unchanged[BrowsingContext, sessionHistory] and
        unchanged[BrowsingContext, isSecureContext]  and
        unchanged[BrowsingContext, isSandboxed] and
	    unchanged[BrowsingContext, opening] and
        unchanged[BrowsingContext, accesses] and
	    unchanged[Document, (Document <: src)] and
	    unchanged[Document - d, elements] and 
	    unchanged[Script - f.newScr, (Script <: context)] and 
	    unchanged[NonActive, (NonActive <: context)]

}