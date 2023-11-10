module frameConditions

--open concreteUrl
open browser
--open orderings
--open concreteCallFunction


pred unchangedNavigateAbsolute[nbc : BrowsingContext, d : Document] {
            unchanged[Browser, bcs]
            unchanged[Browser, blobs] 
            unchanged[BrowsingContext - nbc, (BrowsingContext <: origin)]
            --unchanged[BrowsingContext, wind]
            unchanged[BrowsingContext - nbc, currentDoc]
            unchanged[BrowsingContext, nestedBcs]
            unchanged[BrowsingContext, sessionHistory]
            unchanged[BrowsingContext - nbc, isSecureContext] 
            unchanged[BrowsingContext - nbc, isSandboxed]
            unchanged[BrowsingContext - nbc, sandboxWaitingNavigate]
            --unchanged[Window, doc]
            unchanged[BrowsingContext - nbc, opening]
            unchanged[BrowsingContext - nbc, accesses]
            unchanged[Document - d, (Document <: src)]
            unchanged[Document - d, elements]
            unchanged[Script - (d.elements & Script), (Script <: context)]
            unchanged[NonActive - (d.elements & NonActive), (NonActive <: context)]
            
}

pred unchangedNavigate [nbc : BrowsingContext, d : Document, d2 : Document] {

        unchanged[Browser, bcs] 
        unchanged[BrowsingContext - (nbc + nbc.^nestedBcs), (BrowsingContext <: origin)] 
        unchanged[BrowsingContext - (nbc + nbc.^nestedBcs), currentDoc] 
        unchanged[BrowsingContext - (nbc + nbc.^nestedBcs), nestedBcs] 
        unchanged[BrowsingContext - (nbc + nbc.^nestedBcs), sessionHistory] 
        unchanged[BrowsingContext - (nbc + nbc.^nestedBcs), isSecureContext]
        unchanged[BrowsingContext - (nbc + nbc.^nestedBcs), isSandboxed]
        unchanged[BrowsingContext - (nbc + nbc.^nestedBcs), sandboxWaitingNavigate]
        unchanged[BrowsingContext - (nbc + nbc.^nestedBcs), opening] 
        unchanged[BrowsingContext - (nbc + nbc.^nestedBcs ), accesses]
        unchanged[Document - d, (Document <: src)] 
        unchanged[Document - (d + d2 + (d2.^elements <: Document)), elements] 
        unchanged[Script - (d2.^elements & Script), (Script <: context)]
        unchanged[NonActive - (d2.^elements & NonActive), (NonActive <: context)]

}

pred unchangedNavigateNested [nbc : BrowsingContext, d : Document, d2 : Document] {
        

        unchanged[Browser, bcs]
        unchanged[BrowsingContext - (nbc + nbc.^nestedBcs), (BrowsingContext <: origin)] 
        unchanged[BrowsingContext - (nbc + nbc.^nestedBcs), currentDoc] 
        unchanged[BrowsingContext - (nbc + nbc.^nestedBcs), nestedBcs] 
        unchanged[BrowsingContext - (nbc + nbc.^nestedBcs), sessionHistory] 
        unchanged[BrowsingContext - (nbc + nbc.^nestedBcs), isSecureContext]
        unchanged[BrowsingContext - (nbc + nbc.^nestedBcs), isSandboxed]
        unchanged[BrowsingContext - nbc, sandboxWaitingNavigate]
        unchanged[BrowsingContext - (nbc + nbc.^nestedBcs), opening] 
        unchanged[BrowsingContext - (nbc + nbc.^nestedBcs), accesses]
        unchanged[Document - d, (Document <: src)] 
        unchanged[Document - (d + d2 + (d2.^elements <: Document)), elements]  
        unchanged[Script - ((d.^elements & Script) + (d2.^elements & Script)), (Script <: context)]
        unchanged[NonActive - ((d.^elements & NonActive) + (d2.^elements & NonActive)), (NonActive <: context)]
        
}


pred unchangedAbsNavSafariXFOptionsNested [nbc : BrowsingContext] {
        

        unchanged[Browser, bcs]
        unchanged[Browser, blobs] 
        unchanged[BrowsingContext - nbc, (BrowsingContext <: origin)] 
        unchanged[BrowsingContext, currentDoc] 
        unchanged[BrowsingContext, nestedBcs] 
        unchanged[BrowsingContext, sessionHistory] 
        unchanged[BrowsingContext - nbc, isSecureContext]
        unchanged[BrowsingContext - nbc, isSandboxed]
        unchanged[BrowsingContext - nbc, sandboxWaitingNavigate]
        unchanged[BrowsingContext, opening] 
        unchanged[BrowsingContext, accesses]
        unchanged[Document, (Document <: src)] 
        unchanged[Document, elements]  
        unchanged[Script, (Script <: context)]
        unchanged[NonActive, (NonActive <: context)]
        
}


pred unchangedCreateIframeNested [rbc : BrowsingContext, nbc : BrowsingContext,  d : Document, rd : Document] {
        

        unchanged[Browser, bcs]
        unchanged[Browser, blobs] 
        unchanged[BrowsingContext - (nbc + nbc.^nestedBcs'), (BrowsingContext <: origin)]
        unchanged[BrowsingContext - (nbc + nbc.^nestedBcs'), currentDoc] 
        unchanged[BrowsingContext - (rbc + nbc + nbc.^nestedBcs'), nestedBcs] 
        unchanged[BrowsingContext - (nbc + nbc.^nestedBcs'), sessionHistory] 
        unchanged[BrowsingContext - (nbc + nbc.^nestedBcs'), isSecureContext]
        unchanged[BrowsingContext - (nbc + nbc.^nestedBcs'), isSandboxed]
        unchanged[BrowsingContext, sandboxWaitingNavigate]
        unchanged[BrowsingContext, opening] 
        unchanged[BrowsingContext, accesses]
        unchanged[Document - d, (Document <: src)] 
        unchanged[Document - (d + rd), elements] 
        unchanged[Script - (d.elements & Script), (Script <: context)]
        unchanged[NonActive - (d.elements & NonActive), (NonActive <: context)]
         
        
}

pred unchangedCreateIframe [rbc : BrowsingContext, nbc : BrowsingContext,  d : Document, rd : Document] {

        unchanged[Browser, bcs]
        unchanged[Browser, blobs] 
        unchanged[BrowsingContext - nbc, (BrowsingContext <: origin)] 
        unchanged[BrowsingContext - nbc, currentDoc] 
        unchanged[BrowsingContext - rbc, nestedBcs] 
        unchanged[BrowsingContext - nbc, sessionHistory] 
        unchanged[BrowsingContext - nbc, isSecureContext]
        unchanged[BrowsingContext - nbc, isSandboxed]
        unchanged[BrowsingContext, sandboxWaitingNavigate]
        unchanged[BrowsingContext, opening] 
        unchanged[BrowsingContext, accesses]
        unchanged[Document - d, (Document <: src)] 
        unchanged[Document - (d + rd), elements] 
        unchanged[Script - (d.elements & Script), (Script <: context)]
        unchanged[NonActive - (d.elements & NonActive), (NonActive <: context)]
        

}

pred unchangedCreateIframeRaw [nbc : BrowsingContext,  d : Document] {

        unchanged[Browser, bcs]
        unchanged[Browser, blobs] 
        unchanged[BrowsingContext - nbc, (BrowsingContext <: origin)] 
        unchanged[BrowsingContext - nbc, currentDoc] 
        unchanged[BrowsingContext, nestedBcs] 
        unchanged[BrowsingContext - nbc, sessionHistory] 
        unchanged[BrowsingContext - nbc, isSecureContext]
        unchanged[BrowsingContext - nbc, isSandboxed]
        unchanged[BrowsingContext - nbc, sandboxWaitingNavigate]
        unchanged[BrowsingContext, opening] 
        unchanged[BrowsingContext, accesses]
        unchanged[Document - d, (Document <: src)] 
        unchanged[Document - d, elements] 
        unchanged[Script - (d.elements & Script), (Script <: context)]
        unchanged[NonActive - (d.elements & NonActive), (NonActive <: context)]
        

}

pred no_change {
	    unchanged[Browser, bcs]
	    unchanged[Browser, blobs] 
	    unchanged[BrowsingContext, (BrowsingContext <: origin)]
	    unchanged[BrowsingContext, currentDoc]
	    unchanged[BrowsingContext, nestedBcs]
	    unchanged[BrowsingContext, sessionHistory]
            unchanged[BrowsingContext, isSecureContext] 
            unchanged[BrowsingContext, isSandboxed]
            unchanged[BrowsingContext, sandboxWaitingNavigate]
	    unchanged[BrowsingContext, opening]
            unchanged[BrowsingContext, accesses]
	    unchanged[Document, (Document <: src)]
	    unchanged[Document, elements]
	    unchanged[History, (History <: next)] 
	    unchanged[History, (History <: prev)]
            unchanged[Script, (Script <: context)]
            unchanged[NonActive, (NonActive <: context)]
            
}

pred unchangedPopup [nbc : BrowsingContext, openerBc : BrowsingContext, d : Document] {

        unchanged[Browser, blobs] 
        unchanged[BrowsingContext - nbc, (BrowsingContext <: origin)] 
        unchanged[BrowsingContext - nbc, currentDoc] 
        unchanged[BrowsingContext, nestedBcs] 
        unchanged[BrowsingContext - nbc, sessionHistory] 
        unchanged[BrowsingContext - nbc, isSecureContext]
        unchanged[BrowsingContext, isSandboxed]
        unchanged[BrowsingContext, sandboxWaitingNavigate]
        unchanged[BrowsingContext - openerBc, opening] 
        unchanged[BrowsingContext, accesses]
        unchanged[Document, (Document <: src)] 
        unchanged[Document - d, elements] 
        unchanged[Script - (d.elements & Script), (Script <: context)]
        unchanged[NonActive - (d.elements & NonActive), (NonActive <: context)]
        
}


pred unchangedPopupNested [nbc : BrowsingContext, openerBc : BrowsingContext ] {

        unchanged[Browser, blobs] 
        unchanged[BrowsingContext - (nbc + nbc.^nestedBcs'), (BrowsingContext <: origin)]
	unchanged[BrowsingContext - (nbc + nbc.^nestedBcs'), currentDoc]  
        unchanged[BrowsingContext - (nbc + nbc.^nestedBcs'), nestedBcs]  
        unchanged[BrowsingContext - (nbc + nbc.^nestedBcs'), sessionHistory]  
        unchanged[BrowsingContext - (nbc + nbc.^nestedBcs'), isSecureContext]  
        unchanged[BrowsingContext - nbc.^nestedBcs', isSandboxed]
        unchanged[BrowsingContext, sandboxWaitingNavigate]
	unchanged[BrowsingContext - openerBc, opening]
        unchanged[BrowsingContext, accesses]
	unchanged[Document, (Document <: src)]
	unchanged[Document, elements]
        unchanged[Script, (Script <: context)]
        unchanged[NonActive, (NonActive <: context)]
	

}

pred unchangedCreateBlob {
            unchanged[Browser, bcs]
            unchanged[BrowsingContext, (BrowsingContext <: origin)]
            unchanged[BrowsingContext, currentDoc]
            unchanged[BrowsingContext, nestedBcs]
            unchanged[BrowsingContext, sessionHistory]
            unchanged[BrowsingContext, isSecureContext] 
            unchanged[BrowsingContext, isSandboxed]
            unchanged[BrowsingContext, sandboxWaitingNavigate]
            unchanged[BrowsingContext, opening]
            unchanged[BrowsingContext, accesses]
            unchanged[Document, (Document <: src)]
            unchanged[Document, elements]
            unchanged[History, (History <: next)] 
            unchanged[History, (History <: prev)] 
            unchanged[Script, (Script <: context)]  
            unchanged[NonActive, (NonActive <: context)]
            
}