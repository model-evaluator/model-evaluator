module frameConditions

--open concreteUrl
open concreteBrowser
--open orderings
--open concreteCallFunction


pred unchangedNavigateAbsolute[nbc : BrowsingContext, d : Document] {
            unchanged[Browser, bcs]
            --unchanged[Browser, cookies]
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
            unchanged[Script, (Script <: src)]
            unchanged[Script, (Script <: context)]
            unchanged[NonActive, (NonActive <: src)]
            unchanged[NonActive, (NonActive <: context)]
            --unchanged[DataflowModule, accesses]
            --unchanged[Calls, (Calls <: prev)]
            --unchanged[Calls, (Calls <: prevs)]
            
}

pred unchangedNavigate [nbc : BrowsingContext, d : Document, d2 : Document] {

        unchanged[Browser, bcs]
        --unchanged[Browser, cookies] --TODO(BrowsingContext <: origin
        unchanged[Browser, blobs] 
        unchanged[BrowsingContext - (nbc + nbc.^nestedBcs), (BrowsingContext <: origin)] 
        --unchanged[BrowsingContext, window] 
        unchanged[BrowsingContext - (nbc + nbc.^nestedBcs), currentDoc] 
        unchanged[BrowsingContext - (nbc + nbc.^nestedBcs), nestedBcs] 
        unchanged[BrowsingContext - (nbc + nbc.^nestedBcs), sessionHistory] 
        unchanged[BrowsingContext - (nbc + nbc.^nestedBcs), isSecureContext]
        unchanged[BrowsingContext - (nbc + nbc.^nestedBcs), isSandboxed]
        unchanged[BrowsingContext - (nbc + nbc.^nestedBcs), sandboxWaitingNavigate]
        --unchanged[Window - (w + nbc.^nestedBcs.window ), doc] 
        unchanged[BrowsingContext - (nbc + nbc.^nestedBcs), opening] 
        unchanged[BrowsingContext - (nbc + nbc.^nestedBcs ), accesses]
        unchanged[Document - d, (Document <: src)] 
        unchanged[Document - (d + d2 + (d2.^elements <: Document)), elements] 
        unchanged[Script, (Script <: src)] 
        unchanged[Script - (d2.^elements <: Script), (Script <: context)] 
        --unchanged[DataflowModule, accesses]
        

}

pred unchangedNavigateNested [nbc : BrowsingContext, d : Document, d2 : Document] {
        unchanged[NonActive, (NonActive <: src)] 
        unchanged[NonActive - (d2.elements <: NonActive), (NonActive <: context)]

        unchanged[Browser, bcs]
        --unchanged[Browser, cookies] --TODO(BrowsingContext <: origin
        unchanged[Browser, blobs] 
        unchanged[BrowsingContext - (nbc + nbc.^nestedBcs), (BrowsingContext <: origin)] 
        --unchanged[BrowsingContext, window] 
        unchanged[BrowsingContext - (nbc + nbc.^nestedBcs), currentDoc] 
        unchanged[BrowsingContext - (nbc + nbc.^nestedBcs), nestedBcs] 
        unchanged[BrowsingContext - (nbc + nbc.^nestedBcs), sessionHistory] 
        unchanged[BrowsingContext - (nbc + nbc.^nestedBcs), isSecureContext]
        unchanged[BrowsingContext - (nbc + nbc.^nestedBcs), isSandboxed]
        unchanged[BrowsingContext - nbc, sandboxWaitingNavigate]
        --unchanged[Window - (w + nbc.^nestedBcs.window), doc] -- TODO 
        unchanged[BrowsingContext - (nbc + nbc.^nestedBcs), opening] 
        unchanged[BrowsingContext - (nbc + nbc.^nestedBcs), accesses]
        unchanged[Document - d, (Document <: src)] 
        unchanged[Document - (d + d2 + (d2.^elements <: Document)), elements] 
        unchanged[Script, (Script <: src)] 
        unchanged[Script - (d2.^elements <: Script), (Script <: context)] 
        --unchanged[DataflowModule, accesses]  
        
}


pred unchangedAbsNavSafariXFOptionsNested [nbc : BrowsingContext] {
        unchanged[NonActive, (NonActive <: src)] 
        unchanged[NonActive, (NonActive <: context)]

        unchanged[Browser, bcs]
        --unchanged[Browser, cookies] --TODO(BrowsingContext <: origin
        unchanged[Browser, blobs] 
        unchanged[BrowsingContext - nbc, (BrowsingContext <: origin)] 
        --unchanged[BrowsingContext, window] 
        unchanged[BrowsingContext, currentDoc] 
        unchanged[BrowsingContext, nestedBcs] 
        unchanged[BrowsingContext, sessionHistory] 
        unchanged[BrowsingContext - nbc, isSecureContext]
        unchanged[BrowsingContext - nbc, isSandboxed]
        unchanged[BrowsingContext - nbc, sandboxWaitingNavigate]
        --unchanged[Window, doc] -- TODO 
        unchanged[BrowsingContext, opening] 
        unchanged[BrowsingContext, accesses]
        unchanged[Document, (Document <: src)] 
        unchanged[Document, elements] 
        unchanged[Script, (Script <: src)] 
        unchanged[Script, (Script <: context)] 
        --unchanged[DataflowModule, accesses]  
        
}


pred unchangedCreateIframeNested [rbc : BrowsingContext, nbc : BrowsingContext,  d : Document, rd : Document] {
        unchanged[NonActive, (NonActive <: src)] 
        unchanged[NonActive, (NonActive <: context)]

        unchanged[Browser, bcs]
        --unchanged[Browser, cookies] --TODO(BrowsingContext <: origin
        unchanged[Browser, blobs] 
        unchanged[BrowsingContext - (nbc + nbc.^nestedBcs'), (BrowsingContext <: origin)] 
        --unchanged[BrowsingContext, window] 
        unchanged[BrowsingContext - (nbc + nbc.^nestedBcs'), currentDoc] 
        unchanged[BrowsingContext - (rbc + nbc + nbc.^nestedBcs'), nestedBcs] 
        unchanged[BrowsingContext - (nbc + nbc.^nestedBcs'), sessionHistory] 
        unchanged[BrowsingContext - (nbc + nbc.^nestedBcs'), isSecureContext]
        unchanged[BrowsingContext - (nbc + nbc.^nestedBcs'), isSandboxed]
        unchanged[BrowsingContext, sandboxWaitingNavigate]
        --unchanged[Window - (w + nbc.^nestedBcs'.window), doc] -- TODO 
        unchanged[BrowsingContext, opening] 
        unchanged[BrowsingContext, accesses]
        unchanged[Document - d, (Document <: src)] 
        unchanged[Document - (d + rd), elements] 
        unchanged[Script, (Script <: src)] 
        unchanged[Script, (Script <: context)] 
        --unchanged[DataflowModule, accesses]  
        
}

pred unchangedCreateIframe [rbc : BrowsingContext, nbc : BrowsingContext,  d : Document, rd : Document] {

        unchanged[Browser, bcs]
        --unchanged[Browser, cookies] --TODO(BrowsingContext <: origin
        unchanged[Browser, blobs] 
        unchanged[BrowsingContext - nbc, (BrowsingContext <: origin)] 
        --unchanged[BrowsingContext, window] 
        unchanged[BrowsingContext - nbc, currentDoc] 
        unchanged[BrowsingContext - rbc, nestedBcs] 
        unchanged[BrowsingContext - nbc, sessionHistory] 
        unchanged[BrowsingContext - nbc, isSecureContext]
        unchanged[BrowsingContext - nbc, isSandboxed]
        unchanged[BrowsingContext, sandboxWaitingNavigate]
        --unchanged[Window - w, doc] 
        unchanged[BrowsingContext, opening] 
        unchanged[BrowsingContext, accesses]
        unchanged[Document - d, (Document <: src)] 
        unchanged[Document - (d + rd), elements] 
        unchanged[Script, (Script <: src)] 
        unchanged[Script, (Script <: context)] 
        --unchanged[DataflowModule, accesses]
        

}

pred unchangedCreateIframeRaw [nbc : BrowsingContext,  d : Document] {

        unchanged[Browser, bcs]
        --unchanged[Browser, cookies] --TODO(BrowsingContext <: origin
        unchanged[Browser, blobs] 
        unchanged[BrowsingContext - nbc, (BrowsingContext <: origin)] 
        --unchanged[BrowsingContext, window] 
        unchanged[BrowsingContext - nbc, currentDoc] 
        unchanged[BrowsingContext, nestedBcs] 
        unchanged[BrowsingContext - nbc, sessionHistory] 
        unchanged[BrowsingContext - nbc, isSecureContext]
        unchanged[BrowsingContext - nbc, isSandboxed]
        unchanged[BrowsingContext - nbc, sandboxWaitingNavigate]
        --unchanged[Window - w, doc] 
        unchanged[BrowsingContext, opening] 
        unchanged[BrowsingContext, accesses]
        unchanged[Document - d, (Document <: src)] 
        unchanged[Document - d, elements] 
        unchanged[Script, (Script <: src)] 
        unchanged[Script, (Script <: context)] 
        --unchanged[DataflowModule, accesses]
        

}

pred no_change {
	    unchanged[Browser, bcs]
	    --unchanged[Browser, cookies]
	    unchanged[Browser, blobs] 
	    unchanged[BrowsingContext, (BrowsingContext <: origin)]
	    --unchanged[BrowsingContext, window]
	    unchanged[BrowsingContext, currentDoc]
	    unchanged[BrowsingContext, nestedBcs]
	    unchanged[BrowsingContext, sessionHistory]
            unchanged[BrowsingContext, isSecureContext] 
            unchanged[BrowsingContext, isSandboxed]
            unchanged[BrowsingContext, sandboxWaitingNavigate]
	    --unchanged[Window, doc]
	    unchanged[BrowsingContext, opening]
            unchanged[BrowsingContext, accesses]
	    unchanged[Document, (Document <: src)]
	    unchanged[Document, elements]
	    unchanged[Script, (Script <: src)]
	    unchanged[Script, (Script <: context)]
	    unchanged[NonActive, (NonActive <: src)]
	    unchanged[NonActive, (NonActive <: context)]
	    --unchanged[DataflowModule, accesses]
	    unchanged[History, (History <: next)] 
	    unchanged[History, (History <: prev)]
	    --unchanged[Calls, (Calls <: prev)]
	    --unchanged[Calls, (Calls <: prevs)]
            
}

pred unchangedPopup [nbc : BrowsingContext, openerBc : BrowsingContext, d : Document] {

        --unchanged[Browser, cookies] --TODO(BrowsingContext <: origin
        unchanged[Browser, blobs] 
        unchanged[BrowsingContext - nbc, (BrowsingContext <: origin)] 
        --unchanged[BrowsingContext, window] 
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
        unchanged[Script, (Script <: src)] 
        unchanged[Script, (Script <: context)] 
        --unchanged[DataflowModule, accesses]
}


pred unchangedPopupNested [nbc : BrowsingContext, openerBc : BrowsingContext ] {

        --unchanged[Browser, cookies]
        unchanged[Browser, blobs] 
        unchanged[BrowsingContext - (nbc + nbc.^nestedBcs'), (BrowsingContext <: origin)]
        --unchanged[BrowsingContext, win]
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
	unchanged[Script, (Script <: src)]
	unchanged[Script, (Script <: context)]
	unchanged[NonActive, (NonActive <: src)]
	unchanged[NonActive, (NonActive <: context)]
	--unchanged[DataflowModule, accesses]

}

pred unchangedCreateBlob {
            unchanged[Browser, bcs]
            --unchanged[Browser, cookies]
            --unchanged[Browser, blobs] 
            unchanged[BrowsingContext, (BrowsingContext <: origin)]
            --unchanged[BrowsingContext, window]
            unchanged[BrowsingContext, currentDoc]
            unchanged[BrowsingContext, nestedBcs]
            unchanged[BrowsingContext, sessionHistory]
            unchanged[BrowsingContext, isSecureContext] 
            unchanged[BrowsingContext, isSandboxed]
            unchanged[BrowsingContext, sandboxWaitingNavigate]
            --unchanged[Window, doc]
            unchanged[BrowsingContext, opening]
            unchanged[BrowsingContext, accesses]
            unchanged[Document, (Document <: src)]
            unchanged[Document, elements]
            unchanged[Script, (Script <: src)]
            unchanged[Script, (Script <: context)]
            unchanged[NonActive, (NonActive <: src)]
            unchanged[NonActive, (NonActive <: context)]
            --unchanged[DataflowModule, accesses]
            unchanged[History, (History <: next)] 
            unchanged[History, (History <: prev)]
            
}