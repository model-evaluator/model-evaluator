module scmCallFunction

open browser

var lone abstract sig Call {
    var from : lone (BrowsingContext + Script),
    var to : lone ( BrowsingContext + Browser + Server),
    var args : set HtmlResource,
    var returns : set HtmlResource,
    var event : one Function,
    var urls : set Url
}{
    Url in urls
    
}

var lone abstract sig Function {
    var rootBc : BrowsingContext,
    var bc : BrowsingContext,
    var party : BrowsingContext
}

fact {
    always (all f : Function - WindowOpen | f.rootBc in Browser.bcs and (f.bc = f.rootBc or f.bc in f.rootBc.^nestedBcs) )
    always (all f : Function | 
        (f.party = f.bc ) or  
        (f.party != f.bc and 
            f.party.^~nestedBcs in Browser.bcs and  
            (f.party in f.bc.opening or f.bc in f.party.opening)
        )
    )
    always (all f : Function |
        let nbc2 = f.bc |
        let nbc = f.party |
        
           nbc = nbc2 or sameOriginPolicy[nbc, nbc2]

    )
    always (all f : DocumentWrite | 
        let nbc = f.bc |
        let nbc2 = f.targetBc |

            sameOriginPolicy[nbc, nbc2]
    )

    always (all f : CreateIframe | 
        let nbc = f.bc |
        let nbc2 = f.(CreateIframe <: newBc) |

            sameOriginPolicy[nbc, nbc2]
    )


    always (all f : WindowOpen | let call = f.~event | call.to = Browser and call.from = none ) //in the future call.from could be User!

    always (all f : Navigate | let call = f.~event | 
        call.from = none and
        f.url in AbsoluteUrl implies (
            call.to in Server   
        )else (
            call.to in Browser
        )

    )

    always (all f : LocationReplace | let call = f.~event | 
        call.from = none and
        f.url in AbsoluteUrl implies (
            call.to in Server   
        )else (
            call.to in Browser
        )

    )

    --always (all f : LocationReplace | let call = f.~event | call.to in Server)

    always (all f : HistoryPushState | let call = f.~event | 
        call.to = f.bc 
    )

    always (all f : CreateBlob + Access2Media | let call = f.~event |
        call.to = Browser 
    )

    always (all f : Popup | let call = f.~event |
        call.to = f.(Popup <: newBc)
    )

    always (all f : CreateIframe | let call = f.~event |
        call.to = f.(CreateIframe <: newBc) 
    )

    always (all f : DocumentWrite | let call = f.~event | 
        call.to = f.targetBc 
    )

   always (all f : Skip | let call = f.~event |
        call.from = none and 
        call.to = none
    )

   always (all f : Function - (WindowOpen + LocationReplace + Navigate + Skip) | let call = f.~event |
        some call.from and 
        call.from in f.party.currentDoc.elements and 
        call.from in Script
    )

    always (all f : ReadDom | let call = f.~event | 
        call.to = f.bc and 
        call.args = none and 
        call.returns = f.response
    )

    always (all f : WriteDom | let call = f.~event | 
        call.to = f.bc and 
        call.args = f.(WriteDom <: newEl) and 
        call.returns = none
    )

    always (all f : InjectScript | let call = f.~event |
        call.to = f.bc and 
        call.args = f.newScr and 
        call.returns = none
    )

    always (all f : Function - (ReadDom + WriteDom + InjectScript) | let call = f.~event |
        call.args = none and 
        call.returns = none
    )

}

pred sameOriginPolicy [nbc : BrowsingContext, nbc2 : BrowsingContext] {
        nbc.origin != StartupOrigin and nbc2.origin != StartupOrigin and
        (
            
            (nbc2.currentDoc.src in AboutUrl and nbc.isSandboxed = False and nbc2.isSandboxed = False and nbc.origin = nbc2.origin) or
            (nbc.origin in TupleOrigin and nbc2.origin in TupleOrigin and nbc.origin = nbc2.origin)
        )
}

var lone sig WindowOpen extends Function {}

var lone sig RenderResource extends Function {
    var doc : one Document,
    var newBc : one BrowsingContext
}

var lone sig HistoryPushState extends Function {
    var tarUrl : one (Url + Path),
    var url : one Url
}

var lone sig LocationReplace extends Function {
    var url : one Url,
    var response : lone Document
}

var lone sig CreateBlob extends Function {

    var url : one Url
}

var lone sig ReadDom extends Function {
    var response : (HtmlResource - Script)
}

var lone sig WriteDom extends Function {
    var oldEl : lone HtmlResource,
    var newEl : HtmlResource - Document //create iframe exists already for document option
}

var lone sig InjectScript extends Function {
    var targetDoc : Document,
    var newScr : Script
}


var lone sig Navigate extends Function {
    var url : one Url,
    var response : lone Document
}

var lone sig Popup extends Function {
    var url : one Url,
    var response : lone Document,
    var newBc : one BrowsingContext
}

var lone sig CreateIframe extends Function {
    var url : one Url,
    var response : one Document,
    var newBc : one BrowsingContext
}


var lone sig DocumentWrite extends Function {
    var newEl : one Document, --HtmlResource,
    var targetBc : one BrowsingContext
}

var lone sig Access2Media extends Function {
    var media : one Media,
    var canAccess : lone BrowsingContext

}

var lone sig Skip extends Function {

}
