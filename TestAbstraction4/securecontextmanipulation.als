module securecontextmanipulation


open scmCallFunction
open concreteBrowser
--open concreteTrust
open concreteNavigate
open concretePopup
open concreteCreateIframe


pred navigateAbsUrlDeny [f : Function, c : Call] {
    let nbc = f.bc | let u = f.(Navigate <: url) | 
        let rbc = f.bc.~nestedBcs |
        let d = f.(Navigate <: response) |
        let d2 = nbc.currentDoc |
        --let w = f.bc.window |

        --(some d2 implies d = d2) and

        --(some d2 implies d = d2) and

        u in valid_absolute_url and

        nbc.win in Iframe and

        some c.to.xframeOptions[d] and 
        ((c.to.xframeOptions[d].option = Deny) or (c.to.xframeOptions[d].option = SameOrigin and rbc.origin != c.to.origin )) and

        ---the opposite should be here also

        navigateAbsoluteUrlDeny[ nbc, d, d2, u, c.to] and 
        d = c.to.resources[u.path <: DirectoryPath] and 
        c.to in Server and 
        c.to in Dns.map[u.authority.domain] --and 
        --no c.returns --and 
        --unchanged[nbc, sessionHistory] and
        --unchanged[w, accesses]

}

pred navigateAbsUrlNoDeny [f : Function, c : Call] {
    one sh : History |
    let nbc = f.bc | let u = f.(Navigate <: url) | 
        --let rbc = f.bc.~nestedBcs |
        let d = f.(Navigate <: response) |
        let d2 = nbc.currentDoc |
        --let w = f.bc.window |

        --(some d2 implies d = d2) and

        (some d2 implies d = d2) and

        addToSessionHistory[nbc, sh, u] and
        some d and
        --no c.from and 
        nbc.accesses' = none and
        nbc.opening' = none and

        resetIframe[d2] and

        u in valid_absolute_url and

        nbc.win in Iframe and

        c.to.xframeOptions[d] = none and


        navigateAbsoluteUrl[ nbc, d, d2, u, c.to] and 
        d = c.to.resources[u.path <: DirectoryPath] and 
        c.to in Server and 
        c.to in Dns.map[u.authority.domain] --and 
        --no c.returns --and 
        --unchanged[nbc, sessionHistory] and
        --unchanged[w, accesses]

}

pred navigate [f : Function, c : Call] {
        one sh : History |
            let nbc = f.bc | let u = f.(Navigate <: url) | 
            let d = f.(Navigate <: response) |
            let d2 = nbc.currentDoc |
            --let w = f.bc.window |


        --d !in (BrowsingContext.currentDoc - d2) and

        --d = d2 and

        --u !in valid_absolute_url and

        (some d2 implies d = d2) and

        addToSessionHistory[nbc, sh, u] and
        some d and
        --no c.from and 
        nbc.accesses' = none and
        nbc.opening' = none and

        resetIframe[d2] and

        --((w in Iframe and u in valid_absolute_url) implies no c.to.xframeOptions[d]) and

        /*(d2 != d implies (

            d2.elements' = none

        )) and*/
        
        (
            (navigateAbsoluteUrl[ nbc, d, d2, u, c.to] and nbc.win in TopLWindow and d = c.to.resources[f.(Navigate <: url).path <: DirectoryPath] and c.to in Server and c.to in Dns.map[f.(Navigate <: url).authority.domain] ) or 
            (navigateDataHtmlUrl[ nbc,  d, d2, u] and c.to in Browser ) or 
            (navigateDataScriptUrl[ nbc, d, d2, u] and c.to in Browser ) or 
            (navigateBlobBlobsHtmlUrl[ nbc,  d2, d, u, BrowsingContext] and c.to in Browser ) or 
            (navigateBlobBlobsScriptUrl[ nbc,  d, d2, u, BrowsingContext] and c.to in Browser ) or 
            (navigateBlobNoBlobsUrl[  nbc,  d, d2, u, BrowsingContext] and c.to in Browser ) or 
            (navigateAboutUrl[  nbc,  d, d2, u] and c.to in Browser ) or 
            (navigateErrorUrl[  nbc,  d, d2, u, valid_url] and c.to in Browser )
        ) --and 
        --unchanged[Window, accesses]


}

pred navigateBlobTuple [f : Function, c : Call] {
    
    let nbc = f.bc | let u = f.(Navigate <: url) |

        nbc.win in Iframe and
        u in valid_blob_url and
        u in Browser.blobs[BrowsingContext] and 
        nbc.origin in TupleOrigin and
        nbc.origin != u.path.creator_origin and 
        no_change

}

pred navigateBlobNoTuple [f : Function, c : Call] {
    

    let nbc = f.bc | let u = f.(Navigate <: url) |

        nbc.win in Iframe and
        u in valid_blob_url and
        u !in Browser.blobs[nbc] and 
        nbc.origin !in TupleOrigin and
        no_change


}

pred navigateBlobNoBlobs [f : Function, c : Call] {

    let nbc = f.bc | let u = f.(Navigate <: url) |

        nbc.win in Iframe and
        u in valid_blob_url and
        u !in Browser.blobs[BrowsingContext] and 
        no_change
}

pred navigateBlobSchemeNoChange [f : Function, c : Call] {

    let nbc = f.bc | let u = f.(Navigate <: url) |

        nbc.win in Iframe and
        u !in valid_blob_url and
        u.scheme in Blob and 
        no_change
}



pred popup [f : Function, c : Call] {


    let nbc = f.bc |
        let nbc2 = f.(Popup <: newBc) |
        let d = f.(Popup <: response) |
        --let nw = f.(Popup <: win) | 
        --let w = f.bc.window |
        let u = f.(Popup <: url) |

        nbc2 !in Browser.bcs and
        Browser.bcs' = Browser.bcs + nbc2 and 
        --nw = nbc2.window and 
        --nw.bc = nbc2 and 

        --nw.opener = w and 
        nbc.opening' = nbc.opening + nbc2 and 

        f.bc != nbc2 and
        f.party != nbc2 and

        d !in (BrowsingContext.currentDoc) and

        (
            (popupAbsoluteUrl[nbc2, nbc, d, u ] and c.to in Server and c.to in Dns.map[u.authority.domain] and d = c.to.resources[u.path <: DirectoryPath]  ) or 
            (popupDataHtmlUrl[nbc2, nbc, d, u ] and c.to in Browser  ) or 
            (popupDataScriptUrl[ nbc2, nbc, d, u ] and c.to in Browser  ) or 
            (popupTupleOriginBlobBlobsHtmlUrl[ nbc2, nbc, d, BrowsingContext, u ] and c.to in Browser ) or 
            (popupTupleOriginBlobBlobsScriptUrl[ nbc2, nbc, d, BrowsingContext, u ] and c.to in Browser ) or 
            (popupNonTupleOriginBlobBlobsHtmlUrl[ nbc2, nbc, d, f.bc, u ] and c.to in Browser ) or 
            (popupNonTupleOriginBlobBlobsScriptUrl[ nbc2, nbc, d, f.bc, u ] and c.to in Browser ) or 
            (popupTupleOriginErrorUrl[ nbc2, nbc, d, BrowsingContext, u ] and c.to in Browser ) or
            --popupBlobNoBlobsUrl[f, c, nbc2, nbc, d , sh] or 
            (popupAboutUrl[ nbc2, nbc, d, u ] and c.to in Browser ) or 
            (popupErrorUrl[ nbc2, nbc, d, u ] and c.to in Browser )
        )
}


pred popupTupleDifferentOriginBlobNoChange [f : Function, c : Call] {
    f.(Popup <: url) in valid_blob_url and
    ((f.bc.origin in TupleOrigin and origin[f.(Popup <: url)] != f.bc.origin)) and 
    no_change
}
/*
pred popupNoBlobNoChange [f : Function, c : Call] {
    f.(Popup <: url) in valid_blob_url and
    f.(Popup <: url) !in Browser.blobs[BrowsingContext]
    no_change
}*/

pred popupNonTupleDifferentBcBlobNoChange [f : Function, c : Call] {
    f.(Popup <: url) in valid_blob_url and
    f.bc.origin !in TupleOrigin and 
    f.(Popup <: url) !in Browser.blobs[f.bc] and 
    no_change
}


pred create_iframe [f : Function, c : Call] {

    one sh : History |
        let nbc = f.bc |
        let nbc3 = f.(CreateIframe <: newBc) |
        let d1 = f.(CreateIframe <: response) |
        --let w3 = f.(CreateIframe <: win) |
        let u = f.(CreateIframe <: url) |

        nbc3 !in Browser.bcs and 
        nbc3 !in BrowsingContext.^nestedBcs and

        nbc.nestedBcs' = nbc.nestedBcs + nbc3 and 
        nbc.currentDoc.elements' = nbc.currentDoc.elements + d1 and
        --nbc3.window' = w3 and 
        --w3.doc' = d1 and 

        d1 !in (BrowsingContext.currentDoc) and

        addToSessionHistory[nbc3, sh, u] and
        
        (
            (createIframeAbsoluteUrl[ nbc, nbc3,  d1, u, c.to] and d1 = c.to.resources[u.path <: DirectoryPath] and c.to in Server and c.to in Dns.map[u.authority.domain] ) or 
            (createIframeDataHtmlUrl[  nbc, nbc3,  d1, u] and c.to in Browser ) or 
            (createIframeDataScriptUrl[  nbc, nbc3,  d1, u] and c.to in Browser ) or 
            (createIframeTupleOriginBlobBlobsHtmlUrl[  nbc, nbc3,  d1, u, BrowsingContext] and c.to in Browser ) or 
            (createIframeTupleOriginBlobBlobsScriptUrl[  nbc, nbc3,  d1, u, BrowsingContext] and c.to in Browser ) or 
            (createIframeNonTupleOriginBlobBlobsHtmlUrl[  nbc, nbc3,  d1, u, nbc] and c.to in Browser ) or
            (createIframeNonTupleOriginBlobBlobsScriptUrl[  nbc, nbc3,  d1, u, nbc] and c.to in Browser ) or
            (createIframeChromeAboutUrl[ nbc, nbc3,  d1, u] and c.to in Browser ) or 
            (createIframeSafariAboutUrl[ nbc, nbc3,  d1, u] and c.to in Browser ) or 
            (createIframeChromeInvalidDataAbsoluteUrl[nbc, nbc3,  d1, u] and c.to in Browser ) or
            (createIframeSafariInvalidDataAbsoluteUrl[nbc, nbc3,  d1, u] and c.to in Browser ) --or
            --(createIframeErrorUrl[ nbc, nbc3, w3, d1, u] and c.to in Browser and no c.returns)
        ) 

}

pred createIframeInvalidBlobUrlNoChange [f : Function, c : Call] {

  --always (all f : CreateIframe | 


    f.(CreateIframe <: url) in invalid_blob_url and
    no_change

 -- )
    
}


pred createIframeTupleDifferentOriginBlobNoChange [f : Function, c : Call] {

  --always (all f : CreateIframe | 


    f.(CreateIframe <: url) in valid_blob_url and
    f.bc.origin in TupleOrigin and 
    f.(CreateIframe <: url).path.creator_origin != f.bc.origin and 
    no_change

 -- )
    
}

pred createIframeNoBlobNoChange [f : Function, c : Call] {

  --always (all f : CreateIframe | 
    f.(CreateIframe <: url) in valid_blob_url and
    f.(CreateIframe <: url) !in Browser.blobs[BrowsingContext]  and 
    no_change

  --)
}

pred createIframeNonTupleDifferentBcBlobNoChange [f : Function, c : Call] {

  --always (all f : CreateIframe | 
    f.(CreateIframe <: url) in valid_blob_url and
    f.bc.origin !in TupleOrigin and 
    f.(CreateIframe <: url) !in Browser.blobs[f.bc]  and 
    no_change
  --)
}

pred add_sandbox [f : Function, c : Call] {

    let nbc3 = f.(AddSandbox <: sandBc) |

        nbc3 in f.bc.^nestedBcs and 

        (nbc3.sandboxWaitingNavigate = False or nbc3.sandboxWaitingNavigate = none ) and

        nbc3.sandboxWaitingNavigate' = True and 

        unchanged[Browser, bcs] and
        --unchanged[Browser, cookies] and
        unchanged[Browser, blobs]  and
        unchanged[BrowsingContext, (BrowsingContext <: origin)] and
        --unchanged[BrowsingContext, window] and
        unchanged[BrowsingContext, currentDoc] and
        unchanged[BrowsingContext, nestedBcs] and
        unchanged[BrowsingContext, sessionHistory] and
        unchanged[BrowsingContext, isSecureContext]  and
        unchanged[BrowsingContext, isSandboxed] and
        unchanged[BrowsingContext - nbc3, sandboxWaitingNavigate] and
        --unchanged[Window, doc] and
        unchanged[BrowsingContext, opening] and
        unchanged[BrowsingContext, accesses] and
        unchanged[Document, (Document <: src)] and
        unchanged[Document, elements] and
        unchanged[Script, (Script <: src)] and
        unchanged[Script, (Script <: context)] and
        unchanged[NonActive, (NonActive <: src)] and
        unchanged[NonActive, (NonActive <: context)] and
        --unchanged[DataflowModule, accesses]
        unchanged[History, (History <: next)]  and
        unchanged[History, (History <: prev)]



}



pred document_write_iframeDocument [f : Function, c : Call] {


    let nbc = f.bc |
        let nbc2 = f.targetBc |
        let d2 = f.(DocumentWrite <: newEl) |
        --let w = f.bc.window |
        --let w2 = nbc2.window |

        f.party = nbc and

        ((nbc2 in nbc.nestedBcs and d2 in nbc.currentDoc.elements)
            or 
            (nbc2 in nbc.opening and nbc2 in Browser.bcs) or 
            (nbc in nbc2.opening and nbc2 in Browser.bcs)
        ) and

        d2 = nbc2.currentDoc and

        d2.(Document <: src') = nbc.currentDoc.(Document <: src) and 

        d2.elements' = none and 

        nbc2.accesses' = none and
        nbc2.opening' = none and
        nbc2.~opening.opening' = nbc2.~opening.opening - nbc2 and

        resetIframe[d2] and

        nbc2.origin' = nbc.origin and 
        nbc2.nestedBcs' = none and
     
        unchanged[BrowsingContext - nbc2.^nestedBcs, currentDoc] and 
        unchanged[BrowsingContext - nbc2.^nestedBcs, sessionHistory] and 
        unchanged[BrowsingContext - nbc2.^nestedBcs, isSecureContext] and 
        unchanged[BrowsingContext - (nbc2 + nbc2.^nestedBcs), nestedBcs] and
        unchanged[BrowsingContext - nbc2.^nestedBcs, isSandboxed] and --because there are new elements inside
        unchanged[BrowsingContext - nbc2.^nestedBcs, sandboxWaitingNavigate] and
        unchanged[Document - d2, (Document <: src)] and
        unchanged[Document - (d2 + (d2.^elements <: Document) ), elements] and 
        unchanged[Script, (Script <: src)] and 
        unchanged[Script - (d2.^elements <: Script), (Script <: context)] and
        unchanged[NonActive, (NonActive <: src)] and
        unchanged[NonActive - (d2.^elements <: NonActive), (NonActive <: context)] and 
        unchanged[Browser, bcs] and
        --unchanged[Browser, cookies] and
        unchanged[Browser, blobs] and
        unchanged[BrowsingContext - (nbc2 + nbc2.^nestedBcs), (BrowsingContext <: origin)] and
        --unchanged[BrowsingContext, window] and
        --unchanged[Window - nbc2.^nestedBcs.window, doc] and
        unchanged[BrowsingContext - (nbc2 + nbc2.~opening + nbc2.^nestedBcs), opening] and
        unchanged[BrowsingContext - (nbc2 + nbc2.^nestedBcs), accesses] and 
        unchanged[History, (History <: next)]  and
        unchanged[History, (History <: prev)]
    
        

}

pred document_write_iframeScript [f : Function, c : Call] {

    let nbc = f.bc |
        let nbc2 = f.targetBc |
        --let w = f.bc.window |
        --let w2 = nbc2.window |
        let d2 = nbc2.currentDoc |
        let el = f.(DocumentWrite <: newEl) |

        f.party = nbc and

        ((nbc2 in nbc.nestedBcs and d2 in nbc.currentDoc.elements)
            or 
            (nbc2 in nbc.opening and nbc2 in Browser.bcs) or 
            (nbc in nbc2.opening and nbc2 in Browser.bcs)
        ) and


        el !in Document.elements and

        el !in Document and

        el in (Script + NonActive) and

        d2.elements' = el and 

        nbc2.accesses' = none and
        nbc2.opening' = none and
        nbc2.~opening.opening' = nbc2.~opening.opening - nbc2 and

        resetIframe[d2] and

        nbc2.nestedBcs' = none and
            
        d2.src' = nbc.currentDoc.src and 
        nbc2.origin' = nbc.origin and 
        unchanged[BrowsingContext - nbc2.^nestedBcs, currentDoc] and 
        unchanged[BrowsingContext - nbc2.^nestedBcs, sessionHistory] and 
        unchanged[BrowsingContext - nbc2.^nestedBcs, isSecureContext] and 
        unchanged[BrowsingContext - (nbc2 + nbc2.^nestedBcs), nestedBcs] and
        unchanged[BrowsingContext - nbc2.^nestedBcs, isSandboxed] and 
        unchanged[BrowsingContext - nbc2.^nestedBcs, sandboxWaitingNavigate] and
        unchanged[Document - d2, (Document <: src)] and
        unchanged[Document - (d2 + (d2.^elements <: Document) ), elements] and 
        unchanged[Script, (Script <: src)] and 
        unchanged[NonActive, (NonActive <: src)] and

        (el in Script implies (
            el.(Script <: context)' = d2 and
            unchanged[Script - (el + (d2.^elements <: Script) ), (Script <: context)] and
            unchanged[NonActive - (d2.^elements <: NonActive), (NonActive <: context)] 
        )else (
            el.(NonActive <: context)' = d2 and
            unchanged[Script - (d2.^elements <: Script), (Script <: context)] and
            unchanged[NonActive - (el + (d2.^elements <: NonActive) ), (NonActive <: context)] 
        )) and 
        unchanged[Browser, bcs] and
        --unchanged[Browser, cookies] and
        unchanged[Browser, blobs] and
        unchanged[BrowsingContext - (nbc2 + nbc2.^nestedBcs), (BrowsingContext <: origin)] and
        --unchanged[BrowsingContext, window] and
        --unchanged[Window - nbc2.^nestedBcs.window, doc] and
        unchanged[BrowsingContext - (nbc2 + nbc2.~opening + nbc2.^nestedBcs), opening] and
        unchanged[BrowsingContext - (nbc2 + nbc2.^nestedBcs), accesses] and 
        unchanged[History, (History <: next)]  and
        unchanged[History, (History <: prev)]


}




fact {

  /*always (all f : DocumentWrite |

      f.bc.currentDoc.src = f.targetBc.currentDoc.src implies no_change


  )*/
}

/*
fact document_write_iframeUnchanged  {
    always (all f : DocumentWrite | one rbc : BrowsingContext | one nbc : BrowsingContext | 

        (f.rootBc = rbc and

        f.bc = nbc and
        (nbc = rbc or nbc in rbc.^nestedBcs) and

         --and 
        (rbc !in Browser.bcs or no nbc.nestedBcs or no nbc.window.opening or no nbc.window.~opening)) implies no_change
    )

}


fact document_write_iframeUnchanged {
  always (all f : DocumentWrite | 
        (f.(DocumentWrite <: newEl) in (Document.elements + Window.doc) and

        f.(DocumentWrite <: newEl) in Document) implies no_change

  )
}

fact document_write_iframeUnchanged {
  always (all f : DocumentWrite |
        (f.(DocumentWrite <: newEl) in (Document.elements ) and

        f.(DocumentWrite <: newEl) !in Document ) implies no_change
  )
}

fact {
    always (all f : DocumentWrite | f.bc != f.targetBc )
}*/


pred access_to_media [f : Function, c : Call] {


    let nbc = f.bc |
        --let w = f.canAccess |

        f.canAccess = nbc and

        nbc.accesses' = nbc.accesses + f.media and 

        unchanged[Browser, bcs] and
        --unchanged[Browser, cookies] and
        unchanged[Browser, blobs]  and
        unchanged[BrowsingContext, (BrowsingContext <: origin)] and
        --unchanged[BrowsingContext, window] and
        unchanged[BrowsingContext, currentDoc] and
        unchanged[BrowsingContext, nestedBcs] and
        unchanged[BrowsingContext, sessionHistory] and
        unchanged[BrowsingContext, isSecureContext]  and
        unchanged[BrowsingContext, isSandboxed] and
        unchanged[BrowsingContext, sandboxWaitingNavigate] and
        --unchanged[Window, doc] and
        unchanged[BrowsingContext, opening] and
        unchanged[BrowsingContext - nbc, accesses] and
        unchanged[Document, (Document <: src)] and
        unchanged[Document, elements] and
        unchanged[Script, (Script <: src)] and
        unchanged[Script, (Script <: context)] and
        unchanged[NonActive, (NonActive <: src)] and
        unchanged[NonActive, (NonActive <: context)] and
        --unchanged[DataflowModule, accesses]
        unchanged[History, (History <: next)]  and
        unchanged[History, (History <: prev)]

        
}


fact sopMediaAccess {
    always (
        all f : Access2Media | 
        let nbc = f.bc | let m = f.media |
        let dom = find_domain[nbc.currentDoc.src] |


            f.canAccess = nbc implies (

                nbc in Browser.bcs and

                nbc.currentDoc.src in valid_url and

                --nbc.currentDoc.src.authority.domain in m.permitted and 
                some dom and dom in m.permitted and
                decideUltimateSecureContext[nbc] = True  
            )
            

            --w.accesses' = w.accesses + f.media
    )
}

/*pred no_operation {
    
    no_change
}*/

