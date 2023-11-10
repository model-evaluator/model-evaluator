module scmanipulation


open scmCallFunction
open browser
open navigate
open popup
open createIframe


pred navigateAbsUrlDeny [f : Function, c : Call, u : Url, d : Document] {
    let nbc = f.bc | 
        let rbc = f.bc.~nestedBcs |

        let d2 = nbc.currentDoc |


        u in AbsoluteUrl and


        nbc.win in Iframe and

        some c.to.xframeOptions[d] and 
        ((c.to.xframeOptions[d].option = Deny) or (c.to.xframeOptions[d].option = SameOrigin and rbc.origin != c.to.origin )) and


        navigateAbsoluteUrlDeny[ nbc, d, d2, u, c.to] and 
        d = c.to.resources[u.path] and 
        c.to in Server and 
        c.to in Dns.map[u.(AbsoluteUrl <: domain)] 

}

pred navigateAbsUrlNoDeny [f : Function, c : Call, u : Url, d : Document, lr : Boolean] {
    
    let nbc = f.bc | 
        let rbc = f.bc.~nestedBcs |
        let d2 = nbc.currentDoc |

        (some d2 implies d = d2) and

        some d and

        u in AbsoluteUrl and

        nbc.win in Iframe and

        ((c.to.xframeOptions[d] = none) or
        (some c.to.xframeOptions[d] and c.to.xframeOptions[d].option = SameOrigin and rbc.origin = c.to.origin )) and

        (lr = False implies (
            one sh : History |
            addToSessionHistory[nbc, sh, u] 
        )else(
            unchanged[nbc, sessionHistory]
        )) and
        
        


        Browser.blobs' = Browser.blobs - (nbc -> Url + nbc.^nestedBcs -> Url ) and 

        nbc.accesses' = none and
        
        unchanged[nbc, opening] and
        resetIframe[d2] and

        navigateAbsoluteUrl[ nbc, d, d2, u, lr] and 
        d = c.to.resources[u.path] and 
        c.to in Server and 
        c.to in Dns.map[u.(AbsoluteUrl <: domain)] 

}

pred navigate [f : Function, c : Call, u : Url, d : Document, lr : Boolean] {
        
            let nbc = f.bc | 
            let d2 = nbc.currentDoc |

        (some d2 implies d = d2) and


        (lr = False implies (
            one sh : History |
            addToSessionHistory[nbc, sh, u] 
        )else(
            unchanged[nbc, sessionHistory]
        )) and


        some d and

        nbc.accesses' = none and
        unchanged[nbc, opening] and
        Browser.blobs' = Browser.blobs - (nbc -> Url + nbc.^nestedBcs -> Url ) and 

        resetIframe[d2] and

        
        (
            (navigateAbsoluteUrl[ nbc, d, d2, u, lr] and nbc.win in TopLWindow and d = c.to.resources[f.(Navigate <: url).path] and c.to in Server and c.to in Dns.map[f.(Navigate <: url).(AbsoluteUrl <: domain)] ) or 
            (navigateDataUrl[ nbc,  d, d2, u, lr] and c.to in Browser ) or 
            (navigateBlobUrl[ nbc,  d, d2, u, lr] and c.to in Browser ) or 
            (navigateIframeBlobUrl[nbc.~nestedBcs, nbc,  d, d2, u] and c.to in Browser ) or
            (navigateBlobNoBlobsUrl[  nbc,  d, d2, u] and c.to in Browser ) or 
            (navigateAboutUrl[  nbc,  d, d2, u] and c.to in Browser ) or 
            (navigateErrorUrl[  nbc,  d, d2, u, ValidUrl] and c.to in Browser )
        ) 


}




pred popup [f : Function, c : Call] {


    let nbc = f.bc |
        let nbc2 = f.(Popup <: newBc) |
        let d = f.(Popup <: response) |
        let u = f.(Popup <: url) |

        nbc2 !in Browser.bcs and
        Browser.bcs' = Browser.bcs + nbc2 and 

        nbc.origin != StartupOrigin and


        nbc.opening' = nbc.opening + nbc2 and 

        f.bc != nbc2 and
        f.party != nbc2 and

        d !in (BrowsingContext.currentDoc) and

        (
            (popupAbsoluteUrl[nbc2, nbc, d, u ] and c.to in Server and c.to in Dns.map[u.(AbsoluteUrl <: domain)] and d = c.to.resources[u.path]  ) or 
            (popupDataUrl[nbc2, nbc, d, u ] and c.to in Browser  ) or 
            (popupAbsoluteSameOriginBlobUrl[nbc2, nbc, d, u ] and c.to in Browser  ) or 
            (popupAbsoluteCrossOriginBlobUrl[ nbc2, nbc, d, u ] and c.to in Browser ) or 
            (popupBlobBlobUrl[ nbc2, nbc, d, u ] and c.to in Browser ) or 
            (popupDataSameBcNullBlobUrl[ nbc2, nbc, d, u ] and c.to in Browser ) or 
            (popupDataAboutCrossBcNullBlobUrl[ nbc2, nbc, d, u ] and c.to in Browser ) or 
            (popupDataAboutOpenerBcNullBlobUrl[ nbc2, nbc, d, u ] and c.to in Browser ) or 
            (popupDataAboutTupleBlobUrl[ nbc2, nbc, d, u ] and c.to in Browser ) or 
            (popupAboutUrl[ nbc2, nbc, d, u ] and c.to in Browser ) or 
            (popupErrorUrl[ nbc2, nbc, d, u ] and c.to in Browser )
        )
}


pred create_iframe [f : Function, c : Call] {

    one sh : History |
        let nbc = f.bc |
        let nbc3 = f.(CreateIframe <: newBc) |
        let d1 = f.(CreateIframe <: response) |
        let u = f.(CreateIframe <: url) |

        nbc3 !in Browser.bcs and 
        nbc3 !in BrowsingContext.^nestedBcs and

        nbc.nestedBcs' = nbc.nestedBcs + nbc3 and 
        nbc.currentDoc.elements' = nbc.currentDoc.elements + d1 and


        nbc3.win in Iframe and

        d1 !in (BrowsingContext.currentDoc) and

        addToSessionHistory[nbc3, sh, u] and
        
        (
            (createIframeAbsoluteUrl[ nbc, nbc3,  d1, u, c.to] and d1 = c.to.resources[u.path ] and c.to in Server and c.to in Dns.map[u.(AbsoluteUrl <: domain)] ) or 
            (createIframeDataUrl[  nbc, nbc3,  d1, u] and c.to in Browser ) or 
            (createIframeTupleOriginBlobUrl[  nbc, nbc3,  d1, u] and c.to in Browser ) or 
            (createIframeNonTupleOriginBlobUrl[  nbc, nbc3,  d1, u] and c.to in Browser ) or
            (createIframeDataAboutBlobUrl[  nbc, nbc3,  d1, u] and c.to in Browser ) or
            (createIframeAboutUrl[ nbc, nbc3,  d1, u] and c.to in Browser ) or 
            (createIframeInvalidDataAbsoluteUrl[nbc, nbc3,  d1, u] and c.to in Browser ) 
        ) 

}




pred add_sandbox [f : Function, c : Call] {

    let nbc3 = f.(AddSandbox <: sandBc) |

        nbc3 in f.bc.^nestedBcs and 

        (nbc3.sandboxWaitingNavigate = False or nbc3.sandboxWaitingNavigate = none ) and

        nbc3.sandboxWaitingNavigate' = True and 

        unchanged[Browser, bcs] and
        unchanged[Browser, blobs]  and
        unchanged[BrowsingContext, (BrowsingContext <: origin)] and
        unchanged[BrowsingContext, currentDoc] and
        unchanged[BrowsingContext, nestedBcs] and
        unchanged[BrowsingContext, sessionHistory] and
        unchanged[BrowsingContext, isSecureContext]  and
        unchanged[BrowsingContext, isSandboxed] and
        unchanged[BrowsingContext - nbc3, sandboxWaitingNavigate] and
        unchanged[BrowsingContext, opening] and
        unchanged[BrowsingContext, accesses] and
        unchanged[Document, (Document <: src)] and
        unchanged[Document, elements] and
        unchanged[History, (History <: next)]  and
        unchanged[History, (History <: prev)]



}



pred document_write_iframeDocument [f : Function, c : Call] {


    let nbc = f.bc |
        let nbc2 = f.targetBc |
        let d2 = f.(DocumentWrite <: newEl) |


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

        Browser.blobs' = Browser.blobs - (nbc.^nestedBcs -> Url) and

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
        unchanged[Browser, bcs] and

        unchanged[BrowsingContext - (nbc2 + nbc2.^nestedBcs), (BrowsingContext <: origin)] and

        unchanged[BrowsingContext - ( nbc2.^nestedBcs), opening] and
        unchanged[BrowsingContext - (nbc2 + nbc2.^nestedBcs), accesses] and 
        unchanged[History, (History <: next)]  and
        unchanged[History, (History <: prev)]
    
        

}



pred access_to_media [f : Function, c : Call] {


    let nbc = f.bc |

        f.canAccess = nbc and

        nbc.accesses' = nbc.accesses + f.media and 

        unchanged[Browser, bcs] and
        unchanged[Browser, blobs]  and
        unchanged[BrowsingContext, (BrowsingContext <: origin)] and
        unchanged[BrowsingContext, currentDoc] and
        unchanged[BrowsingContext, nestedBcs] and
        unchanged[BrowsingContext, sessionHistory] and
        unchanged[BrowsingContext, isSecureContext]  and
        unchanged[BrowsingContext, isSandboxed] and
        unchanged[BrowsingContext, sandboxWaitingNavigate] and
        unchanged[BrowsingContext, opening] and
        unchanged[BrowsingContext - nbc, accesses] and
        unchanged[Document, (Document <: src)] and
        unchanged[Document, elements] and
        unchanged[History, (History <: next)]  and
        unchanged[History, (History <: prev)]

        
}


fact mediaAccess {
    always (
        all f : Access2Media | 
        let nbc = f.bc | let m = f.media |
        let dom = find_domain[nbc.currentDoc.src] |


            f.canAccess = nbc implies (

                nbc in Browser.bcs and

                nbc.currentDoc.src in ValidUrl and

                nbc.origin !in StartupOrigin and

                some dom and dom in m.permitted and
                decideUltimateSecureContext[nbc] = True  
            )
            

    )
}

