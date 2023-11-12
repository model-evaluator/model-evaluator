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
        ((c.to.xframeOptions[d].option = Deny) or (c.to.xframeOptions[d].option = SameOrigin and rbc.origin != c.to.(Server <: origin) )) and

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
        (some c.to.xframeOptions[d] and c.to.xframeOptions[d].option = SameOrigin and rbc.origin = c.to.(Server <: origin)  )) and

        (lr = False implies (
            one sh : History |
            addToSessionHistory[nbc, sh, u] 
        )else(
            unchanged[nbc, sessionHistory]
        )) and
        
        nbc.accesses' = none and
        unchanged[nbc, opening] and
        resetIframe[d2] and

        navigateAbsoluteUrl[ nbc, d, u] and 
        d = c.to.resources[u.path] and 
        c.to in Server and 
        c.to in Dns.map[u.(AbsoluteUrl <: domain)] 

}

pred navigate [nbc : BrowsingContext, s : BrowsingContext + Browser + Server, u : Url, d : Document, lr : Boolean] {

        (lr = False implies (
            one sh : History |
            addToSessionHistory[nbc, sh, u] 
        )else(
            unchanged[nbc, sessionHistory]
        )) and

        some d and

        d !in Document.elements and

        nbc.accesses' = none and
        unchanged[nbc, opening] and

        resetIframe[ nbc.currentDoc] and

        nbc.^nestedBcs' = none and 


        (
            (navigateAbsoluteUrl[ nbc, d, u] and nbc.win in TopLWindow and  s in Server and d = s.resources[u.path] and d.elements = s.constantResources[u.path][d] and s in Dns.map[u.(AbsoluteUrl <: domain)] ) or 
            (navigateDataUrl[ nbc,  d, u] ) or 
            (navigateBlobUrl[ nbc,  d, u] and nbc.win in TopLWindow ) or 
            (navigateIframeBlobUrl[nbc.~nestedBcs', nbc,  d, u] ) or
            (navigateAboutUrl[  nbc.~nestedBcs', nbc,  d, u] ) or 
            (navigateErrorUrl[  nbc,  d, u, ValidUrl]  )
        ) 


}

pred render_resource [f : Function, c : Call] {

    let d2 = f.(RenderResource <: doc) | let u = d2.src | one sh : History | let nbc3 = f.(RenderResource <: newBc) | let nbc = f.bc |
    
    d2 in nbc.currentDoc.elements <: Document and

    no d2.~currentDoc and 

    nbc3 !in Browser.bcs and 
    nbc3 !in BrowsingContext.nestedBcs and 

    nbc3.currentDoc' = d2 and 

    nbc.nestedBcs' = nbc.nestedBcs + nbc3 and 
    nbc3.nestedBcs' = none and

    addToSessionHistory[nbc3, sh, u] and

    (
        (createIframeAbsUrlDeny[ nbc, nbc3,  d2, u, c.to] and d2 = c.to.resources[u.path] and c.to in Server and c.to in Dns.map[u.(AbsoluteUrl <: domain)] and unchangedCreateIframe[nbc, nbc3, True] ) or 
        (createIframeAbsUrl[ nbc, nbc3,  d2, u] and d2 = c.to.resources[u.path] and c.to in Server and d2.elements = c.to.constantResources[u.path][d2] and c.to in Dns.map[u.(AbsoluteUrl <: domain)] and unchangedCreateIframe[nbc, nbc3, True] ) or 
        (createIframeDataUrl[  nbc, nbc3,  d2, u]  and unchangedCreateIframe[nbc, nbc3, True] ) or 
        (createIframeTupleOriginBlobUrl[  nbc, nbc3,  d2, u] and unchangedCreateIframe[nbc, nbc3, True] ) or 
        (createIframeNonTupleOriginBlobUrl[  nbc, nbc3,  d2, u] and unchangedCreateIframe[nbc, nbc3, True] ) or
        (createIframeDataAboutBlobUrl[  nbc, nbc3,  d2, u] and unchangedCreateIframe[nbc, nbc3, True] ) or
        (createIframeAboutUrl[ nbc, nbc3,  d2, u]  and unchangedCreateIframe[nbc, nbc3, True] ) or 
        (createIframeInvalidDataAbsoluteUrl[ nbc, nbc3,  d2, u] and unchangedCreateIframe[nbc, nbc3, True] ) 
    ) 



}

pred create_iframe [f : Function, c : Call] {

    one sh : History |
        let nbc = f.bc |
        let nbc3 = f.(CreateIframe <: newBc) |
        let d1 = f.(CreateIframe <: response) |
        let u = f.(CreateIframe <: url) |

        u = d1.src and

        d1 !in Document.elements and

        some nbc.currentDoc and

        nbc3 !in Browser.bcs and 
        nbc3 !in BrowsingContext.^nestedBcs and

        nbc.nestedBcs' = nbc.nestedBcs + nbc3 and 
        nbc.currentDoc.elements' = nbc.currentDoc.elements + d1 and


        nbc3.win in Iframe and

        d1 !in (BrowsingContext.currentDoc) and

        addToSessionHistory[nbc3, sh, u] and
        
        (
            (createIframeAbsUrlDeny[ nbc, nbc3,  d1, u, c.to] and d1 = c.to.resources[u.path ] and c.to in Server and c.to in Dns.map[u.(AbsoluteUrl <: domain)] and unchangedCreateIframe[nbc, nbc3, False] ) or 
            (createIframeAbsUrl[ nbc, nbc3,  d1, u] and d1 = c.to.resources[u.path ] and c.to in Server and d1.elements = c.to.constantResources[u.path][d1] and c.to in Dns.map[u.(AbsoluteUrl <: domain)] and unchangedCreateIframe[nbc, nbc3, False] ) or 
            (createIframeDataUrl[  nbc, nbc3,  d1, u] and c.to in Browser and unchangedCreateIframe[nbc, nbc3, False] ) or 
            (createIframeTupleOriginBlobUrl[  nbc, nbc3,  d1, u] and c.to in Browser and unchangedCreateIframe[nbc, nbc3, False] ) or 
            (createIframeNonTupleOriginBlobUrl[  nbc, nbc3,  d1, u] and c.to in Browser and unchangedCreateIframe[nbc, nbc3, False] ) or
            (createIframeDataAboutBlobUrl[  nbc, nbc3,  d1, u] and c.to in Browser and unchangedCreateIframe[nbc, nbc3, False] ) or
            (createIframeAboutUrl[ nbc, nbc3,  d1, u] and c.to in Browser and unchangedCreateIframe[nbc, nbc3, False] ) or 
            (createIframeInvalidDataAbsoluteUrl[nbc, nbc3,  d1, u] and c.to in Browser and unchangedCreateIframe[nbc, nbc3, False]) 
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
            (popupAbsoluteBlobUrl[nbc2, nbc, d, u ] and c.to in Server and c.to in Dns.map[u.(AbsoluteUrl <: domain)] and d = c.to.resources[u.path] and d.elements = c.to.constantResources[u.path][d] ) or 
            (popupDataUrl[nbc2, nbc, d, u ] and c.to in Browser  ) or 
            (popupAbsoluteBlobUrl[ nbc2, nbc, d, u ] and c.to in Browser ) or 
            (popupAboutUrl[ nbc2, nbc, d, u ] and c.to in Browser ) or 
            (popupErrorUrl[ nbc2, nbc, d, u ] and c.to in Browser )
        )
}


pred reachability [nbc : BrowsingContext, nbc2 : BrowsingContext] {

    let nestedNbc = (nbc.^~nestedBcs - nbc2.^~nestedBcs) | let nestedNbc2 = (nbc2.^~nestedBcs - nbc.^~nestedBcs ) |
    let openingNbc = nbc.^~opening | let openingNbc2 = nbc2.^~opening |
    let openingNestedNbc = nbc.^~opening.^~nestedBcs | let openingNestedNbc2 = nbc2.^~opening.^~nestedBcs | 


    sameOriginPolicy[nbc, nbc2] and 

    ((nbc2 in nestedNbc and (all n : nestedNbc | sameOriginPolicy[nbc, n])) or
        (nbc in nestedNbc2 and (all n : nestedNbc2 | sameOriginPolicy[nbc, n])) or
        (nbc2 in openingNbc and (all n : openingNbc | sameOriginPolicy[nbc, n])) or
        (nbc in openingNbc2 and (all n : openingNbc2 | sameOriginPolicy[nbc, n])) or
        (nbc2 in openingNestedNbc and (all n : openingNestedNbc | sameOriginPolicy[nbc, n])) or
        (nbc in openingNestedNbc2 and (all n : openingNestedNbc2 | sameOriginPolicy[nbc, n]))
    )
}




pred document_write [f : Function, c : Call] {


    let nbc = f.party |
        let nbc2 = f.targetBc |
        let d2 = f.(DocumentWrite <: newEl) |

        d2 !in Document.elements and
        d2 !in BrowsingContext.currentDoc and

        nbc != nbc2 and 

        some nbc.currentDoc and

        reachability[nbc, nbc2] and

        nbc2.currentDoc' = d2 and

        d2.(Document <: src') = nbc.currentDoc.(Document <: src) and 

        nbc2.~nestedBcs.currentDoc.elements' = nbc2.~nestedBcs.currentDoc.elements + d2 and

        nbc2.accesses' = none and


        resetIframe[nbc2.currentDoc] and

        nbc2.origin' = nbc.origin and 
     
        unchanged[BrowsingContext - (nbc2 + nbc2.^nestedBcs), currentDoc] and 
        unchanged[BrowsingContext - nbc2.^nestedBcs, sessionHistory] and 
        unchanged[BrowsingContext - nbc2.^nestedBcs, isSecureContext] and 
        unchanged[BrowsingContext - nbc2.^nestedBcs, nestedBcs] and
        unchanged[BrowsingContext - nbc2.^nestedBcs, isSandboxed] and --because there are new elements inside
        unchanged[Document - d2, (Document <: src)] and
        unchanged[Document - nbc2.~nestedBcs.currentDoc, elements] and  
        unchanged[Browser, bcs] and
        unchanged[Browser, blobs] and
        unchanged[BrowsingContext - (nbc2 + nbc2.^nestedBcs), (BrowsingContext <: origin)] and
        unchanged[BrowsingContext - ( nbc2.^nestedBcs), opening] and
        unchanged[BrowsingContext - (nbc2 + nbc2.^nestedBcs), accesses] and 
        unchanged[Script, (Script <: context)] and 
        unchanged[NonActive, (NonActive <: context)]
    
        

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
        unchanged[BrowsingContext, opening] and
        unchanged[BrowsingContext - nbc, accesses] and
        unchanged[Document, (Document <: src)] and
        unchanged[Document, elements] and
        unchanged[Script, (Script <: context)] and 
        unchanged[NonActive, (NonActive <: context)]

        
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
                decideSecureContext[nbc, nbc.currentDoc.src] = True  
            )
            

    )
}

