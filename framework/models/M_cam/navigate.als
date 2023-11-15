module navigate 


open navigateCore
open frameConditions
open blobIframe
open secureContext

pred navigateOriginIframe [nbc : BrowsingContext, u : Url] {
            (nbc.sandboxWaitingNavigate = True or nbc.isSandboxed = True) implies (
                nbc.isSandboxed' = True and 
                nbc.origin' = OpaqueOrigin and
                nbc.sandboxWaitingNavigate' = False
            )else (
                nbc.origin' = originY[u] and
                unchanged[nbc, isSandboxed] and 
                unchanged[nbc, sandboxWaitingNavigate]
            )
}



pred navigateOrigin [nbc : BrowsingContext, u : Url, lr : Boolean] {
        nbc.win in TopLWindow implies (

            ((lr = True and u in BlobUrl) implies (
                nbc.origin' = originBlob[u]
              )else (
                nbc.origin' = originZ[u]
              )

            ) and
            unchanged[nbc, isSandboxed] and 
            unchanged[nbc, sandboxWaitingNavigate]
        )else (
            navigateOriginIframe[nbc, u]
        )
}



pred navigateAbsoluteUrlDeny [ nbc : BrowsingContext, d : Document, d2 : Document, u : Url, s : Server] {


                (nbc.sandboxWaitingNavigate = True implies (
                    nbc.isSandboxed' = True and 
                    nbc.origin' = OpaqueOrigin and
                    nbc.sandboxWaitingNavigate' = False
                )else (
                    nbc.isSandboxed' = nbc.isSandboxed and 
                    nbc.origin' = OpaqueOrigin and 
                    nbc.sandboxWaitingNavigate' = False
                )) and 

                some nbc.currentDoc implies (

                    nbc.isSecureContext' = decideSecureContext[nbc, d2.(Document<:src')] and
                    
                    unchangedAbsNavSafariXFOptionsNested[nbc]

                )else (
                    one u2 : Url |
                        u2 in AboutUrl and 
                        nbc.accesses' = none and
                        --nbc.opening' = none and
                        unchanged[nbc, opening] and --TODO
                        navAboutUrlCore[nbc, u2, d2, AboutUrl] and 
                        nbc.isSecureContext' = True and
                        unchangedNavigateAbsolute[nbc, d2]
                )
                
        
}

--d2 = old document
pred navigateAbsoluteUrl [nbc : BrowsingContext, d : Document, d2 : Document, u : Url, lr : Boolean] {

            u in AbsoluteUrl and

            navAbsUrlCore[nbc, u, d] and
            
            nbc.isSecureContext' = decideSecureContext[nbc, u] and
            navigateOrigin[nbc, u, lr] and

            addNavigateNoNestedBcs[nbc] and
            
            unchangedNavigateNested[nbc, d, d2]


}


pred navigateDataUrl [ nbc : BrowsingContext, d : Document, d2 : Document, u : Url, lr : Boolean] {


        navDataHtmlUrlCore[nbc, u, d] and

        navigateOrigin[nbc, u, lr] and

        addNavigateNoNestedBcs[nbc] and
            
        unchangedNavigateNested[nbc, d, d2] and


        ((nbc.win in TopLWindow and nbc.isSecureContext' = True) or 
        (nbc.win in Iframe and nbc.isSecureContext' = decideSecureContext[nbc, u]))

        
}



pred navigateBlobUrl [ nbc : BrowsingContext,  d : Document, d2 : Document, u : Url, lr : Boolean] {


        nbc.win in TopLWindow and

        navBlobBlobsHtmlUrlCore[nbc, u, d] and 
        u in Browser.blobs[BrowsingContext] and

        nbc.isSecureContext' = decideSecureContext[nbc, u] and
        

        navigateOrigin[nbc, u, lr] and

        addNavigateNoNestedBcs[nbc] and

        unchangedNavigateNested[nbc, d, d2] 
}

pred navigateIframeBlobUrl [rbc : BrowsingContext, nbc : BrowsingContext,  d : Document, d2 : Document, u : Url] {

        nbc.win in Iframe and
        
        (tupleOriginBlobUrl[rbc, nbc, d, u] or nonTupleOriginBlobUrl[rbc, nbc, d, u] or dataAboutBlobUrl[rbc, nbc, d, u]) and 
        navigateOriginIframe[nbc, u] and
        unchangedNavigateNested[nbc,  d, d2]
    
}



pred navigateBlobNoBlobsUrl [ nbc : BrowsingContext, d : Document, d2 : Document, u : Url] {


        navBlobNoBlobsUrlCore[nbc, u, d] and
        u !in Browser.blobs[BrowsingContext] and
        nbc.isSecureContext' = True and

        nbc.win in TopLWindow and

        nbc.origin' = StartupOrigin and

        unchanged[nbc, isSandboxed] and 
        unchanged[nbc, sandboxWaitingNavigate] and

        unchangedNavigate[nbc, d, d2] 

}


pred navigateAboutUrl [  nbc : BrowsingContext, d : Document, d2 : Document, u : Url] {


        navAboutUrlCore[nbc, u, d, AboutUrl] and

        (nbc.win in TopLWindow implies (
            nbc.origin' = origin[u] and 
            nbc.isSecureContext' = True and

            unchanged[nbc, isSandboxed] and 
            unchanged[nbc, sandboxWaitingNavigate] 
        )else (

            ((nbc.sandboxWaitingNavigate = True or nbc.isSandboxed = True) implies (
                nbc.isSandboxed' = True and 
                nbc.origin' = OpaqueOrigin and
                nbc.sandboxWaitingNavigate' = False
            )else (
                nbc.origin' = nbc.~nestedBcs.origin and 
                unchanged[nbc, isSandboxed] and 
                unchanged[nbc, sandboxWaitingNavigate]
            )) and
            nbc.isSecureContext' = decideSecureContext[nbc, u]
        )) and

        unchangedNavigate[nbc, d, d2] and
        nbc.nestedBcs' = none 

}



pred navigateErrorUrl [ nbc : BrowsingContext, d : Document, d2 : Document, u : Url, allowedUrls : set Url] {

        u !in allowedUrls and 
        navErrorUrlCore[nbc, u, d] and
        nbc.isSecureContext' = False and
        nbc.origin' = OpaqueOrigin and

        ((nbc.sandboxWaitingNavigate = True or nbc.isSandboxed = True) implies (
            nbc.isSandboxed' = True and
            nbc.sandboxWaitingNavigate' = False
        ) else (
            unchanged[nbc, isSandboxed] and 
            unchanged[nbc, sandboxWaitingNavigate] 
        )) and

        nbc.nestedBcs' = none and
        unchangedNavigate[nbc, d, d2]
}

pred resetIframe [d2 : Document] {
  
        all d : d2.^elements <: Document |

            let nbc = d.~currentDoc | 


                d.elements' = none and

                nbc.origin' = StartupOrigin and
                nbc.currentDoc' = none and 
                nbc.isSandboxed' = none and 
                nbc.isSecureContext' = none and 
                nbc.sessionHistory' = none and 
                nbc.sandboxWaitingNavigate' = none and 
                nbc.nestedBcs' = none and
                nbc.opening' = none and 
                nbc.accesses' = none
  

}

