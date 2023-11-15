module navigate 


open navigateCore
open frameConditions
open blobIframe
open secureContext



pred navigateAbsoluteUrlDeny [ nbc : BrowsingContext, d : Document, d2 : Document, u : Url, s : Server] {


                nbc.isSandboxed' = nbc.isSandboxed and 

                some nbc.currentDoc implies (

                    nbc.isSecureContext' = decideSecureContext[nbc, d2.(Document<:src')] and

                    nbc.origin' = nbc.origin and
                    
                    unchangedAbsNavXFOptionsNested[nbc]

                )else (
                    one u2 : Url |
                        u2 in AboutUrl and 
                        nbc.accesses' = none and
                        nbc.origin' = nbc.~nestedBcs.origin and
      
                        unchanged[nbc, opening] and 
                        navAboutUrlCore[nbc, u2, d2, AboutUrl] and 
                        nbc.isSecureContext' = True and
                        unchangedNavigateAbsolute[nbc, d2]
                )
                
        
}


pred navigateAbsoluteUrl [nbc : BrowsingContext, d : Document, u : Url] {



            navAbsUrlCore[nbc, u, d] and
            
            nbc.isSecureContext' = decideSecureContext[nbc, u] and

            nbc.origin' = origin[u] and
            
            unchangedNavigateNested[nbc] 


}


pred navigateDataUrl [ nbc : BrowsingContext, d : Document, u : Url] {


        navDataHtmlUrlCore[nbc, u, d] and

        nbc.origin' = origin[u] and

            
        unchangedNavigateNested[nbc] and

        nbc.isSecureContext' = False


}



pred navigateBlobUrl [ nbc : BrowsingContext,  d : Document, u : Url] {


        nbc.win in TopLWindow and

        navBlobBlobsHtmlUrlCore[nbc, u, d] and 
        u in Browser.blobs[BrowsingContext] and

        nbc.isSecureContext' = decideSecureContext[nbc, u] and
        

        nbc.origin' = origin[u] and


        unchangedNavigateNested[nbc] 
}

pred navigateIframeBlobUrl [rbc : BrowsingContext, nbc : BrowsingContext,  d : Document, u : Url] {

        nbc.win in Iframe and
        
        (tupleOriginBlobUrl[rbc, nbc, d, u] or nonTupleOriginBlobUrl[rbc, nbc, d, u] or dataAboutBlobUrl[rbc, nbc, d, u]) and 
        nbc.origin' = origin[u] and
        unchangedNavigateNested[nbc]
    
}



pred navigateAboutUrl [ rbc : BrowsingContext, nbc : BrowsingContext, d : Document, u : Url] {


        navAboutUrlCore[nbc, u, d, AboutUrl] and

        (nbc.win in TopLWindow implies (
            nbc.origin' = origin[u] and 
            nbc.isSecureContext' = True and

            unchanged[nbc, isSandboxed]  
        )else (

            nbc.origin' = rbc.origin and 
            unchanged[nbc, isSandboxed] and 
            nbc.isSecureContext' = rbc.isSecureContext
        )) and

        
        unchangedNavigateNested[nbc] 

}



pred navigateErrorUrl [ nbc : BrowsingContext, d : Document, u : Url, allowedUrls : set Url] {

        u !in allowedUrls and 
        navErrorUrlCore[nbc, u, d] and
        nbc.isSecureContext' = False and
        nbc.origin' = OpaqueOrigin and

        unchanged[nbc, isSandboxed] and 

        nbc.nestedBcs' = none and
        unchangedNavigateNested[nbc]
}

pred resetIframe [d2 : Document] {
  
        (all d : d2.^elements <: Document |

            let nbc = d.~currentDoc | 


                nbc.origin' = StartupOrigin and
                nbc.currentDoc' = none and 
                nbc.isSandboxed' = none and 
                nbc.isSecureContext' = none and 
                nbc.sessionHistory' = none and 
                nbc.nestedBcs' = none and
                nbc.opening' = none and 
                nbc.accesses' = none
        ) /*and 
        (all scr : d2.^elements <: Script |
            scr.(Script <: context') = none

        ) and 
        (all non : d2.^elements <: NonActive |
            non.(NonActive <: context') = none

        )*/

}



