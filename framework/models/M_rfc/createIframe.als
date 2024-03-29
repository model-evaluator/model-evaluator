module createIframe

open navigateCore
open frameConditions
--open scmCallFunction
open secureContext
open sandbox
open blobIframe

pred BcSecureContextOrigin [rbc : BrowsingContext, nbc : BrowsingContext, u : Url, d : Document ] {

            nbc.isSecureContext' = decideSecureContext[nbc, u] and

            (sandboxedIframeOrigin[nbc] or regularIframeOrigin[nbc, u]) 

}


pred createIframeAbsUrlDeny [ rbc : BrowsingContext, nbc : BrowsingContext, d : Document, u : Url, s : Server] {

        u in AbsoluteUrl and
        some s.xframeOptions[d] and 
        ((s.xframeOptions[d].option = Deny) or (s.xframeOptions[d].option = SameOrigin and nbc.origin != s.origin )) and


        one u2 : AboutUrl |
            navAboutUrlCore[nbc, u2, d, AboutUrl] and 
            nbc.isSecureContext' = rbc.isSecureContext and 
            nbc.origin' = rbc.origin

            
        

        
}


pred createIframeAbsUrl [ rbc : BrowsingContext, nbc : BrowsingContext, d : Document, u : Url] {



             u in AbsoluteUrl and
             navAbsUrlCore[nbc, u,  d] and

             BcSecureContextOrigin[rbc, nbc, u, d]

       

        
}


pred createIframeDataUrl [rbc : BrowsingContext, nbc : BrowsingContext, d : Document, u : Url] {


        navDataHtmlUrlCore[nbc, u,  d] and

        BcSecureContextOrigin[rbc, nbc, u, d]

        
}



pred createIframeTupleOriginBlobUrl [rbc : BrowsingContext, nbc : BrowsingContext, d : Document, u : Url] {


        tupleOriginBlobUrl[rbc, nbc, d, u] and 
        (sandboxedIframeOrigin[nbc] or regularIframeOrigin[nbc, u])
                            
}

pred createIframeNonTupleOriginBlobUrl [rbc : BrowsingContext, nbc : BrowsingContext, d : Document, u : Url] {


        nonTupleOriginBlobUrl[rbc, nbc, d, u] and 
        (sandboxedIframeOrigin[nbc] or regularIframeOrigin[nbc, u]) 
                            
}


pred createIframeDataAboutBlobUrl [rbc : BrowsingContext, nbc : BrowsingContext, d : Document, u : Url] {


        dataAboutBlobUrl[rbc, nbc, d, u] and 
        (sandboxedIframeOrigin[nbc] or regularIframeOrigin[nbc, u])
                            
}




pred createIframeAboutUrl [  rbc : BrowsingContext, nbc : BrowsingContext,  d : Document, u : Url] {


        navAboutUrlCore[nbc, u,  d, (AboutUrl + invalid_about_url)] and

        ((nbc.isSandboxed' = True and nbc.origin' = OpaqueOrigin) or 
        (nbc.isSandboxed' = False and nbc.origin' = rbc.origin))

        nbc.isSecureContext' = rbc.isSecureContext

}



pred createIframeInvalidDataAbsoluteUrl [  rbc : BrowsingContext, nbc : BrowsingContext,  d : Document, u : Url] {

        u in (invalid_absolute_url + invalid_data_url) and
        one u2 : AboutUrl |
            navErrorUrlCore[nbc, u2,  d] and

            nbc.isSecureContext' = rbc.isSecureContext and
            (sandboxedIframeOrigin[nbc] or regularErrorIframeOrigin[nbc]) 

}



