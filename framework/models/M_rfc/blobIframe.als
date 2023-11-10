module blobIframe

open browser
open url
open navigateCore



pred tupleOriginBlobUrl [rbc : BrowsingContext, nbc : BrowsingContext, d : Document, u : Url] {


        navBlobBlobsHtmlUrlCore[nbc, u,  d] and
        u in Browser.blobs[BrowsingContext] and --BrowsingContext
        rbc.origin in TupleOrigin and 
        rbc.origin = u.creator_origin and

        nbc.isSecureContext' = decideSecureContext[nbc, u] and
        addNavigateNoNestedBcs[nbc] --and
                         
}

pred nonTupleOriginBlobUrl [rbc : BrowsingContext, nbc : BrowsingContext, d : Document, u : Url] {


        navBlobBlobsHtmlUrlCore[nbc, u,  d] and
        u in Browser.blobs[nbc] and --nbc should come here
        rbc.currentDoc.src in BlobUrl and
        rbc.origin in OpaqueOrigin and 
        (rbc.origin = u.creator_origin or u.creator_origin in OpaqueOrigin) and


        nbc.isSecureContext' = False and

        addNavigateNoNestedBcs[nbc]
                            
}


pred dataAboutBlobUrl [rbc : BrowsingContext, nbc : BrowsingContext, d : Document, u : Url] {


        navBlobBlobsHtmlUrlCore[nbc, u,  d] and
        u in Browser.blobs[nbc] and --nbc should come here
        rbc.currentDoc.src in (AboutUrl + DataUrl) and
        rbc.origin in OpaqueOrigin and 
        rbc.origin = u.creator_origin and


        nbc.isSecureContext' = rbc.isSecureContext and


        addNavigateNoNestedBcs[nbc]  


                            
}
