module blobIframe

open browser
open url
open navigateCore



pred tupleOriginBlobUrl [rbc : BrowsingContext, nbc : BrowsingContext, d : Document, u : Url] {


        navBlobBlobsHtmlUrlCore[nbc, u,  d] and
        u in Browser.blobs[BrowsingContext] and 
        rbc.origin in TupleOrigin and 

        nbc.isSecureContext' = decideSecureContext[nbc, u] 
                         
}

pred nonTupleOriginBlobUrl [rbc : BrowsingContext, nbc : BrowsingContext, d : Document, u : Url] {


        navBlobBlobsHtmlUrlCore[nbc, u,  d] and
        u in Browser.blobs[rbc] and 
        rbc.currentDoc.src in (BlobUrl + AboutUrl + DataUrl) and
        rbc.origin !in TupleOrigin and


        nbc.isSecureContext' = False 

                            
}


pred dataAboutBlobUrl [rbc : BrowsingContext, nbc : BrowsingContext, d : Document, u : Url] {


        navBlobBlobsHtmlUrlCore[nbc, u,  d] and
        u in Browser.blobs[BrowsingContext] and 
        rbc.currentDoc.src in BlobUrl and
        rbc.currentDoc.src !in secure_urls and


        nbc.isSecureContext' = False and


        addNavigateNoNestedBcs[nbc]  


                            
}
