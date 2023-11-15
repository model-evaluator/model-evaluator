module urlmanipulation

open scmCallFunction
open browser
open appendHistory
open navigate

pred window_open [f : Function, c : Call] {

    let nbc = f.bc | 

        
        f.rootBc = nbc and 
        nbc !in Browser.bcs and
        nbc !in BrowsingContext.nestedBcs and
        Browser.bcs' = Browser.bcs + nbc and
        nbc.origin = StartupOrigin and
        no nbc.currentDoc and
        nbc.win in TopLWindow and
        unchanged[Browser, blobs] and
        unchanged[BrowsingContext, (BrowsingContext <: origin)] and
        unchanged[BrowsingContext, currentDoc] and
        unchanged[BrowsingContext, nestedBcs] and
        unchanged[BrowsingContext, sessionHistory] and
        unchanged[BrowsingContext, isSecureContext] and
        unchanged[BrowsingContext, isSandboxed] and
        unchanged[BrowsingContext, sandboxWaitingNavigate] and
        unchanged[BrowsingContext, opening] and
        unchanged[BrowsingContext, accesses] and
        unchanged[Document, (Document <: src)] and
        unchanged[Document, elements] 
}



pred hpsAbsolute [u : Url, f : Function] {
    let x = f.(HistoryPushState <: url) |


        u in AbsoluteUrl and 
        x in AbsoluteUrl and
        f.tarUrl in AbsoluteUrl and 
        origin[x] = origin[u] and
        origin[x] = origin[f.tarUrl]

        

}
pred hpsDirectoryPath [u : Url, f : Function] {
    let x = f.(HistoryPushState <: url) |


        u in AbsoluteUrl and 
        x in AbsoluteUrl and
        f.tarUrl in AbsoluteUrl and 
        origin[x] = origin[u] and
        origin[x] = origin[f.tarUrl] and

        f.tarUrl in Path and 
        x.path = f.tarUrl
        

}



pred hpsNonAbsolute [u : Url, f : Function] {

    let x = f.(HistoryPushState <: url) |

        u !in AbsoluteUrl  and 
        f.tarUrl !in AbsoluteUrl and 
        x !in AbsoluteUrl and 

        equalsNonAbsolute[u, f.tarUrl] and 
        equalsNonAbsolute[u, x] 

}

pred hpsBlobNoPath [nbc : BrowsingContext, u : Url, f : Function] {--blob://
    let x = f.(HistoryPushState <: url) |


        u in ValidBlobUrl and 
        nbc.origin = BlankOrigin and
        originW[u, nbc.win] in BlankOrigin and

        f.tarUrl in BlobNoPathUrl and

        x = f.tarUrl
}

pred hpsBlobPath [nbc : BrowsingContext, u : Url, f : Function] {//example.com
    let x = f.(HistoryPushState <: url) |


        u !in ValidBlobUrl and 
        originW[u, nbc.win] = BlankOrigin and 
        nbc.origin = BlankOrigin and 
        u in BlobNoPathUrl and
        f.tarUrl in BlobOnlyDomainUrl and 

        x in BlobAbsoluteUrl --blob://example.com

}



pred history_push_state [f : Function, c : Call] {

    one sh : History | 
        let nbc = f.bc | let d = nbc.currentDoc |
        let x = f.(HistoryPushState <: url) |

        d.src' = x and

        addToSessionHistory[nbc, sh, x] and

        (hpsDirectoryPath[d.src, f] or hpsAbsolute[d.src, f] or
            hpsNonAbsolute[d.src, f] or hpsBlobNoPath[nbc, d.src, f] or
                hpsBlobPath[nbc, d.src, f] 
        ) and

       
        unchanged[Browser, bcs] and 
        unchanged[Browser, blobs]  and 
        unchanged[BrowsingContext, (BrowsingContext <: origin)] and 
        unchanged[BrowsingContext, currentDoc] and 
        unchanged[BrowsingContext, nestedBcs] and 
        unchanged[BrowsingContext - nbc, sessionHistory] and 
        unchanged[BrowsingContext, isSecureContext]  and 
        unchanged[BrowsingContext, isSandboxed] and 
        unchanged[BrowsingContext, sandboxWaitingNavigate] and
        unchanged[BrowsingContext, opening] and 
        unchanged[BrowsingContext, accesses] and 
        unchanged[Document - d, (Document <: src)] and 
        unchanged[Document, elements] 


}


pred create_blob [f : Function, c : Call] {


    let nbc = f.bc | let u = f.(CreateBlob <: url) |

        u in ValidBlobUrl and

        u !in BrowsingContext.currentDoc.src and

        u.creator_origin = nbc.origin and 
        Browser.blobs' = Browser.blobs + nbc -> u and 
        unchangedCreateBlob

  
}


