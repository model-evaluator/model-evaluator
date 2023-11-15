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
        unchanged[BrowsingContext, opening] and
        unchanged[BrowsingContext, accesses] and
        unchanged[Document, (Document <: src)] and
        unchanged[Document, elements] and 
        unchanged[Script, (Script <: context)] and 
        unchanged[NonActive, (NonActive <: context)]
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

pred hpsAbout [u : Url, f : Function] {
    let x = f.(HistoryPushState <: url) |

        
        u + x in AboutUrl
}

pred hpsData [u : Url, f : Function] {
    let x = f.(HistoryPushState <: url) |

        
        u + x in DataUrl and
        u.(DataUrl <: content) = x.(DataUrl <: content)
}

pred hpsBlob [u : Url, f : Function] {
    let x = f.(HistoryPushState <: url) |

        
        u + x in BlobUrl and 
        u.(BlobUrl <: content) = x.(BlobUrl <: content)
}


pred history_push_state [f : Function, c : Call] {

    one sh : History | 
        let nbc = f.bc | let d = nbc.currentDoc |
        let x = f.(HistoryPushState <: url) |

        d.src' = x and

        addToSessionHistory[nbc, sh, x] and

        (hpsDirectoryPath[d.src, f] or hpsAbsolute[d.src, f] or 
            hpsAbout[d.src, f] or hpsData[d.src, f] or hpsBlob[d.src, f]
        ) and

        unchanged[Browser, bcs] and 
        unchanged[Browser, blobs]  and 
        unchanged[BrowsingContext, (BrowsingContext <: origin)] and 
        unchanged[BrowsingContext, currentDoc] and 
        unchanged[BrowsingContext, nestedBcs] and 
        unchanged[BrowsingContext - nbc, sessionHistory] and 
        unchanged[BrowsingContext, isSecureContext]  and 
        unchanged[BrowsingContext, isSandboxed] and 
        unchanged[BrowsingContext, opening] and 
        unchanged[BrowsingContext, accesses] and 
        unchanged[Document - d, (Document <: src)] and 
        unchanged[Document, elements] and 
        unchanged[Script, (Script <: context)] and 
        unchanged[NonActive, (NonActive <: context)]


}


pred create_blob [f : Function, c : Call] {


    let nbc = f.bc | let u = f.(CreateBlob <: url) |

        u in BlobUrl and

        u !in BrowsingContext.currentDoc.src and

        u.creator_origin = nbc.origin and 
        Browser.blobs' = Browser.blobs + nbc -> u and 
        unchangedCreateBlob

  
}


