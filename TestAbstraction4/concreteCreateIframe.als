module concreteCreateIframe

open concreteNavigateCore
open frameConditions
--open scmCallFunction
open concreteSecureContext
open concreteSandbox


pred createIframeAbsoluteUrl [ rbc : BrowsingContext, nbc : BrowsingContext, d : Document, u : Url, s : Server] {
    --one d : Document |  --one sh : History |

        --some f.x and 
        --f.x = d and

        (some s.xframeOptions[d] and ((s.xframeOptions[d].option = Deny) or (s.xframeOptions[d].option = SameOrigin and nbc.origin != s.origin ))) implies (

            BrowserVersion.version = Safari implies (

                one u2 : Url |
                            u2 in valid_about_url and 
                            navAboutUrlCore[nbc, u2, d, valid_about_url] and 
                            --navAboutSecureContext[nbc, u2, valid_about_url] and
                            nbc.isSecureContext' = decideSecureContext[nbc, u2] and 
                            unchangedCreateIframeRaw[nbc, d] and
                            unchanged[NonActive, (NonActive <: src)] and 
                            unchanged[NonActive, (NonActive <: context)]

            )else (

                    d in ErrorDocument and 
                    navErrorUrlCore[nbc, StartupUrl, d] and 
                    nbc.isSecureContext' = False and 
                    unchangedCreateIframeRaw[nbc, d] and
                    unchanged[NonActive, (NonActive <: src)] and 
                    unchanged[NonActive, (NonActive <: context)]
            )
        )else (

            navAbsUrlCore[nbc, u,  d] and

            --(navAbsSecureContext[nbc, u] or navInSecureContext[nbc, u] ) and
            nbc.isSecureContext' = decideSecureContext[nbc, u] and
            --(addNavigateNoNestedBcs[d, nbc] or addNavigateNestedBcs[d, nbc] ) and
            (sandboxedIframeOrigin[nbc] or regularIframeOrigin[nbc, u]) and
            /*(noDocInside[d.elements] implies addNavigateNoNestedBcs[nbc]
                else addNavigateNestedBcs[d, nbc]
            ) and*/
            addNavigateNoNestedBcs[nbc] and
            unchangedCreateIframeNested[rbc, nbc,  d, rbc.currentDoc] 
            --unchanged[DataPath, data]

        )










        
}


pred createIframeDataHtmlUrl [rbc : BrowsingContext, nbc : BrowsingContext, d : Document, u : Url] {
    --one d : Document |  --one sh : History |

        --some f.x and
        --f.x = d and 

        navDataHtmlUrlCore[nbc, u,  d] and
        --navInSecureContext[nbc, u] and 
        nbc.isSecureContext' = decideSecureContext[nbc, u] and
        --(addNavigateNoNestedBcs[d, nbc] or addNavigateNestedBcs[d, nbc] ) and
        (sandboxedIframeOrigin[nbc] or regularIframeOrigin[nbc, u]) and
        /*(noDocInside[d.elements] implies addNavigateNoNestedBcs[nbc]
            else addNavigateNestedBcs[d, nbc]
        ) and*/
        addNavigateNoNestedBcs[nbc] and
        unchangedCreateIframeNested[rbc, nbc,  d, rbc.currentDoc] 
        --unchanged[DataPath - f.(Navigate <: url).path, data]
        
}


pred createIframeDataScriptUrl [ rbc : BrowsingContext, nbc : BrowsingContext,  d : Document, u : Url] {
    /*one d : Document |  /*one sh : History |*/ one na : NonActive |

        --some f.x and
        --f.x = d and 

        navDataScriptUrlCore[nbc, u, d,  na] and
        --navInSecureContext[nbc, u] and
        nbc.isSecureContext' = decideSecureContext[nbc, u] and
        (sandboxedIframeOrigin[nbc] or regularIframeOrigin[nbc, u]) and
        unchangedCreateIframe[rbc, nbc, d, rbc.currentDoc] and
        unchanged[NonActive - na, (NonActive <: src)] and 
        unchanged[NonActive - na, (NonActive <: context)]
        --unchanged[DataPath, data]
}



pred createIframeTupleOriginBlobBlobsHtmlUrl [rbc : BrowsingContext, nbc : BrowsingContext, d : Document, u : Url, blbCntx : BrowsingContext] {
   /* one d : Document |  /*one sh : History |*/ --one na : NonActive |


        --some f.x and
        --f.x = d and 

        navBlobBlobsHtmlUrlCore[nbc, u,  d] and
        u in Browser.blobs[blbCntx] and
        rbc.origin in TupleOrigin and 
        rbc.origin = u.path.creator_origin and

        --(navAbsSecureContext[nbc, u] or navInSecureContext[nbc, u] ) and
        nbc.isSecureContext' = decideSecureContext[nbc, u] and
        (sandboxedIframeOrigin[nbc] or regularIframeOrigin[nbc, u]) and
        --(addNavigateNoNestedBcs[d, nbc] or addNavigateNestedBcs[d, nbc] ) and
        /*(noDocInside[d.elements] implies addNavigateNoNestedBcs[nbc]
            else addNavigateNestedBcs[d, nbc]
        ) and*/
        addNavigateNoNestedBcs[nbc] and

        unchangedCreateIframeNested[rbc, nbc,  d, rbc.currentDoc] 
        --unchanged[NonActive - na, (NonActive <: src)] and 
        --unchanged[NonActive - na, (NonActive <: context)] 
        --unchanged[DataPath, data]
                            
}

pred createIframeTupleOriginBlobBlobsScriptUrl [ rbc : BrowsingContext, nbc : BrowsingContext,  d : Document, u : Url, blbCntx : BrowsingContext] {
   /* one d : Document |  /*one sh : History |*/ one na : NonActive |


        --some f.x and
        --f.x = d and 

        navBlobBlobsScriptUrlCore[nbc, u,  d, na] and
        u in Browser.blobs[blbCntx] and
        rbc.origin in TupleOrigin and 
        rbc.origin = u.path.creator_origin and

        nbc.isSecureContext' = decideSecureContext[nbc, u] and

        --(navAbsSecureContext[nbc, u] or navInSecureContext[nbc, u] ) and
        (sandboxedIframeOrigin[nbc] or regularIframeOrigin[nbc, u]) and
        --(addNavigateNoNestedBcs[d, nbc] or addNavigateNestedBcs[d, nbc] ) and

        unchangedCreateIframe[rbc, nbc,  d, rbc.currentDoc] and
        unchanged[NonActive - na, (NonActive <: src)] and 
        unchanged[NonActive - na, (NonActive <: context)] 
        --unchanged[DataPath, data]
                            
}

pred createIframeNonTupleOriginBlobBlobsHtmlUrl [rbc : BrowsingContext, nbc : BrowsingContext, d : Document, u : Url, blbCntx : BrowsingContext] {
   /* one d : Document |  /*one sh : History |*/ --one na : NonActive |


        --some f.x and
        --f.x = d and 

        navBlobBlobsHtmlUrlCore[nbc, u,  d] and
        u in Browser.blobs[blbCntx] and --nbc should come here
        rbc.origin !in TupleOrigin and 
        rbc.origin = u.path.creator_origin and

        --navInSecureContext[nbc, u] and
        --nbc.isSecureContext' = False and

        nbc.isSecureContext' = decideSecureContext[nbc, u] and

        (sandboxedIframeOrigin[nbc] or regularIframeOrigin[nbc, u]) and
        --(addNavigateNoNestedBcs[d, nbc] or addNavigateNestedBcs[d, nbc] ) and

        /*(noDocInside[d.elements] implies addNavigateNoNestedBcs[nbc]
            else addNavigateNestedBcs[d, nbc]
        ) and*/

        addNavigateNoNestedBcs[nbc] and

        unchangedCreateIframeNested[rbc, nbc, d, rbc.currentDoc] --and 

        --unchanged[NonActive - na, (NonActive <: src)] and 
        --unchanged[NonActive - na, (NonActive <: context)] 
        --unchanged[DataPath, data]
                            
}

pred createIframeNonTupleOriginBlobBlobsScriptUrl [ rbc : BrowsingContext, nbc : BrowsingContext, d : Document, u : Url, blbCntx : BrowsingContext] {
   /* one d : Document |  /*one sh : History |*/ one na : NonActive |


        --some f.x and
        --f.x = d and 

        navBlobBlobsScriptUrlCore[nbc, u,  d, na] and
        u in Browser.blobs[blbCntx] and --nbc should come 
        rbc.origin !in TupleOrigin and 
        rbc.origin = u.path.creator_origin and

        --navInSecureContext[nbc, u] and
        --nbc.isSecureContext' = False and
        nbc.isSecureContext' = decideSecureContext[nbc, u] and
        (sandboxedIframeOrigin[nbc] or regularIframeOrigin[nbc, u]) and
        --(addNavigateNoNestedBcs[d, nbc] or addNavigateNestedBcs[d, nbc] ) and

        unchangedCreateIframe[rbc, nbc,  d, rbc.currentDoc] and
        unchanged[NonActive - na, (NonActive <: src)] and 
        unchanged[NonActive - na, (NonActive <: context)] 
        --unchanged[DataPath, data]
                            
}
/*
pred createIframeTupleOriginBlobNoBlobsUrl [c : Call, rbc : BrowsingContext, nbc : BrowsingContext, w : TopLWindow, d : Document, u : Url, blbCntx : BrowsingContext] {
    one na : NonActive |


        --some f.x and
        --f.x = d and 
        navBlobBlobsUrlCore[nbc, u, w, d, c, na] and
        u !in Browser.blobs[blbCntx] and
        rbc.origin in TupleOrigin and 
        rbc.origin = u.path.creator_origin and

        unchangedCreateIframe[rbc, nbc, w, d, rbc.currentDoc] and
        unchanged[NonActive - na, (NonActive <: src)] and 
        unchanged[NonActive - na, (NonActive <: context)] 
        --unchanged[DataPath, data]
                            
}



pred createIframeBlobNoBlobsUrl [c : Call, rbc : BrowsingContext, nbc : BrowsingContext, w : TopLWindow, d : Document, u : Url, blbCntx : BrowsingContext] {
    --one d : Document |  --one sh : History |

        --some f.x and
        --f.x = d and 
        navBlobNoBlobsUrlCore[nbc, u, w, d, c] and
        u !in Browser.blobs[blbCntx] and
        unchangedCreateIframe[rbc, nbc, w, d, rbc.currentDoc] and
        unchanged[NonActive, (NonActive <: src)] and 
        unchanged[NonActive, (NonActive <: context)]
        --unchanged[DataPath, data]
}*/


pred createIframeChromeAboutUrl [  rbc : BrowsingContext, nbc : BrowsingContext,  d : Document, u : Url] {
    --one d : Document |  --one sh : History |
        
        --some f.x and
        --f.x = d and 

        BrowserVersion.version != Safari  and

        navAboutUrlCore[nbc, u, d, (valid_about_url + invalid_about_url)] and
        --nbc.origin' = rbc.origin and
        (sandboxedIframeOrigin[nbc] or regularAboutIframeOrigin[rbc, nbc]) and
        --navAboutSecureContext[nbc, u, (valid_about_url + invalid_about_url) ] and
        nbc.isSecureContext' = rbc.isSecureContext and
        unchangedCreateIframe[rbc, nbc, d, rbc.currentDoc] and
        unchanged[NonActive, (NonActive <: src)] and 
        unchanged[NonActive, (NonActive <: context)]
        --unchanged[DataPath, data]

}

pred createIframeSafariAboutUrl [  rbc : BrowsingContext, nbc : BrowsingContext,  d : Document, u : Url] {
    --one d : Document |  --one sh : History |
        
        --some f.x and
        --f.x = d and 
        BrowserVersion.version = Safari and

        navAboutUrlCore[nbc, u,  d, (valid_about_url + invalid_about_url)] and
        --nbc.origin' = rbc.origin and
        --(sandboxedIframeOrigin[nbc] or regularAboutIframeOrigin[rbc, nbc]) and

        ---nbc.isSandboxed' = True -- let Alloy decide this
        ((nbc.isSandboxed' = True and nbc.origin' = OpaqueOrigin) or 
        (nbc.isSandboxed' = False and nbc.origin' = rbc.origin))
        --nbc.origin' = rbc.origin and
        --nbc.isSecureContext' = False and
        nbc.isSecureContext' = rbc.isSecureContext and
        --navAboutSecureContext[nbc, u, (valid_about_url + invalid_about_url) ] and
        unchangedCreateIframe[rbc, nbc,  d, rbc.currentDoc] and
        unchanged[NonActive, (NonActive <: src)] and 
        unchanged[NonActive, (NonActive <: context)]
        --unchanged[DataPath, data]

}

pred createIframeChromeInvalidDataAbsoluteUrl [  rbc : BrowsingContext, nbc : BrowsingContext,  d : Document, u : Url] {
   -- one d : Document |  --one sh : History |

        --some f.x and
        --f.x = d and 
        BrowserVersion.version != Safari and
        u in (invalid_absolute_url + invalid_data_url) and
        navErrorUrlCore[nbc, StartupUrl,  d] and
        nbc.isSecureContext' = False and
        nbc.origin' = OpaqueOrigin and
        --(sandboxedIframeOrigin[nbc] or regularErrorIframeOrigin[nbc]) and
        unchangedCreateIframe[rbc, nbc,  d, rbc.currentDoc] and
        unchanged[NonActive, (NonActive <: src)] and 
        unchanged[NonActive, (NonActive <: context)]
        --unchanged[DataPath, data]
}

pred createIframeSafariInvalidDataAbsoluteUrl [  rbc : BrowsingContext, nbc : BrowsingContext,  d : Document, u : Url] {
   -- one d : Document |  --one sh : History |

        --some f.x and
        --f.x = d and 
        BrowserVersion.version = Safari and
        u in (invalid_absolute_url + invalid_data_url) and
        one u2 : valid_about_url |
            navErrorUrlCore[nbc, u2,  d] and
            --navAboutSecureContext[nbc, u2, valid_about_url ] and
            nbc.isSecureContext' = decideSecureContext[nbc, u2] and
            (sandboxedIframeOrigin[nbc] or regularErrorIframeOrigin[nbc]) and
            unchangedCreateIframe[rbc, nbc,  d, rbc.currentDoc] and
            unchanged[NonActive, (NonActive <: src)] and 
            unchanged[NonActive, (NonActive <: context)]
        --unchanged[DataPath, data]
}


/*pred createIframeErrorUrl [  rbc : BrowsingContext, nbc : BrowsingContext, w : Iframe, d : Document, u : Url] {
   -- one d : Document |  --one sh : History |

        --some f.x and
        --f.x = d and 
        u !in (valid_absolute_url + valid_data_url + valid_blob_url + valid_about_url + invalid_absolute_url + invalid_data_url + invalid_blob_url + invalid_about_url ) and
        navErrorUrlCore[nbc, u, w, d] and
        nbc.isSecureContext' = False and
        (sandboxedIframeOrigin[nbc] or regularErrorIframeOrigin[nbc]) and
        unchangedCreateIframe[rbc, nbc, w, d, rbc.currentDoc] and
        unchanged[NonActive, (NonActive <: src)] and 
        unchanged[NonActive, (NonActive <: context)]
        --unchanged[DataPath, data]
}
*/