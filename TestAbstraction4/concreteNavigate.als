module concreteNavigate 


open concreteNavigateCore
open frameConditions
--open scmCallFunction
open concreteSecureContext



pred navigateOrigin [nbc : BrowsingContext, u : Url] {
        nbc.win in TopLWindow implies (
            nbc.origin' = origin[u] and 
            unchanged[nbc, isSandboxed] and 
            unchanged[nbc, sandboxWaitingNavigate]
        )else (
            (nbc.sandboxWaitingNavigate = True or nbc.isSandboxed = True) implies (
                nbc.isSandboxed' = True and 
                nbc.origin' = OpaqueOrigin and
                nbc.sandboxWaitingNavigate' = False
            )else (
                nbc.origin' = origin[u] and
                unchanged[nbc, isSandboxed] and 
                unchanged[nbc, sandboxWaitingNavigate]
                --nbc.isSandboxed' = False and 
                --nbc.sandboxWaitingNavigate' = False
            )
        )
}

pred navigateAbsoluteUrlDeny [ nbc : BrowsingContext, d : Document, d2 : Document, u : Url, s : Server] {

        /*u in valid_absolute_url and

        w in Iframe and 
        some s.xframeOptions[d] and 
        ((s.xframeOptions[d].option = Deny) or (s.xframeOptions[d].option = SameOrigin and rbc.origin != s.origin )) and*/

                (nbc.sandboxWaitingNavigate = True implies (
                    nbc.isSandboxed' = True and 
                    nbc.origin' = OpaqueOrigin and
                    nbc.sandboxWaitingNavigate' = False
                )else (
                    nbc.isSandboxed' = nbc.isSandboxed and 
                    nbc.origin' = OpaqueOrigin and 
                    nbc.sandboxWaitingNavigate' = False
                )) and 
                BrowserVersion.version = Safari implies (
                    some nbc.currentDoc implies (
                        nbc.isSecureContext' = decideSecureContext[nbc, nbc.currentDoc.src] and
                        unchangedAbsNavSafariXFOptionsNested[nbc]

                    )else (
                        one u2 : Url |
                            u2 in valid_about_url and 
                            nbc.accesses' = none and
                            nbc.opening' = none and
                            navAboutUrlCore[nbc, u2, d2, valid_about_url] and 
                            nbc.isSecureContext' = decideSecureContext[nbc, u2] and
                            --navAboutSecureContext[nbc, u2, valid_about_url] and 
                            unchangedNavigateAbsolute[nbc, d2] --and
                            --unchanged[NonActive, (NonActive <: src)] and 
                            --unchanged[NonActive - (d2.^elements <: NonActive), (NonActive <: context)]
                    )
                )else (
                    d in ErrorDocument and 
                    nbc.accesses' = none and
                    nbc.opening' = none and
                    navErrorUrlCore[nbc, StartupUrl, d2] and 
                    nbc.isSecureContext' = False and 
                    unchangedNavigateAbsolute[nbc, d2] --and
                    --unchanged[NonActive, (NonActive <: src)] and 
                    --unchanged[NonActive - (d2.^elements <: NonActive), (NonActive <: context)]
                    
                )
        
}

--d2 = old document
pred navigateAbsoluteUrl [nbc : BrowsingContext, d : Document, d2 : Document, u : Url, s : Server] {

    --w in Iframe implies (

        u in valid_absolute_url and

        --(w in Iframe and some s.xframeOptions[d] and ((s.xframeOptions[d].option = Deny) or (s.xframeOptions[d].option = SameOrigin and nbc.origin != s.origin ))) implies (

                /*nbc.isSandboxed' = True and 
                    nbc.origin' = OpaqueOrigin and
                    nbc.sandboxWaitingNavigate' = False and
                    --nbc.isSecureContext' = decideSecureContext[nbc, u] and
                    unchangedAbsNavSafariXFOptionsNested[nbc, w]*/


                /*(nbc.sandboxWaitingNavigate = True implies (
                    nbc.isSandboxed' = True and 
                    nbc.origin' = OpaqueOrigin and
                    nbc.sandboxWaitingNavigate' = False  
                    
                )else (
                    nbc.isSandboxed' = nbc.isSandboxed and 
                    nbc.origin' = OpaqueOrigin and 
                    nbc.sandboxWaitingNavigate' = False 
                )) and 
                
                BrowserVersion.version = Safari implies (
                    some w.doc implies (
                        --w.doc = d2 and
                        --unchanged[d2, (Document <: src)] and
                        --unchanged[d2, elements] and
                        nbc.isSecureContext' = decideSecureContext[nbc, u] and
                        unchangedAbsNavSafariXFOptionsNested[nbc, w]

                    )else (
                        one u2 : Url |
                            u2 in valid_about_url and 
                            w.accesses' = none and
                            navAboutUrlCore[nbc, u2, w, d, valid_about_url] and 
                            nbc.isSecureContext' = decideSecureContext[nbc, u2] and
                            --navAboutSecureContext[nbc, u2, valid_about_url] and 
                            unchangedNavigateAbsolute[nbc, w, d] --and
                            --unchanged[NonActive, (NonActive <: src)] and 
                            --unchanged[NonActive - (d2.^elements <: NonActive), (NonActive <: context)]
                    )
                )else (
                    d in ErrorDocument and 
                    w.accesses' = none and
                    navErrorUrlCore[nbc, StartupUrl, w, d] and 
                    nbc.isSecureContext' = False and 
                    unchangedNavigateAbsolute[nbc, w, d] --and
                    --unchanged[NonActive, (NonActive <: src)] and 
                    --unchanged[NonActive - (d2.^elements <: NonActive), (NonActive <: context)]
                    
                )*/



        --)
        --(w) implies (

            --(w in TopLWindow or (w in Iframe and no s.xframeOptions[d] )) and

            navAbsUrlCore[nbc, u, d] and
            --(navAbsSecureContext[nbc, u] or navInSecureContext[nbc, u] ) and

            nbc.isSecureContext' = decideSecureContext[nbc, u] and


            navigateOrigin[nbc, u] and

            --noDocInside[d.elements] and 
            addNavigateNoNestedBcs[nbc] and
            
            /*(noDocInside[d.elements] implies addNavigateNoNestedBcs[nbc]
                else addNavigateNestedBcs[d, nbc]
            ) and*/
            --(addNavigateNoNestedBcs[d, nbc] or addNavigateNestedBcs[d, nbc] ) and
            unchangedNavigateNested[nbc, d, d2] 

        --)

    /*) else (

            navAbsUrlCore[nbc, u, w, d] and
            (navAbsSecureContext[nbc, u] or navInSecureContext[nbc, u] ) and


            navigateOrigin[nbc, w, u] and
            
            (noDocInside[d.elements] implies addNavigateNoNestedBcs[nbc]
                else addNavigateNestedBcs[d, nbc]
            ) and
            --(addNavigateNoNestedBcs[d, nbc] or addNavigateNestedBcs[d, nbc] ) and
            unchangedNavigateNested[nbc, w, d] 


    )*/

}


/*
pred navigateAbsoluteUrl [nbc : BrowsingContext, w : Window, d : Document, u : Url, s : Server] {
    --one d : Document |  --one sh : History |

        --some f.x and 
        --f.x = d and
        ((w in Iframe) and (some s.xframeOptions[d] and ((s.xframeOptions[d].option = Deny) or (s.xframeOptions[d].option = SameOrigin and nbc.origin != s.origin )))) implies (

             --implies (
                
                (nbc.sandboxWaitingNavigate = True implies (
                    nbc.isSandboxed' = True and 
                    nbc.origin' = OpaqueOrigin and
                    nbc.sandboxWaitingNavigate' = False
                )else (
                    nbc.isSandboxed' = nbc.isSandboxed and 
                    nbc.origin' = OpaqueOrigin and 
                    nbc.sandboxWaitingNavigate' = False
                )) and 
                BrowserVersion.version = Safari implies (
                    some w.doc implies (
                        w.doc = d and
                        unchangedAbsNavSafariXFOptionsNested[nbc, w, d]

                    )else (
                        one u2 : Url |
                            u2 in valid_about_url and 
                            navAboutUrlCore[nbc, u2, w, d] and 
                            navAboutSecureContext[nbc, u2] and 
                            unchangedNavigate[nbc, w, d] and
                            unchanged[NonActive, (NonActive <: src)] and 
                            unchanged[NonActive, (NonActive <: context)]
                    )
                )else (
                    d in ErrorDocument and 
                    navErrorUrlCore[nbc, StartupUrl, w, d] and 
                    nbc.isSecureContext' = False and 
                    unchangedNavigate[nbc, w, d] and
                    unchanged[NonActive, (NonActive <: src)] and 
                    unchanged[NonActive, (NonActive <: context)]
                    
                )
                
            --)
        )else (

            navAbsUrlCore[nbc, u, w, d] and
            (navAbsSecureContext[nbc, u] or navInSecureContext[nbc, u] ) and


            navigateOrigin[nbc, w, u] and
            
            (noDocInside[d.elements] implies addNavigateNoNestedBcs[nbc]
                else addNavigateNestedBcs[d, nbc]
            ) and
            --(addNavigateNoNestedBcs[d, nbc] or addNavigateNestedBcs[d, nbc] ) and
            unchangedNavigateNested[nbc, w, d] 
            --unchanged[DataPath, data]

        )
        
}
*/

pred navigateDataHtmlUrl [ nbc : BrowsingContext, d : Document, d2 : Document, u : Url] {
    --one d : Document |  --one sh : History |

        --some f.x and
        --f.x = d and 

        navDataHtmlUrlCore[nbc, u, d] and
        --navInSecureContext[nbc, u] and

        nbc.isSecureContext' = decideSecureContext[nbc, u] and

        --nbc.origin' = origin[u] and
        navigateOrigin[nbc, u] and
        --(addNavigateNoNestedBcs[d, nbc] or addNavigateNestedBcs[d, nbc] ) and

        --noDocInside[d.elements] and 
        addNavigateNoNestedBcs[nbc] and
        /*(noDocInside[d.elements] implies addNavigateNoNestedBcs[nbc]
            else addNavigateNestedBcs[d, nbc]
        ) and*/
        unchangedNavigateNested[nbc, d, d2] 
        --unchanged[DataPath - f.(Navigate <: url).path, data]
        
}


pred navigateDataScriptUrl [ nbc : BrowsingContext, d : Document, d2 : Document, u : Url] {
    /*one d : Document |  /*one sh : History |*/ one na : NonActive |

        --some f.x and
        --f.x = d and 

        navDataScriptUrlCore[nbc, u, d, na] and
        --navInSecureContext[nbc, u] and

        nbc.isSecureContext' = decideSecureContext[nbc, u] and
        --nbc.origin' = origin[u] and
        navigateOrigin[nbc, u] and
        unchangedNavigate[nbc, d, d2] and
        nbc.nestedBcs' = none and
        unchanged[NonActive - na, (NonActive <: src)] and 
        unchanged[NonActive - (na + (d2.^elements <: NonActive) ), (NonActive <: context)]
        --unchanged[DataPath, data]
}

pred navigateBlobBlobsHtmlUrl [ nbc : BrowsingContext,  d : Document, d2 : Document, u : Url, blbCntx : BrowsingContext] {


        navBlobBlobsHtmlUrlCore[nbc, u, d] and 
        u in Browser.blobs[blbCntx] and
        /*(w in TopLWindow implies (
            (navBlobSecureContext[nbc, u] or navBlobInSecureContext[nbc, u] or navBlobNullOriginInSecureContext[nbc, u])
        )else (
            (navAbsSecureContext[nbc, u] or navInSecureContext[nbc, u] )
        )) and*/

        nbc.isSecureContext' = decideSecureContext[nbc, u] and
        
        --nbc.origin' = origin[u] and
        navigateOrigin[nbc, u] and
        --(addNavigateNoNestedBcs[d, nbc] or addNavigateNestedBcs[d, nbc] ) and

        --noDocInside[d.elements] and 
        addNavigateNoNestedBcs[nbc] and
        /*(noDocInside[d.elements] implies addNavigateNoNestedBcs[nbc]
            else addNavigateNestedBcs[d, nbc]
        ) and*/
        unchangedNavigateNested[nbc, d, d2] 
}



pred navigateBlobBlobsScriptUrl [ nbc : BrowsingContext, d : Document, d2 : Document, u : Url, blbCntx : BrowsingContext] {
   /* one d : Document |  /*one sh : History |*/ one na : NonActive |


        --some f.x and

        navBlobBlobsScriptUrlCore[nbc, u, d, na] and
        u in Browser.blobs[blbCntx] and

        /*(w in TopLWindow implies (
            (navBlobSecureContext[nbc, u] or navBlobInSecureContext[nbc, u] or navBlobNullOriginInSecureContext[nbc, u])
        )else (
            (navAbsSecureContext[nbc, u] or navInSecureContext[nbc, u] )
        )) and*/

        nbc.isSecureContext' = decideSecureContext[nbc, u] and

        --nbc.origin' = origin[u] and

        navigateOrigin[nbc, u] and

        nbc.nestedBcs' = none and

        unchangedNavigate[nbc, d, d2] and
        unchanged[NonActive - na, (NonActive <: src)] and 
        unchanged[NonActive - (na + (d2.^elements <: NonActive) ), (NonActive <: context)] 
        --unchanged[DataPath, data]
                            
}



pred navigateBlobNoBlobsUrl [ nbc : BrowsingContext, d : Document, d2 : Document, u : Url, blbCntx : BrowsingContext] {
    --one d : Document |  --one sh : History |

        --some f.x and
        --f.x = d and 

        navBlobNoBlobsUrlCore[nbc, u, d] and
        u !in Browser.blobs[blbCntx] and
        nbc.isSecureContext' = False and
        --nbc.origin' = OpaqueOrigin and

        (BrowserVersion.version = Safari implies nbc.origin' = StartupOrigin
        else nbc.origin' = OpaqueOrigin ) and

        unchanged[nbc, isSandboxed] and 
        unchanged[nbc, sandboxWaitingNavigate] and
        --nbc.nestedBcs' = none and
        unchangedNavigate[nbc, d, d2] and
        unchanged[NonActive, (NonActive <: src)] and 
        unchanged[NonActive - (d2.^elements <: NonActive), (NonActive <: context)]
        --unchanged[DataPath, data]
}


pred navigateAboutUrl [  nbc : BrowsingContext, d : Document, d2 : Document, u : Url] {
    --one d : Document |  --one sh : History |
        
        --some f.x and
        --f.x = d and 

        navAboutUrlCore[nbc, u, d, valid_about_url] and
        --nbc.origin' = origin[u] and

        (nbc.win in TopLWindow implies (
            nbc.origin' = origin[u] and 
            --nbc.isSecureContext' = False and
            unchanged[nbc, isSandboxed] and 
            unchanged[nbc, sandboxWaitingNavigate] 
        )else (
            --navAboutSecureContext[nbc, u, valid_about_url] and
            (nbc.sandboxWaitingNavigate = True or nbc.isSandboxed = True) implies (
                nbc.isSandboxed' = True and 
                nbc.origin' = OpaqueOrigin and
                nbc.sandboxWaitingNavigate' = False
            )else (
                nbc.origin' = nbc.~nestedBcs.origin and 
                --nbc.isSandboxed' = False and 
                --nbc.sandboxWaitingNavigate' = False and 
                unchanged[nbc, isSandboxed] and 
                unchanged[nbc, sandboxWaitingNavigate]
            )
        )) and

        nbc.isSecureContext' = decideSecureContext[nbc, u] and
        
        unchangedNavigate[nbc, d, d2] and
        nbc.nestedBcs' = none and
        unchanged[NonActive, (NonActive <: src)] and 
        unchanged[NonActive - (d2.^elements <: NonActive), (NonActive <: context)]
        --unchanged[DataPath, data]

}



pred navigateErrorUrl [ nbc : BrowsingContext, d : Document, d2 : Document, u : Url, allowedUrls : set Url] {
   -- one d : Document |  --one sh : History |

        --some f.x and
        --f.x = d and 
        --u !in valid_blob_url and
        u !in allowedUrls and --(valid_absolute_url + valid_data_url + valid_blob_url + valid_about_url) and
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
        unchangedNavigate[nbc, d, d2] and
        unchanged[NonActive, (NonActive <: src)] and 
        unchanged[NonActive - (d2.^elements <: NonActive), (NonActive <: context)]
        --unchanged[DataPath, data]
}

pred resetIframe [d2 : Document] {
    (
        all d : d2.^elements <: Document |

        let nbc = d.~currentDoc | --let w = nbc.window |


            d.elements' = none and

            nbc.origin' = StartupOrigin and
            nbc.currentDoc' = none and 
            nbc.isSandboxed' = none and 
            nbc.isSecureContext' = none and 
            nbc.sessionHistory' = none and 
            nbc.sandboxWaitingNavigate' = none and 
            nbc.nestedBcs' = none and
            --w.doc' = none and 
            nbc.opening' = none and 
            nbc.accesses' = none
    ) and 
    (
        all na : d2.^elements <: NonActive |

            na.(NonActive <: context') = none
    ) and 
    (
        all s : d2.^elements <: Script |

            s.(Script <: context') = none
    )

}

/*
pred unchangedIframe [d2 : Document] {
    (
        all d : d2.^elements <: Document |

        let nbc = d.~currentDoc | let w = nbc.window |

            unchanged[d, elements] and 
            unchanged[nbc, origin] and
            unchanged[nbc, currentDoc] and
            unchanged[nbc, isSandboxed] and
            unchanged[nbc, isSecureContext] and
            unchanged[nbc, sessionHistory] and
            unchanged[nbc, sandboxWaitingNavigate] and
            unchanged[nbc, nestedBcs] and

            unchanged[w, doc] and
            unchanged[w, opening] and 
            unchanged[w, accesses]

    ) and 
    (
        all na : d2.^elements <: NonActive |

            unchanged[na, (NonActive <: context) ]
    ) and 
    (
        all s : d2.^elements <: Script |

            unchanged[na, (Script <: context) ]
    )

}*/
