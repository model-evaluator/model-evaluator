module concretePopup

open concreteNavigateCore
open frameConditions
--open scmCallFunction
--open concreteCallFunction
open concreteSecureContext

pred popupAbsoluteUrl [ nbc : BrowsingContext, openerBc : BrowsingContext, d : Document, pu : Url ] {
        one sh : History |
                --some f.(Popup <: response) and 
                --f.(Popup <: response) = d and
                navAbsUrlCore[nbc, pu, d] and
                --d = c.to.resources[pu.path <: DirectoryPath] and
                --c.to in Server and 
                --c.to in Dns.map[pu.authority.domain] and 
                --no c.returns and
                --(popupAbsSecureContext[nbc, pu] or navInSecureContext[nbc, pu]) and
                nbc.isSecureContext' = decideSecureContext[nbc, pu] and
                nbc.origin' = origin[pu] and
                addToSessionHistory[nbc, sh, pu] and
                --(addNavigateNoNestedBcs[d, nbc] or addNavigateNestedBcs[d, nbc] ) and
                noDocInside[d.elements] and addNavigateNoNestedBcs[nbc] and
                /*(noDocInside[d.elements] implies addNavigateNoNestedBcs[nbc]
                    else addNavigateNestedBcs[d, nbc]
                ) and*/
                unchangedPopupNested[nbc, openerBc] 

        --unchanged[DataPath, data]
}


pred popupDataHtmlUrl [nbc : BrowsingContext, openerBc : BrowsingContext, d : Document, pu : Url ] {
        

        one u : Url | one sh : History |
                u in valid_about_url and
                --some f.(Popup <: response) and
                --f.(Popup <: response) = d and 

                pu in valid_data_url and
                (pu.path <: DataPath).media_type in Html and

                nbc.isSecureContext' = openerBc.isSecureContext and

                navAboutUrlCore[nbc, u, d, valid_about_url] and
                --c.to in Browser and no c.returns and
                nbc.origin' = openerBc.origin and
                addToSessionHistory[nbc, sh, u] and
                unchangedPopup[nbc, openerBc, d] and
                unchanged[NonActive, (NonActive <: src)] and 
                unchanged[NonActive, (NonActive <: context)]
        
}

pred popupDataScriptUrl [ nbc : BrowsingContext, openerBc : BrowsingContext, d : Document, pu : Url ] {

	one u : Url | one sh : History |
                u in valid_about_url and
                --some f.(Popup <: response) and
                --f.(Popup <: response) = d and 
                pu in valid_data_url and
                (pu.path <: DataPath).media_type in (ScriptMime + NonActiveMime) and

                nbc.isSecureContext' = openerBc.isSecureContext and

                navAboutUrlCore[nbc, u, d, valid_about_url] and
                --c.to in Browser and no c.returns and
                nbc.origin' = openerBc.origin and
                addToSessionHistory[nbc, sh, u] and
                unchangedPopup[nbc, openerBc, d] and
                unchanged[NonActive, (NonActive <: src)] and 
                unchanged[NonActive, (NonActive <: context)]
}

pred popupTupleOriginBlobBlobsHtmlUrl [ nbc : BrowsingContext, openerBc : BrowsingContext, d : Document, blbCntx : BrowsingContext, pu : Url ] {
    
    --one na : NonActive |

        --some f.(Popup <: response) and
        --f.(Popup <: response) = d and 
        navBlobBlobsHtmlUrlCore[nbc, pu, d] and
        --c.to in Browser and no c.returns and

        openerBc.origin in TupleOrigin and
        pu in Browser.blobs[blbCntx] and
        openerBc.origin = origin[pu] and

        nbc.isSecureContext' = openerBc.isSecureContext and

        nbc.origin' = origin[pu] and

        noDocInside[d.elements] and addNavigateNoNestedBcs[nbc] and

        /*(noDocInside[d.elements] implies addNavigateNoNestedBcs[nbc]
            else addNavigateNestedBcs[d, nbc]
        ) and*/

        unchangedPopup[nbc, openerBc, d] and
        unchanged[NonActive, (NonActive <: src)] and 
        unchanged[NonActive, (NonActive <: context)] 
        --unchanged[DataPath, data]
                            
}

pred popupTupleOriginBlobBlobsScriptUrl [ nbc : BrowsingContext, openerBc : BrowsingContext, d : Document, blbCntx : BrowsingContext, pu : Url ] {
    
    one na : NonActive |

        --some f.(Popup <: response) and
        --f.(Popup <: response) = d and 
        navBlobBlobsScriptUrlCore[nbc, pu, d, na] and
        --c.to in Browser and no c.returns and

        openerBc.origin in TupleOrigin and
        pu in Browser.blobs[blbCntx] and
        openerBc.origin = origin[pu] and

        nbc.isSecureContext' = openerBc.isSecureContext and

        nbc.origin' = origin[pu] and

        unchangedPopup[nbc, openerBc, d] and
        unchanged[NonActive - na, (NonActive <: src)] and 
        unchanged[NonActive - na, (NonActive <: context)] 
        --unchanged[DataPath, data]
                            
}

pred popupNonTupleOriginBlobBlobsHtmlUrl [ nbc : BrowsingContext, openerBc : BrowsingContext, d : Document, blbCntx : BrowsingContext, pu : Url ] {
    
    --one na : NonActive |

        --some f.(Popup <: response) and
        --f.(Popup <: response) = d and 
        navBlobBlobsHtmlUrlCore[nbc, pu, d] and
        --c.to in Browser and no c.returns and

        openerBc.origin !in TupleOrigin and
        pu in Browser.blobs[blbCntx] and --blbCntx should be nbc
        --wopener.bc.origin = origin[pu] and

        nbc.isSecureContext' = False and

        nbc.origin' = origin[pu] and

        noDocInside[d.elements] and addNavigateNoNestedBcs[nbc] and

        /*(noDocInside[d.elements] implies addNavigateNoNestedBcs[nbc]
            else addNavigateNestedBcs[d, nbc]
        ) and*/

        unchangedPopup[nbc, openerBc, d] and
        unchanged[NonActive, (NonActive <: src)] and 
        unchanged[NonActive, (NonActive <: context)] 
        --unchanged[DataPath, data]
                            
}

pred popupNonTupleOriginBlobBlobsScriptUrl [ nbc : BrowsingContext, openerBc : BrowsingContext, d : Document, blbCntx : BrowsingContext, pu : Url ] {
    
    one na : NonActive |

        --some f.(Popup <: response) and
        --f.(Popup <: response) = d and 
        navBlobBlobsScriptUrlCore[nbc, pu, d, na] and
        --c.to in Browser and no c.returns and

        openerBc.origin !in TupleOrigin and
        pu in Browser.blobs[blbCntx] and --blbCntx should be nbc
        --wopener.bc.origin = origin[pu] and

        nbc.isSecureContext' = False and

        nbc.origin' = origin[pu] and

        unchangedPopup[nbc, openerBc, d] and
        unchanged[NonActive - na, (NonActive <: src)] and 
        unchanged[NonActive - na, (NonActive <: context)] 
        --unchanged[DataPath, data]
                            
}

pred popupTupleOriginErrorUrl [ nbc : BrowsingContext, openerBc : BrowsingContext, d : Document, blbCntx : BrowsingContext, pu : Url ] {

        one sh : History |
                --some f.(Popup <: response) and
                --f.(Popup <: response) = d and 
                pu in valid_blob_url and
                navErrorUrlCore[nbc, pu, d] and
                --c.to in Browser and no c.returns and

                openerBc.origin in TupleOrigin and
                pu !in Browser.blobs[blbCntx] and
                openerBc.origin = origin[pu] and
                nbc.isSecureContext' = False and
                nbc.origin' = OpaqueOrigin and
                addToSessionHistory[nbc, sh, pu] and
                unchangedPopup[nbc, openerBc, d] and
                unchanged[NonActive, (NonActive <: src)] and 
                unchanged[NonActive, (NonActive <: context)]
                --unchanged[DataPath, data]
}
/*
pred popupBlobNoBlobsUrl [f : Function, c : Call, nbc : BrowsingContext, openerBc : BrowsingContext, d : Document, sh : History ] {

        some f.(Popup <: response) and
        f.(Popup <: response) = d and 
        navBlobNoBlobsUrlCore[nbc, pu, w, d, c, sh] and
        pu !in Browser.blobs[nbc] and
        unchangedPopup[nbc, w, d, wopener] and
        unchanged[NonActive, (NonActive <: src)] and 
        unchanged[NonActive, (NonActive <: context)]
        --unchanged[DataPath, data]
}*/

pred popupAboutUrl [ nbc : BrowsingContext, openerBc : BrowsingContext, d : Document, pu : Url ] {

        one sh : History |
                --some f.(Popup <: response) and
                --f.(Popup <: response) = d and 
                navAboutUrlCore[nbc, pu, d, valid_about_url] and
                --c.to in Browser and no c.returns and
                nbc.origin' = openerBc.origin and
                nbc.isSecureContext' = openerBc.isSecureContext and
                addToSessionHistory[nbc, sh, pu] and
                unchangedPopup[nbc, openerBc, d] and
                unchanged[NonActive, (NonActive <: src)] and 
                unchanged[NonActive, (NonActive <: context)]
                --unchanged[DataPath, data]

}

pred popupErrorUrl [ nbc : BrowsingContext, openerBc : BrowsingContext, d : Document, pu : Url ] {

        one sh : History |
                --some f.(Popup <: response) and
                --f.(Popup <: response) = d and 
                pu !in (valid_absolute_url + valid_data_url + valid_blob_url + valid_about_url) and
                navErrorUrlCore[nbc, pu, d] and
                --c.to in Browser and no c.returns and
                nbc.isSecureContext' = False and
                nbc.origin' = OpaqueOrigin and
                addToSessionHistory[nbc, sh, pu] and
                unchangedPopup[nbc, openerBc, d] and
                unchanged[NonActive, (NonActive <: src)] and 
                unchanged[NonActive, (NonActive <: context)]
                --unchanged[DataPath, data]
}


