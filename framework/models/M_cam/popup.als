module popup

open navigateCore
open frameConditions
open secureContext

pred popupAbsoluteUrl [ nbc : BrowsingContext, openerBc : BrowsingContext, d : Document, pu : Url ] {
        one sh : History |

                navAbsUrlCore[nbc, pu, d] and

                nbc.isSecureContext' = decideSecureContext[nbc, pu] and
                nbc.origin' = origin[pu] and
                addToSessionHistory[nbc, sh, pu] and

                noDocInside[d.elements] and addNavigateNoNestedBcs[nbc] and

                unchangedPopupNested[nbc, openerBc] 

}




pred popupDataUrl [nbc : BrowsingContext, openerBc : BrowsingContext, d : Document, pu : Url ] {
        

        one sh : History |

                navDataHtmlUrlCore[nbc, pu, d] and

                addToSessionHistory[nbc, sh, pu] and
                nbc.origin' = OpaqueOrigin and
                nbc.isSecureContext' = True and
                
                unchangedPopup[nbc, openerBc, d] 
        
}


pred popupAbsoluteSameOriginBlobUrl [ nbc : BrowsingContext, openerBc : BrowsingContext, d : Document, pu : Url ] {
    
        one sh : History |
                navBlobBlobsHtmlUrlCore[nbc, pu, d] and

                openerBc.currentDoc.src in AbsoluteUrl and

                pu in Browser.blobs[BrowsingContext] and
                openerBc.origin = originW[pu, nbc.win] and

                nbc.isSecureContext' = openerBc.isSecureContext and

                nbc.origin' = originW[pu, nbc.win] and

                addToSessionHistory[nbc, sh, pu] and

                addNavigateNoNestedBcs[nbc] and


                unchangedPopup[nbc, openerBc, d] 

                            
}

pred popupAbsoluteCrossOriginBlobUrl [ nbc : BrowsingContext, openerBc : BrowsingContext, d : Document, pu : Url ] {
    
        one na : AboutUrl | one sh : History |

                navAboutUrlCore[nbc, pu, d, AboutUrl] and 

                openerBc.currentDoc.src in AbsoluteUrl and

                pu in Browser.blobs[BrowsingContext] and
                openerBc.origin != originW[pu, nbc.win] and

                nbc.isSecureContext' = openerBc.isSecureContext and

                nbc.origin' = openerBc.origin and

                addToSessionHistory[nbc, sh, na] and

                addNavigateNoNestedBcs[nbc] and

                unchangedPopup[nbc, openerBc, d] 

                            
}

pred popupBlobBlobUrl [ nbc : BrowsingContext, openerBc : BrowsingContext, d : Document, pu : Url ] {
    

        one sh : History |
                navBlobBlobsHtmlUrlCore[nbc, pu, d] and

                openerBc.origin in (BlankOrigin + TupleOrigin) and

                pu in Browser.blobs[BrowsingContext] and
                openerBc.origin = originW[pu, nbc.win] and

                nbc.isSecureContext' = decideSecureContext[nbc, pu] and

                nbc.origin' = originW[pu, nbc.win] and

                addToSessionHistory[nbc, sh, pu] and

                addNavigateNoNestedBcs[nbc] and


                unchangedPopup[nbc, openerBc, d] 

                            
}


pred popupOpaqueBlobBlobUrl [ nbc : BrowsingContext, openerBc : BrowsingContext, d : Document, pu : Url ] {
    

        one sh : History |
                navBlobBlobsHtmlUrlCore[nbc, pu, d] and

                openerBc.origin in (OpaqueOrigin) and

                pu in Browser.blobs[openerBc + openerBc.^~opening + openerBc.^opening] and
                openerBc.origin = originW[pu, nbc.win] and

                nbc.isSecureContext' = True and

                nbc.origin' = OpaqueOrigin and

                addToSessionHistory[nbc, sh, pu] and

                addNavigateNoNestedBcs[nbc] and


                unchangedPopup[nbc, openerBc, d] 

                            
}


pred popupDataSameBcNullBlobUrl [ nbc : BrowsingContext, openerBc : BrowsingContext, d : Document, pu : Url ] {
    

        one sh : History |
                navBlobBlobsHtmlUrlCore[nbc, pu, d] and

                openerBc.currentDoc.src in (DataUrl + AboutUrl) and

                pu in Browser.blobs[openerBc] and
                --openerBc.origin = originW[pu, nbc.win] and

                originW[pu, nbc.win] in BlankOrigin and

                nbc.isSecureContext' = True and

                nbc.origin' = OpaqueOrigin and

                addToSessionHistory[nbc, sh, pu] and

                addNavigateNoNestedBcs[nbc] and


                unchangedPopup[nbc, openerBc, d] 

                            
}

pred popupDataAboutCrossBcNullBlobUrl [ nbc : BrowsingContext, openerBc : BrowsingContext, d : Document, pu : Url ] {
    
        one sh : History |
                navBlobBlobsHtmlUrlCore[nbc, pu, d] and

                openerBc.currentDoc.src in (DataUrl + AboutUrl ) and

                pu in Browser.blobs[BrowsingContext] and
                pu !in Browser.blobs[openerBc + openerBc.^~opening + openerBc.^opening] and
                --openerBc.origin = originW[pu, nbc.win] and

                originW[pu, nbc.win] in BlankOrigin and

                nbc.isSecureContext' = False and

                nbc.origin' = BlankOrigin and

                addToSessionHistory[nbc, sh, pu] and

                addNavigateNoNestedBcs[nbc] and


                unchangedPopup[nbc, openerBc, d] 

                            
}

pred popupDataAboutOpenerBcNullBlobUrl [ nbc : BrowsingContext, openerBc : BrowsingContext, d : Document, pu : Url ] {
    
        one sh : History |
                navBlobBlobsHtmlUrlCore[nbc, pu, d] and

                openerBc.currentDoc.src in (DataUrl + AboutUrl ) and

                pu in Browser.blobs[BrowsingContext] and
                pu in Browser.blobs[openerBc + openerBc.^~opening + openerBc.^opening] and

                originW[pu, nbc.win] in BlankOrigin and

                nbc.isSecureContext' = True and

                nbc.origin' = OpaqueOrigin and
                addToSessionHistory[nbc, sh, pu] and

                addNavigateNoNestedBcs[nbc] and


                unchangedPopup[nbc, openerBc, d] 

                            
}

pred popupDataAboutTupleBlobUrl [ nbc : BrowsingContext, openerBc : BrowsingContext, d : Document, pu : Url ] {
    
        one sh : History |
                navBlobBlobsHtmlUrlCore[nbc, pu, d] and

                openerBc.currentDoc.src in (DataUrl + AboutUrl) and

                pu in Browser.blobs[BrowsingContext] and

                originW[pu, nbc.win] in TupleOrigin and

                nbc.isSecureContext' = decideSecureContext[nbc, pu] and 

                nbc.origin' = originW[pu, nbc.win] and

                addToSessionHistory[nbc, sh, pu] and

                addNavigateNoNestedBcs[nbc] and


                unchangedPopup[nbc, openerBc, d] 

                            
}




pred popupAboutUrl [ nbc : BrowsingContext, openerBc : BrowsingContext, d : Document, pu : Url ] {

        one sh : History |

                
                navAboutUrlCore[nbc, pu, d, AboutUrl] and

                (openerBc.origin in BlankOrigin implies (
                        nbc.isSecureContext' = False
                )else (
                        nbc.isSecureContext' = True
                )) and

                nbc.origin' = openerBc.origin and
                addToSessionHistory[nbc, sh, pu] and
                unchangedPopup[nbc, openerBc, d] 

}




pred popupErrorUrl [ nbc : BrowsingContext, openerBc : BrowsingContext, d : Document, pu : Url ] {

        one sh : History |

                pu in ErrorUrl and
                navErrorUrlCore[nbc, pu, d] and

                nbc.isSecureContext' = False and
                nbc.origin' = OpaqueOrigin and
                addToSessionHistory[nbc, sh, pu] and
                unchangedPopup[nbc, openerBc, d] 
}


