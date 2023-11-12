module popup

open navigateCore
open frameConditions
open secureContext

pred popupAbsoluteBlobUrl [ nbc : BrowsingContext, openerBc : BrowsingContext, d : Document, pu : Url ] {
        one sh : History |

                navAbsUrlCore[nbc, pu, d] and

                nbc.isSecureContext' = decideSecureContext[nbc, pu] and
                nbc.origin' = origin[pu] and
                addToSessionHistory[nbc, sh, pu] and


                unchangedPopup[nbc, openerBc, d] 

}




pred popupDataUrl [nbc : BrowsingContext, openerBc : BrowsingContext, d : Document, pu : Url ] {
        

        one na : AboutUrl | one sh : History |

                navAboutUrlCore[nbc, pu, d, AboutUrl] and 

                nbc.isSecureContext' = openerBc.isSecureContext and

                nbc.origin' = openerBc.origin and

                addToSessionHistory[nbc, sh, na] and

                unchangedPopup[nbc, openerBc, d] 
        
}


pred popupAboutUrl [ nbc : BrowsingContext, openerBc : BrowsingContext, d : Document, pu : Url ] {

        one sh : History |

                navAboutUrlCore[nbc, pu, d, AboutUrl] and

                nbc.isSecureContext' = openerBc.isSecureContext and

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


