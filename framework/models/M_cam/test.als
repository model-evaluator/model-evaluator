module test


open scmexec



fact {

    always (some Call)

}


pred umInit [nbc : BrowsingContext] {

    nbc = Browser.bcs 
    nbc.win in TopLWindow
    nbc.isSecureContext = True

    BrowsingContext.currentDoc = none
    BrowsingContext.origin = StartupOrigin
    BrowsingContext.isSandboxed = none
    BrowsingContext.sessionHistory = none
    (BrowsingContext - nbc).isSecureContext = none
    BrowsingContext.sandboxWaitingNavigate = none
    BrowsingContext.opening = none
    BrowsingContext.accesses = none

}

fact {
    one nbc : BrowsingContext | umInit[nbc]
    #Browser.blobs = 0
    #Document.elements = 0

}

assert cameraAttack {

    always {
        no nbc : BrowsingContext | some m : Media {

            nbc.currentDoc.src !in AbsoluteUrl 
            m in nbc.accesses 
            
        }
    }

}
check cameraAttack for 1 but 6 Url, 2 Domain, 3 BrowsingContext, 3 Document, 3 Endpoint, 4 Origin, 4 History, 8 Function,  13 steps





pred sequence_checker {
    eventually {
        some  nbc, nbc2, nbc3 : BrowsingContext {

            once {
                nbc in Browser.bcs
                nbc.currentDoc.src in BlobAbsoluteUrl
                nbc.origin = BlankOrigin
                nbc.isSecureContext = False
                nbc.isSandboxed = none
                nbc.sandboxWaitingNavigate = none
                nbc2 in nbc.nestedBcs
                nbc2.currentDoc = nbc.currentDoc.elements
                nbc2.origin = OpaqueOrigin
                nbc2.win in Iframe
                nbc2.currentDoc.src in BlobAbsoluteUrl
                nbc2.isSandboxed = True

            }
           
            eventually {
                nbc3 in Browser.bcs
                nbc3.origin in OpaqueOrigin
                decideUltimateSecureContext[nbc3]  = True
                nbc3.currentDoc.src in BlobAbsoluteUrl
            }
            after {
                some m : Media |
                 m in nbc3.accesses 
            }

            
        }
        
    }
}

run sequence_analysis {
    sequence_checker 
} for 1 but 6 Url, 3 Path, 3 Domain, 3 BrowsingContext, 3 Document, 3 Endpoint, 4 Origin, 6 History, 9 Function,  13 steps

run attack_reachable {

    eventually {
        one nbc : BrowsingContext | one m : Media {
            nbc.currentDoc.src in BlobUrl
            nbc.origin in OpaqueOrigin
            m in nbc.accesses
        }
    }
} for 1 but 6 Url, 3 Path, 3 Domain, 3 BrowsingContext, 3 Document, 3 Endpoint, 6 Origin, 6 History, 9 Function, 13 steps




run origin_reachable {
    eventually {
        one nbc : BrowsingContext {
            nbc.origin in BlankOrigin
            nbc.currentDoc.src = BlobAbsoluteUrl
        }
    }

} for 1 but 3 Url, 1 Path, 2 Domain, 1 BrowsingContext, 1 Document, 3 Endpoint, 4 Origin, 2 History


run url_reachable {
    eventually {
        one nbc : BrowsingContext | some m : Media {
        nbc.currentDoc.src = BlobAbsoluteUrl
        m in nbc.accesses
    }
    }

} for 1 but 6 Url, 2 Domain, 3 BrowsingContext, 3 Document, 3 Endpoint, 4 Origin, 2 History, 8 Function, exactly 12 steps
