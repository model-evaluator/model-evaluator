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
    
    --(BrowsingContext - nbc) !in Browser.bcs


}


/*pred UrlManipulationDone[nbc : BrowsingContext, w : TopLWindow, d : Document] {

    nbc in Browser.bcs
    nbc.window = w
    w.bc = nbc
    w.doc = d 
    blob_absolute_url[d.src]
    nbc.currentDoc = d
    d.elements = none
    nbc.nestedBcs = none
    nbc.origin = BlankOrigin
    nbc.sessionHistory = none
    nbc.isSecureContext = none
    nbc.isSandboxed = none
    nbc.sandboxWaitingNavigate = none

}*/

/*pred UrlManipulationDone[nbc : BrowsingContext, nbc2 : BrowsingContext, nbc3 : BrowsingContext, d : Document] {

    nbc in Browser.bcs

    blob_absolute_url[d.src]
    nbc.currentDoc = d
    nbc.win in TopLWindow
    nbc.origin = BlankOrigin
    nbc.sessionHistory = none
    nbc.isSecureContext = False
    nbc.isSandboxed = False
    nbc.sandboxWaitingNavigate = False


    nbc2 in nbc.nestedBcs
    nbc2.currentDoc = nbc.currentDoc.elements
    nbc2.origin = OpaqueOrigin
    nbc2.win in Iframe
    blob_absolute_url[nbc2.currentDoc.src]
    nbc2.isSandboxed = True
    nbc2.isSecureContext = True
    nbc2.sessionHistory = none
    nbc2.sandboxWaitingNavigate = False


    nbc3.origin = StartupOrigin
    nbc3 !in nbc.^nestedBcs
    nbc3 !in nbc2.^nestedBcs
    nbc3 !in Browser.bcs and
    nbc3.currentDoc = none
    nbc3.isSandboxed = False
    nbc3.isSecureContext = none
    nbc3.sessionHistory = none
    nbc3.sandboxWaitingNavigate = False

}*/

/*fact {
    #BrowsingContext.currentDoc = 0
    BrowsingContext.origin = StartupOrigin
    #BrowsingContext.sessionHistory = 0
    BrowsingContext.isSecureContext = none
    BrowsingContext.isSandboxed = none
    BrowsingContext.sandboxWaitingNavigate = none
    #BrowsingContext.nestedBcs = 0
    #Browser.bcs = 0
    #Browser.blobs = 0
    #BrowsingContext.opening = 0
    #BrowsingContext.accesses = 0
    #Document.elements = 0
    BrowserVersion.version = Safari

}*/

/*fact {
    BrowserVersion.version = Safari
    #Browser.blobs = 0
    #BrowsingContext.opening = 0
    #BrowsingContext.accesses = 0
}*/

fact {
    one nbc : BrowsingContext | umInit[nbc]
    #Browser.blobs = 0
    #Document.elements = 0
    --BrowserVersion.version = Safari

}




pred tzx {
    eventually {
        some  nbc, nbc2, nbc3 : BrowsingContext {

            once {
                nbc in Browser.bcs
                nbc.currentDoc.src in BlobAbsoluteUrl
                --nbc.nestedBcs = none
                nbc.origin = BlankOrigin
                --nbc.sessionHistory = none
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
                --nbc3.window in nbc2.window.opening 
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

run tzx_analysis {
    tzx 
} for 1 but 6 Url, 3 Path, 3 Domain, 3 BrowsingContext, 3 Document, 3 Endpoint, 4 Origin, 6 History, 9 Function,  13 steps

run tzz_analysis {

    eventually {
        one nbc : BrowsingContext | one m : Media {
            nbc.currentDoc.src in BlobUrl
            nbc.origin in OpaqueOrigin
            m in nbc.accesses
        }
    }
} for 1 but 6 Url, 3 Path, 3 Domain, 3 BrowsingContext, 3 Document, 3 Endpoint, 6 Origin, 6 History, 9 Function, 13 steps



assert cameraAttack3 {

    always {
        no nbc : BrowsingContext | some m : Media {

            nbc.currentDoc.src !in AbsoluteUrl 
            m in nbc.accesses 
            
        }
    }

}
check cameraAttack3 for 1 but 6 Url, 2 Domain, 3 BrowsingContext, 3 Document, 3 Endpoint, 4 Origin, 4 History, 8 Function,  13 steps
--check cameraAttack3 for 1 but 6 Url, 3 Path, 3 Domain, 3 BrowsingContext, 3 Document, 4 Endpoint, 6 Origin, 7 History, 14 Function, 14 steps


--for 1 but 5 Url, 5 Path, 4 Scheme, 3 BrowsingContext, 3 Document, 3 Endpoint, 4 Origin, 4 History, 15 Function, 15 steps

run abc {
    eventually {
        one nbc : BrowsingContext {
            nbc.origin in BlankOrigin
            nbc.currentDoc.src = BlobAbsoluteUrl
        }
    }

} for 1 but 3 Url, 1 Path, 2 Domain, 1 BrowsingContext, 1 Document, 3 Endpoint, 4 Origin, 2 History


run def {
    eventually {
        one nbc : BrowsingContext | some m : Media {
        nbc.currentDoc.src = BlobAbsoluteUrl
        m in nbc.accesses
    }
    }

} for 1 but 6 Url, 2 Domain, 3 BrowsingContext, 3 Document, 3 Endpoint, 4 Origin, 2 History, 8 Function, exactly 12 steps



run def1 {
    eventually {
        one nbc : BrowsingContext {
            some nbc.currentDoc and
            some nbc.currentDoc.elements & Script
        }
    }

} for 1 but 3 Url, 2 Domain, 1 BrowsingContext, 1 Document, 3 Endpoint, 4 Origin, 2 History, 8 Function

