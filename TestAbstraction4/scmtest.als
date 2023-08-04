module scmtest


open scmexec



fact {

    always (some Call)

}



fact {
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

}






pred tzx {
    eventually {
        some  nbc, nbc2 : BrowsingContext {

            once {
                nbc in Browser.bcs
                blob_absolute_url[ nbc.currentDoc.src]
                nbc.origin = BlankOrigin
                nbc.isSecureContext = False
                nbc.isSandboxed = none
                nbc.sandboxWaitingNavigate = none
                nbc2 in nbc.nestedBcs
                nbc2.currentDoc = nbc.currentDoc.elements
                nbc2.origin = OpaqueOrigin
                nbc2.win in Iframe
                blob_absolute_url[nbc2.currentDoc.src]
                nbc2.isSandboxed = True

            }
           
           

            
        }
        
    }
}

run tzx_analysis {
    tzx 
} for 1 but 5 Url, 5 Path, 4 Scheme, 2 BrowsingContext, 2 Document, 3 Endpoint, 4 Origin, 4 History, 13 Function, 13 steps


run tzz_analysis {

    eventually {
        some nbc : BrowsingContext | some m : Media {
            nbc.currentDoc.src in valid_blob_url
            nbc.origin in OpaqueOrigin
            m in nbc.accesses
        }
    }
} for 1 but 5 Url, 5 Path, 4 Scheme, 3 BrowsingContext, 3 Document, 3 Endpoint, 4 Origin, 4 History, 15 Function, 15 steps --, exactly 13 steps



