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
    BrowsingContext.opening = none
    BrowsingContext.accesses = none

}



fact {
    one nbc : BrowsingContext | umInit[nbc]
    #Browser.blobs = 0
    --#Document.elements = 0

}


run create_iframe_test {
    eventually {
	one nbc : BrowsingContext {
		once {
			some nbc.currentDoc.elements <: Document and some nbc.nestedBcs
		}
		after {
			one f : CreateIframe | f.bc in nbc.nestedBcs
				
		}
	}
        
    }
    
} for 5

run doc_write_test {
	eventually {
        some DocumentWrite
    }
} for 4 but 7 Url, 7 Document, 6 BrowsingContext

run popup_test {
	eventually {
        some Popup
    }
} for 4 but 7 Url, 7 Document, 6 BrowsingContext



run cameraAccess {
    eventually {
        one nbc : BrowsingContext | some m : Media { 
            m in nbc.accesses
        }
    }
} for 4 
