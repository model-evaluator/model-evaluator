module scmCallFunction

open concreteBrowser

var lone abstract sig Call {
    --var from : lone Window,
    var to : lone ( Browser + Server),
    --var args : set NonActive,
    --var returns : set NonActive,
    var event : one Function,
    var urls : set Url
}{
    Url in urls
    
}

var lone abstract sig Function {
    var rootBc : BrowsingContext,
    var bc : BrowsingContext,
    var party : BrowsingContext
}

fact {
    always (all f : Function - WindowOpen | f.rootBc in Browser.bcs and (f.bc = f.rootBc or f.bc in f.rootBc.^nestedBcs) )
    always (all f : Function | 
        (f.party = f.bc ) or  
        (f.party != f.bc and 
            f.party.^~nestedBcs in Browser.bcs and  
            (f.party in f.bc.opening or f.bc in f.party.opening)
        )
    )
    always (all f : Function |
        let nbc = f.bc |
        let nbc2 = f.party |
        
           nbc = nbc2 or sameOriginPolicy[nbc, nbc2]

    )
    always (all f : DocumentWrite | 
        let nbc = f.bc |
        let nbc2 = f.targetBc |

            sameOriginPolicy[nbc, nbc2]
    )

    always (all f : AddSandbox | 
        let nbc = f.bc |
        let nbc2 = f.sandBc |

            sameOriginPolicy[nbc, nbc2]
    )
}

pred sameOriginPolicy [nbc : BrowsingContext, nbc2 : BrowsingContext] {
        nbc.origin != StartupOrigin and nbc2.origin != StartupOrigin and
        (
            (nbc.origin in OpaqueOrigin and nbc2.origin in OpaqueOrigin /*and equalsNonAbsoluteExceptFragment[nbc.currentDoc.src, nbc2.currentDoc.src]*/) or 
            (nbc.origin in BlankOrigin and nbc2.origin in BlankOrigin /*and equalsNonAbsoluteExceptFragment[nbc.currentDoc.src, nbc2.currentDoc.src]*/) or
            (nbc.origin in TupleOrigin and nbc2.origin in TupleOrigin and nbc.origin = nbc2.origin)
        )
}

var lone sig WindowOpen extends Function {}

var lone sig HistoryPushState extends Function {
    var tarUrl : one (Url + Path),
    var url : one Url
}{
    tarUrl in Path implies tarUrl in (DirectoryPath + BlobPath)
}

var lone sig LocationReplace extends Function {
    var url : one Url,
    var response : lone Document
}

var lone sig CreateBlob extends Function {

    var url : one Url,
    var creatorDoc : one Document
}


var lone sig Navigate extends Function {
    var url : one Url,
    var response : lone Document,
    --var party : one BrowsingContext
}

var lone sig Popup extends Function {
    var url : one Url,
    var response : lone Document,
    var newBc : one BrowsingContext
}

var lone sig CreateIframe extends Function {
    var url : one Url,
    --var party : one BrowsingContext,
    var response : one Document,
    var newBc : one BrowsingContext
}

var lone sig AddSandbox extends Function {
    var url : one Url,
    --var party : one BrowsingContext,
    var sandBc : one BrowsingContext
}

var lone sig DocumentWrite extends Function {
    var newEl : one HtmlResource,
    var targetBc : one BrowsingContext
}

var lone sig Access2Media extends Function {
    var media : one Media,
    var canAccess : lone BrowsingContext

}

var lone sig Skip extends Function {

}
