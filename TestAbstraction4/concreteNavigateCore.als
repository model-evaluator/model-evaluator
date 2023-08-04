module concreteNavigateCore

---open concreteUrl
open concreteBrowser
--open orderings
open concreteHistory
--open scmCallFunction
open concreteSecureContext
open concreteSandbox



pred navAbsUrlCore [nbc : BrowsingContext, url : Url, d : Document ] {
    d !in Document.elements
    d !in ErrorDocument
    url in valid_absolute_url
    --c.to in Server
    --c.to in Dns.map[url.authority.domain]
    --d = c.to.resources[url.path <: DirectoryPath]
    d.src' = url 
    d.elements' = none--d.elements
    --nbc.origin' = origin[url]
    nbc.currentDoc' = d 
    --w.doc' = d
    --addToSessionHistory[nbc, sh, url]
    --(addNavigateNoNestedBcs[d, nbc] or addNavigateNestedBcs[d, nbc] )
    --no c.returns

}

pred navDataHtmlUrlCore [nbc : BrowsingContext, url : Url, d : Document ] {
    d !in Document.elements 
    d !in ErrorDocument
    url in valid_data_url
    (url.path <: DataPath).media_type = Html
    --c.to in Browser
    --nbc.origin' = origin[url]
    nbc.currentDoc' = d
    --w.doc' = d
    d.src' = url
    d.elements' = none--d.elements
    d = (url.path <: DataPath).data
    --no nbc.nestedBcs
    --no c.returns
    --addToSessionHistory[nbc, sh, url]
    --(addNavigateNoNestedBcs[d, nbc] or addNavigateNestedBcs[d, nbc] )
}


pred navDataScriptUrlCore [nbc : BrowsingContext, url : Url, d : Document, na : NonActive ] {
    d !in Document.elements
    d !in ErrorDocument
    url in valid_data_url
    (url.path <: DataPath).media_type in (ScriptMime + NonActiveMime)
    --c.to in Browser
    --nbc.origin' = origin[url]
    nbc.currentDoc' = d
    --w.doc' = d
    d.src' = url
    na.src' = none
    na.context' = d
    --no d.elements
    d.elements' =  na
    na = (url.path <: DataPath).data 
    no nbc.nestedBcs' 
    --no c.returns
    --addToSessionHistory[nbc, sh, url]
}

pred navBlobBlobsHtmlUrlCore [nbc : BrowsingContext, url : Url, d : Document ] {
    d !in Document.elements
    d !in ErrorDocument
    url in valid_blob_url
    (url.path <: BlobPath).media_type = Html
    --url in Browser.blobs[BrowsingContext]
    --c.to in Browser
    --nbc.origin' = origin[url]
    nbc.currentDoc' = d
    --w.doc' = d
    d.src' = url
    d.elements' = none--d.elements 
    d = (url.path <: BlobPath).data 
    --no nbc.nestedBcs'
    --no c.returns
    --addToSessionHistory[nbc, sh, url]

}

pred navBlobBlobsScriptUrlCore [nbc : BrowsingContext, url : Url, d : Document, na : NonActive ] {
    d !in Document.elements
    d !in ErrorDocument
    url in valid_blob_url
    (url.path <: BlobPath).media_type in (ScriptMime + NonActiveMime)
    --url in Browser.blobs[BrowsingContext]
    --c.to in Browser
    --nbc.origin' = origin[url]
    nbc.currentDoc' = d
    --w.doc' = d
    d.src' = url
    na.src' = none
    na.context' = d
    d.elements' = na
    --na = (url.path <: BlobPath).data 
    --no nbc.nestedBcs'
    --no c.returns
    --addToSessionHistory[nbc, sh, url]

}

pred navBlobNoBlobsUrlCore [nbc : BrowsingContext, url : Url, d : Document ] {
    d !in Document.elements
    d in ErrorDocument
    url in valid_blob_url
    --url !in Browser.blobs[BrowsingContext]
    --c.to in Browser
    --w.doc' = d
    --nbc.origin' = OpaqueOrigin
    nbc.currentDoc' = d
    d.src' = url
    d.elements' = none
    no nbc.nestedBcs' 
    --no c.returns
    --addToSessionHistory[nbc, sh, url]
}

pred navAboutUrlCore [nbc : BrowsingContext, url : Url, d : Document, valid : set Url] {
    d !in Document.elements
    d !in ErrorDocument
    url in valid
    --c.to in Browser
    --w.doc' = d
    --nbc.origin' = origin[url]
    nbc.currentDoc' = d
    d.src' = url
    d.elements' = none
    no nbc.nestedBcs'
    --no c.returns
    --addToSessionHistory[nbc, sh, url]

}

pred navErrorUrlCore [nbc : BrowsingContext, url : Url, d : Document ] {
    d !in Document.elements
    d in ErrorDocument
    /*url !in valid_absolute_url 
    url !in valid_data_url
    url !in valid_blob_url
    url !in valid_about_url*/
    --c.to in Browser
    --w.doc' = d
    d.elements' = none
    --nbc.origin' = OpaqueOrigin
    nbc.currentDoc' = d
    d.src' = url
    no nbc.nestedBcs'
    --no c.returns
    --addToSessionHistory[nbc, sh, url]

}

pred noDocInside [els : set HtmlResource ] {
	no el : els | el in Document
}

pred addNavigateNoNestedBcs [ nbc : BrowsingContext] {
    --noDocInside[d1.elements] implies 
    no nbc.nestedBcs'
}

