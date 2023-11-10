module navigateCore

open browser
open appendHistory
open secureContext
open sandbox



pred navAbsUrlCore [nbc : BrowsingContext, url : Url, d : Document ] {
    d !in Document.elements
    d !in ErrorDocument
    url in AbsoluteUrl
    d.src' = url 
    d.elements' = none
    nbc.currentDoc' = d 


}

pred navDataHtmlUrlCore [nbc : BrowsingContext, url : Url, d : Document ] {
    d !in Document.elements 
    d !in ErrorDocument
    url in DataUrl
    nbc.currentDoc' = d
    --w.doc' = d
    d.src' = url
    d.elements' = none--d.elements
}



pred navBlobBlobsHtmlUrlCore [nbc : BrowsingContext, url : Url, d : Document ] {
    d !in Document.elements
    d !in ErrorDocument
    url in ValidBlobUrl
    nbc.currentDoc' = d
    --w.doc' = d
    d.src' = url
    d.elements' = none

}


pred navBlobNoBlobsUrlCore [nbc : BrowsingContext, url : Url, d : Document ] {
    d !in Document.elements
    d in ErrorDocument
    url in BlobUrl
    nbc.currentDoc' = d
    d.src' = url
    d.elements' = none
    no nbc.nestedBcs' 

}

pred navAboutUrlCore [nbc : BrowsingContext, url : Url, d : Document, valid : set Url] {
    d !in Document.elements
    d !in ErrorDocument
    url in valid
    nbc.currentDoc' = d
    d.src' = url
    d.elements' = none
    no nbc.nestedBcs'


}

pred navErrorUrlCore [nbc : BrowsingContext, url : Url, d : Document ] {
    d !in Document.elements
    d in ErrorDocument

    d.elements' = none
    nbc.currentDoc' = d
    d.src' = url
    no nbc.nestedBcs'


}

pred noDocInside [els : set Document ] {
	no el : els | el in Document
}

pred addNavigateNoNestedBcs [ nbc : BrowsingContext] {
    --noDocInside[d1.elements] implies 
    no nbc.nestedBcs'
}

