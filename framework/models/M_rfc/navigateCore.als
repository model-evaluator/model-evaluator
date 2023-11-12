module navigateCore

open browser
open appendHistory
open secureContext
open sandbox



pred navAbsUrlCore [nbc : BrowsingContext, url : Url, d : Document ] {

    url in AbsoluteUrl
    d.src' = url 
    d.elements' = d.elements
    nbc.currentDoc' = d 


}

pred navDataHtmlUrlCore [nbc : BrowsingContext, url : Url, d : Document ] {

    url in DataUrl
    nbc.currentDoc' = d
    d.src' = url
    url.(DataUrl <: content) = d
    d.elements' = d.elements
}



pred navBlobBlobsHtmlUrlCore [nbc : BrowsingContext, url : Url, d : Document ] {

    url in BlobUrl
    nbc.currentDoc' = d
    d.src' = url
    url.(BlobUrl <: content) = d
    d.elements' = d.elements

}



pred navAboutUrlCore [nbc : BrowsingContext, url : Url, d : Document, valid : set Url] {

    url in valid
    nbc.currentDoc' = d
    d.src' = url
    d.elements' = none
    no nbc.nestedBcs'


}

pred navErrorUrlCore [nbc : BrowsingContext, url : Url, d : Document ] {


    d.elements' = none
    nbc.currentDoc' = d
    d.src' = url
    no nbc.nestedBcs'


}

pred noDocInside [els : set Document ] {
	no el : els | el in Document
}

pred addNavigateNoNestedBcs [ nbc : BrowsingContext] {

    no nbc.nestedBcs'
}

