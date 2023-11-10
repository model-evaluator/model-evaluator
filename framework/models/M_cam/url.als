module url

open util/relation
open helpers

enum Boolean {True, False}

enum Version {Safari, Chrome, RFC}


sig Media {
    permitted : set Domain
}

enum Window {TopLWindow, Iframe}

one sig Dns { 
    map: Domain -> one Server 
}

abstract sig Endpoint {}
sig Client extends Endpoint {}

sig Server extends Endpoint {
    origin : TupleOrigin,
    resources : set Path -> lone Document,
    xframeOptions : set Document -> lone XFrameOptions
}

enum XFrameOptionsType {Deny, SameOrigin}

sig XFrameOptions {
    option : one XFrameOptionsType
}

fact {
    always (all s : Server | s.xframeOptions.XFrameOptions in s.resources[Path] )
    always (all disj s1, s2 : Server | some s1.xframeOptions implies s1.xframeOptions.XFrameOptions !in s2.xframeOptions.XFrameOptions )
    always (all disj s1, s2 : Server | some s1.resources implies s1.resources[Path] !in s2.resources[Path] )

}

fact {
    always (all s : Server | some s[map])
}



enum Scheme {Http, Https, Data, Blob, About}

sig Path {}


abstract sig Url {
    scheme : lone Scheme
}

abstract sig ValidUrl extends Url {}

one sig AboutUrl extends ValidUrl {
}{
    scheme = About
}
sig DataUrl extends ValidUrl {}{
    scheme = Data
}

abstract sig BlobUrl extends ValidUrl {
    creator_origin : lone Origin
}{
    scheme = Blob
}

sig ValidBlobUrl extends BlobUrl {}
sig BlobAbsoluteUrl extends BlobUrl{//-> blob://skype.com
    domain : Domain
}{
    no creator_origin
} 

sig BlobNoPathUrl extends BlobUrl {//-> ://

}{
    no creator_origin
}
sig BlobOnlyDomainUrl extends BlobUrl {//-> skype.com
    domain : Domain
}{
    no creator_origin
}

abstract sig AbsoluteUrl extends ValidUrl {
    domain : Domain,
    path : Path
}

sig HttpsUrl extends AbsoluteUrl {}{
    scheme = Https
}
sig HttpUrl extends AbsoluteUrl {}{
    scheme = Http
}

abstract sig ErrorUrl extends Url {}
abstract sig StartupUrl extends Url {}{
    no scheme
}

fun invalid_about_url [] : ErrorUrl {
    {u : Url | u.scheme in About }
}
fun invalid_data_url [] : ErrorUrl {
    {u : Url | u.scheme in Data }
}
fun invalid_blob_url [] : ErrorUrl {
    {u : Url | u.scheme in Blob }
}
fun invalid_absolute_url [] : ErrorUrl {
    {u : Url | u.scheme in (Http + Https) }
}

fact {

    --always (all d : Document | all n : NonActive | n in d.elements <=> n.(NonActive <: context ) = d)
    --always (all d : Document | all n : Script | n in d.elements <=> n.(Script <: context ) = d)
    always (all d1, d2, d3 : Document | d1 in d2.elements and d1 in d3.elements implies d2 = d3 )
    always (all d : Document | d.src !in ValidUrl implies d in ErrorDocument )
    --always (all d1, d2 : Document | d1 in d2.^elements implies d1.src != d2.src )
    always (all d1, d2, d3 : Document | d1 in d3.elements and d2 in d3.elements implies d1 = d2 )

    always (all disj d1, d2, d3 : Document | (d1 in d2.elements and d2 in d3.elements) implies no (d1.elements <: Document) )
}

sig Document {
    var src : one Url,
    var elements : set Document --+ Url
}{
    this !in elements
}

sig ErrorDocument in Document {}{
    elements = none
} 



sig Domain { 
  subsumes: set Domain 
}
fact subsumesRule { partialOrder[subsumes, Domain] }


abstract sig Origin {}

sig TupleOrigin extends Origin {
    scheme : (Http+Https),
    domain : Domain
}

one sig OpaqueOrigin extends Origin {}
one sig StartupOrigin extends Origin {}
lone sig BlankOrigin extends Origin {}



fun find_domain[u : Url] : Domain {
    {d : Domain |

        u in BlobAbsoluteUrl implies (
            d = u.(BlobAbsoluteUrl <: domain)
        )else (
            u in AbsoluteUrl implies (
                d = u.(AbsoluteUrl <: domain)
            )else (
                d = none
            )
            
        )

    }
}

fun originY [u : Url] : Origin {
    {o : Origin |
        u in ValidBlobUrl implies (
            o = u.creator_origin
        )else (
            o = origin[u]
        )
    }
}

fun originW [u : Url, w : Window] : Origin {
    {o : Origin |

            w in TopLWindow implies (
                o = origin[u]
            )else (
                o = originY[u]
            )
        

    }
}

fun originX [u : Url, w : Window] : Origin {
    {o : Origin |

            w in TopLWindow implies (
                o = originZ[u]
            )else (
                o = originY[u]
            )
        

    }
}

fun originBlob [u : BlobUrl] : Origin {
    {o : Origin |
        u in ( BlobAbsoluteUrl + BlobNoPathUrl + BlobOnlyDomainUrl) implies (
            o in BlankOrigin
        ) else (
            u in ValidBlobUrl implies (
                u.creator_origin in OpaqueOrigin implies (
                    o in BlankOrigin
                )else (
                    u.creator_origin in TupleOrigin implies (
                        o in TupleOrigin and o = u.creator_origin
                    )else (
                        u.creator_origin in BlankOrigin implies (
                            o in BlankOrigin
                        )
                    )
                )
            )
            
        )

    }
}


fun origin [u : Url] : Origin {
    {o : Origin | 
        u in StartupUrl implies (
            o in StartupOrigin
        )else (
            u in AbsoluteUrl implies (
                o in TupleOrigin and o.scheme = u.scheme and o.domain = u.(AbsoluteUrl <: domain)
            )else (
                u in (AboutUrl + DataUrl) implies (
                    o in OpaqueOrigin
                )else (

                        u in BlobUrl implies (
                            o = originBlob[u]
                        )else (
                            o in StartupOrigin
                        )
                    
                        
                    
                )
            )
        )
    }
}

fun originZ [u : Url] : Origin {
    {o : Origin |
        (u in BlobUrl implies (

            (u in ValidBlobUrl implies (
                (u.creator_origin in TupleOrigin implies (
                    o in TupleOrigin and o = u.creator_origin
                )else (
                    o in OpaqueOrigin
                ))
            )else (
                o in OpaqueOrigin
            ))

        )else (
            o = origin[u]
        ))

    }
}

fact {
    all u : Url | some origin[u]
}


pred equalsBlob [u1 : Url, u2 : Url] {
    u1 in ValidBlobUrl
    u2 in ValidBlobUrl

    u1.creator_origin = u2.creator_origin    

}

pred equalsData [u1 : Url, u2 : Url] {
    u1 in DataUrl
    u2 in DataUrl
}

pred equalsAbout [u1 : Url, u2 : Url] {
    u1 in AboutUrl
    u2 in AboutUrl
}


pred equalsNonAbsolute [u1: Url, u2 : Url] {
    u1 !in AbsoluteUrl
    u2 !in AbsoluteUrl
    (equalsData[u1, u2] or equalsBlob[u1, u2] or equalsAbout[u1, u2])
}
