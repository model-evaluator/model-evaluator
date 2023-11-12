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
    constantResources : resources -> set HtmlResource,
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
sig DataUrl extends ValidUrl {
    content : one Document
}{
    scheme = Data
}

abstract sig BlobUrl extends ValidUrl {
    creator_origin : Origin,
    content : one Document
}{
    scheme = Blob
}

abstract sig AbsoluteUrl extends ValidUrl {
    domain : Domain,
    path : Path,
    port : Port
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

    always (all d : Document | all n : NonActive | n in d.elements <=> n.(NonActive <: context ) = d)
    always (all d : Document | all n : Script | n in d.elements <=> n.(Script <: context ) = d)
    always (all r : HtmlResource | all d2, d3 : Document | (r in d2.elements and r in d3.elements) implies d2 = d3 )
    always (all d : Document | d.src !in ValidUrl implies d in ErrorDocument )
    
}

abstract sig HtmlResource {}


sig Document extends HtmlResource {
    var src : one Url,
    var elements : set HtmlResource --+ Url
}{
    this !in elements
}

sig ErrorDocument in Document {}{
    elements = none
} 

sig Script extends HtmlResource {
    src : Url,
    var context : lone Document
}

sig NonActive extends HtmlResource {
    src : Url,
    var context : lone Document
}


sig Port {}



sig Domain { 
  subsumes: set Domain 
}
fact subsumesRule { partialOrder[subsumes, Domain] }


abstract sig Origin {}

sig TupleOrigin extends Origin {
    scheme : (Http+Https),
    domain : Domain,
    port : Port
}

one sig OpaqueOrigin extends Origin {}
one sig StartupOrigin extends Origin {}



fun find_domain[u : Url] : Domain {
    {d : Domain |

            u in AbsoluteUrl implies (
                d = u.(AbsoluteUrl <: domain)
            )else (
                d = none
            )

    }
}

fun origin [u : Url] : Origin {
    {o : Origin | 
        u in StartupUrl implies (
            o in StartupOrigin
        )else (
            u in AbsoluteUrl implies (
                o in TupleOrigin and o.scheme = u.scheme and o.domain = u.(AbsoluteUrl <: domain) and o.port = u.port
            )else (
                u in (AboutUrl + DataUrl) implies (
                    o in OpaqueOrigin
                )else (

                        u in BlobUrl implies (
                            o = u.creator_origin
                        )else (
                            o in StartupOrigin
                        )
                )
            )
        )
    }
}

fact {
    all u : Url | some origin[u]
}

fun secure_urls [] : Url {
    {u : Url |
        u.scheme in Https or 
        (u in BlobUrl and u.creator_origin in TupleOrigin and u.creator_origin.scheme in Https)
    }
}



