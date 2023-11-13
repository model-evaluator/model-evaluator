module url_old_not_used

/**
** This is an old version of the url model, not used 
**/

open util/relation
open helpers

enum Boolean {True, False}


sig Media {
    permitted : set Domain
}



one sig Dns { 
    map: Domain -> one Server 
}

abstract sig Endpoint {}
sig Client extends Endpoint {}

sig Server extends Endpoint {
    origin : TupleOrigin,
    resources : set DirectoryPath -> lone HtmlResource,
    xframeOptions : set Document -> lone XFrameOptions
}

enum XFrameOptionsType {Deny, SameOrigin}

sig XFrameOptions {
    option : one XFrameOptionsType
}

fact {
    always (all s : Server | s.xframeOptions.XFrameOptions in s.resources[DirectoryPath] )
    always (all disj s1, s2 : Server | some s1.xframeOptions implies s1.xframeOptions.XFrameOptions !in s2.xframeOptions.XFrameOptions )
    always (all disj s1, s2 : Server | some s1.resources implies s1.resources[DirectoryPath] !in s2.resources[DirectoryPath] )

}


fact serverNotProvidesErrorDocument {
    always (all e : ErrorDocument | e !in (Server.resources[Path] /*+ Document.elements*/ ))

}



--each server maps to some domain
fact {
    always (all s : Server | some s[map])
}

fact {

    always (all d : Document | all n : NonActive | n in d.elements <=> n.(NonActive <: context ) = d)
    always (all d : Document | all n : Script | n in d.elements <=> n.(Script <: context ) = d)
    --always (all d1, d2, d3 : Document | d1 in d2.elements and d1 in d3.elements implies d2 = d3 )
    always (all d : Document | d.src !in (valid_absolute_url + valid_data_url + valid_about_url + valid_blob_url) implies d in ErrorDocument )
    --always (all d1, d2 : Document | d1 in d2.^elements implies d1.src != d2.src )

    always (all disj d1, d2, d3 : Document | (d1 in d2.elements and d2 in d3.elements) implies no (d1.elements <: Document) )
}

sig Document {
    var src : one Url,
    var elements : set HtmlResource --+ Url
}{
    this !in elements
}

sig ErrorDocument in Document {}{
    elements = none
} 

sig HtmlResource = Script + NonActive + Document {} 
sig Script extends Client {
    var src : lone Url,
    var context : lone Document
}

sig NonActive { 
    var src : lone Url,
    var context : lone Document
}

--let unchanged[s,r] = all x : s | x.(r)'=x.(r)

abstract sig Delimiter {}
one sig ColonDelim, DoubleSlashDelim, SlashDelim, CommaDelim, QueryDelim, CharDelim, AtDelim, SemiColonDelim extends Delimiter{}-- : // / , ? # @ ;

abstract sig Scheme {}

abstract sig SpecialScheme extends Scheme{}

one sig Http, Https /*File, WS, WSS, FTP*/ extends SpecialScheme{}

abstract sig LocalScheme extends Scheme {}

one sig Data, Blob, About extends LocalScheme {}

enum MimeType { Html, NonActiveMime, ScriptMime}

let serialisables = Http + Https


sig Domain { 
  subsumes: set Domain 
}
fact subsumesRule { partialOrder[subsumes, Domain] }

sig Text, Port {}
sig UUID {}

sig Authority {
    username : lone Text,
    username_delim : lone Delimiter,
    password : lone Text,
    userinfo_delim : lone Delimiter,
    --subdomain : set Text,
    domain : lone Domain,
    port_delim : lone Delimiter,
    port : lone Port

}

abstract sig Path {}

sig DirectoryPath extends Path {}
/*sig FilePath extends Path {}*/
sig AboutPath extends Path {}

sig DataPath extends Path {
    media_type : lone MimeType,
    encoding_delim : lone Delimiter,
    encoding : lone Text,
    data_delim : lone Delimiter,
    data : lone HtmlResource
}

sig BlobPath extends Path {
    creator_origin : lone (OpaqueOrigin + TupleOrigin),
    uuid_delim : lone Delimiter,
    uuid : lone UUID,
    media_type : lone MimeType,
    data : lone HtmlResource,
    domain : lone Domain 
}

sig Url{
    scheme : Scheme,
    sch_delim : lone Delimiter,
    auth_precede : lone Delimiter,
    authority : lone Authority,
    path_delim : lone Delimiter,
    path : lone Path,
    query_delim : lone Delimiter,
    query : lone Text,
    frag_delim : lone Delimiter,
    fragment : lone Text

}
lone sig StartupUrl extends Url {}

fact {
    all su : StartupUrl |
        no su.scheme and
        no su.sch_delim and
        no su.auth_precede and 
        no su.authority and
        no su.path_delim and
        no su.path and 
        no su.query_delim and
        no su.query and
        no su.frag_delim and
        no su.fragment
}

sig AbsoluteUrl in Url {}

fact {
    all a : AbsoluteUrl | a.scheme in (Https + Http)
}


abstract sig Origin {}

sig TupleOrigin extends Origin {
    scheme : Scheme,
    sch_delim : ColonDelim,
    auth_precede : DoubleSlashDelim,
    --subdomain : lone Text,
    domain : Domain,
    port_delim : lone ColonDelim,
    port : lone Port
}

one sig OpaqueOrigin extends Origin {}

--one sig NullOrigin extends Origin {}

one sig StartupOrigin extends Origin {}

lone sig BlankOrigin extends Origin {}

fact {
    BrowserVersion.version = Safari implies one BlankOrigin else no BlankOrigin
} 



fun origin [u : Url] : Origin {
    {o : Origin | 
        u in StartupUrl implies (
            o in StartupOrigin
        )else (


            u.scheme in serialisables => (
                u in (valid_http_url + valid_https_url) => (
                    o in TupleOrigin and
                    o.scheme = u.scheme and
                    --o.subdomain = u.authority.subdomain and
                    o.domain = u.authority.domain and
                    o.port = u.authority.port)
                else o in OpaqueOrigin
            )else (
                u in valid_blob_url implies (

                    BrowserVersion.version = Safari implies (
                        some u.auth_precede implies (
                            (valid_blob_path_predSafariNoPath[u.path] or valid_blob_path_predSafariOnlyDomain[u.path]) implies (
                                o = BlankOrigin
                            ) else (
                                o = StartupOrigin
                            )
                        ) else (
                            (u.path.creator_origin in OpaqueOrigin or u.path.creator_origin = none) implies o = BlankOrigin
                            else (
                                u.path.creator_origin in TupleOrigin implies o = u.path.creator_origin
                            )
                        )
                        
                    ) else (
                        o = u.path.creator_origin
                    )

                ) else (
                   
                        u in (valid_data_url + valid_about_url) implies (
                            o in OpaqueOrigin
                        ) else (
                            o in OpaqueOrigin
                        )
                    --)
                    
                )

            )
        )
        
    }
}

fact {
    all u : Url | some origin[u]
}




fun valid_authority [] : Authority {
    {a : Authority | 
        valid_feature[a, username, username_delim] and
        valid_feature[a, username, password] and
        valid_feature[a, username, userinfo_delim] and
        (some a.username_delim => a.username_delim = ColonDelim) and
        (some a.userinfo_delim => a.userinfo_delim = AtDelim) and
        --lone a.subdomain and
        some a.domain and
        --valid_feature[a, port, port_delim] and
        (lone a.port and some a.port <=> some a.port_delim  ) and
        (some a.port_delim => a.port_delim = ColonDelim)
    }
}

let valid_feature[u, s, d] = lone u.s and (some u.s <=> some u.d )


pred valid_http_feature[u: Url] {

    u.sch_delim = ColonDelim and
    u.auth_precede = DoubleSlashDelim and 
    some u.authority and
    u.authority in valid_authority[] and
    valid_feature[u, path, path_delim] and
    (some u.path_delim => u.path_delim = SlashDelim) and
    (some u.path => u.path in DirectoryPath) and
    valid_feature[u, query, query_delim] and
    (some u.query_delim => u.query_delim = QueryDelim) and
    valid_feature[u, fragment, frag_delim] and
    (some u.frag_delim => u.frag_delim = CharDelim)

}

fun valid_http_url [] : Url {
    {u : Url | u.scheme in Http and
        valid_http_feature[u]
    }
}

fun valid_https_url [] : Url {
    {u : Url | u.scheme in Https and
        valid_http_feature[u]
    }
}

fun valid_absolute_url [] : AbsoluteUrl {
    {u : AbsoluteUrl | 
        u = valid_https_url or u = valid_http_url
    }
}

fun valid_url [] : Url {
    {u : Url |
        u in (valid_about_url + valid_blob_url + valid_data_url + valid_absolute_url)
    }
}


fun valid_data_path [] : DataPath {
    {d: DataPath | some d.media_type and
        d.encoding_delim = SemiColonDelim and
        some d.encoding and
        d.data_delim = CommaDelim and
        some d.data and
        ((d.media_type in NonActiveMime and d.data in NonActive ) or
        (d.media_type in ScriptMime and d.data in Script ) or
        (d.media_type in Html and d.data in Document ))
        
    }
}

fun valid_data_url [] : Url {
    {u : Url | u.scheme in Data and
        u.sch_delim = ColonDelim and
        no u.auth_precede and
        no u.authority and
        no u.path_delim and
        some u.path and
        u.path in valid_data_path[] and
        no u.query_delim and
        no u.query and
        valid_feature[u, fragment, frag_delim] and
        (some u.frag_delim => u.frag_delim = CharDelim)
    }
}

pred valid_blob_path_pred [b : BlobPath] {
    some b.creator_origin and
    b.uuid_delim = SlashDelim and
    some b.uuid and 
    some b.media_type and 
    no b.domain and
    ((b.media_type in NonActiveMime and b.data in NonActive ) or
    (b.media_type in ScriptMime and b.data in Script ) or
    (b.media_type in Html and b.data in Document ))
}

pred valid_blob_path_predSafari [b : BlobPath] {
    lone b.creator_origin and
    lone b.uuid_delim and 
    lone b.uuid and
    lone b.media_type and
    lone b.data and 
    lone b.domain
}

pred valid_blob_path_predSafariNoPath [b : BlobPath] {
    no b.domain and
    no b.creator_origin and
    no b.uuid_delim and
    no b.uuid and
    no b.media_type and
    no b.data
}

pred valid_blob_path_predSafariOnlyDomain [b : BlobPath] {
    some b.domain and
    no b.creator_origin and
    no b.uuid_delim and
    no b.uuid and
    no b.media_type and
    no b.data

}



fun valid_blob_path [] : BlobPath {
    {b : BlobPath | 
        BrowserVersion.version != Safari implies (
            valid_blob_path_pred[b]
        ) else (
            valid_blob_path_pred[b] or valid_blob_path_predSafari[b]
        )
    }
}


fact {
    BrowserVersion.version != Safari implies no BlobPath.domain
}

fun valid_blob_url [] : Url {
    {u : Url | u.scheme in Blob and
        u.sch_delim = ColonDelim and
        --no u.auth_precede and
        no u.authority and
        no u.path_delim and
        some u.path and
        u.path in valid_blob_path[] and
        
        no u.query_delim and
        no u.query and
        valid_feature[u, fragment, frag_delim] and
        (some u.frag_delim => u.frag_delim = CharDelim)
    }
}


pred blob_absolute_url [u : Url] {

        u.scheme in Blob and 
        u.sch_delim = ColonDelim and 
        u.auth_precede = DoubleSlashDelim and
        no u.authority and 
        no u.path_delim and 
        some u.path and
        valid_blob_path_predSafariOnlyDomain[u.path] and 
        no u.query_delim and
        no u.query and
        no u.frag_delim and 
        no u.fragment


    
}

fact {
    always (all u : valid_blob_url | BrowserVersion.version != Safari implies no u.auth_precede)
    always (all u : valid_blob_url | some u.auth_precede implies u.auth_precede = DoubleSlashDelim)
    always (all u : valid_blob_url | some u.path.uuid_delim <=> some u.path.uuid)
    always (all disj u1, u2 : valid_blob_url | (some u1.path.uuid and some u2.path.uuid) implies u1.path.uuid != u2.path.uuid )
}

fun valid_about_url [] : Url {
    {u : Url | u.scheme in About and
        u.sch_delim = ColonDelim and
        no u.auth_precede and
        no u.authority and
        no u.path_delim and
        some u.path and
        u.path in AboutPath and
        no u.query_delim and
        no u.query and
        valid_feature[u, fragment, frag_delim] and
        (some u.frag_delim => u.frag_delim = CharDelim)
    }
}


pred equalsBlobExceptFragment [u1 : Url, u2 : Url] {
    u1 in valid_blob_url
    u2 in valid_blob_url

    u1.path = u2.path
    

}

pred equalsDataExceptFragment [u1 : Url, u2 : Url] {
    u1 in valid_data_url
    u2 in valid_data_url

    u1.path = u2.path
}

pred equalsAboutExceptFragment [u1 : Url, u2 : Url] {
    u1 in valid_about_url
    u2 in valid_about_url

    u1.path = u2.path
}


pred equalsNonAbsoluteExceptFragment [u1: Url, u2 : Url] {
    u1 !in valid_absolute_url
    u2 !in valid_absolute_url
    (equalsDataExceptFragment[u1, u2] or equalsBlobExceptFragment[u1, u2] or equalsAboutExceptFragment[u1, u2])
}



fun invalid_blob_url [] : Url {
    {u : Url | u.scheme in Blob and
        u !in valid_blob_url
    }
}

fun invalid_data_url [] : Url {
    {u : Url | u.scheme in Data and
        u !in valid_data_url
    }
}

fun invalid_absolute_url [] : Url {
    {u : Url | u.scheme in (Http + Https) and
        u !in valid_absolute_url
    }
}

fun invalid_about_url [] : Url {
    {u : Url | u.scheme in About and
        u !in valid_about_url
    }
}


run {
    some u : valid_https_url | some u.authority.username_delim and some u.frag_delim 
} for 4 but 1 Authority, 1 Url



run {

    some valid_data_url
} for 3 but 1 Url


run {

    some u : Url | u in valid_blob_url and valid_blob_path_predSafariNoPath[u.path] and some u.auth_precede --and no u.path.creator_origin --and no u.path.uuid
} for 4 but 1 Url


run {

    some u : BlobPath | valid_blob_path_predSafariNoPath[u] and valid_blob_path_predSafari[u]
}for 4 but 1 Url

/*
         foo://example.com:8042/over/there?name=ferret#nose
         \_/   \______________/\_________/ \_________/ \__/
          |           |            |            |        |
       scheme     authority       path        query   fragment
          |   _____________________|__
         / \ /                        \
         urn:example:animal:ferret:nose

*/
