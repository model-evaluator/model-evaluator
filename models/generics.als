module generics

abstract sig SchemeDelimiter {}
one sig SchDelimiter, SchSlashDelimiter extends SchemeDelimiter {}

abstract sig Delimiter {}
one sig SlashDelim, CommaDelim extends Delimiter{}

abstract sig Scheme {}
one sig Http, Https, Data, Blob, About extends Scheme {}

abstract sig Context {}
one sig SecureContext, InSecureContext extends Context {}

sig Text {}
sig Sandbox {}
sig Document {}

let serialisables = (Http+Https)
//let data_about = (Data+About)
//let data_about_blob = (Data+About+Blob)
sig HistoryState { url : one URL }
//sig HistoryState1 , HistoryState2, HistoryState3 { url : one URL }
abstract sig Origin {}

sig TupleOrigin extends Origin {       
        scheme : one Scheme,
        host : one Text
}

sig OpaqueOrigin, BlankOrigin, UnknownOrigin extends Origin {}

abstract sig Content {}

sig BlobContent extends Content {
        location : one Location
}{
	 location.href.scheme=Blob
}

sig Location {
        href :  one URL
        , origin :      one Origin
}


sig URL {
         scheme :                       lone Scheme
        , sch_delim :           lone SchemeDelimiter
        , host :                        lone Text
        , path_delim :          lone SlashDelim
        , path :                        lone Text
        , comma_delim :         lone CommaDelim
        , mime :                        lone Text
        , data :                        lone Text
        , creator_origin :      lone Origin
}


//sig TupleOrigin extends Origin {
//      scheme : one Scheme,
//      host : one Text
//}

pred proper_tuple [ u : URL] {
        u.scheme in serialisables and u.sch_delim = SchSlashDelimiter
                and some u.host //and some u.path_delim and some u.data
                and no u.data and no u.creator_origin and no u.comma_delim and no u.mime
}

pred proper_https [u : URL] {
	proper_tuple[u] and u.scheme = Https
}

pred proper_data [ u : URL] {
        u.scheme = Data and u.sch_delim = SchDelimiter
                and u.comma_delim = CommaDelim
                and no u.host and no u.path_delim and no u.path and no u.creator_origin
}

pred proper_blob [ u : URL] {
        u.scheme = Blob and u.sch_delim = SchDelimiter
                and some u.creator_origin and some u.path_delim and some u.data
                and no u.host and no u.path and no u.comma_delim and no u.mime
}

pred proper_about [u : URL]{
	 u.scheme = About and u.sch_delim = SchDelimiter
                and no u.comma_delim and no u.mime and no u.data
                and no u.host and no u.path_delim and no u.path and no u.creator_origin
}

pred only_path_url [u : URL]{
        some u.path and no u.scheme and no u.sch_delim and no u.host
        and no u.path_delim and no u.comma_delim and no u.mime
        and no u.data and no u.creator_origin
}

pred only_scheme_and_delim_url [u : URL]{
        no u.path and some u.scheme and some u.sch_delim and no u.host
        and no u.path_delim and no u.comma_delim and no u.mime
        and no u.data and no u.creator_origin
}

pred improper_blob [u : URL] {
        u.scheme=Blob and u.sch_delim = SchSlashDelimiter
        and some u.host and no u.path_delim and no u.comma_delim and no u.mime
        and no u.data and no u.creator_origin and no u.path
}



fun origin[u: URL]:one Origin {
        { o : Origin |
                        o = {{u.scheme in serialisables} => tuple_origin_gen[u] else opaque_origins[u]}
                }
}

fun tuple_origin_gen [u: URL]: one Origin {
        { o: Origin |
                o = {{proper_tuple[u]} => tuple_origin[u] else UnknownOrigin  }
         }
}

fun tuple_origin [u : URL] : one TupleOrigin {
        {o : TupleOrigin |
                o.scheme = u.scheme and o.host = u.host
                        }
}

fun opaque_origins [u: URL] : one Origin {
        { o : Origin |
                        o = {{u.scheme = Data or u.scheme = About } => data_about_origin[u] else blobs_and_others[u] }
                }
}

fun data_about_origin [u : URL] : one Origin {
        { o : Origin |
                        o = {{proper_data[u] or proper_about[u]} => OpaqueOrigin else data_about_slashdelim[u] }
                }
}

fun data_about_slashdelim [u : URL] : one Origin {
	{ o : Origin |
			  o = {{u.sch_delim = SchSlashDelimiter} => BlankOrigin else UnknownOrigin }
		}
}


fun blobs_and_others [u: URL] : one Origin {
        { o : Origin |
                        o = {{u.scheme = Blob} => blob_origin_gen[u] else UnknownOrigin }
                }
}

fun blob_origin_gen [u: URL] : one Origin {
        { o : Origin |
                        o = {{proper_blob[u] } => blob_origin[u] else improper_blob_origin[u] }
                }
}

fun blob_origin [u: URL] : one Origin {
        { o : Origin |
                        o = {{ u.creator_origin = OpaqueOrigin } => BlankOrigin else u.creator_origin}
                }
}

fun improper_blob_origin [u : URL] : one Origin {
        { o : Origin |
                        o = {{improper_blob[u]} => BlankOrigin else improper_blob_origin2[u] }
                }       
}

fun improper_blob_origin2 [u : URL] : one Origin {
        { o : Origin |
                        o = {{u.sch_delim = SchSlashDelimiter and no u.host} => BlankOrigin else UnknownOrigin }
                }       
}



