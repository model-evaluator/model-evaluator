module urlmanipulation

open scmCallFunction
open concreteBrowser
--open concreteTrust
open concreteHistory
open concreteNavigate

--open frameConditions


pred window_open [f : Function, c : Call] {

    let nbc = f.bc | --let w = nbc.window |

        --no c.from and 
        --no c.to and
        f.rootBc = nbc and 
        --w.bc = nbc and
        --nbc !in Browser.bcs and
        nbc !in BrowsingContext.nestedBcs and
        Browser.bcs' = Browser.bcs + nbc and
        nbc.origin = StartupOrigin and
        --no w.doc and
        no nbc.currentDoc and
        --nbc.opener = none and
        nbc.win in TopLWindow and
        --unchanged[Browser, cookies] and
        unchanged[Browser, blobs] and
        unchanged[BrowsingContext, (BrowsingContext <: origin)] and
        --unchanged[BrowsingContext, window] and
        unchanged[BrowsingContext, currentDoc] and
        unchanged[BrowsingContext, nestedBcs] and
        unchanged[BrowsingContext, sessionHistory] and
        unchanged[BrowsingContext, isSecureContext] and
        unchanged[BrowsingContext, isSandboxed] and
        unchanged[BrowsingContext, sandboxWaitingNavigate] and
        --unchanged[Window, doc] and
        unchanged[BrowsingContext, opening] and
        unchanged[BrowsingContext, accesses] and
        unchanged[Document, (Document <: src)] and
        unchanged[Document, elements] and
        unchanged[Script, (Script <: src)] and
        unchanged[Script, (Script <: context)] and
        unchanged[NonActive, (NonActive <: src)] and
        unchanged[NonActive, (NonActive <: context)] and 
        --unchanged[DataflowModule, accesses] and 
        unchanged[History, (History <: next)] and
        unchanged[History, (History <: prev)]
}

pred hpsDirectoryPath [u : Url, f : Function] {
    let x = f.(HistoryPushState <: url) |

        u in valid_absolute_url and 
        f.tarUrl in DirectoryPath and 
        x in valid_absolute_url and

        x.scheme = u.scheme and
        x.sch_delim = u.sch_delim and
        x.auth_precede = u.auth_precede and
        x.authority = u.authority and
        x.path_delim = SlashDelim and
        x.path = f.tarUrl-- and
        --x.query_delim = f.tarUrl.query_delim and
        --x.query = f.tarUrl.query and
        --x.frag_delim = f.tarUrl.frag_delim and
        --x.fragment = f.tarUrl.fragment

}



pred hpsAbsolute [u : Url, f : Function] {

    let x = f.(HistoryPushState <: url) |

        u in valid_absolute_url and
        f.tarUrl in valid_absolute_url and
        x in valid_absolute_url and
        origin[u] = origin[f.tarUrl] and

        --some sh.url.authority.username => sh.url.authority.username = tarUrl.authority.username 
        --some sh.url.authority.password => sh.url.authority.password = tarUrl.authority.password

        u.authority.username = f.tarUrl.authority.username and
        u.authority.password = f.tarUrl.authority.password and

        x.scheme = u.scheme and
        x.sch_delim = u.sch_delim and
        x.auth_precede = u.auth_precede and
        x.authority = u.authority and
        x.path_delim = f.tarUrl.path_delim and
        x.path = f.tarUrl.path and
        x.query_delim = f.tarUrl.query_delim and
        x.query = f.tarUrl.query and
        x.frag_delim = f.tarUrl.frag_delim and
        x.fragment = f.tarUrl.fragment

}

pred hpsNonAbsolute [u : Url, f : Function] {

    let x = f.(HistoryPushState <: url) |

        u !in valid_absolute_url and 
        f.tarUrl !in valid_absolute_url and 
        x !in valid_absolute_url and 

        --sh.url in (valid_blob_url + valid_data_url + valid_about_url) and
        --(((sh.url + f.tarUrl + x) in valid_blob_url) or ((sh.url + f.tarUrl + x) in valid_data_url) or ((sh.url + f.tarUrl + x) in valid_about_url) ) --and --doesnlt work
        equalsNonAbsoluteExceptFragment[u, f.tarUrl] and --works
        equalsNonAbsoluteExceptFragment[u, x] and --doesn't work --remember location replace doesnt put history!TODO
        --BrowserVersion.version = Safari implies (
        --    x.path.domain = f.tarUrl.path.domain
        --) and
        x.frag_delim = f.tarUrl.frag_delim and 
        x.fragment = f.tarUrl.fragment

}

pred hpsBlobNoPath [nbc : BrowsingContext, u : Url, f : Function] {--blob://
    let x = f.(HistoryPushState <: url) |

        u in valid_blob_url and 
        nbc.origin = BlankOrigin and --SAFARI
        origin[u] in BlankOrigin and
        some f.tarUrl.auth_precede and
        f.tarUrl in valid_blob_url and 
        f.tarUrl.path in valid_blob_path and 
        valid_blob_path_predSafariNoPath[f.tarUrl.path] and 

        x.scheme = u.scheme and
        x.sch_delim = u.sch_delim and
        x.auth_precede = f.tarUrl.auth_precede and
        x.authority = u.authority and
        x.path_delim = u.path_delim and
        x.path = f.tarUrl.path --and
        --x.query_delim = f.tarUrl.query_delim and
        --x.query = f.tarUrl.query and
        --x.frag_delim = f.tarUrl.frag_delim and
        --x.fragment = f.tarUrl.fragment
}

pred hpsBlobPath [nbc : BrowsingContext, u : Url, f : Function] {//skype.com
    let x = f.(HistoryPushState <: url) |

        u in valid_blob_url and 
        f.tarUrl in BlobPath and 
        --x in valid_blob_url and 

        origin[u] in BlankOrigin and
        nbc.origin = BlankOrigin and --SAFARI
        some u.auth_precede and

        valid_blob_path_predSafariNoPath[u.path] and

        valid_blob_path_predSafariOnlyDomain[f.tarUrl] and 

        --valid_blob_path_predSafariOnlyDomain[x.path] and

        x.scheme = u.scheme and
        x.sch_delim = u.sch_delim and
        x.auth_precede = u.auth_precede and
        x.authority = u.authority and
        x.path_delim = u.path_delim and
        x.path = f.tarUrl --and
        --x.query_delim = f.tarUrl.query_delim and
        --x.query = f.tarUrl.query and
        --x.frag_delim = f.tarUrl.frag_delim and
        --x.fragment = f.tarUrl.fragment
}

fact {

    --always (NNavigate in (Calls.(Calls <: prev) + Calls.(Calls <: prevs)) implies Call.event != Navigate )
}


pred history_push_state [f : Function, c : Call] {

    one sh : History | 
        let nbc = f.bc | let d = nbc.currentDoc |
        let u = f.(HistoryPushState <: url) |

        d.src' = u and

        addToSessionHistory[nbc, sh, u] and

        (hpsDirectoryPath[d.src, f] or hpsAbsolute[d.src, f] or 
            hpsNonAbsolute[d.src, f] or hpsBlobNoPath[nbc, d.src, f] or
                hpsBlobPath[nbc, d.src, f] 
        ) and

        --c.from.accesses' = c.from.accesses + nbc.sessionHistory + sh and 

        unchanged[Browser, bcs] and 
        --unchanged[Browser, cookies] and 
        unchanged[Browser, blobs]  and 
        unchanged[BrowsingContext, (BrowsingContext <: origin)] and 
        --unchanged[BrowsingContext, window] and 
        unchanged[BrowsingContext, currentDoc] and 
        unchanged[BrowsingContext, nestedBcs] and 
        unchanged[BrowsingContext - nbc, sessionHistory] and 
        unchanged[BrowsingContext, isSecureContext]  and 
        unchanged[BrowsingContext, isSandboxed] and 
        unchanged[BrowsingContext, sandboxWaitingNavigate] and
        --unchanged[Window, doc] and 
        unchanged[BrowsingContext, opening] and 
        unchanged[BrowsingContext, accesses] and 
        unchanged[Document - d, (Document <: src)] and 
        unchanged[Document, elements] and 
        unchanged[Script, (Script <: src)] and 
        unchanged[Script, (Script <: context)] and 
        unchanged[NonActive, (NonActive <: src)] and 
        unchanged[NonActive, (NonActive <: context)]


}

pred location_replaceAbsUrlDeny [f : Function, c : Call] {
    let nbc = f.bc | let u = f.(LocationReplace <: url) |
        let rbc = f.bc.~nestedBcs | 
        let d = f.(LocationReplace <: response) |
        let d2 = nbc.currentDoc |
        --let w = f.bc.window |

        u in valid_absolute_url and

        nbc.win in Iframe and

        some c.to.xframeOptions[d] and 
        ((c.to.xframeOptions[d].option = Deny) or (c.to.xframeOptions[d].option = SameOrigin and rbc.origin != c.to.origin )) and



        navigateAbsoluteUrlDeny[ nbc, d, d2, u, c.to] and 
        d = c.to.resources[u.path <: DirectoryPath] and 
        c.to in Server and 
        c.to in Dns.map[u.authority.domain] ---and 
        --no c.returns --and 
        --unchanged[nbc, sessionHistory] and
        --unchanged[w, accesses]

}

pred location_replaceAbsUrlNoDeny [f : Function, c : Call] {
    let nbc = f.bc | let u = f.(LocationReplace <: url) | 
        --let rbc = f.bc.~nestedBcs |
        let d = f.(LocationReplace <: response) |
        let d2 = nbc.currentDoc |
        --let w = f.bc.window |

        --(some d2 implies d = d2) and

        (some d2 implies d = d2) and

        --addToSessionHistory[nbc, sh, u] and
        some d and
        --no c.from and 
        nbc.accesses' = none and
        nbc.opening' = none and

        resetIframe[d2] and

        u in valid_absolute_url and

        nbc.win in Iframe and

        no c.to.xframeOptions[d] and


        navigateAbsoluteUrl[ nbc, d, d2, u, c.to] and 
        d = c.to.resources[u.path <: DirectoryPath] and 
        c.to in Server and 
        c.to in Dns.map[u.authority.domain] --and 
        --no c.returns --and 
        --unchanged[nbc, sessionHistory] and
        --unchanged[w, accesses]

}

pred location_replace [f : Function, c : Call] {


    let nbc = f.bc | let d = f.(LocationReplace <: response) |
        let u = f.(LocationReplace <: url ) | 
        --let w = nbc.window |
        let d2 = nbc.currentDoc |


        --nbc.currentDoc' = d and
        --w.doc' = d and
        nbc.accesses' = none and
        nbc.opening' = none and

        (some d2 implies d = d2) and

        --d !in (BrowsingContext.currentDoc - d2) and

        resetIframe[d2] and

        -- TODO what is the below doing actually?
        ((nbc.win in Iframe and u in valid_absolute_url) implies no c.to.xframeOptions[d]) and

        --(d2 != d implies (

        --    d2.elements' = none

        --)) and

        (
            (navigateAbsoluteUrl[ nbc, d, d2, u, c.to] and nbc.win in TopLWindow and d = c.to.resources[f.(LocationReplace <: url).path <: DirectoryPath] and c.to in Server and c.to in Dns.map[f.(LocationReplace <: url).authority.domain] ) or 
            --navigateDataHtmlUrl[ c, nbc, w, d, f.(LocationReplace <: url )] or 
            --navigateDataScriptUrl[ c, nbc, w, d, f.(LocationReplace <: url )] or 
            (navigateBlobBlobsHtmlUrl[ nbc,  d, d2, u, nbc] and c.to in Browser ) or 
            (navigateBlobBlobsScriptUrl[ nbc, d, d2, u, nbc] and c.to in Browser ) or 
            --navigateBlobNoBlobsUrl[ c, nbc, w, d, f.(LocationReplace <: url )] or 
            (navigateAboutUrl[ nbc, d, d2, u] and c.to in Browser ) or 
            (navigateErrorUrl[ nbc,  d, d2, u, (valid_absolute_url + valid_data_url + valid_about_url + valid_blob_url)] and c.to in Browser )
        ) and 
        unchanged[nbc, sessionHistory]

}


pred locationReplaceBlobNoChange [f : Function, c : Call] {
    --always (
        --all f : LocationReplace |
        f.bc in Browser.bcs and
        f.(LocationReplace <: url) !in (valid_absolute_url + valid_about_url + valid_data_url) and
        f.(LocationReplace <: url) in valid_blob_url  and
        f.(LocationReplace <: url) !in Browser.blobs[f.bc] and 
        no_change
    --)
}

pred locationReplaceBlobSchemeNoChange [f : Function, c : Call] {
    --always (
        --all f : LocationReplace |
        f.bc in Browser.bcs and
        f.(LocationReplace <: url) !in (valid_absolute_url + valid_blob_url + valid_about_url + valid_data_url) and
        f.(LocationReplace <: url).scheme in Blob and
        f.(LocationReplace <: url) !in Browser.blobs[f.bc] and 
        no_change
   -- )
}



pred locationReplaceDataNoChange [f : Function, c : Call] {
    --always (
        --all f : LocationReplace |
        f.bc in Browser.bcs and
        f.(LocationReplace <: url) !in (valid_absolute_url + valid_about_url + valid_blob_url) and
        f.(LocationReplace <: url) in valid_data_url and 
        no_change
    --)
}

pred create_blob [f : Function, c : Call] {


    let nbc = f.bc | let u = f.(CreateBlob <: url) |
        let d = f.creatorDoc |

        nbc.currentDoc = d and
        u in valid_blob_url and
        valid_blob_path_pred[u.path ] and
        no u.auth_precede and
        some u.path and
        u !in BrowsingContext.currentDoc.src and

        u.path.creator_origin = nbc.origin and 
        Browser.blobs' = Browser.blobs + nbc -> u and 
        unchangedCreateBlob

  
}


