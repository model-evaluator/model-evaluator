

module scmexec

open scmCallFunction
open urlmanipulation
open securecontextmanipulation
open contentmanipulation

fact {
  --always (some Call implies some Function)
    always (no Call implies no Function)
}


fact {

    always (all c : Call | scmExec[c.event, c])
}


pred scmExec [f : Function, c : Call] {
    f in WindowOpen implies (window_open[f, c] )
    f in Popup implies ((popup[f, c] /*or popupTupleDifferentOriginBlobNoChange[f, c] or popupNonTupleDifferentBcBlobNoChange[f, c]*/) )
    f in Navigate implies ( 
      let u = f.(Navigate <: url) |
      let d = f.(Navigate <: response) |
      (navigateAbsUrlDeny[f, c, u, d] or 
      navigateAbsUrlNoDeny[f, c, u, d, False] or 
      navigate[f, c, u, d, False])   
    ) --c.args TODO
    --f in ReadDom implies (/*c.from in Script and c.to in Browser and */ read_dom[f, c] and no c.args)
    --f in WriteDom implies (/*c.from in Script and c.to in Browser and*/ write_dom[f, c] )
    f in HistoryPushState implies (/*c.from in Script and c.to in Browser and*/ history_push_state[f, c]  )
    --f in LocationReplace implies ((location_replaceAbsUrlDeny[f, c] or location_replaceAbsUrlNoDeny[f, c] or location_replace[f, c] or locationReplaceBlobNoChange[f, c] or locationReplaceBlobSchemeNoChange[f, c] or locationReplaceDataNoChange[f, c] )  )
    f in CreateBlob implies (create_blob[f, c] )
    f in ReadDom implies (read_dom[f, c] )
    f in WriteDom implies (write_dom[f, c] )
    f in InjectScript implies (inject_script[f, c] )
    f in LocationReplace implies (
      let u = f.(LocationReplace <: url) |
      let d = f.(LocationReplace <: response) |
      (navigateAbsUrlDeny[f, c, u, d ] or 
      navigateAbsUrlNoDeny[f, c, u, d, True] or 
      navigate[f, c, u, d, True]) 
    )
    f in CreateIframe implies ((create_iframe[f, c] /*or createIframeTupleDifferentOriginBlobNoChange[f, c] or createIframeNoBlobNoChange[f, c] or createIframeInvalidBlobUrlNoChange[f, c]*/ ) )
    f in AddSandbox implies (add_sandbox[f, c] )
    f in DocumentWrite implies ((document_write_iframeDocument[f, c] /*or document_write_iframeScript[f, c]*/) )
    f in Access2Media implies (access_to_media[f, c]  )
    f in Skip implies no_change
}




