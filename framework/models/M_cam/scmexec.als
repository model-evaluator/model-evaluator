

module scmexec

open scmCallFunction
open urlmanipulation
open securecontextmanipulation

fact {
    always (no Call implies no Function)
}


fact {

    always (all c : Call | scmExec[c.event, c])
}


pred scmExec [f : Function, c : Call] {
    f in WindowOpen implies (window_open[f, c] )
    f in Popup implies (popup[f, c] )
    f in Navigate implies ( 
      let u = f.(Navigate <: url) |
      let d = f.(Navigate <: response) |
      (navigateAbsUrlDeny[f, c, u, d] or 
      navigateAbsUrlNoDeny[f, c, u, d, f.lr] or 
      navigate[f, c, u, d, f.lr])   
    ) 
    f in HistoryPushState implies ( history_push_state[f, c]  )
    f in CreateBlob implies (create_blob[f, c] )
    f in CreateIframe implies (create_iframe[f, c] )
    f in AddSandbox implies (add_sandbox[f, c] )
    f in DocumentWrite implies (document_write_iframeDocument[f, c] )
    f in Access2Media implies (access_to_media[f, c]  )
    f in Skip implies no_change
}




