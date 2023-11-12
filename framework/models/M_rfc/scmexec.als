

module scmexec

open scmCallFunction
open urlmanipulation
open securecontextmanipulation
open contentmanipulation

fact {

    always (no Call implies no Function)
}


fact {

    always (all c : Call | scmExec[c.event, c])
}


pred scmExec [f : Function, c : Call] {
    f in WindowOpen implies (window_open[f, c] )
    f in Popup implies (popup[f, c]  )
    f in Navigate implies ( 
      let u = f.(Navigate <: url) |
      let d = f.(Navigate <: response) |
      (navigateAbsUrlDeny[f, c, u, d] or 
      navigateAbsUrlNoDeny[f, c, u, d, False] or 
      navigate[f.bc, c.to, u, d, False])   
    ) 
    f in ReadDom implies ( read_dom[f, c])
    f in WriteDom implies ( write_dom[f, c] )
    f in HistoryPushState implies ( history_push_state[f, c]  )
    
    f in CreateBlob implies (create_blob[f, c] )
    f in InjectScript implies (inject_script[f, c] )
    f in LocationReplace implies (
      let u = f.(LocationReplace <: url) |
      let d = f.(LocationReplace <: response) |
      (navigateAbsUrlDeny[f, c, u, d ] or 
      navigateAbsUrlNoDeny[f, c, u, d, True] or 
      navigate[f.bc, c.to, u, d, True]) 
    )
    f in RenderResource implies (
      render_resource[f, c]
    )
    f in CreateIframe implies (create_iframe[f, c]  )
    f in DocumentWrite implies (document_write[f, c] )
    f in Access2Media implies (access_to_media[f, c]  )
    f in Skip implies no_change
}




