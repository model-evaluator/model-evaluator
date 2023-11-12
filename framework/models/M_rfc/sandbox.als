module sandbox

open browser


pred sandboxedIframeOrigin [nbc : BrowsingContext] {
    nbc.isSandboxed' = True
    nbc.origin' = OpaqueOrigin
}

pred regularIframeOrigin [nbc : BrowsingContext, u : Url] {
    nbc.isSandboxed' = False
    let u1 = origin[u] |
    	nbc.origin' = u1
    
}

pred regularAboutIframeOrigin [rbc : BrowsingContext, nbc : BrowsingContext ] {
    nbc.isSandboxed' = False
    nbc.origin' = rbc.origin
}

pred regularErrorIframeOrigin [nbc : BrowsingContext ] {
    nbc.isSandboxed' = False
    nbc.origin' = OpaqueOrigin
}


pred nestedSandboxRegularOrigin [rbc : BrowsingContext, nbc : BrowsingContext, u : Url] {

	u in ErrorUrl implies (sandboxedIframeOrigin[nbc] or regularErrorIframeOrigin[nbc])
	else (
		u in AboutUrl implies (
			sandboxedIframeOrigin[nbc] or regularAboutIframeOrigin[rbc, nbc]
		)else (
			sandboxedIframeOrigin[nbc] or regularIframeOrigin[nbc, u]
		)
	)

}