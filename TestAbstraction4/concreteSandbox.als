module concreteSandbox

--open concreteUrl
open concreteBrowser
--open concreteCallFunction


pred sandboxedIframeOrigin [nbc : BrowsingContext] {
    nbc.isSandboxed' = True
    nbc.origin' = OpaqueOrigin
}

--SAFARI here
pred regularIframeOrigin [nbc : BrowsingContext, u : Url] {
    nbc.isSandboxed' = False
    let u1 = origin[u] |
    	u1 = BlankOrigin implies (
    		nbc.origin' = OpaqueOrigin
    	)else (
    		nbc.origin' = u1
    	)
    
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

	u !in (valid_absolute_url + valid_data_url + valid_blob_url + valid_about_url) implies (sandboxedIframeOrigin[nbc] or regularErrorIframeOrigin[nbc])
	else (
		u in valid_about_url implies (
			sandboxedIframeOrigin[nbc] or regularAboutIframeOrigin[rbc, nbc]
		)else (
			sandboxedIframeOrigin[nbc] or regularIframeOrigin[nbc, u]
		)
	)

}