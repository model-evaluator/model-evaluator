module concreteSecureContext

--open concreteUrl
open concreteBrowser
--open concreteCallFunction

pred allSecureContext [ nbcs : set BrowsingContext] {
	all nbc : nbcs | nbc.isSecureContext' = True
}

pred navHttpsSecureContext [nbc : BrowsingContext] {
	allSecureContext[nbc.^~nestedBcs']
	nbc.isSecureContext' = True
}

pred navHttpsInSecureContext [nbc : BrowsingContext] {
	!allSecureContext[nbc.^~nestedBcs']
	nbc.isSecureContext' = False
}


pred navAbsSecureContext [nbc : BrowsingContext, u : Url] {
	u in valid_https_url
	--nbc.^~nestedBcs.isSecureContext' = True
	navHttpsSecureContext[nbc] or navHttpsInSecureContext[nbc]
}

pred navAboutSecureContext [nbc : BrowsingContext, u : Url, valid : set Url] {
	u in valid 
	navHttpsSecureContext[nbc] or navHttpsInSecureContext[nbc]
}

pred navInSecureContext [nbc : BrowsingContext, u : Url] {
	u in (valid_http_url + valid_data_url /*+ valid_about_url /*+ valid_blob_url*/)
	nbc.isSecureContext' = False
}

pred navErrInSecureContext [nbc : BrowsingContext, u : Url] {
	u !in (valid_absolute_url + valid_data_url + valid_about_url + valid_blob_url)
	nbc.isSecureContext' = False
}

pred navBlobSecureContext [nbc : BrowsingContext, u : Url] {
	u.path.creator_origin in TupleOrigin
	u.path.creator_origin.scheme in Https 
	nbc.isSecureContext' = True
}

pred navBlobInSecureContext [nbc : BrowsingContext, u : Url] {
	u.path.creator_origin in TupleOrigin
	u.path.creator_origin.scheme !in Https 
	nbc.isSecureContext' = False
}

pred navBlobNullOriginInSecureContext [nbc : BrowsingContext, u : Url] {
	--u.path.creator_origin !in TupleOrigin
	origin[u] !in TupleOrigin
	nbc.isSecureContext' = False
}

pred navBlobContext [nbc : BrowsingContext, u : Url] {
	u in valid_blob_url
	(navBlobSecureContext[nbc, u] or navBlobInSecureContext[nbc, u] or navBlobNullOriginInSecureContext[nbc, u] )
}

pred popupAbsSecureContext [nbc : BrowsingContext, u : Url] {
	u in valid_https_url
	nbc.isSecureContext' = True
}




fun decideSecureContext [nbc : BrowsingContext, u : Url] : Boolean {
	{b : Boolean |

		(	(u in (valid_about_url + valid_data_url + valid_blob_url ) and nbc.isSandboxed' = True) 
			or 
			(u in valid_absolute_url and u.scheme in Https)
			or 
			(u in valid_blob_url and (nbc.isSandboxed' = False or nbc.isSandboxed' = none) and some u.path.creator_origin and u.path.creator_origin in TupleOrigin and u.path.creator_origin.scheme in Https )
		) implies (
				
				b = True
	
		)else (
			b = False
		)
			

	}
}


fun decideUltimateSecureContext [nbc : BrowsingContext] : Boolean {
	{b : Boolean |

		(nbc.isSecureContext = False or nbc.isSecureContext = none ) implies (
			b = False
		)else (
			BrowserVersion.version = Safari implies (
				(nbc.isSecureContext = True and (nbc.^~nestedBcs'.isSecureContext = none or nbc.^~nestedBcs'.isSecureContext = True)) implies (
					b = True
				)else (
					b = False
				)
			)else (
				(nbc.isSecureContext = True and nbc.^~nestedBcs'.isSecureContext = True and nbc.~opening'.isSecureContext = True ) implies (
					b = True
				)else (
					b = False
				)
			)
			
		)

	}
}

fun decideUltimateSecureContext2 [nbc : BrowsingContext] : Boolean {
	{b : Boolean |

		(nbc.isSecureContext = False or nbc.isSecureContext = none ) implies (
			b = False
		)else (
			BrowserVersion.version = Safari implies (
				(nbc.isSecureContext = True and (nbc.^~nestedBcs'.isSecureContext = none or nbc.^~nestedBcs'.isSecureContext = True)) implies (
					b = True
				)else (
					b = False
				)
			)else (
				(nbc.isSecureContext = True and nbc.^~nestedBcs'.isSecureContext = True and decideUltimateSecureContext[nbc.~opening'] = True ) implies (
					b = True
				)else (
					b = False
				)
			)
			
		)

	}
}
