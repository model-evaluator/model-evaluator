module secureContext

--open concreteUrl
open browser
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
	u in HttpsUrl
	--nbc.^~nestedBcs.isSecureContext' = True
	navHttpsSecureContext[nbc] or navHttpsInSecureContext[nbc]
}

pred navAboutSecureContext [nbc : BrowsingContext, u : Url, valid : set Url] {
	u in valid 
	navHttpsSecureContext[nbc] or navHttpsInSecureContext[nbc]
}

pred navInSecureContext [nbc : BrowsingContext, u : Url] {
	u in (HttpUrl + DataUrl /*+ valid_about_url /*+ valid_blob_url*/)
	nbc.isSecureContext' = False
}

pred navErrInSecureContext [nbc : BrowsingContext, u : Url] {
	u in ErrorUrl
	nbc.isSecureContext' = False
}

pred navBlobSecureContext [nbc : BrowsingContext, u : BlobUrl] {
	u.creator_origin in TupleOrigin
	u.creator_origin.scheme in Https 
	nbc.isSecureContext' = True
}

pred navBlobInSecureContext [nbc : BrowsingContext, u : BlobUrl] {
	u.creator_origin in TupleOrigin
	u.creator_origin.scheme !in Https 
	nbc.isSecureContext' = False
}

pred navBlobNullOriginInSecureContext [nbc : BrowsingContext, u : BlobUrl] {
	--u.path.creator_origin !in TupleOrigin
	origin[u] !in TupleOrigin
	nbc.isSecureContext' = False
}

pred navBlobContext [nbc : BrowsingContext, u : BlobUrl] {
	--u in BlobUrl
	(navBlobSecureContext[nbc, u] or navBlobInSecureContext[nbc, u] or navBlobNullOriginInSecureContext[nbc, u] )
}

pred popupAbsSecureContext [nbc : BrowsingContext, u : HttpsUrl] {
	--u in HttpsUrl
	nbc.isSecureContext' = True
}




fun decideSecureContext [nbc : BrowsingContext, u : Url] : Boolean {
	{b : Boolean |

		(	(u in (AboutUrl + DataUrl + BlobUrl ) and nbc.isSandboxed' = True) 
			or 
			(u in HttpsUrl )
			or 
			(u in BlobUrl and (nbc.isSandboxed' = False or nbc.isSandboxed' = none) and some u.creator_origin and u.creator_origin in TupleOrigin and u.creator_origin.scheme in Https )
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
				(nbc.isSecureContext = True and (nbc.^~nestedBcs'.isSecureContext = none or nbc.^~nestedBcs'.isSecureContext = True)) implies (
					b = True
				)else (
					b = False
				)
			
		)

	}
}


