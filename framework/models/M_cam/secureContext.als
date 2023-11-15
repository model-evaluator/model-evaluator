module secureContext

open browser


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


