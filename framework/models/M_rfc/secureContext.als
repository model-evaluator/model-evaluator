module secureContext

open browser


fun decideSecureContext [nbc : BrowsingContext, u : Url] : Boolean {
	{b : Boolean |
		let rbcs = nbc.^~nestedBcs' |
		let openers = nbc.^~opening' |

		(u in secure_urls and 
			(rbcs.isSecureContext = none or rbcs.isSecureContext = True) and 
				(openers.isSecureContext = none or openers.isSecureContext = True)) implies (
				b = True
		)else (
				b = False
		)

	}
}

run {
	some nbc : BrowsingContext | some u : Url |
		decideSecureContext[nbc, u] = True and #nbc.^~nestedBcs = 2
} for 4


