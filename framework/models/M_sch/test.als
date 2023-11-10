module test

open event
open call
open browser
open url

fact init {
	#Browser.bcgs = 0
	#BrowsingContextGroup.bcs = 0
	BrowsingContext.html = none
	BrowsingContext.document = none
	BrowsingContext.rendered = False
	BrowsingContext.opening = none
	Document.sharedbuffer = none
	Script.sabAccess = none
}


run {
	eventually {
		some Script.sabAccess
	}
} for 4


run {
	eventually{
		some Browser.bcgs
	
	}
} for 6


run {
	eventually{
		--some bc : BrowsingContext |  #bc.document.elements = 2 and #Server.policies[Path][HtmlRaw + (HtmlResource - Document)] = 6
		some bc : BrowsingContext |  #bc.document.elements = 1 and #bc.document.blocked = 1
	
	}
} for 6 but 1 BrowsingContextGroup, 1 BrowsingContext


run {
	eventually{
		--some bc : BrowsingContext |  #bc.document.elements = 2 and #Server.policies[Path][HtmlRaw + (HtmlResource - Document)] = 6
		some disj bc1, bc2 : BrowsingContext | some bcg : BrowsingContextGroup |  bc1 + bc2 in bcg.bcs
	
	}
} for 6 but 1 BrowsingContextGroup, 3 BrowsingContext



assert coopPolicy {
	always {
		no nbc : BrowsingContext | some bcg : nbc.~bcs | some nbc2 : BrowsingContext |

			nbc != nbc2 and

			nbc2 in nbc.opening and

			CrossOriginIsolatedState[nbc] and 

			nbc2.origin != nbc.origin and 

			nbc2 in bcg.bcs
	}
}
check coopPolicy for 4 but 1 BrowsingContextGroup, 1 BrowsingContext, 3 Server


assert coepPolicy {
	always {
		no nbc : BrowsingContext | some bcg : nbc.~bcs | some el : Script | some s : Server |
		let elPolCORP = s.policies[el.src.path][el] & CORP |
		let elPolCORS = s.policies[el.src.path][el] & CORS |

			el in s.resources[el.src.path] and
			bcg in Browser.bcgs and 

			CrossOriginIsolatedState[nbc] and 

			el in nbc.document.elements and 

			nbc.origin != el.src.origin and 


			!((some elPolCORP and elPolCORP.directive = CrossOrigin and no elPolCORS ) or 
				(some elPolCORP and elPolCORP.directive = CrossOrigin and some elPolCORS and nbc.origin in elPolCORS.allowedOrigins ) or 
				(no elPolCORP and some elPolCORS and nbc.origin in elPolCORS.allowedOrigins))


	}
}
check coepPolicy for 4 but 1 BrowsingContextGroup, 1 BrowsingContext, 3 Server

assert sharedBufferAccess {
	always {
		no script : Script | some buffer : SharedArrayBuffer |
		let crossOriginDoc = buffer.~sharedbuffer |
		let scriptDoc = script.context |
			legitScript[script] and
			buffer in script.sabAccess and 
			crossOriginDoc.src.origin != scriptDoc.src.origin 
	}
}
check sharedBufferAccess for 4 but 2 BrowsingContextGroup, 3 BrowsingContext, 3 Server
