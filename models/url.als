open generics

open util/ordering[Window]

abstract sig Transition {}

one sig TLocationReplace, TNewBlob, TCreateIframeWoSandbox, TSandbox, TDocumentWrite, TPopup extends Transition {}

one sig THistoryPushState_1 extends Transition {
	state1 : some HistoryState
}

one sig THistoryPushState_2 extends Transition {
	state2 : some HistoryState
}

one sig THistoryPushState_3 extends Transition {
	state3 : some HistoryState
}

sig Window {
       location : 			one Location
	 , frames : 		set Frame
         , state : 			lone HistoryState
         , content : 		lone Content
	 , document : 		lone Document 
	 , context : 		one Context
         , transition : 		lone Transition

}
sig Frame {
	location : 			one Location
	, sandbox : 		lone Sandbox
	, ancestor : 		one Window
	, context : 		one Context
	//, srcdoc : 			lone Document
}

fact  {

	all w : Window - last | some w.transition
}



fun secureContext [w: Window] : one Context {
	{ c :  Context | 
		proper_https[w.location.href] => c = SecureContext else c = InSecureContext
	}
}

fun secureContext [f : Frame] : one Context {
	{ c : Context | 
		(f.ancestor.context = SecureContext and f.context = SecureContext) => c = SecureContext
				else c = InSecureContext

	}



}

fun secureContext [loc : Location] : one Context {
	{ c :  Context | 
		loc.origin = OpaqueOrigin => c = SecureContext 
			else (
				proper_https[loc.href] => c= SecureContext else c= InSecureContext
			)
	}
}

fun popupSecureContext [f : Frame, w1 : Window] : one Context {
	{ c : Context |
		(secureContext[f] = SecureContext and secureContext[w1] = SecureContext ) => c = SecureContext else c = InSecureContext
	}
}

//initial state for the first window
pred init [w: Window] {
   proper_data[w.location.href] and w.location.origin = origin[w.location.href]  and w.context = secureContext[w]
	and assignNullExcept[w, {f : Window$.fields | f = Window$location or f = Window$context   }]

}
//all traces must have one of the transitions
fact traces {
      init[first]
      all w : Window - last, w1 : Window |  w1 = w.next implies transitionSwitch[w, w1]
}
//switch for the transitions predicates
pred transitionSwitch [w, w1 : Window] {
	transition[w] = TLocationReplace => locationReplace[w, w1]
	else ( transition[w] in THistoryPushState_1 => ( one st :  transition[w].state1 | historyPushState1[w, w1, st] )
	else ( transition[w] in THistoryPushState_2 => ( one st2 :  transition[w].state2 | historyPushState2[w, w1, st2] )
	else ( transition[w] in THistoryPushState_3 => ( one st3 :  transition[w].state3 | historyPushState3[w, w1, st3] )
	else ( transition[w] = TNewBlob => (some u:URL |  newBlob[w,w1,u])
	else ( transition[w] = TCreateIframeWoSandbox => (some u:URL | newIframeWoSandbox[w,w1,u] )
	else ( transition[w] = TPopup => ( popupDocWrite[w,w1])
	else ( transition[w] = TSandbox => (dynamicSandbox[w,w1])
	else ( transition[w] = TDocumentWrite => ( documentWrite2Frame[w,w1] )
	//else ( transition[w] = create_iframe_with_sandbox => (some u:URL | new_iframe_with_sandbox[w,w1,u] )
	//else ( transition[w] = popup_document_write => (popup_document_write[w,w1] ) 
	//))
	))))))))

}





pred locationReplace [w, w1 : Window] {
	( some w.content) 
	 w1.location = w.content.location and  w1.context = secureContext[w1] and
	assignNullExcept[w1, {f : Window$.fields | f = Window$location   }]
}

pred historyPushState1 [w, w1 : Window, hs : HistoryState ] {
		( origin[hs.url] = w.location.origin and origin[hs.url] != UnknownOrigin and only_scheme_and_delim_url[hs.url]  ) 
		w1.location.href = hs.url and w1.location.origin=w.location.origin and w1.state.url = hs.url and 
		w1.context = secureContext[w1] and
		equalsExcept[w, w1, {f : Window$.fields | f = Window$location or f = Window$state  } ]
}

//run historyPushState1 for 4

pred historyPushState2 [w, w1 : Window, hs : HistoryState ] {
		( origin[hs.url] != w.location.origin and origin[hs.url] = UnknownOrigin and only_path_url[hs.url] and some w.location.href.host )
		w1.location.href.path = hs.url.path and equalsExceptLocation[w.location.href, w1.location.href,  {f : URL$.fields | f = URL$path  } ]
		and w1.location.origin=w.location.origin and w1.state.url=w1.location.href and  
		//w1.context = secureContext[w1] and
		equalsExcept[w, w1, {f : Window$.fields | f = Window$location or f = Window$state  } ]
		
}

pred historyPushState3 [w, w1 : Window, hs : HistoryState ] {
		(  only_path_url[hs.url] and no w.location.href.host )
		w1.location.href.host = hs.url.path and equalsExceptLocation[w.location.href, w1.location.href,  {f :URL$.fields | f = URL$host  } ]
		and w1.location.origin=w.location.origin and w1.state.url=w1.location.href and  
		//w1.context = secureContext[w1] and
		equalsExcept[w, w1, {f : Window$.fields | f = Window$location or f = Window$state   } ]
}

//run historyPushState3 for 4


pred newBlob  [w, w1 : Window, u : URL ] {
		( proper_blob[u] and w.location.href.scheme != Blob ) 
		u.creator_origin= w.location.origin and  w1.content.location.href = u and w1.content.location.origin = origin[u]
		and  w1.context = secureContext[w1]
		and equalsExcept[w, w1, {f : Window$.fields | f = Window$content  } ]
}	


//assign null to every fields except trans+ef
pred assignNullExcept [w : Window, ef : univ] {
	all f : Window$.fields | f in ef or f  = Window$transition or f = Window$context or no w.(f.value)
}
//carry the same state from the previous window, except trans+ef
pred equalsExcept[w, w1 : Window, ef : univ] {
	all f : Window$.fields | f in ef or f  = Window$transition or f = Window$context or w1.(f.value) = w.(f.value) 
}
//carry the same state from the previous URL, except ef 
pred equalsExceptLocation[ u, u1 : URL, ef : univ] {
	all f : URL$.fields | f in ef or u1.(f.value) = u.(f.value) 
}

pred equalsExceptFrame[w, w1 : Frame, ef : univ] {
	all f : Frame$.fields | f in ef or f = Window$context or w1.(f.value) = w.(f.value) 
}



pred IframeAccessControl [ f : Frame, w : Window ] {
	w.location.origin = f.location.origin and no f.sandbox
}


//creates new iframe and doesn't assign sandbox and context. sandbox is assigned via predicate and context is assigned with a general fact
fun newIframeInit [u : URL, w, w1 : Window] : one Frame {
	{ w2 : Frame |
		w2.location.href = u and w2.location.origin = origin[w.location.href]  
				and w2.ancestor = w1 //and  w2.context = secureContext[w2.location]

	}
}
//w2 : iframe has no sandbox
pred newIframeWoSandbox [w, w1 : Window, u : URL] {
	(proper_about[u])
	let w2 = newIframeInit [u, w, w1]  |
		w1.frames = w.frames+w2 and no w2.sandbox and  w1.context = w.context and w2.context = secureContext[w2.location] and
		equalsExcept[w, w1, {f : Window$.fields | f = Window$frames  or f = Window$context  } ]
	
}

//pred new_iframe_with_sandbox [w, w1 : Window, u : URL] {
//	(proper_about[u])
//	let w2 = newIframeInit [u, w1]  |
//		w1.frames = w.frames+w2 and some w2.sandbox and  w1.context = w.context and w2.context = SecureContext and
//		equalsExcept[w, w1, {f : Window$.fields | f = Window$frames  or f = Window$context  } ]
//	
//}


//run newIframeWoSandbox for 2


//applying document_write inside iframe, changes the href and origin
pred documentWrite2Frame [w, w1 : Window] {
	(some w.frames)
	one fr : w.frames | one x : Frame | {
		//((fr.location.origin = OpaqueOrigin and unsandboxed_document[fr] ) or (fr.location.origin = w.location.origin))
		IframeAccessControl[fr, w] => ( x.location.href = w.location.href and x.location.origin = fr.location.origin and x.ancestor = w1 
					and equalsExceptFrame[fr, x, {f : Frame$.fields | f = Frame$location or f = Frame$ancestor } ]
					and x.context = fr.context
					and w1.frames = w.frames - fr + x and w1.context = w.context and
					equalsExcept[w, w1, {f : Window$.fields | f = Window$frames or f = Window$context } ]) 
			else w1 = w
	}
}



pred dynamicSandbox [w, w1 : Window] {
	(some w.frames)
	one fr : w.frames | one x : Frame | {
		(fr.location.origin = BlankOrigin => x.location.origin=OpaqueOrigin else x.location.origin = fr.location.origin)
		and x.location.href = fr.location.href
		and some x.sandbox and x.ancestor = w1
		//and x.context = fr.context //{ {secureContext[x.location] = SecureContext and secureContext[w1.location] = SecureContext} => SecureContext else InSecureContext } 
		//and x.context = { {secureContext[x.location] = SecureContext and w1.context = SecureContext} => SecureContext else InSecureContext } 
		and x.context = secureContext[x.location]
		//and equalsExceptFrame[fr, x, {f :Frame$.fields | f = Frame$sandbox or f = Frame$location or f = Frame$ancestor or f = Frame$context } ]
		and w1.frames = w.frames - fr + x and 
		//w1.context = w.context and
		//w1.context = { {secureContext[x.location] = SecureContext and w.context = SecureContext} => SecureContext else InSecureContext } and
		equalsExcept[w, w1, {f : Window$.fields | f = Window$frames } ]
	}
}



//pred popup_iframe [w, w1 : Window] {
//	(some w.frames  )
//	one fr : w.frames | {
//		w1.location.href = w.location.href and w1.location.origin = fr.location.origin and 
//		w1.context = { { secureContext[fr.location] = SecureContext and secureContext[w.location] = SecureContext} => SecureContext else InSecureContext } and
//		assignNullExcept[w1, {f : Window$.fields | f = Window$location    }]
//
//	}
//}

pred popupDocWrite [w, w1 : Window] {
	(some w.frames)	
	one fr : w.frames | {
		w1.location.href = fr.location.href and w1.location.origin = fr.location.origin and
		w1.context = fr.context and
		assignNullExcept[w1, {f : Window$.fields | f = Window$location or f = Window$context    }]
	}
}


pred currentlyOpenRecognisable [w : Window] {
	let u = w.location.href |
		u.sch_delim = SchSlashDelimiter and some u.host
}

//pred access2API_allowed [u : set URL] {
//	u.host 
//}


//run init for 1
pred access2API {
  improper_blob[last.location.href] and last.location.origin=OpaqueOrigin and last.context = SecureContext and currentlyOpenRecognisable[last]


}
//run access2API for 6 but exactly 3 Frame, 9 Window
assert change2SecureContext {
   all w, w1 : Window {
		( first = w and last = w1 ) => last.context = InSecureContext
   }
}
//check change2SecureContext for 3 //but exactly 3 Frame, 8 Window
//check access2API2 for 5 but exactly 3 Frame, 8 Window

assert change2OpaqueOrigin{
   all w, w1 : Window {
		( first = w and last = w1 ) => last.location.origin=BlankOrigin
   }
}
//check change2OpaqueOrigin for 2

assert APIaccessible{
	!access2API
  // all w, w1 : Window {
//		( first = w and last = w1 ) =>( last.location.origin=BlankOrigin or  last.context = InSecureContext or  proper_blob[last.location.href]  )
//   }
}
check APIaccessible for  6 but exactly 3 Frame, 9 Window
