module call

open browser
open url

var one abstract sig Call {
	var bcg : BrowsingContextGroup,
	var bc : BrowsingContext,
	var event : Function,
	var to : lone Server
}

fact {
	always (all c : Call | c.event != WindowOpen implies (c.bcg in Browser.bcgs and c.bc in c.bcg.bcs) )
	--always (all c : Call | c.bc in c.bcg.bcs )
}


var lone abstract sig Function {}

var lone sig WindowOpen extends Function {}

var lone sig Navigate extends Function {
	var url : Url,
	var html : HtmlRaw
}

var lone sig ResourceRequest extends Function {
	var url : Url,
	var body : Script + NonActive
}

var lone sig Popup extends Function {
	var url : Url,
	var html : HtmlRaw,
	var newBc : BrowsingContext,
	var newBcGr : lone BrowsingContextGroup
}


var lone sig SharedArrayBufferAccess extends Function {
	var script : Script,
	var buffer : SharedArrayBuffer 
}

var lone sig Skip extends Function {}
