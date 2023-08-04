module concreteBrowser

open concreteUrl
open orderings[Url] --as history--[History] as history

--open concreteHttp

--open util/ordering[History] as history

one abstract sig Browser extends Client {
    var bcs : set BrowsingContext,
    --var bcgs : set BrowsingContextGroup,
    --var cookies : set Cookie,
    var blobs : set BrowsingContext -> Url,
    --version : one BrowserVersion
}{
    blobs[BrowsingContext] in valid_blob_url
}

/*
abstract sig Window {}
one sig TopLWindow extends Window{}
one sig Iframe extends Window{}*/

enum Window {TopLWindow, Iframe}

sig BrowsingContext {

  var origin : one Origin,
  var currentDoc : lone Document,
  var nestedBcs : set BrowsingContext,
  var sessionHistory : set History,
  var isSecureContext : lone Boolean,
  var isSandboxed : lone Boolean,
  var sandboxWaitingNavigate : lone Boolean,
  var opening : set BrowsingContext,
  var accesses : set Media,
  win : one Window

}{

}

fact {
    always(all b : BrowsingContext | b in Browser.bcs implies b.win in TopLWindow)

    always (all b : BrowsingContext | b !in b.nestedBcs)
    always (all b : BrowsingContext | b in Browser.bcs implies b !in BrowsingContext.nestedBcs)
    --always (all b1, b2 : BrowsingContext | (some b1.currentDoc and b1.currentDoc = b2.currentDoc) implies b1=b2 )
    always (all b1, b2 : BrowsingContext | b1 in b2.nestedBcs implies b2 !in b1.^nestedBcs )
    always (all b : BrowsingContext | lone b.~nestedBcs )
    always (all b : BrowsingContext | no b.currentDoc implies no b.isSecureContext )
    always (all b : BrowsingContext | some b.currentDoc implies some b.isSecureContext )
    always (all disj b1, b2 : BrowsingContext | (some b1.currentDoc and some b2.currentDoc) implies b1.currentDoc != b2.currentDoc )
    --always (all b1, b2 : BrowsingContext | b1.win = b2.win <=> b1 = b2  )
}

fact {

    always (all b : BrowsingContext | all sh : b.sessionHistory | sh.^prev in b.sessionHistory and sh.^next in b.sessionHistory)
    always (all disj b, b1 : BrowsingContext | all sh : b.sessionHistory | sh !in b1.sessionHistory)
}




fact {
    --all w : Window | w in w.bc.windows
    --all b : BrowsingContext | some b.windows => (one TopLWindow & b.windows )--at most one top level window has to be in
    --all d : Document | d !in HtmlDocument implies no d.elements
    --all hd : HtmlDocument | hd.src in AbsoluteURL
}
run {
   -- some b:  BrowsingContext | #b.windows = 3
   --some d : Document | one i : Iframe | i in d.elements
  -- some b : BrowsingContext | #b.sessionHistory.^prev = 3
} for 4
