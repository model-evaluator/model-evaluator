module browser

open url
open history[Url] 


one abstract sig Browser extends Client {
    var bcs : set BrowsingContext,
    var blobs : set BrowsingContext -> BlobUrl
}



sig BrowsingContext {

  var origin : one Origin,
  var currentDoc : lone Document,
  var nestedBcs : set BrowsingContext,
  var sessionHistory : set History,
  var isSecureContext : lone Boolean,
  var isSandboxed : lone Boolean,
  var opening : set BrowsingContext,
  var accesses : set (Media + HtmlResource),
  win : one Window

}{

}

fact {
    always(all b : BrowsingContext | b in Browser.bcs implies b.win in TopLWindow)

    always (all b : BrowsingContext | b !in b.nestedBcs)
    always (all b : BrowsingContext | b in Browser.bcs implies b !in BrowsingContext.nestedBcs)

    always (all b1, b2 : BrowsingContext | b1 in b2.nestedBcs implies b2 !in b1.^nestedBcs )
    always (all b : BrowsingContext | lone b.~nestedBcs )

    always (all b : BrowsingContext | some b.currentDoc implies some b.isSecureContext )
    always (all disj b1, b2 : BrowsingContext | (some b1.currentDoc and some b2.currentDoc) implies b1.currentDoc != b2.currentDoc )

    always (all b : BrowsingContext | some b.~nestedBcs implies (some b.currentDoc and b.currentDoc in b.~nestedBcs.currentDoc.elements) )

    always (all b : BrowsingContext | all sh : b.sessionHistory | sh.^prev in b.sessionHistory and sh.^next in b.sessionHistory)
    always (all disj b, b1 : BrowsingContext | all sh : b.sessionHistory | sh !in b1.sessionHistory)
}





