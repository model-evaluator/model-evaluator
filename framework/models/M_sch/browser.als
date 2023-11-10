module browser


open url


one sig Browser {

	var bcgs : set BrowsingContextGroup
}

sig BrowsingContextGroup {
	var bcs : set BrowsingContext
}

sig BrowsingContext {
	var html : lone HtmlRaw,
	var document : lone Document,
	var origin : lone Origin,
	var rendered : one Boolean,
	var opening : set BrowsingContext
}


fact {

	always (all disj bcg1, bcg2 : BrowsingContextGroup | all x : bcg1.bcs | x !in bcg2.bcs )

	always (all disj bc1, bc2 : BrowsingContext | all d : bc1.document | d != bc2.document)
}
