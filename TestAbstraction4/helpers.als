--open concreteHttp
--open concreteBrowser

/*pred top_level_context[bc : BrowsingContext] {

	bc.window in TopLWindow

}*/


let unchanged[s,r] = all x : s | x.(r)'=x.(r)