module appendHistory

open browser

pred addToSessionHistoryInit [nbc : BrowsingContext, sh : History] {
    no nbc.sessionHistory
    history_append_init[nbc.sessionHistory, nbc.sessionHistory', sh]
}

pred addToSessionHistoryNext [nbc: BrowsingContext, sh : History] {
    some nbc.sessionHistory
    history_append[nbc.sessionHistory, nbc.sessionHistory', sh]
}

pred addToSessionHistory [nbc : BrowsingContext, sh : History, u : Url] {

        sh.url = u and 
        (addToSessionHistoryInit[nbc, sh] or addToSessionHistoryNext[nbc, sh])

}