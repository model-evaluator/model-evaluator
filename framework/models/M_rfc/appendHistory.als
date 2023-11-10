module appendHistory

open browser

pred addToSessionHistoryFirst [nbc : BrowsingContext, sh : History] {
    no nbc.sessionHistory
    history_append_first[nbc.sessionHistory, nbc.sessionHistory', sh]
}

pred addToSessionHistoryMore [nbc: BrowsingContext, sh : History] {
    some nbc.sessionHistory
    history_append[nbc.sessionHistory, nbc.sessionHistory', sh]
}

pred addToSessionHistory [nbc : BrowsingContext, sh : History, u : Url] {

        sh.url = u and 
        (addToSessionHistoryFirst[nbc, sh] or addToSessionHistoryMore[nbc, sh])

}