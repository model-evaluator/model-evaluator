module url 

enum Boolean {True, False}

abstract sig Directive {}
one sig SameOrigin extends Directive {}
one sig CrossOrigin extends Directive {}
one sig SameOriginAllowPopups extends Directive {}
one sig UnsafeNone extends Directive {}
one sig RequireCorp extends Directive {}

one sig SharedArrayBuffer{}

abstract sig Policy {}

sig COOP extends Policy {
	directive : SameOrigin + SameOriginAllowPopups + UnsafeNone
}
sig COEP extends Policy {
	directive : RequireCorp
}
sig CORP extends Policy {
	directive : SameOrigin + CrossOrigin
}
sig CORS extends Policy {
	allowedOrigins : set Origin
}


one sig Dns { 
    map: Domain -> one Server 
}

fact {
    always (all s : Server | one s[map] and s[map][Dns] = s.origin.domain)
}

sig Server {
	origin : Origin,
	resources : Path -> lone (HtmlRaw + (HtmlResource - Document)),
	policies : resources -> set Policy
}

fact {
	always (all s : Server | s.policies[Path][HtmlResource-Document] in (CORS + CORP))
	always (all s : Server | s.policies[Path][HtmlRaw] in (COOP + COEP))
	always (all disj s1, s2 : Server | all x : s1.resources.(HtmlRaw + (HtmlResource - Document)) | x !in s2.resources.(HtmlRaw + (HtmlResource - Document)))
	always (all x : (HtmlRaw + (HtmlResource - Document)) | x in Server.resources[Path] implies one Server.resources.x)

	always (all p : Path | all x : HtmlRaw | 

		#(Server.policies[p][x] & COOP) < 2 and 
		#(Server.policies[p][x] & COEP) < 2
	)

	always (all p : Path | all x : HtmlResource - Document | 

		#(Server.policies[p][x] & CORP) < 2 and 
		#(Server.policies[p][x] & CORS) < 2
	)

	always (all d : Document |
		#(d.policies & COOP) < 2 and
		#(d.policies & COEP) < 2
	)

	always (all disj d1, d2 : Document | all x : d1.elements | x !in (d2.elements + d2.blocked))

	always (all disj d1, d2 : Document | d1.sharedbuffer = d2.sharedbuffer implies d1.src.origin = d2.src.origin)


}


fact {
	all disj s1, s2 : Server | s1.origin != s2.origin
}


sig Path, Domain {}

sig Origin {
    domain : Domain
}

sig Url {
    origin : Origin,
    path : Path
}

sig HtmlRaw {
	src : Url,
	var elements : set Url
}

fact {
	all h : HtmlRaw | all u : h.elements | one s : Server |
		u.origin = s.origin and 
		s.resources[u.path] in (Script + NonActive) 
}

abstract sig HtmlResource {}

sig Document extends HtmlResource {
	src : Url,
	var blocked : set (Script + NonActive),
	var elements : set (Script + NonActive),
	var policies : set (COOP + COEP),
	var sharedbuffer : lone SharedArrayBuffer
}

sig Script extends HtmlResource {
	src : Url,
	var context : lone Document,
	var sabAccess : set SharedArrayBuffer
	--var policies : set (CORP + CORS)
}

sig NonActive extends HtmlResource {
	src : Url,
	var context : lone Document,
	--var policies : set (CORP + CORS)
}

