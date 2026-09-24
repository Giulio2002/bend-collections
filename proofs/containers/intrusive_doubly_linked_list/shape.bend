import Base
import ./graph.bend as G


# The graph is a proof shadow. These are pointwise map laws, proved here,
# not postconditions assumed of the list operation.

def next_sn(~N: Data, ~R: Data, ~P: Data, ~eq: N -> N -> Bool, +g: G.Graph<N,R,P>, +n: N, +v: Maybe<&2,N>, +x: N) -> {G.next(~N, ~R, ~P, ~eq,G.sn(~N, ~R, ~P,g,n,v),x) == G.choose(~Maybe<&2,N>,eq(n,x),v,G.next(~N, ~R, ~P, ~eq,g,x)) : Maybe<&2,N>}:
  match g:
    case G.Graph{ns,ps,rs,f}: {==}

def prev_sn(~N: Data, ~R: Data, ~P: Data, ~eq: N -> N -> Bool, +g: G.Graph<N,R,P>, +n: N, +v: Maybe<&2,N>, +x: N) -> {G.prev(~N, ~R, ~P, ~eq,G.sn(~N, ~R, ~P,g,n,v),x) == G.prev(~N, ~R, ~P, ~eq,g,x) : Maybe<&2,N>}:
  match g:
    case G.Graph{ns,ps,rs,f}: {==}

def next_sp(~N: Data, ~R: Data, ~P: Data, ~eq: N -> N -> Bool, +g: G.Graph<N,R,P>, +n: N, +v: Maybe<&2,N>, +x: N) -> {G.next(~N, ~R, ~P, ~eq,G.sp(~N, ~R, ~P,g,n,v),x) == G.next(~N, ~R, ~P, ~eq,g,x) : Maybe<&2,N>}:
  match g:
    case G.Graph{ns,ps,rs,f}: {==}

def prev_sp(~N: Data, ~R: Data, ~P: Data, ~eq: N -> N -> Bool, +g: G.Graph<N,R,P>, +n: N, +v: Maybe<&2,N>, +x: N) -> {G.prev(~N, ~R, ~P, ~eq,G.sp(~N, ~R, ~P,g,n,v),x) == G.choose(~Maybe<&2,N>,eq(n,x),v,G.prev(~N, ~R, ~P, ~eq,g,x)) : Maybe<&2,N>}:
  match g:
    case G.Graph{ns,ps,rs,f}: {==}

def next_sh(~N: Data, ~R: Data, ~P: Data, ~eq: N -> N -> Bool, +g: G.Graph<N,R,P>, +r: R, +v: Maybe<&2,N>, +x: N) -> {G.next(~N, ~R, ~P, ~eq,G.sh(~N, ~R, ~P,g,r,v),x) == G.next(~N, ~R, ~P, ~eq,g,x) : Maybe<&2,N>}:
  match g:
    case G.Graph{ns,ps,rs,f}: {==}

def prev_sh(~N: Data, ~R: Data, ~P: Data, ~eq: N -> N -> Bool, +g: G.Graph<N,R,P>, +r: R, +v: Maybe<&2,N>, +x: N) -> {G.prev(~N, ~R, ~P, ~eq,G.sh(~N, ~R, ~P,g,r,v),x) == G.prev(~N, ~R, ~P, ~eq,g,x) : Maybe<&2,N>}:
  match g:
    case G.Graph{ns,ps,rs,f}: {==}

def next_sn_other(~N: Data, ~R: Data, ~P: Data, ~eq: N -> N -> Bool, +g: G.Graph<N,R,P>, +n: N, +v: Maybe<&2,N>, +x: N, neq: {eq(n,x) == False{} : Bool}) -> {G.next(~N, ~R, ~P, ~eq,G.sn(~N, ~R, ~P,g,n,v),x) == G.next(~N, ~R, ~P, ~eq,g,x) : Maybe<&2,N>}:
  %Equal.sym(Maybe<&2,N>,G.next(~N, ~R, ~P, ~eq,G.sn(~N, ~R, ~P,g,n,v),x),G.choose(~Maybe<&2,N>,eq(n,x),v,G.next(~N, ~R, ~P, ~eq,g,x)),next_sn(~N, ~R, ~P, ~eq,g,n,v,x)) : {_ == G.next(~N, ~R, ~P, ~eq,g,x) : Maybe<&2,N>}
  %Equal.sym(Bool,eq(n,x),False{},neq) : {G.choose(~Maybe<&2,N>,_,v,G.next(~N, ~R, ~P, ~eq,g,x)) == G.next(~N, ~R, ~P, ~eq,g,x) : Maybe<&2,N>}
  {==}

def prev_sp_other(~N: Data, ~R: Data, ~P: Data, ~eq: N -> N -> Bool, +g: G.Graph<N,R,P>, +n: N, +v: Maybe<&2,N>, +x: N, neq: {eq(n,x) == False{} : Bool}) -> {G.prev(~N, ~R, ~P, ~eq,G.sp(~N, ~R, ~P,g,n,v),x) == G.prev(~N, ~R, ~P, ~eq,g,x) : Maybe<&2,N>}:
  %Equal.sym(Maybe<&2,N>,G.prev(~N, ~R, ~P, ~eq,G.sp(~N, ~R, ~P,g,n,v),x),G.choose(~Maybe<&2,N>,eq(n,x),v,G.prev(~N, ~R, ~P, ~eq,g,x)),prev_sp(~N, ~R, ~P, ~eq,g,n,v,x)) : {_ == G.prev(~N, ~R, ~P, ~eq,g,x) : Maybe<&2,N>}
  %Equal.sym(Bool,eq(n,x),False{},neq) : {G.choose(~Maybe<&2,N>,_,v,G.prev(~N, ~R, ~P, ~eq,g,x)) == G.prev(~N, ~R, ~P, ~eq,g,x) : Maybe<&2,N>}
  {==}

def next_sn_self(~N: Data, ~R: Data, ~P: Data, ~eq: N -> N -> Bool, +g: G.Graph<N,R,P>, +n: N, +v: Maybe<&2,N>, same: {eq(n,n) == True{} : Bool}) -> {G.next(~N, ~R, ~P, ~eq,G.sn(~N, ~R, ~P,g,n,v),n) == v : Maybe<&2,N>}:
  %Equal.sym(Maybe<&2,N>,G.next(~N, ~R, ~P, ~eq,G.sn(~N, ~R, ~P,g,n,v),n),G.choose(~Maybe<&2,N>,eq(n,n),v,G.next(~N, ~R, ~P, ~eq,g,n)),next_sn(~N, ~R, ~P, ~eq,g,n,v,n)) : {_ == v : Maybe<&2,N>}
  %Equal.sym(Bool,eq(n,n),True{},same) : {G.choose(~Maybe<&2,N>,_,v,G.next(~N, ~R, ~P, ~eq,g,n)) == v : Maybe<&2,N>}
  {==}

def prev_sp_self(~N: Data, ~R: Data, ~P: Data, ~eq: N -> N -> Bool, +g: G.Graph<N,R,P>, +n: N, +v: Maybe<&2,N>, same: {eq(n,n) == True{} : Bool}) -> {G.prev(~N, ~R, ~P, ~eq,G.sp(~N, ~R, ~P,g,n,v),n) == v : Maybe<&2,N>}:
  %Equal.sym(Maybe<&2,N>,G.prev(~N, ~R, ~P, ~eq,G.sp(~N, ~R, ~P,g,n,v),n),G.choose(~Maybe<&2,N>,eq(n,n),v,G.prev(~N, ~R, ~P, ~eq,g,n)),prev_sp(~N, ~R, ~P, ~eq,g,n,v,n)) : {_ == v : Maybe<&2,N>}
  %Equal.sym(Bool,eq(n,n),True{},same) : {G.choose(~Maybe<&2,N>,_,v,G.prev(~N, ~R, ~P, ~eq,g,n)) == v : Maybe<&2,N>}
  {==}

def segment_sn_frame(~N: Data, ~R: Data, ~P: Data, ~eq: N -> N -> Bool, +g: G.Graph<N,R,P>, +n: N, +v: Maybe<&2,N>, +xs: List<&2,N>, +p: Maybe<&2,N>, +q: Maybe<&2,N>, away: G.away(~N,~eq,n,xs), good: G.segment(~N, ~R, ~P, ~eq,g,p,xs,q)) -> G.segment(~N, ~R, ~P, ~eq,G.sn(~N, ~R, ~P,g,n,v),p,xs,q):
  match xs away good:
    case Nil{} _ _: Unit{}
    case Con{+x,+rest} Tuple{Tuple{neq,rev},ar} Tuple{hp,Tuple{hn,ht}}:
      (Equal.trans(Maybe<&2,N>,G.prev(~N, ~R, ~P, ~eq,G.sn(~N, ~R, ~P,g,n,v),x),G.prev(~N, ~R, ~P, ~eq,g,x),p,prev_sn(~N, ~R, ~P, ~eq,g,n,v,x),hp),
       (Equal.trans(Maybe<&2,N>,G.next(~N, ~R, ~P, ~eq,G.sn(~N, ~R, ~P,g,n,v),x),G.next(~N, ~R, ~P, ~eq,g,x),G.first(~N,rest,q),next_sn_other(~N, ~R, ~P, ~eq,g,n,v,x,neq),hn),
        segment_sn_frame(~N, ~R, ~P, ~eq,g,n,v,rest,Some{x},q,ar,ht)))

def segment_sp_frame(~N: Data, ~R: Data, ~P: Data, ~eq: N -> N -> Bool, +g: G.Graph<N,R,P>, +n: N, +v: Maybe<&2,N>, +xs: List<&2,N>, +p: Maybe<&2,N>, +q: Maybe<&2,N>, away: G.away(~N,~eq,n,xs), good: G.segment(~N, ~R, ~P, ~eq,g,p,xs,q)) -> G.segment(~N, ~R, ~P, ~eq,G.sp(~N, ~R, ~P,g,n,v),p,xs,q):
  match xs away good:
    case Nil{} _ _: Unit{}
    case Con{+x,+rest} Tuple{Tuple{neq,rev},ar} Tuple{hp,Tuple{hn,ht}}:
      (Equal.trans(Maybe<&2,N>,G.prev(~N, ~R, ~P, ~eq,G.sp(~N, ~R, ~P,g,n,v),x),G.prev(~N, ~R, ~P, ~eq,g,x),p,prev_sp_other(~N, ~R, ~P, ~eq,g,n,v,x,neq),hp),
       (Equal.trans(Maybe<&2,N>,G.next(~N, ~R, ~P, ~eq,G.sp(~N, ~R, ~P,g,n,v),x),G.next(~N, ~R, ~P, ~eq,g,x),G.first(~N,rest,q),next_sp(~N, ~R, ~P, ~eq,g,n,v,x),hn),
        segment_sp_frame(~N, ~R, ~P, ~eq,g,n,v,rest,Some{x},q,ar,ht)))

def segment_sh_frame(~N: Data, ~R: Data, ~P: Data, ~eq: N -> N -> Bool, +g: G.Graph<N,R,P>, +r: R, +v: Maybe<&2,N>, +xs: List<&2,N>, +p: Maybe<&2,N>, +q: Maybe<&2,N>, good: G.segment(~N, ~R, ~P, ~eq,g,p,xs,q)) -> G.segment(~N, ~R, ~P, ~eq,G.sh(~N, ~R, ~P,g,r,v),p,xs,q):
  match xs good:
    case Nil{} _: Unit{}
    case Con{+x,+rest} Tuple{hp,Tuple{hn,ht}}:
      (Equal.trans(Maybe<&2,N>,G.prev(~N, ~R, ~P, ~eq,G.sh(~N, ~R, ~P,g,r,v),x),G.prev(~N, ~R, ~P, ~eq,g,x),p,prev_sh(~N, ~R, ~P, ~eq,g,r,v,x),hp),
       (Equal.trans(Maybe<&2,N>,G.next(~N, ~R, ~P, ~eq,G.sh(~N, ~R, ~P,g,r,v),x),G.next(~N, ~R, ~P, ~eq,g,x),G.first(~N,rest,q),next_sh(~N, ~R, ~P, ~eq,g,r,v,x),hn),
        segment_sh_frame(~N, ~R, ~P, ~eq,g,r,v,rest,Some{x},q,ht)))

# Changing a segment's first predecessor preserves its entire suffix.
def segment_first_prev(~N: Data, ~R: Data, ~P: Data, ~eq: N -> N -> Bool, +g: G.Graph<N,R,P>, +x: N, +rest: List<&2,N>, +p: Maybe<&2,N>, +q: Maybe<&2,N>, +v: Maybe<&2,N>, same: {eq(x,x) == True{} : Bool}, away: G.away(~N,~eq,x,rest), good: G.segment(~N, ~R, ~P, ~eq,g,p,Con{x,rest},q)) -> G.segment(~N, ~R, ~P, ~eq,G.sp(~N, ~R, ~P,g,x,v),v,Con{x,rest},q):
  match good:
    case Tuple{hp,Tuple{hn,ht}}:
      (prev_sp_self(~N, ~R, ~P, ~eq,g,x,v,same),
       (Equal.trans(Maybe<&2,N>,G.next(~N, ~R, ~P, ~eq,G.sp(~N, ~R, ~P,g,x,v),x),G.next(~N, ~R, ~P, ~eq,g,x),G.first(~N,rest,q),next_sp(~N, ~R, ~P, ~eq,g,x,v,x),hn),
        segment_sp_frame(~N, ~R, ~P, ~eq,g,x,v,rest,Some{x},q,away,ht)))

def away_at(~N: Data, ~eq: N -> N -> Bool, +prefix: List<&2,N>, +n: N, +suffix: List<&2,N>, +x: N, h: G.away(~N,~eq,x,G.append(~N,prefix,Con{n,suffix}))) -> G.both({eq(x,n) == False{} : Bool}, {eq(n,x) == False{} : Bool}):
  match prefix h:
    case Nil{} Tuple{hn,ht}: hn
    case Con{a,rest} Tuple{ha,ht}: away_at(~N,~eq,rest,n,suffix,x,ht)

def away_delete(~N: Data, ~eq: N -> N -> Bool, +prefix: List<&2,N>, +n: N, +suffix: List<&2,N>, +x: N, h: G.away(~N,~eq,x,G.append(~N,prefix,Con{n,suffix}))) -> G.away(~N,~eq,x,G.append(~N,prefix,suffix)):
  match prefix h:
    case Nil{} Tuple{hn,ht}: ht
    case Con{a,rest} Tuple{ha,ht}: (ha,away_delete(~N,~eq,rest,n,suffix,x,ht))

def unique_delete(~N: Data, ~eq: N -> N -> Bool, +prefix: List<&2,N>, +n: N, +suffix: List<&2,N>, h: G.unique(~N,~eq,G.append(~N,prefix,Con{n,suffix}))) -> G.unique(~N,~eq,G.append(~N,prefix,suffix)):
  match prefix h:
    case Nil{} Tuple{hn,ht}: ht
    case Con{+a,+rest} Tuple{ha,ht}: (away_delete(~N,~eq,rest,n,suffix,a,ha),unique_delete(~N,~eq,rest,n,suffix,ht))

def swapped(~N: Data, ~eq: N -> N -> Bool, +a: N, +b: N, h: G.both({eq(a,b) == False{} : Bool}, {eq(b,a) == False{} : Bool})) -> G.both({eq(b,a) == False{} : Bool}, {eq(a,b) == False{} : Bool}):
  match h:
    case Tuple{ab,ba}: (ba,ab)

def deleted_away(~N: Data, ~eq: N -> N -> Bool, +prefix: List<&2,N>, +n: N, +suffix: List<&2,N>, h: G.unique(~N,~eq,G.append(~N,prefix,Con{n,suffix}))) -> G.away(~N,~eq,n,G.append(~N,prefix,suffix)):
  match prefix h:
    case Nil{} Tuple{hn,ht}: hn
    case Con{+a,+rest} Tuple{ha,ht}: (swapped(~N,~eq,a,n,away_at(~N,~eq,rest,n,suffix,a,ha)),deleted_away(~N,~eq,rest,n,suffix,ht))

def first_append(~N: Data, +a: List<&2,N>, +b: List<&2,N>, +q: Maybe<&2,N>) -> {G.first(~N,G.append(~N,a,b),q) == G.first(~N,a,G.first(~N,b,q)) : Maybe<&2,N>}:
  match a:
    case Nil{}: {==}
    case Con{x,rest}: {==}

def first_end(~N: Data, +a: List<&2,N>, +n: N, +q: Maybe<&2,N>, +v: Maybe<&2,N>) -> {G.first(~N,G.append(~N,a,Con{n,Nil{}}),q) == G.first(~N,G.append(~N,a,Con{n,Nil{}}),v) : Maybe<&2,N>}:
  match a:
    case Nil{}: {==}
    case Con{x,rest}: {==}

def segment_last_next(~N: Data, ~R: Data, ~P: Data, ~eq: N -> N -> Bool, +g: G.Graph<N,R,P>, +prefix: List<&2,N>, +n: N, +p: Maybe<&2,N>, +q: Maybe<&2,N>, +v: Maybe<&2,N>, +same: {eq(n,n) == True{} : Bool}, unique: G.unique(~N,~eq,G.append(~N,prefix,Con{n,Nil{}})), good: G.segment(~N, ~R, ~P, ~eq,g,p,G.append(~N,prefix,Con{n,Nil{}}),q)) -> G.segment(~N, ~R, ~P, ~eq,G.sn(~N, ~R, ~P,g,n,v),p,G.append(~N,prefix,Con{n,Nil{}}),v):
  match prefix unique good:
    case Nil{} _ Tuple{hp,Tuple{hn,ht}}:
      (Equal.trans(Maybe<&2,N>,G.prev(~N, ~R, ~P, ~eq,G.sn(~N, ~R, ~P,g,n,v),n),G.prev(~N, ~R, ~P, ~eq,g,n),p,prev_sn(~N, ~R, ~P, ~eq,g,n,v,n),hp),(next_sn_self(~N, ~R, ~P, ~eq,g,n,v,same),Unit{}))
    case Con{+x,+rest} Tuple{away,un} Tuple{hp,Tuple{hn,ht}}:
      (Equal.trans(Maybe<&2,N>,G.prev(~N, ~R, ~P, ~eq,G.sn(~N, ~R, ~P,g,n,v),x),G.prev(~N, ~R, ~P, ~eq,g,x),p,prev_sn(~N, ~R, ~P, ~eq,g,n,v,x),hp),
       (Equal.trans(Maybe<&2,N>,G.next(~N, ~R, ~P, ~eq,G.sn(~N, ~R, ~P,g,n,v),x),G.next(~N, ~R, ~P, ~eq,g,x),G.first(~N,G.append(~N,rest,Con{n,Nil{}}),v),next_sn_other(~N, ~R, ~P, ~eq,g,n,v,x,G.right({eq(x,n) == False{} : Bool},{eq(n,x) == False{} : Bool},away_at(~N,~eq,rest,n,Nil{},x,away))),Equal.trans(Maybe<&2,N>,G.next(~N, ~R, ~P, ~eq,g,x),G.first(~N,G.append(~N,rest,Con{n,Nil{}}),q),G.first(~N,G.append(~N,rest,Con{n,Nil{}}),v),hn,first_end(~N,rest,n,q,v))),
        segment_last_next(~N, ~R, ~P, ~eq,g,rest,n,Some{x},q,v,same,un,ht)))

def segment_join(~N: Data, ~R: Data, ~P: Data, ~eq: N -> N -> Bool, +a: List<&2,N>, +g: G.Graph<N,R,P>, +b: List<&2,N>, +p: Maybe<&2,N>, +q: Maybe<&2,N>, ga: G.segment(~N, ~R, ~P, ~eq,g,p,a,G.first(~N,b,q)), gb: G.segment(~N, ~R, ~P, ~eq,g,G.last(~N,a,p),b,q)) -> G.segment(~N, ~R, ~P, ~eq,g,p,G.append(~N,a,b),q):
  match a ga:
    case Nil{} _: gb
    case Con{+x,+rest} Tuple{hp,Tuple{hn,ht}}:
      (hp,(Equal.trans(Maybe<&2,N>,G.next(~N, ~R, ~P, ~eq,g,x),G.first(~N,rest,G.first(~N,b,q)),G.first(~N,G.append(~N,rest,b),q),hn,Equal.sym(Maybe<&2,N>,G.first(~N,G.append(~N,rest,b),q),G.first(~N,rest,G.first(~N,b,q)),first_append(~N,rest,b,q))),segment_join(~N, ~R, ~P, ~eq,rest,g,b,Some{x},q,ht,gb)))

def away_join(~N: Data, ~eq: N -> N -> Bool, +a: List<&2,N>, +b: List<&2,N>, +n: N, ga: G.away(~N,~eq,n,a), gb: G.away(~N,~eq,n,b)) -> G.away(~N,~eq,n,G.append(~N,a,b)):
  match a ga:
    case Nil{} _: gb
    case Con{x,rest} Tuple{hx,ht}: (hx,away_join(~N,~eq,rest,b,n,ht,gb))

def unique_join(~N: Data, ~eq: N -> N -> Bool, +a: List<&2,N>, +b: List<&2,N>, ua: G.unique(~N,~eq,a), +ub: G.unique(~N,~eq,b), dis: G.disjoint(~N,~eq,a,b)) -> G.unique(~N,~eq,G.append(~N,a,b)):
  match a ua dis:
    case Nil{} _ _: ub
    case Con{+x,+rest} Tuple{away,ut} Tuple{ab,dt}: (away_join(~N,~eq,rest,b,x,away,ab),unique_join(~N,~eq,rest,b,ut,ub,dt))

def disjoint_last(~N: Data, ~eq: N -> N -> Bool, +prefix: List<&2,N>, +n: N, +suffix: List<&2,N>, dis: G.disjoint(~N,~eq,G.append(~N,prefix,Con{n,Nil{}}),suffix)) -> G.away(~N,~eq,n,suffix):
  match prefix dis:
    case Nil{} Tuple{a,d}: a
    case Con{x,rest} Tuple{a,d}: disjoint_last(~N,~eq,rest,n,suffix,d)

def disjoint_head(~N: Data, ~eq: N -> N -> Bool, +prefix: List<&2,N>, +n: N, +suffix: List<&2,N>, dis: G.disjoint(~N,~eq,prefix,Con{n,suffix})) -> G.away(~N,~eq,n,prefix):
  match prefix dis:
    case Nil{} _: Unit{}
    case Con{+x,+rest} Tuple{Tuple{hn,ht},dt}: (swapped(~N,~eq,x,n,hn),disjoint_head(~N,~eq,rest,n,suffix,dt))

def last_end(~N: Data, +a: List<&2,N>, +n: N, +p: Maybe<&2,N>) -> {G.last(~N,G.append(~N,a,Con{n,Nil{}}),p) == Some{n} : Maybe<&2,N>}:
  match a:
    case Nil{}: {==}
    case Con{x,rest}: last_end(~N,rest,n,Some{x})

# A prefix/suffix split is the ordinary witness for removing a known member.
# The following lemmas extract the representation facts from the whole chain.
def first_middle(~N: Data, +a: List<&2,N>, +n: N, +b: List<&2,N>, +q: Maybe<&2,N>) -> {G.first(~N,G.append(~N,a,Con{n,b}),q) == G.first(~N,a,Some{n}) : Maybe<&2,N>}:
  match a:
    case Nil{}: {==}
    case Con{x,rest}: {==}

def prefix_segment(~N: Data, ~R: Data, ~P: Data, ~eq: N -> N -> Bool, +a: List<&2,N>, +g: G.Graph<N,R,P>, +n: N, +b: List<&2,N>, +p: Maybe<&2,N>, +q: Maybe<&2,N>, good: G.segment(~N, ~R, ~P, ~eq,g,p,G.append(~N,a,Con{n,b}),q)) -> G.segment(~N, ~R, ~P, ~eq,g,p,a,Some{n}):
  match a good:
    case Nil{} _: Unit{}
    case Con{+x,+rest} Tuple{hp,Tuple{hn,ht}}:
      (hp,(Equal.trans(Maybe<&2,N>,G.next(~N, ~R, ~P, ~eq,g,x),G.first(~N,G.append(~N,rest,Con{n,b}),q),G.first(~N,rest,Some{n}),hn,first_middle(~N,rest,n,b,q)),prefix_segment(~N, ~R, ~P, ~eq,rest,g,n,b,Some{x},q,ht)))

def member_prev(~N: Data, ~R: Data, ~P: Data, ~eq: N -> N -> Bool, +a: List<&2,N>, +g: G.Graph<N,R,P>, +n: N, +b: List<&2,N>, +p: Maybe<&2,N>, +q: Maybe<&2,N>, good: G.segment(~N, ~R, ~P, ~eq,g,p,G.append(~N,a,Con{n,b}),q)) -> {G.prev(~N, ~R, ~P, ~eq,g,n) == G.last(~N,a,p) : Maybe<&2,N>}:
  match a good:
    case Nil{} Tuple{hp,tail}: hp
    case Con{x,rest} Tuple{hp,Tuple{hn,ht}}: member_prev(~N, ~R, ~P, ~eq,rest,g,n,b,Some{x},q,ht)

def member_next(~N: Data, ~R: Data, ~P: Data, ~eq: N -> N -> Bool, +a: List<&2,N>, +g: G.Graph<N,R,P>, +n: N, +b: List<&2,N>, +p: Maybe<&2,N>, +q: Maybe<&2,N>, good: G.segment(~N, ~R, ~P, ~eq,g,p,G.append(~N,a,Con{n,b}),q)) -> {G.next(~N, ~R, ~P, ~eq,g,n) == G.first(~N,b,q) : Maybe<&2,N>}:
  match a good:
    case Nil{} Tuple{hp,Tuple{hn,ht}}: hn
    case Con{x,rest} Tuple{hp,Tuple{hn,ht}}: member_next(~N, ~R, ~P, ~eq,rest,g,n,b,Some{x},q,ht)

def suffix_segment(~N: Data, ~R: Data, ~P: Data, ~eq: N -> N -> Bool, +a: List<&2,N>, +g: G.Graph<N,R,P>, +n: N, +b: List<&2,N>, +p: Maybe<&2,N>, +q: Maybe<&2,N>, good: G.segment(~N, ~R, ~P, ~eq,g,p,G.append(~N,a,Con{n,b}),q)) -> G.segment(~N, ~R, ~P, ~eq,g,Some{n},b,q):
  match a good:
    case Nil{} Tuple{hp,Tuple{hn,ht}}: ht
    case Con{x,rest} Tuple{hp,Tuple{hn,ht}}: suffix_segment(~N, ~R, ~P, ~eq,rest,g,n,b,Some{x},q,ht)

def head_sn(~N: Data, ~R: Data, ~P: Data, ~req: R -> R -> Bool, +g: G.Graph<N,R,P>, +n: N, +v: Maybe<&2,N>, +r: R) -> {G.head(~N, ~R, ~P,~req,G.sn(~N, ~R, ~P,g,n,v),r) == G.head(~N, ~R, ~P,~req,g,r) : Maybe<&2,N>}:
  match g:
    case G.Graph{ns,ps,rs,f}: {==}

def head_sp(~N: Data, ~R: Data, ~P: Data, ~req: R -> R -> Bool, +g: G.Graph<N,R,P>, +n: N, +v: Maybe<&2,N>, +r: R) -> {G.head(~N, ~R, ~P,~req,G.sp(~N, ~R, ~P,g,n,v),r) == G.head(~N, ~R, ~P,~req,g,r) : Maybe<&2,N>}:
  match g:
    case G.Graph{ns,ps,rs,f}: {==}

def frame_sn(~N: Data, ~R: Data, ~P: Data, +g: G.Graph<N,R,P>, +n: N, +v: Maybe<&2,N>) -> {G.frame(~N, ~R, ~P,G.sn(~N, ~R, ~P,g,n,v)) == G.frame(~N, ~R, ~P,g) : P}:
  match g:
    case G.Graph{ns,ps,rs,f}: {==}

def frame_sp(~N: Data, ~R: Data, ~P: Data, +g: G.Graph<N,R,P>, +n: N, +v: Maybe<&2,N>) -> {G.frame(~N, ~R, ~P,G.sp(~N, ~R, ~P,g,n,v)) == G.frame(~N, ~R, ~P,g) : P}:
  match g:
    case G.Graph{ns,ps,rs,f}: {==}

def frame_sh(~N: Data, ~R: Data, ~P: Data, +g: G.Graph<N,R,P>, +r: R, +v: Maybe<&2,N>) -> {G.frame(~N, ~R, ~P,G.sh(~N, ~R, ~P,g,r,v)) == G.frame(~N, ~R, ~P,g) : P}:
  match g:
    case G.Graph{ns,ps,rs,f}: {==}

def head_sh(~N: Data, ~R: Data, ~P: Data, ~req: R -> R -> Bool, +g: G.Graph<N,R,P>, +r: R, +v: Maybe<&2,N>, +x: R) -> {G.head(~N, ~R, ~P,~req,G.sh(~N, ~R, ~P,g,r,v),x) == G.choose(~Maybe<&2,N>,req(r,x),v,G.head(~N, ~R, ~P,~req,g,x)) : Maybe<&2,N>}:
  match g:
    case G.Graph{ns,ps,rs,f}: {==}

def head_sh_self(~N: Data, ~R: Data, ~P: Data, ~req: R -> R -> Bool, +g: G.Graph<N,R,P>, +r: R, +v: Maybe<&2,N>, same: {req(r,r) == True{} : Bool}) -> {G.head(~N, ~R, ~P,~req,G.sh(~N, ~R, ~P,g,r,v),r) == v : Maybe<&2,N>}:
  %Equal.sym(Maybe<&2,N>,G.head(~N, ~R, ~P,~req,G.sh(~N, ~R, ~P,g,r,v),r),G.choose(~Maybe<&2,N>,req(r,r),v,G.head(~N, ~R, ~P,~req,g,r)),head_sh(~N, ~R, ~P,~req,g,r,v,r)) : {_ == v : Maybe<&2,N>}
  %Equal.sym(Bool,req(r,r),True{},same) : {G.choose(~Maybe<&2,N>,_,v,G.head(~N, ~R, ~P,~req,g,r)) == v : Maybe<&2,N>}
  {==}

def head_sh_other(~N: Data, ~R: Data, ~P: Data, ~req: R -> R -> Bool, +g: G.Graph<N,R,P>, +r: R, +v: Maybe<&2,N>, +x: R, neq: {req(r,x) == False{} : Bool}) -> {G.head(~N, ~R, ~P,~req,G.sh(~N, ~R, ~P,g,r,v),x) == G.head(~N, ~R, ~P,~req,g,x) : Maybe<&2,N>}:
  %Equal.sym(Maybe<&2,N>,G.head(~N, ~R, ~P,~req,G.sh(~N, ~R, ~P,g,r,v),x),G.choose(~Maybe<&2,N>,req(r,x),v,G.head(~N, ~R, ~P,~req,g,x)),head_sh(~N, ~R, ~P,~req,g,r,v,x)) : {_ == G.head(~N, ~R, ~P,~req,g,x) : Maybe<&2,N>}
  %Equal.sym(Bool,req(r,x),False{},neq) : {G.choose(~Maybe<&2,N>,_,v,G.head(~N, ~R, ~P,~req,g,x)) == G.head(~N, ~R, ~P,~req,g,x) : Maybe<&2,N>}
  {==}

def away_left(~N: Data, ~eq: N -> N -> Bool, +a: List<&2,N>, +b: List<&2,N>, +n: N, h: G.away(~N,~eq,n,G.append(~N,a,b))) -> G.away(~N,~eq,n,a):
  match a h:
    case Nil{} _: Unit{}
    case Con{x,rest} Tuple{hx,ht}: (hx,away_left(~N,~eq,rest,b,n,ht))

def away_right(~N: Data, ~eq: N -> N -> Bool, +a: List<&2,N>, +b: List<&2,N>, +n: N, h: G.away(~N,~eq,n,G.append(~N,a,b))) -> G.away(~N,~eq,n,b):
  match a h:
    case Nil{} _: h
    case Con{x,rest} Tuple{hx,ht}: away_right(~N,~eq,rest,b,n,ht)

def unique_left(~N: Data, ~eq: N -> N -> Bool, +a: List<&2,N>, +b: List<&2,N>, h: G.unique(~N,~eq,G.append(~N,a,b))) -> G.unique(~N,~eq,a):
  match a h:
    case Nil{} _: Unit{}
    case Con{+x,+rest} Tuple{ax,ut}: (away_left(~N,~eq,rest,b,x,ax),unique_left(~N,~eq,rest,b,ut))

def unique_right(~N: Data, ~eq: N -> N -> Bool, +a: List<&2,N>, +b: List<&2,N>, h: G.unique(~N,~eq,G.append(~N,a,b))) -> G.unique(~N,~eq,b):
  match a h:
    case Nil{} _: h
    case Con{x,rest} Tuple{ax,ut}: unique_right(~N,~eq,rest,b,ut)

def disjoint_unique(~N: Data, ~eq: N -> N -> Bool, +a: List<&2,N>, +b: List<&2,N>, h: G.unique(~N,~eq,G.append(~N,a,b))) -> G.disjoint(~N,~eq,a,b):
  match a h:
    case Nil{} _: Unit{}
    case Con{+x,+rest} Tuple{ax,ut}: (away_right(~N,~eq,rest,b,x,ax),disjoint_unique(~N,~eq,rest,b,ut))
