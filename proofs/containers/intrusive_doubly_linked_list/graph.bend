import Base

def both(-A: Data, -B: Data) -> Data:
  Sigma<&2,&2,A,_ => B>

def left(-A: Data, -B: Data, p: both(A,B)) -> A:
  (a,b) = p
  a

def right(-A: Data, -B: Data, p: both(A,B)) -> B:
  (a,b) = p
  b

# Proof-only finite maps. New bindings shadow old ones; no storage layout,
# allocation strategy, machine integer width or payload type is assumed.
type Binding<-K: Data, -V: Data> is Data:
  Binding{key: K, value: V}

def choose(~V: Data, b: Bool, yes: V, no: V) -> V:
  match b:
    case True{}: yes
    case False{}: no

def lookup(~K: Data, ~V: Data, ~eq: K -> K -> Bool, +key: K, xs: List<&2, Binding<K, V>>, +default: V) -> V:
  match xs:
    case Nil{}: default
    case Con{Binding{k, v}, rest}: choose(~V, eq(k, key), v, lookup(~K, ~V, ~eq, key, rest, default))

type Graph<-N: Data, -R: Data, -P: Data> is Data:
  Graph{nexts: List<&2, Binding<N, Maybe<&2, N>>>, prevs: List<&2, Binding<N, Maybe<&2, N>>>, roots: List<&2, Binding<R, Maybe<&2, N>>>, frame: P}

def next(~N: Data, ~R: Data, ~P: Data, ~eq: N -> N -> Bool, g: Graph<N,R,P>, n: N) -> Maybe<&2,N>:
  Graph{ns, ps, rs, f} = g
  lookup(~N, ~Maybe<&2,N>, ~eq, n, ns, None{})

def prev(~N: Data, ~R: Data, ~P: Data, ~eq: N -> N -> Bool, g: Graph<N,R,P>, n: N) -> Maybe<&2,N>:
  Graph{ns, ps, rs, f} = g
  lookup(~N, ~Maybe<&2,N>, ~eq, n, ps, None{})

def head(~N: Data, ~R: Data, ~P: Data, ~eq: R -> R -> Bool, g: Graph<N,R,P>, r: R) -> Maybe<&2,N>:
  Graph{ns, ps, rs, f} = g
  lookup(~R, ~Maybe<&2,N>, ~eq, r, rs, None{})

def frame(~N: Data, ~R: Data, ~P: Data, g: Graph<N,R,P>) -> P:
  Graph{ns, ps, rs, f} = g
  f

def sn(~N: Data, ~R: Data, ~P: Data, g: Graph<N,R,P>, n: N, v: Maybe<&2,N>) -> Graph<N,R,P>:
  Graph{ns, ps, rs, f} = g
  Graph{Con{Binding{n,v},ns}, ps, rs, f}

def sp(~N: Data, ~R: Data, ~P: Data, g: Graph<N,R,P>, n: N, v: Maybe<&2,N>) -> Graph<N,R,P>:
  Graph{ns, ps, rs, f} = g
  Graph{ns, Con{Binding{n,v},ps}, rs, f}

def sh(~N: Data, ~R: Data, ~P: Data, g: Graph<N,R,P>, r: R, v: Maybe<&2,N>) -> Graph<N,R,P>:
  Graph{ns, ps, rs, f} = g
  Graph{ns, ps, Con{Binding{r,v},rs}, f}

def first(~N: Data, xs: List<&2,N>, d: Maybe<&2,N>) -> Maybe<&2,N>:
  match xs:
    case Nil{}: d
    case Con{x, rest}: Some{x}

def last(~N: Data, xs: List<&2,N>, d: Maybe<&2,N>) -> Maybe<&2,N>:
  match xs:
    case Nil{}: d
    case Con{x, rest}: last(~N, rest, Some{x})

def append(~N: Data, xs: List<&2,N>, +ys: List<&2,N>) -> List<&2,N>:
  match xs:
    case Nil{}: ys
    case Con{x, rest}: Con{x, append(~N, rest, ys)}

# Away records disjoint identities in both directions. A lawful equality is
# reflexive and agrees with identity; the algorithm does not execute it.
def away(~N: Data, ~eq: N -> N -> Bool, +n: N, xs: List<&2,N>) -> Data:
  match xs:
    case Nil{}: Unit
    case Con{x, rest}: both(both({eq(n,x) == False{} : Bool}, {eq(x,n) == False{} : Bool}), away(~N, ~eq, n, rest))

def unique(~N: Data, ~eq: N -> N -> Bool, xs: List<&2,N>) -> Data:
  match xs:
    case Nil{}: Unit
    case Con{+x, +rest}: both(away(~N, ~eq, x, rest), unique(~N, ~eq, rest))

# A segment states BOTH links of EVERY member, with explicit external ends.
# With unique(xs), segment(g,None,xs,None) describes an acyclic reciprocal
# chain, rather than merely an ordered write trace.
def segment(~N: Data, ~R: Data, ~P: Data, ~eq: N -> N -> Bool, +g: Graph<N,R,P>, p: Maybe<&2,N>, xs: List<&2,N>, +q: Maybe<&2,N>) -> Data:
  match xs:
    case Nil{}: Unit
    case Con{+x, +rest}: both({prev(~N,~R,~P,~eq,g,x) == p : Maybe<&2,N>}, both({next(~N,~R,~P,~eq,g,x) == first(~N,rest,q) : Maybe<&2,N>}, segment(~N,~R,~P,~eq,g,Some{x},rest,q)))

def valid(~N: Data, ~R: Data, ~P: Data, ~eq: N -> N -> Bool, ~req: R -> R -> Bool, +g: Graph<N,R,P>, r: R, +xs: List<&2,N>) -> Data:
  both(unique(~N,~eq,xs), both({head(~N,~R,~P,~req,g,r) == first(~N,xs,None{}) : Maybe<&2,N>}, segment(~N,~R,~P,~eq,g,None{},xs,None{})))

def disjoint(~N: Data, ~eq: N -> N -> Bool, xs: List<&2,N>, +ys: List<&2,N>) -> Data:
  match xs:
    case Nil{}: Unit
    case Con{x,rest}: both(away(~N,~eq,x,ys),disjoint(~N,~eq,rest,ys))

def optional_prev(~N: Data, ~R: Data, ~P: Data, g: Graph<N,R,P>, at: Maybe<&2,N>, v: Maybe<&2,N>) -> Graph<N,R,P>:
  match at:
    case None{}: g
    case Some{n}: sp(~N,~R,~P,g,n,v)

def attach(~N: Data, ~R: Data, ~P: Data, g: Graph<N,R,P>, r: R, +n: N, +h: Maybe<&2,N>) -> Graph<N,R,P>:
  sh(~N,~R,~P,optional_prev(~N,~R,~P,sn(~N,~R,~P,g,n,h),h,Some{n}),r,Some{n})

def cut_left(~N: Data, ~R: Data, ~P: Data, g: Graph<N,R,P>, r: R, +n: N, p: Maybe<&2,N>, q: Maybe<&2,N>) -> Graph<N,R,P>:
  match p:
    case None{}: sn(~N,~R,~P,sh(~N,~R,~P,g,r,q),n,None{})
    case Some{p}: sn(~N,~R,~P,sp(~N,~R,~P,sn(~N,~R,~P,g,p,q),n,None{}),n,None{})

def cut(~N: Data, ~R: Data, ~P: Data, g: Graph<N,R,P>, r: R, +n: N, +p: Maybe<&2,N>, +q: Maybe<&2,N>) -> Graph<N,R,P>:
  cut_left(~N,~R,~P,optional_prev(~N,~R,~P,g,q,p),r,n,p,q)

def prepend(~N: Data, ~R: Data, ~P: Data, ~req: R -> R -> Bool, +g: Graph<N,R,P>, +r: R, n: N) -> Graph<N,R,P>:
  attach(~N,~R,~P,g,r,n,head(~N,~R,~P,~req,g,r))

def remove(~N: Data, ~R: Data, ~P: Data, ~eq: N -> N -> Bool, +g: Graph<N,R,P>, r: R, +n: N) -> Graph<N,R,P>:
  cut(~N,~R,~P,g,r,n,prev(~N,~R,~P,~eq,g,n),next(~N,~R,~P,~eq,g,n))
