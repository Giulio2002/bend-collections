import Base
import ./graph.bend as G
import ./edits.bend as E
import ../../lib/logic.bend as Logic


# The split fields are proof witnesses, not runtime arguments to remove.
# They name the old ordered sequence independently of the link algorithm.
type Edit<-N: Data> is Data:
  Prepend{node: N}
  RemoveHead{node: N, rest: List<&2,N>}
  RemoveAfter{prefix: List<&2,N>, previous: N, node: N, suffix: List<&2,N>}

def order(~N: Data, op: Edit<N>, xs: List<&2,N>) -> List<&2,N>:
  match op:
    case Prepend{n}: Con{n,xs}
    case RemoveHead{n,rest}: rest
    case RemoveAfter{a,p,n,b}: G.append(~N,G.append(~N,a,Con{p,Nil{}}),b)

def step(~N: Data, ~R: Data, ~P: Data, ~eq: N -> N -> Bool, ~req: R -> R -> Bool, g: G.Graph<N,R,P>, r: R, op: Edit<N>) -> G.Graph<N,R,P>:
  match op:
    case Prepend{n}: G.prepend(~N, ~R, ~P,~req,g,r,n)
    case RemoveHead{n,rest}: G.remove(~N, ~R, ~P, ~eq,g,r,n)
    case RemoveAfter{a,p,n,b}: G.remove(~N, ~R, ~P, ~eq,g,r,n)

def permitted(~N: Data, ~R: Data, ~P: Data, ~eq: N -> N -> Bool, +g: G.Graph<N,R,P>, op: Edit<N>, +xs: List<&2,N>) -> Data:
  match op:
    case Prepend{+n}: G.both(G.away(~N,~eq,n,xs),G.both({G.prev(~N, ~R, ~P, ~eq,g,n) == None{} : Maybe<&2,N>},{G.next(~N, ~R, ~P, ~eq,g,n) == None{} : Maybe<&2,N>}))
    case RemoveHead{n,rest}: {xs == Con{n,rest} : List<&2,N>}
    case RemoveAfter{a,p,n,b}: {xs == G.append(~N,G.append(~N,a,Con{p,Nil{}}),Con{n,b}) : List<&2,N>}

def legal(~N: Data, ~R: Data, ~P: Data, ~eq: N -> N -> Bool, ~req: R -> R -> Bool, ops: List<&2,Edit<N>>, +g: G.Graph<N,R,P>, +r: R, +xs: List<&2,N>) -> Data:
  match ops:
    case Nil{}: Unit
    case Con{+op,+rest}: G.both(permitted(~N, ~R, ~P, ~eq,g,op,xs),legal(~N, ~R, ~P, ~eq, ~req,rest,step(~N, ~R, ~P, ~eq, ~req,g,r,op),r,order(~N,op,xs)))

def run(~N: Data, ~R: Data, ~P: Data, ~eq: N -> N -> Bool, ~req: R -> R -> Bool, ops: List<&2,Edit<N>>, g: G.Graph<N,R,P>, +r: R) -> G.Graph<N,R,P>:
  match ops:
    case Nil{}: g
    case Con{op,rest}: run(~N, ~R, ~P, ~eq, ~req,rest,step(~N, ~R, ~P, ~eq, ~req,g,r,op),r)

def orders(~N: Data, ops: List<&2,Edit<N>>, xs: List<&2,N>) -> List<&2,N>:
  match ops:
    case Nil{}: xs
    case Con{op,rest}: orders(~N,rest,order(~N,op,xs))

def step_preserves(~N: Data, ~R: Data, ~P: Data, ~eq: N -> N -> Bool, ~req: R -> R -> Bool, ~reflex: @x: N -> {eq(x,x) == True{} : Bool}, +g: G.Graph<N,R,P>, +r: R, +op: Edit<N>, +xs: List<&2,N>, rsame: {req(r,r) == True{} : Bool}, pre: permitted(~N, ~R, ~P, ~eq,g,op,xs), good: G.valid(~N, ~R, ~P, ~eq, ~req,g,r,xs)) -> G.valid(~N, ~R, ~P, ~eq, ~req,step(~N, ~R, ~P, ~eq, ~req,g,r,op),r,order(~N,op,xs)):
  match op pre:
    case Prepend{+n} Tuple{away,Tuple{hp,hn}}: E.prepend_preserves(~N, ~R, ~P, ~eq, ~req,~reflex,g,r,n,xs,rsame,away,hp,good)
    case RemoveHead{+n,+rest} equation:
      E.remove_head_preserves(~N, ~R, ~P, ~eq, ~req,~reflex,g,r,n,rest,rsame,Logic.subst(List<&2,N>,ys => G.valid(~N, ~R, ~P, ~eq, ~req,g,r,ys),xs,Con{n,rest},equation,good))
    case RemoveAfter{+a,+p,+n,+b} equation:
      E.remove_nonhead_preserves(~N, ~R, ~P, ~eq, ~req,~reflex,g,r,n,a,p,b,Logic.subst(List<&2,N>,ys => G.valid(~N, ~R, ~P, ~eq, ~req,g,r,ys),xs,G.append(~N,G.append(~N,a,Con{p,Nil{}}),Con{n,b}),equation,good))

# Induction over any finite legal history, not a bound or enumeration.
def run_preserves(~N: Data, ~R: Data, ~P: Data, ~eq: N -> N -> Bool, ~req: R -> R -> Bool, ~reflex: @x: N -> {eq(x,x) == True{} : Bool}, +ops: List<&2,Edit<N>>, +g: G.Graph<N,R,P>, +r: R, +xs: List<&2,N>, +rsame: {req(r,r) == True{} : Bool}, history: legal(~N, ~R, ~P, ~eq, ~req,ops,g,r,xs), good: G.valid(~N, ~R, ~P, ~eq, ~req,g,r,xs)) -> G.valid(~N, ~R, ~P, ~eq, ~req,run(~N, ~R, ~P, ~eq, ~req,ops,g,r),r,orders(~N,ops,xs)):
  match ops history:
    case Nil{} _: good
    case Con{+op,+rest} Tuple{pre,ht}:
      run_preserves(~N, ~R, ~P, ~eq, ~req,~reflex,rest,step(~N, ~R, ~P, ~eq, ~req,g,r,op),r,order(~N,op,xs),rsame,ht,step_preserves(~N, ~R, ~P, ~eq, ~req,~reflex,g,r,op,xs,rsame,pre,good))

def step_frame(~N: Data, ~R: Data, ~P: Data, ~eq: N -> N -> Bool, ~req: R -> R -> Bool, +g: G.Graph<N,R,P>, +r: R, +op: Edit<N>) -> {G.frame(~N, ~R, ~P,step(~N, ~R, ~P, ~eq, ~req,g,r,op)) == G.frame(~N, ~R, ~P,g) : P}:
  match op:
    case Prepend{+n}: E.attach_frame(~N, ~R, ~P,g,r,n,G.head(~N, ~R, ~P,~req,g,r))
    case RemoveHead{+n,rest}: E.cut_frame(~N, ~R, ~P,g,r,n,G.prev(~N, ~R, ~P, ~eq,g,n),G.next(~N, ~R, ~P, ~eq,g,n))
    case RemoveAfter{a,p,+n,b}: E.cut_frame(~N, ~R, ~P,g,r,n,G.prev(~N, ~R, ~P, ~eq,g,n),G.next(~N, ~R, ~P, ~eq,g,n))

def run_frame(~N: Data, ~R: Data, ~P: Data, ~eq: N -> N -> Bool, ~req: R -> R -> Bool, +ops: List<&2,Edit<N>>, +g: G.Graph<N,R,P>, +r: R) -> {G.frame(~N, ~R, ~P,run(~N, ~R, ~P, ~eq, ~req,ops,g,r)) == G.frame(~N, ~R, ~P,g) : P}:
  match ops:
    case Nil{}: {==}
    case Con{+op,+rest}:
      Equal.trans(P,G.frame(~N, ~R, ~P,run(~N, ~R, ~P, ~eq, ~req,rest,step(~N, ~R, ~P, ~eq, ~req,g,r,op),r)),G.frame(~N, ~R, ~P,step(~N, ~R, ~P, ~eq, ~req,g,r,op)),G.frame(~N, ~R, ~P,g),run_frame(~N, ~R, ~P, ~eq, ~req,rest,step(~N, ~R, ~P, ~eq, ~req,g,r,op),r),step_frame(~N, ~R, ~P, ~eq, ~req,g,r,op))
