import Base
import ./graph.bend as G
import ./spec.bend as Spec
import ./writes.bend as W
import ../../../src/containers/intrusive_doubly_linked_list.bend as L


# A shadow can contain proof-only history. real need not be injective: two
# finite-map logs may denote the same physical array. This is a simulation
# relation, not an impossible requirement that arrays retain the write log.
def apply(~N: Data, ~R: Data, ~P: Data, ~I: Data, ~root: I -> R, g: G.Graph<N,R,P>, e: Spec.Edit<N,I>) -> G.Graph<N,R,P>:
  match e:
    case Spec.Next{n,m}: G.sn(~N, ~R, ~P,g,n,m)
    case Spec.Prev{n,m}: G.sp(~N, ~R, ~P,g,n,m)
    case Spec.Head{i,m}: G.sh(~N, ~R, ~P,g,root(i),m)
    case Spec.Nonempty{i,n}: G.sh(~N, ~R, ~P,g,root(i),Some{n})

def run(~N: Data, ~R: Data, ~P: Data, ~I: Data, ~root: I -> R, es: List<&2,Spec.Edit<N,I>>, g: G.Graph<N,R,P>) -> G.Graph<N,R,P>:
  match es:
    case Nil{}: g
    case Con{e,rest}: run(~N, ~R, ~P, ~I, ~root,rest,apply(~N, ~R, ~P, ~I, ~root,g,e))

# Only primitive setter equations are premises. They can be discharged for
# each reachable, in-bounds state; no universal law about invalid IDs or an
# out-of-bounds array operation is required. No list postcondition appears.
def laws(~S: Type, ~N: Data, ~R: Data, ~P: Data, ~I: Data, ~real: G.Graph<N,R,P> -> S, ~root: I -> R, ~sn: S -> N -> Maybe<&2,N> -> S, ~sp: S -> N -> Maybe<&2,N> -> S, ~sh: S -> I -> Maybe<&2,N> -> S, ~sf: S -> I -> N -> S, es: List<&2,Spec.Edit<N,I>>, +g: G.Graph<N,R,P>) -> Data:
  match es:
    case Nil{}: Unit
    case Con{+e,+rest}: G.both({Spec.apply(~S, ~N, ~I, ~sn, ~sp, ~sh, ~sf,real(g),e) == real(apply(~N, ~R, ~P, ~I, ~root,g,e)) : S},laws(~S, ~N, ~R, ~P, ~I, ~real, ~root, ~sn, ~sp, ~sh, ~sf,rest,apply(~N, ~R, ~P, ~I, ~root,g,e)))

def program_refines(~S: Type, ~N: Data, ~R: Data, ~P: Data, ~I: Data, ~real: G.Graph<N,R,P> -> S, ~root: I -> R, ~sn: S -> N -> Maybe<&2,N> -> S, ~sp: S -> N -> Maybe<&2,N> -> S, ~sh: S -> I -> Maybe<&2,N> -> S, ~sf: S -> I -> N -> S, +es: List<&2,Spec.Edit<N,I>>, +g: G.Graph<N,R,P>, hs: laws(~S, ~N, ~R, ~P, ~I, ~real, ~root, ~sn, ~sp, ~sh, ~sf,es,g)) -> {Spec.run(~S, ~N, ~I, ~sn, ~sp, ~sh, ~sf,es,real(g)) == real(run(~N, ~R, ~P, ~I, ~root,es,g)) : S}:
  match es hs:
    case Nil{} _: {==}
    case Con{+e,+rest} Tuple{he,ht}:
      %Equal.sym(S,Spec.apply(~S, ~N, ~I, ~sn, ~sp, ~sh, ~sf,real(g),e),real(apply(~N, ~R, ~P, ~I, ~root,g,e)),he) : {Spec.run(~S, ~N, ~I, ~sn, ~sp, ~sh, ~sf,rest,_) == real(run(~N, ~R, ~P, ~I, ~root,rest,apply(~N, ~R, ~P, ~I, ~root,g,e))) : S}
      program_refines(~S, ~N, ~R, ~P, ~I, ~real, ~root, ~sn, ~sp, ~sh, ~sf,rest,apply(~N, ~R, ~P, ~I, ~root,g,e),ht)

def remove_program(~N: Data, ~R: Data, ~P: Data, ~I: Data, ~root: I -> R, +g: G.Graph<N,R,P>, +i: I, +n: N, +p: Maybe<&2,N>, +q: Maybe<&2,N>) -> {run(~N, ~R, ~P, ~I, ~root,Spec.remove(N,I,i,n,p,q),g) == G.cut(~N, ~R, ~P,g,root(i),n,p,q) : G.Graph<N,R,P>}:
  match p q:
    case None{} None{}: {==}
    case None{} Some{x}: {==}
    case Some{x} None{}: {==}
    case Some{x} Some{y}: {==}

def prepend_program(~N: Data, ~R: Data, ~P: Data, ~I: Data, ~root: I -> R, +g: G.Graph<N,R,P>, +i: I, +n: N, +h: Maybe<&2,N>) -> {run(~N, ~R, ~P, ~I, ~root,Spec.prepend(N,I,i,n,h),g) == G.attach(~N, ~R, ~P,g,root(i),n,h) : G.Graph<N,R,P>}:
  match h:
    case None{}: {==}
    case Some{x}: {==}


# The source/model connection reaches the actual exported remove function.
def remove_refines(~S: Type, ~N: Data, ~R: Data, ~P: Data, ~I: Data, ~real: G.Graph<N,R,P> -> S, ~root: I -> R, ~sn: S -> N -> Maybe<&2,N> -> S, ~sp: S -> N -> Maybe<&2,N> -> S, ~sh: S -> I -> Maybe<&2,N> -> S, ~sf: S -> I -> N -> S, ~eq: N -> N -> Bool, ~next: S -> N -> S & Maybe<&2,N>, ~prev: S -> N -> S & Maybe<&2,N>, +g: G.Graph<N,R,P>, +i: I, +n: N, hn: {next(real(g),n) == (real(g),G.next(~N, ~R, ~P,~eq,g,n)) : S & Maybe<&2,N>}, hp: {prev(real(g),n) == (real(g),G.prev(~N, ~R, ~P,~eq,g,n)) : S & Maybe<&2,N>}, hs: laws(~S, ~N, ~R, ~P, ~I, ~real, ~root, ~sn, ~sp, ~sh, ~sf,Spec.remove(N,I,i,n,G.prev(~N, ~R, ~P,~eq,g,n),G.next(~N, ~R, ~P,~eq,g,n)),g)) -> {L.remove(~S,~N,~I,~next,~prev,~sn,~sp,~sh,real(g),i,n) == real(G.remove(~N, ~R, ~P,~eq,g,root(i),n)) : S}:
  Equal.trans(S,L.remove(~S,~N,~I,~next,~prev,~sn,~sp,~sh,real(g),i,n),Spec.run(~S, ~N, ~I, ~sn, ~sp, ~sh, ~sf,Spec.remove(N,I,i,n,G.prev(~N, ~R, ~P,~eq,g,n),G.next(~N, ~R, ~P,~eq,g,n)),real(g)),real(G.remove(~N, ~R, ~P,~eq,g,root(i),n)),
    W.remove_writes(~S,~N,~I,~next,~prev,~sn,~sp,~sh,~sf,real(g),real(g),real(g),i,n,G.prev(~N, ~R, ~P,~eq,g,n),G.next(~N, ~R, ~P,~eq,g,n),hn,hp),
    Equal.trans(S,Spec.run(~S, ~N, ~I, ~sn, ~sp, ~sh, ~sf,Spec.remove(N,I,i,n,G.prev(~N, ~R, ~P,~eq,g,n),G.next(~N, ~R, ~P,~eq,g,n)),real(g)),real(run(~N, ~R, ~P, ~I, ~root,Spec.remove(N,I,i,n,G.prev(~N, ~R, ~P,~eq,g,n),G.next(~N, ~R, ~P,~eq,g,n)),g)),real(G.remove(~N, ~R, ~P,~eq,g,root(i),n)),program_refines(~S, ~N, ~R, ~P, ~I, ~real, ~root, ~sn, ~sp, ~sh, ~sf,Spec.remove(N,I,i,n,G.prev(~N, ~R, ~P,~eq,g,n),G.next(~N, ~R, ~P,~eq,g,n)),g,hs),Equal.cong(G.Graph<N,R,P>,S,real,run(~N, ~R, ~P, ~I, ~root,Spec.remove(N,I,i,n,G.prev(~N, ~R, ~P,~eq,g,n),G.next(~N, ~R, ~P,~eq,g,n)),g),G.cut(~N, ~R, ~P,g,root(i),n,G.prev(~N, ~R, ~P,~eq,g,n),G.next(~N, ~R, ~P,~eq,g,n)),remove_program(~N, ~R, ~P, ~I, ~root,g,i,n,G.prev(~N, ~R, ~P,~eq,g,n),G.next(~N, ~R, ~P,~eq,g,n)))))


# H and I remain distinct. The read equation expresses coherence of the
# particular reader/writer contexts; it does not force identical types.
def prepend_refines(~S: Type, ~N: Data, ~R: Data, ~P: Data, ~I: Data, ~real: G.Graph<N,R,P> -> S, ~root: I -> R, ~sn: S -> N -> Maybe<&2,N> -> S, ~sp: S -> N -> Maybe<&2,N> -> S, ~sh: S -> I -> Maybe<&2,N> -> S, ~sf: S -> I -> N -> S, ~H: Data, ~req: R -> R -> Bool, ~get: S -> H -> S & Maybe<&2,N>, +g: G.Graph<N,R,P>, +h: H, +i: I, +n: N, hg: {get(real(g),h) == (real(g),G.head(~N, ~R, ~P,~req,g,root(i))) : S & Maybe<&2,N>}, hs: laws(~S, ~N, ~R, ~P, ~I, ~real, ~root, ~sn, ~sp, ~sh, ~sf,Spec.prepend(N,I,i,n,G.head(~N, ~R, ~P,~req,g,root(i))),g)) -> {L.prepend_as(~S,~N,~H,~I,~get,~sn,~sp,~sf,real(g),h,i,n) == real(G.prepend(~N, ~R, ~P,~req,g,root(i),n)) : S}:
  Equal.trans(S,L.prepend_as(~S,~N,~H,~I,~get,~sn,~sp,~sf,real(g),h,i,n),Spec.run(~S, ~N, ~I, ~sn, ~sp, ~sh, ~sf,Spec.prepend(N,I,i,n,G.head(~N, ~R, ~P,~req,g,root(i))),real(g)),real(G.prepend(~N, ~R, ~P,~req,g,root(i),n)),
    W.prepend_writes(~S,~N,~H,~I,~get,~sn,~sp,~sh,~sf,real(g),real(g),h,i,n,G.head(~N, ~R, ~P,~req,g,root(i)),hg),
    Equal.trans(S,Spec.run(~S, ~N, ~I, ~sn, ~sp, ~sh, ~sf,Spec.prepend(N,I,i,n,G.head(~N, ~R, ~P,~req,g,root(i))),real(g)),real(run(~N, ~R, ~P, ~I, ~root,Spec.prepend(N,I,i,n,G.head(~N, ~R, ~P,~req,g,root(i))),g)),real(G.prepend(~N, ~R, ~P,~req,g,root(i),n)),program_refines(~S, ~N, ~R, ~P, ~I, ~real, ~root, ~sn, ~sp, ~sh, ~sf,Spec.prepend(N,I,i,n,G.head(~N, ~R, ~P,~req,g,root(i))),g,hs),Equal.cong(G.Graph<N,R,P>,S,real,run(~N, ~R, ~P, ~I, ~root,Spec.prepend(N,I,i,n,G.head(~N, ~R, ~P,~req,g,root(i))),g),G.attach(~N, ~R, ~P,g,root(i),n,G.head(~N, ~R, ~P,~req,g,root(i))),prepend_program(~N, ~R, ~P, ~I, ~root,g,i,n,G.head(~N, ~R, ~P,~req,g,root(i))))))
