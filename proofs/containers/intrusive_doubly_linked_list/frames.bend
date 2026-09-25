import Base
import ./graph.bend as G
import ./shape.bend as S


def separated(~N: Data, ~eq: N -> N -> Bool, at: Maybe<&2,N>, xs: List<&2,N>) -> Data:
  match at:
    case None{}: Unit
    case Some{n}: G.away(~N,~eq,n,xs)

def optional_frame(~N: Data, ~R: Data, ~P: Data, ~eq: N -> N -> Bool, +g: G.Graph<N,R,P>, +at: Maybe<&2,N>, +v: Maybe<&2,N>, +xs: List<&2,N>, +p: Maybe<&2,N>, +q: Maybe<&2,N>, sep: separated(~N,~eq,at,xs), good: G.segment(~N, ~R, ~P, ~eq,g,p,xs,q)) -> G.segment(~N, ~R, ~P, ~eq,G.optional_prev(~N, ~R, ~P,g,at,v),p,xs,q):
  match at:
    case None{}: good
    case Some{n}: S.segment_sp_frame(~N, ~R, ~P, ~eq,g,n,v,xs,p,q,sep,good)

# Any other chain disjoint from the edited node and its two neighbours keeps
# every next/prev link. It may be another root in the same association.
def remove_segment_frame(~N: Data, ~R: Data, ~P: Data, ~eq: N -> N -> Bool, +g: G.Graph<N,R,P>, +r: R, +n: N, +before: Maybe<&2,N>, +after: Maybe<&2,N>, +xs: List<&2,N>, +p: Maybe<&2,N>, +q: Maybe<&2,N>, +an: G.away(~N,~eq,n,xs), ap: separated(~N,~eq,before,xs), aq: separated(~N,~eq,after,xs), good: G.segment(~N, ~R, ~P, ~eq,g,p,xs,q)) -> G.segment(~N, ~R, ~P, ~eq,G.cut(~N, ~R, ~P,g,r,n,before,after),p,xs,q):
  match before:
    case None{}:
      S.segment_sn_frame(~N, ~R, ~P, ~eq,G.sh(~N, ~R, ~P,G.optional_prev(~N, ~R, ~P,g,after,None{}),r,after),n,None{},xs,p,q,an,S.segment_sh_frame(~N, ~R, ~P, ~eq,G.optional_prev(~N, ~R, ~P,g,after,None{}),r,after,xs,p,q,optional_frame(~N, ~R, ~P, ~eq,g,after,None{},xs,p,q,aq,good)))
    case Some{+prev}:
      S.segment_sn_frame(~N, ~R, ~P, ~eq,G.sp(~N, ~R, ~P,G.sn(~N, ~R, ~P,G.optional_prev(~N, ~R, ~P,g,after,Some{prev}),prev,after),n,None{}),n,None{},xs,p,q,an,
        S.segment_sp_frame(~N, ~R, ~P, ~eq,G.sn(~N, ~R, ~P,G.optional_prev(~N, ~R, ~P,g,after,Some{prev}),prev,after),n,None{},xs,p,q,an,
          S.segment_sn_frame(~N, ~R, ~P, ~eq,G.optional_prev(~N, ~R, ~P,g,after,Some{prev}),prev,after,xs,p,q,ap,optional_frame(~N, ~R, ~P, ~eq,g,after,Some{prev},xs,p,q,aq,good))))

def prepend_segment_frame(~N: Data, ~R: Data, ~P: Data, ~eq: N -> N -> Bool, +g: G.Graph<N,R,P>, +r: R, +n: N, +head: Maybe<&2,N>, +xs: List<&2,N>, +p: Maybe<&2,N>, +q: Maybe<&2,N>, an: G.away(~N,~eq,n,xs), ah: separated(~N,~eq,head,xs), good: G.segment(~N, ~R, ~P, ~eq,g,p,xs,q)) -> G.segment(~N, ~R, ~P, ~eq,G.attach(~N, ~R, ~P,g,r,n,head),p,xs,q):
  S.segment_sh_frame(~N, ~R, ~P, ~eq,G.optional_prev(~N, ~R, ~P,G.sn(~N, ~R, ~P,g,n,head),head,Some{n}),r,Some{n},xs,p,q,optional_frame(~N, ~R, ~P, ~eq,G.sn(~N, ~R, ~P,g,n,head),head,Some{n},xs,p,q,ah,S.segment_sn_frame(~N, ~R, ~P, ~eq,g,n,head,xs,p,q,an,good)))

def root_effect(~N: Data, ~R: Data, ~P: Data, ~req: R -> R -> Bool, +g: G.Graph<N,R,P>, +r: R, p: Maybe<&2,N>, q: Maybe<&2,N>, +x: R) -> Maybe<&2,N>:
  match p:
    case None{}: G.choose(~Maybe<&2,N>,req(r,x),q,G.head(~N, ~R, ~P,~req,g,x))
    case Some{n}: G.head(~N, ~R, ~P,~req,g,x)

def remove_root_effect(~N: Data, ~R: Data, ~P: Data, ~req: R -> R -> Bool, +g: G.Graph<N,R,P>, +r: R, +n: N, +p: Maybe<&2,N>, +q: Maybe<&2,N>, +x: R) -> {G.head(~N, ~R, ~P,~req,G.cut(~N, ~R, ~P,g,r,n,p,q),x) == root_effect(~N, ~R, ~P,~req,g,r,p,q,x) : Maybe<&2,N>}:
  match g p q:
    case G.Graph{ns,ps,rs,f} None{} None{}: {==}
    case G.Graph{ns,ps,rs,f} None{} Some{a}: {==}
    case G.Graph{ns,ps,rs,f} Some{a} None{}: {==}
    case G.Graph{ns,ps,rs,f} Some{a} Some{b}: {==}

def root_effect_other(~N: Data, ~R: Data, ~P: Data, ~req: R -> R -> Bool, +g: G.Graph<N,R,P>, +r: R, +p: Maybe<&2,N>, +q: Maybe<&2,N>, +x: R, neq: {req(r,x) == False{} : Bool}) -> {root_effect(~N, ~R, ~P,~req,g,r,p,q,x) == G.head(~N, ~R, ~P,~req,g,x) : Maybe<&2,N>}:
  match p:
    case None{}:
      %Equal.sym(Bool,req(r,x),False{},neq) : {G.choose(~Maybe<&2,N>,_,q,G.head(~N, ~R, ~P,~req,g,x)) == G.head(~N, ~R, ~P,~req,g,x) : Maybe<&2,N>}
      {==}
    case Some{n}: {==}

def remove_other_root(~N: Data, ~R: Data, ~P: Data, ~req: R -> R -> Bool, +g: G.Graph<N,R,P>, +r: R, +n: N, +p: Maybe<&2,N>, +q: Maybe<&2,N>, +x: R, neq: {req(r,x) == False{} : Bool}) -> {G.head(~N, ~R, ~P,~req,G.cut(~N, ~R, ~P,g,r,n,p,q),x) == G.head(~N, ~R, ~P,~req,g,x) : Maybe<&2,N>}:
  Equal.trans(Maybe<&2,N>,G.head(~N, ~R, ~P,~req,G.cut(~N, ~R, ~P,g,r,n,p,q),x),root_effect(~N, ~R, ~P,~req,g,r,p,q,x),G.head(~N, ~R, ~P,~req,g,x),remove_root_effect(~N, ~R, ~P,~req,g,r,n,p,q,x),root_effect_other(~N, ~R, ~P,~req,g,r,p,q,x,neq))

def prepend_root_effect(~N: Data, ~R: Data, ~P: Data, ~req: R -> R -> Bool, +g: G.Graph<N,R,P>, +r: R, +n: N, +h: Maybe<&2,N>, +x: R) -> {G.head(~N, ~R, ~P,~req,G.attach(~N, ~R, ~P,g,r,n,h),x) == G.choose(~Maybe<&2,N>,req(r,x),Some{n},G.head(~N, ~R, ~P,~req,g,x)) : Maybe<&2,N>}:
  match g h:
    case G.Graph{ns,ps,rs,f} None{}: {==}
    case G.Graph{ns,ps,rs,f} Some{a}: {==}

def prepend_other_root(~N: Data, ~R: Data, ~P: Data, ~req: R -> R -> Bool, +g: G.Graph<N,R,P>, +r: R, +n: N, +h: Maybe<&2,N>, +x: R, neq: {req(r,x) == False{} : Bool}) -> {G.head(~N, ~R, ~P,~req,G.attach(~N, ~R, ~P,g,r,n,h),x) == G.head(~N, ~R, ~P,~req,g,x) : Maybe<&2,N>}:
  %Equal.sym(Maybe<&2,N>,G.head(~N, ~R, ~P,~req,G.attach(~N, ~R, ~P,g,r,n,h),x),G.choose(~Maybe<&2,N>,req(r,x),Some{n},G.head(~N, ~R, ~P,~req,g,x)),prepend_root_effect(~N, ~R, ~P,~req,g,r,n,h,x)) : {_ == G.head(~N, ~R, ~P,~req,g,x) : Maybe<&2,N>}
  %Equal.sym(Bool,req(r,x),False{},neq) : {G.choose(~Maybe<&2,N>,_,Some{n},G.head(~N, ~R, ~P,~req,g,x)) == G.head(~N, ~R, ~P,~req,g,x) : Maybe<&2,N>}
  {==}

def removed_next(~N: Data, ~R: Data, ~P: Data, ~eq: N -> N -> Bool, +g: G.Graph<N,R,P>, +r: R, +n: N, +p: Maybe<&2,N>, +q: Maybe<&2,N>, same: {eq(n,n) == True{} : Bool}) -> {G.next(~N, ~R, ~P, ~eq,G.cut(~N, ~R, ~P,g,r,n,p,q),n) == None{} : Maybe<&2,N>}:
  match p:
    case None{}: S.next_sn_self(~N, ~R, ~P, ~eq,G.sh(~N, ~R, ~P,G.optional_prev(~N, ~R, ~P,g,q,None{}),r,q),n,None{},same)
    case Some{prev}: S.next_sn_self(~N, ~R, ~P, ~eq,G.sp(~N, ~R, ~P,G.sn(~N, ~R, ~P,G.optional_prev(~N, ~R, ~P,g,q,Some{prev}),prev,q),n,None{}),n,None{},same)

def removed_nonhead_prev(~N: Data, ~R: Data, ~P: Data, ~eq: N -> N -> Bool, +g: G.Graph<N,R,P>, +r: R, +n: N, +p: N, +q: Maybe<&2,N>, same: {eq(n,n) == True{} : Bool}) -> {G.prev(~N, ~R, ~P, ~eq,G.cut(~N, ~R, ~P,g,r,n,Some{p},q),n) == None{} : Maybe<&2,N>}:
  Equal.trans(Maybe<&2,N>,G.prev(~N, ~R, ~P, ~eq,G.cut(~N, ~R, ~P,g,r,n,Some{p},q),n),G.prev(~N, ~R, ~P, ~eq,G.sp(~N, ~R, ~P,G.sn(~N, ~R, ~P,G.optional_prev(~N, ~R, ~P,g,q,Some{p}),p,q),n,None{}),n),None{},S.prev_sn(~N, ~R, ~P, ~eq,G.sp(~N, ~R, ~P,G.sn(~N, ~R, ~P,G.optional_prev(~N, ~R, ~P,g,q,Some{p}),p,q),n,None{}),n,None{},n),S.prev_sp_self(~N, ~R, ~P, ~eq,G.sn(~N, ~R, ~P,G.optional_prev(~N, ~R, ~P,g,q,Some{p}),p,q),n,None{},same))

def removed_head_prev(~N: Data, ~R: Data, ~P: Data, ~eq: N -> N -> Bool, +g: G.Graph<N,R,P>, +r: R, +n: N, +q: Maybe<&2,N>, hp: {G.prev(~N, ~R, ~P, ~eq,g,n) == None{} : Maybe<&2,N>}, aq: separated(~N,~eq,q,Con{n,Nil{}})) -> {G.prev(~N, ~R, ~P, ~eq,G.cut(~N, ~R, ~P,g,r,n,None{},q),n) == None{} : Maybe<&2,N>}:
  match q aq:
    case None{} _:
      Equal.trans(Maybe<&2,N>,G.prev(~N, ~R, ~P, ~eq,G.cut(~N, ~R, ~P,g,r,n,None{},None{}),n),G.prev(~N, ~R, ~P, ~eq,G.sh(~N, ~R, ~P,g,r,None{}),n),None{},S.prev_sn(~N, ~R, ~P, ~eq,G.sh(~N, ~R, ~P,g,r,None{}),n,None{},n),Equal.trans(Maybe<&2,N>,G.prev(~N, ~R, ~P, ~eq,G.sh(~N, ~R, ~P,g,r,None{}),n),G.prev(~N, ~R, ~P, ~eq,g,n),None{},S.prev_sh(~N, ~R, ~P, ~eq,g,r,None{},n),hp))
    case Some{+x} Tuple{Tuple{neq,rev},rest}:
      Equal.trans(Maybe<&2,N>,G.prev(~N, ~R, ~P, ~eq,G.cut(~N, ~R, ~P,g,r,n,None{},Some{x}),n),G.prev(~N, ~R, ~P, ~eq,G.sh(~N, ~R, ~P,G.sp(~N, ~R, ~P,g,x,None{}),r,Some{x}),n),None{},S.prev_sn(~N, ~R, ~P, ~eq,G.sh(~N, ~R, ~P,G.sp(~N, ~R, ~P,g,x,None{}),r,Some{x}),n,None{},n),Equal.trans(Maybe<&2,N>,G.prev(~N, ~R, ~P, ~eq,G.sh(~N, ~R, ~P,G.sp(~N, ~R, ~P,g,x,None{}),r,Some{x}),n),G.prev(~N, ~R, ~P, ~eq,G.sp(~N, ~R, ~P,g,x,None{}),n),None{},S.prev_sh(~N, ~R, ~P, ~eq,G.sp(~N, ~R, ~P,g,x,None{}),r,Some{x},n),Equal.trans(Maybe<&2,N>,G.prev(~N, ~R, ~P, ~eq,G.sp(~N, ~R, ~P,g,x,None{}),n),G.prev(~N, ~R, ~P, ~eq,g,n),None{},S.prev_sp_other(~N, ~R, ~P, ~eq,g,x,None{},n,neq),hp)))
