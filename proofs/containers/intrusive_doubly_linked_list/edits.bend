import Base
import ./graph.bend as G
import ./shape.bend as S


# Prepend preserves a whole reciprocal, unique chain. Identity comparison is
# proof-only; the production algorithm still performs only its field accesses.
def prepend_valid(~N: Data, ~R: Data, ~P: Data, ~eq: N -> N -> Bool, ~req: R -> R -> Bool, ~reflex: @x: N -> {eq(x,x) == True{} : Bool}, +g: G.Graph<N,R,P>, +r: R, +n: N, +xs: List<&2,N>, +rsame: {req(r,r) == True{} : Bool}, +un: G.unique(~N,~eq,xs), +away: G.away(~N,~eq,n,xs), +detached: {G.prev(~N, ~R, ~P, ~eq,g,n) == None{} : Maybe<&2,N>}, good: G.segment(~N, ~R, ~P, ~eq,g,None{},xs,None{})) -> G.valid(~N, ~R, ~P, ~eq, ~req,G.attach(~N, ~R, ~P,g,r,n,G.first(~N,xs,None{})),r,Con{n,xs}):
  match xs un away:
    case Nil{} _ _:
      ((Unit{},Unit{}),
       (S.head_sh_self(~N, ~R, ~P,~req,G.sn(~N, ~R, ~P,g,n,None{}),r,Some{n},rsame),
        (Equal.trans(Maybe<&2,N>,G.prev(~N, ~R, ~P, ~eq,G.sh(~N, ~R, ~P,G.sn(~N, ~R, ~P,g,n,None{}),r,Some{n}),n),G.prev(~N, ~R, ~P, ~eq,G.sn(~N, ~R, ~P,g,n,None{}),n),None{},S.prev_sh(~N, ~R, ~P, ~eq,G.sn(~N, ~R, ~P,g,n,None{}),r,Some{n},n),Equal.trans(Maybe<&2,N>,G.prev(~N, ~R, ~P, ~eq,G.sn(~N, ~R, ~P,g,n,None{}),n),G.prev(~N, ~R, ~P, ~eq,g,n),None{},S.prev_sn(~N, ~R, ~P, ~eq,g,n,None{},n),detached)),
         (Equal.trans(Maybe<&2,N>,G.next(~N, ~R, ~P, ~eq,G.sh(~N, ~R, ~P,G.sn(~N, ~R, ~P,g,n,None{}),r,Some{n}),n),G.next(~N, ~R, ~P, ~eq,G.sn(~N, ~R, ~P,g,n,None{}),n),None{},S.next_sh(~N, ~R, ~P, ~eq,G.sn(~N, ~R, ~P,g,n,None{}),r,Some{n},n),S.next_sn_self(~N, ~R, ~P, ~eq,g,n,None{},reflex(n))),Unit{}))))
    case Con{+h,+tail} Tuple{+ah,+ut} Tuple{Tuple{+nh,+hn},+at}:
      (((((nh,hn),at)),(ah,ut)),
       (S.head_sh_self(~N, ~R, ~P,~req,G.sp(~N, ~R, ~P,G.sn(~N, ~R, ~P,g,n,Some{h}),h,Some{n}),r,Some{n},rsame),
        (Equal.trans(Maybe<&2,N>,G.prev(~N, ~R, ~P, ~eq,G.sh(~N, ~R, ~P,G.sp(~N, ~R, ~P,G.sn(~N, ~R, ~P,g,n,Some{h}),h,Some{n}),r,Some{n}),n),G.prev(~N, ~R, ~P, ~eq,G.sp(~N, ~R, ~P,G.sn(~N, ~R, ~P,g,n,Some{h}),h,Some{n}),n),None{},S.prev_sh(~N, ~R, ~P, ~eq,G.sp(~N, ~R, ~P,G.sn(~N, ~R, ~P,g,n,Some{h}),h,Some{n}),r,Some{n},n),Equal.trans(Maybe<&2,N>,G.prev(~N, ~R, ~P, ~eq,G.sp(~N, ~R, ~P,G.sn(~N, ~R, ~P,g,n,Some{h}),h,Some{n}),n),G.prev(~N, ~R, ~P, ~eq,G.sn(~N, ~R, ~P,g,n,Some{h}),n),None{},S.prev_sp_other(~N, ~R, ~P, ~eq,G.sn(~N, ~R, ~P,g,n,Some{h}),h,Some{n},n,hn),Equal.trans(Maybe<&2,N>,G.prev(~N, ~R, ~P, ~eq,G.sn(~N, ~R, ~P,g,n,Some{h}),n),G.prev(~N, ~R, ~P, ~eq,g,n),None{},S.prev_sn(~N, ~R, ~P, ~eq,g,n,Some{h},n),detached))),
         (Equal.trans(Maybe<&2,N>,G.next(~N, ~R, ~P, ~eq,G.sh(~N, ~R, ~P,G.sp(~N, ~R, ~P,G.sn(~N, ~R, ~P,g,n,Some{h}),h,Some{n}),r,Some{n}),n),G.next(~N, ~R, ~P, ~eq,G.sp(~N, ~R, ~P,G.sn(~N, ~R, ~P,g,n,Some{h}),h,Some{n}),n),Some{h},S.next_sh(~N, ~R, ~P, ~eq,G.sp(~N, ~R, ~P,G.sn(~N, ~R, ~P,g,n,Some{h}),h,Some{n}),r,Some{n},n),Equal.trans(Maybe<&2,N>,G.next(~N, ~R, ~P, ~eq,G.sp(~N, ~R, ~P,G.sn(~N, ~R, ~P,g,n,Some{h}),h,Some{n}),n),G.next(~N, ~R, ~P, ~eq,G.sn(~N, ~R, ~P,g,n,Some{h}),n),Some{h},S.next_sp(~N, ~R, ~P, ~eq,G.sn(~N, ~R, ~P,g,n,Some{h}),h,Some{n},n),S.next_sn_self(~N, ~R, ~P, ~eq,g,n,Some{h},reflex(n)))),
          S.segment_sh_frame(~N, ~R, ~P, ~eq,G.sp(~N, ~R, ~P,G.sn(~N, ~R, ~P,g,n,Some{h}),h,Some{n}),r,Some{n},Con{h,tail},Some{n},None{},S.segment_first_prev(~N, ~R, ~P, ~eq,G.sn(~N, ~R, ~P,g,n,Some{h}),h,tail,None{},None{},Some{n},reflex(h),ah,S.segment_sn_frame(~N, ~R, ~P, ~eq,g,n,Some{h},Con{h,tail},None{},None{},((nh,hn),at),good)))))))


def remove_head_valid(~N: Data, ~R: Data, ~P: Data, ~eq: N -> N -> Bool, ~req: R -> R -> Bool, ~reflex: @x: N -> {eq(x,x) == True{} : Bool}, +g: G.Graph<N,R,P>, +r: R, +n: N, +xs: List<&2,N>, +rsame: {req(r,r) == True{} : Bool}, +un: G.unique(~N,~eq,xs), away: G.away(~N,~eq,n,xs), good: G.segment(~N, ~R, ~P, ~eq,g,Some{n},xs,None{})) -> G.valid(~N, ~R, ~P, ~eq, ~req,G.cut(~N, ~R, ~P,g,r,n,None{},G.first(~N,xs,None{})),r,xs):
  match xs un:
    case Nil{} _:
      (Unit{},(Equal.trans(Maybe<&2,N>,G.head(~N, ~R, ~P,~req,G.sn(~N, ~R, ~P,G.sh(~N, ~R, ~P,g,r,None{}),n,None{}),r),G.head(~N, ~R, ~P,~req,G.sh(~N, ~R, ~P,g,r,None{}),r),None{},S.head_sn(~N, ~R, ~P,~req,G.sh(~N, ~R, ~P,g,r,None{}),n,None{},r),S.head_sh_self(~N, ~R, ~P,~req,g,r,None{},rsame)),Unit{}))
    case Con{+h,+tail} Tuple{+ah,+ut}:
      ((ah,ut),
       (Equal.trans(Maybe<&2,N>,G.head(~N, ~R, ~P,~req,G.sn(~N, ~R, ~P,G.sh(~N, ~R, ~P,G.optional_prev(~N, ~R, ~P,g,G.first(~N,xs,None{}),None{}),r,G.first(~N,xs,None{})),n,None{}),r),G.head(~N, ~R, ~P,~req,G.sh(~N, ~R, ~P,G.optional_prev(~N, ~R, ~P,g,G.first(~N,xs,None{}),None{}),r,G.first(~N,xs,None{})),r),Some{h},S.head_sn(~N, ~R, ~P,~req,G.sh(~N, ~R, ~P,G.optional_prev(~N, ~R, ~P,g,G.first(~N,xs,None{}),None{}),r,G.first(~N,xs,None{})),n,None{},r),S.head_sh_self(~N, ~R, ~P,~req,G.optional_prev(~N, ~R, ~P,g,G.first(~N,xs,None{}),None{}),r,Some{h},rsame)),
        S.segment_sn_frame(~N, ~R, ~P, ~eq,G.sh(~N, ~R, ~P,G.optional_prev(~N, ~R, ~P,g,G.first(~N,xs,None{}),None{}),r,G.first(~N,xs,None{})),n,None{},Con{h,tail},None{},None{},away,S.segment_sh_frame(~N, ~R, ~P, ~eq,G.optional_prev(~N, ~R, ~P,g,G.first(~N,xs,None{}),None{}),r,Some{h},Con{h,tail},None{},None{},S.segment_first_prev(~N, ~R, ~P, ~eq,g,h,tail,Some{n},None{},None{},reflex(h),ah,good)))))

def optional_prefix(~N: Data, ~R: Data, ~P: Data, ~eq: N -> N -> Bool, +g: G.Graph<N,R,P>, +prefix: List<&2,N>, +suffix: List<&2,N>, +p: N, +n: N, dis: G.disjoint(~N,~eq,prefix,suffix), good: G.segment(~N, ~R, ~P, ~eq,g,None{},prefix,Some{n})) -> G.segment(~N, ~R, ~P, ~eq,G.optional_prev(~N, ~R, ~P,g,G.first(~N,suffix,None{}),Some{p}),None{},prefix,Some{n}):
  match suffix:
    case Nil{}: good
    case Con{+h,+tail}: S.segment_sp_frame(~N, ~R, ~P, ~eq,g,h,Some{p},prefix,None{},Some{n},S.disjoint_head(~N,~eq,prefix,h,tail,dis),good)

def optional_suffix(~N: Data, ~R: Data, ~P: Data, ~eq: N -> N -> Bool, ~reflex: @x: N -> {eq(x,x) == True{} : Bool}, +g: G.Graph<N,R,P>, +suffix: List<&2,N>, +p: N, +n: N, un: G.unique(~N,~eq,suffix), good: G.segment(~N, ~R, ~P, ~eq,g,Some{n},suffix,None{})) -> G.segment(~N, ~R, ~P, ~eq,G.optional_prev(~N, ~R, ~P,g,G.first(~N,suffix,None{}),Some{p}),Some{p},suffix,None{}):
  match suffix un:
    case Nil{} _: Unit{}
    case Con{+h,+tail} Tuple{ah,ut}: S.segment_first_prev(~N, ~R, ~P, ~eq,g,h,tail,Some{n},None{},Some{p},reflex(h),ah,good)

def cut_nonhead_root(~N: Data, ~R: Data, ~P: Data, ~req: R -> R -> Bool, +g: G.Graph<N,R,P>, +r: R, +n: N, +p: N, +q: Maybe<&2,N>, +x: R) -> {G.head(~N, ~R, ~P,~req,G.cut(~N, ~R, ~P,g,r,n,Some{p},q),x) == G.head(~N, ~R, ~P,~req,g,x) : Maybe<&2,N>}:
  match g q:
    case G.Graph{ns,ps,rs,f} None{}: {==}
    case G.Graph{ns,ps,rs,f} Some{h}: {==}

def join_last(~N: Data, ~R: Data, ~P: Data, ~eq: N -> N -> Bool, +a: List<&2,N>, +g: G.Graph<N,R,P>, +p: N, +b: List<&2,N>, ga: G.segment(~N, ~R, ~P, ~eq,g,None{},G.append(~N,a,Con{p,Nil{}}),G.first(~N,b,None{})), gb: G.segment(~N, ~R, ~P, ~eq,g,Some{p},b,None{})) -> G.segment(~N, ~R, ~P, ~eq,g,None{},G.append(~N,G.append(~N,a,Con{p,Nil{}}),b),None{}):
  S.segment_join(~N, ~R, ~P, ~eq,G.append(~N,a,Con{p,Nil{}}),g,b,None{},None{},ga,
    %Equal.sym(Maybe<&2,N>,G.last(~N,G.append(~N,a,Con{p,Nil{}}),None{}),Some{p},S.last_end(~N,a,p,None{})) : G.segment(~N, ~R, ~P, ~eq,g,_,b,None{})
    gb)


# The input is a zipper around the known member. Its premises are exactly
# separate, unique prefix/member/suffix identities and their old field facts;
# no postcondition is assumed. Prefix and suffix can have arbitrary lengths.
def remove_nonhead_valid(~N: Data, ~R: Data, ~P: Data, ~eq: N -> N -> Bool, ~req: R -> R -> Bool, ~reflex: @x: N -> {eq(x,x) == True{} : Bool}, +g: G.Graph<N,R,P>, +r: R, +n: N, +a: List<&2,N>, +p: N, +b: List<&2,N>, +up: G.unique(~N,~eq,G.append(~N,a,Con{p,Nil{}})), +ub: G.unique(~N,~eq,b), +dis: G.disjoint(~N,~eq,G.append(~N,a,Con{p,Nil{}}),b), +np: G.away(~N,~eq,n,G.append(~N,a,Con{p,Nil{}})), +nb: G.away(~N,~eq,n,b), root: {G.head(~N, ~R, ~P,~req,g,r) == G.first(~N,G.append(~N,a,Con{p,Nil{}}),None{}) : Maybe<&2,N>}, prefix: G.segment(~N, ~R, ~P, ~eq,g,None{},G.append(~N,a,Con{p,Nil{}}),Some{n}), suffix: G.segment(~N, ~R, ~P, ~eq,g,Some{n},b,None{})) -> G.valid(~N, ~R, ~P, ~eq, ~req,G.cut(~N, ~R, ~P,g,r,n,Some{p},G.first(~N,b,None{})),r,G.append(~N,G.append(~N,a,Con{p,Nil{}}),b)):
  (S.unique_join(~N,~eq,G.append(~N,a,Con{p,Nil{}}),b,up,ub,dis),
   (Equal.trans(Maybe<&2,N>,G.head(~N, ~R, ~P,~req,G.sn(~N, ~R, ~P,G.sp(~N, ~R, ~P,G.sn(~N, ~R, ~P,G.optional_prev(~N, ~R, ~P,g,G.first(~N,b,None{}),Some{p}),p,G.first(~N,b,None{})),n,None{}),n,None{}),r),G.head(~N, ~R, ~P,~req,g,r),G.first(~N,G.append(~N,G.append(~N,a,Con{p,Nil{}}),b),None{}),cut_nonhead_root(~N, ~R, ~P,~req,g,r,n,p,G.first(~N,b,None{}),r),
      Equal.trans(Maybe<&2,N>,G.head(~N, ~R, ~P,~req,g,r),G.first(~N,G.append(~N,a,Con{p,Nil{}}),None{}),G.first(~N,G.append(~N,G.append(~N,a,Con{p,Nil{}}),b),None{}),root,
        Equal.trans(Maybe<&2,N>,G.first(~N,G.append(~N,a,Con{p,Nil{}}),None{}),G.first(~N,G.append(~N,a,Con{p,Nil{}}),G.first(~N,b,None{})),G.first(~N,G.append(~N,G.append(~N,a,Con{p,Nil{}}),b),None{}),S.first_end(~N,a,p,None{},G.first(~N,b,None{})),Equal.sym(Maybe<&2,N>,G.first(~N,G.append(~N,G.append(~N,a,Con{p,Nil{}}),b),None{}),G.first(~N,G.append(~N,a,Con{p,Nil{}}),G.first(~N,b,None{})),S.first_append(~N,G.append(~N,a,Con{p,Nil{}}),b,None{}))))),
    join_last(~N, ~R, ~P, ~eq,a,G.sn(~N, ~R, ~P,G.sp(~N, ~R, ~P,G.sn(~N, ~R, ~P,G.optional_prev(~N, ~R, ~P,g,G.first(~N,b,None{}),Some{p}),p,G.first(~N,b,None{})),n,None{}),n,None{}),p,b,
      S.segment_sn_frame(~N, ~R, ~P, ~eq,G.sp(~N, ~R, ~P,G.sn(~N, ~R, ~P,G.optional_prev(~N, ~R, ~P,g,G.first(~N,b,None{}),Some{p}),p,G.first(~N,b,None{})),n,None{}),n,None{},G.append(~N,a,Con{p,Nil{}}),None{},G.first(~N,b,None{}),np,
        S.segment_sp_frame(~N, ~R, ~P, ~eq,G.sn(~N, ~R, ~P,G.optional_prev(~N, ~R, ~P,g,G.first(~N,b,None{}),Some{p}),p,G.first(~N,b,None{})),n,None{},G.append(~N,a,Con{p,Nil{}}),None{},G.first(~N,b,None{}),np,
          S.segment_last_next(~N, ~R, ~P, ~eq,G.optional_prev(~N, ~R, ~P,g,G.first(~N,b,None{}),Some{p}),a,p,None{},Some{n},G.first(~N,b,None{}),reflex(p),up,optional_prefix(~N, ~R, ~P, ~eq,g,G.append(~N,a,Con{p,Nil{}}),b,p,n,dis,prefix)))),
      S.segment_sn_frame(~N, ~R, ~P, ~eq,G.sp(~N, ~R, ~P,G.sn(~N, ~R, ~P,G.optional_prev(~N, ~R, ~P,g,G.first(~N,b,None{}),Some{p}),p,G.first(~N,b,None{})),n,None{}),n,None{},b,Some{p},None{},nb,
        S.segment_sp_frame(~N, ~R, ~P, ~eq,G.sn(~N, ~R, ~P,G.optional_prev(~N, ~R, ~P,g,G.first(~N,b,None{}),Some{p}),p,G.first(~N,b,None{})),n,None{},b,Some{p},None{},nb,
          S.segment_sn_frame(~N, ~R, ~P, ~eq,G.optional_prev(~N, ~R, ~P,g,G.first(~N,b,None{}),Some{p}),p,G.first(~N,b,None{}),b,Some{p},None{},S.disjoint_last(~N,~eq,a,p,b,dis),optional_suffix(~N, ~R, ~P, ~eq,~reflex,g,b,p,n,ub,suffix)))))))

# Public semantic statements: all input facts are taken from valid(g,order).
def prepend_preserves(~N: Data, ~R: Data, ~P: Data, ~eq: N -> N -> Bool, ~req: R -> R -> Bool, ~reflex: @x: N -> {eq(x,x) == True{} : Bool}, +g: G.Graph<N,R,P>, +r: R, +n: N, +xs: List<&2,N>, rsame: {req(r,r) == True{} : Bool}, away: G.away(~N,~eq,n,xs), detached: {G.prev(~N, ~R, ~P, ~eq,g,n) == None{} : Maybe<&2,N>}, valid: G.valid(~N, ~R, ~P, ~eq, ~req,g,r,xs)) -> G.valid(~N, ~R, ~P, ~eq, ~req,G.prepend(~N, ~R, ~P,~req,g,r,n),r,Con{n,xs}):
  match valid:
    case Tuple{un,Tuple{root,good}}:
      %Equal.sym(Maybe<&2,N>,G.head(~N, ~R, ~P,~req,g,r),G.first(~N,xs,None{}),root) : G.valid(~N, ~R, ~P, ~eq, ~req,G.attach(~N, ~R, ~P,g,r,n,_),r,Con{n,xs})
      prepend_valid(~N, ~R, ~P, ~eq, ~req,~reflex,g,r,n,xs,rsame,un,away,detached,good)

def remove_head_preserves(~N: Data, ~R: Data, ~P: Data, ~eq: N -> N -> Bool, ~req: R -> R -> Bool, ~reflex: @x: N -> {eq(x,x) == True{} : Bool}, +g: G.Graph<N,R,P>, +r: R, +n: N, +xs: List<&2,N>, rsame: {req(r,r) == True{} : Bool}, valid: G.valid(~N, ~R, ~P, ~eq, ~req,g,r,Con{n,xs})) -> G.valid(~N, ~R, ~P, ~eq, ~req,G.remove(~N, ~R, ~P, ~eq,g,r,n),r,xs):
  match valid:
    case Tuple{Tuple{away,un},Tuple{root,Tuple{hp,Tuple{hn,good}}}}:
      %Equal.sym(Maybe<&2,N>,G.prev(~N, ~R, ~P, ~eq,g,n),None{},hp) : G.valid(~N, ~R, ~P, ~eq, ~req,G.cut(~N, ~R, ~P,g,r,n,_,G.next(~N, ~R, ~P, ~eq,g,n)),r,xs)
      %Equal.sym(Maybe<&2,N>,G.next(~N, ~R, ~P, ~eq,g,n),G.first(~N,xs,None{}),hn) : G.valid(~N, ~R, ~P, ~eq, ~req,G.cut(~N, ~R, ~P,g,r,n,None{},_),r,xs)
      remove_head_valid(~N, ~R, ~P, ~eq, ~req,~reflex,g,r,n,xs,rsame,un,away,good)

def remove_nonhead_preserves(~N: Data, ~R: Data, ~P: Data, ~eq: N -> N -> Bool, ~req: R -> R -> Bool, ~reflex: @x: N -> {eq(x,x) == True{} : Bool}, +g: G.Graph<N,R,P>, +r: R, +n: N, +a: List<&2,N>, +p: N, +b: List<&2,N>, valid: G.valid(~N, ~R, ~P, ~eq, ~req,g,r,G.append(~N,G.append(~N,a,Con{p,Nil{}}),Con{n,b}))) -> G.valid(~N, ~R, ~P, ~eq, ~req,G.remove(~N, ~R, ~P, ~eq,g,r,n),r,G.append(~N,G.append(~N,a,Con{p,Nil{}}),b)):
  match valid:
    case Tuple{un0,Tuple{root,good0}}:
      +un : G.unique(~N,~eq,G.append(~N,G.append(~N,a,Con{p,Nil{}}),Con{n,b})) = un0
      +good : G.segment(~N, ~R, ~P, ~eq,g,None{},G.append(~N,G.append(~N,a,Con{p,Nil{}}),Con{n,b}),None{}) = good0
      +remaining : G.unique(~N,~eq,G.append(~N,G.append(~N,a,Con{p,Nil{}}),b)) = S.unique_delete(~N,~eq,G.append(~N,a,Con{p,Nil{}}),n,b,un)
      +away : G.away(~N,~eq,n,G.append(~N,G.append(~N,a,Con{p,Nil{}}),b)) = S.deleted_away(~N,~eq,G.append(~N,a,Con{p,Nil{}}),n,b,un)
      %Equal.sym(Maybe<&2,N>,G.prev(~N, ~R, ~P, ~eq,g,n),Some{p},Equal.trans(Maybe<&2,N>,G.prev(~N, ~R, ~P, ~eq,g,n),G.last(~N,G.append(~N,a,Con{p,Nil{}}),None{}),Some{p},S.member_prev(~N, ~R, ~P, ~eq,G.append(~N,a,Con{p,Nil{}}),g,n,b,None{},None{},good),S.last_end(~N,a,p,None{}))) : G.valid(~N, ~R, ~P, ~eq, ~req,G.cut(~N, ~R, ~P,g,r,n,_,G.next(~N, ~R, ~P, ~eq,g,n)),r,G.append(~N,G.append(~N,a,Con{p,Nil{}}),b))
      %Equal.sym(Maybe<&2,N>,G.next(~N, ~R, ~P, ~eq,g,n),G.first(~N,b,None{}),S.member_next(~N, ~R, ~P, ~eq,G.append(~N,a,Con{p,Nil{}}),g,n,b,None{},None{},good)) : G.valid(~N, ~R, ~P, ~eq, ~req,G.cut(~N, ~R, ~P,g,r,n,Some{p},_),r,G.append(~N,G.append(~N,a,Con{p,Nil{}}),b))
      remove_nonhead_valid(~N, ~R, ~P, ~eq, ~req,~reflex,g,r,n,a,p,b,
        S.unique_left(~N,~eq,G.append(~N,a,Con{p,Nil{}}),b,remaining),S.unique_right(~N,~eq,G.append(~N,a,Con{p,Nil{}}),b,remaining),S.disjoint_unique(~N,~eq,G.append(~N,a,Con{p,Nil{}}),b,remaining),
        S.away_left(~N,~eq,G.append(~N,a,Con{p,Nil{}}),b,n,away),S.away_right(~N,~eq,G.append(~N,a,Con{p,Nil{}}),b,n,away),
        Equal.trans(Maybe<&2,N>,G.head(~N, ~R, ~P,~req,g,r),G.first(~N,G.append(~N,G.append(~N,a,Con{p,Nil{}}),Con{n,b}),None{}),G.first(~N,G.append(~N,a,Con{p,Nil{}}),None{}),root,Equal.trans(Maybe<&2,N>,G.first(~N,G.append(~N,G.append(~N,a,Con{p,Nil{}}),Con{n,b}),None{}),G.first(~N,G.append(~N,a,Con{p,Nil{}}),Some{n}),G.first(~N,G.append(~N,a,Con{p,Nil{}}),None{}),S.first_middle(~N,G.append(~N,a,Con{p,Nil{}}),n,b,None{}),S.first_end(~N,a,p,Some{n},None{}))),
        S.prefix_segment(~N, ~R, ~P, ~eq,G.append(~N,a,Con{p,Nil{}}),g,n,b,None{},None{},good),S.suffix_segment(~N, ~R, ~P, ~eq,G.append(~N,a,Con{p,Nil{}}),g,n,b,None{},None{},good))

def attach_frame(~N: Data, ~R: Data, ~P: Data, +g: G.Graph<N,R,P>, +r: R, +n: N, +h: Maybe<&2,N>) -> {G.frame(~N, ~R, ~P,G.attach(~N, ~R, ~P,g,r,n,h)) == G.frame(~N, ~R, ~P,g) : P}:
  match g h:
    case G.Graph{ns,ps,rs,f} None{}: {==}
    case G.Graph{ns,ps,rs,f} Some{x}: {==}

def cut_frame(~N: Data, ~R: Data, ~P: Data, +g: G.Graph<N,R,P>, +r: R, +n: N, +p: Maybe<&2,N>, +q: Maybe<&2,N>) -> {G.frame(~N, ~R, ~P,G.cut(~N, ~R, ~P,g,r,n,p,q)) == G.frame(~N, ~R, ~P,g) : P}:
  match g p q:
    case G.Graph{ns,ps,rs,f} None{} None{}: {==}
    case G.Graph{ns,ps,rs,f} None{} Some{x}: {==}
    case G.Graph{ns,ps,rs,f} Some{x} None{}: {==}
    case G.Graph{ns,ps,rs,f} Some{x} Some{y}: {==}
