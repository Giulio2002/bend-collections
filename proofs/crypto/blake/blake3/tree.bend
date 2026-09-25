import Base
import ../../../../src/crypto/blake/blake3/types.bend as T
import ../../../../src/crypto/blake/blake3/compress.bend as C
import ../../../../src/crypto/blake/blake3/blake3.bend as K
import ../../../lib/logic.bend as L
import ../../../lib/nat.bend as N
import ../../../../spec/lib/common.bend as SC
import ../../../../spec/crypto/blake/blake3.bend as S
import ./compress.bend as P
import ./lists.bend as LS

# The implementation's subtree stack computes the specification's tree.
#
# For a list F of chunk outputs pushed onto the stack (as chaining values) and
# a pending last output o, folding the stack into o gives the root of the
# specification's tree over F ++ [o] (tree_stack below), for every F and o.
# The invariant: a stack whose h lowest slots are empty (E(h, t)) absorbs
# 2^h chaining values as one complete subtree carried into slot h (complete),
# and fewer than 2^h values plus the pending output fold into the
# specification's tree of height h (partial).

# ---- node-level agreement ----

def out_cv_correct(+o: T.Out) -> {K.out_cv(o) == S.cv(o) : T.CV}:
  match o:
    case T.Out{+c,+b,+t,+len,+flags}: P.compress_correct(c,b,t,len,flags)

def parent_block_correct(+l: T.CV, +r: T.CV) -> {K.parent_block(l,r) == S.block_of(SC.append(U32,S.cv_words(l),S.cv_words(r))) : T.Block}:
  match l r:
    case T.CV{l0,l1,l2,l3,l4,l5,l6,l7} T.CV{r0,r1,r2,r3,r4,r5,r6,r7}: {==}

def iv_correct() -> {K.iv() == S.cv_of(S.iv()) : T.CV}:
  {==}

def parent_out_correct(+l: T.CV, +r: T.CV) -> {K.parent_out(l,r) == S.parent(l,r) : T.Out}:
  %parent_block_correct(l,r) : {K.parent_out(l,r) == T.Out{S.cv_of(S.iv()),_,0,64,S.parent_flag()} : T.Out}
  {==}

def parent_cv_correct(+l: T.CV, +r: T.CV) -> {K.parent_cv(l,r) == S.cv(S.parent(l,r)) : T.CV}:
  Equal.trans(T.CV,
    C.compress(K.iv(),K.parent_block(l,r),0,64,4),
    S.compress(K.iv(),K.parent_block(l,r),0,64,4),
    S.compress(S.cv_of(S.iv()),S.block_of(SC.append(U32,S.cv_words(l),S.cv_words(r))),0,64,S.parent_flag()),
    P.compress_correct(K.iv(),K.parent_block(l,r),0,64,4),
    Equal.trans(T.CV,
      S.compress(K.iv(),K.parent_block(l,r),0,64,4),
      S.compress(S.cv_of(S.iv()),K.parent_block(l,r),0,64,4),
      S.compress(S.cv_of(S.iv()),S.block_of(SC.append(U32,S.cv_words(l),S.cv_words(r))),0,64,S.parent_flag()),
      Equal.cong(T.CV,T.CV,c => S.compress(c,K.parent_block(l,r),0,64,4),K.iv(),S.cv_of(S.iv()),iv_correct()),
      Equal.cong(T.Block,T.CV,b => S.compress(S.cv_of(S.iv()),b,0,64,S.parent_flag()),K.parent_block(l,r),S.block_of(SC.append(U32,S.cv_words(l),S.cv_words(r))),parent_block_correct(l,r))))

# ---- stacks ----

# h empty slots below y.
def emps(h: Nat, y: K.Stack) -> K.Stack:
  match h:
    case 0n: y
    case 1n+g: emps(g,K.SEmpty{y})

# The stack t with h empty slots below it (the empty stack stays empty).
def E(+h: Nat, t: K.Stack) -> K.Stack:
  match t:
    case K.SNil{}: K.SNil{}
    case K.SEmpty{r}: emps(h,K.SEmpty{r})
    case K.SFull{c,r}: emps(h,K.SFull{c,r})

def lift(t: K.Stack) -> K.Stack:
  match t:
    case K.SNil{}: K.SNil{}
    case K.SEmpty{r}: K.SEmpty{K.SEmpty{r}}
    case K.SFull{c,r}: K.SEmpty{K.SFull{c,r}}

def pushes(cs: List<&2,T.CV>, s: K.Stack) -> K.Stack:
  match cs:
    case Nil{}: s
    case Con{c,r}: pushes(r,K.push(s,c))

# Pushes the chaining values cs in order.
def push_all(s: K.Stack, cs: List<&2,T.CV>) -> K.Stack:
  pushes(cs,s)

def cvs(xs: List<&2,T.Out>) -> List<&2,T.CV>:
  match xs:
    case Nil{}: Nil{}
    case Con{x,r}: Con{K.out_cv(x),cvs(r)}

def E_succ(+g: Nat, +t: K.Stack) -> {E(1n+g,t) == E(g,lift(t)) : K.Stack}:
  match t:
    case K.SNil{}: {==}
    case K.SEmpty{+r}: {==}
    case K.SFull{+c,+r}: {==}

def E_zero(+t: K.Stack) -> {E(0n,t) == t : K.Stack}:
  match t:
    case K.SNil{}: {==}
    case K.SEmpty{+r}: {==}
    case K.SFull{+c,+r}: {==}

def push_lift(+t: K.Stack, +c: T.CV) -> {K.push(lift(t),c) == K.SFull{c,t} : K.Stack}:
  match t:
    case K.SNil{}: {==}
    case K.SEmpty{+r}: {==}
    case K.SFull{+d,+r}: {==}

def lift_push(+t: K.Stack, +c: T.CV) -> {lift(K.push(t,c)) == K.SEmpty{K.push(t,c)} : K.Stack}:
  match t:
    case K.SNil{}: {==}
    case K.SEmpty{+r}: {==}
    case K.SFull{+d,+r}: {==}

def finish_lift(+t: K.Stack, +o: T.Out) -> {K.finish(lift(t),o) == K.finish(t,o) : T.Out}:
  match t:
    case K.SNil{}: {==}
    case K.SEmpty{+r}: {==}
    case K.SFull{+d,+r}: {==}

def pushes_append(+xs: List<&2,T.CV>, +s: K.Stack, +ys: List<&2,T.CV>) -> {push_all(s,SC.append(T.CV,xs,ys)) == push_all(push_all(s,xs),ys) : K.Stack}:
  match xs:
    case Nil{}: {==}
    case Con{+c,+r}: pushes_append(r,K.push(s,c),ys)

def push_all_append(+s: K.Stack, +xs: List<&2,T.CV>, +ys: List<&2,T.CV>) -> {push_all(s,SC.append(T.CV,xs,ys)) == push_all(push_all(s,xs),ys) : K.Stack}:
  pushes_append(xs,s,ys)

def cvs_append(+xs: List<&2,T.Out>, +ys: List<&2,T.Out>) -> {cvs(SC.append(T.Out,xs,ys)) == SC.append(T.CV,cvs(xs),cvs(ys)) : List<&2,T.CV>}:
  match xs:
    case Nil{}: {==}
    case Con{+x,+r}: LS.cons_cong(T.CV,K.out_cv(x),cvs(SC.append(T.Out,r,ys)),SC.append(T.CV,cvs(r),cvs(ys)),cvs_append(r,ys))

# Pushing the chaining values of xs ++ ys.
def push_split(+s: K.Stack, +xs: List<&2,T.Out>, +ys: List<&2,T.Out>) -> {push_all(s,cvs(SC.append(T.Out,xs,ys))) == push_all(push_all(s,cvs(xs)),cvs(ys)) : K.Stack}:
  %Equal.sym(List<&2,T.CV>,cvs(SC.append(T.Out,xs,ys)),SC.append(T.CV,cvs(xs),cvs(ys)),cvs_append(xs,ys)) : {push_all(s,_) == push_all(push_all(s,cvs(xs)),cvs(ys)) : K.Stack}
  push_all_append(s,cvs(xs),cvs(ys))

# ---- the specification's tree ----

def tree_con(+g: Nat, +xs: List<&2,T.Out>, +ne: {S.is_nil(xs) == False{} : Bool}) -> {S.tree(1n+g,xs) == S.join(S.tree(g,SC.take(T.Out,xs,SC.pow2(g))),S.tree(g,SC.drop(T.Out,xs,SC.pow2(g))),S.is_nil(SC.drop(T.Out,xs,SC.pow2(g)))) : T.Out}:
  match xs:
    case Nil{}: Empty.absurd({S.tree(1n+g,Nil{}) == S.join(S.tree(g,SC.take(T.Out,Nil{},SC.pow2(g))),S.tree(g,SC.drop(T.Out,Nil{},SC.pow2(g))),S.is_nil(SC.drop(T.Out,Nil{},SC.pow2(g)))) : T.Out},L.true_false(ne))
    case Con{+x,+r}: {==}

def nil_is_empty(+xs: List<&2,T.Out>) -> {S.is_nil(xs) == LS.is_empty(T.Out,xs) : Bool}:
  match xs:
    case Nil{}: {==}
    case Con{+x,+r}: {==}

def snoc_ne(+xs: List<&2,T.Out>, +o: T.Out) -> {S.is_nil(SC.append(T.Out,xs,Con{o,Nil{}})) == False{} : Bool}:
  match xs:
    case Nil{}: {==}
    case Con{+x,+r}: {==}

def len_ne(+xs: List<&2,T.Out>, +n: Nat, +h: {SC.length(T.Out,xs) == 1n+n : Nat}) -> {S.is_nil(xs) == False{} : Bool}:
  match xs:
    case Nil{}: Empty.absurd({S.is_nil(Nil{}) == False{} : Bool},N.zero_succ(n,h))
    case Con{+x,+r}: {==}

# The drop is empty exactly when the list fits.
def drop_nil(+xs: List<&2,T.Out>, +k: Nat) -> {S.is_nil(SC.drop(T.Out,xs,k)) == Nat.is_le(SC.length(T.Out,xs),k) : Bool}:
  %Equal.sym(Bool,S.is_nil(SC.drop(T.Out,xs,k)),LS.is_empty(T.Out,SC.drop(T.Out,xs,k)),nil_is_empty(SC.drop(T.Out,xs,k))) : {_ == Nat.is_le(SC.length(T.Out,xs),k) : Bool}
  LS.empty_drop(T.Out,xs,k)

def join_false(+l: T.Out, +r: T.Out) -> {S.join(l,r,False{}) == S.parent(S.cv(l),S.cv(r)) : T.Out}:
  {==}

def zero_pow(+p: Nat, +hl: {0n == SC.pow2(p) : Nat}) -> {Nat.is_le(1n,0n) == True{} : Bool}:
  %Equal.sym(Nat,0n,SC.pow2(p),hl) : {Nat.is_le(1n,_) == True{} : Bool}
  N.pow2_pos(p)

def pow_ne(+xs: List<&2,T.Out>, +p: Nat, +hl: {SC.length(T.Out,xs) == SC.pow2(p) : Nat}) -> {S.is_nil(xs) == False{} : Bool}:
  match xs:
    case Nil{}: Empty.absurd({S.is_nil(Nil{}) == False{} : Bool},L.false_true(zero_pow(p,hl)))
    case Con{+x,+r}: {==}

# ---- complete subtrees ----

# The two halves of a list of 2^(g+1) outputs.
def half_len_take(+xs: List<&2,T.Out>, +g: Nat, +hl: {SC.length(T.Out,xs) == SC.pow2(1n+g) : Nat}) -> {SC.length(T.Out,SC.take(T.Out,xs,SC.pow2(g))) == SC.pow2(g) : Nat}:
  LS.length_take(T.Out,xs,SC.pow2(g),Equal.trans(Bool,Nat.is_le(SC.pow2(g),SC.length(T.Out,xs)),Nat.is_le(SC.pow2(g),Nat.double(SC.pow2(g))),True{},
    Equal.cong(Nat,Bool,n => Nat.is_le(SC.pow2(g),n),SC.length(T.Out,xs),Nat.double(SC.pow2(g)),hl),N.double_self_le(SC.pow2(g))))

def half_len_drop(+xs: List<&2,T.Out>, +g: Nat, +hl: {SC.length(T.Out,xs) == SC.pow2(1n+g) : Nat}) -> {SC.length(T.Out,SC.drop(T.Out,xs,SC.pow2(g))) == SC.pow2(g) : Nat}:
  %Equal.sym(Nat,SC.length(T.Out,SC.drop(T.Out,xs,SC.pow2(g))),Nat.sub(SC.length(T.Out,xs),SC.pow2(g)),LS.length_drop(T.Out,xs,SC.pow2(g))) : {_ == SC.pow2(g) : Nat}
  %Equal.sym(Nat,SC.length(T.Out,xs),SC.pow2(1n+g),hl) : {Nat.sub(_,SC.pow2(g)) == SC.pow2(g) : Nat}
  LS.sub_double(SC.pow2(g))

def half_not_nil(+xs: List<&2,T.Out>, +g: Nat, +hl: {SC.length(T.Out,xs) == SC.pow2(1n+g) : Nat}) -> {S.is_nil(SC.drop(T.Out,xs,SC.pow2(g))) == False{} : Bool}:
  %Equal.sym(Bool,S.is_nil(SC.drop(T.Out,xs,SC.pow2(g))),Nat.is_le(SC.length(T.Out,xs),SC.pow2(g)),drop_nil(xs,SC.pow2(g))) : {_ == False{} : Bool}
  %Equal.sym(Nat,SC.length(T.Out,xs),SC.pow2(1n+g),hl) : {Nat.is_le(_,SC.pow2(g)) == False{} : Bool}
  N.lt_not_le(SC.pow2(g),Nat.double(SC.pow2(g)),N.pow2_lt_succ(g))

def complete_step(+g: Nat, +xs: List<&2,T.Out>, +t: K.Stack,
    ne: {S.is_nil(xs) == False{} : Bool},
    nd: {S.is_nil(SC.drop(T.Out,xs,SC.pow2(g))) == False{} : Bool},
    ih1: {push_all(E(g,lift(t)),cvs(SC.take(T.Out,xs,SC.pow2(g)))) == E(g,K.push(lift(t),S.cv(S.tree(g,SC.take(T.Out,xs,SC.pow2(g)))))) : K.Stack},
    ih2: {push_all(E(g,K.SFull{S.cv(S.tree(g,SC.take(T.Out,xs,SC.pow2(g)))),t}),cvs(SC.drop(T.Out,xs,SC.pow2(g)))) == E(g,K.push(K.SFull{S.cv(S.tree(g,SC.take(T.Out,xs,SC.pow2(g)))),t},S.cv(S.tree(g,SC.drop(T.Out,xs,SC.pow2(g)))))) : K.Stack}
  ) -> {push_all(E(1n+g,t),cvs(xs)) == E(1n+g,K.push(t,S.cv(S.tree(1n+g,xs)))) : K.Stack}:
  %Equal.sym(T.Out,S.tree(1n+g,xs),S.join(S.tree(g,SC.take(T.Out,xs,SC.pow2(g))),S.tree(g,SC.drop(T.Out,xs,SC.pow2(g))),S.is_nil(SC.drop(T.Out,xs,SC.pow2(g)))),tree_con(g,xs,ne)) : {push_all(E(1n+g,t),cvs(xs)) == E(1n+g,K.push(t,S.cv(_))) : K.Stack}
  %Equal.sym(Bool,S.is_nil(SC.drop(T.Out,xs,SC.pow2(g))),False{},nd) : {push_all(E(1n+g,t),cvs(xs)) == E(1n+g,K.push(t,S.cv(S.join(S.tree(g,SC.take(T.Out,xs,SC.pow2(g))),S.tree(g,SC.drop(T.Out,xs,SC.pow2(g))),_)))) : K.Stack}
  %Equal.sym(T.Out,S.join(S.tree(g,SC.take(T.Out,xs,SC.pow2(g))),S.tree(g,SC.drop(T.Out,xs,SC.pow2(g))),False{}),S.parent(S.cv(S.tree(g,SC.take(T.Out,xs,SC.pow2(g)))),S.cv(S.tree(g,SC.drop(T.Out,xs,SC.pow2(g))))),join_false(S.tree(g,SC.take(T.Out,xs,SC.pow2(g))),S.tree(g,SC.drop(T.Out,xs,SC.pow2(g))))) : {push_all(E(1n+g,t),cvs(xs)) == E(1n+g,K.push(t,S.cv(_))) : K.Stack}
  %parent_cv_correct(S.cv(S.tree(g,SC.take(T.Out,xs,SC.pow2(g)))),S.cv(S.tree(g,SC.drop(T.Out,xs,SC.pow2(g))))) : {push_all(E(1n+g,t),cvs(xs)) == E(1n+g,K.push(t,_)) : K.Stack}
  %Equal.sym(K.Stack,E(1n+g,K.push(t,K.parent_cv(S.cv(S.tree(g,SC.take(T.Out,xs,SC.pow2(g)))),S.cv(S.tree(g,SC.drop(T.Out,xs,SC.pow2(g))))))),E(g,lift(K.push(t,K.parent_cv(S.cv(S.tree(g,SC.take(T.Out,xs,SC.pow2(g)))),S.cv(S.tree(g,SC.drop(T.Out,xs,SC.pow2(g)))))))),E_succ(g,K.push(t,K.parent_cv(S.cv(S.tree(g,SC.take(T.Out,xs,SC.pow2(g)))),S.cv(S.tree(g,SC.drop(T.Out,xs,SC.pow2(g)))))))) : {push_all(E(1n+g,t),cvs(xs)) == _ : K.Stack}
  %Equal.sym(K.Stack,lift(K.push(t,K.parent_cv(S.cv(S.tree(g,SC.take(T.Out,xs,SC.pow2(g)))),S.cv(S.tree(g,SC.drop(T.Out,xs,SC.pow2(g))))))),K.SEmpty{K.push(t,K.parent_cv(S.cv(S.tree(g,SC.take(T.Out,xs,SC.pow2(g)))),S.cv(S.tree(g,SC.drop(T.Out,xs,SC.pow2(g))))))},lift_push(t,K.parent_cv(S.cv(S.tree(g,SC.take(T.Out,xs,SC.pow2(g)))),S.cv(S.tree(g,SC.drop(T.Out,xs,SC.pow2(g))))))) : {push_all(E(1n+g,t),cvs(xs)) == E(g,_) : K.Stack}
  %LS.take_drop(T.Out,xs,SC.pow2(g)) : {push_all(E(1n+g,t),cvs(_)) == E(g,K.SEmpty{K.push(t,K.parent_cv(S.cv(S.tree(g,SC.take(T.Out,xs,SC.pow2(g)))),S.cv(S.tree(g,SC.drop(T.Out,xs,SC.pow2(g))))))}) : K.Stack}
  %Equal.sym(K.Stack,E(1n+g,t),E(g,lift(t)),E_succ(g,t)) : {push_all(_,cvs(SC.append(T.Out,SC.take(T.Out,xs,SC.pow2(g)),SC.drop(T.Out,xs,SC.pow2(g))))) == E(g,K.SEmpty{K.push(t,K.parent_cv(S.cv(S.tree(g,SC.take(T.Out,xs,SC.pow2(g)))),S.cv(S.tree(g,SC.drop(T.Out,xs,SC.pow2(g))))))}) : K.Stack}
  %Equal.sym(K.Stack,push_all(E(g,lift(t)),cvs(SC.append(T.Out,SC.take(T.Out,xs,SC.pow2(g)),SC.drop(T.Out,xs,SC.pow2(g))))),push_all(push_all(E(g,lift(t)),cvs(SC.take(T.Out,xs,SC.pow2(g)))),cvs(SC.drop(T.Out,xs,SC.pow2(g)))),push_split(E(g,lift(t)),SC.take(T.Out,xs,SC.pow2(g)),SC.drop(T.Out,xs,SC.pow2(g)))) : {_ == E(g,K.SEmpty{K.push(t,K.parent_cv(S.cv(S.tree(g,SC.take(T.Out,xs,SC.pow2(g)))),S.cv(S.tree(g,SC.drop(T.Out,xs,SC.pow2(g))))))}) : K.Stack}
  %Equal.sym(K.Stack,push_all(E(g,lift(t)),cvs(SC.take(T.Out,xs,SC.pow2(g)))),E(g,K.push(lift(t),S.cv(S.tree(g,SC.take(T.Out,xs,SC.pow2(g)))))),ih1) : {push_all(_,cvs(SC.drop(T.Out,xs,SC.pow2(g)))) == E(g,K.SEmpty{K.push(t,K.parent_cv(S.cv(S.tree(g,SC.take(T.Out,xs,SC.pow2(g)))),S.cv(S.tree(g,SC.drop(T.Out,xs,SC.pow2(g))))))}) : K.Stack}
  %Equal.sym(K.Stack,K.push(lift(t),S.cv(S.tree(g,SC.take(T.Out,xs,SC.pow2(g))))),K.SFull{S.cv(S.tree(g,SC.take(T.Out,xs,SC.pow2(g)))),t},push_lift(t,S.cv(S.tree(g,SC.take(T.Out,xs,SC.pow2(g)))))) : {push_all(E(g,_),cvs(SC.drop(T.Out,xs,SC.pow2(g)))) == E(g,K.SEmpty{K.push(t,K.parent_cv(S.cv(S.tree(g,SC.take(T.Out,xs,SC.pow2(g)))),S.cv(S.tree(g,SC.drop(T.Out,xs,SC.pow2(g))))))}) : K.Stack}
  ih2

def complete_zero(+xs: List<&2,T.Out>, +t: K.Stack, +hl: {SC.length(T.Out,xs) == 1n : Nat}) -> {push_all(E(0n,t),cvs(xs)) == E(0n,K.push(t,S.cv(S.tree(0n,xs)))) : K.Stack}:
  match xs:
    case Nil{}: Empty.absurd({push_all(E(0n,t),cvs(Nil{})) == E(0n,K.push(t,S.cv(S.tree(0n,Nil{})))) : K.Stack},N.zero_succ(0n,hl))
    case Con{+x,Nil{}}:
      %Equal.sym(K.Stack,E(0n,t),t,E_zero(t)) : {push_all(_,cvs(Con{x,Nil{}})) == E(0n,K.push(t,S.cv(S.tree(0n,Con{x,Nil{}})))) : K.Stack}
      %Equal.sym(K.Stack,E(0n,K.push(t,S.cv(x))),K.push(t,S.cv(x)),E_zero(K.push(t,S.cv(x)))) : {push_all(t,cvs(Con{x,Nil{}})) == _ : K.Stack}
      %out_cv_correct(x) : {push_all(t,cvs(Con{x,Nil{}})) == K.push(t,_) : K.Stack}
      {==}
    case Con{+x,Con{+y,+r}}: Empty.absurd({push_all(E(0n,t),cvs(Con{x,Con{y,r}})) == E(0n,K.push(t,S.cv(S.tree(0n,Con{x,Con{y,r}})))) : K.Stack},N.succ_zero(SC.length(T.Out,r),N.succ_inj(1n+SC.length(T.Out,r),0n,hl)))

# A stack with g empty low slots absorbs the chaining values of 2^g outputs
# as one complete subtree pushed at slot g.
def complete(+g: Nat, +xs: List<&2,T.Out>, +t: K.Stack, +hl: {SC.length(T.Out,xs) == SC.pow2(g) : Nat}) -> {push_all(E(g,t),cvs(xs)) == E(g,K.push(t,S.cv(S.tree(g,xs)))) : K.Stack}:
  match g:
    case 0n: complete_zero(xs,t,hl)
    case 1n+p:
      complete_step(p,xs,t,pow_ne(xs,1n+p,hl),half_not_nil(xs,p,hl),
        complete(p,SC.take(T.Out,xs,SC.pow2(p)),lift(t),half_len_take(xs,p,hl)),
        complete(p,SC.drop(T.Out,xs,SC.pow2(p)),K.SFull{S.cv(S.tree(p,SC.take(T.Out,xs,SC.pow2(p)))),t},half_len_drop(xs,p,hl)))

# ---- the pending output ----

def partial_zero(+fs: List<&2,T.Out>, +o: T.Out, +t: K.Stack, +hl: {Nat.is_lt(SC.length(T.Out,fs),1n) == True{} : Bool}) -> {K.finish(push_all(E(0n,t),cvs(fs)),o) == K.finish(t,S.tree(0n,SC.append(T.Out,fs,Con{o,Nil{}}))) : T.Out}:
  match fs:
    case Nil{}:
      %Equal.sym(K.Stack,E(0n,t),t,E_zero(t)) : {K.finish(_,o) == K.finish(t,S.tree(0n,Con{o,Nil{}})) : T.Out}
      {==}
    case Con{+f,+r}: Empty.absurd({K.finish(push_all(E(0n,t),cvs(Con{f,r})),o) == K.finish(t,S.tree(0n,SC.append(T.Out,Con{f,r},Con{o,Nil{}}))) : T.Out},N.lt_zero_absurd(SC.length(T.Out,r),hl))

# Fewer than 2^p outputs before o: the whole tree fits in height p.
def partial_fit(+p: Nat, +fs: List<&2,T.Out>, +o: T.Out, +t: K.Stack,
    +hb: {Nat.is_lt(SC.length(T.Out,fs),SC.pow2(p)) == True{} : Bool},
    rec: @f2: List<&2,T.Out> -> @t2: K.Stack -> @h2: {Nat.is_lt(SC.length(T.Out,f2),SC.pow2(p)) == True{} : Bool} -> {K.finish(push_all(E(p,t2),cvs(f2)),o) == K.finish(t2,S.tree(p,SC.append(T.Out,f2,Con{o,Nil{}}))) : T.Out}
  ) -> {K.finish(push_all(E(1n+p,t),cvs(fs)),o) == K.finish(t,S.tree(1n+p,SC.append(T.Out,fs,Con{o,Nil{}}))) : T.Out}:
  +xs = SC.append(T.Out,fs,Con{o,Nil{}})
  +k = SC.pow2(p)
  +hx = {%Equal.sym(Nat,SC.length(T.Out,xs),1n+SC.length(T.Out,fs),LS.length_snoc(T.Out,fs,o)) : {Nat.is_le(_,k) == True{} : Bool}
    N.lt_succ_le_succ(SC.length(T.Out,fs),k,hb) : {Nat.is_le(SC.length(T.Out,xs),k) == True{} : Bool}}
  %Equal.sym(T.Out,S.tree(1n+p,xs),S.join(S.tree(p,SC.take(T.Out,xs,k)),S.tree(p,SC.drop(T.Out,xs,k)),S.is_nil(SC.drop(T.Out,xs,k))),tree_con(p,xs,snoc_ne(fs,o))) : {K.finish(push_all(E(1n+p,t),cvs(fs)),o) == K.finish(t,_) : T.Out}
  %Equal.sym(List<&2,T.Out>,SC.take(T.Out,xs,k),xs,LS.take_all(T.Out,xs,k,hx)) : {K.finish(push_all(E(1n+p,t),cvs(fs)),o) == K.finish(t,S.join(S.tree(p,_),S.tree(p,SC.drop(T.Out,xs,k)),S.is_nil(SC.drop(T.Out,xs,k)))) : T.Out}
  %Equal.sym(List<&2,T.Out>,SC.drop(T.Out,xs,k),Nil{},LS.drop_all(T.Out,xs,k,hx)) : {K.finish(push_all(E(1n+p,t),cvs(fs)),o) == K.finish(t,S.join(S.tree(p,xs),S.tree(p,_),S.is_nil(_))) : T.Out}
  %Equal.sym(K.Stack,E(1n+p,t),E(p,lift(t)),E_succ(p,t)) : {K.finish(push_all(_,cvs(fs)),o) == K.finish(t,S.join(S.tree(p,xs),S.tree(p,Nil{}),S.is_nil(Nil{}))) : T.Out}
  Equal.trans(T.Out,K.finish(push_all(E(p,lift(t)),cvs(fs)),o),K.finish(lift(t),S.tree(p,xs)),K.finish(t,S.tree(p,xs)),
    rec(fs,lift(t),hb),finish_lift(t,S.tree(p,xs)))

# At least 2^p outputs before o: a complete left subtree of 2^p chunks, then
# the rest with o.
def partial_big(+p: Nat, +fs: List<&2,T.Out>, +o: T.Out, +t: K.Stack,
    +hl: {Nat.is_lt(SC.length(T.Out,fs),SC.pow2(1n+p)) == True{} : Bool},
    +hb: {Nat.is_lt(SC.length(T.Out,fs),SC.pow2(p)) == False{} : Bool},
    rec: @f2: List<&2,T.Out> -> @t2: K.Stack -> @h2: {Nat.is_lt(SC.length(T.Out,f2),SC.pow2(p)) == True{} : Bool} -> {K.finish(push_all(E(p,t2),cvs(f2)),o) == K.finish(t2,S.tree(p,SC.append(T.Out,f2,Con{o,Nil{}}))) : T.Out}
  ) -> {K.finish(push_all(E(1n+p,t),cvs(fs)),o) == K.finish(t,S.tree(1n+p,SC.append(T.Out,fs,Con{o,Nil{}}))) : T.Out}:
  +xs = SC.append(T.Out,fs,Con{o,Nil{}})
  +k = SC.pow2(p)
  +f1 = SC.take(T.Out,fs,k)
  +f2 = SC.drop(T.Out,fs,k)
  +c1 = S.cv(S.tree(p,f1))
  +t2 = S.tree(p,SC.append(T.Out,f2,Con{o,Nil{}}))
  +kl = N.not_lt_le(SC.length(T.Out,fs),k,hb)
  +h1 = LS.length_take(T.Out,fs,k,kl)
  +h2 = {%Equal.sym(Nat,SC.length(T.Out,f2),Nat.sub(SC.length(T.Out,fs),k),LS.length_drop(T.Out,fs,k)) : {Nat.is_lt(_,k) == True{} : Bool}
    N.sub_lt(SC.length(T.Out,fs),k,k,kl,{%LS.double_add(k) : {Nat.is_lt(SC.length(T.Out,fs),_) == True{} : Bool}
      hl : {Nat.is_lt(SC.length(T.Out,fs),Nat.add(k,k)) == True{} : Bool}}) : {Nat.is_lt(SC.length(T.Out,f2),k) == True{} : Bool}}
  %Equal.sym(T.Out,S.tree(1n+p,xs),S.join(S.tree(p,SC.take(T.Out,xs,k)),S.tree(p,SC.drop(T.Out,xs,k)),S.is_nil(SC.drop(T.Out,xs,k))),tree_con(p,xs,snoc_ne(fs,o))) : {K.finish(push_all(E(1n+p,t),cvs(fs)),o) == K.finish(t,_) : T.Out}
  %Equal.sym(List<&2,T.Out>,SC.take(T.Out,xs,k),f1,LS.take_append_left(T.Out,fs,Con{o,Nil{}},k,kl)) : {K.finish(push_all(E(1n+p,t),cvs(fs)),o) == K.finish(t,S.join(S.tree(p,_),S.tree(p,SC.drop(T.Out,xs,k)),S.is_nil(SC.drop(T.Out,xs,k)))) : T.Out}
  %Equal.sym(List<&2,T.Out>,SC.drop(T.Out,xs,k),SC.append(T.Out,f2,Con{o,Nil{}}),LS.drop_append_left(T.Out,fs,Con{o,Nil{}},k,kl)) : {K.finish(push_all(E(1n+p,t),cvs(fs)),o) == K.finish(t,S.join(S.tree(p,f1),S.tree(p,_),S.is_nil(_))) : T.Out}
  %Equal.sym(Bool,S.is_nil(SC.append(T.Out,f2,Con{o,Nil{}})),False{},snoc_ne(f2,o)) : {K.finish(push_all(E(1n+p,t),cvs(fs)),o) == K.finish(t,S.join(S.tree(p,f1),t2,_)) : T.Out}
  %Equal.sym(T.Out,S.join(S.tree(p,f1),t2,False{}),S.parent(c1,S.cv(t2)),join_false(S.tree(p,f1),t2)) : {K.finish(push_all(E(1n+p,t),cvs(fs)),o) == K.finish(t,_) : T.Out}
  %out_cv_correct(t2) : {K.finish(push_all(E(1n+p,t),cvs(fs)),o) == K.finish(t,S.parent(c1,_)) : T.Out}
  %parent_out_correct(c1,K.out_cv(t2)) : {K.finish(push_all(E(1n+p,t),cvs(fs)),o) == K.finish(t,_) : T.Out}
  %LS.take_drop(T.Out,fs,k) : {K.finish(push_all(E(1n+p,t),cvs(_)),o) == K.finish(t,K.parent_out(c1,K.out_cv(t2))) : T.Out}
  %Equal.sym(K.Stack,E(1n+p,t),E(p,lift(t)),E_succ(p,t)) : {K.finish(push_all(_,cvs(SC.append(T.Out,f1,f2))),o) == K.finish(t,K.parent_out(c1,K.out_cv(t2))) : T.Out}
  %Equal.sym(K.Stack,push_all(E(p,lift(t)),cvs(SC.append(T.Out,f1,f2))),push_all(push_all(E(p,lift(t)),cvs(f1)),cvs(f2)),push_split(E(p,lift(t)),f1,f2)) : {K.finish(_,o) == K.finish(t,K.parent_out(c1,K.out_cv(t2))) : T.Out}
  %Equal.sym(K.Stack,push_all(E(p,lift(t)),cvs(f1)),E(p,K.push(lift(t),c1)),complete(p,f1,lift(t),h1)) : {K.finish(push_all(_,cvs(f2)),o) == K.finish(t,K.parent_out(c1,K.out_cv(t2))) : T.Out}
  %Equal.sym(K.Stack,K.push(lift(t),c1),K.SFull{c1,t},push_lift(t,c1)) : {K.finish(push_all(E(p,_),cvs(f2)),o) == K.finish(t,K.parent_out(c1,K.out_cv(t2))) : T.Out}
  rec(f2,K.SFull{c1,t},h2)

def partial_split(+p: Nat, +fs: List<&2,T.Out>, +o: T.Out, +t: K.Stack,
    +hl: {Nat.is_lt(SC.length(T.Out,fs),SC.pow2(1n+p)) == True{} : Bool},
    +b: Bool, +hb: {Nat.is_lt(SC.length(T.Out,fs),SC.pow2(p)) == b : Bool},
    rec: @f2: List<&2,T.Out> -> @t2: K.Stack -> @h2: {Nat.is_lt(SC.length(T.Out,f2),SC.pow2(p)) == True{} : Bool} -> {K.finish(push_all(E(p,t2),cvs(f2)),o) == K.finish(t2,S.tree(p,SC.append(T.Out,f2,Con{o,Nil{}}))) : T.Out}
  ) -> {K.finish(push_all(E(1n+p,t),cvs(fs)),o) == K.finish(t,S.tree(1n+p,SC.append(T.Out,fs,Con{o,Nil{}}))) : T.Out}:
  match b:
    case True{}: partial_fit(p,fs,o,t,hb,rec)
    case False{}: partial_big(p,fs,o,t,hl,hb,rec)

# Fewer than 2^g chaining values pushed on a stack with g empty low slots,
# then folded into the pending output o: the specification's tree of height
# g over the outputs and o, folded into the rest of the stack.
def partial(+g: Nat, +fs: List<&2,T.Out>, +o: T.Out, +t: K.Stack, +hl: {Nat.is_lt(SC.length(T.Out,fs),SC.pow2(g)) == True{} : Bool}) -> {K.finish(push_all(E(g,t),cvs(fs)),o) == K.finish(t,S.tree(g,SC.append(T.Out,fs,Con{o,Nil{}}))) : T.Out}:
  match g:
    case 0n: partial_zero(fs,o,t,hl)
    case 1n+p:
      partial_split(p,fs,o,t,hl,Nat.is_lt(SC.length(T.Out,fs),SC.pow2(p)),{==},f2 => t2 => h2 => partial(p,f2,o,t2,h2))

# The whole message: the stack starts empty and the height is the chunk count.
def tree_stack(+fs: List<&2,T.Out>, +o: T.Out) -> {K.finish(push_all(K.SNil{},cvs(fs)),o) == S.tree(1n+SC.length(T.Out,fs),SC.append(T.Out,fs,Con{o,Nil{}})) : T.Out}:
  partial(1n+SC.length(T.Out,fs),fs,o,K.SNil{},LS.lt_pow2_succ(SC.length(T.Out,fs)))
