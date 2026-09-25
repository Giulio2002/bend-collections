import Base
import ../../../../src/crypto/blake/blake3/types.bend as T
import ../../../../src/crypto/blake/blake3/blake3.bend as K
import ../../../lib/nat.bend as N
import ../../../../spec/lib/common.bend as SC
import ../../../../spec/crypto/blake/blake3.bend as S
import ./array.bend as A
import ./lists.bend as LS
import ./chunk.bend as CH
import ./tree.bend as TR

# The implementation's chunk loop (read a chunk, push its chaining value)
# equals running the stack over the specification's list of chunk outputs,
# which in turn is the specification's tree over that list.

# The stack run over a list of outputs: every output but the last is pushed
# as a chaining value, the last one is pending.
def run2(rest: List<&2,T.Out>, s: K.Stack, x: T.Out) -> T.Out:
  match rest:
    case Nil{}: K.finish(s,x)
    case Con{y,r}: run2(r,K.push(s,K.out_cv(x)),y)

def run(s: K.Stack, xs: List<&2,T.Out>) -> T.Out:
  match xs:
    case Nil{}: S.first(Nil{})
    case Con{x,r}: run2(r,s,x)

def init2(rest: List<&2,T.Out>, +x: T.Out) -> List<&2,T.Out>:
  match rest:
    case Nil{}: Nil{}
    case Con{y,r}: Con{x,init2(r,y)}

def last2(rest: List<&2,T.Out>, +x: T.Out) -> T.Out:
  match rest:
    case Nil{}: x
    case Con{y,r}: last2(r,y)

def run2_split(+r: List<&2,T.Out>, +s: K.Stack, +x: T.Out) -> {run2(r,s,x) == K.finish(TR.push_all(s,TR.cvs(init2(r,x))),last2(r,x)) : T.Out}:
  match r:
    case Nil{}: {==}
    case Con{+y,+q}: run2_split(q,K.push(s,K.out_cv(x)),y)

def snoc2(+r: List<&2,T.Out>, +x: T.Out) -> {SC.append(T.Out,init2(r,x),Con{last2(r,x),Nil{}}) == Con{x,r} : List<&2,T.Out>}:
  match r:
    case Nil{}: {==}
    case Con{+y,+q}: LS.cons_cong(T.Out,x,SC.append(T.Out,init2(q,y),Con{last2(q,y),Nil{}}),Con{y,q},snoc2(q,y))

def len_init2(+r: List<&2,T.Out>, +x: T.Out) -> {SC.length(T.Out,init2(r,x)) == SC.length(T.Out,r) : Nat}:
  match r:
    case Nil{}: {==}
    case Con{+y,+q}: N.succ_cong(SC.length(T.Out,init2(q,y)),SC.length(T.Out,q),len_init2(q,y))

def run_tree_go(+x: T.Out, +r: List<&2,T.Out>) -> {K.finish(TR.push_all(K.SNil{},TR.cvs(init2(r,x))),last2(r,x)) == S.tree(1n+SC.length(T.Out,r),Con{x,r}) : T.Out}:
  %snoc2(r,x) : {K.finish(TR.push_all(K.SNil{},TR.cvs(init2(r,x))),last2(r,x)) == S.tree(1n+SC.length(T.Out,r),_) : T.Out}
  %len_init2(r,x) : {K.finish(TR.push_all(K.SNil{},TR.cvs(init2(r,x))),last2(r,x)) == S.tree(1n+_,SC.append(T.Out,init2(r,x),Con{last2(r,x),Nil{}})) : T.Out}
  TR.tree_stack(init2(r,x),last2(r,x))

# A nonempty list of outputs: the stack run is the tree of height |list|.
def run_tree(+x: T.Out, +r: List<&2,T.Out>) -> {run(K.SNil{},Con{x,r}) == S.tree(SC.length(T.Out,Con{x,r}),Con{x,r}) : T.Out}:
  Equal.trans(T.Out,run2(r,K.SNil{},x),K.finish(TR.push_all(K.SNil{},TR.cvs(init2(r,x))),last2(r,x)),S.tree(1n+SC.length(T.Out,r),Con{x,r}),
    run2_split(r,K.SNil{},x),
    run_tree_go(x,r))

# The specification's chunk list is never empty.
def run_chunks(+n: Nat, +t: U32, +index: U32, +len: Nat, q: Array<U32> & T.Out) -> {run(K.SNil{},S.chunks(n,t,index,len,q)) == S.tree(SC.length(T.Out,S.chunks(n,t,index,len,q)),S.chunks(n,t,index,len,q)) : T.Out}:
  match n q:
    case 0n Tuple{a,o}: run_tree(o,Nil{})
    case 1n+p Tuple{a,o}: run_tree(o,S.chunks(p,U32.inc(t),U32.add(index,256),len,S.chunk_at(p,U32.inc(t),U32.add(index,256),len,a)))

def base_run(+t: U32, +index: U32, +len: Nat, q: Array<U32> & T.Out, +s: K.Stack) -> {run(s,S.chunks(0n,t,index,len,q)) == K.finish(s,Pair.snd(Array<U32>,T.Out,q)) : T.Out}:
  (a,o) = q
  {==}

def run2_run(+p: Nat, +t: U32, +index: U32, +len: Nat, q: Array<U32> & T.Out, +s: K.Stack, +o: T.Out) -> {run2(S.chunks(p,t,index,len,q),s,o) == run(K.push(s,K.out_cv(o)),S.chunks(p,t,index,len,q)) : T.Out}:
  match p q:
    case 0n Tuple{a,y}: {==}
    case 1n+g Tuple{a,y}: {==}

# ---- the loop ----

def fuse_zero(+t: U32, +index: U32, +len: Nat, -a: Array<U32>, +s: K.Stack, view: Sigma<&2,&1,A.Tree,x => {a == A.thaw(x) : Array<U32>}>) -> {K.chunks(0n,t,index,len,(a,s)) == run(s,S.chunks(0n,t,index,len,S.chunk_at(0n,t,index,len,a))) : T.Out}:
  match view:
    case Tuple{+tree,pf}:
      %Equal.sym(Array<U32>,a,A.thaw(tree),pf) : {K.chunks(0n,t,index,len,(_,s)) == run(s,S.chunks(0n,t,index,len,S.chunk_at(0n,t,index,len,_))) : T.Out}
      Equal.trans(T.Out,
        K.finish(s,Pair.snd(Array<U32>,T.Out,K.last_chunk(A.thaw(tree),t,index,len))),
        K.finish(s,Pair.snd(Array<U32>,T.Out,S.chunk(A.thaw(tree),t,index,len))),
        run(s,S.chunks(0n,t,index,len,S.chunk(A.thaw(tree),t,index,len))),
        Equal.cong(Array<U32> & T.Out,T.Out,q => K.finish(s,Pair.snd(Array<U32>,T.Out,q)),K.last_chunk(A.thaw(tree),t,index,len),S.chunk(A.thaw(tree),t,index,len),CH.last_chunk_correct(A.thaw(tree),t,index,len)),
        Equal.sym(T.Out,run(s,S.chunks(0n,t,index,len,S.chunk(A.thaw(tree),t,index,len))),K.finish(s,Pair.snd(Array<U32>,T.Out,S.chunk(A.thaw(tree),t,index,len))),base_run(t,index,len,S.chunk(A.thaw(tree),t,index,len),s)))

def fuse_step2(+p: Nat, +t: U32, +index: U32, +len: Nat, +s: K.Stack, -a: Array<U32>, +o: T.Out,
    view: Sigma<&2,&1,A.Tree,x => {a == A.thaw(x) : Array<U32>}>,
    rec: @a2: Array<U32> -> @s2: K.Stack -> {K.chunks(p,U32.inc(t),U32.add(index,256),len,(a2,s2)) == run(s2,S.chunks(p,U32.inc(t),U32.add(index,256),len,S.chunk_at(p,U32.inc(t),U32.add(index,256),len,a2))) : T.Out}
  ) -> {K.chunks(p,U32.inc(t),U32.add(index,256),len,K.pushed(s,CH.outcv((a,o)))) == run(s,S.chunks(1n+p,t,index,len,(a,o))) : T.Out}:
  match view:
    case Tuple{+tree,pf}:
      %Equal.sym(Array<U32>,a,A.thaw(tree),pf) : {K.chunks(p,U32.inc(t),U32.add(index,256),len,K.pushed(s,CH.outcv((_,o)))) == run(s,S.chunks(1n+p,t,index,len,(_,o))) : T.Out}
      Equal.trans(T.Out,
        K.chunks(p,U32.inc(t),U32.add(index,256),len,(A.thaw(tree),K.push(s,S.cv(o)))),
        run(K.push(s,S.cv(o)),S.chunks(p,U32.inc(t),U32.add(index,256),len,S.chunk_at(p,U32.inc(t),U32.add(index,256),len,A.thaw(tree)))),
        run2(S.chunks(p,U32.inc(t),U32.add(index,256),len,S.chunk_at(p,U32.inc(t),U32.add(index,256),len,A.thaw(tree))),s,o),
        rec(A.thaw(tree),K.push(s,S.cv(o))),
        Equal.trans(T.Out,
          run(K.push(s,S.cv(o)),S.chunks(p,U32.inc(t),U32.add(index,256),len,S.chunk_at(p,U32.inc(t),U32.add(index,256),len,A.thaw(tree)))),
          run(K.push(s,K.out_cv(o)),S.chunks(p,U32.inc(t),U32.add(index,256),len,S.chunk_at(p,U32.inc(t),U32.add(index,256),len,A.thaw(tree)))),
          run2(S.chunks(p,U32.inc(t),U32.add(index,256),len,S.chunk_at(p,U32.inc(t),U32.add(index,256),len,A.thaw(tree))),s,o),
          Equal.cong(T.CV,T.Out,c => run(K.push(s,c),S.chunks(p,U32.inc(t),U32.add(index,256),len,S.chunk_at(p,U32.inc(t),U32.add(index,256),len,A.thaw(tree)))),
            S.cv(o),K.out_cv(o),Equal.sym(T.CV,K.out_cv(o),S.cv(o),TR.out_cv_correct(o))),
          Equal.sym(T.Out,run2(S.chunks(p,U32.inc(t),U32.add(index,256),len,S.chunk_at(p,U32.inc(t),U32.add(index,256),len,A.thaw(tree))),s,o),
            run(K.push(s,K.out_cv(o)),S.chunks(p,U32.inc(t),U32.add(index,256),len,S.chunk_at(p,U32.inc(t),U32.add(index,256),len,A.thaw(tree)))),
            run2_run(p,U32.inc(t),U32.add(index,256),len,S.chunk_at(p,U32.inc(t),U32.add(index,256),len,A.thaw(tree)),s,o))))

def fuse_step(+p: Nat, +t: U32, +index: U32, +len: Nat, +s: K.Stack, q: Array<U32> & T.Out,
    rec: @a2: Array<U32> -> @s2: K.Stack -> {K.chunks(p,U32.inc(t),U32.add(index,256),len,(a2,s2)) == run(s2,S.chunks(p,U32.inc(t),U32.add(index,256),len,S.chunk_at(p,U32.inc(t),U32.add(index,256),len,a2))) : T.Out}
  ) -> {K.chunks(p,U32.inc(t),U32.add(index,256),len,K.pushed(s,CH.outcv(q))) == run(s,S.chunks(1n+p,t,index,len,q)) : T.Out}:
  (a,o) = q
  fuse_step2(p,t,index,len,s,a,o,A.reify(a),rec)

def fuse_one(+p: Nat, +t: U32, +index: U32, +len: Nat, -a: Array<U32>, +s: K.Stack,
    view: Sigma<&2,&1,A.Tree,x => {a == A.thaw(x) : Array<U32>}>,
    rec: @a2: Array<U32> -> @s2: K.Stack -> {K.chunks(p,U32.inc(t),U32.add(index,256),len,(a2,s2)) == run(s2,S.chunks(p,U32.inc(t),U32.add(index,256),len,S.chunk_at(p,U32.inc(t),U32.add(index,256),len,a2))) : T.Out}
  ) -> {K.chunks(1n+p,t,index,len,(a,s)) == run(s,S.chunks(1n+p,t,index,len,S.chunk_at(1n+p,t,index,len,a))) : T.Out}:
  match view:
    case Tuple{+tree,pf}:
      %Equal.sym(Array<U32>,a,A.thaw(tree),pf) : {K.chunks(1n+p,t,index,len,(_,s)) == run(s,S.chunks(1n+p,t,index,len,S.chunk_at(1n+p,t,index,len,_))) : T.Out}
      Equal.trans(T.Out,
        K.chunks(p,U32.inc(t),U32.add(index,256),len,K.pushed(s,K.full_chunk(A.thaw(tree),t,index))),
        K.chunks(p,U32.inc(t),U32.add(index,256),len,K.pushed(s,CH.outcv(S.chunk(A.thaw(tree),t,index,1024n)))),
        run(s,S.chunks(1n+p,t,index,len,S.chunk(A.thaw(tree),t,index,1024n))),
        Equal.cong(Array<U32> & T.CV,T.Out,q => K.chunks(p,U32.inc(t),U32.add(index,256),len,K.pushed(s,q)),
          K.full_chunk(A.thaw(tree),t,index),CH.outcv(S.chunk(A.thaw(tree),t,index,1024n)),CH.full_chunk_correct(A.thaw(tree),t,index)),
        fuse_step(p,t,index,len,s,S.chunk(A.thaw(tree),t,index,1024n),rec))

law fuse:
  for +n: Nat
  for +t: U32
  for +index: U32
  for +len: Nat
  for a: Array<U32>
  for +s: K.Stack
  {K.chunks(n,t,index,len,(a,s)) == run(s,S.chunks(n,t,index,len,S.chunk_at(n,t,index,len,a))) : T.Out}

def fuse(n,t,index,len,a,s):
  match n:
    case 0n: fuse_zero(t,index,len,a,s,A.reify(a))
    case 1n+p: fuse_one(p,t,index,len,a,s,A.reify(a),a2 => s2 => fuse(p,U32.inc(t),U32.add(index,256),len,a2,s2))
