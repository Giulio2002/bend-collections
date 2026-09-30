import Base
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../../lib/list.bend as LL
import ../../lib/array.bend as AR
import ../../../spec/lib/common.bend as C
import ../../../spec/containers/stack.bend as S
import ../../../src/containers/stack.bend as D
import ../../../src/containers/dynamic_array.bend as DA
import ../../../src/containers/types/stack.bend as E
import ../dynamic_array/layout.bend as LY
import ../dynamic_array/state.bend as DST
import ../dynamic_array/steps.bend as DSP
import ../dynamic_array/growth.bend as GR
import ../dynamic_array/walk.bend as W

# The chunked stack (src/containers/stack.bend) refines the list model of
# spec/containers/stack.bend.
#
#   shadow   Sh: per chunk its depth d, length n, the mirror tree t of its
#            slot array, the stack's count c, and the chunks below
#   model    each chunk's elements, top first (the reverse of its occupied
#            slots, bottom first), then the chunks below
#   good     every chunk is a good dynamic-array shadow of limit cmax
#            (perfect tree, first n slots Some, the rest None), holds at
#            least one element, and c counts the whole stack
#
# A chunk is a dynamic-array shadow (DST.Sh{cmax, d, n, t}), so the slot
# lemmas of proofs/containers/dynamic_array (set, swap, get, growth) carry
# over unchanged.

type Sh<-T: Data> is Data:
  SSE{}
  SST{d: Nat, n: Nat, t: AR.Tree<Maybe<&2, T>>, c: Nat, r: Sh<T>}

def real(~T: Data, sh: Sh<T>) -> D.Stack<T>:
  match sh:
    case SSE{}:
      D.SE{}
    case SST{d, n, t, c, r}:
      D.ST{d, n, AR.thaw(Maybe<&2, T>, t), c, real(~T, r)}

def chunk(-T: Data, t: AR.Tree<Maybe<&2, T>>) -> List<&2, T>:
  C.reverse(T, LY.somes(T, AR.slots(Maybe<&2, T>, t)))

def model(-T: Data, sh: Sh<T>) -> List<&2, T>:
  match sh:
    case SSE{}:
      Nil{}
    case SST{d, n, t, c, r}:
      C.append(T, chunk(T, t), model(T, r))

def cgood(-T: Data, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>) -> Bool:
  DST.good(T, DST.Sh{D.cmax(), d, n, t})

def good(-T: Data, sh: Sh<T>) -> Bool:
  match sh:
    case SSE{}:
      True{}
    case SST{+d, +n, +t, +c, +r}:
      Bool.and(cgood(T, d, n, t), Bool.and(Nat.is_lt(0n, n), Bool.and(Nat.is_eq(c, Nat.add(n, C.length(T, model(T, r)))), good(T, r))))

# ---- projections of good ----


def g_chunk(-T: Data, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +c: Nat, +r: Sh<T>, +g: {good(T, SST{d, n, t, c, r}) == True{} : Bool}) -> {cgood(T, d, n, t) == True{} : Bool}:
  L.and_left(cgood(T, d, n, t), Bool.and(Nat.is_lt(0n, n), Bool.and(Nat.is_eq(c, Nat.add(n, C.length(T, model(T, r)))), good(T, r))), g)

def g_pos(-T: Data, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +c: Nat, +r: Sh<T>, +g: {good(T, SST{d, n, t, c, r}) == True{} : Bool}) -> {Nat.is_lt(0n, n) == True{} : Bool}:
  L.and_left(Nat.is_lt(0n, n), Bool.and(Nat.is_eq(c, Nat.add(n, C.length(T, model(T, r)))), good(T, r)), L.and_right(cgood(T, d, n, t), Bool.and(Nat.is_lt(0n, n), Bool.and(Nat.is_eq(c, Nat.add(n, C.length(T, model(T, r)))), good(T, r))), g))

def g_ct(-T: Data, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +c: Nat, +r: Sh<T>, +g: {good(T, SST{d, n, t, c, r}) == True{} : Bool}) -> {Bool.and(Nat.is_eq(c, Nat.add(n, C.length(T, model(T, r)))), good(T, r)) == True{} : Bool}:
  L.and_right(Nat.is_lt(0n, n), Bool.and(Nat.is_eq(c, Nat.add(n, C.length(T, model(T, r)))), good(T, r)), L.and_right(cgood(T, d, n, t), Bool.and(Nat.is_lt(0n, n), Bool.and(Nat.is_eq(c, Nat.add(n, C.length(T, model(T, r)))), good(T, r))), g))

def g_count(-T: Data, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +c: Nat, +r: Sh<T>, +g: {good(T, SST{d, n, t, c, r}) == True{} : Bool}) -> {c == Nat.add(n, C.length(T, model(T, r))) : Nat}:
  N.eq_from_is_eq(c, Nat.add(n, C.length(T, model(T, r))), L.and_left(Nat.is_eq(c, Nat.add(n, C.length(T, model(T, r)))), good(T, r), g_ct(T, d, n, t, c, r, g)))

def g_rest(-T: Data, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +c: Nat, +r: Sh<T>, +g: {good(T, SST{d, n, t, c, r}) == True{} : Bool}) -> {good(T, r) == True{} : Bool}:
  L.and_right(Nat.is_eq(c, Nat.add(n, C.length(T, model(T, r)))), good(T, r), g_ct(T, d, n, t, c, r, g))

def good_intro(-T: Data, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +c: Nat, +r: Sh<T>, +a: {cgood(T, d, n, t) == True{} : Bool}, +b: {Nat.is_lt(0n, n) == True{} : Bool}, +e: {c == Nat.add(n, C.length(T, model(T, r))) : Nat}, +f: {good(T, r) == True{} : Bool}) -> {good(T, SST{d, n, t, c, r}) == True{} : Bool}:
  %Equal.sym(Nat, c, Nat.add(n, C.length(T, model(T, r))), e) : {Bool.and(cgood(T, d, n, t), Bool.and(Nat.is_lt(0n, n), Bool.and(Nat.is_eq(_, Nat.add(n, C.length(T, model(T, r)))), good(T, r)))) == True{} : Bool}
  L.and_intro(cgood(T, d, n, t), Bool.and(Nat.is_lt(0n, n), Bool.and(Nat.is_eq(Nat.add(n, C.length(T, model(T, r))), Nat.add(n, C.length(T, model(T, r)))), good(T, r))), a,
    L.and_intro(Nat.is_lt(0n, n), Bool.and(Nat.is_eq(Nat.add(n, C.length(T, model(T, r))), Nat.add(n, C.length(T, model(T, r)))), good(T, r)), b,
      L.and_intro(Nat.is_eq(Nat.add(n, C.length(T, model(T, r))), Nat.add(n, C.length(T, model(T, r)))), good(T, r), N.is_eq_refl(Nat.add(n, C.length(T, model(T, r)))), f)))

# ---- list facts ----

def len_rev_append(-T: Data, +xs: List<&2, T>, +ys: List<&2, T>) -> {C.length(T, C.append(T, C.reverse(T, xs), ys)) == Nat.add(C.length(T, xs), C.length(T, ys)) : Nat}:
  %Equal.sym(Nat, C.length(T, C.append(T, C.reverse(T, xs), ys)), Nat.add(C.length(T, C.reverse(T, xs)), C.length(T, ys)), LL.length_append(T, C.reverse(T, xs), ys)) : {_ == Nat.add(C.length(T, xs), C.length(T, ys)) : Nat}
  Equal.cong(Nat, Nat, z => Nat.add(z, C.length(T, ys)), C.length(T, C.reverse(T, xs)), C.length(T, xs), LL.length_rev(T, xs))

# the stack's count is its model's length
def count_eq(-T: Data, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +c: Nat, +r: Sh<T>, +g: {good(T, SST{d, n, t, c, r}) == True{} : Bool}) -> {c == C.length(T, model(T, SST{d, n, t, c, r})) : Nat}:
  +xs = LY.somes(T, AR.slots(Maybe<&2, T>, t))
  +hl = LY.lay_len(T, AR.slots(Maybe<&2, T>, t), n, DST.g_lay(T, D.cmax(), d, n, t, g_chunk(T, d, n, t, c, r, g)))
  %Equal.sym(Nat, C.length(T, C.append(T, C.reverse(T, xs), model(T, r))), Nat.add(C.length(T, xs), C.length(T, model(T, r))), len_rev_append(T, xs, model(T, r))) : {c == _ : Nat}
  %Equal.sym(Nat, C.length(T, xs), n, hl) : {c == Nat.add(_, C.length(T, model(T, r))) : Nat}
  g_count(T, d, n, t, c, r, g)

# a list of length 1 + m is its first m elements and a last one
def SnocView(-T: Data, xs: List<&2, T>, m: Nat) -> Type:
  Sigma<&1, &1, List<&2, T>, ys => Sigma<&1, &1, T, y => {xs == C.snoc(T, ys, y) : List<&2, T>} & {C.length(T, ys) == m : Nat}>>

def sv_cons(-T: Data, +x: T, +k: Nat, +xs: List<&2, T>, v: SnocView(T, xs, k)) -> SnocView(T, Con{x, xs}, 1n+k):
  match v:
    case Tuple{ys, Tuple{y, Tuple{e, hl}}}:
      (Con{x, ys}, (y, (Equal.cong(List<&2, T>, List<&2, T>, z => Con{x, z}, xs, C.snoc(T, ys, y), e), Equal.cong(Nat, Nat, z => 1n+z, C.length(T, ys), k, hl))))

def snoc_view(-T: Data, +xs: List<&2, T>, +m: Nat, +h: {C.length(T, xs) == 1n+m : Nat}) -> SnocView(T, xs, m):
  match xs m:
    case Nil{} _:
      Empty.absurd(SnocView(T, Nil{}, m), N.zero_succ(m, h))
    case Con{+x, Nil{}} 0n:
      (Nil{}, (x, ({==}, {==})))
    case Con{+x, Nil{}} 1n+k:
      Empty.absurd(SnocView(T, Con{x, Nil{}}, 1n+k), N.zero_succ(k, N.succ_inj(0n, 1n+k, h)))
    case Con{+x, Con{+x2, +r}} 0n:
      Empty.absurd(SnocView(T, Con{x, Con{x2, r}}, 0n), N.zero_succ(C.length(T, r), Equal.sym(Nat, 1n+C.length(T, r), 0n, N.succ_inj(1n+C.length(T, r), 0n, h))))
    case Con{+x, Con{+x2, +r}} 1n+k:
      sv_cons(T, x, k, Con{x2, r}, snoc_view(T, Con{x2, r}, k, N.succ_inj(1n+C.length(T, r), 1n+k, h)))

def nth_snoc(-T: Data, +ys: List<&2, T>, +m: Nat, +y: T, +h: {C.length(T, ys) == m : Nat}) -> {C.nth(T, C.snoc(T, ys, y), m) == Some{y} : Maybe<&2, T>}:
  match ys m:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+k:
      Empty.absurd({C.nth(T, C.snoc(T, Nil{}, y), 1n+k) == Some{y} : Maybe<&2, T>}, N.zero_succ(k, h))
    case Con{+x, +r} 0n:
      Empty.absurd({C.nth(T, C.snoc(T, Con{x, r}, y), 0n) == Some{y} : Maybe<&2, T>}, N.zero_succ(C.length(T, r), Equal.sym(Nat, 1n+C.length(T, r), 0n, h)))
    case Con{+x, +r} 1n+k:
      nth_snoc(T, r, k, y, N.succ_inj(C.length(T, r), k, h))

# ---- spec steps on an arbitrary model ----

def spec_len(-T: Data, +xs: List<&2, T>) -> {S.step(T, xs, E.Length{}) == (xs, E.ONat{C.length(T, xs)}) : List<&2, T> & E.Obs<T>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      {==}

def spec_push(-T: Data, +xs: List<&2, T>, +v: T) -> {S.step(T, xs, E.Push{v}) == (Con{v, xs}, E.OUnit{}) : List<&2, T> & E.Obs<T>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      {==}

def spec_tl(-T: Data, +xs: List<&2, T>) -> {S.step(T, xs, E.ToList{}) == (xs, E.OList{xs}) : List<&2, T> & E.Obs<T>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      {==}

# ---- one step ----

def StepOK(~T: Data, sh: Sh<T>, op: E.Op<T>) -> Type:
  Sigma<&1, &1, Sh<T>, sh2 => Sigma<&1, &1, E.Obs<T>, o => {D.step(~T, real(~T, sh), op) == (real(~T, sh2), o) : D.Stack<T> & E.Obs<T>} & ({good(T, sh2) == True{} : Bool} & {(model(T, sh2), o) == S.step(T, model(T, sh), op) : List<&2, T> & E.Obs<T>})>>


def length_ok(~T: Data, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +c: Nat, +r: Sh<T>, +g: {good(T, SST{d, n, t, c, r}) == True{} : Bool}) -> StepOK(~T, SST{d, n, t, c, r}, E.Length{}):
  (SST{d, n, t, c, r}, (E.ONat{c}, ({==}, (g,
    %Equal.sym(List<&2, T> & E.Obs<T>, S.step(T, model(T, SST{d, n, t, c, r}), E.Length{}), (model(T, SST{d, n, t, c, r}), E.ONat{C.length(T, model(T, SST{d, n, t, c, r}))}), spec_len(T, model(T, SST{d, n, t, c, r}))) : {(model(T, SST{d, n, t, c, r}), E.ONat{c}) == _ : List<&2, T> & E.Obs<T>}
    Equal.cong(Nat, List<&2, T> & E.Obs<T>, z => (model(T, SST{d, n, t, c, r}), E.ONat{z}), c, C.length(T, model(T, SST{d, n, t, c, r})), count_eq(T, d, n, t, c, r, g))))))


# ---- push ----

def push_empty(~T: Data, +v: T) -> StepOK(~T, SSE{}, E.Push{v}):
  (SST{0n, 1n, AR.TLeaf{Some{v}}, 1n, SSE{}}, (E.OUnit{}, ({==}, ({==}, {==}))))

def push_case(~T: Data, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +c: Nat, +r: Sh<T>, +g: {good(T, SST{d, n, t, c, r}) == True{} : Bool}, +v: T, +room: Bool, +er: {Nat.is_lt(n, DA.pow2(d)) == room : Bool}, +grow: Bool, +eg: {Nat.is_lt(d, D.cmax()) == grow : Bool}) -> StepOK(~T, SST{d, n, t, c, r}, E.Push{v}):
  match room grow:
    case True{} _:
      +hn = L.subst(Nat, k => {Nat.is_lt(n, k) == True{} : Bool}, DA.pow2(d), C.pow2(d), DST.pow2_src(d), er)
      +t2 = AR.upd(Maybe<&2, T>, d, t, n, Some{v})
      (SST{d, 1n+n, t2, 1n+c, r}, (E.OUnit{}, (
        %Equal.sym(Bool, Nat.is_lt(n, DA.pow2(d)), True{}, er) : {(D.push_room(~T, d, n, AR.thaw(Maybe<&2, T>, t), c, real(~T, r), v, _), E.OUnit{}) == (real(~T, SST{d, 1n+n, t2, 1n+c, r}), E.OUnit{}) : D.Stack<T> & E.Obs<T>}
        %Equal.sym(Array<Maybe<&2, T>>, Array.set(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, t), U32.from_nat(n), Some{v}), AR.thaw(Maybe<&2, T>, t2), DSP.pi_arr(T, D.cmax(), d, n, t, v, g_chunk(T, d, n, t, c, r, g), hn)) : {(D.ST{d, 1n+n, _, 1n+c, real(~T, r)}, E.OUnit{}) == (real(~T, SST{d, 1n+n, t2, 1n+c, r}), E.OUnit{}) : D.Stack<T> & E.Obs<T>}
        {==},
        (good_intro(T, d, 1n+n, t2, 1n+c, r, DSP.pi_good(T, D.cmax(), d, n, t, v, g_chunk(T, d, n, t, c, r, g), hn), {==}, Equal.cong(Nat, Nat, z => 1n+z, c, Nat.add(n, C.length(T, model(T, r))), g_count(T, d, n, t, c, r, g)), g_rest(T, d, n, t, c, r, g)),
         %Equal.sym(List<&2, T> & E.Obs<T>, S.step(T, model(T, SST{d, n, t, c, r}), E.Push{v}), (Con{v, model(T, SST{d, n, t, c, r})}, E.OUnit{}), spec_push(T, model(T, SST{d, n, t, c, r}), v)) : {(model(T, SST{d, 1n+n, t2, 1n+c, r}), E.OUnit{}) == _ : List<&2, T> & E.Obs<T>}
         %Equal.sym(List<&2, T>, LY.somes(T, AR.slots(Maybe<&2, T>, t2)), C.snoc(T, LY.somes(T, AR.slots(Maybe<&2, T>, t)), v), DSP.pi_model(T, D.cmax(), d, n, t, v, g_chunk(T, d, n, t, c, r, g), hn)) : {(C.append(T, C.reverse(T, _), model(T, r)), E.OUnit{}) == (Con{v, model(T, SST{d, n, t, c, r})}, E.OUnit{}) : List<&2, T> & E.Obs<T>}
         %Equal.sym(List<&2, T>, C.reverse(T, C.snoc(T, LY.somes(T, AR.slots(Maybe<&2, T>, t)), v)), Con{v, C.reverse(T, LY.somes(T, AR.slots(Maybe<&2, T>, t)))}, LL.rev_snoc(T, LY.somes(T, AR.slots(Maybe<&2, T>, t)), v)) : {(C.append(T, _, model(T, r)), E.OUnit{}) == (Con{v, model(T, SST{d, n, t, c, r})}, E.OUnit{}) : List<&2, T> & E.Obs<T>}
         {==}))))
    case False{} True{}:
      +t1 = {AR.TNode{t, AR.trep(Maybe<&2, T>, d, None{})} : AR.Tree<Maybe<&2, T>>}
      +g1 = GR.grow_good(T, D.cmax(), d, n, t, g_chunk(T, d, n, t, c, r, g), eg)
      +hn = N.le_lt_trans(n, C.pow2(d), C.pow2(1n+d), DSP.n_le_cap(T, D.cmax(), d, n, t, g_chunk(T, d, n, t, c, r, g)), N.pow2_lt_succ(d))
      +t2 = AR.upd(Maybe<&2, T>, 1n+d, t1, n, Some{v})
      (SST{1n+d, 1n+n, t2, 1n+c, r}, (E.OUnit{}, (
        %Equal.sym(Bool, Nat.is_lt(n, DA.pow2(d)), False{}, er) : {(D.push_room(~T, d, n, AR.thaw(Maybe<&2, T>, t), c, real(~T, r), v, _), E.OUnit{}) == (real(~T, SST{1n+d, 1n+n, t2, 1n+c, r}), E.OUnit{}) : D.Stack<T> & E.Obs<T>}
        %Equal.sym(Bool, Nat.is_lt(d, D.cmax()), True{}, eg) : {(D.push_full(~T, d, n, AR.thaw(Maybe<&2, T>, t), c, real(~T, r), v, _), E.OUnit{}) == (real(~T, SST{1n+d, 1n+n, t2, 1n+c, r}), E.OUnit{}) : D.Stack<T> & E.Obs<T>}
        %Equal.sym(Array<Maybe<&2, T>>, DA.grown(T, d, AR.thaw(Maybe<&2, T>, t)), AR.thaw(Maybe<&2, T>, t1), DST.grown_eq(T, d, t)) : {(D.ST{1n+d, 1n+n, Array.set(Maybe<&2, T>, _, U32.from_nat(n), Some{v}), 1n+c, real(~T, r)}, E.OUnit{}) == (real(~T, SST{1n+d, 1n+n, t2, 1n+c, r}), E.OUnit{}) : D.Stack<T> & E.Obs<T>}
        %Equal.sym(Array<Maybe<&2, T>>, Array.set(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, t1), U32.from_nat(n), Some{v}), AR.thaw(Maybe<&2, T>, t2), DSP.pi_arr(T, D.cmax(), 1n+d, n, t1, v, g1, hn)) : {(D.ST{1n+d, 1n+n, _, 1n+c, real(~T, r)}, E.OUnit{}) == (real(~T, SST{1n+d, 1n+n, t2, 1n+c, r}), E.OUnit{}) : D.Stack<T> & E.Obs<T>}
        {==},
        (good_intro(T, 1n+d, 1n+n, t2, 1n+c, r, DSP.pi_good(T, D.cmax(), 1n+d, n, t1, v, g1, hn), {==}, Equal.cong(Nat, Nat, z => 1n+z, c, Nat.add(n, C.length(T, model(T, r))), g_count(T, d, n, t, c, r, g)), g_rest(T, d, n, t, c, r, g)),
         %Equal.sym(List<&2, T> & E.Obs<T>, S.step(T, model(T, SST{d, n, t, c, r}), E.Push{v}), (Con{v, model(T, SST{d, n, t, c, r})}, E.OUnit{}), spec_push(T, model(T, SST{d, n, t, c, r}), v)) : {(model(T, SST{1n+d, 1n+n, t2, 1n+c, r}), E.OUnit{}) == _ : List<&2, T> & E.Obs<T>}
         %Equal.sym(List<&2, T>, LY.somes(T, AR.slots(Maybe<&2, T>, t2)), C.snoc(T, LY.somes(T, AR.slots(Maybe<&2, T>, t1)), v), DSP.pi_model(T, D.cmax(), 1n+d, n, t1, v, g1, hn)) : {(C.append(T, C.reverse(T, _), model(T, r)), E.OUnit{}) == (Con{v, model(T, SST{d, n, t, c, r})}, E.OUnit{}) : List<&2, T> & E.Obs<T>}
         %Equal.sym(List<&2, T>, LY.somes(T, AR.slots(Maybe<&2, T>, t1)), LY.somes(T, AR.slots(Maybe<&2, T>, t)), GR.grow_model(T, d, t)) : {(C.append(T, C.reverse(T, C.snoc(T, _, v)), model(T, r)), E.OUnit{}) == (Con{v, model(T, SST{d, n, t, c, r})}, E.OUnit{}) : List<&2, T> & E.Obs<T>}
         %Equal.sym(List<&2, T>, C.reverse(T, C.snoc(T, LY.somes(T, AR.slots(Maybe<&2, T>, t)), v)), Con{v, C.reverse(T, LY.somes(T, AR.slots(Maybe<&2, T>, t)))}, LL.rev_snoc(T, LY.somes(T, AR.slots(Maybe<&2, T>, t)), v)) : {(C.append(T, _, model(T, r)), E.OUnit{}) == (Con{v, model(T, SST{d, n, t, c, r})}, E.OUnit{}) : List<&2, T> & E.Obs<T>}
         {==}))))
    case False{} False{}:
      (SST{0n, 1n, AR.TLeaf{Some{v}}, 1n+c, SST{d, n, t, c, r}}, (E.OUnit{}, (
        %Equal.sym(Bool, Nat.is_lt(n, DA.pow2(d)), False{}, er) : {(D.push_room(~T, d, n, AR.thaw(Maybe<&2, T>, t), c, real(~T, r), v, _), E.OUnit{}) == (real(~T, SST{0n, 1n, AR.TLeaf{Some{v}}, 1n+c, SST{d, n, t, c, r}}), E.OUnit{}) : D.Stack<T> & E.Obs<T>}
        %Equal.sym(Bool, Nat.is_lt(d, D.cmax()), False{}, eg) : {(D.push_full(~T, d, n, AR.thaw(Maybe<&2, T>, t), c, real(~T, r), v, _), E.OUnit{}) == (real(~T, SST{0n, 1n, AR.TLeaf{Some{v}}, 1n+c, SST{d, n, t, c, r}}), E.OUnit{}) : D.Stack<T> & E.Obs<T>}
        {==},
        (good_intro(T, 0n, 1n, AR.TLeaf{Some{v}}, 1n+c, SST{d, n, t, c, r}, {==}, {==}, Equal.cong(Nat, Nat, z => 1n+z, c, C.length(T, model(T, SST{d, n, t, c, r})), count_eq(T, d, n, t, c, r, g)), g),
         %Equal.sym(List<&2, T> & E.Obs<T>, S.step(T, model(T, SST{d, n, t, c, r}), E.Push{v}), (Con{v, model(T, SST{d, n, t, c, r})}, E.OUnit{}), spec_push(T, model(T, SST{d, n, t, c, r}), v)) : {(model(T, SST{0n, 1n, AR.TLeaf{Some{v}}, 1n+c, SST{d, n, t, c, r}}), E.OUnit{}) == _ : List<&2, T> & E.Obs<T>}
         {==}))))

def push_ok(~T: Data, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +c: Nat, +r: Sh<T>, +g: {good(T, SST{d, n, t, c, r}) == True{} : Bool}, +v: T) -> StepOK(~T, SST{d, n, t, c, r}, E.Push{v}):
  push_case(~T, d, n, t, c, r, g, v, Nat.is_lt(n, DA.pow2(d)), {==}, Nat.is_lt(d, D.cmax()), {==})

# ---- pop and peek: the top slot holds the model's head ----


def pos_absurd(~T: Data, +d: Nat, +t: AR.Tree<Maybe<&2, T>>, +c: Nat, +r: Sh<T>, +g: {good(T, SST{d, 0n, t, c, r}) == True{} : Bool}, +op: E.Op<T>) -> StepOK(~T, SST{d, 0n, t, c, r}, op):
  Empty.absurd(StepOK(~T, SST{d, 0n, t, c, r}, op), L.false_true(g_pos(T, d, 0n, t, c, r, g)))

# the model with its top element split off
def top_model(-T: Data, +xs: List<&2, T>, +ys: List<&2, T>, +y: T, +rest: List<&2, T>, +e: {xs == C.snoc(T, ys, y) : List<&2, T>}) -> {C.append(T, C.reverse(T, xs), rest) == Con{y, C.append(T, C.reverse(T, ys), rest)} : List<&2, T>}:
  %Equal.sym(List<&2, T>, xs, C.snoc(T, ys, y), e) : {C.append(T, C.reverse(T, _), rest) == Con{y, C.append(T, C.reverse(T, ys), rest)} : List<&2, T>}
  %Equal.sym(List<&2, T>, C.reverse(T, C.snoc(T, ys, y)), Con{y, C.reverse(T, ys)}, LL.rev_snoc(T, ys, y)) : {C.append(T, _, rest) == Con{y, C.append(T, C.reverse(T, ys), rest)} : List<&2, T>}
  {==}

def top_slot(-T: Data, +xs: List<&2, T>, +ys: List<&2, T>, +y: T, +m: Nat, +e: {xs == C.snoc(T, ys, y) : List<&2, T>}, +hl: {C.length(T, ys) == m : Nat}) -> {C.nth(T, xs, m) == Some{y} : Maybe<&2, T>}:
  Equal.trans(Maybe<&2, T>, C.nth(T, xs, m), C.nth(T, C.snoc(T, ys, y), m), Some{y}, Equal.cong(List<&2, T>, Maybe<&2, T>, z => C.nth(T, z, m), xs, C.snoc(T, ys, y), e), nth_snoc(T, ys, m, y, hl))

def pop_top(~T: Data, +d: Nat, +m: Nat, +t: AR.Tree<Maybe<&2, T>>, +c: Nat, +r: Sh<T>, +g: {good(T, SST{d, 1n+m, t, c, r}) == True{} : Bool}, +ys: List<&2, T>, +y: T, +e: {LY.somes(T, AR.slots(Maybe<&2, T>, t)) == C.snoc(T, ys, y) : List<&2, T>}, +hl: {C.length(T, ys) == m : Nat}) -> StepOK(~T, SST{d, 1n+m, t, c, r}, E.Pop{}):
  match m:
    case 0n:
      +hlay = DST.g_lay(T, D.cmax(), d, 1n, t, g_chunk(T, d, 1n, t, c, r, g))
      +hm = N.lt_succ(0n)
      +hi = N.lt_le_trans(0n, 1n, C.pow2(d), hm, DSP.n_le_cap(T, D.cmax(), d, 1n, t, g_chunk(T, d, 1n, t, c, r, g)))
      +t2 = AR.upd(Maybe<&2, T>, d, t, 0n, None{})
      +hs = DSP.upd_slots(T, D.cmax(), d, 1n, t, 0n, None{}, g_chunk(T, d, 1n, t, c, r, g), hi)
      +hx = top_slot(T, LY.somes(T, AR.slots(Maybe<&2, T>, t)), ys, y, 0n, e, hl)
      +em = top_model(T, LY.somes(T, AR.slots(Maybe<&2, T>, t)), ys, y, model(T, r), e)
      (r, (E.OItem{Done{y}}, (
        %Equal.sym(Array<Maybe<&2, T>> & Maybe<&2, T>, Array.swap(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, t), U32.from_nat(0n), None{}), (AR.thaw(Maybe<&2, T>, t2), C.nth(T, LY.somes(T, AR.slots(Maybe<&2, T>, t)), 0n)), DSP.swap_arr(T, D.cmax(), d, 1n, t, 0n, None{}, C.nth(T, LY.somes(T, AR.slots(Maybe<&2, T>, t)), 0n), g_chunk(T, d, 1n, t, c, r, g), hi, LY.lay_nth(T, AR.slots(Maybe<&2, T>, t), 1n, 0n, hlay, hm))) : {D.obs_item(~T, D.pop_fin(~T, d, 0n, c, real(~T, r), _)) == (real(~T, r), E.OItem{Done{y}}) : D.Stack<T> & E.Obs<T>}
        %Equal.sym(Maybe<&2, T>, C.nth(T, LY.somes(T, AR.slots(Maybe<&2, T>, t)), 0n), Some{y}, hx) : {D.obs_item(~T, D.pop_fin(~T, d, 0n, c, real(~T, r), (AR.thaw(Maybe<&2, T>, t2), _))) == (real(~T, r), E.OItem{Done{y}}) : D.Stack<T> & E.Obs<T>}
        {==},
        (g_rest(T, d, 1n, t, c, r, g),
         %Equal.sym(List<&2, T>, C.append(T, C.reverse(T, LY.somes(T, AR.slots(Maybe<&2, T>, t))), model(T, r)), Con{y, C.append(T, C.reverse(T, ys), model(T, r))}, em) : {(model(T, r), E.OItem{Done{y}}) == S.step(T, _, E.Pop{}) : List<&2, T> & E.Obs<T>}
         %Equal.sym(List<&2, T>, ys, Nil{}, LL.length_zero_nil(T, ys, hl)) : {(model(T, r), E.OItem{Done{y}}) == S.step(T, Con{y, C.append(T, C.reverse(T, _), model(T, r))}, E.Pop{}) : List<&2, T> & E.Obs<T>}
         {==}))))
    case 1n+ +k:
      +hlay = DST.g_lay(T, D.cmax(), d, 2n+k, t, g_chunk(T, d, 2n+k, t, c, r, g))
      +hm = N.lt_succ(1n+k)
      +hi = N.lt_le_trans(1n+k, 2n+k, C.pow2(d), hm, DSP.n_le_cap(T, D.cmax(), d, 2n+k, t, g_chunk(T, d, 2n+k, t, c, r, g)))
      +t2 = AR.upd(Maybe<&2, T>, d, t, 1n+k, None{})
      +hs = DSP.upd_slots(T, D.cmax(), d, 2n+k, t, 1n+k, None{}, g_chunk(T, d, 2n+k, t, c, r, g), hi)
      +hx = top_slot(T, LY.somes(T, AR.slots(Maybe<&2, T>, t)), ys, y, 1n+k, e, hl)
      +em = top_model(T, LY.somes(T, AR.slots(Maybe<&2, T>, t)), ys, y, model(T, r), e)
      (SST{d, 1n+k, t2, Nat.sub(c, 1n), r}, (E.OItem{Done{y}}, (
        %Equal.sym(Array<Maybe<&2, T>> & Maybe<&2, T>, Array.swap(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, t), U32.from_nat(1n+k), None{}), (AR.thaw(Maybe<&2, T>, t2), C.nth(T, LY.somes(T, AR.slots(Maybe<&2, T>, t)), 1n+k)), DSP.swap_arr(T, D.cmax(), d, 2n+k, t, 1n+k, None{}, C.nth(T, LY.somes(T, AR.slots(Maybe<&2, T>, t)), 1n+k), g_chunk(T, d, 2n+k, t, c, r, g), hi, LY.lay_nth(T, AR.slots(Maybe<&2, T>, t), 2n+k, 1n+k, hlay, hm))) : {D.obs_item(~T, D.pop_fin(~T, d, 1n+k, c, real(~T, r), _)) == (real(~T, SST{d, 1n+k, t2, Nat.sub(c, 1n), r}), E.OItem{Done{y}}) : D.Stack<T> & E.Obs<T>}
        %Equal.sym(Maybe<&2, T>, C.nth(T, LY.somes(T, AR.slots(Maybe<&2, T>, t)), 1n+k), Some{y}, hx) : {D.obs_item(~T, D.pop_fin(~T, d, 1n+k, c, real(~T, r), (AR.thaw(Maybe<&2, T>, t2), _))) == (real(~T, SST{d, 1n+k, t2, Nat.sub(c, 1n), r}), E.OItem{Done{y}}) : D.Stack<T> & E.Obs<T>}
        {==},
        (good_intro(T, d, 1n+k, t2, Nat.sub(c, 1n), r,
           DST.good_intro(T, D.cmax(), d, 1n+k, t2, DST.g_limit(T, D.cmax(), d, 2n+k, t, g_chunk(T, d, 2n+k, t, c, r, g)), DST.g_depth(T, D.cmax(), d, 2n+k, t, g_chunk(T, d, 2n+k, t, c, r, g)), AR.upd_perfect(Maybe<&2, T>, d, t, 1n+k, None{}, DST.g_perfect(T, D.cmax(), d, 2n+k, t, g_chunk(T, d, 2n+k, t, c, r, g))),
             L.subst(List<&2, Maybe<&2, T>>, zs => {LY.lay(T, zs, 1n+k) == True{} : Bool}, C.update(Maybe<&2, T>, AR.slots(Maybe<&2, T>, t), 1n+k, None{}), AR.slots(Maybe<&2, T>, t2), Equal.sym(List<&2, Maybe<&2, T>>, AR.slots(Maybe<&2, T>, t2), C.update(Maybe<&2, T>, AR.slots(Maybe<&2, T>, t), 1n+k, None{}), hs), LY.lay_pop(T, AR.slots(Maybe<&2, T>, t), 1n+k, hlay))),
           {==},
           %Equal.sym(Nat, c, Nat.add(2n+k, C.length(T, model(T, r))), g_count(T, d, 2n+k, t, c, r, g)) : {Nat.sub(_, 1n) == Nat.add(1n+k, C.length(T, model(T, r))) : Nat}
           {==},
           g_rest(T, d, 2n+k, t, c, r, g)),
         %Equal.sym(List<&2, Maybe<&2, T>>, AR.slots(Maybe<&2, T>, t2), C.update(Maybe<&2, T>, AR.slots(Maybe<&2, T>, t), 1n+k, None{}), hs) : {(C.append(T, C.reverse(T, LY.somes(T, _)), model(T, r)), E.OItem{Done{y}}) == S.step(T, model(T, SST{d, 2n+k, t, c, r}), E.Pop{}) : List<&2, T> & E.Obs<T>}
         %Equal.sym(List<&2, T>, LY.somes(T, C.update(Maybe<&2, T>, AR.slots(Maybe<&2, T>, t), 1n+k, None{})), C.init(T, LY.somes(T, AR.slots(Maybe<&2, T>, t))), LY.somes_pop(T, AR.slots(Maybe<&2, T>, t), 1n+k, hlay)) : {(C.append(T, C.reverse(T, _), model(T, r)), E.OItem{Done{y}}) == S.step(T, model(T, SST{d, 2n+k, t, c, r}), E.Pop{}) : List<&2, T> & E.Obs<T>}
         %Equal.sym(List<&2, T>, LY.somes(T, AR.slots(Maybe<&2, T>, t)), C.snoc(T, ys, y), e) : {(C.append(T, C.reverse(T, C.init(T, _)), model(T, r)), E.OItem{Done{y}}) == S.step(T, model(T, SST{d, 2n+k, t, c, r}), E.Pop{}) : List<&2, T> & E.Obs<T>}
         %Equal.sym(List<&2, T>, C.init(T, C.snoc(T, ys, y)), ys, LL.init_snoc(T, ys, y)) : {(C.append(T, C.reverse(T, _), model(T, r)), E.OItem{Done{y}}) == S.step(T, model(T, SST{d, 2n+k, t, c, r}), E.Pop{}) : List<&2, T> & E.Obs<T>}
         %Equal.sym(List<&2, T>, C.append(T, C.reverse(T, LY.somes(T, AR.slots(Maybe<&2, T>, t))), model(T, r)), Con{y, C.append(T, C.reverse(T, ys), model(T, r))}, em) : {(C.append(T, C.reverse(T, ys), model(T, r)), E.OItem{Done{y}}) == S.step(T, _, E.Pop{}) : List<&2, T> & E.Obs<T>}
         {==}))))

def peek_top(~T: Data, +d: Nat, +m: Nat, +t: AR.Tree<Maybe<&2, T>>, +c: Nat, +r: Sh<T>, +g: {good(T, SST{d, 1n+m, t, c, r}) == True{} : Bool}, +ys: List<&2, T>, +y: T, +e: {LY.somes(T, AR.slots(Maybe<&2, T>, t)) == C.snoc(T, ys, y) : List<&2, T>}, +hl: {C.length(T, ys) == m : Nat}) -> StepOK(~T, SST{d, 1n+m, t, c, r}, E.Peek{}):
  +hlay = DST.g_lay(T, D.cmax(), d, 1n+m, t, g_chunk(T, d, 1n+m, t, c, r, g))
  +hm = N.lt_succ(m)
  +hi = N.lt_le_trans(m, 1n+m, C.pow2(d), hm, DSP.n_le_cap(T, D.cmax(), d, 1n+m, t, g_chunk(T, d, 1n+m, t, c, r, g)))
  +hx = top_slot(T, LY.somes(T, AR.slots(Maybe<&2, T>, t)), ys, y, m, e, hl)
  +em = top_model(T, LY.somes(T, AR.slots(Maybe<&2, T>, t)), ys, y, model(T, r), e)
  +es = Equal.trans(Maybe<&2, T>, W.slot(T, AR.slots(Maybe<&2, T>, t), m), C.nth(T, LY.somes(T, AR.slots(Maybe<&2, T>, t)), m), Some{y}, Equal.cong(Maybe<&2, Maybe<&2, T>>, Maybe<&2, T>, z => W.unwrap(T, z), C.nth(Maybe<&2, T>, AR.slots(Maybe<&2, T>, t), m), Some{C.nth(T, LY.somes(T, AR.slots(Maybe<&2, T>, t)), m)}, LY.lay_nth(T, AR.slots(Maybe<&2, T>, t), 1n+m, m, hlay, hm)), hx)
  (SST{d, 1n+m, t, c, r}, (E.OItem{Done{y}}, (
    %Equal.sym(Array<Maybe<&2, T>> & Maybe<&2, T>, Array.get(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, t), U32.from_nat(m)), (AR.thaw(Maybe<&2, T>, t), W.slot(T, AR.slots(Maybe<&2, T>, t), m)), W.get_slot(T, D.cmax(), d, t, m, DST.g_depth(T, D.cmax(), d, 1n+m, t, g_chunk(T, d, 1n+m, t, c, r, g)), DST.g_limit(T, D.cmax(), d, 1n+m, t, g_chunk(T, d, 1n+m, t, c, r, g)), hi, DST.g_perfect(T, D.cmax(), d, 1n+m, t, g_chunk(T, d, 1n+m, t, c, r, g)))) : {D.obs_item(~T, D.peek_fin(~T, d, 1n+m, c, real(~T, r), _)) == (real(~T, SST{d, 1n+m, t, c, r}), E.OItem{Done{y}}) : D.Stack<T> & E.Obs<T>}
    %Equal.sym(Maybe<&2, T>, W.slot(T, AR.slots(Maybe<&2, T>, t), m), Some{y}, es) : {D.obs_item(~T, D.peek_fin(~T, d, 1n+m, c, real(~T, r), (AR.thaw(Maybe<&2, T>, t), _))) == (real(~T, SST{d, 1n+m, t, c, r}), E.OItem{Done{y}}) : D.Stack<T> & E.Obs<T>}
    {==},
    (g,
     %Equal.sym(List<&2, T>, C.append(T, C.reverse(T, LY.somes(T, AR.slots(Maybe<&2, T>, t))), model(T, r)), Con{y, C.append(T, C.reverse(T, ys), model(T, r))}, em) : {(_, E.OItem{Done{y}}) == S.step(T, _, E.Peek{}) : List<&2, T> & E.Obs<T>}
     {==}))))

def pop_view(~T: Data, +d: Nat, +m: Nat, +t: AR.Tree<Maybe<&2, T>>, +c: Nat, +r: Sh<T>, +g: {good(T, SST{d, 1n+m, t, c, r}) == True{} : Bool}, v: SnocView(T, LY.somes(T, AR.slots(Maybe<&2, T>, t)), m)) -> StepOK(~T, SST{d, 1n+m, t, c, r}, E.Pop{}):
  match v:
    case Tuple{+ys, Tuple{+y, Tuple{e, hl}}}:
      pop_top(~T, d, m, t, c, r, g, ys, y, e, hl)

def peek_view(~T: Data, +d: Nat, +m: Nat, +t: AR.Tree<Maybe<&2, T>>, +c: Nat, +r: Sh<T>, +g: {good(T, SST{d, 1n+m, t, c, r}) == True{} : Bool}, v: SnocView(T, LY.somes(T, AR.slots(Maybe<&2, T>, t)), m)) -> StepOK(~T, SST{d, 1n+m, t, c, r}, E.Peek{}):
  match v:
    case Tuple{+ys, Tuple{+y, Tuple{e, hl}}}:
      peek_top(~T, d, m, t, c, r, g, ys, y, e, hl)

def len_xs(-T: Data, +d: Nat, +m: Nat, +t: AR.Tree<Maybe<&2, T>>, +c: Nat, +r: Sh<T>, +g: {good(T, SST{d, 1n+m, t, c, r}) == True{} : Bool}) -> {C.length(T, LY.somes(T, AR.slots(Maybe<&2, T>, t))) == 1n+m : Nat}:
  LY.lay_len(T, AR.slots(Maybe<&2, T>, t), 1n+m, DST.g_lay(T, D.cmax(), d, 1n+m, t, g_chunk(T, d, 1n+m, t, c, r, g)))

def pop_ok(~T: Data, +d: Nat, +m: Nat, +t: AR.Tree<Maybe<&2, T>>, +c: Nat, +r: Sh<T>, +g: {good(T, SST{d, 1n+m, t, c, r}) == True{} : Bool}) -> StepOK(~T, SST{d, 1n+m, t, c, r}, E.Pop{}):
  pop_view(~T, d, m, t, c, r, g, snoc_view(T, LY.somes(T, AR.slots(Maybe<&2, T>, t)), m, len_xs(T, d, m, t, c, r, g)))

def peek_ok(~T: Data, +d: Nat, +m: Nat, +t: AR.Tree<Maybe<&2, T>>, +c: Nat, +r: Sh<T>, +g: {good(T, SST{d, 1n+m, t, c, r}) == True{} : Bool}) -> StepOK(~T, SST{d, 1n+m, t, c, r}, E.Peek{}):
  peek_view(~T, d, m, t, c, r, g, snoc_view(T, LY.somes(T, AR.slots(Maybe<&2, T>, t)), m, len_xs(T, d, m, t, c, r, g)))

# ---- to_list: the upward slot walk conses the chunk's elements in reverse ----

# the walk over slots i .. i + k of a slot list, consing each onto acc
def uv(~T: Data, k: Nat, +ss: List<&2, Maybe<&2, T>>, +i: Nat, acc: List<&2, T>) -> List<&2, T>:
  match k:
    case 0n:
      D.cons_some(~T, W.slot(T, ss, i), acc)
    case 1n+p:
      uv(~T, p, ss, 1n+i, D.cons_some(~T, W.slot(T, ss, i), acc))

def tl_loop(~T: Data, k: Nat, +d: Nat, +t: AR.Tree<Maybe<&2, T>>, +i: Nat, acc: List<&2, T>, +hd: {Nat.is_le(d, D.cmax()) == True{} : Bool}, +hb: {Nat.is_lt(Nat.add(i, k), C.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, T>, d, t) == True{} : Bool}) -> {D.tl_go(~T, k, i, acc, (AR.thaw(Maybe<&2, T>, t), W.slot(T, AR.slots(Maybe<&2, T>, t), i))) == (AR.thaw(Maybe<&2, T>, t), uv(~T, k, AR.slots(Maybe<&2, T>, t), i, acc)) : Array<Maybe<&2, T>> & List<&2, T>}:
  match k:
    case 0n:
      {==}
    case 1n+ +p:
      +hb1 = L.subst(Nat, z => {Nat.is_lt(z, C.pow2(d)) == True{} : Bool}, Nat.add(i, 1n+p), 1n+Nat.add(i, p), N.add_succ(i, p), hb)
      +hj = N.le_lt_trans(1n+i, 1n+Nat.add(i, p), C.pow2(d), N.le_add_right(i, p), hb1)
      %Equal.sym(Array<Maybe<&2, T>> & Maybe<&2, T>, Array.get(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, t), U32.from_nat(1n+i)), (AR.thaw(Maybe<&2, T>, t), W.slot(T, AR.slots(Maybe<&2, T>, t), 1n+i)), W.get_slot(T, D.cmax(), d, t, 1n+i, hd, {==}, hj, pf)) : {D.tl_go(~T, p, 1n+i, D.cons_some(~T, W.slot(T, AR.slots(Maybe<&2, T>, t), i), acc), _) == (AR.thaw(Maybe<&2, T>, t), uv(~T, 1n+p, AR.slots(Maybe<&2, T>, t), i, acc)) : Array<Maybe<&2, T>> & List<&2, T>}
      tl_loop(~T, p, d, t, 1n+i, D.cons_some(~T, W.slot(T, AR.slots(Maybe<&2, T>, t), i), acc), hd, hb1, pf)

def uv_shift(~T: Data, k: Nat, +s: Maybe<&2, T>, +r: List<&2, Maybe<&2, T>>, +i: Nat, acc: List<&2, T>) -> {uv(~T, k, Con{s, r}, 1n+i, acc) == uv(~T, k, r, i, acc) : List<&2, T>}:
  match k:
    case 0n:
      {==}
    case 1n+ +p:
      uv_shift(~T, p, s, r, 1n+i, D.cons_some(~T, W.slot(T, r, i), acc))

def uv_rev(~T: Data, +ss: List<&2, Maybe<&2, T>>, +m: Nat, +acc: List<&2, T>, +h: {LY.lay(T, ss, 1n+m) == True{} : Bool}) -> {uv(~T, m, ss, 0n, acc) == C.append(T, C.reverse(T, LY.somes(T, ss)), acc) : List<&2, T>}:
  match ss m:
    case Nil{} _:
      Empty.absurd({uv(~T, m, Nil{}, 0n, acc) == C.append(T, C.reverse(T, LY.somes(T, Nil{})), acc) : List<&2, T>}, L.false_true(h))
    case Con{None{}, +r} _:
      Empty.absurd({uv(~T, m, Con{None{}, r}, 0n, acc) == C.append(T, C.reverse(T, LY.somes(T, Con{None{}, r})), acc) : List<&2, T>}, L.false_true(h))
    case Con{Some{+y}, +r} 0n:
      %Equal.sym(List<&2, T>, LY.somes(T, r), Nil{}, LY.nones_somes(T, r, LY.lay0_nones(T, r, h))) : {Con{y, acc} == C.append(T, C.snoc(T, C.reverse(T, _), y), acc) : List<&2, T>}
      {==}
    case Con{Some{+y}, +r} 1n+ +p:
      Equal.trans(List<&2, T>, uv(~T, p, Con{Some{y}, r}, 1n, Con{y, acc}), uv(~T, p, r, 0n, Con{y, acc}), C.append(T, C.snoc(T, C.reverse(T, LY.somes(T, r)), y), acc),
        uv_shift(~T, p, Some{y}, r, 0n, Con{y, acc}),
        Equal.trans(List<&2, T>, uv(~T, p, r, 0n, Con{y, acc}), C.append(T, C.reverse(T, LY.somes(T, r)), Con{y, acc}), C.append(T, C.snoc(T, C.reverse(T, LY.somes(T, r)), y), acc),
          uv_rev(~T, r, p, Con{y, acc}, h),
          Equal.sym(List<&2, T>, C.append(T, C.snoc(T, C.reverse(T, LY.somes(T, r)), y), acc), C.append(T, C.reverse(T, LY.somes(T, r)), Con{y, acc}), LL.snoc_append_cons(T, C.reverse(T, LY.somes(T, r)), y, acc))))

def tl_real(~T: Data, +sh: Sh<T>, +g: {good(T, sh) == True{} : Bool}) -> {D.to_list(~T, real(~T, sh)) == (real(~T, sh), model(T, sh)) : D.Stack<T> & List<&2, T>}:
  match sh:
    case SSE{}:
      {==}
    case SST{+d, 0n, +t, +c, +r}:
      Empty.absurd({D.to_list(~T, real(~T, SST{d, 0n, t, c, r})) == (real(~T, SST{d, 0n, t, c, r}), model(T, SST{d, 0n, t, c, r})) : D.Stack<T> & List<&2, T>}, L.false_true(g_pos(T, d, 0n, t, c, r, g)))
    case SST{+d, 1n+ +m, +t, +c, +r}:
      +cg = g_chunk(T, d, 1n+m, t, c, r, g)
      +hd = DST.g_depth(T, D.cmax(), d, 1n+m, t, cg)
      +pf = DST.g_perfect(T, D.cmax(), d, 1n+m, t, cg)
      +hm = N.succ_le_lt(m, C.pow2(d), DSP.n_le_cap(T, D.cmax(), d, 1n+m, t, cg))
      +h0 = N.succ_le_lt(0n, C.pow2(d), N.pow2_pos(d))
      %Equal.sym(D.Stack<T> & List<&2, T>, D.to_list(~T, real(~T, r)), (real(~T, r), model(T, r)), tl_real(~T, r, g_rest(T, d, 1n+m, t, c, r, g))) : {D.tl_chunk(~T, d, 1n+m, AR.thaw(Maybe<&2, T>, t), c, _) == (real(~T, SST{d, 1n+m, t, c, r}), model(T, SST{d, 1n+m, t, c, r})) : D.Stack<T> & List<&2, T>}
      %Equal.sym(Array<Maybe<&2, T>> & Maybe<&2, T>, Array.get(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, t), U32.from_nat(0n)), (AR.thaw(Maybe<&2, T>, t), W.slot(T, AR.slots(Maybe<&2, T>, t), 0n)), W.get_slot(T, D.cmax(), d, t, 0n, hd, {==}, h0, pf)) : {D.tl_fin(~T, d, 1n+m, c, real(~T, r), D.tl_go(~T, m, 0n, model(T, r), _)) == (real(~T, SST{d, 1n+m, t, c, r}), model(T, SST{d, 1n+m, t, c, r})) : D.Stack<T> & List<&2, T>}
      %Equal.sym(Array<Maybe<&2, T>> & List<&2, T>, D.tl_go(~T, m, 0n, model(T, r), (AR.thaw(Maybe<&2, T>, t), W.slot(T, AR.slots(Maybe<&2, T>, t), 0n))), (AR.thaw(Maybe<&2, T>, t), uv(~T, m, AR.slots(Maybe<&2, T>, t), 0n, model(T, r))), tl_loop(~T, m, d, t, 0n, model(T, r), hd, hm, pf)) : {D.tl_fin(~T, d, 1n+m, c, real(~T, r), _) == (real(~T, SST{d, 1n+m, t, c, r}), model(T, SST{d, 1n+m, t, c, r})) : D.Stack<T> & List<&2, T>}
      %Equal.sym(List<&2, T>, uv(~T, m, AR.slots(Maybe<&2, T>, t), 0n, model(T, r)), C.append(T, C.reverse(T, LY.somes(T, AR.slots(Maybe<&2, T>, t))), model(T, r)), uv_rev(~T, AR.slots(Maybe<&2, T>, t), m, model(T, r), DST.g_lay(T, D.cmax(), d, 1n+m, t, cg))) : {D.tl_fin(~T, d, 1n+m, c, real(~T, r), (AR.thaw(Maybe<&2, T>, t), _)) == (real(~T, SST{d, 1n+m, t, c, r}), model(T, SST{d, 1n+m, t, c, r})) : D.Stack<T> & List<&2, T>}
      {==}

def to_list_ok(~T: Data, +sh: Sh<T>, +g: {good(T, sh) == True{} : Bool}) -> StepOK(~T, sh, E.ToList{}):
  (sh, (E.OList{model(T, sh)}, (
    %Equal.sym(D.Stack<T> & List<&2, T>, D.to_list(~T, real(~T, sh)), (real(~T, sh), model(T, sh)), tl_real(~T, sh, g)) : {D.obs_list(~T, _) == (real(~T, sh), E.OList{model(T, sh)}) : D.Stack<T> & E.Obs<T>}
    {==},
    (g, Equal.sym(List<&2, T> & E.Obs<T>, S.step(T, model(T, sh), E.ToList{}), (model(T, sh), E.OList{model(T, sh)}), spec_tl(T, model(T, sh)))))))

# ---- every operation ----

def step_ok(~T: Data, +sh: Sh<T>, +op: E.Op<T>, +g: {good(T, sh) == True{} : Bool}) -> StepOK(~T, sh, op):
  match sh op:
    case SSE{} E.Length{}:
      (SSE{}, (E.ONat{0n}, ({==}, ({==}, {==}))))
    case SSE{} E.Push{+v}:
      push_empty(~T, v)
    case SSE{} E.Pop{}:
      (SSE{}, (E.OItem{Fail{E.EmptyStack{}}}, ({==}, ({==}, {==}))))
    case SSE{} E.Peek{}:
      (SSE{}, (E.OItem{Fail{E.EmptyStack{}}}, ({==}, ({==}, {==}))))
    case SSE{} E.ToList{}:
      (SSE{}, (E.OList{Nil{}}, ({==}, ({==}, {==}))))
    case SST{+d, +n, +t, +c, +r} E.Length{}:
      length_ok(~T, d, n, t, c, r, g)
    case SST{+d, +n, +t, +c, +r} E.Push{+v}:
      push_ok(~T, d, n, t, c, r, g, v)
    case SST{+d, 0n, +t, +c, +r} E.Pop{}:
      pos_absurd(~T, d, t, c, r, g, E.Pop{})
    case SST{+d, 1n+ +m, +t, +c, +r} E.Pop{}:
      pop_ok(~T, d, m, t, c, r, g)
    case SST{+d, 0n, +t, +c, +r} E.Peek{}:
      pos_absurd(~T, d, t, c, r, g, E.Peek{})
    case SST{+d, 1n+ +m, +t, +c, +r} E.Peek{}:
      peek_ok(~T, d, m, t, c, r, g)
    case SST{+d, +n, +t, +c, +r} E.ToList{}:
      to_list_ok(~T, SST{d, n, t, c, r}, g)
