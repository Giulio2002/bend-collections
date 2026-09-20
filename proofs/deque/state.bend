import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/u32.bend as U
import ../lib/array.bend as AR
import ../../spec/common.bend as SC
import ../../src/deque.bend as DQ
import ../../types/deque.bend as E
import ../dynamic_array/layout.bend as LY
import ./layout.bend as WN

# Shadow (Data) description of a reachable deque: depth, window offset,
# length and the mirror tree t of its Base.Array (the array is thaw(t)).
#
#   model(sh)  = LY.somes(slots(t))   the elements, front first
#   good(sh)   = depth <= 31 (so every slot index is a representable U32),
#                the tree is perfect of that depth, and the Some slots are
#                exactly the window [lo, lo + len).

type Shadow<-T: Data> is Data:
  Sh{depth: Nat, lo: Nat, len: Nat, tree: AR.Tree<Maybe<&2, T>>}

# The capacity field is derived, not stored in the shadow: a real deque built
# by the constructor always carries 2^depth there (proofs/deque/init.bend),
# and every law below is about a `real(sh)` that does.
def real(-T: Data, sh: Shadow<T>) -> DQ.Deque<T>:
  match sh:
    case Sh{+d, lo, n, t}:
      DQ.DQ{d, SC.pow2(d), lo, n, AR.thaw(Maybe<&2, T>, t)}

def good(-T: Data, sh: Shadow<T>) -> Bool:
  match sh:
    case Sh{+d, +lo, +n, +t}:
      Bool.and(Nat.is_le(d, 31n), Bool.and(AR.perfect(Maybe<&2, T>, d, t), WN.win(T, AR.slots(Maybe<&2, T>, t), lo, n)))

def model(-T: Data, sh: Shadow<T>) -> List<&2, T>:
  match sh:
    case Sh{d, lo, n, t}:
      LY.somes(T, AR.slots(Maybe<&2, T>, t))

# ---- projections of good ----

def rest1(-T: Data, +d: Nat, +lo: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>) -> Bool:
  Bool.and(AR.perfect(Maybe<&2, T>, d, t), WN.win(T, AR.slots(Maybe<&2, T>, t), lo, n))

def g_depth(-T: Data, +d: Nat, +lo: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +g: {good(T, Sh{d, lo, n, t}) == True{} : Bool}) -> {Nat.is_le(d, 31n) == True{} : Bool}:
  L.and_left(Nat.is_le(d, 31n), rest1(T, d, lo, n, t), g)

def g_r1(-T: Data, +d: Nat, +lo: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +g: {good(T, Sh{d, lo, n, t}) == True{} : Bool}) -> {rest1(T, d, lo, n, t) == True{} : Bool}:
  L.and_right(Nat.is_le(d, 31n), rest1(T, d, lo, n, t), g)

def g_perfect(-T: Data, +d: Nat, +lo: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +g: {good(T, Sh{d, lo, n, t}) == True{} : Bool}) -> {AR.perfect(Maybe<&2, T>, d, t) == True{} : Bool}:
  L.and_left(AR.perfect(Maybe<&2, T>, d, t), WN.win(T, AR.slots(Maybe<&2, T>, t), lo, n), g_r1(T, d, lo, n, t, g))

def g_win(-T: Data, +d: Nat, +lo: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +g: {good(T, Sh{d, lo, n, t}) == True{} : Bool}) -> {WN.win(T, AR.slots(Maybe<&2, T>, t), lo, n) == True{} : Bool}:
  L.and_right(AR.perfect(Maybe<&2, T>, d, t), WN.win(T, AR.slots(Maybe<&2, T>, t), lo, n), g_r1(T, d, lo, n, t, g))

def good_intro(-T: Data, +d: Nat, +lo: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +a: {Nat.is_le(d, 31n) == True{} : Bool}, +cc: {AR.perfect(Maybe<&2, T>, d, t) == True{} : Bool}, +e: {WN.win(T, AR.slots(Maybe<&2, T>, t), lo, n) == True{} : Bool}) -> {good(T, Sh{d, lo, n, t}) == True{} : Bool}:
  L.and_intro(Nat.is_le(d, 31n), rest1(T, d, lo, n, t), a,
    L.and_intro(AR.perfect(Maybe<&2, T>, d, t), WN.win(T, AR.slots(Maybe<&2, T>, t), lo, n), cc, e))

# ---- derived facts ----

def lt32(+d: Nat, +hd: {Nat.is_le(d, 31n) == True{} : Bool}) -> {Nat.is_lt(d, 32n) == True{} : Bool}:
  N.le_lt_succ(d, 31n, hd)

def le32(+d: Nat, +hd: {Nat.is_le(d, 31n) == True{} : Bool}) -> {Nat.is_le(d, 32n) == True{} : Bool}:
  N.lt_le(d, 32n, lt32(d, hd))

def pow2_src(+d: Nat) -> {DQ.pow2(d) == SC.pow2(d) : Nat}:
  match d:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, Nat.double, DQ.pow2(p), SC.pow2(p), pow2_src(p))

# the spec's item, spelled here so that slot_item can be stated before the
# spec import chain of steps.bend
def S_item(-T: Data, x: Maybe<&2, T>) -> Result<&2, &2, E.Error, T>:
  match x:
    case None{}:
      Fail{E.EmptyDeque{}}
    case Some{v}:
      Done{v}

def slot_item(-T: Data, +m: Maybe<&2, T>) -> {DQ.item(T, m) == S_item(T, m) : Result<&2, &2, E.Error, T>}:
  match m:
    case None{}:
      {==}
    case Some{x}:
      {==}

def empty_eq(-T: Data, +d: Nat) -> {DQ.empty_slots(T, d) == AR.thaw(Maybe<&2, T>, AR.trep(Maybe<&2, T>, d, None{})) : Array<Maybe<&2, T>>}:
  AR.new(Maybe<&2, T>, d, None{})

# growing at the back: the old block is the lower half, every index unchanged
def grown_back_eq(-T: Data, +d: Nat, +t: AR.Tree<Maybe<&2, T>>) -> {DQ.grown_back(T, d, AR.thaw(Maybe<&2, T>, t)) == AR.thaw(Maybe<&2, T>, AR.TNode{t, AR.trep(Maybe<&2, T>, d, None{})}) : Array<Maybe<&2, T>>}:
  %Equal.sym(Array<Maybe<&2, T>>, DQ.empty_slots(T, d), AR.thaw(Maybe<&2, T>, AR.trep(Maybe<&2, T>, d, None{})), empty_eq(T, d)) : {ANode{AR.thaw(Maybe<&2, T>, t), _} == ANode{AR.thaw(Maybe<&2, T>, t), AR.thaw(Maybe<&2, T>, AR.trep(Maybe<&2, T>, d, None{}))} : Array<Maybe<&2, T>>}
  {==}

# growing at the front: the old block is the upper half, every index moves up
def grown_front_eq(-T: Data, +d: Nat, +t: AR.Tree<Maybe<&2, T>>) -> {DQ.grown_front(T, d, AR.thaw(Maybe<&2, T>, t)) == AR.thaw(Maybe<&2, T>, AR.TNode{AR.trep(Maybe<&2, T>, d, None{}), t}) : Array<Maybe<&2, T>>}:
  %Equal.sym(Array<Maybe<&2, T>>, DQ.empty_slots(T, d), AR.thaw(Maybe<&2, T>, AR.trep(Maybe<&2, T>, d, None{})), empty_eq(T, d)) : {ANode{_, AR.thaw(Maybe<&2, T>, t)} == ANode{AR.thaw(Maybe<&2, T>, AR.trep(Maybe<&2, T>, d, None{})), AR.thaw(Maybe<&2, T>, t)} : Array<Maybe<&2, T>>}
  {==}

def slots_back(-T: Data, +d: Nat, +t: AR.Tree<Maybe<&2, T>>) -> {AR.slots(Maybe<&2, T>, AR.TNode{t, AR.trep(Maybe<&2, T>, d, None{})}) == SC.append(Maybe<&2, T>, AR.slots(Maybe<&2, T>, t), SC.replicate(Maybe<&2, T>, SC.pow2(d), None{})) : List<&2, Maybe<&2, T>>}:
  %Equal.sym(List<&2, Maybe<&2, T>>, AR.slots(Maybe<&2, T>, AR.trep(Maybe<&2, T>, d, None{})), SC.replicate(Maybe<&2, T>, SC.pow2(d), None{}), AR.trep_slots(Maybe<&2, T>, d, None{})) : {SC.append(Maybe<&2, T>, AR.slots(Maybe<&2, T>, t), _) == SC.append(Maybe<&2, T>, AR.slots(Maybe<&2, T>, t), SC.replicate(Maybe<&2, T>, SC.pow2(d), None{})) : List<&2, Maybe<&2, T>>}
  {==}

def slots_front(-T: Data, +d: Nat, +t: AR.Tree<Maybe<&2, T>>) -> {AR.slots(Maybe<&2, T>, AR.TNode{AR.trep(Maybe<&2, T>, d, None{}), t}) == SC.append(Maybe<&2, T>, SC.replicate(Maybe<&2, T>, SC.pow2(d), None{}), AR.slots(Maybe<&2, T>, t)) : List<&2, Maybe<&2, T>>}:
  %Equal.sym(List<&2, Maybe<&2, T>>, AR.slots(Maybe<&2, T>, AR.trep(Maybe<&2, T>, d, None{})), SC.replicate(Maybe<&2, T>, SC.pow2(d), None{}), AR.trep_slots(Maybe<&2, T>, d, None{})) : {SC.append(Maybe<&2, T>, _, AR.slots(Maybe<&2, T>, t)) == SC.append(Maybe<&2, T>, SC.replicate(Maybe<&2, T>, SC.pow2(d), None{}), AR.slots(Maybe<&2, T>, t)) : List<&2, Maybe<&2, T>>}
  {==}

def node_perfect(-T: Data, +d: Nat, +l: AR.Tree<Maybe<&2, T>>, +r: AR.Tree<Maybe<&2, T>>, +pl: {AR.perfect(Maybe<&2, T>, d, l) == True{} : Bool}, +pr: {AR.perfect(Maybe<&2, T>, d, r) == True{} : Bool}) -> {AR.perfect(Maybe<&2, T>, 1n+d, AR.TNode{l, r}) == True{} : Bool}:
  L.and_intro(AR.perfect(Maybe<&2, T>, d, l), AR.perfect(Maybe<&2, T>, d, r), pl, pr)

# ---- the shadow of a live deque is unique ----
#
# A runtime deque determines its shadow, so "the operation lands on the array
# of THIS shadow, whose model is the spec's" pins the abstract state: the
# laws cannot be satisfied by naming a different shadow.

def eat(-T: Data, t: AR.Tree<Maybe<&2, T>>, +v: Nat) -> Nat:
  match t:
    case AR.TLeaf{x}:
      v
    case AR.TNode{l, r}:
      eat(T, r, eat(T, l, v))

def f_depth(-T: Data, f: DQ.Deque<T>) -> Nat:
  match f:
    case DQ.DQ{+d, c, lo, n, a}:
      eat(T, AR.freeze(Maybe<&2, T>, a), d)

def f_lo(-T: Data, f: DQ.Deque<T>) -> Nat:
  match f:
    case DQ.DQ{d, c, +lo, n, a}:
      eat(T, AR.freeze(Maybe<&2, T>, a), lo)

def f_len(-T: Data, f: DQ.Deque<T>) -> Nat:
  match f:
    case DQ.DQ{d, c, lo, +n, a}:
      eat(T, AR.freeze(Maybe<&2, T>, a), n)

def f_tree(-T: Data, f: DQ.Deque<T>) -> AR.Tree<Maybe<&2, T>>:
  match f:
    case DQ.DQ{d, c, lo, n, a}:
      AR.freeze(Maybe<&2, T>, a)

def eat_id(-T: Data, t: AR.Tree<Maybe<&2, T>>, +v: Nat) -> {eat(T, t, v) == v : Nat}:
  match t:
    case AR.TLeaf{x}:
      {==}
    case AR.TNode{+l, +r}:
      %Equal.sym(Nat, eat(T, l, v), v, eat_id(T, l, v)) : {eat(T, r, _) == v : Nat}
      eat_id(T, r, v)

def eat_thaw(-T: Data, +v: Nat, +t: AR.Tree<Maybe<&2, T>>) -> {eat(T, AR.freeze(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, t)), v) == v : Nat}:
  %Equal.sym(AR.Tree<Maybe<&2, T>>, AR.freeze(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, t)), t, AR.freeze_thaw(Maybe<&2, T>, t)) : {eat(T, _, v) == v : Nat}
  eat_id(T, t, v)

def sh_len(-T: Data, sh: Shadow<T>) -> Nat:
  match sh:
    case Sh{d, lo, n, t}:
      n

def sh_lo(-T: Data, sh: Shadow<T>) -> Nat:
  match sh:
    case Sh{d, lo, n, t}:
      lo

def sh_dep(-T: Data, sh: Shadow<T>) -> Nat:
  match sh:
    case Sh{d, lo, n, t}:
      d

def sh_tree(-T: Data, sh: Shadow<T>) -> AR.Tree<Maybe<&2, T>>:
  match sh:
    case Sh{d, lo, n, t}:
      t

def real_depth(-T: Data, +sh: Shadow<T>) -> {f_depth(T, real(T, sh)) == sh_dep(T, sh) : Nat}:
  match sh:
    case Sh{+d, lo, n, +t}:
      eat_thaw(T, d, t)

def real_lo(-T: Data, +sh: Shadow<T>) -> {f_lo(T, real(T, sh)) == sh_lo(T, sh) : Nat}:
  match sh:
    case Sh{d, +lo, n, +t}:
      eat_thaw(T, lo, t)

def real_len(-T: Data, +sh: Shadow<T>) -> {f_len(T, real(T, sh)) == sh_len(T, sh) : Nat}:
  match sh:
    case Sh{d, lo, +n, +t}:
      eat_thaw(T, n, t)

def real_tree(-T: Data, +sh: Shadow<T>) -> {f_tree(T, real(T, sh)) == sh_tree(T, sh) : AR.Tree<Maybe<&2, T>>}:
  match sh:
    case Sh{d, lo, n, +t}:
      AR.freeze_thaw(Maybe<&2, T>, t)

def sh_eta(-T: Data, +sh: Shadow<T>) -> {sh == Sh{sh_dep(T, sh), sh_lo(T, sh), sh_len(T, sh), sh_tree(T, sh)} : Shadow<T>}:
  match sh:
    case Sh{d, lo, n, t}:
      {==}

def real_inj_parts(-T: Data, +a: Shadow<T>, +b: Shadow<T>, +e: {real(T, a) == real(T, b) : DQ.Deque<T>}) -> {Sh{sh_dep(T, a), sh_lo(T, a), sh_len(T, a), sh_tree(T, a)} == Sh{sh_dep(T, b), sh_lo(T, b), sh_len(T, b), sh_tree(T, b)} : Shadow<T>}:
  %real_depth(T, a) : {Sh{_, sh_lo(T, a), sh_len(T, a), sh_tree(T, a)} == Sh{sh_dep(T, b), sh_lo(T, b), sh_len(T, b), sh_tree(T, b)} : Shadow<T>}
  %real_lo(T, a) : {Sh{f_depth(T, real(T, a)), _, sh_len(T, a), sh_tree(T, a)} == Sh{sh_dep(T, b), sh_lo(T, b), sh_len(T, b), sh_tree(T, b)} : Shadow<T>}
  %real_len(T, a) : {Sh{f_depth(T, real(T, a)), f_lo(T, real(T, a)), _, sh_tree(T, a)} == Sh{sh_dep(T, b), sh_lo(T, b), sh_len(T, b), sh_tree(T, b)} : Shadow<T>}
  %real_tree(T, a) : {Sh{f_depth(T, real(T, a)), f_lo(T, real(T, a)), f_len(T, real(T, a)), _} == Sh{sh_dep(T, b), sh_lo(T, b), sh_len(T, b), sh_tree(T, b)} : Shadow<T>}
  %real_depth(T, b) : {Sh{f_depth(T, real(T, a)), f_lo(T, real(T, a)), f_len(T, real(T, a)), f_tree(T, real(T, a))} == Sh{_, sh_lo(T, b), sh_len(T, b), sh_tree(T, b)} : Shadow<T>}
  %real_lo(T, b) : {Sh{f_depth(T, real(T, a)), f_lo(T, real(T, a)), f_len(T, real(T, a)), f_tree(T, real(T, a))} == Sh{f_depth(T, real(T, b)), _, sh_len(T, b), sh_tree(T, b)} : Shadow<T>}
  %real_len(T, b) : {Sh{f_depth(T, real(T, a)), f_lo(T, real(T, a)), f_len(T, real(T, a)), f_tree(T, real(T, a))} == Sh{f_depth(T, real(T, b)), f_lo(T, real(T, b)), _, sh_tree(T, b)} : Shadow<T>}
  %real_tree(T, b) : {Sh{f_depth(T, real(T, a)), f_lo(T, real(T, a)), f_len(T, real(T, a)), f_tree(T, real(T, a))} == Sh{f_depth(T, real(T, b)), f_lo(T, real(T, b)), f_len(T, real(T, b)), _} : Shadow<T>}
  Equal.cong(DQ.Deque<T>, Shadow<T>, s => Sh{f_depth(T, s), f_lo(T, s), f_len(T, s), f_tree(T, s)}, real(T, a), real(T, b), e)

def real_inj(-T: Data, +a: Shadow<T>, +b: Shadow<T>, +e: {real(T, a) == real(T, b) : DQ.Deque<T>}) -> {a == b : Shadow<T>}:
  Equal.trans(Shadow<T>, a, Sh{sh_dep(T, a), sh_lo(T, a), sh_len(T, a), sh_tree(T, a)}, b,
    sh_eta(T, a),
    Equal.trans(Shadow<T>, Sh{sh_dep(T, a), sh_lo(T, a), sh_len(T, a), sh_tree(T, a)}, Sh{sh_dep(T, b), sh_lo(T, b), sh_len(T, b), sh_tree(T, b)}, b,
      real_inj_parts(T, a, b, e),
      Equal.sym(Shadow<T>, b, Sh{sh_dep(T, b), sh_lo(T, b), sh_len(T, b), sh_tree(T, b)}, sh_eta(T, b))))
