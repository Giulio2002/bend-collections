import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/u32.bend as U
import ../lib/array.bend as AR
import ../spec/common.bend as SC
import ../../src/containers/deque.bend as DQ
import ./ring.bend as R

# Shadow (Data) description of a reachable ring deque (src/deque.bend).
#
# Base.Array is linear, so -- as for every array-backed structure here -- the
# laws are about the deque BUILT from a Data mirror: S0 is the deque that
# never held an element (DQ.DE, no block), Sh{d, lo, n, t} the ring whose
# block is thaw(t), a tree of 2^d slots, with offset lo and n elements.
#
#   model(sh) = take(rot(slots(t), lo), n)   the elements, front first
#   good(sh)  = d <= 31 (every slot index is a representable U32 and the
#               block is a valid Base.Array), the tree is perfect of depth d,
#               lo < 2^d and n <= 2^d.
#
# The capacity field of the runtime record is derived: real(sh) stores
# 2^d there, and every public operation keeps it that way.

type Shadow<-T: Data> is Data:
  S0{}
  Sh{d: Nat, lo: Nat, n: Nat, t: AR.Tree<T>}

def real(-T: Data, sh: Shadow<T>) -> DQ.Deque<T>:
  match sh:
    case S0{}:
      DQ.DE{}
    case Sh{+d, lo, n, t}:
      DQ.DQ{d, SC.pow2(d), lo, n, AR.thaw(T, t)}

def rest(-T: Data, +d: Nat, +lo: Nat, +n: Nat, +t: AR.Tree<T>) -> Bool:
  Bool.and(AR.perfect(T, d, t), Bool.and(Nat.is_lt(lo, SC.pow2(d)), Nat.is_le(n, SC.pow2(d))))

def good(-T: Data, sh: Shadow<T>) -> Bool:
  match sh:
    case S0{}:
      True{}
    case Sh{+d, +lo, +n, +t}:
      Bool.and(Nat.is_le(d, 31n), rest(T, d, lo, n, t))

def model(-T: Data, sh: Shadow<T>) -> List<&2, T>:
  match sh:
    case S0{}:
      Nil{}
    case Sh{d, +lo, +n, +t}:
      SC.take(T, R.rot(T, AR.slots(T, t), lo), n)

def initial(-T: Data) -> Shadow<T>:
  S0{}

# ---- projections of good ----

def g_depth(-T: Data, +d: Nat, +lo: Nat, +n: Nat, +t: AR.Tree<T>, +g: {good(T, Sh{d, lo, n, t}) == True{} : Bool}) -> {Nat.is_le(d, 31n) == True{} : Bool}:
  L.and_left(Nat.is_le(d, 31n), rest(T, d, lo, n, t), g)

def g_rest(-T: Data, +d: Nat, +lo: Nat, +n: Nat, +t: AR.Tree<T>, +g: {good(T, Sh{d, lo, n, t}) == True{} : Bool}) -> {rest(T, d, lo, n, t) == True{} : Bool}:
  L.and_right(Nat.is_le(d, 31n), rest(T, d, lo, n, t), g)

def g_perfect(-T: Data, +d: Nat, +lo: Nat, +n: Nat, +t: AR.Tree<T>, +g: {good(T, Sh{d, lo, n, t}) == True{} : Bool}) -> {AR.perfect(T, d, t) == True{} : Bool}:
  L.and_left(AR.perfect(T, d, t), Bool.and(Nat.is_lt(lo, SC.pow2(d)), Nat.is_le(n, SC.pow2(d))), g_rest(T, d, lo, n, t, g))

def g_r2(-T: Data, +d: Nat, +lo: Nat, +n: Nat, +t: AR.Tree<T>, +g: {good(T, Sh{d, lo, n, t}) == True{} : Bool}) -> {Bool.and(Nat.is_lt(lo, SC.pow2(d)), Nat.is_le(n, SC.pow2(d))) == True{} : Bool}:
  L.and_right(AR.perfect(T, d, t), Bool.and(Nat.is_lt(lo, SC.pow2(d)), Nat.is_le(n, SC.pow2(d))), g_rest(T, d, lo, n, t, g))

def g_lo(-T: Data, +d: Nat, +lo: Nat, +n: Nat, +t: AR.Tree<T>, +g: {good(T, Sh{d, lo, n, t}) == True{} : Bool}) -> {Nat.is_lt(lo, SC.pow2(d)) == True{} : Bool}:
  L.and_left(Nat.is_lt(lo, SC.pow2(d)), Nat.is_le(n, SC.pow2(d)), g_r2(T, d, lo, n, t, g))

def g_n(-T: Data, +d: Nat, +lo: Nat, +n: Nat, +t: AR.Tree<T>, +g: {good(T, Sh{d, lo, n, t}) == True{} : Bool}) -> {Nat.is_le(n, SC.pow2(d)) == True{} : Bool}:
  L.and_right(Nat.is_lt(lo, SC.pow2(d)), Nat.is_le(n, SC.pow2(d)), g_r2(T, d, lo, n, t, g))

def good_intro(-T: Data, +d: Nat, +lo: Nat, +n: Nat, +t: AR.Tree<T>, +hd: {Nat.is_le(d, 31n) == True{} : Bool}, +pf: {AR.perfect(T, d, t) == True{} : Bool}, +hl: {Nat.is_lt(lo, SC.pow2(d)) == True{} : Bool}, +hn: {Nat.is_le(n, SC.pow2(d)) == True{} : Bool}) -> {good(T, Sh{d, lo, n, t}) == True{} : Bool}:
  L.and_intro(Nat.is_le(d, 31n), rest(T, d, lo, n, t), hd,
    L.and_intro(AR.perfect(T, d, t), Bool.and(Nat.is_lt(lo, SC.pow2(d)), Nat.is_le(n, SC.pow2(d))), pf,
      L.and_intro(Nat.is_lt(lo, SC.pow2(d)), Nat.is_le(n, SC.pow2(d)), hl, hn)))

# the slot list of a good shadow has 2^d elements
def g_len(-T: Data, +d: Nat, +lo: Nat, +n: Nat, +t: AR.Tree<T>, +g: {good(T, Sh{d, lo, n, t}) == True{} : Bool}) -> {SC.length(T, AR.slots(T, t)) == SC.pow2(d) : Nat}:
  AR.slots_length(T, d, t, g_perfect(T, d, lo, n, t, g))

# ---- values, indices and indexed access ----

# Any element of a tree (the leftmost): a default for the element at a slot.
def any(-T: Data, t: AR.Tree<T>) -> T:
  match t:
    case AR.TLeaf{x}:
      x
    case AR.TNode{l, r}:
      any(T, l)

# The element in slot j of the tree.
def vat(-T: Data, +t: AR.Tree<T>, +j: Nat) -> T:
  L.some_value(T, SC.nth(T, AR.slots(T, t), j), any(T, t))

def some_val(-A: Data, +m: Maybe<&2, A>, +dflt: A, +h: {Bool.not(Maybe.is_none(&2, A, m)) == True{} : Bool}) -> {m == Some{L.some_value(A, m, dflt)} : Maybe<&2, A>}:
  match m:
    case None{}:
      Empty.absurd({None{} == Some{L.some_value(A, None{}, dflt)} : Maybe<&2, A>}, L.false_true(h))
    case Some{x}:
      {==}

def nth_some(-A: Data, +xs: List<&2, A>, +j: Nat, +dflt: A, +h: {Nat.is_lt(j, SC.length(A, xs)) == True{} : Bool}) -> {SC.nth(A, xs, j) == Some{L.some_value(A, SC.nth(A, xs, j), dflt)} : Maybe<&2, A>}:
  match xs j:
    case Nil{} _:
      Empty.absurd({SC.nth(A, Nil{}, j) == Some{L.some_value(A, SC.nth(A, Nil{}, j), dflt)} : Maybe<&2, A>}, N.lt_zero_absurd(j, h))
    case Con{x, t} 0n:
      {==}
    case Con{+x, +t} 1n+ +p:
      nth_some(A, t, p, dflt, h)

def slot_val(-T: Data, +d: Nat, +t: AR.Tree<T>, +j: Nat, +pf: {AR.perfect(T, d, t) == True{} : Bool}, +hj: {Nat.is_lt(j, SC.pow2(d)) == True{} : Bool}) -> {SC.nth(T, AR.slots(T, t), j) == Some{vat(T, t, j)} : Maybe<&2, T>}:
  nth_some(T, AR.slots(T, t), j, any(T, t), AR.len_lt(T, d, t, j, pf, hj))

def idx(+d: Nat, +j: Nat, +hd: {Nat.is_le(d, 31n) == True{} : Bool}, +hj: {Nat.is_lt(j, SC.pow2(d)) == True{} : Bool}) -> {U32.to_nat(U32.from_nat(j)) == j : Nat}:
  U.to_nat_from_nat(j, d, N.lt_le(d, 32n, N.le_lt_succ(d, 31n, hd)), hj)

def idx_lt(+d: Nat, +j: Nat, +hd: {Nat.is_le(d, 31n) == True{} : Bool}, +hj: {Nat.is_lt(j, SC.pow2(d)) == True{} : Bool}) -> {Nat.is_lt(U32.to_nat(U32.from_nat(j)), SC.pow2(d)) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(d)) == True{} : Bool}, j, U32.to_nat(U32.from_nat(j)), Equal.sym(Nat, U32.to_nat(U32.from_nat(j)), j, idx(d, j, hd, hj)), hj)

def lt32(+d: Nat, +hd: {Nat.is_le(d, 31n) == True{} : Bool}) -> {Nat.is_lt(d, 32n) == True{} : Bool}:
  N.le_lt_succ(d, 31n, hd)

# reading slot j of the block
def get_at(-T: Data, +d: Nat, +t: AR.Tree<T>, +j: Nat, +hd: {Nat.is_le(d, 31n) == True{} : Bool}, +pf: {AR.perfect(T, d, t) == True{} : Bool}, +hj: {Nat.is_lt(j, SC.pow2(d)) == True{} : Bool}) -> {Array.get(T, AR.thaw(T, t), U32.from_nat(j)) == (AR.thaw(T, t), vat(T, t, j)) : Array<T> & T}:
  AR.get(T, d, t, U32.from_nat(j), vat(T, t, j), lt32(d, hd), idx_lt(d, j, hd, hj),
    L.subst(Nat, z => {SC.nth(T, AR.slots(T, t), z) == Some{vat(T, t, j)} : Maybe<&2, T>}, j, U32.to_nat(U32.from_nat(j)), Equal.sym(Nat, U32.to_nat(U32.from_nat(j)), j, idx(d, j, hd, hj)), slot_val(T, d, t, j, pf, hj)),
    pf)

# writing slot j of the block
def set_at(-T: Data, +d: Nat, +t: AR.Tree<T>, +j: Nat, +v: T, +hd: {Nat.is_le(d, 31n) == True{} : Bool}, +pf: {AR.perfect(T, d, t) == True{} : Bool}, +hj: {Nat.is_lt(j, SC.pow2(d)) == True{} : Bool}) -> {Array.set(T, AR.thaw(T, t), U32.from_nat(j), v) == AR.thaw(T, AR.upd(T, d, t, j, v)) : Array<T>}:
  +e = AR.set(T, d, t, U32.from_nat(j), v, vat(T, t, j), lt32(d, hd), idx_lt(d, j, hd, hj),
    L.subst(Nat, z => {SC.nth(T, AR.slots(T, t), z) == Some{vat(T, t, j)} : Maybe<&2, T>}, j, U32.to_nat(U32.from_nat(j)), Equal.sym(Nat, U32.to_nat(U32.from_nat(j)), j, idx(d, j, hd, hj)), slot_val(T, d, t, j, pf, hj)),
    pf)
  L.subst(Nat, z => {Array.set(T, AR.thaw(T, t), U32.from_nat(j), v) == AR.thaw(T, AR.upd(T, d, t, z, v)) : Array<T>}, U32.to_nat(U32.from_nat(j)), j, idx(d, j, hd, hj), e)

# ---- a runtime deque determines its shadow ----

def unreal(-T: Data, d: DQ.Deque<T>) -> Shadow<T>:
  match d:
    case DQ.DE{}:
      S0{}
    case DQ.DQ{dep, cap, lo, n, a}:
      Sh{dep, lo, n, AR.freeze(T, a)}

def unreal_real(-T: Data, +sh: Shadow<T>) -> {unreal(T, real(T, sh)) == sh : Shadow<T>}:
  match sh:
    case S0{}:
      {==}
    case Sh{+d, +lo, +n, +t}:
      Equal.cong(AR.Tree<T>, Shadow<T>, z => Sh{d, lo, n, z}, AR.freeze(T, AR.thaw(T, t)), t, AR.freeze_thaw(T, t))

def real_inj(-T: Data, +a: Shadow<T>, +b: Shadow<T>, +e: {real(T, a) == real(T, b) : DQ.Deque<T>}) -> {a == b : Shadow<T>}:
  Equal.trans(Shadow<T>, a, unreal(T, real(T, a)), b, Equal.sym(Shadow<T>, unreal(T, real(T, a)), a, unreal_real(T, a)),
    Equal.trans(Shadow<T>, unreal(T, real(T, a)), unreal(T, real(T, b)), b, Equal.cong(DQ.Deque<T>, Shadow<T>, z => unreal(T, z), real(T, a), real(T, b), e), unreal_real(T, b)))
