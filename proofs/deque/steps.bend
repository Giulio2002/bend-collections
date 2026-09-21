import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/array.bend as AR
import ../../spec/common.bend as SC
import ../../spec/deque.bend as S
import ../../src/deque.bend as DQ
import ../../types/deque.bend as E
import ./state.bend as ST
import ./stepok.bend as K
import ./reads.bend as RD
import ./pushes.bend as PU

# Every public operation on the deque built from a good shadow refines the
# spec step (K.StepOK). The only premise is the representation's capacity
# condition, and only for a push: the deque holds fewer than 2^q elements
# (q <= 31) when it is pushed onto. A push onto a full ring of 2^d elements
# doubles the block, so 2^d < 2^q <= 2^31 keeps every block within the
# 2^31 slots a Base.Array can index. The bound is on the PEAK number of
# elements; pops never grow anything.

def pushok(-T: Data, +q: Nat, op: E.Op<T>, +xs: List<&2, T>) -> Bool:
  match op:
    case E.PushFront{x}:
      Nat.is_lt(SC.length(T, xs), SC.pow2(q))
    case E.PushBack{x}:
      Nat.is_lt(SC.length(T, xs), SC.pow2(q))
    case _:
      True{}

def lt_of_pow2(+d: Nat, +q: Nat, +h: {Nat.is_lt(SC.pow2(d), SC.pow2(q)) == True{} : Bool}, c: Bool, +ec: {Nat.is_lt(d, q) == c : Bool}) -> {Nat.is_lt(d, q) == True{} : Bool}:
  match c:
    case True{}:
      ec
    case False{}:
      +hle = N.pow2_mono(q, d, N.not_lt_le(d, q, ec))
      Empty.absurd({Nat.is_lt(d, q) == True{} : Bool}, L.false_true(Equal.trans(Bool, False{}, Nat.is_lt(SC.pow2(d), SC.pow2(d)), True{}, Equal.sym(Bool, Nat.is_lt(SC.pow2(d), SC.pow2(d)), False{}, N.lt_irrefl(SC.pow2(d))), N.lt_le_trans(SC.pow2(d), SC.pow2(q), SC.pow2(d), h, hle))))

# a full ring pushed onto under the capacity condition: n = 2^d and d < 31
def full_eq(-T: Data, +d: Nat, +lo: Nat, +n: Nat, +t: AR.Tree<T>, +g: {ST.good(T, ST.Sh{d, lo, n, t}) == True{} : Bool}, +eb: {Nat.is_lt(n, SC.pow2(d)) == False{} : Bool}) -> {n == SC.pow2(d) : Nat}:
  N.le_antisym(n, SC.pow2(d), ST.g_n(T, d, lo, n, t, g), N.not_lt_le(n, SC.pow2(d), eb))

def full_room(-T: Data, +d: Nat, +lo: Nat, +n: Nat, +t: AR.Tree<T>, +g: {ST.good(T, ST.Sh{d, lo, n, t}) == True{} : Bool}, +eb: {Nat.is_lt(n, SC.pow2(d)) == False{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +hp: {Nat.is_lt(SC.length(T, ST.model(T, ST.Sh{d, lo, n, t})), SC.pow2(q)) == True{} : Bool}) -> {Nat.is_le(1n+d, 31n) == True{} : Bool}:
  +hn = L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(q)) == True{} : Bool}, SC.length(T, ST.model(T, ST.Sh{d, lo, n, t})), n, K.mlen(T, d, lo, n, t, g), hp)
  +hc = L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(q)) == True{} : Bool}, n, SC.pow2(d), full_eq(T, d, lo, n, t, g, eb), hn)
  N.le_trans(1n+d, q, 31n, N.lt_succ_le_succ(d, q, lt_of_pow2(d, q, hc, Nat.is_lt(d, q), {==})), hq)

def pb_case(~T: Data, +d: Nat, +lo: Nat, +n: Nat, +t: AR.Tree<T>, +v: T, +g: {ST.good(T, ST.Sh{d, lo, n, t}) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +hp: {Nat.is_lt(SC.length(T, ST.model(T, ST.Sh{d, lo, n, t})), SC.pow2(q)) == True{} : Bool}, b: Bool, +eb: {Nat.is_lt(n, SC.pow2(d)) == b : Bool}) -> K.StepOK(~T, ST.Sh{d, lo, n, t}, E.PushBack{v}):
  match b:
    case True{}:
      PU.pb_room_ok(~T, d, lo, n, t, v, g, eb)
    case False{}:
      +ec = full_eq(T, d, lo, n, t, g, eb)
      +g2 = L.subst(Nat, z => {ST.good(T, ST.Sh{d, lo, z, t}) == True{} : Bool}, n, SC.pow2(d), ec, g)
      L.subst(Nat, z => K.StepOK(~T, ST.Sh{d, lo, z, t}, E.PushBack{v}), SC.pow2(d), n, Equal.sym(Nat, n, SC.pow2(d), ec), PU.pb_full_ok(~T, d, lo, t, v, g2, full_room(T, d, lo, n, t, g, eb, q, hq, hp)))

def pf_case(~T: Data, +d: Nat, +lo: Nat, +n: Nat, +t: AR.Tree<T>, +v: T, +g: {ST.good(T, ST.Sh{d, lo, n, t}) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +hp: {Nat.is_lt(SC.length(T, ST.model(T, ST.Sh{d, lo, n, t})), SC.pow2(q)) == True{} : Bool}, b: Bool, +eb: {Nat.is_lt(n, SC.pow2(d)) == b : Bool}) -> K.StepOK(~T, ST.Sh{d, lo, n, t}, E.PushFront{v}):
  match b:
    case True{}:
      PU.pf_room_ok(~T, d, lo, n, t, v, g, eb)
    case False{}:
      +ec = full_eq(T, d, lo, n, t, g, eb)
      +g2 = L.subst(Nat, z => {ST.good(T, ST.Sh{d, lo, z, t}) == True{} : Bool}, n, SC.pow2(d), ec, g)
      L.subst(Nat, z => K.StepOK(~T, ST.Sh{d, lo, z, t}, E.PushFront{v}), SC.pow2(d), n, Equal.sym(Nat, n, SC.pow2(d), ec), PU.pf_full_ok(~T, d, lo, t, v, g2, full_room(T, d, lo, n, t, g, eb, q, hq, hp)))

def empty_ok(~T: Data, op: E.Op<T>) -> K.StepOK(~T, ST.S0{}, op):
  match op:
    case E.Length{}:
      K.mk(~T, ST.S0{}, E.Length{}, ST.S0{}, E.ONat{0n}, {==}, {==}, {==})
    case E.PushFront{+x}:
      PU.first_front_ok(~T, x)
    case E.PushBack{+x}:
      PU.first_back_ok(~T, x)
    case E.PopFront{}:
      K.mk(~T, ST.S0{}, E.PopFront{}, ST.S0{}, E.OItem{Fail{E.EmptyDeque{}}}, {==}, {==}, {==})
    case E.PopBack{}:
      K.mk(~T, ST.S0{}, E.PopBack{}, ST.S0{}, E.OItem{Fail{E.EmptyDeque{}}}, {==}, {==}, {==})
    case E.PeekFront{}:
      K.mk(~T, ST.S0{}, E.PeekFront{}, ST.S0{}, E.OItem{Fail{E.EmptyDeque{}}}, {==}, {==}, {==})
    case E.PeekBack{}:
      K.mk(~T, ST.S0{}, E.PeekBack{}, ST.S0{}, E.OItem{Fail{E.EmptyDeque{}}}, {==}, {==}, {==})
    case E.ToList{}:
      K.mk(~T, ST.S0{}, E.ToList{}, ST.S0{}, E.OList{Nil{}}, {==}, {==}, {==})

def ring_ok(~T: Data, +d: Nat, +lo: Nat, +n: Nat, +t: AR.Tree<T>, op: E.Op<T>, +g: {ST.good(T, ST.Sh{d, lo, n, t}) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +hp: {pushok(T, q, op, ST.model(T, ST.Sh{d, lo, n, t})) == True{} : Bool}) -> K.StepOK(~T, ST.Sh{d, lo, n, t}, op):
  match op:
    case E.Length{}:
      RD.length_ok(~T, d, lo, n, t, g)
    case E.PushFront{+x}:
      pf_case(~T, d, lo, n, t, x, g, q, hq, hp, Nat.is_lt(n, SC.pow2(d)), {==})
    case E.PushBack{+x}:
      pb_case(~T, d, lo, n, t, x, g, q, hq, hp, Nat.is_lt(n, SC.pow2(d)), {==})
    case E.PopFront{}:
      RD.popf_ok(~T, d, lo, n, t, g)
    case E.PopBack{}:
      RD.popb_ok(~T, d, lo, n, t, g)
    case E.PeekFront{}:
      RD.peekf_ok(~T, d, lo, n, t, g)
    case E.PeekBack{}:
      RD.peekb_ok(~T, d, lo, n, t, g)
    case E.ToList{}:
      RD.tolist_ok(~T, d, lo, n, t, g)

def step_ok(~T: Data, sh: ST.Shadow<T>, op: E.Op<T>, +g: {ST.good(T, sh) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +hp: {pushok(T, q, op, ST.model(T, sh)) == True{} : Bool}) -> K.StepOK(~T, sh, op):
  match sh:
    case ST.S0{}:
      empty_ok(~T, op)
    case ST.Sh{+d, +lo, +n, +t}:
      ring_ok(~T, d, lo, n, t, op, g, q, hq, hp)
