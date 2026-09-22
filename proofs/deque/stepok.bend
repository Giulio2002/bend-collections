import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/array.bend as AR
import ../spec/common.bend as SC
import ../spec/deque.bend as S
import ../../src/containers/deque.bend as DQ
import ../../src/containers/types/deque.bend as E
import ./ring.bend as R
import ./state.bend as ST
import ./grow.bend as G

# The one-step refinement statement and the facts every operation shares.
#
# StepOK(sh, op): the actual public step on the deque built from a good
# shadow sh lands on the deque built from another good shadow sh2, and
# (model(sh2), observation) is exactly the spec step on model(sh).

def StepOK(~T: Data, sh: ST.Shadow<T>, op: E.Op<T>) -> Type:
  Sigma<&1, &1, ST.Shadow<T>, sh2 => Sigma<&1, &1, E.Obs<T>, o => {DQ.step(~T, ST.real(T, sh), op) == (ST.real(T, sh2), o) : DQ.Deque<T> & E.Obs<T>} & ({ST.good(T, sh2) == True{} : Bool} & {(ST.model(T, sh2), o) == S.step(T, ST.model(T, sh), op) : List<&2, T> & E.Obs<T>})>>

def mk(~T: Data, -sh: ST.Shadow<T>, -op: E.Op<T>, sh2: ST.Shadow<T>, o: E.Obs<T>, e1: {DQ.step(~T, ST.real(T, sh), op) == (ST.real(T, sh2), o) : DQ.Deque<T> & E.Obs<T>}, e2: {ST.good(T, sh2) == True{} : Bool}, e3: {(ST.model(T, sh2), o) == S.step(T, ST.model(T, sh), op) : List<&2, T> & E.Obs<T>}) -> StepOK(~T, sh, op):
  (sh2, (o, (e1, (e2, e3))))

# ---- facts about a good ring Sh{d, lo, n, t} ----

def rlen(-T: Data, +d: Nat, +lo: Nat, +n: Nat, +t: AR.Tree<T>, +g: {ST.good(T, ST.Sh{d, lo, n, t}) == True{} : Bool}) -> {SC.length(T, R.rot(T, AR.slots(T, t), lo)) == SC.pow2(d) : Nat}:
  +el = ST.g_len(T, d, lo, n, t, g)
  Equal.trans(Nat, SC.length(T, R.rot(T, AR.slots(T, t), lo)), SC.length(T, AR.slots(T, t)), SC.pow2(d), R.rot_len(T, AR.slots(T, t), lo, L.subst(Nat, z => {Nat.is_le(lo, z) == True{} : Bool}, SC.pow2(d), SC.length(T, AR.slots(T, t)), Equal.sym(Nat, SC.length(T, AR.slots(T, t)), SC.pow2(d), el), N.lt_le(lo, SC.pow2(d), ST.g_lo(T, d, lo, n, t, g)))), el)

def mlen(-T: Data, +d: Nat, +lo: Nat, +n: Nat, +t: AR.Tree<T>, +g: {ST.good(T, ST.Sh{d, lo, n, t}) == True{} : Bool}) -> {SC.length(T, ST.model(T, ST.Sh{d, lo, n, t})) == n : Nat}:
  LL.sc_length_take(T, R.rot(T, AR.slots(T, t), lo), n, L.subst(Nat, z => {Nat.is_le(n, z) == True{} : Bool}, SC.pow2(d), SC.length(T, R.rot(T, AR.slots(T, t), lo)), Equal.sym(Nat, SC.length(T, R.rot(T, AR.slots(T, t), lo)), SC.pow2(d), rlen(T, d, lo, n, t, g)), ST.g_n(T, d, lo, n, t, g)))

# ring position j < 2^d is the slot value at wrap(lo + j)
def rat(-T: Data, +d: Nat, +lo: Nat, +n: Nat, +t: AR.Tree<T>, +j: Nat, +g: {ST.good(T, ST.Sh{d, lo, n, t}) == True{} : Bool}, +hj: {Nat.is_lt(j, SC.pow2(d)) == True{} : Bool}) -> {SC.nth(T, R.rot(T, AR.slots(T, t), lo), j) == Some{ST.vat(T, t, DQ.wrap(Nat.add(lo, j), SC.pow2(d)))} : Maybe<&2, T>}:
  G.ring_at(T, d, lo, j, t, ST.g_perfect(T, d, lo, n, t, g), ST.g_lo(T, d, lo, n, t, g), hj)

def wrap_lo(+lo: Nat, +c: Nat, +hlo: {Nat.is_lt(lo, c) == True{} : Bool}) -> {DQ.wrap(Nat.add(lo, 0n), c) == lo : Nat}:
  %Equal.sym(Nat, Nat.add(lo, 0n), lo, N.add_zero(lo)) : {DQ.wrap(_, c) == lo : Nat}
  R.wrap_small(lo, c, hlo)

# ring position 0 is slot lo
def r0(-T: Data, +d: Nat, +lo: Nat, +n: Nat, +t: AR.Tree<T>, +g: {ST.good(T, ST.Sh{d, lo, n, t}) == True{} : Bool}) -> {SC.nth(T, R.rot(T, AR.slots(T, t), lo), 0n) == Some{ST.vat(T, t, lo)} : Maybe<&2, T>}:
  +hlo = ST.g_lo(T, d, lo, n, t, g)
  L.subst(Nat, z => {SC.nth(T, R.rot(T, AR.slots(T, t), lo), 0n) == Some{ST.vat(T, t, z)} : Maybe<&2, T>}, DQ.wrap(Nat.add(lo, 0n), SC.pow2(d)), lo, wrap_lo(lo, SC.pow2(d), hlo), rat(T, d, lo, n, t, 0n, g, N.le_lt_trans(0n, lo, SC.pow2(d), N.zero_le(lo), hlo)))

def head_take(-T: Data, +r: List<&2, T>, +m: Nat, +x: T, +e: {SC.nth(T, r, 0n) == Some{x} : Maybe<&2, T>}) -> {SC.head(T, SC.take(T, r, 1n+m)) == Some{x} : Maybe<&2, T>}:
  match r:
    case Nil{}:
      Empty.absurd({SC.head(T, SC.take(T, Nil{}, 1n+m)) == Some{x} : Maybe<&2, T>}, L.none_some(T, x, e))
    case Con{y, t}:
      e

def pb_spec(-T: Data, +ys: List<&2, T>, +m: Nat, +h: {SC.length(T, ys) == 1n+m : Nat}) -> {S.pop_back(T, ys) == (SC.init(T, ys), E.OItem{S.item(T, SC.last(T, ys))}) : List<&2, T> & E.Obs<T>}:
  match ys:
    case Nil{}:
      Empty.absurd({S.pop_back(T, Nil{}) == (SC.init(T, Nil{}), E.OItem{S.item(T, SC.last(T, Nil{}))}) : List<&2, T> & E.Obs<T>}, N.zero_succ(m, h))
    case Con{h0, t0}:
      {==}

def pf_spec(-T: Data, +ys: List<&2, T>, +x: T, +e: {SC.nth(T, ys, 0n) == Some{x} : Maybe<&2, T>}) -> {S.pop_front(T, ys) == (SC.tail(T, ys), E.OItem{Done{x}}) : List<&2, T> & E.Obs<T>}:
  match ys:
    case Nil{}:
      Empty.absurd({S.pop_front(T, Nil{}) == (SC.tail(T, Nil{}), E.OItem{Done{x}}) : List<&2, T> & E.Obs<T>}, L.none_some(T, x, e))
    case Con{+y, +t0}:
      %L.some_inj(T, y, x, e) : {(t0, E.OItem{Done{y}}) == (t0, E.OItem{Done{_}}) : List<&2, T> & E.Obs<T>}
      {==}
