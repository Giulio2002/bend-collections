# Retained proof dependency: history/retired-doubly-linked-list/proofs/dlist/tolist.bend
# Only declarations needed by the LRU refinement are kept; no retired runtime is imported.
# Proof-only dependency extracted from retained LRU support; no retired collection API.
import Base
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../../lib/array.bend as AR
import array_ashift.bend as AS2
import ../../../spec/common.bend as SC
import link_primitives.bend as D
import links_state.bend as ST
import links_facts.bend as F
import links_links.bend as LK
import links_nbrs.bend as NB

def lsnoc(+t: List<&2, Nat>, +y: Nat, +x: Nat) -> {ST.ln(ST.lst_or(SC.append(Nat, t, Con{x, Nil{}}), y)) == ST.ln(x) : U32}:
  match t:
    case Nil{}:
      {==}
    case Con{+z, +r}:
      lsnoc(r, z, x)


def lastl_snoc(+a: List<&2, Nat>, +x: Nat, +pv: U32) -> {LK.lastl(SC.append(Nat, a, Con{x, Nil{}}), pv) == ST.ln(x) : U32}:
  match a:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      lsnoc(t, y, x)


def lst_lastl(+ord: List<&2, Nat>) -> {ST.lst(ord) == LK.lastl(ord, D.nil()) : U32}:
  match ord:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      {==}


def get_at(-T: Data, +depth: Nat, +t: AR.Tree<T>, +x: Nat, +d: T, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +pf: {AR.perfect(T, depth, t) == True{} : Bool}, +hx: {Nat.is_lt(x, SC.pow2(depth)) == True{} : Bool}) -> {Array.get(T, AR.thaw(T, t), U32.from_nat(x)) == (AR.thaw(T, t), L.some_value(T, SC.nth(T, AR.slots(T, t), x), d)) : Array<T> & T}:
  +rx = F.id_nat(x, depth, hd, hx)
  AR.get(T, depth, t, U32.from_nat(x), L.some_value(T, SC.nth(T, AR.slots(T, t), x), d), N.le_lt_trans(depth, 31n, 32n, hd, N.lt_succ(31n)),
    L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(depth)) == True{} : Bool}, x, U32.to_nat(U32.from_nat(x)), Equal.sym(Nat, U32.to_nat(U32.from_nat(x)), x, rx), hx),
    L.subst(Nat, z => {SC.nth(T, AR.slots(T, t), z) == Some{L.some_value(T, SC.nth(T, AR.slots(T, t), x), d)} : Maybe<&2, T>}, x, U32.to_nat(U32.from_nat(x)), Equal.sym(Nat, U32.to_nat(U32.from_nat(x)), x, rx), AS2.tsat(T, depth, t, x, d, pf, hx)),
    pf)

# The value slot of a live id x holds Some of its value.

def alllt_l(+a: List<&2, Nat>, +b: List<&2, Nat>, +n: Nat, +h: {ST.alllt(SC.append(Nat, a, b), n) == True{} : Bool}) -> {ST.alllt(a, n) == True{} : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      L.and_intro(Nat.is_lt(y, n), ST.alllt(t, n), L.and_left(Nat.is_lt(y, n), ST.alllt(SC.append(Nat, t, b), n), h), alllt_l(t, b, n, L.and_right(Nat.is_lt(y, n), ST.alllt(SC.append(Nat, t, b), n), h)))


def alllt_r(+a: List<&2, Nat>, +b: List<&2, Nat>, +n: Nat, +h: {ST.alllt(SC.append(Nat, a, b), n) == True{} : Bool}) -> {ST.alllt(b, n) == True{} : Bool}:
  match a:
    case Nil{}:
      h
    case Con{+y, +t}:
      alllt_r(t, b, n, L.and_right(Nat.is_lt(y, n), ST.alllt(SC.append(Nat, t, b), n), h))

# One step back from the link to a live x.

def lk_single_p(+x: Nat, +pv: U32, +e: U32, +ps: List<&2, U32>, +ns: List<&2, U32>, +h: {ST.lk(Con{x, Nil{}}, pv, e, ps, ns) == True{} : Bool}) -> {ST.lat(ps, x) == pv : U32}:
  NB.ueq_true(ST.lat(ps, x), pv, L.and_left(U32.is_eq(ST.lat(ps, x), pv), Bool.and(U32.is_eq(ST.lat(ns, x), e), True{}), h))
