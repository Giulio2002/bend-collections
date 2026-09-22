# Retained proof dependency: history/retired-doubly-linked-list/proofs/dlist/state.bend
# Only declarations needed by the LRU refinement are kept; no retired runtime is imported.
# Proof-only dependency extracted from retained LRU support; no retired collection API.
import Base
import ../../lib/logic.bend as L
import ../../../spec/common.bend as SC
import link_primitives.bend as D

def ln(+p: Nat) -> U32:
  U32.from_nat(1n+p)

# ---- the ends of the order, as links ----


def lst_or(t: List<&2, Nat>, +x: Nat) -> Nat:
  match t:
    case Nil{}:
      x
    case Con{+y, r}:
      lst_or(r, y)


def hd(xs: List<&2, Nat>) -> U32:
  match xs:
    case Nil{}:
      D.nil()
    case Con{+x, t}:
      ln(x)


def lst(xs: List<&2, Nat>) -> U32:
  match xs:
    case Nil{}:
      D.nil()
    case Con{+x, t}:
      ln(lst_or(t, x))

# the link to the first id of xs, or e when xs is empty

def hd_or(xs: List<&2, Nat>, +e: U32) -> U32:
  match xs:
    case Nil{}:
      e
    case Con{+x, t}:
      ln(x)


def lat(+xs: List<&2, U32>, +p: Nat) -> U32:
  L.some_value(U32, SC.nth(U32, xs, p), 0)

# ---- the abstraction ----


def lmem(+i: Nat, xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{+x, t}:
      Bool.or(Nat.is_eq(x, i), lmem(i, t))


def nodup(xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, +t}:
      Bool.and(Bool.not(lmem(x, t)), nodup(t))


def alllt(xs: List<&2, Nat>, +n: Nat) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, t}:
      Bool.and(Nat.is_lt(x, n), alllt(t, n))


def lk(xs: List<&2, Nat>, +prev: U32, +e: U32, +ps: List<&2, U32>, +ns: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, +t}:
      Bool.and(U32.is_eq(lat(ps, x), prev), Bool.and(U32.is_eq(lat(ns, x), hd_or(t, e)), lk(t, ln(x), e, ps, ns)))
