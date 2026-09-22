# Retained proof dependency: history/retired-doubly-linked-list/proofs/dlist/tset.bend
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
import links_items.bend as IT
import links_retarget.bend as RT

def tpup(+depth: Nat, +t: AR.Tree<U32>, b: List<&2, Nat>, +v: U32) -> AR.Tree<U32>:
  match b:
    case Nil{}:
      t
    case Con{+y, r}:
      AR.upd(U32, depth, t, y, v)


def tnup(+depth: Nat, +t: AR.Tree<U32>, a: List<&2, Nat>, +v: U32) -> AR.Tree<U32>:
  match a:
    case Nil{}:
      t
    case Con{+x, r}:
      AR.upd(U32, depth, t, ST.lst_or(r, x), v)


def tpup_pf(+depth: Nat, +t: AR.Tree<U32>, +b: List<&2, Nat>, +v: U32, +pf: {AR.perfect(U32, depth, t) == True{} : Bool}) -> {AR.perfect(U32, depth, tpup(depth, t, b, v)) == True{} : Bool}:
  match b:
    case Nil{}:
      pf
    case Con{+y, +r}:
      AR.upd_perfect(U32, depth, t, y, v, pf)


def tnup_pf(+depth: Nat, +t: AR.Tree<U32>, +a: List<&2, Nat>, +v: U32, +pf: {AR.perfect(U32, depth, t) == True{} : Bool}) -> {AR.perfect(U32, depth, tnup(depth, t, a, v)) == True{} : Bool}:
  match a:
    case Nil{}:
      pf
    case Con{+x, +r}:
      AR.upd_perfect(U32, depth, t, ST.lst_or(r, x), v, pf)


def tpup_slots(+depth: Nat, +t: AR.Tree<U32>, +b: List<&2, Nat>, +v: U32, +pf: {AR.perfect(U32, depth, t) == True{} : Bool}, +hl: {ST.alllt(b, SC.pow2(depth)) == True{} : Bool}) -> {AR.slots(U32, tpup(depth, t, b, v)) == RT.pupd(AR.slots(U32, t), b, v) : List<&2, U32>}:
  match b:
    case Nil{}:
      {==}
    case Con{+y, +r}:
      AR.upd_slots(U32, depth, t, y, v, IT.lt_head(y, r, SC.pow2(depth), hl), pf)


def tnup_slots(+depth: Nat, +t: AR.Tree<U32>, +a: List<&2, Nat>, +v: U32, +pf: {AR.perfect(U32, depth, t) == True{} : Bool}, +hl: {ST.alllt(a, SC.pow2(depth)) == True{} : Bool}) -> {AR.slots(U32, tnup(depth, t, a, v)) == RT.nupd(AR.slots(U32, t), a, v) : List<&2, U32>}:
  match a:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      AR.upd_slots(U32, depth, t, ST.lst_or(r, x), v, RT.lst_lt(r, x, SC.pow2(depth), hl), pf)

# Writing v at the element a link y points to.

def set_at_link(+depth: Nat, +t: AR.Tree<U32>, +y: Nat, +v: U32, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +pf: {AR.perfect(U32, depth, t) == True{} : Bool}, +hy: {Nat.is_lt(y, SC.pow2(depth)) == True{} : Bool}) -> {D.set_next(AR.thaw(U32, t), ST.ln(y), v) == AR.thaw(U32, AR.upd(U32, depth, t, y, v)) : Array<U32>}:
  +ry = F.id_nat(y, depth, hd, hy)
  Equal.trans(Array<U32>, D.set_next_go(AR.thaw(U32, t), ST.ln(y), v, U32.is_eq(ST.ln(y), D.nil())), Array.set(U32, AR.thaw(U32, t), U32.from_nat(y), v), AR.thaw(U32, AR.upd(U32, depth, t, y, v)),
    Equal.trans(Array<U32>, D.set_next_go(AR.thaw(U32, t), ST.ln(y), v, U32.is_eq(ST.ln(y), D.nil())), D.set_next_go(AR.thaw(U32, t), ST.ln(y), v, False{}), Array.set(U32, AR.thaw(U32, t), U32.from_nat(y), v),
      Equal.cong(Bool, Array<U32>, b => D.set_next_go(AR.thaw(U32, t), ST.ln(y), v, b), U32.is_eq(ST.ln(y), D.nil()), False{}, F.ln_ne_nil(y, depth, hd, hy)),
      Equal.cong(U32, Array<U32>, z => Array.set(U32, AR.thaw(U32, t), z, v), D.slot(ST.ln(y)), U32.from_nat(y), F.slot_ln(y, depth, hd, hy))),
    Equal.trans(Array<U32>, Array.set(U32, AR.thaw(U32, t), U32.from_nat(y), v), AR.thaw(U32, AR.upd(U32, depth, t, U32.to_nat(U32.from_nat(y)), v)), AR.thaw(U32, AR.upd(U32, depth, t, y, v)),
      AR.set(U32, depth, t, U32.from_nat(y), v, ST.lat(AR.slots(U32, t), y), N.le_lt_trans(depth, 31n, 32n, hd, N.lt_succ(31n)),
        L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(depth)) == True{} : Bool}, y, U32.to_nat(U32.from_nat(y)), Equal.sym(Nat, U32.to_nat(U32.from_nat(y)), y, ry), hy),
        L.subst(Nat, z => {SC.nth(U32, AR.slots(U32, t), z) == Some{ST.lat(AR.slots(U32, t), y)} : Maybe<&2, U32>}, y, U32.to_nat(U32.from_nat(y)), Equal.sym(Nat, U32.to_nat(U32.from_nat(y)), y, ry), AS2.tsat(U32, depth, t, y, 0, pf, hy)),
        pf),
      Equal.cong(Nat, Array<U32>, z => AR.thaw(U32, AR.upd(U32, depth, t, z, v)), U32.to_nat(U32.from_nat(y)), y, ry)))


def sn_first(+depth: Nat, +t: AR.Tree<U32>, +b: List<&2, Nat>, +v: U32, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +pf: {AR.perfect(U32, depth, t) == True{} : Bool}, +hl: {ST.alllt(b, SC.pow2(depth)) == True{} : Bool}) -> {D.set_next(AR.thaw(U32, t), ST.hd_or(b, D.nil()), v) == AR.thaw(U32, tpup(depth, t, b, v)) : Array<U32>}:
  match b:
    case Nil{}:
      {==}
    case Con{+y, +r}:
      set_at_link(depth, t, y, v, hd, pf, IT.lt_head(y, r, SC.pow2(depth), hl))


def sn_last(+depth: Nat, +t: AR.Tree<U32>, +a: List<&2, Nat>, +v: U32, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +pf: {AR.perfect(U32, depth, t) == True{} : Bool}, +hl: {ST.alllt(a, SC.pow2(depth)) == True{} : Bool}) -> {D.set_next(AR.thaw(U32, t), LK.lastl(a, D.nil()), v) == AR.thaw(U32, tnup(depth, t, a, v)) : Array<U32>}:
  match a:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      set_at_link(depth, t, ST.lst_or(r, x), v, hd, pf, RT.lst_lt(r, x, SC.pow2(depth), hl))
