# Retained proof dependency: history/retired-doubly-linked-list/proofs/dlist/insfacts.bend
# Only declarations needed by the LRU refinement are kept; no retired runtime is imported.
# Proof-only dependency extracted from retained LRU support; no retired collection API.
import Base
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import array_shift.bend as SH
import ../../../spec/common.bend as SC
import links_state.bend as ST
import links_links.bend as LK
import links_mu0.bend as MU0
import links_rmfacts.bend as RF
import links_core.bend as K

def f_notin(+ys: List<&2, Nat>, +f: Nat, +h: {ST.alllt(ys, f) == True{} : Bool}) -> {ST.lmem(f, ys) == False{} : Bool}:
  K.lmem_ge(ys, f, f, h, N.le_refl(f))


def alllt_succ(+ys: List<&2, Nat>, +f: Nat, +h: {ST.alllt(ys, f) == True{} : Bool}) -> {ST.alllt(ys, 1n+f) == True{} : Bool}:
  K.alllt_mono(ys, f, 1n+f, N.le_succ(f), h)


def nodup_ins(+x: List<&2, Nat>, +y: List<&2, Nat>, +f: Nat, +hf: {ST.lmem(f, SC.append(Nat, x, y)) == False{} : Bool}, +h: {ST.nodup(SC.append(Nat, x, y)) == True{} : Bool}) -> {ST.nodup(SC.append(Nat, x, Con{f, y})) == True{} : Bool}:
  match x:
    case Nil{}:
      L.and_intro(Bool.not(ST.lmem(f, y)), ST.nodup(y), L.subst(Bool, z => {Bool.not(z) == True{} : Bool}, False{}, ST.lmem(f, y), Equal.sym(Bool, ST.lmem(f, y), False{}, hf), {==}), h)
    case Con{+a, +t}:
      +ha = MU0.not_true(ST.lmem(a, SC.append(Nat, t, y)), L.and_left(Bool.not(ST.lmem(a, SC.append(Nat, t, y))), ST.nodup(SC.append(Nat, t, y)), h))
      +hfa = LK.or_false_l(Nat.is_eq(a, f), ST.lmem(f, SC.append(Nat, t, y)), hf)
      +hft = LK.or_false_r(Nat.is_eq(a, f), ST.lmem(f, SC.append(Nat, t, y)), hf)
      +hma = Equal.trans(Bool, ST.lmem(a, SC.append(Nat, t, Con{f, y})), ST.lmem(a, SC.append(Nat, t, y)), False{}, Equal.sym(Bool, ST.lmem(a, SC.append(Nat, t, y)), ST.lmem(a, SC.append(Nat, t, Con{f, y})), RF.lmem_cut(a, t, f, y, SH.ne_flip(a, f, hfa))), ha)
      L.and_intro(Bool.not(ST.lmem(a, SC.append(Nat, t, Con{f, y}))), ST.nodup(SC.append(Nat, t, Con{f, y})), L.subst(Bool, z => {Bool.not(z) == True{} : Bool}, False{}, ST.lmem(a, SC.append(Nat, t, Con{f, y})), Equal.sym(Bool, ST.lmem(a, SC.append(Nat, t, Con{f, y})), False{}, hma), {==}),
        nodup_ins(t, y, f, hft, L.and_right(Bool.not(ST.lmem(a, SC.append(Nat, t, y))), ST.nodup(SC.append(Nat, t, y)), h)))

# ---- the value arena ----
