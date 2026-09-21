import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/array.bend as AR
import ../graph/shift.bend as SH
import ../../spec/common.bend as SC
import ../../spec/doubly_linked_list.bend as DS
import ../../src/doubly_linked_list.bend as D
import ../../types/doubly_linked_list.bend as E
import ./state.bend as ST
import ./facts.bend as F
import ./links.bend as LK
import ./items.bend as IT
import ./alive.bend as AL
import ./nbrs.bend as NB
import ./mu0.bend as MU0
import ./split.bend as SP
import ./retarget.bend as RT
import ./tolist.bend as TLa

import ./tolist.bend as TLa
import ./rmfacts.bend as RF
import ./core.bend as K
import ./mut.bend as MU

# Splicing a fresh id f into the order x ++ y (f above every id).

def f_notin(+ys: List<&2, Nat>, +f: Nat, +h: {ST.alllt(ys, f) == True{} : Bool}) -> {ST.lmem(f, ys) == False{} : Bool}:
  K.lmem_ge(ys, f, f, h, N.le_refl(f))

def alllt_succ(+ys: List<&2, Nat>, +f: Nat, +h: {ST.alllt(ys, f) == True{} : Bool}) -> {ST.alllt(ys, 1n+f) == True{} : Bool}:
  K.alllt_mono(ys, f, 1n+f, N.le_succ(f), h)

def alllt_ins(+x: List<&2, Nat>, +y: List<&2, Nat>, +f: Nat, +h: {ST.alllt(SC.append(Nat, x, y), f) == True{} : Bool}) -> {ST.alllt(SC.append(Nat, x, Con{f, y}), 1n+f) == True{} : Bool}:
  SP.alllt_join(x, Con{f, y}, 1n+f, alllt_succ(x, f, TLa.alllt_l(x, y, f, h)), L.and_intro(Nat.is_lt(f, 1n+f), ST.alllt(y, 1n+f), N.lt_succ(f), alllt_succ(y, f, TLa.alllt_r(x, y, f, h))))

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

def lvi_pos(-T: Data, +xs: List<&2, Maybe<&2, T>>, +x: List<&2, Nat>, +y: List<&2, Nat>, +f: Nat, +m: Maybe<&2, T>, +q: Nat, +hq: {Nat.is_eq(f, q) == False{} : Bool}, +hold: {ST.beq(ST.is_some(T, ST.vat(T, xs, q)), ST.lmem(q, SC.append(Nat, x, y))) == True{} : Bool}) -> {ST.beq(ST.is_some(T, ST.vat(T, SC.update(Maybe<&2, T>, xs, f, m), q)), ST.lmem(q, SC.append(Nat, x, Con{f, y}))) == True{} : Bool}:
  L.subst(Maybe<&2, T>, mm => {ST.beq(ST.is_some(T, mm), ST.lmem(q, SC.append(Nat, x, Con{f, y}))) == True{} : Bool}, ST.vat(T, xs, q), ST.vat(T, SC.update(Maybe<&2, T>, xs, f, m), q), Equal.sym(Maybe<&2, T>, ST.vat(T, SC.update(Maybe<&2, T>, xs, f, m), q), ST.vat(T, xs, q), LK.vat_other(T, xs, f, m, q, hq)),
    L.subst(Bool, z => {ST.beq(ST.is_some(T, ST.vat(T, xs, q)), z) == True{} : Bool}, ST.lmem(q, SC.append(Nat, x, y)), ST.lmem(q, SC.append(Nat, x, Con{f, y})), RF.lmem_cut(q, x, f, y, hq), hold))

# The first k positions from p (all below f) keep their state.
def lv_ins(-T: Data, k: Nat, +xs: List<&2, Maybe<&2, T>>, +p: Nat, +x: List<&2, Nat>, +y: List<&2, Nat>, +f: Nat, +m: Maybe<&2, T>, +hf: {Nat.is_le(Nat.add(k, p), f) == True{} : Bool}, +h: {ST.lv(T, k, xs, p, SC.append(Nat, x, y)) == True{} : Bool}) -> {ST.lv(T, k, SC.update(Maybe<&2, T>, xs, f, m), p, SC.append(Nat, x, Con{f, y})) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+ +k1:
      +hp = N.lt_le_trans(p, 1n+Nat.add(k1, p), f, N.le_lt_trans(p, Nat.add(k1, p), 1n+Nat.add(k1, p), L.subst(Nat, z => {Nat.is_le(p, z) == True{} : Bool}, Nat.add(p, k1), Nat.add(k1, p), N.add_comm(p, k1), N.le_add_right(p, k1)), N.lt_succ(Nat.add(k1, p))), hf)
      +hne = SH.ne_flip(p, f, SH.ne_of_lt(p, f, hp))
      +h1 = L.and_left(ST.beq(ST.is_some(T, ST.vat(T, xs, p)), ST.lmem(p, SC.append(Nat, x, y))), ST.lv(T, k1, xs, 1n+p, SC.append(Nat, x, y)), h)
      +h2 = L.and_right(ST.beq(ST.is_some(T, ST.vat(T, xs, p)), ST.lmem(p, SC.append(Nat, x, y))), ST.lv(T, k1, xs, 1n+p, SC.append(Nat, x, y)), h)
      L.and_intro(ST.beq(ST.is_some(T, ST.vat(T, SC.update(Maybe<&2, T>, xs, f, m), p)), ST.lmem(p, SC.append(Nat, x, Con{f, y}))), ST.lv(T, k1, SC.update(Maybe<&2, T>, xs, f, m), 1n+p, SC.append(Nat, x, Con{f, y})),
        lvi_pos(T, xs, x, y, f, m, p, hne, h1),
        lv_ins(T, k1, xs, 1n+p, x, y, f, m, L.subst(Nat, z => {Nat.is_le(z, f) == True{} : Bool}, Nat.add(1n+k1, p), Nat.add(k1, 1n+p), Equal.sym(Nat, Nat.add(k1, 1n+p), Nat.add(1n+k1, p), N.add_succ(k1, p)), hf), h2))

# lv over one more position at the end.
def lv_snoc(-T: Data, k: Nat, +xs: List<&2, Maybe<&2, T>>, +p: Nat, +ord: List<&2, Nat>, +h: {ST.lv(T, k, xs, p, ord) == True{} : Bool}, +hl: {ST.beq(ST.is_some(T, ST.vat(T, xs, Nat.add(k, p))), ST.lmem(Nat.add(k, p), ord)) == True{} : Bool}) -> {ST.lv(T, 1n+k, xs, p, ord) == True{} : Bool}:
  match k:
    case 0n:
      L.and_intro(ST.beq(ST.is_some(T, ST.vat(T, xs, p)), ST.lmem(p, ord)), True{}, hl, {==})
    case 1n+ +k1:
      +h1 = L.and_left(ST.beq(ST.is_some(T, ST.vat(T, xs, p)), ST.lmem(p, ord)), ST.lv(T, k1, xs, 1n+p, ord), h)
      +h2 = L.and_right(ST.beq(ST.is_some(T, ST.vat(T, xs, p)), ST.lmem(p, ord)), ST.lv(T, k1, xs, 1n+p, ord), h)
      L.and_intro(ST.beq(ST.is_some(T, ST.vat(T, xs, p)), ST.lmem(p, ord)), ST.lv(T, 1n+k1, xs, 1n+p, ord), h1,
        lv_snoc(T, k1, xs, 1n+p, ord, h2, L.subst(Nat, z => {ST.beq(ST.is_some(T, ST.vat(T, xs, z)), ST.lmem(z, ord)) == True{} : Bool}, Nat.add(1n+k1, p), Nat.add(k1, 1n+p), Equal.sym(Nat, Nat.add(k1, 1n+p), Nat.add(1n+k1, p), N.add_succ(k1, p)), hl)))

def lv_new(-T: Data, +xs: List<&2, Maybe<&2, T>>, +fresh: Nat, +x: List<&2, Nat>, +y: List<&2, Nat>, +v: T, +hn: {Nat.is_lt(fresh, SC.length(Maybe<&2, T>, xs)) == True{} : Bool}, +h: {ST.lv(T, fresh, xs, 0n, SC.append(Nat, x, y)) == True{} : Bool}) -> {ST.lv(T, 1n+fresh, SC.update(Maybe<&2, T>, xs, fresh, Some{v}), 0n, SC.append(Nat, x, Con{fresh, y})) == True{} : Bool}:
  +xs2 = SC.update(Maybe<&2, T>, xs, fresh, Some{v})
  +hmem = Equal.trans(Bool, ST.lmem(fresh, SC.append(Nat, x, Con{fresh, y})), Bool.or(ST.lmem(fresh, x), Bool.or(Nat.is_eq(fresh, fresh), ST.lmem(fresh, y))), True{}, SP.lmem_app(fresh, x, Con{fresh, y}),
    AL.or_true_r(ST.lmem(fresh, x), Bool.or(Nat.is_eq(fresh, fresh), ST.lmem(fresh, y)), L.subst(Bool, z => {Bool.or(z, ST.lmem(fresh, y)) == True{} : Bool}, True{}, Nat.is_eq(fresh, fresh), Equal.sym(Bool, Nat.is_eq(fresh, fresh), True{}, N.is_eq_refl(fresh)), {==})))
  +hlast = L.subst(Nat, z => {ST.beq(ST.is_some(T, ST.vat(T, xs2, z)), ST.lmem(z, SC.append(Nat, x, Con{fresh, y}))) == True{} : Bool}, fresh, Nat.add(fresh, 0n), Equal.sym(Nat, Nat.add(fresh, 0n), fresh, N.add_zero(fresh)),
    L.subst(Maybe<&2, T>, mm => {ST.beq(ST.is_some(T, mm), ST.lmem(fresh, SC.append(Nat, x, Con{fresh, y}))) == True{} : Bool}, Some{v}, ST.vat(T, xs2, fresh), Equal.sym(Maybe<&2, T>, ST.vat(T, xs2, fresh), Some{v}, LK.vat_same(T, xs, fresh, Some{v}, hn)),
      L.subst(Bool, z => {ST.beq(True{}, z) == True{} : Bool}, True{}, ST.lmem(fresh, SC.append(Nat, x, Con{fresh, y})), Equal.sym(Bool, ST.lmem(fresh, SC.append(Nat, x, Con{fresh, y})), True{}, hmem), {==})))
  lv_snoc(T, fresh, xs2, 0n, SC.append(Nat, x, Con{fresh, y}), lv_ins(T, fresh, xs, 0n, x, y, fresh, Some{v}, L.subst(Nat, z => {Nat.is_le(z, fresh) == True{} : Bool}, fresh, Nat.add(fresh, 0n), Equal.sym(Nat, Nat.add(fresh, 0n), fresh, N.add_zero(fresh)), N.le_refl(fresh)), h), hlast)
