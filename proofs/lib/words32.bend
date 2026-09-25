import Base
import ./logic.bend as L
import ./u32alg.bend as A
import ./u32.bend as UW
import ./word.bend as WD
import ./u32div.bend as UD
import ./nat.bend as N
import ../../spec/lib/common.bend as SC
import ../../src/containers/hash_table.bend as H
import ./arith.bend as AT

# U32 word facts over a symbolic 1 (so 2^32 is never unfolded): bounds of
# link words, increments, equality symmetry, and the 32-bit tables read and
# updated by index.

def eq_sym_c(+a: U32, +b: U32, +c: Bool, +hc: {U32.is_eq(a, b) == c : Bool}, +d: Bool, +hd: {U32.is_eq(b, a) == d : Bool}) -> {c == d : Bool}:
  match c d:
    case True{} True{}:
      {==}
    case False{} False{}:
      {==}
    case True{} False{}:
      Empty.absurd({True{} == False{} : Bool}, L.true_false(Equal.trans(Bool, True{}, U32.is_eq(b, a), False{}, L.subst(U32, z => {True{} == U32.is_eq(b, z) : Bool}, b, a, Equal.sym(U32, a, b, A.eq_of(a, b, hc)), Equal.sym(Bool, U32.is_eq(b, b), True{}, UW.u32_eq_refl(b))), hd)))
    case False{} True{}:
      Empty.absurd({False{} == True{} : Bool}, L.false_true(Equal.trans(Bool, False{}, U32.is_eq(a, b), True{}, Equal.sym(Bool, U32.is_eq(a, b), False{}, hc), L.subst(U32, z => {U32.is_eq(a, z) == True{} : Bool}, a, b, Equal.sym(U32, b, a, A.eq_of(b, a, hd)), UW.u32_eq_refl(a)))))

def eq_sym_u32(+a: U32, +b: U32) -> {U32.is_eq(a, b) == U32.is_eq(b, a) : Bool}:
  eq_sym_c(a, b, U32.is_eq(a, b), {==}, U32.is_eq(b, a), {==})

def inc_val(+one: Nat, +h1: {one == 1n : Nat}, +i: U32, +h: {Nat.is_lt(1n+UD.v(i), WD.sc(32n, one)) == True{} : Bool}) -> {UD.v(U32.inc(i)) == 1n+UD.v(i) : Nat}:
  match i:
    case U32{+w}:
      +hw = L.subst(Nat, z => {Nat.is_lt(1n+z, WD.sc(32n, one)) == True{} : Bool}, UD.v(U32{w}), WD.uw(32n, w), UD.vw(w), h)
      Equal.trans(Nat, UD.v(U32{Word.inc(32n, w)}), WD.uw(32n, Word.inc(32n, w)), 1n+UD.v(U32{w}), UD.vw(Word.inc(32n, w)), Equal.trans(Nat, WD.uw(32n, Word.inc(32n, w)), 1n+WD.uw(32n, w), 1n+UD.v(U32{w}), WD.inc_exact(32n, one, h1, w, hw), Equal.cong(Nat, Nat, z => 1n+z, WD.uw(32n, w), UD.v(U32{w}), Equal.sym(Nat, UD.v(U32{w}), WD.uw(32n, w), UD.vw(w)))))

def link_val(+one: Nat, +h1: {one == 1n : Nat}, +s: U32, +hs: {Nat.is_lt(1n+UD.v(s), WD.sc(32n, one)) == True{} : Bool}) -> {UD.v(H.link(s)) == 1n+UD.v(s) : Nat}:
  inc_val(one, h1, s, hs)

def link_nz_c(+one: Nat, +h1: {one == 1n : Nat}, +s: U32, +hs: {Nat.is_lt(1n+UD.v(s), WD.sc(32n, one)) == True{} : Bool}, +c: Bool, +hc: {U32.is_eq(H.link(s), 0) == c : Bool}) -> {c == False{} : Bool}:
  match c:
    case False{}:
      {==}
    case True{}:
      +e0 = Equal.cong(U32, Nat, z => UD.v(z), H.link(s), 0, A.eq_of(H.link(s), 0, hc))
      Empty.absurd({True{} == False{} : Bool}, N.succ_zero(UD.v(s), Equal.trans(Nat, 1n+UD.v(s), UD.v(H.link(s)), 0n, Equal.sym(Nat, UD.v(H.link(s)), 1n+UD.v(s), link_val(one, h1, s, hs)), e0)))

def link_nz(+one: Nat, +h1: {one == 1n : Nat}, +s: U32, +hs: {Nat.is_lt(1n+UD.v(s), WD.sc(32n, one)) == True{} : Bool}) -> {U32.is_eq(H.link(s), 0) == False{} : Bool}:
  link_nz_c(one, h1, s, hs, U32.is_eq(H.link(s), 0), {==})

def nth0(tb: List<&2, U32>, +i: Nat) -> U32:
  match tb i:
    case Nil{} _:
      0
    case Con{x, t} 0n:
      x
    case Con{x, t} 1n+p:
      nth0(t, p)

def nth_some(+tb: List<&2, U32>, +i: Nat, +h: {Nat.is_lt(i, SC.length(U32, tb)) == True{} : Bool}) -> {SC.nth(U32, tb, i) == Some{nth0(tb, i)} : Maybe<&2, U32>}:
  match tb i:
    case Nil{} _:
      Empty.absurd({SC.nth(U32, Nil{}, i) == Some{nth0(Nil{}, i)} : Maybe<&2, U32>}, N.lt_zero_absurd(i, h))
    case Con{x, t} 0n:
      {==}
    case Con{x, t} 1n+p:
      nth_some(t, p, h)

def nth0_upd_same(+xs: List<&2, U32>, +i: Nat, +v: U32, +h: {Nat.is_lt(i, SC.length(U32, xs)) == True{} : Bool}) -> {nth0(SC.update(U32, xs, i, v), i) == v : U32}:
  match xs i:
    case Nil{} _:
      Empty.absurd({nth0(SC.update(U32, Nil{}, i, v), i) == v : U32}, N.lt_zero_absurd(i, h))
    case Con{x, t} 0n:
      {==}
    case Con{x, t} 1n+p:
      nth0_upd_same(t, p, v, h)

def nth0_upd_other(+xs: List<&2, U32>, +i: Nat, +j: Nat, +v: U32, +h: {Nat.is_eq(i, j) == False{} : Bool}) -> {nth0(SC.update(U32, xs, i, v), j) == nth0(xs, j) : U32}:
  match xs i j:
    case Nil{} _ _:
      {==}
    case Con{x, r} 0n 0n:
      Empty.absurd({nth0(SC.update(U32, Con{x, r}, 0n, v), 0n) == nth0(Con{x, r}, 0n) : U32}, L.true_false(h))
    case Con{x, r} 0n 1n+q:
      {==}
    case Con{x, r} 1n+p 0n:
      {==}
    case Con{x, r} 1n+p 1n+q:
      nth0_upd_other(r, p, q, v, h)

def pow_one(+one: Nat, +h1: {one == 1n : Nat}, +d: Nat) -> {SC.pow2(d) == WD.sc(d, one) : Nat}:
  Equal.trans(Nat, SC.pow2(d), WD.sc(d, 1n), WD.sc(d, one), UW.pow2_scale(d), Equal.cong(Nat, Nat, o => WD.sc(d, o), 1n, one, Equal.sym(Nat, one, 1n, h1)))

def pow_le32(+one: Nat, +h1: {one == 1n : Nat}, +d: Nat, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}) -> {Nat.is_le(SC.pow2(d), WD.sc(32n, one)) == True{} : Bool}:
  +j = Nat.sub(32n, d)
  +e = Equal.trans(Nat, WD.sc(32n, one), WD.sc(Nat.add(d, j), one), WD.sc(d, WD.sc(j, one)), Equal.cong(Nat, Nat, z => WD.sc(z, one), 32n, Nat.add(d, j), Equal.sym(Nat, Nat.add(d, j), 32n, N.sub_add(32n, d, N.lt_le(d, 32n, hd)))), AT.sc_idx(d, j, one))
  L.subst(Nat, z => {Nat.is_le(SC.pow2(d), z) == True{} : Bool}, WD.sc(d, WD.sc(j, one)), WD.sc(32n, one), Equal.sym(Nat, WD.sc(32n, one), WD.sc(d, WD.sc(j, one)), e), L.subst(Nat, z => {Nat.is_le(z, WD.sc(d, WD.sc(j, one))) == True{} : Bool}, WD.sc(d, one), SC.pow2(d), Equal.sym(Nat, SC.pow2(d), WD.sc(d, one), pow_one(one, h1, d)), AT.sc_le(d, one, WD.sc(j, one), AT.le_sc(j, one))))

def bound32(+one: Nat, +h1: {one == 1n : Nat}, +x: Nat, +d: Nat, +hd: {Nat.is_lt(1n+d, 32n) == True{} : Bool}, +hx: {Nat.is_lt(x, SC.pow2(d)) == True{} : Bool}) -> {Nat.is_lt(1n+x, WD.sc(32n, one)) == True{} : Bool}:
  N.le_lt_trans(1n+x, SC.pow2(d), WD.sc(32n, one), N.lt_succ_le_succ(x, SC.pow2(d), hx), N.lt_le_trans(SC.pow2(d), SC.pow2(1n+d), WD.sc(32n, one), N.pow2_lt_succ(d), pow_le32(one, h1, 1n+d, hd)))
