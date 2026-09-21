import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/array.bend as A
import ../../spec/common.bend as SC
import ../../src/union_find.bend as U
import ./arr.bend as AR

# The constructor's arenas are filled by FLAT loops (src/union_find.bend
# iota_go / solo_go: write slot j := f(j) for j = k-1 .. 0 into a uniform
# block), so that every operation that materialises a lazy structure still
# compiles to a native loop. This file proves what such a loop computes:
#   fill      the slot-list mirror of the loop, and its slot-wise content
#   tfill     the mirror-tree form, whose slot list is `fill`
#   iota/solo each executable loop IS `tfill` on the thawed arena
# init.bend takes `tfill` of the uniform block as the constructor's mirror
# trees and uses exactly the facts proved here: they are perfect and slot j
# holds f(j) (the root j, resp. the member list [j]).

def fill(~T: Data, ~f: Nat -> T, k: Nat, xs: List<&2, T>) -> List<&2, T>:
  match k:
    case 0n:
      xs
    case 1n+ +j:
      fill(~T, ~f, j, SC.update(T, xs, j, f(j)))

def len_fill(~T: Data, ~f: Nat -> T, k: Nat, +xs: List<&2, T>) -> {SC.length(T, fill(~T, ~f, k, xs)) == SC.length(T, xs) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+ +j:
      Equal.trans(Nat, SC.length(T, fill(~T, ~f, j, SC.update(T, xs, j, f(j)))), SC.length(T, SC.update(T, xs, j, f(j))), SC.length(T, xs),
        len_fill(~T, ~f, j, SC.update(T, xs, j, f(j))),
        LL.length_update(T, xs, j, f(j)))

# Slots at or above k are untouched.
def fill_above(~T: Data, ~f: Nat -> T, k: Nat, +xs: List<&2, T>, +j: Nat, +h: {Nat.is_le(k, j) == True{} : Bool}) -> {SC.nth(T, fill(~T, ~f, k, xs), j) == SC.nth(T, xs, j) : Maybe<&2, T>}:
  match k:
    case 0n:
      {==}
    case 1n+ +i:
      +lt = N.succ_le_lt(i, j, h)
      Equal.trans(Maybe<&2, T>, SC.nth(T, fill(~T, ~f, i, SC.update(T, xs, i, f(i))), j), SC.nth(T, SC.update(T, xs, i, f(i)), j), SC.nth(T, xs, j),
        fill_above(~T, ~f, i, SC.update(T, xs, i, f(i)), j, N.lt_le(i, j, lt)),
        LL.nth_update_other(T, xs, i, j, f(i), N.is_eq_lt(i, j, lt)))

def fb_case(~T: Data, ~f: Nat -> T, +i: Nat, +xs: List<&2, T>, +j: Nat, +hj: {Nat.is_lt(j, 1n+i) == True{} : Bool}, +hk: {Nat.is_le(1n+i, SC.length(T, xs)) == True{} : Bool}, b: Bool, +eb: {Nat.is_lt(j, i) == b : Bool}, ih: @+q: {Nat.is_lt(j, i) == True{} : Bool} -> {SC.nth(T, fill(~T, ~f, i, SC.update(T, xs, i, f(i))), j) == Some{f(j)} : Maybe<&2, T>}) -> {SC.nth(T, fill(~T, ~f, i, SC.update(T, xs, i, f(i))), j) == Some{f(j)} : Maybe<&2, T>}:
  match b:
    case True{}:
      ih(eb)
    case False{}:
      +eji = N.le_antisym(j, i, N.lt_succ_le(j, i, hj), N.not_lt_le(j, i, eb))
      +at_i = Equal.trans(Maybe<&2, T>, SC.nth(T, fill(~T, ~f, i, SC.update(T, xs, i, f(i))), i), SC.nth(T, SC.update(T, xs, i, f(i)), i), Some{f(i)},
        fill_above(~T, ~f, i, SC.update(T, xs, i, f(i)), i, N.le_refl(i)),
        LL.nth_update_same(T, xs, i, f(i), N.lt_le_trans(i, 1n+i, SC.length(T, xs), N.lt_succ(i), hk)))
      L.subst(Nat, z => {SC.nth(T, fill(~T, ~f, i, SC.update(T, xs, i, f(i))), z) == Some{f(z)} : Maybe<&2, T>}, i, j, Equal.sym(Nat, j, i, eji), at_i)

# Slots below k hold f(slot).
def fill_below(~T: Data, ~f: Nat -> T, k: Nat, +xs: List<&2, T>, +j: Nat, +hj: {Nat.is_lt(j, k) == True{} : Bool}, +hk: {Nat.is_le(k, SC.length(T, xs)) == True{} : Bool}) -> {SC.nth(T, fill(~T, ~f, k, xs), j) == Some{f(j)} : Maybe<&2, T>}:
  match k:
    case 0n:
      Empty.absurd({SC.nth(T, xs, j) == Some{f(j)} : Maybe<&2, T>}, N.lt_zero_absurd(j, hj))
    case 1n+ +i:
      +hk2 = Equal.trans(Nat, SC.length(T, SC.update(T, xs, i, f(i))), SC.length(T, xs), SC.length(T, xs), LL.length_update(T, xs, i, f(i)), {==})
      fb_case(~T, ~f, i, xs, j, hj, hk, Nat.is_lt(j, i), {==},
        q => fill_below(~T, ~f, i, SC.update(T, xs, i, f(i)), j, q,
          L.subst(Nat, z => {Nat.is_le(i, z) == True{} : Bool}, SC.length(T, xs), SC.length(T, SC.update(T, xs, i, f(i))), Equal.sym(Nat, SC.length(T, SC.update(T, xs, i, f(i))), SC.length(T, xs), hk2),
            N.le_trans(i, 1n+i, SC.length(T, xs), N.le_succ(i), hk))))

# ---- the mirror tree of the loop ----

def tfill(~T: Data, ~f: Nat -> T, +d: Nat, k: Nat, t: A.Tree<T>) -> A.Tree<T>:
  match k:
    case 0n:
      t
    case 1n+ +j:
      tfill(~T, ~f, d, j, A.upd(T, d, t, j, f(j)))

def tfill_perfect(~T: Data, ~f: Nat -> T, +d: Nat, k: Nat, +t: A.Tree<T>, +pf: {A.perfect(T, d, t) == True{} : Bool}) -> {A.perfect(T, d, tfill(~T, ~f, d, k, t)) == True{} : Bool}:
  match k:
    case 0n:
      pf
    case 1n+ +j:
      tfill_perfect(~T, ~f, d, j, A.upd(T, d, t, j, f(j)), A.upd_perfect(T, d, t, j, f(j), pf))

def tfill_slots(~T: Data, ~f: Nat -> T, +d: Nat, k: Nat, +t: A.Tree<T>, +hk: {Nat.is_le(k, SC.pow2(d)) == True{} : Bool}, +pf: {A.perfect(T, d, t) == True{} : Bool}) -> {A.slots(T, tfill(~T, ~f, d, k, t)) == fill(~T, ~f, k, A.slots(T, t)) : List<&2, T>}:
  match k:
    case 0n:
      {==}
    case 1n+ +j:
      +hj = N.succ_le_lt(j, SC.pow2(d), hk)
      Equal.trans(List<&2, T>, A.slots(T, tfill(~T, ~f, d, j, A.upd(T, d, t, j, f(j)))), fill(~T, ~f, j, A.slots(T, A.upd(T, d, t, j, f(j)))), fill(~T, ~f, j, SC.update(T, A.slots(T, t), j, f(j))),
        tfill_slots(~T, ~f, d, j, A.upd(T, d, t, j, f(j)), N.lt_le(j, SC.pow2(d), hj), A.upd_perfect(T, d, t, j, f(j), pf)),
        Equal.cong(List<&2, T>, List<&2, T>, z => fill(~T, ~f, j, z), A.slots(T, A.upd(T, d, t, j, f(j))), SC.update(T, A.slots(T, t), j, f(j)), A.upd_slots(T, d, t, j, f(j), hj, pf)))

# Every slot j < 2^d of the full loop's result holds f(j).
def tfill_nth(~T: Data, ~f: Nat -> T, +d: Nat, +t: A.Tree<T>, +j: Nat, +hj: {Nat.is_lt(j, SC.pow2(d)) == True{} : Bool}, +pt: {A.perfect(T, d, t) == True{} : Bool}) -> {SC.nth(T, A.slots(T, tfill(~T, ~f, d, SC.pow2(d), t)), j) == Some{f(j)} : Maybe<&2, T>}:
  +lt = A.slots_length(T, d, t, pt)
  +hk = L.subst(Nat, z => {Nat.is_le(SC.pow2(d), z) == True{} : Bool}, SC.pow2(d), SC.length(T, A.slots(T, t)), Equal.sym(Nat, SC.length(T, A.slots(T, t)), SC.pow2(d), lt), N.le_refl(SC.pow2(d)))
  %Equal.sym(List<&2, T>, A.slots(T, tfill(~T, ~f, d, SC.pow2(d), t)), fill(~T, ~f, SC.pow2(d), A.slots(T, t)), tfill_slots(~T, ~f, d, SC.pow2(d), t, N.le_refl(SC.pow2(d)), pt)) : {SC.nth(T, _, j) == Some{f(j)} : Maybe<&2, T>}
  fill_below(~T, ~f, SC.pow2(d), A.slots(T, t), j, hj, hk)

# ---- the executable loops are tfill on the thawed arena ----

def iota_f(x: Nat) -> U.Nt:
  U.N{x}

def solo_f(x: Nat) -> U.Ms:
  U.M{Con{x, Nil{}}}

def iota_go_ok(+d: Nat, k: Nat, +t: A.Tree<U.Nt>, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hk: {Nat.is_le(k, SC.pow2(d)) == True{} : Bool}, +pf: {A.perfect(U.Nt, d, t) == True{} : Bool}) -> {U.iota_go(k, A.thaw(U.Nt, t)) == A.thaw(U.Nt, tfill(~U.Nt, ~iota_f, d, k, t)) : Array<U.Nt>}:
  match k:
    case 0n:
      {==}
    case 1n+ +j:
      +hj = N.succ_le_lt(j, SC.pow2(d), hk)
      Equal.trans(Array<U.Nt>, U.iota_go(j, U.write_nat(A.thaw(U.Nt, t), d, j, j)), U.iota_go(j, A.thaw(U.Nt, A.upd(U.Nt, d, t, j, U.N{j}))), A.thaw(U.Nt, tfill(~U.Nt, ~iota_f, d, j, A.upd(U.Nt, d, t, j, U.N{j}))),
        Equal.cong(Array<U.Nt>, Array<U.Nt>, z => U.iota_go(j, z), U.write_nat(A.thaw(U.Nt, t), d, j, j), A.thaw(U.Nt, A.upd(U.Nt, d, t, j, U.N{j})), AR.write_nat_ok(d, t, j, j, hd, hj, pf)),
        iota_go_ok(d, j, A.upd(U.Nt, d, t, j, U.N{j}), hd, N.lt_le(j, SC.pow2(d), hj), A.upd_perfect(U.Nt, d, t, j, U.N{j}, pf)))

def solo_go_ok(+d: Nat, k: Nat, +t: A.Tree<U.Ms>, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hk: {Nat.is_le(k, SC.pow2(d)) == True{} : Bool}, +pf: {A.perfect(U.Ms, d, t) == True{} : Bool}) -> {U.solo_go(k, A.thaw(U.Ms, t)) == A.thaw(U.Ms, tfill(~U.Ms, ~solo_f, d, k, t)) : Array<U.Ms>}:
  match k:
    case 0n:
      {==}
    case 1n+ +j:
      +hj = N.succ_le_lt(j, SC.pow2(d), hk)
      Equal.trans(Array<U.Ms>, U.solo_go(j, U.write_ms(A.thaw(U.Ms, t), d, j, Con{j, Nil{}})), U.solo_go(j, A.thaw(U.Ms, A.upd(U.Ms, d, t, j, U.M{Con{j, Nil{}}}))), A.thaw(U.Ms, tfill(~U.Ms, ~solo_f, d, j, A.upd(U.Ms, d, t, j, U.M{Con{j, Nil{}}}))),
        Equal.cong(Array<U.Ms>, Array<U.Ms>, z => U.solo_go(j, z), U.write_ms(A.thaw(U.Ms, t), d, j, Con{j, Nil{}}), A.thaw(U.Ms, A.upd(U.Ms, d, t, j, U.M{Con{j, Nil{}}})), AR.write_ms_ok(d, t, j, Con{j, Nil{}}, hd, hj, pf)),
        solo_go_ok(d, j, A.upd(U.Ms, d, t, j, U.M{Con{j, Nil{}}}), hd, N.lt_le(j, SC.pow2(d), hj), A.upd_perfect(U.Ms, d, t, j, U.M{Con{j, Nil{}}}, pf)))
