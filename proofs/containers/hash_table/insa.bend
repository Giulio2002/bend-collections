import Base
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../../lib/spec_common.bend as SC
import ../../lib/u32div.bend as UD
import ../../../src/containers/hash_table.bend as H
import ./words.bend as WR
import ./strings.bend as STR
import ./keys.bend as K
import ./table.bend as TB
import ./buckets.bend as B
import ./state.bend as ST
import ./probe_all.bend as PA
import ./insm.bend as IM
import ../../lib/words32.bend as W32

# The arrays after putting (w, L) into bucket e and the key sk into slot
# slot(L) read as the old bucket list with bucket e replaced.


# ---- list updates ----

def len_upd(+xs: List<&2, U32>, +i: Nat, +v: U32) -> {SC.length(U32, SC.update(U32, xs, i, v)) == SC.length(U32, xs) : Nat}:
  match xs i:
    case Nil{} _:
      {==}
    case Con{h, t} 0n:
      {==}
    case Con{h, t} 1n+p:
      Equal.cong(Nat, Nat, z => 1n+z, SC.length(U32, SC.update(U32, t, p, v)), SC.length(U32, t), len_upd(t, p, v))



def nths_upd_same(+xs: List<&2, String>, +i: Nat, +v: String, +h: {Nat.is_lt(i, SC.length(String, xs)) == True{} : Bool}) -> {TB.nths(SC.update(String, xs, i, v), i) == v : String}:
  match xs i:
    case Nil{} _:
      Empty.absurd({TB.nths(SC.update(String, Nil{}, i, v), i) == v : String}, N.lt_zero_absurd(i, h))
    case Con{x, t} 0n:
      {==}
    case Con{x, t} 1n+p:
      nths_upd_same(t, p, v, h)

def nths_upd_other(+xs: List<&2, String>, +i: Nat, +j: Nat, +v: String, +h: {Nat.is_eq(i, j) == False{} : Bool}) -> {TB.nths(SC.update(String, xs, i, v), j) == TB.nths(xs, j) : String}:
  match xs i j:
    case Nil{} _ _:
      {==}
    case Con{x, r} 0n 0n:
      Empty.absurd({TB.nths(SC.update(String, Con{x, r}, 0n, v), 0n) == TB.nths(Con{x, r}, 0n) : String}, L.true_false(h))
    case Con{x, r} 0n 1n+q:
      {==}
    case Con{x, r} 1n+p 0n:
      {==}
    case Con{x, r} 1n+p 1n+q:
      nths_upd_other(r, p, q, v, h)

# ---- word and link indices of different buckets differ ----

def dd_c(+a: Nat, +b: Nat, +h: {Nat.is_eq(a, b) == False{} : Bool}, +c: Bool, +hc: {Nat.is_eq(Nat.double(a), Nat.double(b)) == c : Bool}) -> {c == False{} : Bool}:
  match c:
    case False{}:
      {==}
    case True{}:
      +e = N.double_inj(a, b, N.eq_from_is_eq(Nat.double(a), Nat.double(b), hc))
      Empty.absurd({True{} == False{} : Bool}, L.true_false(Equal.trans(Bool, True{}, Nat.is_eq(a, b), False{}, L.subst(Nat, z => {True{} == Nat.is_eq(a, z) : Bool}, a, b, e, Equal.sym(Bool, Nat.is_eq(a, a), True{}, N.is_eq_refl(a))), h)))

def dd_ne(+a: Nat, +b: Nat, +h: {Nat.is_eq(a, b) == False{} : Bool}) -> {Nat.is_eq(Nat.double(a), Nat.double(b)) == False{} : Bool}:
  dd_c(a, b, h, Nat.is_eq(Nat.double(a), Nat.double(b)), {==})

def eo_c(+a: Nat, +b: Nat, +c: Bool, +hc: {Nat.is_eq(Nat.double(a), 1n+Nat.double(b)) == c : Bool}) -> {c == False{} : Bool}:
  match c:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, N.even_odd(a, b, N.eq_from_is_eq(Nat.double(a), 1n+Nat.double(b), hc)))

def eo_ne(+a: Nat, +b: Nat) -> {Nat.is_eq(Nat.double(a), 1n+Nat.double(b)) == False{} : Bool}:
  eo_c(a, b, Nat.is_eq(Nat.double(a), 1n+Nat.double(b)), {==})

def oe_ne(+a: Nat, +b: Nat) -> {Nat.is_eq(1n+Nat.double(a), Nat.double(b)) == False{} : Bool}:
  N.is_eq_sym_false(Nat.double(b), 1n+Nat.double(a), eo_ne(b, a))

# ---- decoding one bucket ----

def w_other(+tb: List<&2, U32>, +e: Nat, +w: U32, +L: U32, +j: Nat, +hne: {Nat.is_eq(e, j) == False{} : Bool}) -> {W32.nth0(SC.update(U32, SC.update(U32, tb, Nat.double(e), w), 1n+Nat.double(e), L), Nat.double(j)) == W32.nth0(tb, Nat.double(j)) : U32}:
  Equal.trans(U32, W32.nth0(SC.update(U32, SC.update(U32, tb, Nat.double(e), w), 1n+Nat.double(e), L), Nat.double(j)), W32.nth0(SC.update(U32, tb, Nat.double(e), w), Nat.double(j)), W32.nth0(tb, Nat.double(j)), W32.nth0_upd_other(SC.update(U32, tb, Nat.double(e), w), 1n+Nat.double(e), Nat.double(j), L, oe_ne(e, j)), W32.nth0_upd_other(tb, Nat.double(e), Nat.double(j), w, dd_ne(e, j, hne)))

def l_other(+tb: List<&2, U32>, +e: Nat, +w: U32, +L: U32, +j: Nat, +hne: {Nat.is_eq(e, j) == False{} : Bool}) -> {W32.nth0(SC.update(U32, SC.update(U32, tb, Nat.double(e), w), 1n+Nat.double(e), L), 1n+Nat.double(j)) == W32.nth0(tb, 1n+Nat.double(j)) : U32}:
  Equal.trans(U32, W32.nth0(SC.update(U32, SC.update(U32, tb, Nat.double(e), w), 1n+Nat.double(e), L), 1n+Nat.double(j)), W32.nth0(SC.update(U32, tb, Nat.double(e), w), 1n+Nat.double(j)), W32.nth0(tb, 1n+Nat.double(j)), W32.nth0_upd_other(SC.update(U32, tb, Nat.double(e), w), 1n+Nat.double(e), 1n+Nat.double(j), L, dd_ne(e, j, hne)), W32.nth0_upd_other(tb, Nat.double(e), 1n+Nat.double(j), w, eo_ne(e, j)))

def w_same(+tb: List<&2, U32>, +e: Nat, +w: U32, +L: U32, +htb: {Nat.is_lt(1n+Nat.double(e), SC.length(U32, tb)) == True{} : Bool}) -> {W32.nth0(SC.update(U32, SC.update(U32, tb, Nat.double(e), w), 1n+Nat.double(e), L), Nat.double(e)) == w : U32}:
  Equal.trans(U32, W32.nth0(SC.update(U32, SC.update(U32, tb, Nat.double(e), w), 1n+Nat.double(e), L), Nat.double(e)), W32.nth0(SC.update(U32, tb, Nat.double(e), w), Nat.double(e)), w, W32.nth0_upd_other(SC.update(U32, tb, Nat.double(e), w), 1n+Nat.double(e), Nat.double(e), L, oe_ne(e, e)), W32.nth0_upd_same(tb, Nat.double(e), w, N.lt_trans(Nat.double(e), 1n+Nat.double(e), SC.length(U32, tb), N.lt_succ(Nat.double(e)), htb)))

def l_same(+tb: List<&2, U32>, +e: Nat, +w: U32, +L: U32, +htb: {Nat.is_lt(1n+Nat.double(e), SC.length(U32, tb)) == True{} : Bool}) -> {W32.nth0(SC.update(U32, SC.update(U32, tb, Nat.double(e), w), 1n+Nat.double(e), L), 1n+Nat.double(e)) == L : U32}:
  W32.nth0_upd_same(SC.update(U32, tb, Nat.double(e), w), 1n+Nat.double(e), L, L.subst(Nat, z => {Nat.is_lt(1n+Nat.double(e), z) == True{} : Bool}, SC.length(U32, tb), SC.length(U32, SC.update(U32, tb, Nat.double(e), w)), Equal.sym(Nat, SC.length(U32, SC.update(U32, tb, Nat.double(e), w)), SC.length(U32, tb), len_upd(tb, Nat.double(e), w)), htb))

def dec_same_c(+w: U32, +l: U32, +kl: List<&2, String>, +s: Nat, +sk: String, +emp: Bool, +h: {Bool.not(Bool.and(B.occ(TB.dec_c(w, l, kl, emp)), Nat.is_eq(UD.v(H.slot(B.lnk(TB.dec_c(w, l, kl, emp)))), s))) == True{} : Bool}) -> {TB.dec_c(w, l, SC.update(String, kl, s, sk), emp) == TB.dec_c(w, l, kl, emp) : B.Bk}:
  match emp:
    case True{}:
      {==}
    case False{}:
      +hne = N.is_eq_sym_false(UD.v(H.slot(l)), s, K.not_true_eq(Nat.is_eq(UD.v(H.slot(l)), s), h))
      Equal.cong(String, B.Bk, z => B.BF{w, l, TB.keyof(w, z)}, TB.nths(SC.update(String, kl, s, sk), UD.v(H.slot(l))), TB.nths(kl, UD.v(H.slot(l))), nths_upd_other(kl, s, UD.v(H.slot(l)), sk, hne))

def dec_other(+tb: List<&2, U32>, +kl: List<&2, String>, +e: Nat, +w: U32, +L: U32, +sk: String, +j: Nat, +hne: {Nat.is_eq(e, j) == False{} : Bool}, +hns: {Bool.not(Bool.and(B.occ(TB.dec(tb, kl, j)), Nat.is_eq(UD.v(H.slot(B.lnk(TB.dec(tb, kl, j)))), UD.v(H.slot(L))))) == True{} : Bool}) -> {TB.dec(SC.update(U32, SC.update(U32, tb, Nat.double(e), w), 1n+Nat.double(e), L), SC.update(String, kl, UD.v(H.slot(L)), sk), j) == TB.dec(tb, kl, j) : B.Bk}:
  +wj = W32.nth0(tb, Nat.double(j))
  +lj = W32.nth0(tb, 1n+Nat.double(j))
  Equal.trans(B.Bk, TB.dec(SC.update(U32, SC.update(U32, tb, Nat.double(e), w), 1n+Nat.double(e), L), SC.update(String, kl, UD.v(H.slot(L)), sk), j), TB.dec_c(wj, W32.nth0(SC.update(U32, SC.update(U32, tb, Nat.double(e), w), 1n+Nat.double(e), L), 1n+Nat.double(j)), SC.update(String, kl, UD.v(H.slot(L)), sk), U32.is_eq(wj, 0)), TB.dec(tb, kl, j), Equal.cong(U32, B.Bk, a => TB.dec_c(a, W32.nth0(SC.update(U32, SC.update(U32, tb, Nat.double(e), w), 1n+Nat.double(e), L), 1n+Nat.double(j)), SC.update(String, kl, UD.v(H.slot(L)), sk), U32.is_eq(a, 0)), W32.nth0(SC.update(U32, SC.update(U32, tb, Nat.double(e), w), 1n+Nat.double(e), L), Nat.double(j)), wj, w_other(tb, e, w, L, j, hne)),
    Equal.trans(B.Bk, TB.dec_c(wj, W32.nth0(SC.update(U32, SC.update(U32, tb, Nat.double(e), w), 1n+Nat.double(e), L), 1n+Nat.double(j)), SC.update(String, kl, UD.v(H.slot(L)), sk), U32.is_eq(wj, 0)), TB.dec_c(wj, lj, SC.update(String, kl, UD.v(H.slot(L)), sk), U32.is_eq(wj, 0)), TB.dec(tb, kl, j), Equal.cong(U32, B.Bk, a => TB.dec_c(wj, a, SC.update(String, kl, UD.v(H.slot(L)), sk), U32.is_eq(wj, 0)), W32.nth0(SC.update(U32, SC.update(U32, tb, Nat.double(e), w), 1n+Nat.double(e), L), 1n+Nat.double(j)), lj, l_other(tb, e, w, L, j, hne)), dec_same_c(wj, lj, kl, UD.v(H.slot(L)), sk, U32.is_eq(wj, 0), hns)))

def dec_at(+tb: List<&2, U32>, +kl: List<&2, String>, +e: Nat, +w: U32, +L: U32, +sk: String, +hw0: {U32.is_eq(w, 0) == False{} : Bool}, +htb: {Nat.is_lt(1n+Nat.double(e), SC.length(U32, tb)) == True{} : Bool}, +hkl: {Nat.is_lt(UD.v(H.slot(L)), SC.length(String, kl)) == True{} : Bool}) -> {TB.dec(SC.update(U32, SC.update(U32, tb, Nat.double(e), w), 1n+Nat.double(e), L), SC.update(String, kl, UD.v(H.slot(L)), sk), e) == B.BF{w, L, TB.keyof(w, sk)} : B.Bk}:
  Equal.trans(B.Bk, TB.dec(SC.update(U32, SC.update(U32, tb, Nat.double(e), w), 1n+Nat.double(e), L), SC.update(String, kl, UD.v(H.slot(L)), sk), e), TB.dec_c(w, W32.nth0(SC.update(U32, SC.update(U32, tb, Nat.double(e), w), 1n+Nat.double(e), L), 1n+Nat.double(e)), SC.update(String, kl, UD.v(H.slot(L)), sk), U32.is_eq(w, 0)), B.BF{w, L, TB.keyof(w, sk)}, Equal.cong(U32, B.Bk, a => TB.dec_c(a, W32.nth0(SC.update(U32, SC.update(U32, tb, Nat.double(e), w), 1n+Nat.double(e), L), 1n+Nat.double(e)), SC.update(String, kl, UD.v(H.slot(L)), sk), U32.is_eq(a, 0)), W32.nth0(SC.update(U32, SC.update(U32, tb, Nat.double(e), w), 1n+Nat.double(e), L), Nat.double(e)), w, w_same(tb, e, w, L, htb)),
    Equal.trans(B.Bk, TB.dec_c(w, W32.nth0(SC.update(U32, SC.update(U32, tb, Nat.double(e), w), 1n+Nat.double(e), L), 1n+Nat.double(e)), SC.update(String, kl, UD.v(H.slot(L)), sk), U32.is_eq(w, 0)), TB.dec_c(w, L, SC.update(String, kl, UD.v(H.slot(L)), sk), U32.is_eq(w, 0)), B.BF{w, L, TB.keyof(w, sk)}, Equal.cong(U32, B.Bk, a => TB.dec_c(w, a, SC.update(String, kl, UD.v(H.slot(L)), sk), U32.is_eq(w, 0)), W32.nth0(SC.update(U32, SC.update(U32, tb, Nat.double(e), w), 1n+Nat.double(e), L), 1n+Nat.double(e)), L, l_same(tb, e, w, L, htb)),
      Equal.trans(B.Bk, TB.dec_c(w, L, SC.update(String, kl, UD.v(H.slot(L)), sk), U32.is_eq(w, 0)), TB.dec_c(w, L, SC.update(String, kl, UD.v(H.slot(L)), sk), False{}), B.BF{w, L, TB.keyof(w, sk)}, Equal.cong(Bool, B.Bk, c => TB.dec_c(w, L, SC.update(String, kl, UD.v(H.slot(L)), sk), c), U32.is_eq(w, 0), False{}, hw0), Equal.cong(String, B.Bk, z => B.BF{w, L, TB.keyof(w, z)}, TB.nths(SC.update(String, kl, UD.v(H.slot(L)), sk), UD.v(H.slot(L))), sk, nths_upd_same(kl, UD.v(H.slot(L)), sk, hkl)))))

# ---- decoding the list ----


def idx_lt(+i: Nat, +p: Nat, +n: Nat, +h: {Nat.is_le(Nat.add(i, 1n+p), n) == True{} : Bool}) -> {Nat.is_lt(i, n) == True{} : Bool}:
  N.succ_le_lt(i, n, N.le_trans(1n+i, Nat.add(i, 1n+p), n, L.subst(Nat, z => {Nat.is_le(1n+i, z) == True{} : Bool}, 1n+Nat.add(i, p), Nat.add(i, 1n+p), Equal.sym(Nat, Nat.add(i, 1n+p), 1n+Nat.add(i, p), N.add_succ(i, p)), N.le_add_right(i, p)), h))

def idx_next(+i: Nat, +p: Nat, +n: Nat, +h: {Nat.is_le(Nat.add(i, 1n+p), n) == True{} : Bool}) -> {Nat.is_le(Nat.add(1n+i, p), n) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_le(z, n) == True{} : Bool}, Nat.add(i, 1n+p), 1n+Nat.add(i, p), N.add_succ(i, p), h)

def ns_dec(+tb: List<&2, U32>, +kl: List<&2, String>, +e: Nat, +w: U32, +L: U32, +sk: String, +n: Nat, +hns: {ST.noslot(TB.buckets(tb, kl, n), UD.v(H.slot(L)), n) == True{} : Bool}, +i: Nat, +hi: {Nat.is_lt(i, n) == True{} : Bool}) -> {Bool.not(Bool.and(B.occ(TB.dec(tb, kl, i)), Nat.is_eq(UD.v(H.slot(B.lnk(TB.dec(tb, kl, i)))), UD.v(H.slot(L))))) == True{} : Bool}:
  L.subst(B.Bk, y => {Bool.not(Bool.and(B.occ(y), Nat.is_eq(UD.v(H.slot(B.lnk(y))), UD.v(H.slot(L))))) == True{} : Bool}, B.at(TB.buckets(tb, kl, n), i), TB.dec(tb, kl, i), TB.at_buckets(tb, kl, n, i, hi), IM.noslot_inst(TB.buckets(tb, kl, n), UD.v(H.slot(L)), n, hns, i, hi))

def con_eq(+a: B.Bk, +b: B.Bk, +x: List<&2, B.Bk>, +y: List<&2, B.Bk>, +ha: {a == b : B.Bk}, +hx: {x == y : List<&2, B.Bk>}) -> {Con{a, x} == Con{b, y} : List<&2, B.Bk>}:
  Equal.trans(List<&2, B.Bk>, Con{a, x}, Con{b, x}, Con{b, y}, Equal.cong(B.Bk, List<&2, B.Bk>, z => Con{z, x}, a, b, ha), Equal.cong(List<&2, B.Bk>, List<&2, B.Bk>, z => Con{b, z}, x, y, hx))

def dl_same(+tb: List<&2, U32>, +kl: List<&2, String>, +e: Nat, +w: U32, +L: U32, +sk: String, +n: Nat, +hns: {ST.noslot(TB.buckets(tb, kl, n), UD.v(H.slot(L)), n) == True{} : Bool}, +m: Nat, +i: Nat, +hmi: {Nat.is_le(Nat.add(i, m), n) == True{} : Bool}, +hei: {Nat.is_lt(e, i) == True{} : Bool}) -> {TB.dlist(SC.update(U32, SC.update(U32, tb, Nat.double(e), w), 1n+Nat.double(e), L), SC.update(String, kl, UD.v(H.slot(L)), sk), m, i) == TB.dlist(tb, kl, m, i) : List<&2, B.Bk>}:
  match m:
    case 0n:
      {==}
    case 1n+p:
      +hi = idx_lt(i, p, n, hmi)
      con_eq(TB.dec(SC.update(U32, SC.update(U32, tb, Nat.double(e), w), 1n+Nat.double(e), L), SC.update(String, kl, UD.v(H.slot(L)), sk), i), TB.dec(tb, kl, i), TB.dlist(SC.update(U32, SC.update(U32, tb, Nat.double(e), w), 1n+Nat.double(e), L), SC.update(String, kl, UD.v(H.slot(L)), sk), p, 1n+i), TB.dlist(tb, kl, p, 1n+i), dec_other(tb, kl, e, w, L, sk, i, N.is_eq_lt(e, i, hei), ns_dec(tb, kl, e, w, L, sk, n, hns, i, hi)), dl_same(tb, kl, e, w, L, sk, n, hns, p, 1n+i, idx_next(i, p, n, hmi), N.lt_trans(e, i, 1n+i, hei, N.lt_succ(i))))

def dl_ins(+tb: List<&2, U32>, +kl: List<&2, String>, +e: Nat, +w: U32, +L: U32, +sk: String, +n: Nat, +hns: {ST.noslot(TB.buckets(tb, kl, n), UD.v(H.slot(L)), n) == True{} : Bool}, +hw0: {U32.is_eq(w, 0) == False{} : Bool}, +htb: {Nat.is_lt(1n+Nat.double(e), SC.length(U32, tb)) == True{} : Bool}, +hkl: {Nat.is_lt(UD.v(H.slot(L)), SC.length(String, kl)) == True{} : Bool}, +m: Nat, +i: Nat, +d: Nat, +hed: {Nat.add(i, d) == e : Nat}, +hmi: {Nat.is_le(Nat.add(i, m), n) == True{} : Bool}) -> {TB.dlist(SC.update(U32, SC.update(U32, tb, Nat.double(e), w), 1n+Nat.double(e), L), SC.update(String, kl, UD.v(H.slot(L)), sk), m, i) == IM.bupd(TB.dlist(tb, kl, m, i), d, B.BF{w, L, TB.keyof(w, sk)}) : List<&2, B.Bk>}:
  match m d:
    case 0n _:
      {==}
    case 1n+p 0n:
      +hie = Equal.trans(Nat, i, Nat.add(i, 0n), e, Equal.sym(Nat, Nat.add(i, 0n), i, N.add_zero(i)), hed)
      +h0 = L.subst(Nat, z => {TB.dec(SC.update(U32, SC.update(U32, tb, Nat.double(e), w), 1n+Nat.double(e), L), SC.update(String, kl, UD.v(H.slot(L)), sk), z) == B.BF{w, L, TB.keyof(w, sk)} : B.Bk}, e, i, Equal.sym(Nat, i, e, hie), dec_at(tb, kl, e, w, L, sk, hw0, htb, hkl))
      +hei = L.subst(Nat, z => {Nat.is_lt(z, 1n+i) == True{} : Bool}, i, e, hie, N.lt_succ(i))
      con_eq(TB.dec(SC.update(U32, SC.update(U32, tb, Nat.double(e), w), 1n+Nat.double(e), L), SC.update(String, kl, UD.v(H.slot(L)), sk), i), B.BF{w, L, TB.keyof(w, sk)}, TB.dlist(SC.update(U32, SC.update(U32, tb, Nat.double(e), w), 1n+Nat.double(e), L), SC.update(String, kl, UD.v(H.slot(L)), sk), p, 1n+i), TB.dlist(tb, kl, p, 1n+i), h0, dl_same(tb, kl, e, w, L, sk, n, hns, p, 1n+i, idx_next(i, p, n, hmi), hei))
    case 1n+p 1n+q:
      +hi = idx_lt(i, p, n, hmi)
      +he1 = Equal.trans(Nat, Nat.add(1n+i, q), Nat.add(i, 1n+q), e, Equal.sym(Nat, Nat.add(i, 1n+q), 1n+Nat.add(i, q), N.add_succ(i, q)), hed)
      +hlt = L.subst(Nat, z => {Nat.is_lt(i, z) == True{} : Bool}, Nat.add(1n+i, q), e, he1, N.le_lt_succ(i, Nat.add(i, q), N.le_add_right(i, q)))
      +hne = N.is_eq_sym_false(i, e, N.is_eq_lt(i, e, hlt))
      con_eq(TB.dec(SC.update(U32, SC.update(U32, tb, Nat.double(e), w), 1n+Nat.double(e), L), SC.update(String, kl, UD.v(H.slot(L)), sk), i), TB.dec(tb, kl, i), TB.dlist(SC.update(U32, SC.update(U32, tb, Nat.double(e), w), 1n+Nat.double(e), L), SC.update(String, kl, UD.v(H.slot(L)), sk), p, 1n+i), IM.bupd(TB.dlist(tb, kl, p, 1n+i), q, B.BF{w, L, TB.keyof(w, sk)}), dec_other(tb, kl, e, w, L, sk, i, hne, ns_dec(tb, kl, e, w, L, sk, n, hns, i, hi)), dl_ins(tb, kl, e, w, L, sk, n, hns, hw0, htb, hkl, p, 1n+i, q, he1, idx_next(i, p, n, hmi)))

# THEOREM: the written arrays decode to the old buckets with bucket e replaced
def buckets_put(+tb: List<&2, U32>, +kl: List<&2, String>, +e: Nat, +w: U32, +L: U32, +sk: String, +n: Nat, +hns: {ST.noslot(TB.buckets(tb, kl, n), UD.v(H.slot(L)), n) == True{} : Bool}, +hw0: {U32.is_eq(w, 0) == False{} : Bool}, +htb: {Nat.is_lt(1n+Nat.double(e), SC.length(U32, tb)) == True{} : Bool}, +hkl: {Nat.is_lt(UD.v(H.slot(L)), SC.length(String, kl)) == True{} : Bool}) -> {TB.buckets(SC.update(U32, SC.update(U32, tb, Nat.double(e), w), 1n+Nat.double(e), L), SC.update(String, kl, UD.v(H.slot(L)), sk), n) == IM.bupd(TB.buckets(tb, kl, n), e, B.BF{w, L, TB.keyof(w, sk)}) : List<&2, B.Bk>}:
  dl_ins(tb, kl, e, w, L, sk, n, hns, hw0, htb, hkl, n, 0n, e, {==}, N.le_refl(n))

def len_dlist(+tb: List<&2, U32>, +kl: List<&2, String>, +m: Nat, +i: Nat) -> {SC.length(B.Bk, TB.dlist(tb, kl, m, i)) == m : Nat}:
  match m:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, z => 1n+z, SC.length(B.Bk, TB.dlist(tb, kl, p, 1n+i)), p, len_dlist(tb, kl, p, 1n+i))

# ---- the stored key decodes to the key ----

def ks_short(+c: U32, +t: String, +h: {K.short_c(c, t) == True{} : Bool}) -> {TB.keyof(H.short_word(c), SNil{}) == SCon{Chr{c}, t} : String}:
  match t:
    case SNil{}:
      +e1 = Equal.cong(Bool, String, b => TB.keyof_c(H.short_word(c), SNil{}, b), H.is_short(H.short_word(c)), True{}, WR.short_is_short(c))
      Equal.trans(String, TB.keyof(H.short_word(c), SNil{}), SCon{Chr{U32.and(H.short_word(c), 2147483647)}, SNil{}}, SCon{Chr{c}, SNil{}}, e1, Equal.cong(U32, String, x => SCon{Chr{x}, SNil{}}, U32.and(H.short_word(c), 2147483647), c, WR.short_back(c, h)))
    case SCon{d, r}:
      Empty.absurd({TB.keyof(H.short_word(c), SNil{}) == SCon{Chr{c}, SCon{d, r}} : String}, L.false_true(h))

def ks_c(+c: U32, +t: String, +sh: Bool, +hsh: {K.short_c(c, t) == sh : Bool}) -> {TB.keyof(K.kw_c(c, t, sh), PA.st_c(c, t, sh)) == SCon{Chr{c}, t} : String}:
  match sh:
    case True{}:
      ks_short(c, t, hsh)
    case False{}:
      Equal.cong(Bool, String, b => TB.keyof_c(K.kw_c(c, t, False{}), SCon{Chr{c}, t}, b), H.is_short(H.long_word(STR.fold(SCon{Chr{c}, t}, 0))), False{}, WR.long_is_long(STR.fold(SCon{Chr{c}, t}, 0)))

# THEOREM: a key's word and the string the probe hands back decode to the key
def keyof_stored(+key: String) -> {TB.keyof(K.kword(key), PA.stored(key)) == key : String}:
  match key:
    case SNil{}:
      Equal.cong(Bool, String, b => TB.keyof_c(K.kword(SNil{}), SNil{}, b), H.is_short(H.long_word(STR.fold(SNil{}, 0))), False{}, WR.long_is_long(STR.fold(SNil{}, 0)))
    case SCon{Chr{+c}, +t}:
      ks_c(c, t, K.short_c(c, t), {==})
