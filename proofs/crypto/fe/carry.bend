import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/crypto/curve25519/fe.bend as FV
import ../../../src/crypto/curve25519/limbs.bend as LS
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/word.bend as WD
import ../../lib/arith.bend as AR
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../../math/natural/arith.bend as NR
import ../curve25519/num.bend as M
import ./nl.bend as NL
import ./pw.bend as PW

# The carry chain of src/crypto/curve25519/limbs.bend in radix R = 2^17
# (hypothesis hR: R == 2^17 in the symbolic one): value(limbs) + 2^(17 n)
# carry_out == value(xs) + carry_in, every limb below R, and a carry bound
# kept along the chain (Fiat-Crypto's carry chains, Erbsen et al. 2019).

def tr(+a: Nat, +b: Nat, +c: Nat, +e1: {a == b : Nat}, +e2: {b == c : Nat}) -> {a == c : Nat}:
  Equal.trans(Nat, a, b, c, e1, e2)

def sy(+a: Nat, +b: Nat, +e: {a == b : Nat}) -> {b == a : Nat}:
  Equal.sym(Nat, a, b, e)

def cl(r: LS.Cr) -> List<&2, Nat>:
  LS.cr_limbs(r)

def cc(r: LS.Cr) -> Nat:
  LS.cr_out(r)

def cr_eta(+r: LS.Cr) -> {r == LS.Cr{LS.cr_limbs(r), LS.cr_out(r)} : LS.Cr}:
  match r:
    case LS.Cr{a, c}:
      {==}

def cl_con(+l: Nat, +r: LS.Cr) -> {LS.cr_limbs(LS.cr_con(l, r)) == Con{l, LS.cr_limbs(r)} : List<&2, Nat>}:
  match r:
    case LS.Cr{a, c}:
      {==}

def cc_con(+l: Nat, +r: LS.Cr) -> {LS.cr_out(LS.cr_con(l, r)) == LS.cr_out(r) : Nat}:
  match r:
    case LS.Cr{a, c}:
      {==}

# ---- the radix ----

def r_pos(+one: Nat, +h1: {one == 1n : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}) -> {Nat.is_lt(0n, R) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_lt(0n, z) == True{} : Bool}, WD.sc(17n, one), R, Equal.sym(Nat, R, WD.sc(17n, one), hR), PW.sc_pos(17n, one, h1))

def r_succ(+one: Nat, +h1: {one == 1n : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}) -> {1n+Nat.sub(R, 1n) == R : Nat}:
  N.sub_add(R, 1n, N.lt_succ_le_succ(0n, R, r_pos(one, h1, R, hR)))

# R x == 2^17 x
def mul_r(+one: Nat, +h1: {one == 1n : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +x: Nat) -> {Nat.mul(R, x) == C.shift(17n, x) : Nat}:
  +e = L.subst(Nat, z => {Nat.mul(x, z) == WD.sc(17n, x) : Nat}, WD.sc(17n, one), R, Equal.sym(Nat, R, WD.sc(17n, one), hR), AR.mul_sc1(17n, one, h1, x))
  tr(Nat.mul(R, x), Nat.mul(x, R), WD.sc(17n, x), NA.mul_comm(R, x), e)

# s mod R + 2^17 (s div R) == s
def dm(+one: Nat, +h1: {one == 1n : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +s: Nat) -> {Nat.add(Nat.mod(s, R), C.shift(17n, Nat.div(s, R))) == s : Nat}:
  +b = Nat.sub(R, 1n)
  +e0 = L.subst(Nat, z => {s == Nat.add(Nat.mul(Nat.div(s, z), z), Nat.mod(s, z)) : Nat}, 1n+b, R, r_succ(one, h1, R, hR), NR.dm_eq(b, s))
  +q = Nat.div(s, R)
  +m = Nat.mod(s, R)
  +e1 = M.cong_r(m, C.shift(17n, q), Nat.mul(q, R), sy(Nat.mul(q, R), C.shift(17n, q), tr(Nat.mul(q, R), Nat.mul(R, q), C.shift(17n, q), NA.mul_comm(q, R), mul_r(one, h1, R, hR, q))))
  tr(Nat.add(m, C.shift(17n, q)), Nat.add(m, Nat.mul(q, R)), s, e1, tr(Nat.add(m, Nat.mul(q, R)), Nat.add(Nat.mul(q, R), m), s, NA.add_comm(m, Nat.mul(q, R)), sy(s, Nat.add(Nat.mul(q, R), m), e0)))

def mod_lt(+one: Nat, +h1: {one == 1n : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +s: Nat) -> {Nat.is_lt(Nat.mod(s, R), R) == True{} : Bool}:
  +b = Nat.sub(R, 1n)
  L.subst(Nat, z => {Nat.is_lt(Nat.mod(s, z), z) == True{} : Bool}, 1n+b, R, r_succ(one, h1, R, hR), NR.dm_lt(b, s))

# s < R E -> s div R < E
def div_lt(+one: Nat, +h1: {one == 1n : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +s: Nat, +E: Nat, +h: {Nat.is_lt(s, Nat.mul(R, E)) == True{} : Bool}) -> {Nat.is_lt(Nat.div(s, R), E) == True{} : Bool}:
  +b = Nat.sub(R, 1n)
  +e0 = L.subst(Nat, z => {Nat.is_le(E, Nat.div(s, z)) == Nat.is_le(Nat.mul(E, z), s) : Bool}, 1n+b, R, r_succ(one, h1, R, hR), NR.le_div(b, E, s))
  +h2 = L.subst(Nat, z => {Nat.is_lt(s, z) == True{} : Bool}, Nat.mul(R, E), Nat.mul(E, R), NA.mul_comm(R, E), h)
  +e1 = Equal.trans(Bool, Nat.is_le(E, Nat.div(s, R)), Nat.is_le(Nat.mul(E, R), s), False{}, e0, N.lt_not_le(s, Nat.mul(E, R), h2))
  N.not_le_lt(E, Nat.div(s, R), e1)

# ---- values ----

# 2^(17 len(xs)) x
def shl(xs: List<&2, Nat>, +x: Nat) -> Nat:
  match xs:
    case Nil{}:
      x
    case Con{h, t}:
      C.shift(17n, shl(t, x))

# (h + c) + X == (h + X) + c
def swap3(+h: Nat, +c: Nat, +X: Nat) -> {Nat.add(Nat.add(h, c), X) == Nat.add(Nat.add(h, X), c) : Nat}:
  tr(Nat.add(Nat.add(h, c), X), Nat.add(h, Nat.add(c, X)), Nat.add(Nat.add(h, X), c), NA.add_assoc(h, c, X),
    tr(Nat.add(h, Nat.add(c, X)), Nat.add(h, Nat.add(X, c)), Nat.add(Nat.add(h, X), c), M.cong_r(h, Nat.add(c, X), Nat.add(X, c), NA.add_comm(c, X)), sy(Nat.add(Nat.add(h, X), c), Nat.add(h, Nat.add(X, c)), NA.add_assoc(h, X, c))))

# (m + 2^17 A) + 2^17 B == (m + 2^17 D) + 2^17 T when A + B == T + D
def regroup(+m: Nat, +A: Nat, +B: Nat, +T: Nat, +D: Nat, +e: {Nat.add(A, B) == Nat.add(T, D) : Nat}) -> {Nat.add(Nat.add(m, C.shift(17n, A)), C.shift(17n, B)) == Nat.add(Nat.add(m, C.shift(17n, D)), C.shift(17n, T)) : Nat}:
  +SA = C.shift(17n, A)
  +SB = C.shift(17n, B)
  +ST = C.shift(17n, T)
  +SD = C.shift(17n, D)
  +e1 = NA.add_assoc(m, SA, SB)
  +e2 = M.cong_r(m, Nat.add(SA, SB), C.shift(17n, Nat.add(A, B)), M.sc_add(17n, A, B))
  +e3 = M.cong_r(m, C.shift(17n, Nat.add(A, B)), C.shift(17n, Nat.add(T, D)), M.cong_sc(17n, Nat.add(A, B), Nat.add(T, D), e))
  +e4 = M.cong_r(m, C.shift(17n, Nat.add(T, D)), Nat.add(ST, SD), sy(Nat.add(ST, SD), C.shift(17n, Nat.add(T, D)), M.sc_add(17n, T, D)))
  +e5 = M.cong_r(m, Nat.add(ST, SD), Nat.add(SD, ST), NA.add_comm(ST, SD))
  +e6 = sy(Nat.add(Nat.add(m, SD), ST), Nat.add(m, Nat.add(SD, ST)), NA.add_assoc(m, SD, ST))
  tr(Nat.add(Nat.add(m, SA), SB), Nat.add(m, Nat.add(SA, SB)), Nat.add(Nat.add(m, SD), ST), e1,
    tr(Nat.add(m, Nat.add(SA, SB)), Nat.add(m, C.shift(17n, Nat.add(A, B))), Nat.add(Nat.add(m, SD), ST), e2,
      tr(Nat.add(m, C.shift(17n, Nat.add(A, B))), Nat.add(m, C.shift(17n, Nat.add(T, D))), Nat.add(Nat.add(m, SD), ST), e3,
        tr(Nat.add(m, C.shift(17n, Nat.add(T, D))), Nat.add(m, Nat.add(ST, SD)), Nat.add(Nat.add(m, SD), ST), e4,
          tr(Nat.add(m, Nat.add(ST, SD)), Nat.add(m, Nat.add(SD, ST)), Nat.add(Nat.add(m, SD), ST), e5, e6)))))

# the carry pass keeps the value: value(limbs) + 2^(17 n) out == value(xs) + c
def carry_val(+one: Nat, +h1: {one == 1n : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +xs: List<&2, Nat>, +c: Nat) -> {Nat.add(FV.lv(cl(LS.carry(R, xs, c))), shl(xs, cc(LS.carry(R, xs, c)))) == Nat.add(FV.lv(xs), c) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      +s = Nat.add(h, c)
      +d = Nat.div(s, R)
      +m = Nat.mod(s, R)
      +r = LS.carry(R, t, d)
      +A = FV.lv(cl(r))
      +B = shl(t, cc(r))
      +T = FV.lv(t)
      +ec = M.cong_add(FV.lv(cl(LS.cr_con(m, r))), FV.lv(Con{m, cl(r)}), shl(Con{h, t}, cc(LS.cr_con(m, r))), C.shift(17n, B), Equal.cong(List<&2, Nat>, Nat, z => FV.lv(z), cl(LS.cr_con(m, r)), Con{m, cl(r)}, cl_con(m, r)), M.cong_sc(17n, shl(t, cc(LS.cr_con(m, r))), B, Equal.cong(Nat, Nat, z => shl(t, z), cc(LS.cr_con(m, r)), cc(r), cc_con(m, r))))
      +eg = regroup(m, A, B, T, d, carry_val(one, h1, R, hR, t, d))
      +ed = M.cong_l(Nat.add(m, C.shift(17n, d)), s, C.shift(17n, T), dm(one, h1, R, hR, s))
      tr(Nat.add(FV.lv(cl(LS.cr_con(m, r))), shl(Con{h, t}, cc(LS.cr_con(m, r)))), Nat.add(Nat.add(m, C.shift(17n, A)), C.shift(17n, B)), Nat.add(Nat.add(h, C.shift(17n, T)), c), ec,
        tr(Nat.add(Nat.add(m, C.shift(17n, A)), C.shift(17n, B)), Nat.add(Nat.add(m, C.shift(17n, d)), C.shift(17n, T)), Nat.add(Nat.add(h, C.shift(17n, T)), c), eg,
          tr(Nat.add(Nat.add(m, C.shift(17n, d)), C.shift(17n, T)), Nat.add(s, C.shift(17n, T)), Nat.add(Nat.add(h, C.shift(17n, T)), c), ed, swap3(h, c, C.shift(17n, T)))))

def carry0_val(+one: Nat, +h1: {one == 1n : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +xs: List<&2, Nat>) -> {Nat.add(FV.lv(cl(LS.carry0(R, xs))), shl(xs, cc(LS.carry0(R, xs)))) == FV.lv(xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      +d = Nat.div(h, R)
      +m = Nat.mod(h, R)
      +r = LS.carry(R, t, d)
      +A = FV.lv(cl(r))
      +B = shl(t, cc(r))
      +T = FV.lv(t)
      +ec = M.cong_add(FV.lv(cl(LS.cr_con(m, r))), FV.lv(Con{m, cl(r)}), shl(Con{h, t}, cc(LS.cr_con(m, r))), C.shift(17n, B), Equal.cong(List<&2, Nat>, Nat, z => FV.lv(z), cl(LS.cr_con(m, r)), Con{m, cl(r)}, cl_con(m, r)), M.cong_sc(17n, shl(t, cc(LS.cr_con(m, r))), B, Equal.cong(Nat, Nat, z => shl(t, z), cc(LS.cr_con(m, r)), cc(r), cc_con(m, r))))
      +eg = regroup(m, A, B, T, d, carry_val(one, h1, R, hR, t, d))
      +ed = M.cong_l(Nat.add(m, C.shift(17n, d)), h, C.shift(17n, T), dm(one, h1, R, hR, h))
      tr(Nat.add(FV.lv(cl(LS.cr_con(m, r))), shl(Con{h, t}, cc(LS.cr_con(m, r)))), Nat.add(Nat.add(m, C.shift(17n, A)), C.shift(17n, B)), Nat.add(h, C.shift(17n, T)), ec,
        tr(Nat.add(Nat.add(m, C.shift(17n, A)), C.shift(17n, B)), Nat.add(Nat.add(m, C.shift(17n, d)), C.shift(17n, T)), Nat.add(h, C.shift(17n, T)), eg, ed))

# ---- bounds ----

# limbs below A, carry in below E, A + E <= R E: limbs below R, carry out below E
def carry_below(+one: Nat, +h1: {one == 1n : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +xs: List<&2, Nat>, +c: Nat, +A: Nat, +E: Nat, +hx: {FV.below(xs, A) == True{} : Bool}, +hc: {Nat.is_lt(c, E) == True{} : Bool}, +hAE: {Nat.is_le(Nat.add(A, E), Nat.mul(R, E)) == True{} : Bool}) -> {Bool.and(FV.below(cl(LS.carry(R, xs, c)), R), Nat.is_lt(cc(LS.carry(R, xs, c)), E)) == True{} : Bool}:
  match xs:
    case Nil{}:
      hc
    case Con{+h, +t}:
      +s = Nat.add(h, c)
      +d = Nat.div(s, R)
      +m = Nat.mod(s, R)
      +r = LS.carry(R, t, d)
      +hs = N.lt_le_trans(s, Nat.add(A, E), Nat.mul(R, E), NL.lt_add2(h, c, A, E, NL.below_head(h, t, A, hx), hc), hAE)
      +ih = carry_below(one, h1, R, hR, t, d, A, E, NL.below_tail(h, t, A, hx), div_lt(one, h1, R, hR, s, E, hs), hAE)
      +hl = L.and_left(FV.below(cl(r), R), Nat.is_lt(cc(r), E), ih)
      +ho = L.and_right(FV.below(cl(r), R), Nat.is_lt(cc(r), E), ih)
      +bl = L.subst(List<&2, Nat>, z => {FV.below(z, R) == True{} : Bool}, Con{m, cl(r)}, cl(LS.cr_con(m, r)), Equal.sym(List<&2, Nat>, cl(LS.cr_con(m, r)), Con{m, cl(r)}, cl_con(m, r)), NL.below_con(m, cl(r), R, mod_lt(one, h1, R, hR, s), hl))
      +bo = L.subst(Nat, z => {Nat.is_lt(z, E) == True{} : Bool}, cc(r), cc(LS.cr_con(m, r)), sy(cc(LS.cr_con(m, r)), cc(r), cc_con(m, r)), ho)
      L.and_intro(FV.below(cl(LS.cr_con(m, r)), R), Nat.is_lt(cc(LS.cr_con(m, r)), E), bl, bo)

def carry0_below(+one: Nat, +h1: {one == 1n : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +xs: List<&2, Nat>, +A: Nat, +E: Nat, +hx: {FV.below(xs, A) == True{} : Bool}, +hE: {Nat.is_lt(0n, E) == True{} : Bool}, +hAE: {Nat.is_le(Nat.add(A, E), Nat.mul(R, E)) == True{} : Bool}) -> {Bool.and(FV.below(cl(LS.carry0(R, xs)), R), Nat.is_lt(cc(LS.carry0(R, xs)), E)) == True{} : Bool}:
  match xs:
    case Nil{}:
      hE
    case Con{+h, +t}:
      +d = Nat.div(h, R)
      +m = Nat.mod(h, R)
      +r = LS.carry(R, t, d)
      +hs = N.lt_le_trans(h, Nat.add(A, E), Nat.mul(R, E), N.lt_le_trans(h, A, Nat.add(A, E), NL.below_head(h, t, A, hx), N.le_add_right(A, E)), hAE)
      +ih = carry_below(one, h1, R, hR, t, d, A, E, NL.below_tail(h, t, A, hx), div_lt(one, h1, R, hR, h, E, hs), hAE)
      +hl = L.and_left(FV.below(cl(r), R), Nat.is_lt(cc(r), E), ih)
      +ho = L.and_right(FV.below(cl(r), R), Nat.is_lt(cc(r), E), ih)
      +bl = L.subst(List<&2, Nat>, z => {FV.below(z, R) == True{} : Bool}, Con{m, cl(r)}, cl(LS.cr_con(m, r)), Equal.sym(List<&2, Nat>, cl(LS.cr_con(m, r)), Con{m, cl(r)}, cl_con(m, r)), NL.below_con(m, cl(r), R, mod_lt(one, h1, R, hR, h), hl))
      +bo = L.subst(Nat, z => {Nat.is_lt(z, E) == True{} : Bool}, cc(r), cc(LS.cr_con(m, r)), sy(cc(LS.cr_con(m, r)), cc(r), cc_con(m, r)), ho)
      L.and_intro(FV.below(cl(LS.cr_con(m, r)), R), Nat.is_lt(cc(LS.cr_con(m, r)), E), bl, bo)

# every sum of the chain is below R E
def sums_below(+one: Nat, +h1: {one == 1n : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +xs: List<&2, Nat>, +c: Nat, +A: Nat, +E: Nat, +hx: {FV.below(xs, A) == True{} : Bool}, +hc: {Nat.is_lt(c, E) == True{} : Bool}, +hAE: {Nat.is_le(Nat.add(A, E), Nat.mul(R, E)) == True{} : Bool}) -> {FV.below(FV.sums(R, xs, c), Nat.mul(R, E)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      +s = Nat.add(h, c)
      +hs = N.lt_le_trans(s, Nat.add(A, E), Nat.mul(R, E), NL.lt_add2(h, c, A, E, NL.below_head(h, t, A, hx), hc), hAE)
      NL.below_con(s, FV.sums(R, t, Nat.div(s, R)), Nat.mul(R, E), hs, sums_below(one, h1, R, hR, t, Nat.div(s, R), A, E, NL.below_tail(h, t, A, hx), div_lt(one, h1, R, hR, s, E, hs), hAE))
