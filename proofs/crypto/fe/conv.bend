import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/crypto/curve25519/field.bend as FS
import ../../../spec/crypto/curve25519/fe.bend as FV
import ../../../src/crypto/curve25519/fe.bend as FE
import ../../../src/crypto/curve25519/limbs.bend as LS
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/word.bend as WD
import ../../lib/arith.bend as AR
import ../../lib/u32.bend as U
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../../math/natural/arith.bend as NR
import ../curve25519/num.bend as M
import ../curve25519/cong.bend as G
import ./nl.bend as NL
import ./pw.bend as PW
import ./pass.bend as PS
import ./ops.bend as OP
import ./sub.bend as SB
import ./canon.bend as CN
import ./pack.bend as PK
import ./eqarith.bend as EA
import ./bridge.bend as BR

# freeze, to_bytes, of_bytes, is_zero, eq and parity of
# src/crypto/curve25519/fe.bend on elements.

def tr(+a: Nat, +b: Nat, +c: Nat, +e1: {a == b : Nat}, +e2: {b == c : Nat}) -> {a == c : Nat}:
  Equal.trans(Nat, a, b, c, e1, e2)

def sy(+a: Nat, +b: Nat, +e: {a == b : Nat}) -> {b == a : Nat}:
  Equal.sym(Nat, a, b, e)

# ---- lengths ----

def sel_len(+s: Nat, +xs: List<&2, Nat>, +ys: List<&2, Nat>, +h: {PS.ln(xs) == PS.ln(ys) : Nat}) -> {PS.ln(LS.sel(s, xs, ys)) == PS.ln(xs) : Nat}:
  match xs ys:
    case Nil{} _:
      {==}
    case Con{x, xt} Nil{}:
      Empty.absurd({0n == 1n+PS.ln(xt) : Nat}, N.succ_zero(PS.ln(xt), h))
    case Con{+x, +xt} Con{+y, +yt}:
      Equal.cong(Nat, Nat, t => 1n+t, PS.ln(LS.sel(s, xt, yt)), PS.ln(xt), sel_len(s, xt, yt, N.succ_inj(PS.ln(xt), PS.ln(yt), h)))

def freeze_len(+R: Nat, +xs: List<&2, Nat>, +hl: {PS.ln(xs) == 15n : Nat}) -> {PS.ln(LS.freeze_l(R, xs)) == 15n : Nat}:
  +y = LS.pass(R, xs)
  +z = LS.pass(R, y)
  +hlz = CN.pass_len(R, y, CN.pass_len(R, xs, hl))
  +r = LS.carry(R, z, 19n)
  +e0 = Equal.cong(List<&2, Nat>, Nat, t => PS.ln(t), LS.freeze_l(R, xs), LS.sel(LS.cr_out(r), z, LS.cr_limbs(r)), CN.csub_eta(r, z))
  tr(PS.ln(LS.freeze_l(R, xs)), PS.ln(LS.sel(LS.cr_out(r), z, LS.cr_limbs(r))), 15n, e0, tr(PS.ln(LS.sel(LS.cr_out(r), z, LS.cr_limbs(r))), PS.ln(z), 15n, sel_len(LS.cr_out(r), z, LS.cr_limbs(r), sy(PS.ln(LS.cr_limbs(r)), PS.ln(z), CN.carry_len(R, z, 19n))), hlz))

# ---- freeze ----

def fz(+R: Nat, +a: FE.Fe) -> List<&2, Nat>:
  LS.freeze_l(R, FE.to_list(a))

def fz_facts(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +a: FE.Fe, +ha: {FV.ok(one, a) == True{} : Bool}) -> {Bool.and(Bool.and(FV.below(fz(R, a), R), Nat.is_lt(FV.lv(fz(R, a)), 1n+pp)), Nat.is_eq(FV.lv(fz(R, a)), Nat.mod(FV.value(a), 1n+pp))) == True{} : Bool}:
  CN.freeze_c(one, h1, pp, hP, R, hR, FE.to_list(a), OP.L15(a), ha)

def fz_below(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +a: FE.Fe, +ha: {FV.ok(one, a) == True{} : Bool}) -> {FV.below(fz(R, a), R) == True{} : Bool}:
  +f = fz_facts(one, h1, pp, hP, R, hR, a, ha)
  L.and_left(FV.below(fz(R, a), R), Nat.is_lt(FV.lv(fz(R, a)), 1n+pp), L.and_left(Bool.and(FV.below(fz(R, a), R), Nat.is_lt(FV.lv(fz(R, a)), 1n+pp)), Nat.is_eq(FV.lv(fz(R, a)), Nat.mod(FV.value(a), 1n+pp)), f))

def fz_lt(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +a: FE.Fe, +ha: {FV.ok(one, a) == True{} : Bool}) -> {Nat.is_lt(FV.lv(fz(R, a)), 1n+pp) == True{} : Bool}:
  +f = fz_facts(one, h1, pp, hP, R, hR, a, ha)
  L.and_right(FV.below(fz(R, a), R), Nat.is_lt(FV.lv(fz(R, a)), 1n+pp), L.and_left(Bool.and(FV.below(fz(R, a), R), Nat.is_lt(FV.lv(fz(R, a)), 1n+pp)), Nat.is_eq(FV.lv(fz(R, a)), Nat.mod(FV.value(a), 1n+pp)), f))

def fz_val(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +a: FE.Fe, +ha: {FV.ok(one, a) == True{} : Bool}) -> {FV.lv(fz(R, a)) == Nat.mod(FV.value(a), 1n+pp) : Nat}:
  +f = fz_facts(one, h1, pp, hP, R, hR, a, ha)
  N.eq_from_is_eq(FV.lv(fz(R, a)), Nat.mod(FV.value(a), 1n+pp), L.and_right(Bool.and(FV.below(fz(R, a), R), Nat.is_lt(FV.lv(fz(R, a)), 1n+pp)), Nat.is_eq(FV.lv(fz(R, a)), Nat.mod(FV.value(a), 1n+pp)), f))

def fz_list(+R: Nat, +a: FE.Fe) -> {FE.to_list(FE.freeze(R, a)) == fz(R, a) : List<&2, Nat>}:
  BR.to_of(fz(R, a), freeze_len(R, FE.to_list(a), OP.L15(a)))

def freeze_value(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +a: FE.Fe, +ha: {FV.ok(one, a) == True{} : Bool}) -> {FV.value(FE.freeze(R, a)) == Nat.mod(FV.value(a), 1n+pp) : Nat}:
  tr(FV.value(FE.freeze(R, a)), FV.lv(fz(R, a)), Nat.mod(FV.value(a), 1n+pp), Equal.cong(List<&2, Nat>, Nat, t => FV.lv(t), FE.to_list(FE.freeze(R, a)), fz(R, a), fz_list(R, a)), fz_val(one, h1, pp, hP, R, hR, a, ha))

def freeze_canon(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +a: FE.Fe, +ha: {FV.ok(one, a) == True{} : Bool}) -> {Bool.and(FV.below(FE.to_list(FE.freeze(R, a)), WD.sc(17n, one)), Nat.is_lt(FV.value(FE.freeze(R, a)), 1n+pp)) == True{} : Bool}:
  +el = Equal.sym(List<&2, Nat>, FE.to_list(FE.freeze(R, a)), fz(R, a), fz_list(R, a))
  +hb = L.subst(List<&2, Nat>, t => {FV.below(t, WD.sc(17n, one)) == True{} : Bool}, fz(R, a), FE.to_list(FE.freeze(R, a)), el, L.subst(Nat, t => {FV.below(fz(R, a), t) == True{} : Bool}, R, WD.sc(17n, one), hR, fz_below(one, h1, pp, hP, R, hR, a, ha)))
  +hl = L.subst(List<&2, Nat>, t => {Nat.is_lt(FV.lv(t), 1n+pp) == True{} : Bool}, fz(R, a), FE.to_list(FE.freeze(R, a)), el, fz_lt(one, h1, pp, hP, R, hR, a, ha))
  L.and_intro(FV.below(FE.to_list(FE.freeze(R, a)), WD.sc(17n, one)), Nat.is_lt(FV.value(FE.freeze(R, a)), 1n+pp), hb, hl)

# ---- the conversions on limb lists (pack.bend) ----

# 15 limbs below 2^17 to 32 bytes: the value
def tb_value(+one: Nat, +h1: {one == 1n : Nat}, +zs: List<&2, Nat>, +hz: {FV.below(zs, WD.sc(17n, one)) == True{} : Bool}, +hl: {PS.ln(zs) == 15n : Nat}) -> {FS.value(LS.to_bytes_l(zs)) == FV.lv(zs) : Nat}:
  PK.up_val(one, h1, zs, 0n, 0n, hz, PW.sc_pos(0n, one, h1), {==})

# 15 limbs to 32 bytes below 256
def tb_tight(+one: Nat, +h1: {one == 1n : Nat}, +zs: List<&2, Nat>, +hl: {PS.ln(zs) == 15n : Nat}) -> {FS.tight(LS.to_bytes_l(zs)) == True{} : Bool}:
  PK.bytes_of(32n, LS.to_bytes_l(zs), tr(PS.ln(LS.nat_of(LS.to_bytes_l(zs))), PK.upn(PS.ln(zs), 0n), 32n, PK.up_len(zs, 0n, 0n), Equal.cong(Nat, Nat, z => PK.upn(z, 0n), PS.ln(zs), 15n, hl)), PK.up_below(zs, 0n, 0n))

def nat_below(+n: Nat, +bs: List<&2, U32>, +h: {FS.bytes_ok(n, bs) == True{} : Bool}) -> {FV.below(LS.nat_of(bs), 256n) == True{} : Bool}:
  match n bs:
    case 0n Nil{}:
      {==}
    case 0n Con{x, xt}:
      Empty.absurd({FV.below(LS.nat_of(Con{x, xt}), 256n) == True{} : Bool}, L.false_true(h))
    case 1n+m Nil{}:
      {==}
    case 1n+ +m Con{+x, +xt}:
      NL.below_con(U32.to_nat(x), LS.nat_of(xt), 256n, L.and_left(Nat.is_lt(U32.to_nat(x), 256n), FS.bytes_ok(m, xt), h), nat_below(m, xt, L.and_right(Nat.is_lt(U32.to_nat(x), 256n), FS.bytes_ok(m, xt), h)))

# every 17-bit limb of bytes below 256: the value, limbs below 2^17
def l17_value(+bs: List<&2, U32>, +hb: {FV.below(LS.nat_of(bs), 256n) == True{} : Bool}) -> {FV.lv(LS.limbs17(bs)) == FS.value(bs) : Nat}:
  PK.pk_val(bs, 0n, 0n, hb, {==})

def l17_below(+one: Nat, +h1: {one == 1n : Nat}, +bs: List<&2, U32>) -> {FV.below(LS.limbs17(bs), WD.sc(17n, one)) == True{} : Bool}:
  PK.pk_below(one, h1, bs, 0n, 0n, PW.sc_pos(0n, one, h1), {==})

# n bytes have pkn(n, 0) limbs
def l17_len(+n: Nat, +bs: List<&2, U32>, +h: {FS.bytes_ok(n, bs) == True{} : Bool}) -> {PS.ln(LS.limbs17(bs)) == PK.pkn(n, 0n) : Nat}:
  tr(PS.ln(LS.limbs17(bs)), PK.pkn(PS.ln(LS.nat_of(bs)), 0n), PK.pkn(n, 0n), PK.pk_len(bs, 0n, 0n), Equal.cong(Nat, Nat, z => PK.pkn(z, 0n), PS.ln(LS.nat_of(bs)), n, PK.bytes_len(n, bs, h)))

def ob_len(+bs: List<&2, U32>) -> {PS.ln(LS.of_bytes_l(bs)) == 15n : Nat}:
  PK.fit_len(15n, LS.limbs17(bs))

def ob_below(+one: Nat, +h1: {one == 1n : Nat}, +bs: List<&2, U32>) -> {FV.below(LS.of_bytes_l(bs), WD.sc(17n, one)) == True{} : Bool}:
  PK.fit_below(15n, LS.limbs17(bs), WD.sc(17n, one), PW.sc_pos(17n, one, h1), l17_below(one, h1, bs))

# 32 bytes to 15 limbs of 17 bits: the value mod 2^255
def ob_value(+one: Nat, +h1: {one == 1n : Nat}, +bs: List<&2, U32>, +hb: {FS.tight(bs) == True{} : Bool}) -> {FV.lv(LS.of_bytes_l(bs)) == Nat.mod(FS.value(bs), WD.sc(255n, one)) : Nat}:
  +P = LS.limbs17(bs)
  +T = FV.lv(LS.of_bytes_l(bs))
  +D = FV.lv(LS.drop(15n, P))
  +Mo = WD.sc(255n, one)
  +b = Nat.sub(Mo, 1n)
  +hb1 = PW.pos_succ(one, h1, 255n)
  +hT = CN.lv_lt15(one, h1, WD.sc(17n, one), {==}, LS.of_bytes_l(bs), ob_len(bs), ob_below(one, h1, bs))
  +e0 = tr(FS.value(bs), FV.lv(P), Nat.add(FV.lv(LS.take(15n, P)), NL.sh(15n, D)), sy(FV.lv(P), FS.value(bs), l17_value(bs, nat_below(32n, bs, hb))), NL.lv_split(15n, P))
  +e1 = tr(FS.value(bs), Nat.add(FV.lv(LS.take(15n, P)), NL.sh(15n, D)), Nat.add(T, WD.sc(255n, D)), e0, M.cong_add(FV.lv(LS.take(15n, P)), T, NL.sh(15n, D), WD.sc(255n, D), sy(T, FV.lv(LS.take(15n, P)), PK.fit_val(15n, P)), NL.sh15(D)))
  +e2 = tr(FS.value(bs), Nat.add(T, WD.sc(255n, D)), Nat.add(Nat.mul(D, Mo), T), e1, tr(Nat.add(T, WD.sc(255n, D)), Nat.add(WD.sc(255n, D), T), Nat.add(Nat.mul(D, Mo), T), NA.add_comm(T, WD.sc(255n, D)), M.cong_l(WD.sc(255n, D), Nat.mul(D, Mo), T, sy(Nat.mul(D, Mo), WD.sc(255n, D), AR.mul_sc1(255n, one, h1, D)))))
  +hT2 = L.subst(Nat, t => {Nat.is_lt(T, t) == True{} : Bool}, Mo, 1n+b, sy(1n+b, Mo, hb1), hT)
  +e3 = L.subst(Nat, t => {Nat.mod(Nat.add(Nat.mul(D, t), T), t) == T : Nat}, 1n+b, Mo, hb1, NR.mod_of(D, b, T, hT2))
  sy(Nat.mod(FS.value(bs), Mo), T, tr(Nat.mod(FS.value(bs), Mo), Nat.mod(Nat.add(Nat.mul(D, Mo), T), Mo), T, Equal.cong(Nat, Nat, t => Nat.mod(t, Mo), FS.value(bs), Nat.add(Nat.mul(D, Mo), T), e2), e3))

# ---- bytes out ----

def to_bytes_value(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +a: FE.Fe, +ha: {FV.ok(one, a) == True{} : Bool}) -> {FS.value(FE.to_bytes(R, a)) == Nat.mod(FV.value(a), 1n+pp) : Nat}:
  +Z = fz(R, a)
  +hlZ = freeze_len(R, FE.to_list(a), OP.L15(a))
  +hZb = L.subst(Nat, t => {FV.below(Z, t) == True{} : Bool}, R, WD.sc(17n, one), hR, fz_below(one, h1, pp, hP, R, hR, a, ha))
  tr(FS.value(LS.to_bytes_l(Z)), FV.lv(Z), Nat.mod(FV.value(a), 1n+pp), tb_value(one, h1, Z, hZb, hlZ), fz_val(one, h1, pp, hP, R, hR, a, ha))

def to_bytes_tight(+one: Nat, +h1: {one == 1n : Nat}, +R: Nat, +a: FE.Fe) -> {FS.tight(FE.to_bytes(R, a)) == True{} : Bool}:
  tb_tight(one, h1, fz(R, a), freeze_len(R, FE.to_list(a), OP.L15(a)))

# ---- bytes in ----

def ob_list(+bs: List<&2, U32>) -> {FE.to_list(FE.of_bytes(bs)) == LS.of_bytes_l(bs) : List<&2, Nat>}:
  BR.to_of(LS.of_bytes_l(bs), ob_len(bs))

def of_bytes_value(+one: Nat, +h1: {one == 1n : Nat}, +bs: List<&2, U32>, +hb: {FS.tight(bs) == True{} : Bool}) -> {FV.value(FE.of_bytes(bs)) == Nat.mod(FS.value(bs), WD.sc(255n, one)) : Nat}:
  tr(FV.value(FE.of_bytes(bs)), FV.lv(LS.of_bytes_l(bs)), Nat.mod(FS.value(bs), WD.sc(255n, one)), Equal.cong(List<&2, Nat>, Nat, t => FV.lv(t), FE.to_list(FE.of_bytes(bs)), LS.of_bytes_l(bs), ob_list(bs)), ob_value(one, h1, bs, hb))

def of_bytes_ok(+one: Nat, +h1: {one == 1n : Nat}, +bs: List<&2, U32>) -> {FV.ok(one, FE.of_bytes(bs)) == True{} : Bool}:
  +h19 = NL.below_mono(LS.of_bytes_l(bs), WD.sc(17n, one), WD.sc(19n, one), PW.le_sc(2n, 17n, one), ob_below(one, h1, bs))
  L.subst(List<&2, Nat>, t => {FV.below(t, WD.sc(19n, one)) == True{} : Bool}, LS.of_bytes_l(bs), FE.to_list(FE.of_bytes(bs)), Equal.sym(List<&2, Nat>, FE.to_list(FE.of_bytes(bs)), LS.of_bytes_l(bs), ob_list(bs)), h19)

# ---- is_zero, eq, parity ----

def and_true(+b: Bool) -> {Bool.and(b, True{}) == b : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def and_assoc(+x: Bool, +y: Bool, +z: Bool) -> {Bool.and(Bool.and(x, y), z) == Bool.and(x, Bool.and(y, z)) : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

def add_eq0(+a: Nat, +b: Nat) -> {Nat.is_eq(Nat.add(a, b), 0n) == Bool.and(Nat.is_eq(a, 0n), Nat.is_eq(b, 0n)) : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+a2:
      {==}

def dbl_eq0(+y: Nat) -> {Nat.is_eq(Nat.double(y), 0n) == Nat.is_eq(y, 0n) : Bool}:
  match y:
    case 0n:
      {==}
    case 1n+y2:
      {==}

def shift_eq0(+k: Nat, +y: Nat) -> {Nat.is_eq(C.shift(k, y), 0n) == Nat.is_eq(y, 0n) : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+ +m:
      Equal.trans(Bool, Nat.is_eq(Nat.double(C.shift(m, y)), 0n), Nat.is_eq(C.shift(m, y), 0n), Nat.is_eq(y, 0n), dbl_eq0(C.shift(m, y)), shift_eq0(m, y))

def sum_eq0(+zs: List<&2, Nat>, +acc: Nat) -> {Nat.is_eq(LS.sum(zs, acc), 0n) == Bool.and(Nat.is_eq(acc, 0n), Nat.is_eq(FV.lv(zs), 0n)) : Bool}:
  match zs:
    case Nil{}:
      Equal.sym(Bool, Bool.and(Nat.is_eq(acc, 0n), True{}), Nat.is_eq(acc, 0n), and_true(Nat.is_eq(acc, 0n)))
    case Con{+x, +t}:
      +a = Nat.is_eq(acc, 0n)
      +bx = Nat.is_eq(x, 0n)
      +bt = Nat.is_eq(FV.lv(t), 0n)
      +e1 = sum_eq0(t, Nat.add(acc, x))
      +e2 = Equal.cong(Bool, Bool, u => Bool.and(u, bt), Nat.is_eq(Nat.add(acc, x), 0n), Bool.and(a, bx), add_eq0(acc, x))
      +e3 = and_assoc(a, bx, bt)
      +e4 = Equal.cong(Bool, Bool, u => Bool.and(a, u), Bool.and(bx, bt), Nat.is_eq(Nat.add(x, C.shift(17n, FV.lv(t))), 0n), Equal.sym(Bool, Nat.is_eq(Nat.add(x, C.shift(17n, FV.lv(t))), 0n), Bool.and(bx, bt), Equal.trans(Bool, Nat.is_eq(Nat.add(x, C.shift(17n, FV.lv(t))), 0n), Bool.and(bx, Nat.is_eq(C.shift(17n, FV.lv(t)), 0n)), Bool.and(bx, bt), add_eq0(x, C.shift(17n, FV.lv(t))), Equal.cong(Bool, Bool, u => Bool.and(bx, u), Nat.is_eq(C.shift(17n, FV.lv(t)), 0n), bt, shift_eq0(17n, FV.lv(t))))))
      Equal.trans(Bool, Nat.is_eq(LS.sum(t, Nat.add(acc, x)), 0n), Bool.and(Nat.is_eq(Nat.add(acc, x), 0n), bt), Bool.and(a, Nat.is_eq(Nat.add(x, C.shift(17n, FV.lv(t))), 0n)), e1, Equal.trans(Bool, Bool.and(Nat.is_eq(Nat.add(acc, x), 0n), bt), Bool.and(Bool.and(a, bx), bt), Bool.and(a, Nat.is_eq(Nat.add(x, C.shift(17n, FV.lv(t))), 0n)), e2, Equal.trans(Bool, Bool.and(Bool.and(a, bx), bt), Bool.and(a, Bool.and(bx, bt)), Bool.and(a, Nat.is_eq(Nat.add(x, C.shift(17n, FV.lv(t))), 0n)), e3, e4)))

def is_zero_val(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +a: FE.Fe, +ha: {FV.ok(one, a) == True{} : Bool}) -> {FE.is_zero(R, a) == Nat.is_eq(Nat.mod(FV.value(a), 1n+pp), 0n) : Bool}:
  Equal.trans(Bool, Nat.is_eq(LS.sum(fz(R, a), 0n), 0n), Nat.is_eq(FV.lv(fz(R, a)), 0n), Nat.is_eq(Nat.mod(FV.value(a), 1n+pp), 0n), sum_eq0(fz(R, a), 0n), Equal.cong(Nat, Bool, u => Nat.is_eq(u, 0n), FV.lv(fz(R, a)), Nat.mod(FV.value(a), 1n+pp), fz_val(one, h1, pp, hP, R, hR, a, ha)))

def eq_val(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +a: FE.Fe, +b: FE.Fe, +ha: {FV.ok(one, a) == True{} : Bool}, +hb: {FV.ok(one, b) == True{} : Bool}) -> {FE.eq(R, a, b) == Nat.is_eq(Nat.mod(FV.value(a), 1n+pp), Nat.mod(FV.value(b), 1n+pp)) : Bool}:
  +P = {1n+pp : Nat}
  +A = Nat.mod(FV.value(a), P)
  +B = Nat.mod(FV.value(b), P)
  +d = FE.sub(R, a, b)
  +e1 = is_zero_val(one, h1, pp, hP, R, hR, d, SB.sub_ok(one, h1, R, hR, a, b, ha))
  +e2 = SB.sub_c(one, h1, pp, hP, R, hR, a, b, hb)
  +e3 = G.c_subm(pp, FV.value(a), A, B, G.c_sym(pp, A, FV.value(a), G.c_mod(pp, FV.value(a))), N.lt_le(B, P, NR.dm_lt(pp, FV.value(b))))
  +e4 = Equal.trans(Nat, Nat.mod(FV.value(d), P), Nat.mod(Nat.sub(Nat.add(FV.value(a), P), B), P), Nat.mod(EA.pw(pp, A, B), P), e2, e3)
  +e5 = Equal.cong(Nat, Bool, z => Nat.is_eq(z, 0n), Nat.mod(FV.value(d), P), Nat.mod(EA.pw(pp, A, B), P), e4)
  Equal.trans(Bool, FE.eq(R, a, b), Nat.is_eq(Nat.mod(FV.value(d), P), 0n), Nat.is_eq(A, B), e1, Equal.trans(Bool, Nat.is_eq(Nat.mod(FV.value(d), P), 0n), Nat.is_eq(Nat.mod(EA.pw(pp, A, B), P), 0n), Nat.is_eq(A, B), e5, EA.eq_bool(pp, A, B, NR.dm_lt(pp, FV.value(a)), NR.dm_lt(pp, FV.value(b)), Nat.is_eq(A, B), {==})))

def head_mod2(+zs: List<&2, Nat>) -> {Nat.mod(LS.head(zs), 2n) == Nat.mod(FV.lv(zs), 2n) : Nat}:
  match zs:
    case Nil{}:
      {==}
    case Con{+z, +t}:
      +y = C.shift(16n, FV.lv(t))
      +e1 = tr(Nat.add(z, C.shift(17n, FV.lv(t))), Nat.add(z, Nat.mul(y, 2n)), Nat.add(Nat.mul(y, 2n), z), M.cong_r(z, Nat.double(y), Nat.mul(y, 2n), tr(Nat.double(y), Nat.mul(2n, y), Nat.mul(y, 2n), NA.double_mul(y), NA.mul_comm(2n, y))), NA.add_comm(z, Nat.mul(y, 2n)))
      sy(Nat.mod(Nat.add(z, C.shift(17n, FV.lv(t))), 2n), Nat.mod(z, 2n), tr(Nat.mod(Nat.add(z, C.shift(17n, FV.lv(t))), 2n), Nat.mod(Nat.add(Nat.mul(y, 2n), z), 2n), Nat.mod(z, 2n), Equal.cong(Nat, Nat, u => Nat.mod(u, 2n), Nat.add(z, C.shift(17n, FV.lv(t))), Nat.add(Nat.mul(y, 2n), z), e1), NR.absorb(1n, y, z)))

def parity_val(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +a: FE.Fe, +ha: {FV.ok(one, a) == True{} : Bool}) -> {U32.to_nat(FE.parity(R, a)) == Nat.mod(Nat.mod(FV.value(a), 1n+pp), 2n) : Nat}:
  +h0 = LS.head(fz(R, a))
  +m = Nat.mod(h0, 2n)
  +e1 = U.to_nat_from_nat(m, 1n, {==}, NR.dm_lt(1n, h0))
  tr(U32.to_nat(U32.from_nat(m)), m, Nat.mod(Nat.mod(FV.value(a), 1n+pp), 2n), e1, tr(m, Nat.mod(FV.lv(fz(R, a)), 2n), Nat.mod(Nat.mod(FV.value(a), 1n+pp), 2n), head_mod2(fz(R, a)), Equal.cong(Nat, Nat, u => Nat.mod(u, 2n), FV.lv(fz(R, a)), Nat.mod(FV.value(a), 1n+pp), fz_val(one, h1, pp, hP, R, hR, a, ha))))
