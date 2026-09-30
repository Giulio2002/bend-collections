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
import ./carry.bend as CA
import ./pass.bend as PS
import ./ops.bend as OP
import ./sub.bend as SB
import ./canon.bend as CN
import ./bytes.bend as BY
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

# ---- bytes out ----

def bits_all_len(+w: Nat, +xs: List<&2, Nat>) -> {PS.ln(LS.bits_all(w, xs)) == Nat.mul(PS.ln(xs), w) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +xt}:
      tr(PS.ln(LS.app(LS.bits(w, x), LS.bits_all(w, xt))), Nat.add(PS.ln(LS.bits(w, x)), PS.ln(LS.bits_all(w, xt))), Nat.add(w, Nat.mul(PS.ln(xt), w)), BY.app_len(LS.bits(w, x), LS.bits_all(w, xt)), M.cong_add(PS.ln(LS.bits(w, x)), w, PS.ln(LS.bits_all(w, xt)), Nat.mul(PS.ln(xt), w), BY.bits_len(w, x), bits_all_len(w, xt)))

def group_len(+w: Nat, +n: Nat, +bs: List<&2, Nat>) -> {PS.ln(LS.group(w, n, bs)) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+ +m:
      Equal.cong(Nat, Nat, t => 1n+t, PS.ln(LS.group(w, m, LS.drop(w, bs))), m, group_len(w, m, LS.drop(w, bs)))

def group_below(+one: Nat, +h1: {one == 1n : Nat}, +w: Nat, +n: Nat, +bs: List<&2, Nat>, +h: {FV.below(bs, 2n) == True{} : Bool}) -> {FV.below(LS.group(w, n, bs), WD.sc(w, one)) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+ +m:
      NL.below_con(LS.unbits(w, bs), LS.group(w, m, LS.drop(w, bs)), WD.sc(w, one), BY.unbits_lt(one, h1, w, bs, h), group_below(one, h1, w, m, LS.drop(w, bs), BY.drop_lt2(w, bs, h)))

def u32_val(+xs: List<&2, Nat>, +h: {FV.below(xs, 256n) == True{} : Bool}) -> {FS.value(LS.u32_of(xs)) == BY.lvw(8n, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +xt}:
      M.cong_add(U32.to_nat(U32.from_nat(x)), x, C.shift(8n, FS.value(LS.u32_of(xt))), WD.sc(8n, BY.lvw(8n, xt)), U.to_nat_from_nat(x, 8n, {==}, NL.below_head(x, xt, 256n, h)), M.cong_sc(8n, FS.value(LS.u32_of(xt)), BY.lvw(8n, xt), u32_val(xt, NL.below_tail(x, xt, 256n, h))))

def u32_bytes(+n: Nat, +xs: List<&2, Nat>, +hl: {PS.ln(xs) == n : Nat}, +h: {FV.below(xs, 256n) == True{} : Bool}) -> {FS.bytes_ok(n, LS.u32_of(xs)) == True{} : Bool}:
  match n xs:
    case 0n Nil{}:
      {==}
    case 0n Con{x, xt}:
      Empty.absurd({FS.bytes_ok(0n, LS.u32_of(Con{x, xt})) == True{} : Bool}, N.succ_zero(PS.ln(xt), hl))
    case 1n+m Nil{}:
      Empty.absurd({FS.bytes_ok(1n+m, Nil{}) == True{} : Bool}, N.zero_succ(m, hl))
    case 1n+ +m Con{+x, +xt}:
      +hx = L.subst(Nat, t => {Nat.is_lt(t, 256n) == True{} : Bool}, x, U32.to_nat(U32.from_nat(x)), sy(U32.to_nat(U32.from_nat(x)), x, U.to_nat_from_nat(x, 8n, {==}, NL.below_head(x, xt, 256n, h))), NL.below_head(x, xt, 256n, h))
      L.and_intro(Nat.is_lt(U32.to_nat(U32.from_nat(x)), 256n), FS.bytes_ok(m, LS.u32_of(xt)), hx, u32_bytes(m, xt, N.succ_inj(PS.ln(xt), m, hl), NL.below_tail(x, xt, 256n, h)))

def bits17(+R: Nat, +a: FE.Fe) -> List<&2, Nat>:
  LS.bits_all(17n, fz(R, a))

def g8(+R: Nat, +a: FE.Fe) -> List<&2, Nat>:
  LS.group(8n, 32n, bits17(R, a))

def g8_below(+one: Nat, +h1: {one == 1n : Nat}, +R: Nat, +a: FE.Fe) -> {FV.below(g8(R, a), 256n) == True{} : Bool}:
  L.subst(Nat, o => {FV.below(g8(R, a), WD.sc(8n, o)) == True{} : Bool}, one, 1n, h1, group_below(one, h1, 8n, 32n, bits17(R, a), BY.bits_all_lt(17n, fz(R, a))))

def to_bytes_value(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +a: FE.Fe, +ha: {FV.ok(one, a) == True{} : Bool}) -> {FS.value(FE.to_bytes(R, a)) == Nat.mod(FV.value(a), 1n+pp) : Nat}:
  +Z = fz(R, a)
  +B = bits17(R, a)
  +hlZ = freeze_len(R, FE.to_list(a), OP.L15(a))
  +hlB = tr(PS.ln(B), Nat.mul(PS.ln(Z), 17n), 255n, bits_all_len(17n, Z), Equal.cong(Nat, Nat, t => Nat.mul(t, 17n), PS.ln(Z), 15n, hlZ))
  +hfit = BY.fits_len(8n, 32n, B, L.subst(Nat, t => {Nat.is_le(t, 256n) == True{} : Bool}, 255n, PS.ln(B), sy(PS.ln(B), 255n, hlB), {==}))
  +hZb = L.subst(Nat, t => {FV.below(Z, t) == True{} : Bool}, R, WD.sc(17n, one), hR, fz_below(one, h1, pp, hP, R, hR, a, ha))
  +e1 = u32_val(g8(R, a), g8_below(one, h1, R, a))
  +e2 = BY.group_val(8n, 32n, B, hfit)
  +e3 = BY.bits_all_val(one, h1, 17n, Z, hZb)
  +e4 = BY.lvw17(Z)
  tr(FS.value(LS.u32_of(g8(R, a))), BY.lvw(8n, g8(R, a)), Nat.mod(FV.value(a), 1n+pp), e1, tr(BY.lvw(8n, g8(R, a)), BY.bv(B), Nat.mod(FV.value(a), 1n+pp), e2, tr(BY.bv(B), BY.lvw(17n, Z), Nat.mod(FV.value(a), 1n+pp), e3, tr(BY.lvw(17n, Z), FV.lv(Z), Nat.mod(FV.value(a), 1n+pp), e4, fz_val(one, h1, pp, hP, R, hR, a, ha)))))

def to_bytes_tight(+one: Nat, +h1: {one == 1n : Nat}, +R: Nat, +a: FE.Fe) -> {FS.tight(FE.to_bytes(R, a)) == True{} : Bool}:
  u32_bytes(32n, g8(R, a), group_len(8n, 32n, bits17(R, a)), g8_below(one, h1, R, a))

# ---- bytes in ----

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

def unbits_take(+n: Nat, +bs: List<&2, Nat>) -> {LS.unbits(n, bs) == BY.bv(LS.take(n, bs)) : Nat}:
  match n bs:
    case 0n _:
      {==}
    case 1n+m Nil{}:
      {==}
    case 1n+ +m Con{+b, +bt}:
      M.cong_r(b, Nat.double(LS.unbits(m, bt)), Nat.double(BY.bv(LS.take(m, bt))), Equal.cong(Nat, Nat, t => Nat.double(t), LS.unbits(m, bt), BY.bv(LS.take(m, bt)), unbits_take(m, bt)))

# the low n bits: value mod 2^n
def take_mod(+one: Nat, +h1: {one == 1n : Nat}, +n: Nat, +bs: List<&2, Nat>, +h: {FV.below(bs, 2n) == True{} : Bool}) -> {BY.bv(LS.take(n, bs)) == Nat.mod(BY.bv(bs), WD.sc(n, one)) : Nat}:
  +T = BY.bv(LS.take(n, bs))
  +D = BY.bv(LS.drop(n, bs))
  +Mo = WD.sc(n, one)
  +b = Nat.sub(Mo, 1n)
  +hb = N.sub_add(Mo, 1n, N.lt_succ_le_succ(0n, Mo, PW.sc_pos(n, one, h1)))
  +hT = L.subst(Nat, t => {Nat.is_lt(t, Mo) == True{} : Bool}, LS.unbits(n, bs), T, unbits_take(n, bs), BY.unbits_lt(one, h1, n, bs, h))
  +e1 = tr(BY.bv(bs), Nat.add(T, WD.sc(n, D)), Nat.add(Nat.mul(D, Mo), T), tr(BY.bv(bs), Nat.add(LS.unbits(n, bs), WD.sc(n, D)), Nat.add(T, WD.sc(n, D)), BY.split_val(n, bs), M.cong_l(LS.unbits(n, bs), T, WD.sc(n, D), unbits_take(n, bs))), tr(Nat.add(T, WD.sc(n, D)), Nat.add(WD.sc(n, D), T), Nat.add(Nat.mul(D, Mo), T), NA.add_comm(T, WD.sc(n, D)), M.cong_l(WD.sc(n, D), Nat.mul(D, Mo), T, sy(Nat.mul(D, Mo), WD.sc(n, D), AR.mul_sc1(n, one, h1, D)))))
  +hT2 = L.subst(Nat, t => {Nat.is_lt(T, t) == True{} : Bool}, Mo, 1n+b, sy(1n+b, Mo, hb), hT)
  +e2 = L.subst(Nat, t => {Nat.mod(Nat.add(Nat.mul(D, t), T), t) == T : Nat}, 1n+b, Mo, hb, NR.mod_of(D, b, T, hT2))
  sy(Nat.mod(BY.bv(bs), Mo), T, tr(Nat.mod(BY.bv(bs), Mo), Nat.mod(Nat.add(Nat.mul(D, Mo), T), Mo), T, Equal.cong(Nat, Nat, t => Nat.mod(t, Mo), BY.bv(bs), Nat.add(Nat.mul(D, Mo), T), e1), e2))

def ob_bits(+bs: List<&2, U32>) -> List<&2, Nat>:
  LS.take(255n, LS.bits_all(8n, LS.nat_of(bs)))

def ob_group(+bs: List<&2, U32>) -> List<&2, Nat>:
  LS.group(17n, 15n, ob_bits(bs))

def ob_list(+bs: List<&2, U32>) -> {FE.to_list(FE.of_bytes(bs)) == ob_group(bs) : List<&2, Nat>}:
  BR.to_of(ob_group(bs), group_len(17n, 15n, ob_bits(bs)))

def of_bytes_value(+one: Nat, +h1: {one == 1n : Nat}, +bs: List<&2, U32>, +hb: {FS.tight(bs) == True{} : Bool}) -> {FV.value(FE.of_bytes(bs)) == Nat.mod(FS.value(bs), WD.sc(255n, one)) : Nat}:
  +B = LS.bits_all(8n, LS.nat_of(bs))
  +T = ob_bits(bs)
  +e0 = Equal.cong(List<&2, Nat>, Nat, t => FV.lv(t), FE.to_list(FE.of_bytes(bs)), ob_group(bs), ob_list(bs))
  +e1 = sy(BY.lvw(17n, ob_group(bs)), FV.lv(ob_group(bs)), BY.lvw17(ob_group(bs)))
  +hfit = BY.fits_len(17n, 15n, T, BY.take_len(255n, B))
  +e2 = BY.group_val(17n, 15n, T, hfit)
  +e3 = take_mod(one, h1, 255n, B, BY.bits_all_lt(8n, LS.nat_of(bs)))
  +hn = L.subst(Nat, o => {FV.below(LS.nat_of(bs), WD.sc(8n, o)) == True{} : Bool}, 1n, one, Equal.sym(Nat, one, 1n, h1), nat_below(32n, bs, hb))
  +e4 = tr(BY.bv(B), BY.lvw(8n, LS.nat_of(bs)), FS.value(bs), BY.bits_all_val(one, h1, 8n, LS.nat_of(bs), hn), BY.lvw8(bs))
  tr(FV.value(FE.of_bytes(bs)), FV.lv(ob_group(bs)), Nat.mod(FS.value(bs), WD.sc(255n, one)), e0, tr(FV.lv(ob_group(bs)), BY.lvw(17n, ob_group(bs)), Nat.mod(FS.value(bs), WD.sc(255n, one)), e1, tr(BY.lvw(17n, ob_group(bs)), BY.bv(T), Nat.mod(FS.value(bs), WD.sc(255n, one)), e2, tr(BY.bv(T), Nat.mod(BY.bv(B), WD.sc(255n, one)), Nat.mod(FS.value(bs), WD.sc(255n, one)), e3, Equal.cong(Nat, Nat, t => Nat.mod(t, WD.sc(255n, one)), BY.bv(B), FS.value(bs), e4)))))

def of_bytes_ok(+one: Nat, +h1: {one == 1n : Nat}, +bs: List<&2, U32>) -> {FV.ok(one, FE.of_bytes(bs)) == True{} : Bool}:
  +B = LS.bits_all(8n, LS.nat_of(bs))
  +h17 = group_below(one, h1, 17n, 15n, ob_bits(bs), NL.take_below(255n, B, 2n, BY.bits_all_lt(8n, LS.nat_of(bs))))
  +h19 = NL.below_mono(ob_group(bs), WD.sc(17n, one), WD.sc(19n, one), PW.le_sc(2n, 17n, one), h17)
  L.subst(List<&2, Nat>, t => {FV.below(t, WD.sc(19n, one)) == True{} : Bool}, ob_group(bs), FE.to_list(FE.of_bytes(bs)), Equal.sym(List<&2, Nat>, FE.to_list(FE.of_bytes(bs)), ob_group(bs), ob_list(bs)), h19)

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

# ---- the conversions on limb lists ----

# 15 limbs below 2^17 to 32 bytes: the value
def tb_value(+one: Nat, +h1: {one == 1n : Nat}, +zs: List<&2, Nat>, +hz: {FV.below(zs, WD.sc(17n, one)) == True{} : Bool}, +hl: {PS.ln(zs) == 15n : Nat}) -> {FS.value(LS.to_bytes_l(zs)) == FV.lv(zs) : Nat}:
  +B = LS.bits_all(17n, zs)
  +G8 = LS.group(8n, 32n, B)
  +hlB = tr(PS.ln(B), Nat.mul(PS.ln(zs), 17n), 255n, bits_all_len(17n, zs), Equal.cong(Nat, Nat, z => Nat.mul(z, 17n), PS.ln(zs), 15n, hl))
  +hfit = BY.fits_len(8n, 32n, B, L.subst(Nat, t => {Nat.is_le(t, 256n) == True{} : Bool}, 255n, PS.ln(B), sy(PS.ln(B), 255n, hlB), {==}))
  +hg = L.subst(Nat, o => {FV.below(G8, WD.sc(8n, o)) == True{} : Bool}, one, 1n, h1, group_below(one, h1, 8n, 32n, B, BY.bits_all_lt(17n, zs)))
  tr(FS.value(LS.u32_of(G8)), BY.lvw(8n, G8), FV.lv(zs), u32_val(G8, hg), tr(BY.lvw(8n, G8), BY.bv(B), FV.lv(zs), BY.group_val(8n, 32n, B, hfit), tr(BY.bv(B), BY.lvw(17n, zs), FV.lv(zs), BY.bits_all_val(one, h1, 17n, zs, hz), BY.lvw17(zs))))

def tb_tight(+one: Nat, +h1: {one == 1n : Nat}, +zs: List<&2, Nat>) -> {FS.tight(LS.to_bytes_l(zs)) == True{} : Bool}:
  +B = LS.bits_all(17n, zs)
  +G8 = LS.group(8n, 32n, B)
  +hg = L.subst(Nat, o => {FV.below(G8, WD.sc(8n, o)) == True{} : Bool}, one, 1n, h1, group_below(one, h1, 8n, 32n, B, BY.bits_all_lt(17n, zs)))
  u32_bytes(32n, G8, group_len(8n, 32n, B), hg)

# 32 bytes to 15 limbs of 17 bits: the value mod 2^255, limbs below 2^17
def ob_value(+one: Nat, +h1: {one == 1n : Nat}, +bs: List<&2, U32>, +hb: {FS.tight(bs) == True{} : Bool}) -> {FV.lv(LS.of_bytes_l(bs)) == Nat.mod(FS.value(bs), WD.sc(255n, one)) : Nat}:
  +B = LS.bits_all(8n, LS.nat_of(bs))
  +T = ob_bits(bs)
  +e1 = sy(BY.lvw(17n, ob_group(bs)), FV.lv(ob_group(bs)), BY.lvw17(ob_group(bs)))
  +hfit = BY.fits_len(17n, 15n, T, BY.take_len(255n, B))
  +e2 = BY.group_val(17n, 15n, T, hfit)
  +e3 = take_mod(one, h1, 255n, B, BY.bits_all_lt(8n, LS.nat_of(bs)))
  +hn = L.subst(Nat, o => {FV.below(LS.nat_of(bs), WD.sc(8n, o)) == True{} : Bool}, 1n, one, Equal.sym(Nat, one, 1n, h1), nat_below(32n, bs, hb))
  +e4 = tr(BY.bv(B), BY.lvw(8n, LS.nat_of(bs)), FS.value(bs), BY.bits_all_val(one, h1, 8n, LS.nat_of(bs), hn), BY.lvw8(bs))
  tr(FV.lv(ob_group(bs)), BY.lvw(17n, ob_group(bs)), Nat.mod(FS.value(bs), WD.sc(255n, one)), e1, tr(BY.lvw(17n, ob_group(bs)), BY.bv(T), Nat.mod(FS.value(bs), WD.sc(255n, one)), e2, tr(BY.bv(T), Nat.mod(BY.bv(B), WD.sc(255n, one)), Nat.mod(FS.value(bs), WD.sc(255n, one)), e3, Equal.cong(Nat, Nat, t => Nat.mod(t, WD.sc(255n, one)), BY.bv(B), FS.value(bs), e4))))

def ob_below(+one: Nat, +h1: {one == 1n : Nat}, +bs: List<&2, U32>) -> {FV.below(LS.of_bytes_l(bs), WD.sc(17n, one)) == True{} : Bool}:
  group_below(one, h1, 17n, 15n, ob_bits(bs), NL.take_below(255n, LS.bits_all(8n, LS.nat_of(bs)), 2n, BY.bits_all_lt(8n, LS.nat_of(bs))))

def ob_len(+bs: List<&2, U32>) -> {PS.ln(LS.of_bytes_l(bs)) == 15n : Nat}:
  group_len(17n, 15n, ob_bits(bs))
