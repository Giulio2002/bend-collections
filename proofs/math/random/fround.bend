import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/math/f64.bend as SF
import ../../../spec/math/w64.bend as SW
import ../../../src/math/f64.bend as F
import ../../../src/math/w64.bend as X
import ../../../src/math/u64.bend as WU
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../typed/width.bend as WW
import ../typed/u32laws.bend as LW
import ../typed/w64add.bend as WA
import ../typed/f64bits.bend as FB
import ../typed/natcmp.bend as NC
import ../typed/w64sh.bend as SH
import ../../lib/u32.bend as U
import ../../lib/u32half.bend as UH
import ../../lib/u32alg.bend as A
import ../../lib/word.bend as WD
import ../../lib/lemmas/spec/numeric.bend as S
import ../../../src/math/natural.bend as M
import ../natural/bits.bend as BT
import ../typed/f64bl.bend as FO

# Copied from proofs/math/typed/f64round.bend and f64rtools.bend: only the
# lemmas proofs/math/random/float.bend needs (and their dependencies), so the
# random proofs do not re-check the heavy rounding lemmas (rj2, rp_nc, ...).

def bits(+s: Bool, +n: Nat) -> F.F64:
  F.Bits{U32.from_nat(C.low(32n, n)), U32.from_nat(Nat.add(C.high(32n, n), C.shift(31n, SF.b2n(s))))}

def enc_bits(+s: Bool, +ef: Nat, +f: Nat) -> {SF.encode(s, ef, f) == bits(s, Nat.add(f, C.shift(52n, ef))) : F.F64}:
  +t = C.shift(20n, ef)
  +n = Nat.add(f, C.shift(52n, ef))
  +b = C.shift(31n, SF.b2n(s))
  +e52 = WW.shift_comp(32n, 20n, ef)
  +el = Equal.trans(Nat, C.low(32n, n), C.low(32n, Nat.add(f, C.shift(32n, t))), C.low(32n, f), Equal.cong(Nat, Nat, z => C.low(32n, Nat.add(f, z)), C.shift(52n, ef), C.shift(32n, t), e52), WW.low_add_shift(32n, f, t))
  +eh0 = Equal.trans(Nat, C.high(32n, n), C.high(32n, Nat.add(f, C.shift(32n, t))), Nat.add(C.high(32n, f), t), Equal.cong(Nat, Nat, z => C.high(32n, Nat.add(f, z)), C.shift(52n, ef), C.shift(32n, t), e52), WW.high_add_shift(32n, f, t))
  +eh = Equal.trans(Nat, Nat.add(C.high(32n, n), b), Nat.add(Nat.add(C.high(32n, f), t), b), Nat.add(C.high(32n, f), C.shift(20n, Nat.add(ef, C.shift(11n, SF.b2n(s))))), Equal.cong(Nat, Nat, z => Nat.add(z, b), C.high(32n, n), Nat.add(C.high(32n, f), t), eh0), FB.fold(C.high(32n, f), ef, SF.b2n(s)))
  +e = Equal.trans(F.F64, bits(s, n), F.Bits{U32.from_nat(C.low(32n, f)), U32.from_nat(Nat.add(C.high(32n, n), b))}, SF.encode(s, ef, f), Equal.cong(Nat, F.F64, z => F.Bits{U32.from_nat(z), U32.from_nat(Nat.add(C.high(32n, n), b))}, C.low(32n, n), C.low(32n, f), el), Equal.cong(Nat, F.F64, z => F.Bits{U32.from_nat(C.low(32n, f)), U32.from_nat(z)}, Nat.add(C.high(32n, n), b), Nat.add(C.high(32n, f), C.shift(20n, Nat.add(ef, C.shift(11n, SF.b2n(s))))), eh))
  Equal.sym(F.F64, bits(s, n), SF.encode(s, ef, f), e)

def rne_c(+q: Nat, +c: Cmp) -> Nat:
  Nat.add(q, SF.b2n(Bool.or(Cmp.is_lt(SF.flip(c)), Bool.and(Cmp.is_eq(c), Nat.is_eq(Nat.mod(q, 2n), 1n)))))

def rne_cmp(+q: Nat, +r: Nat, +h: Nat) -> {SF.rne_up(q, r, h) == rne_c(q, Nat.cmp(r, h)) : Nat}:
  Equal.cong(Cmp, Nat, t => Nat.add(q, SF.b2n(Bool.or(Cmp.is_lt(t), Bool.and(Cmp.is_eq(Nat.cmp(r, h)), Nat.is_eq(Nat.mod(q, 2n), 1n))))), Nat.cmp(h, r), SF.flip(Nat.cmp(r, h)), Equal.sym(Cmp, SF.flip(Nat.cmp(r, h)), Nat.cmp(h, r), NC.cmp_flip(r, h)))

def fz(+d: Nat) -> {C.fits(d, 0n) == True{} : Bool}:
  match d:
    case 0n:
      {==}
    case 1n+ +p:
      fz(p)

def fits_add1(+k: Nat, +a: Nat, +b: Nat, +ha: {C.fits(k, a) == True{} : Bool}, +hb: {C.fits(k, b) == True{} : Bool}) -> {C.fits(1n+k, Nat.add(a, b)) == True{} : Bool}:
  +P = C.pow2(k)
  +h1 = N.lt_add_r2(a, P, b, WW.lt_of_fits(k, a, ha))
  +h2 = N.lt_add_left(b, P, P, WW.lt_of_fits(k, b, hb))
  +h3 = N.lt_trans(Nat.add(a, b), Nat.add(P, b), Nat.add(P, P), h1, h2)
  +h4 = L.subst(Nat, z => {Nat.is_lt(Nat.add(a, b), z) == True{} : Bool}, Nat.add(P, P), Nat.double(P), Equal.sym(Nat, Nat.double(P), Nat.add(P, P), NA.double_self(P)), h3)
  WW.fits_of_lt(1n+k, Nat.add(a, b), h4)

def sub_add_r(+a: Nat, +b: Nat, +m: Nat, +h: {Nat.is_le(m, a) == True{} : Bool}) -> {Nat.sub(Nat.add(a, b), m) == Nat.add(Nat.sub(a, m), b) : Nat}:
  +d = Nat.sub(a, m)
  Equal.trans(Nat, Nat.sub(Nat.add(a, b), m), Nat.sub(Nat.add(Nat.add(m, d), b), m), Nat.add(d, b), Equal.cong(Nat, Nat, z => Nat.sub(Nat.add(z, b), m), a, Nat.add(m, d), Equal.sym(Nat, Nat.add(m, d), a, N.sub_add(a, m, h))), Equal.trans(Nat, Nat.sub(Nat.add(Nat.add(m, d), b), m), Nat.sub(Nat.add(m, Nat.add(d, b)), m), Nat.add(d, b), Equal.cong(Nat, Nat, z => Nat.sub(z, m), Nat.add(Nat.add(m, d), b), Nat.add(m, Nat.add(d, b)), NA.add_assoc(m, d, b)), N.add_sub_cancel(m, Nat.add(d, b))))

def parq(+q: Nat) -> {Nat.add(q, SF.b2n(Nat.is_eq(C.bit(q), 1n))) == Nat.double(C.half(Nat.add(q, 1n))) : Nat}:
  match q:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n+ +p:
      Equal.cong(Nat, Nat, z => 2n+z, Nat.add(p, SF.b2n(Nat.is_eq(C.bit(p), 1n))), Nat.double(C.half(Nat.add(p, 1n))), parq(p))

def subm(+n: Nat) -> {Nat.sub(n, Nat.mod(n, 2n)) == Nat.double(C.half(n)) : Nat}:
  Equal.trans(Nat, Nat.sub(n, Nat.mod(n, 2n)), Nat.sub(n, C.bit(n)), Nat.double(C.half(n)), Equal.cong(Nat, Nat, z => Nat.sub(n, z), Nat.mod(n, 2n), C.bit(n), Equal.sym(Nat, C.bit(n), Nat.mod(n, 2n), WW.bit_mod(n))), Equal.trans(Nat, Nat.sub(n, C.bit(n)), Nat.sub(Nat.add(C.bit(n), Nat.double(C.half(n))), C.bit(n)), Nat.double(C.half(n)), Equal.cong(Nat, Nat, z => Nat.sub(z, C.bit(n)), n, Nat.add(C.bit(n), Nat.double(C.half(n))), WW.hb(n)), N.add_sub_cancel(C.bit(n), Nat.double(C.half(n)))))

def rp_c(+q0: Nat, +r0: Nat, +hr: {C.fits(10n, r0) == True{} : Bool}, +c: Cmp, +hc: {Nat.cmp(r0, 512n) == c : Cmp}) -> {SF.pick(Nat, Nat.is_eq(r0, 512n), Nat.sub(Nat.add(q0, C.high(10n, Nat.add(r0, 512n))), Nat.mod(Nat.add(q0, C.high(10n, Nat.add(r0, 512n))), 2n)), Nat.add(q0, C.high(10n, Nat.add(r0, 512n)))) == SF.rne_up(q0, r0, 512n) : Nat}:
  match c:
    case LT{}:
      +hlt = NC.lt_of_cmp(r0, 512n, hc)
      +he = Equal.cong(Cmp, Bool, t => Cmp.is_eq(t), Nat.cmp(r0, 512n), LT{}, hc)
      +hg = Equal.cong(Cmp, Bool, t => Cmp.is_lt(t), Nat.cmp(512n, r0), GT{}, Equal.trans(Cmp, Nat.cmp(512n, r0), SF.flip(Nat.cmp(r0, 512n)), GT{}, Equal.sym(Cmp, SF.flip(Nat.cmp(r0, 512n)), Nat.cmp(512n, r0), NC.cmp_flip(r0, 512n)), Equal.cong(Cmp, Cmp, t => SF.flip(t), Nat.cmp(r0, 512n), LT{}, hc)))
      +f = WW.fits_of_lt(10n, Nat.add(r0, 512n), N.lt_add_r2(r0, 512n, 512n, hlt))
      +h0 = N.eq_from_is_eq(C.high(10n, Nat.add(r0, 512n)), 0n, f)
      +l1 = Equal.cong(Bool, Nat, t => SF.pick(Nat, t, Nat.sub(Nat.add(q0, C.high(10n, Nat.add(r0, 512n))), Nat.mod(Nat.add(q0, C.high(10n, Nat.add(r0, 512n))), 2n)), Nat.add(q0, C.high(10n, Nat.add(r0, 512n)))), Nat.is_eq(r0, 512n), False{}, he)
      +l2 = Equal.cong(Nat, Nat, z => Nat.add(q0, z), C.high(10n, Nat.add(r0, 512n)), 0n, h0)
      +r1 = Equal.cong(Bool, Nat, t => Nat.add(q0, SF.b2n(Bool.or(t, Bool.and(Nat.is_eq(r0, 512n), Nat.is_eq(Nat.mod(q0, 2n), 1n))))), Nat.is_lt(512n, r0), False{}, hg)
      +r2 = Equal.cong(Bool, Nat, t => Nat.add(q0, SF.b2n(Bool.or(False{}, Bool.and(t, Nat.is_eq(Nat.mod(q0, 2n), 1n))))), Nat.is_eq(r0, 512n), False{}, he)
      Equal.trans(Nat, SF.pick(Nat, Nat.is_eq(r0, 512n), Nat.sub(Nat.add(q0, C.high(10n, Nat.add(r0, 512n))), Nat.mod(Nat.add(q0, C.high(10n, Nat.add(r0, 512n))), 2n)), Nat.add(q0, C.high(10n, Nat.add(r0, 512n)))), Nat.add(q0, C.high(10n, Nat.add(r0, 512n))), SF.rne_up(q0, r0, 512n), l1, Equal.trans(Nat, Nat.add(q0, C.high(10n, Nat.add(r0, 512n))), Nat.add(q0, 0n), SF.rne_up(q0, r0, 512n), l2, Equal.sym(Nat, SF.rne_up(q0, r0, 512n), Nat.add(q0, 0n), Equal.trans(Nat, SF.rne_up(q0, r0, 512n), Nat.add(q0, SF.b2n(Bool.or(False{}, Bool.and(Nat.is_eq(r0, 512n), Nat.is_eq(Nat.mod(q0, 2n), 1n))))), Nat.add(q0, 0n), r1, r2))))
    case GT{}:
      +hgt = NC.lt_of_gt(r0, 512n, hc)
      +he = Equal.cong(Cmp, Bool, t => Cmp.is_eq(t), Nat.cmp(r0, 512n), GT{}, hc)
      +d = Nat.sub(r0, 512n)
      +ed = N.sub_add(r0, 512n, N.lt_le(512n, r0, hgt))
      +ex = Equal.trans(Nat, Nat.add(r0, 512n), Nat.add(Nat.add(512n, d), 512n), Nat.add(d, C.shift(10n, 1n)), Equal.cong(Nat, Nat, z => Nat.add(z, 512n), r0, Nat.add(512n, d), Equal.sym(Nat, Nat.add(512n, d), r0, ed)), Equal.trans(Nat, Nat.add(Nat.add(512n, d), 512n), Nat.add(512n, Nat.add(d, 512n)), Nat.add(d, C.shift(10n, 1n)), NA.add_assoc(512n, d, 512n), Equal.trans(Nat, Nat.add(512n, Nat.add(d, 512n)), Nat.add(1024n, d), Nat.add(d, C.shift(10n, 1n)), Equal.cong(Nat, Nat, z => Nat.add(512n, z), Nat.add(d, 512n), Nat.add(512n, d), NA.add_comm(d, 512n)), NA.add_comm(1024n, d))))
      +hd = SH.fits_lek(10n, d, r0, UH.sub_le(r0, 512n), hr)
      +h1 = Equal.trans(Nat, C.high(10n, Nat.add(r0, 512n)), C.high(10n, Nat.add(d, C.shift(10n, 1n))), 1n, Equal.cong(Nat, Nat, z => C.high(10n, z), Nat.add(r0, 512n), Nat.add(d, C.shift(10n, 1n)), ex), WW.high_u(10n, d, 1n, hd))
      +l1 = Equal.cong(Bool, Nat, t => SF.pick(Nat, t, Nat.sub(Nat.add(q0, C.high(10n, Nat.add(r0, 512n))), Nat.mod(Nat.add(q0, C.high(10n, Nat.add(r0, 512n))), 2n)), Nat.add(q0, C.high(10n, Nat.add(r0, 512n)))), Nat.is_eq(r0, 512n), False{}, he)
      +l2 = Equal.cong(Nat, Nat, z => Nat.add(q0, z), C.high(10n, Nat.add(r0, 512n)), 1n, h1)
      +r1 = Equal.cong(Bool, Nat, t => Nat.add(q0, SF.b2n(Bool.or(t, Bool.and(Nat.is_eq(r0, 512n), Nat.is_eq(Nat.mod(q0, 2n), 1n))))), Nat.is_lt(512n, r0), True{}, hgt)
      Equal.trans(Nat, SF.pick(Nat, Nat.is_eq(r0, 512n), Nat.sub(Nat.add(q0, C.high(10n, Nat.add(r0, 512n))), Nat.mod(Nat.add(q0, C.high(10n, Nat.add(r0, 512n))), 2n)), Nat.add(q0, C.high(10n, Nat.add(r0, 512n)))), Nat.add(q0, C.high(10n, Nat.add(r0, 512n))), SF.rne_up(q0, r0, 512n), l1, Equal.trans(Nat, Nat.add(q0, C.high(10n, Nat.add(r0, 512n))), Nat.add(q0, 1n), SF.rne_up(q0, r0, 512n), l2, Equal.sym(Nat, SF.rne_up(q0, r0, 512n), Nat.add(q0, 1n), r1)))
    case EQ{}:
      +er = NC.eq_of_cmp(r0, 512n, hc)
      +b1 = subm(Nat.add(q0, 1n))
      +b2 = Equal.trans(Nat, Nat.add(q0, SF.b2n(Nat.is_eq(Nat.mod(q0, 2n), 1n))), Nat.add(q0, SF.b2n(Nat.is_eq(C.bit(q0), 1n))), Nat.double(C.half(Nat.add(q0, 1n))), Equal.cong(Nat, Nat, z => Nat.add(q0, SF.b2n(Nat.is_eq(z, 1n))), Nat.mod(q0, 2n), C.bit(q0), Equal.sym(Nat, C.bit(q0), Nat.mod(q0, 2n), WW.bit_mod(q0))), parq(q0))
      +base = Equal.trans(Nat, Nat.sub(Nat.add(q0, 1n), Nat.mod(Nat.add(q0, 1n), 2n)), Nat.double(C.half(Nat.add(q0, 1n))), Nat.add(q0, SF.b2n(Nat.is_eq(Nat.mod(q0, 2n), 1n))), b1, Equal.sym(Nat, Nat.add(q0, SF.b2n(Nat.is_eq(Nat.mod(q0, 2n), 1n))), Nat.double(C.half(Nat.add(q0, 1n))), b2))
      L.subst(Nat, z => {SF.pick(Nat, Nat.is_eq(z, 512n), Nat.sub(Nat.add(q0, C.high(10n, Nat.add(z, 512n))), Nat.mod(Nat.add(q0, C.high(10n, Nat.add(z, 512n))), 2n)), Nat.add(q0, C.high(10n, Nat.add(z, 512n)))) == SF.rne_up(q0, z, 512n) : Nat}, 512n, r0, Equal.sym(Nat, r0, 512n, er), base)

def bl_gt(+k: Nat, +n: Nat, +h1: {C.fits(k, n) == False{} : Bool}, +h2: {C.fits(1n+k, n) == True{} : Bool}, +hg: {Nat.is_le(C.pow2(2n+k), C.pow2(M.bit_length(n))) == True{} : Bool}) -> {M.bit_length(n) == 1n+k : Nat}:
  match n:
    case 0n:
      NC.absurd_tf({M.bit_length(0n) == 1n+k : Nat}, Equal.trans(Bool, False{}, C.fits(k, 0n), True{}, Equal.sym(Bool, C.fits(k, 0n), False{}, h1), fz(k)))
    case 1n+ +np:
      +P = C.pow2(2n+k)
      +hd = N.double_lt(1n+np, C.pow2(1n+k), WW.lt_of_fits(1n+k, 1n+np, h2))
      +hle = N.le_trans(P, C.pow2(M.bit_length(1n+np)), Nat.double(1n+np), hg, BT.bit_length_le(np))
      NC.absurd_tf({M.bit_length(1n+np) == 1n+k : Nat}, Equal.trans(Bool, False{}, Nat.is_lt(P, P), True{}, Equal.sym(Bool, Nat.is_lt(P, P), False{}, N.lt_irrefl(P)), N.le_lt_trans(P, Nat.double(1n+np), P, hle, hd)))

def bl_c(+k: Nat, +n: Nat, +h1: {C.fits(k, n) == False{} : Bool}, +h2: {C.fits(1n+k, n) == True{} : Bool}, +c: Cmp, +hc: {Nat.cmp(M.bit_length(n), 1n+k) == c : Cmp}) -> {M.bit_length(n) == 1n+k : Nat}:
  match c:
    case EQ{}:
      NC.eq_of_cmp(M.bit_length(n), 1n+k, hc)
    case LT{}:
      +hl = N.lt_succ_le(M.bit_length(n), k, NC.lt_of_cmp(M.bit_length(n), 1n+k, hc))
      +hn = N.lt_le_trans(n, C.pow2(M.bit_length(n)), C.pow2(k), BT.bit_length_lt(n), N.pow2_mono(M.bit_length(n), k, hl))
      NC.absurd_tf({M.bit_length(n) == 1n+k : Nat}, Equal.trans(Bool, False{}, C.fits(k, n), True{}, Equal.sym(Bool, C.fits(k, n), False{}, h1), WW.fits_of_lt(k, n, hn)))
    case GT{}:
      +hg = N.pow2_mono(2n+k, M.bit_length(n), N.lt_succ_le_succ(1n+k, M.bit_length(n), NC.lt_of_gt(M.bit_length(n), 1n+k, hc)))
      bl_gt(k, n, h1, h2, hg)

def fits_hc(+a: Nat, +b: Nat, +n: Nat) -> {C.fits(Nat.add(a, b), n) == C.fits(b, C.high(a, n)) : Bool}:
  Equal.cong(Nat, Bool, z => Nat.is_eq(z, 0n), C.high(Nat.add(a, b), n), C.high(b, C.high(a, n)), WW.high_comp(b, a, n))

def succ_le(+a: Nat, +b: Nat, +h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(Nat.add(a, 1n), b) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_le(z, b) == True{} : Bool}, 1n+a, Nat.add(a, 1n), Equal.sym(Nat, Nat.add(a, 1n), 1n+a, Equal.trans(Nat, Nat.add(a, 1n), Nat.add(1n, a), 1n+a, NA.add_comm(a, 1n), {==})), N.lt_succ_le_succ(a, b, h))

def nfit_c(+k: Nat, +a: Nat, +r: Nat, +hle: {Nat.is_le(a, r) == True{} : Bool}, +f: {C.fits(k, a) == False{} : Bool}, +b: Bool, +hb: {C.fits(k, r) == b : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      NC.absurd_tf({True{} == False{} : Bool}, Equal.trans(Bool, False{}, C.fits(k, a), True{}, Equal.sym(Bool, C.fits(k, a), False{}, f), SH.fits_lek(k, a, r, hle, hb)))
    case False{}:
      {==}

def nfit(+k: Nat, +a: Nat, +r: Nat, +hle: {Nat.is_le(a, r) == True{} : Bool}, +f: {C.fits(k, a) == False{} : Bool}) -> {C.fits(k, r) == False{} : Bool}:
  nfit_c(k, a, r, hle, f, C.fits(k, r), {==})

def lt_fit(+k: Nat, +one: Nat, +h1: {one == 1n : Nat}, +n: Nat) -> {Nat.is_lt(n, C.shift(k, one)) == C.fits(k, n) : Bool}:
  +e2a = Equal.trans(Bool, Nat.is_lt(n, C.shift(k, 1n)), Nat.is_lt(n, C.pow2(k)), C.fits(k, n), Equal.cong(Nat, Bool, z => Nat.is_lt(n, z), C.shift(k, 1n), C.pow2(k), WW.shift_one(k)), Equal.sym(Bool, C.fits(k, n), Nat.is_lt(n, C.pow2(k)), WW.fits_lt(k, n)))
  L.subst(Nat, o => {Nat.is_lt(n, C.shift(k, o)) == C.fits(k, n) : Bool}, 1n, one, Equal.sym(Nat, one, 1n, h1), e2a)

def efv(+u: Nat, +EF: Nat, +hu: {Nat.add(EF, 1926n) == u : Nat}) -> {Nat.sub(Nat.add(u, 1075n), SF.zb()) == 1n+EF : Nat}:
  +e1 = Equal.cong(Nat, Nat, z => Nat.sub(Nat.add(z, 1075n), SF.zb()), u, Nat.add(EF, 1926n), Equal.sym(Nat, Nat.add(EF, 1926n), u, hu))
  +e2 = Equal.cong(Nat, Nat, z => Nat.sub(z, SF.zb()), Nat.add(Nat.add(EF, 1926n), 1075n), Nat.add(EF, 3001n), NA.add_assoc(EF, 1926n, 1075n))
  +e3 = Equal.cong(Nat, Nat, z => Nat.sub(z, SF.zb()), Nat.add(EF, 3001n), Nat.add(3001n, EF), NA.add_comm(EF, 3001n))
  Equal.trans(Nat, Nat.sub(Nat.add(u, 1075n), SF.zb()), Nat.sub(Nat.add(Nat.add(EF, 1926n), 1075n), SF.zb()), 1n+EF, e1, Equal.trans(Nat, Nat.sub(Nat.add(Nat.add(EF, 1926n), 1075n), SF.zb()), Nat.sub(Nat.add(EF, 3001n), SF.zb()), 1n+EF, e2, e3))

def ef2v(+u: Nat, +EF: Nat, +hu: {Nat.add(EF, 1926n) == u : Nat}) -> {Nat.sub(Nat.add(1n+u, 1075n), SF.zb()) == 2n+EF : Nat}:
  +e1 = Equal.cong(Nat, Nat, z => Nat.sub(Nat.add(1n+z, 1075n), SF.zb()), u, Nat.add(EF, 1926n), Equal.sym(Nat, Nat.add(EF, 1926n), u, hu))
  +e2 = Equal.cong(Nat, Nat, z => Nat.sub(z, SF.zb()), Nat.add(Nat.add(1n+EF, 1926n), 1075n), Nat.add(1n+EF, 3001n), NA.add_assoc(1n+EF, 1926n, 1075n))
  +e3 = Equal.cong(Nat, Nat, z => Nat.sub(z, SF.zb()), Nat.add(1n+EF, 3001n), Nat.add(3001n, 1n+EF), NA.add_comm(1n+EF, 3001n))
  Equal.trans(Nat, Nat.sub(Nat.add(1n+u, 1075n), SF.zb()), Nat.sub(Nat.add(Nat.add(1n+EF, 1926n), 1075n), SF.zb()), 2n+EF, e1, Equal.trans(Nat, Nat.sub(Nat.add(Nat.add(1n+EF, 1926n), 1075n), SF.zb()), Nat.sub(Nat.add(1n+EF, 3001n), SF.zb()), 2n+EF, e2, e3))

def hi_one(+H0: Nat, +a: {Nat.is_eq(C.half(H0), 0n) == True{} : Bool}, +b: {Nat.is_eq(H0, 0n) == False{} : Bool}) -> {H0 == 1n : Nat}:
  match H0:
    case 0n:
      Empty.absurd({0n == 1n : Nat}, LW.true_ne_false(b))
    case 1n:
      {==}
    case 2n+ +p:
      NC.absurd_tf({2n+p == 1n : Nat}, a)

def f53h(+q: Nat) -> {C.fits(53n, q) == Nat.is_eq(C.half(C.high(52n, q)), 0n) : Bool}:
  fits_hc(52n, 1n, q)

def top_q(+one: Nat, +h1: {one == 1n : Nat}, +q: Nat, +hq: {Nat.is_le(q, C.shift(53n, one)) == True{} : Bool}, +hf: {C.fits(53n, q) == False{} : Bool}) -> {q == C.shift(52n, Nat.double(one)) : Nat}:
  +hlt = Equal.trans(Bool, Nat.is_lt(q, C.shift(53n, one)), C.fits(53n, q), False{}, lt_fit(53n, one, h1, q), hf)
  +hge = N.not_lt_le(q, C.shift(53n, one), hlt)
  Equal.trans(Nat, q, C.shift(53n, one), C.shift(52n, Nat.double(one)), N.le_antisym(q, C.shift(53n, one), hq, hge), Equal.sym(Nat, C.shift(52n, Nat.double(one)), C.shift(53n, one), WW.shift_dbl(52n, one)))

def pkg_c(+one: Nat, +h1: {one == 1n : Nat}, +s: Bool, +q: Nat, +u: Nat, +EF: Nat, +hEF: {Nat.add(EF, 1926n) == u : Nat}, +hq: {Nat.is_le(q, C.shift(53n, one)) == True{} : Bool}, +f53: Bool, +h53: {C.fits(53n, q) == f53 : Bool}, +f52: Bool, +h52: {C.fits(52n, q) == f52 : Bool}, +h0: {Bool.or(Bool.not(f52), Nat.is_eq(EF, 0n)) == True{} : Bool}, +hov: {Nat.is_lt(Nat.add(EF, SF.pick(Nat, f53, 1n, 2n)), 2047n) == True{} : Bool}) -> {SF.pick(F.F64, f53, SF.pick(F.F64, f52, SF.encode(s, 0n, q), SF.pack_e(s, Nat.sub(Nat.add(u, 1075n), SF.zb()), C.low(52n, q))), SF.pack_e(s, Nat.sub(Nat.add(1n+u, 1075n), SF.zb()), 0n)) == bits(s, Nat.add(q, C.shift(52n, EF))) : F.F64}:
  match f53 f52:
    case True{} True{}:
      +e0 = N.eq_from_is_eq(EF, 0n, h0)
      Equal.trans(F.F64, SF.encode(s, 0n, q), bits(s, Nat.add(q, C.shift(52n, 0n))), bits(s, Nat.add(q, C.shift(52n, EF))), enc_bits(s, 0n, q), Equal.cong(Nat, F.F64, z => bits(s, Nat.add(q, C.shift(52n, z))), 0n, EF, Equal.sym(Nat, EF, 0n, e0)))
    case True{} False{}:
      +eH = hi_one(C.high(52n, q), Equal.trans(Bool, Nat.is_eq(C.half(C.high(52n, q)), 0n), C.fits(53n, q), True{}, Equal.sym(Bool, C.fits(53n, q), Nat.is_eq(C.half(C.high(52n, q)), 0n), f53h(q)), h53), h52)
      +e1 = efv(u, EF, hEF)
      +eE = Equal.trans(Nat, Nat.sub(Nat.add(u, 1075n), SF.zb()), 1n+EF, Nat.add(C.high(52n, q), EF), e1, Equal.cong(Nat, Nat, z => Nat.add(z, EF), 1n, C.high(52n, q), Equal.sym(Nat, C.high(52n, q), 1n, eH)))
      +hle = Equal.trans(Bool, Nat.is_le(2047n, Nat.sub(Nat.add(u, 1075n), SF.zb())), Nat.is_le(2047n, 1n+EF), False{}, Equal.cong(Nat, Bool, z => Nat.is_le(2047n, z), Nat.sub(Nat.add(u, 1075n), SF.zb()), 1n+EF, e1), Equal.trans(Bool, Nat.is_le(2047n, 1n+EF), Bool.not(Nat.is_lt(1n+EF, 2047n)), False{}, FB.le_nlt(2047n, 1n+EF), Equal.cong(Bool, Bool, t => Bool.not(t), Nat.is_lt(1n+EF, 2047n), True{}, L.subst(Nat, z => {Nat.is_lt(z, 2047n) == True{} : Bool}, Nat.add(EF, 1n), 1n+EF, Equal.trans(Nat, Nat.add(EF, 1n), Nat.add(1n, EF), 1n+EF, NA.add_comm(EF, 1n), {==}), hov))))
      +p1 = Equal.cong(Bool, F.F64, t => SF.pick(F.F64, t, SF.inf(s), SF.encode(s, Nat.sub(Nat.add(u, 1075n), SF.zb()), C.low(52n, q))), Nat.is_le(2047n, Nat.sub(Nat.add(u, 1075n), SF.zb())), False{}, hle)
      +p2 = enc_bits(s, Nat.sub(Nat.add(u, 1075n), SF.zb()), C.low(52n, q))
      +v1 = Equal.trans(Nat, Nat.add(C.low(52n, q), C.shift(52n, Nat.sub(Nat.add(u, 1075n), SF.zb()))), Nat.add(C.low(52n, q), C.shift(52n, Nat.add(C.high(52n, q), EF))), Nat.add(q, C.shift(52n, EF)), Equal.cong(Nat, Nat, z => Nat.add(C.low(52n, q), C.shift(52n, z)), Nat.sub(Nat.add(u, 1075n), SF.zb()), Nat.add(C.high(52n, q), EF), eE), Equal.trans(Nat, Nat.add(C.low(52n, q), C.shift(52n, Nat.add(C.high(52n, q), EF))), Nat.add(C.low(52n, q), Nat.add(C.shift(52n, C.high(52n, q)), C.shift(52n, EF))), Nat.add(q, C.shift(52n, EF)), Equal.cong(Nat, Nat, z => Nat.add(C.low(52n, q), z), C.shift(52n, Nat.add(C.high(52n, q), EF)), Nat.add(C.shift(52n, C.high(52n, q)), C.shift(52n, EF)), WW.shift_add(52n, C.high(52n, q), EF)), Equal.trans(Nat, Nat.add(C.low(52n, q), Nat.add(C.shift(52n, C.high(52n, q)), C.shift(52n, EF))), Nat.add(Nat.add(C.low(52n, q), C.shift(52n, C.high(52n, q))), C.shift(52n, EF)), Nat.add(q, C.shift(52n, EF)), Equal.sym(Nat, Nat.add(Nat.add(C.low(52n, q), C.shift(52n, C.high(52n, q))), C.shift(52n, EF)), Nat.add(C.low(52n, q), Nat.add(C.shift(52n, C.high(52n, q)), C.shift(52n, EF))), NA.add_assoc(C.low(52n, q), C.shift(52n, C.high(52n, q)), C.shift(52n, EF))), Equal.cong(Nat, Nat, z => Nat.add(z, C.shift(52n, EF)), Nat.add(C.low(52n, q), C.shift(52n, C.high(52n, q))), q, Equal.sym(Nat, q, Nat.add(C.low(52n, q), C.shift(52n, C.high(52n, q))), WW.low_high(52n, q))))))
      +p3 = Equal.cong(Nat, F.F64, z => bits(s, z), Nat.add(C.low(52n, q), C.shift(52n, Nat.sub(Nat.add(u, 1075n), SF.zb()))), Nat.add(q, C.shift(52n, EF)), v1)
      Equal.trans(F.F64, SF.pack_e(s, Nat.sub(Nat.add(u, 1075n), SF.zb()), C.low(52n, q)), SF.encode(s, Nat.sub(Nat.add(u, 1075n), SF.zb()), C.low(52n, q)), bits(s, Nat.add(q, C.shift(52n, EF))), p1, Equal.trans(F.F64, SF.encode(s, Nat.sub(Nat.add(u, 1075n), SF.zb()), C.low(52n, q)), bits(s, Nat.add(C.low(52n, q), C.shift(52n, Nat.sub(Nat.add(u, 1075n), SF.zb())))), bits(s, Nat.add(q, C.shift(52n, EF))), p2, p3))
    case False{} _:
      +e1 = ef2v(u, EF, hEF)
      +eq = top_q(one, h1, q, hq, h53)
      +two = Nat.double(one)
      +eE = Equal.trans(Nat, Nat.sub(Nat.add(1n+u, 1075n), SF.zb()), 2n+EF, Nat.add(two, EF), e1, Equal.cong(Nat, Nat, z => Nat.add(Nat.double(z), EF), 1n, one, Equal.sym(Nat, one, 1n, h1)))
      +hle = Equal.trans(Bool, Nat.is_le(2047n, Nat.sub(Nat.add(1n+u, 1075n), SF.zb())), Nat.is_le(2047n, 2n+EF), False{}, Equal.cong(Nat, Bool, z => Nat.is_le(2047n, z), Nat.sub(Nat.add(1n+u, 1075n), SF.zb()), 2n+EF, e1), Equal.trans(Bool, Nat.is_le(2047n, 2n+EF), Bool.not(Nat.is_lt(2n+EF, 2047n)), False{}, FB.le_nlt(2047n, 2n+EF), Equal.cong(Bool, Bool, t => Bool.not(t), Nat.is_lt(2n+EF, 2047n), True{}, L.subst(Nat, z => {Nat.is_lt(z, 2047n) == True{} : Bool}, Nat.add(EF, 2n), 2n+EF, Equal.trans(Nat, Nat.add(EF, 2n), Nat.add(2n, EF), 2n+EF, NA.add_comm(EF, 2n), {==}), hov))))
      +p1 = Equal.cong(Bool, F.F64, t => SF.pick(F.F64, t, SF.inf(s), SF.encode(s, Nat.sub(Nat.add(1n+u, 1075n), SF.zb()), 0n)), Nat.is_le(2047n, Nat.sub(Nat.add(1n+u, 1075n), SF.zb())), False{}, hle)
      +p2 = enc_bits(s, Nat.sub(Nat.add(1n+u, 1075n), SF.zb()), 0n)
      +v1 = Equal.trans(Nat, C.shift(52n, Nat.sub(Nat.add(1n+u, 1075n), SF.zb())), C.shift(52n, Nat.add(two, EF)), Nat.add(q, C.shift(52n, EF)), Equal.cong(Nat, Nat, z => C.shift(52n, z), Nat.sub(Nat.add(1n+u, 1075n), SF.zb()), Nat.add(two, EF), eE), Equal.trans(Nat, C.shift(52n, Nat.add(two, EF)), Nat.add(C.shift(52n, two), C.shift(52n, EF)), Nat.add(q, C.shift(52n, EF)), WW.shift_add(52n, two, EF), Equal.cong(Nat, Nat, z => Nat.add(z, C.shift(52n, EF)), C.shift(52n, two), q, Equal.sym(Nat, q, C.shift(52n, two), eq))))
      +p3 = Equal.cong(Nat, F.F64, z => bits(s, z), C.shift(52n, Nat.sub(Nat.add(1n+u, 1075n), SF.zb())), Nat.add(q, C.shift(52n, EF)), v1)
      Equal.trans(F.F64, SF.pack_e(s, Nat.sub(Nat.add(1n+u, 1075n), SF.zb()), 0n), SF.encode(s, Nat.sub(Nat.add(1n+u, 1075n), SF.zb()), 0n), bits(s, Nat.add(q, C.shift(52n, EF))), p1, Equal.trans(F.F64, SF.encode(s, Nat.sub(Nat.add(1n+u, 1075n), SF.zb()), 0n), bits(s, Nat.add(0n, C.shift(52n, Nat.sub(Nat.add(1n+u, 1075n), SF.zb())))), bits(s, Nat.add(q, C.shift(52n, EF))), p2, p3))

def pkg(+one: Nat, +h1: {one == 1n : Nat}, +s: Bool, +q: Nat, +u: Nat, +EF: Nat, +hEF: {Nat.add(EF, 1926n) == u : Nat}, +hq: {Nat.is_le(q, C.shift(53n, one)) == True{} : Bool}, +h0: {Bool.or(Bool.not(C.fits(52n, q)), Nat.is_eq(EF, 0n)) == True{} : Bool}, +hov: {Nat.is_lt(Nat.add(EF, SF.pick(Nat, C.fits(53n, q), 1n, 2n)), 2047n) == True{} : Bool}) -> {SF.pack(s, q, u) == bits(s, Nat.add(q, C.shift(52n, EF))) : F.F64}:
  pkg_c(one, h1, s, q, u, EF, hEF, hq, C.fits(53n, q), {==}, C.fits(52n, q), {==}, h0, hov)

def hsp(+m: Nat) -> {C.high(10n, Nat.add(m, 512n)) == Nat.add(C.high(10n, m), C.high(10n, Nat.add(C.low(10n, m), 512n))) : Nat}:
  Equal.trans(Nat, C.high(10n, Nat.add(m, 512n)), C.high(10n, Nat.add(Nat.add(C.low(10n, m), C.shift(10n, C.high(10n, m))), 512n)), Nat.add(C.high(10n, m), C.high(10n, Nat.add(C.low(10n, m), 512n))), Equal.cong(Nat, Nat, z => C.high(10n, Nat.add(z, 512n)), m, Nat.add(C.low(10n, m), C.shift(10n, C.high(10n, m))), WW.low_high(10n, m)), Equal.trans(Nat, C.high(10n, Nat.add(Nat.add(C.low(10n, m), C.shift(10n, C.high(10n, m))), 512n)), C.high(10n, Nat.add(Nat.add(C.low(10n, m), 512n), C.shift(10n, C.high(10n, m)))), Nat.add(C.high(10n, m), C.high(10n, Nat.add(C.low(10n, m), 512n))), Equal.cong(Nat, Nat, z => C.high(10n, z), Nat.add(Nat.add(C.low(10n, m), C.shift(10n, C.high(10n, m))), 512n), Nat.add(Nat.add(C.low(10n, m), 512n), C.shift(10n, C.high(10n, m))), A.add_rot(C.low(10n, m), C.shift(10n, C.high(10n, m)), 512n)), Equal.trans(Nat, C.high(10n, Nat.add(Nat.add(C.low(10n, m), 512n), C.shift(10n, C.high(10n, m)))), Nat.add(C.high(10n, Nat.add(C.low(10n, m), 512n)), C.high(10n, m)), Nat.add(C.high(10n, m), C.high(10n, Nat.add(C.low(10n, m), 512n))), WW.high_add_shift(10n, Nat.add(C.low(10n, m), 512n), C.high(10n, m)), NA.add_comm(C.high(10n, Nat.add(C.low(10n, m), 512n)), C.high(10n, m)))))

def mod_sh(+k: Nat, +x: Nat) -> {Nat.mod(C.shift(1n+k, x), 2n) == 0n : Nat}:
  WW.odd_limb(k, 0n, x)

def fsub_c(+k: Nat, +one: Nat, +h1: {one == 1n : Nat}, +R0: Nat, +hR: {Nat.is_le(R0, C.shift(1n+k, one)) == True{} : Bool}, +f: Bool, +hf: {C.fits(1n+k, R0) == f : Bool}) -> {C.fits(1n+k, Nat.sub(R0, Nat.mod(R0, 2n))) == f : Bool}:
  match f:
    case True{}:
      SH.fits_lek(1n+k, Nat.sub(R0, Nat.mod(R0, 2n)), R0, UH.sub_le(R0, Nat.mod(R0, 2n)), hf)
    case False{}:
      +hlt = Equal.trans(Bool, Nat.is_lt(R0, C.shift(1n+k, one)), C.fits(1n+k, R0), False{}, lt_fit(1n+k, one, h1, R0), hf)
      +eR = N.le_antisym(R0, C.shift(1n+k, one), hR, N.not_lt_le(R0, C.shift(1n+k, one), hlt))
      +em = Equal.trans(Nat, Nat.mod(R0, 2n), Nat.mod(C.shift(1n+k, one), 2n), 0n, Equal.cong(Nat, Nat, z => Nat.mod(z, 2n), R0, C.shift(1n+k, one), eR), mod_sh(k, one))
      +es = Equal.trans(Nat, Nat.sub(R0, Nat.mod(R0, 2n)), Nat.sub(R0, 0n), R0, Equal.cong(Nat, Nat, z => Nat.sub(R0, z), Nat.mod(R0, 2n), 0n, em), N.sub_zero(R0))
      Equal.trans(Bool, C.fits(1n+k, Nat.sub(R0, Nat.mod(R0, 2n))), C.fits(1n+k, R0), False{}, Equal.cong(Nat, Bool, z => C.fits(1n+k, z), Nat.sub(R0, Nat.mod(R0, 2n)), R0, es), hf)

def fpk(+one: Nat, +h1: {one == 1n : Nat}, +R0: Nat, +hR: {Nat.is_le(R0, C.shift(53n, one)) == True{} : Bool}, +t: Bool) -> {C.fits(53n, SF.pick(Nat, t, Nat.sub(R0, Nat.mod(R0, 2n)), R0)) == C.fits(53n, R0) : Bool}:
  match t:
    case True{}:
      fsub_c(52n, one, h1, R0, hR, C.fits(53n, R0), {==})
    case False{}:
      {==}

def le1(+t: Nat, +h: {C.fits(1n, t) == True{} : Bool}) -> {Nat.is_le(t, 1n) == True{} : Bool}:
  match t:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n+ +p:
      NC.absurd_tf({Nat.is_le(2n+p, 1n) == True{} : Bool}, h)

def R_le(+one: Nat, +h1: {one == 1n : Nat}, +m: Nat, +hm: {C.fits(63n, m) == True{} : Bool}) -> {Nat.is_le(Nat.add(C.high(10n, m), C.high(10n, Nat.add(C.low(10n, m), 512n))), C.shift(53n, one)) == True{} : Bool}:
  +t = C.high(10n, Nat.add(C.low(10n, m), 512n))
  +ht = le1(t, SH.fits_high(10n, 1n, Nat.add(C.low(10n, m), 512n), fits_add1(10n, C.low(10n, m), 512n, WW.low_fits(10n, m), {==})))
  +hq = WW.lt_one(53n, one, h1, C.high(10n, m), SH.fits_high(10n, 53n, m, hm))
  N.le_trans(Nat.add(C.high(10n, m), C.high(10n, Nat.add(C.low(10n, m), 512n))), Nat.add(C.high(10n, m), 1n), C.shift(53n, one), N.le_add_left(t, 1n, C.high(10n, m), ht), succ_le(C.high(10n, m), C.shift(53n, one), hq))

def p2(+one: Nat, +h1: {one == 1n : Nat}, +m: Nat, +hm: {C.fits(63n, m) == True{} : Bool}) -> {C.fits(53n, SF.rne(m, 10n)) == C.fits(63n, Nat.add(m, 512n)) : Bool}:
  +e1 = Equal.cong(Nat, Bool, z => C.fits(53n, z), SF.rne(m, 10n), SF.pick(Nat, Nat.is_eq(C.low(10n, m), 512n), Nat.sub(Nat.add(C.high(10n, m), C.high(10n, Nat.add(C.low(10n, m), 512n))), Nat.mod(Nat.add(C.high(10n, m), C.high(10n, Nat.add(C.low(10n, m), 512n))), 2n)), Nat.add(C.high(10n, m), C.high(10n, Nat.add(C.low(10n, m), 512n)))), Equal.sym(Nat, SF.pick(Nat, Nat.is_eq(C.low(10n, m), 512n), Nat.sub(Nat.add(C.high(10n, m), C.high(10n, Nat.add(C.low(10n, m), 512n))), Nat.mod(Nat.add(C.high(10n, m), C.high(10n, Nat.add(C.low(10n, m), 512n))), 2n)), Nat.add(C.high(10n, m), C.high(10n, Nat.add(C.low(10n, m), 512n)))), SF.rne(m, 10n), rp_c(C.high(10n, m), C.low(10n, m), WW.low_fits(10n, m), Nat.cmp(C.low(10n, m), 512n), {==})))
  +e2 = fpk(one, h1, Nat.add(C.high(10n, m), C.high(10n, Nat.add(C.low(10n, m), 512n))), R_le(one, h1, m, hm), Nat.is_eq(C.low(10n, m), 512n))
  +e3 = Equal.cong(Nat, Bool, z => C.fits(53n, z), Nat.add(C.high(10n, m), C.high(10n, Nat.add(C.low(10n, m), 512n))), C.high(10n, Nat.add(m, 512n)), Equal.sym(Nat, C.high(10n, Nat.add(m, 512n)), Nat.add(C.high(10n, m), C.high(10n, Nat.add(C.low(10n, m), 512n))), hsp(m)))
  +e4 = Equal.sym(Bool, C.fits(63n, Nat.add(m, 512n)), C.fits(53n, C.high(10n, Nat.add(m, 512n))), fits_hc(10n, 53n, Nat.add(m, 512n)))
  Equal.trans(Bool, C.fits(53n, SF.rne(m, 10n)), C.fits(53n, SF.pick(Nat, Nat.is_eq(C.low(10n, m), 512n), Nat.sub(Nat.add(C.high(10n, m), C.high(10n, Nat.add(C.low(10n, m), 512n))), Nat.mod(Nat.add(C.high(10n, m), C.high(10n, Nat.add(C.low(10n, m), 512n))), 2n)), Nat.add(C.high(10n, m), C.high(10n, Nat.add(C.low(10n, m), 512n))))), C.fits(63n, Nat.add(m, 512n)), e1, Equal.trans(Bool, C.fits(53n, SF.pick(Nat, Nat.is_eq(C.low(10n, m), 512n), Nat.sub(Nat.add(C.high(10n, m), C.high(10n, Nat.add(C.low(10n, m), 512n))), Nat.mod(Nat.add(C.high(10n, m), C.high(10n, Nat.add(C.low(10n, m), 512n))), 2n)), Nat.add(C.high(10n, m), C.high(10n, Nat.add(C.low(10n, m), 512n))))), C.fits(53n, Nat.add(C.high(10n, m), C.high(10n, Nat.add(C.low(10n, m), 512n)))), C.fits(63n, Nat.add(m, 512n)), e2, Equal.trans(Bool, C.fits(53n, Nat.add(C.high(10n, m), C.high(10n, Nat.add(C.low(10n, m), 512n)))), C.fits(53n, C.high(10n, Nat.add(m, 512n))), C.fits(63n, Nat.add(m, 512n)), e3, e4)))

def sub_cancel_r(+a: Nat, +b: Nat, +c: Nat) -> {Nat.sub(Nat.add(a, c), Nat.add(b, c)) == Nat.sub(a, b) : Nat}:
  match c:
    case 0n:
      Equal.trans(Nat, Nat.sub(Nat.add(a, 0n), Nat.add(b, 0n)), Nat.sub(a, Nat.add(b, 0n)), Nat.sub(a, b), Equal.cong(Nat, Nat, z => Nat.sub(z, Nat.add(b, 0n)), Nat.add(a, 0n), a, N.add_zero(a)), Equal.cong(Nat, Nat, z => Nat.sub(a, z), Nat.add(b, 0n), b, N.add_zero(b)))
    case 1n+ +cp:
      Equal.trans(Nat, Nat.sub(Nat.add(a, 1n+cp), Nat.add(b, 1n+cp)), Nat.sub(1n+Nat.add(a, cp), Nat.add(b, 1n+cp)), Nat.sub(a, b), Equal.cong(Nat, Nat, z => Nat.sub(z, Nat.add(b, 1n+cp)), Nat.add(a, 1n+cp), 1n+Nat.add(a, cp), N.add_succ(a, cp)), Equal.trans(Nat, Nat.sub(1n+Nat.add(a, cp), Nat.add(b, 1n+cp)), Nat.sub(1n+Nat.add(a, cp), 1n+Nat.add(b, cp)), Nat.sub(a, b), Equal.cong(Nat, Nat, z => Nat.sub(1n+Nat.add(a, cp), z), Nat.add(b, 1n+cp), 1n+Nat.add(b, cp), N.add_succ(b, cp)), sub_cancel_r(a, b, cp)))

def lt0f(+h: Nat) -> {Nat.is_lt(h, 0n) == False{} : Bool}:
  N.not_lt_zero(h)

def rne_exact(+k: Nat, +m: Nat) -> {SF.rne(C.shift(k, m), k) == m : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+ +i:
      +S = C.shift(1n+i, m)
      +h = C.shift(i, 1n)
      +eq = WW.high_u(1n+i, 0n, m, fz(1n+i))
      +el = WW.low_u(1n+i, 0n, m, fz(1n+i))
      +e1 = Equal.cong(Nat, Nat, z => SF.rne_up(z, C.low(1n+i, S), h), C.high(1n+i, S), m, eq)
      +e2 = Equal.cong(Nat, Nat, z => SF.rne_up(m, z, h), C.low(1n+i, S), 0n, el)
      +hz = N.is_eq_sym_false(h, 0n, Equal.trans(Bool, Nat.is_eq(h, 0n), Nat.is_eq(1n, 0n), False{}, WW.shift_eq0(i, 1n), {==}))
      +e3 = Equal.cong(Bool, Nat, t => Nat.add(m, SF.b2n(Bool.or(t, Bool.and(Nat.is_eq(0n, h), Nat.is_eq(Nat.mod(m, 2n), 1n))))), Nat.is_lt(h, 0n), False{}, lt0f(h))
      +e4 = Equal.cong(Bool, Nat, t => Nat.add(m, SF.b2n(Bool.or(False{}, Bool.and(t, Nat.is_eq(Nat.mod(m, 2n), 1n))))), Nat.is_eq(0n, h), False{}, hz)
      +e5 = N.add_zero(m)
      Equal.trans(Nat, SF.rne_up(C.high(1n+i, S), C.low(1n+i, S), h), SF.rne_up(m, C.low(1n+i, S), h), m, e1, Equal.trans(Nat, SF.rne_up(m, C.low(1n+i, S), h), SF.rne_up(m, 0n, h), m, e2, Equal.trans(Nat, SF.rne_up(m, 0n, h), Nat.add(m, SF.b2n(Bool.or(False{}, Bool.and(Nat.is_eq(0n, h), Nat.is_eq(Nat.mod(m, 2n), 1n))))), m, e3, Equal.trans(Nat, Nat.add(m, SF.b2n(Bool.or(False{}, Bool.and(Nat.is_eq(0n, h), Nat.is_eq(Nat.mod(m, 2n), 1n))))), Nat.add(m, 0n), m, e4, e5))))

def rne_shift(+k: Nat, +m: Nat, +j: Nat) -> {SF.rne(C.shift(k, m), Nat.add(j, k)) == SF.rne(m, j) : Nat}:
  match j:
    case 0n:
      rne_exact(k, m)
    case 1n+ +i:
      +a = Nat.add(1n+i, k)
      +ea = NA.add_comm(1n+i, k)
      +hq = Equal.trans(Nat, C.high(a, C.shift(k, m)), C.high(Nat.add(k, 1n+i), C.shift(k, m)), C.high(1n+i, m), Equal.cong(Nat, Nat, z => C.high(z, C.shift(k, m)), a, Nat.add(k, 1n+i), ea), Equal.trans(Nat, C.high(Nat.add(k, 1n+i), C.shift(k, m)), C.high(1n+i, C.high(k, C.shift(k, m))), C.high(1n+i, m), WW.high_comp(1n+i, k, C.shift(k, m)), Equal.cong(Nat, Nat, z => C.high(1n+i, z), C.high(k, C.shift(k, m)), m, WW.high_u(k, 0n, m, fz(k)))))
      +hl = Equal.trans(Nat, C.low(a, C.shift(k, m)), C.low(Nat.add(k, 1n+i), C.shift(k, m)), C.shift(k, C.low(1n+i, m)), Equal.cong(Nat, Nat, z => C.low(z, C.shift(k, m)), a, Nat.add(k, 1n+i), ea), WW.low_shift(k, 1n+i, m))
      +hh = Equal.trans(Nat, C.shift(Nat.add(i, k), 1n), C.shift(Nat.add(k, i), 1n), C.shift(k, C.shift(i, 1n)), Equal.cong(Nat, Nat, z => C.shift(z, 1n), Nat.add(i, k), Nat.add(k, i), NA.add_comm(i, k)), WW.shift_comp(k, i, 1n))
      +hc = Equal.trans(Cmp, Nat.cmp(C.low(a, C.shift(k, m)), C.shift(Nat.add(i, k), 1n)), Nat.cmp(C.shift(k, C.low(1n+i, m)), C.shift(Nat.add(i, k), 1n)), Nat.cmp(C.low(1n+i, m), C.shift(i, 1n)), Equal.cong(Nat, Cmp, z => Nat.cmp(z, C.shift(Nat.add(i, k), 1n)), C.low(a, C.shift(k, m)), C.shift(k, C.low(1n+i, m)), hl), Equal.trans(Cmp, Nat.cmp(C.shift(k, C.low(1n+i, m)), C.shift(Nat.add(i, k), 1n)), Nat.cmp(C.shift(k, C.low(1n+i, m)), C.shift(k, C.shift(i, 1n))), Nat.cmp(C.low(1n+i, m), C.shift(i, 1n)), Equal.cong(Nat, Cmp, z => Nat.cmp(C.shift(k, C.low(1n+i, m)), z), C.shift(Nat.add(i, k), 1n), C.shift(k, C.shift(i, 1n)), hh), NC.cmp_shift(k, C.low(1n+i, m), C.shift(i, 1n))))
      +l1 = rne_cmp(C.high(a, C.shift(k, m)), C.low(a, C.shift(k, m)), C.shift(Nat.add(i, k), 1n))
      +l2 = Equal.cong(Nat, Nat, z => rne_c(z, Nat.cmp(C.low(a, C.shift(k, m)), C.shift(Nat.add(i, k), 1n))), C.high(a, C.shift(k, m)), C.high(1n+i, m), hq)
      +l3 = Equal.cong(Cmp, Nat, t => rne_c(C.high(1n+i, m), t), Nat.cmp(C.low(a, C.shift(k, m)), C.shift(Nat.add(i, k), 1n)), Nat.cmp(C.low(1n+i, m), C.shift(i, 1n)), hc)
      +r1 = rne_cmp(C.high(1n+i, m), C.low(1n+i, m), C.shift(i, 1n))
      Equal.trans(Nat, SF.rne_up(C.high(a, C.shift(k, m)), C.low(a, C.shift(k, m)), C.shift(Nat.add(i, k), 1n)), rne_c(C.high(1n+i, m), Nat.cmp(C.low(1n+i, m), C.shift(i, 1n))), SF.rne_up(C.high(1n+i, m), C.low(1n+i, m), C.shift(i, 1n)), Equal.trans(Nat, SF.rne_up(C.high(a, C.shift(k, m)), C.low(a, C.shift(k, m)), C.shift(Nat.add(i, k), 1n)), rne_c(C.high(a, C.shift(k, m)), Nat.cmp(C.low(a, C.shift(k, m)), C.shift(Nat.add(i, k), 1n))), rne_c(C.high(1n+i, m), Nat.cmp(C.low(1n+i, m), C.shift(i, 1n))), l1, Equal.trans(Nat, rne_c(C.high(a, C.shift(k, m)), Nat.cmp(C.low(a, C.shift(k, m)), C.shift(Nat.add(i, k), 1n))), rne_c(C.high(1n+i, m), Nat.cmp(C.low(a, C.shift(k, m)), C.shift(Nat.add(i, k), 1n))), rne_c(C.high(1n+i, m), Nat.cmp(C.low(1n+i, m), C.shift(i, 1n))), l2, l3)), Equal.sym(Nat, SF.rne_up(C.high(1n+i, m), C.low(1n+i, m), C.shift(i, 1n)), rne_c(C.high(1n+i, m), Nat.cmp(C.low(1n+i, m), C.shift(i, 1n))), r1))

def bl_fit(+n: Nat) -> {C.fits(M.bit_length(n), n) == True{} : Bool}:
  WW.fits_of_lt(M.bit_length(n), n, BT.bit_length_lt(n))

def bl_nfit(+n: Nat, +hz: {Nat.is_eq(n, 0n) == False{} : Bool}) -> {C.fits(Nat.sub(M.bit_length(n), 1n), n) == False{} : Bool}:
  +K = Nat.sub(M.bit_length(n), 1n)
  +nf = Equal.trans(Bool, C.fits(K, C.pow2(K)), Nat.is_lt(C.pow2(K), C.pow2(K)), False{}, WW.fits_lt(K, C.pow2(K)), N.lt_irrefl(C.pow2(K)))
  nfit(K, C.pow2(K), n, FO.lower(n, hz), nf)

def fits_sh(+k: Nat, +a: Nat, +m: Nat) -> {C.fits(Nat.add(k, a), C.shift(k, m)) == C.fits(a, m) : Bool}:
  Equal.cong(Nat, Bool, z => Nat.is_eq(z, 0n), C.high(Nat.add(k, a), C.shift(k, m)), C.high(a, m), Equal.trans(Nat, C.high(Nat.add(k, a), C.shift(k, m)), C.high(a, C.high(k, C.shift(k, m))), C.high(a, m), WW.high_comp(a, k, C.shift(k, m)), Equal.cong(Nat, Nat, z => C.high(a, z), C.high(k, C.shift(k, m)), m, WW.high_u(k, 0n, m, fz(k)))))

def bl_shift(+k: Nat, +m: Nat, +hz: {Nat.is_eq(m, 0n) == False{} : Bool}) -> {M.bit_length(C.shift(k, m)) == Nat.add(M.bit_length(m), k) : Nat}:
  +B = M.bit_length(m)
  +j = Nat.sub(B, 1n)
  +ej = N.sub_add(B, 1n, FO.bl_pos(m, hz, B, {==}))
  +nf = Equal.trans(Bool, C.fits(Nat.add(k, j), C.shift(k, m)), C.fits(j, m), False{}, fits_sh(k, j, m), bl_nfit(m, hz))
  +f0 = L.subst(Nat, z => {C.fits(z, m) == True{} : Bool}, B, 1n+j, Equal.sym(Nat, 1n+j, B, ej), bl_fit(m))
  +f1 = Equal.trans(Bool, C.fits(Nat.add(k, 1n+j), C.shift(k, m)), C.fits(1n+j, m), True{}, fits_sh(k, 1n+j, m), f0)
  +f2 = L.subst(Nat, z => {C.fits(z, C.shift(k, m)) == True{} : Bool}, Nat.add(k, 1n+j), 1n+Nat.add(k, j), N.add_succ(k, j), f1)
  +eb = bl_c(Nat.add(k, j), C.shift(k, m), nf, f2, Nat.cmp(M.bit_length(C.shift(k, m)), 1n+Nat.add(k, j)), {==})
  +er = Equal.trans(Nat, Nat.add(B, k), Nat.add(1n+j, k), 1n+Nat.add(k, j), Equal.cong(Nat, Nat, z => Nat.add(z, k), B, 1n+j, Equal.sym(Nat, 1n+j, B, ej)), Equal.cong(Nat, Nat, z => 1n+z, Nat.add(j, k), Nat.add(k, j), NA.add_comm(j, k)))
  Equal.trans(Nat, M.bit_length(C.shift(k, m)), 1n+Nat.add(k, j), Nat.add(B, k), eb, Equal.sym(Nat, Nat.add(B, k), 1n+Nat.add(k, j), er))

def a1(+x: Nat, +k: Nat, +u: Nat, +h: {Nat.is_le(Nat.add(x, k), u) == True{} : Bool}) -> {Nat.sub(u, x) == Nat.add(Nat.sub(u, Nat.add(x, k)), k) : Nat}:
  +r = Nat.sub(u, Nat.add(x, k))
  +eu = N.sub_add(u, Nat.add(x, k), h)
  Equal.trans(Nat, Nat.sub(u, x), Nat.sub(Nat.add(Nat.add(x, k), r), x), Nat.add(r, k), Equal.cong(Nat, Nat, z => Nat.sub(z, x), u, Nat.add(Nat.add(x, k), r), Equal.sym(Nat, Nat.add(Nat.add(x, k), r), u, eu)), Equal.trans(Nat, Nat.sub(Nat.add(Nat.add(x, k), r), x), Nat.sub(Nat.add(x, Nat.add(k, r)), x), Nat.add(r, k), Equal.cong(Nat, Nat, z => Nat.sub(z, x), Nat.add(Nat.add(x, k), r), Nat.add(x, Nat.add(k, r)), NA.add_assoc(x, k, r)), Equal.trans(Nat, Nat.sub(Nat.add(x, Nat.add(k, r)), x), Nat.add(k, r), Nat.add(r, k), N.add_sub_cancel(x, Nat.add(k, r)), NA.add_comm(k, r))))

def qeq_f(+k: Nat, +m: Nat, +x: Nat, +u: Nat, +c1: Bool, +hc1: {Nat.is_le(x, u) == c1 : Bool}, +hc2: {Nat.is_le(Nat.add(x, k), u) == False{} : Bool}) -> {SF.pick(Nat, c1, SF.rne(C.shift(k, m), Nat.sub(u, x)), C.shift(Nat.sub(x, u), C.shift(k, m))) == C.shift(Nat.sub(Nat.add(x, k), u), m) : Nat}:
  match c1:
    case True{}:
      +t = Nat.sub(u, x)
      +eu = N.sub_add(u, x, hc1)
      +hlt0 = N.not_le_lt(Nat.add(x, k), u, hc2)
      +hlt1 = L.subst(Nat, z => {Nat.is_lt(z, Nat.add(x, k)) == True{} : Bool}, u, Nat.add(x, t), Equal.sym(Nat, Nat.add(x, t), u, eu), hlt0)
      +hlt2 = Equal.trans(Bool, Nat.is_lt(t, k), Nat.is_lt(Nat.add(x, t), Nat.add(x, k)), True{}, Equal.sym(Bool, Nat.is_lt(Nat.add(x, t), Nat.add(x, k)), Nat.is_lt(t, k), WW.lt_cancel_l(x, t, k)), hlt1)
      +htk = N.lt_le(t, k, hlt2)
      +es = NC.sh_split(k, t, m, htk)
      +e1 = Equal.trans(Nat, SF.rne(C.shift(k, m), t), SF.rne(C.shift(t, C.shift(Nat.sub(k, t), m)), t), C.shift(Nat.sub(k, t), m), Equal.cong(Nat, Nat, z => SF.rne(z, t), C.shift(k, m), C.shift(t, C.shift(Nat.sub(k, t), m)), es), rne_exact(t, C.shift(Nat.sub(k, t), m)))
      +e2 = Equal.trans(Nat, Nat.sub(k, t), Nat.sub(Nat.add(k, x), Nat.add(t, x)), Nat.sub(Nat.add(x, k), u), Equal.sym(Nat, Nat.sub(Nat.add(k, x), Nat.add(t, x)), Nat.sub(k, t), sub_cancel_r(k, t, x)), Equal.trans(Nat, Nat.sub(Nat.add(k, x), Nat.add(t, x)), Nat.sub(Nat.add(x, k), Nat.add(t, x)), Nat.sub(Nat.add(x, k), u), Equal.cong(Nat, Nat, z => Nat.sub(z, Nat.add(t, x)), Nat.add(k, x), Nat.add(x, k), NA.add_comm(k, x)), Equal.cong(Nat, Nat, z => Nat.sub(Nat.add(x, k), z), Nat.add(t, x), u, Equal.trans(Nat, Nat.add(t, x), Nat.add(x, t), u, NA.add_comm(t, x), eu))))
      Equal.trans(Nat, SF.rne(C.shift(k, m), t), C.shift(Nat.sub(k, t), m), C.shift(Nat.sub(Nat.add(x, k), u), m), e1, Equal.cong(Nat, Nat, z => C.shift(z, m), Nat.sub(k, t), Nat.sub(Nat.add(x, k), u), e2))
    case False{}:
      +hux = N.lt_le(u, x, N.not_le_lt(x, u, hc1))
      Equal.trans(Nat, C.shift(Nat.sub(x, u), C.shift(k, m)), C.shift(Nat.add(Nat.sub(x, u), k), m), C.shift(Nat.sub(Nat.add(x, k), u), m), Equal.sym(Nat, C.shift(Nat.add(Nat.sub(x, u), k), m), C.shift(Nat.sub(x, u), C.shift(k, m)), WW.shift_comp(Nat.sub(x, u), k, m)), Equal.cong(Nat, Nat, z => C.shift(z, m), Nat.add(Nat.sub(x, u), k), Nat.sub(Nat.add(x, k), u), Equal.sym(Nat, Nat.sub(Nat.add(x, k), u), Nat.add(Nat.sub(x, u), k), sub_add_r(x, k, u, hux))))

def qeq_c(+k: Nat, +m: Nat, +x: Nat, +u: Nat, +c1: Bool, +hc1: {Nat.is_le(x, u) == c1 : Bool}, +c2: Bool, +hc2: {Nat.is_le(Nat.add(x, k), u) == c2 : Bool}) -> {SF.pick(Nat, c1, SF.rne(C.shift(k, m), Nat.sub(u, x)), C.shift(Nat.sub(x, u), C.shift(k, m))) == SF.pick(Nat, c2, SF.rne(m, Nat.sub(u, Nat.add(x, k))), C.shift(Nat.sub(Nat.add(x, k), u), m)) : Nat}:
  match c2:
    case True{}:
      +h1 = N.le_trans(x, Nat.add(x, k), u, N.le_add_right(x, k), hc2)
      +ec1 = Equal.trans(Bool, c1, Nat.is_le(x, u), True{}, Equal.sym(Bool, Nat.is_le(x, u), c1, hc1), h1)
      +r = Nat.sub(u, Nat.add(x, k))
      +base = Equal.trans(Nat, SF.rne(C.shift(k, m), Nat.sub(u, x)), SF.rne(C.shift(k, m), Nat.add(r, k)), SF.rne(m, r), Equal.cong(Nat, Nat, z => SF.rne(C.shift(k, m), z), Nat.sub(u, x), Nat.add(r, k), a1(x, k, u, hc2)), rne_shift(k, m, r))
      L.subst(Bool, t => {SF.pick(Nat, t, SF.rne(C.shift(k, m), Nat.sub(u, x)), C.shift(Nat.sub(x, u), C.shift(k, m))) == SF.rne(m, r) : Nat}, True{}, c1, Equal.sym(Bool, c1, True{}, ec1), base)
    case False{}:
      qeq_f(k, m, x, u, c1, hc1, hc2)

def rs_c(+s: Bool, +k: Nat, +m: Nat, +x: Nat, +z: Bool, +hz: {Nat.is_eq(m, 0n) == z : Bool}) -> {SF.round(s, C.shift(k, m), x) == SF.round(s, m, Nat.add(x, k)) : F.F64}:
  match z:
    case True{}:
      +e0 = Equal.trans(Bool, Nat.is_eq(C.shift(k, m), 0n), Nat.is_eq(m, 0n), True{}, WW.shift_eq0(k, m), hz)
      Equal.trans(F.F64, SF.round(s, C.shift(k, m), x), SF.zero(s), SF.round(s, m, Nat.add(x, k)), Equal.cong(Bool, F.F64, t => SF.pick(F.F64, t, SF.zero(s), SF.round_u(s, C.shift(k, m), x, Nat.max(Nat.sub(Nat.add(x, M.bit_length(C.shift(k, m))), 53n), Nat.sub(SF.zb(), 1074n)))), Nat.is_eq(C.shift(k, m), 0n), True{}, e0), Equal.sym(F.F64, SF.round(s, m, Nat.add(x, k)), SF.zero(s), Equal.cong(Bool, F.F64, t => SF.pick(F.F64, t, SF.zero(s), SF.round_u(s, m, Nat.add(x, k), Nat.max(Nat.sub(Nat.add(Nat.add(x, k), M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n)))), Nat.is_eq(m, 0n), True{}, hz)))
    case False{}:
      +B = M.bit_length(m)
      +e0 = Equal.trans(Bool, Nat.is_eq(C.shift(k, m), 0n), Nat.is_eq(m, 0n), False{}, WW.shift_eq0(k, m), hz)
      +l1 = Equal.cong(Bool, F.F64, t => SF.pick(F.F64, t, SF.zero(s), SF.round_u(s, C.shift(k, m), x, Nat.max(Nat.sub(Nat.add(x, M.bit_length(C.shift(k, m))), 53n), Nat.sub(SF.zb(), 1074n)))), Nat.is_eq(C.shift(k, m), 0n), False{}, e0)
      +ea = Equal.trans(Nat, Nat.add(x, Nat.add(B, k)), Nat.add(x, Nat.add(k, B)), Nat.add(Nat.add(x, k), B), Equal.cong(Nat, Nat, z => Nat.add(x, z), Nat.add(B, k), Nat.add(k, B), NA.add_comm(B, k)), Equal.sym(Nat, Nat.add(Nat.add(x, k), B), Nat.add(x, Nat.add(k, B)), NA.add_assoc(x, k, B)))
      +eu = Equal.trans(Nat, Nat.max(Nat.sub(Nat.add(x, M.bit_length(C.shift(k, m))), 53n), Nat.sub(SF.zb(), 1074n)), Nat.max(Nat.sub(Nat.add(x, Nat.add(B, k)), 53n), Nat.sub(SF.zb(), 1074n)), Nat.max(Nat.sub(Nat.add(Nat.add(x, k), M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n)), Equal.cong(Nat, Nat, w => Nat.max(Nat.sub(Nat.add(x, w), 53n), Nat.sub(SF.zb(), 1074n)), M.bit_length(C.shift(k, m)), Nat.add(B, k), bl_shift(k, m, hz)), Equal.cong(Nat, Nat, w => Nat.max(Nat.sub(w, 53n), Nat.sub(SF.zb(), 1074n)), Nat.add(x, Nat.add(B, k)), Nat.add(Nat.add(x, k), B), ea))
      +l2 = Equal.cong(Nat, F.F64, w => SF.round_u(s, C.shift(k, m), x, w), Nat.max(Nat.sub(Nat.add(x, M.bit_length(C.shift(k, m))), 53n), Nat.sub(SF.zb(), 1074n)), Nat.max(Nat.sub(Nat.add(Nat.add(x, k), M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n)), eu)
      +l3 = Equal.cong(Nat, F.F64, w => SF.pack(s, w, Nat.max(Nat.sub(Nat.add(Nat.add(x, k), M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n))), SF.pick(Nat, Nat.is_le(x, Nat.max(Nat.sub(Nat.add(Nat.add(x, k), M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n))), SF.rne(C.shift(k, m), Nat.sub(Nat.max(Nat.sub(Nat.add(Nat.add(x, k), M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n)), x)), C.shift(Nat.sub(x, Nat.max(Nat.sub(Nat.add(Nat.add(x, k), M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n))), C.shift(k, m))), SF.pick(Nat, Nat.is_le(Nat.add(x, k), Nat.max(Nat.sub(Nat.add(Nat.add(x, k), M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n))), SF.rne(m, Nat.sub(Nat.max(Nat.sub(Nat.add(Nat.add(x, k), M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n)), Nat.add(x, k))), C.shift(Nat.sub(Nat.add(x, k), Nat.max(Nat.sub(Nat.add(Nat.add(x, k), M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n))), m)), qeq_c(k, m, x, Nat.max(Nat.sub(Nat.add(Nat.add(x, k), M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n)), Nat.is_le(x, Nat.max(Nat.sub(Nat.add(Nat.add(x, k), M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n))), {==}, Nat.is_le(Nat.add(x, k), Nat.max(Nat.sub(Nat.add(Nat.add(x, k), M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n))), {==}))
      +r1 = Equal.cong(Bool, F.F64, t => SF.pick(F.F64, t, SF.zero(s), SF.round_u(s, m, Nat.add(x, k), Nat.max(Nat.sub(Nat.add(Nat.add(x, k), M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n)))), Nat.is_eq(m, 0n), False{}, hz)
      Equal.trans(F.F64, SF.round(s, C.shift(k, m), x), SF.round_u(s, m, Nat.add(x, k), Nat.max(Nat.sub(Nat.add(Nat.add(x, k), M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n))), SF.round(s, m, Nat.add(x, k)), Equal.trans(F.F64, SF.round(s, C.shift(k, m), x), SF.round_u(s, C.shift(k, m), x, Nat.max(Nat.sub(Nat.add(x, M.bit_length(C.shift(k, m))), 53n), Nat.sub(SF.zb(), 1074n))), SF.round_u(s, m, Nat.add(x, k), Nat.max(Nat.sub(Nat.add(Nat.add(x, k), M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n))), l1, Equal.trans(F.F64, SF.round_u(s, C.shift(k, m), x, Nat.max(Nat.sub(Nat.add(x, M.bit_length(C.shift(k, m))), 53n), Nat.sub(SF.zb(), 1074n))), SF.round_u(s, C.shift(k, m), x, Nat.max(Nat.sub(Nat.add(Nat.add(x, k), M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n))), SF.round_u(s, m, Nat.add(x, k), Nat.max(Nat.sub(Nat.add(Nat.add(x, k), M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n))), l2, l3)), Equal.sym(F.F64, SF.round(s, m, Nat.add(x, k)), SF.round_u(s, m, Nat.add(x, k), Nat.max(Nat.sub(Nat.add(Nat.add(x, k), M.bit_length(m)), 53n), Nat.sub(SF.zb(), 1074n))), r1))

def round_shift(+s: Bool, +k: Nat, +m: Nat, +x: Nat) -> {SF.round(s, C.shift(k, m), x) == SF.round(s, m, Nat.add(x, k)) : F.F64}:
  rs_c(s, k, m, x, Nat.is_eq(m, 0n), {==})

