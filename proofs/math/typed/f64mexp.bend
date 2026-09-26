import Base
import ../../../spec/math/f64.bend as SF
import ../../../spec/math/w64.bend as SW
import ../../../src/math/f64.bend as F
import ../../../src/math/w64.bend as X
import ../../../src/math/u64.bend as WU
import ../../../src/math/natural.bend as M
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ./w64mul.bend as W64M
import ./natfuel.bend as NF
import ./u32laws.bend as LW
import ./w64clz.bend as CLZ
import ../../lib/u32half.bend as UH
import ../../lib/u32alg.bend as A
import ./f64cmp.bend as FC
import ./f64round.bend as FR
import ./f64rtools.bend as RT
import ./f64norm.bend as NM

# Mul.value of spec/math/f64.bend: SoftFloat's f64_mul multiplies the two
# normalized 53-bit significands (shifted by 10 and 11) into 128 bits, jams
# the low half into bit 0 and rounds with rp62; the spec rounds the exact
# product of the significands. round_jam and round_shift bridge the two.


# ---- exponent bookkeeping ----

def sa_le(+ea: Nat, +fa: WU.U64) -> {Nat.is_le(NM.sa(ea, fa), 53n) == True{} : Bool}:
  match ea:
    case 0n:
      +hc = L.subst(Nat, z => {Nat.is_le(z, 64n) == True{} : Bool}, Nat.sub(64n, M.bit_length(SW.value(fa))), X.clz(fa), Equal.sym(Nat, X.clz(fa), Nat.sub(64n, M.bit_length(SW.value(fa))), CLZ.clz_value(fa)), UH.sub_le(64n, M.bit_length(SW.value(fa))))
      NF.sub_mono_l(X.clz(fa), 64n, 11n, hc)
    case 1n+ +p:
      {==}

def e_ge1(+E: Nat, +h: {Nat.is_eq(E, 0n) == False{} : Bool}) -> {Nat.is_le(1926n, Nat.add(1925n, E)) == True{} : Bool}:
  match E:
    case 0n:
      Empty.absurd({Nat.is_le(1926n, Nat.add(1925n, 0n)) == True{} : Bool}, LW.true_ne_false(h))
    case 1n+ +p:
      N.zero_le(p)

def xg_c(+E: Nat, +c: Bool, +hc: {Nat.is_eq(E, 0n) == c : Bool}) -> {Nat.is_le(1926n, SF.pick(Nat, c, Nat.sub(SF.zb(), 1074n), Nat.sub(Nat.add(E, SF.zb()), 1075n))) == True{} : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      L.subst(Nat, z => {Nat.is_le(1926n, z) == True{} : Bool}, Nat.add(1925n, E), Nat.sub(Nat.add(E, SF.zb()), 1075n), Equal.sym(Nat, Nat.sub(Nat.add(E, SF.zb()), 1075n), Nat.add(1925n, E), FC.esub(E)), e_ge1(E, hc))

def xexp_ge(+E: Nat) -> {Nat.is_le(1926n, SF.pick(Nat, Nat.is_eq(E, 0n), Nat.sub(SF.zb(), 1074n), Nat.sub(Nat.add(E, SF.zb()), 1075n))) == True{} : Bool}:
  xg_c(E, Nat.is_eq(E, 0n), {==})

def eg(+ea: Nat, +sa: Nat, +Xx: Nat, +n2: {Nat.add(ea, sa) == Nat.add(Xx, 2171n) : Nat}, +hs: {Nat.is_le(sa, 53n) == True{} : Bool}, +hX: {Nat.is_le(1926n, Xx) == True{} : Bool}) -> {Nat.is_le(4044n, ea) == True{} : Bool}:
  +h1 = L.subst(Nat, z => {Nat.is_le(4097n, z) == True{} : Bool}, Nat.add(Xx, 2171n), Nat.add(ea, sa), Equal.sym(Nat, Nat.add(ea, sa), Nat.add(Xx, 2171n), n2), Equal.trans(Bool, Nat.is_le(Nat.add(1926n, 2171n), Nat.add(Xx, 2171n)), Nat.is_le(1926n, Xx), True{}, FR.le_cancel_r(1926n, Xx, 2171n), hX))
  +h2 = N.le_trans(4097n, Nat.add(ea, sa), Nat.add(ea, 53n), h1, N.le_add_left(sa, 53n, ea, hs))
  Equal.trans(Bool, Nat.is_le(4044n, ea), Nat.is_le(Nat.add(4044n, 53n), Nat.add(ea, 53n)), True{}, Equal.sym(Bool, Nat.is_le(Nat.add(4044n, 53n), Nat.add(ea, 53n)), Nat.is_le(4044n, ea), FR.le_cancel_r(4044n, ea, 53n)), h2)

def s_ge(+ea: Nat, +eb: Nat, +sa: Nat, +sb: Nat, +Xx: Nat, +Xy: Nat, +n2x: {Nat.add(ea, sa) == Nat.add(Xx, 2171n) : Nat}, +n2y: {Nat.add(eb, sb) == Nat.add(Xy, 2171n) : Nat}, +hsa: {Nat.is_le(sa, 53n) == True{} : Bool}, +hsb: {Nat.is_le(sb, 53n) == True{} : Bool}, +hXx: {Nat.is_le(1926n, Xx) == True{} : Bool}, +hXy: {Nat.is_le(1926n, Xy) == True{} : Bool}) -> {Nat.is_le(8088n, Nat.add(ea, eb)) == True{} : Bool}:
  +ha = eg(ea, sa, Xx, n2x, hsa, hXx)
  +hb = eg(eb, sb, Xy, n2y, hsb, hXy)
  N.le_trans(8088n, Nat.add(4044n, eb), Nat.add(ea, eb), N.le_add_left(4044n, eb, 4044n, hb), Equal.trans(Bool, Nat.is_le(Nat.add(4044n, eb), Nat.add(ea, eb)), Nat.is_le(4044n, ea), True{}, FR.le_cancel_r(4044n, ea, eb), ha))

def e0_ge(+ea: Nat, +eb: Nat, +sa: Nat, +sb: Nat, +Xx: Nat, +Xy: Nat, +n2x: {Nat.add(ea, sa) == Nat.add(Xx, 2171n) : Nat}, +n2y: {Nat.add(eb, sb) == Nat.add(Xy, 2171n) : Nat}, +hsa: {Nat.is_le(sa, 53n) == True{} : Bool}, +hsb: {Nat.is_le(sb, 53n) == True{} : Bool}, +hXx: {Nat.is_le(1926n, Xx) == True{} : Bool}, +hXy: {Nat.is_le(1926n, Xy) == True{} : Bool}) -> {Nat.is_le(2244n, Nat.sub(Nat.add(ea, eb), Nat.add(F.off(), 1023n))) == True{} : Bool}:
  RT.le_sub(2244n, 5119n, Nat.add(ea, eb), N.le_trans(Nat.add(2244n, 5119n), 8088n, Nat.add(ea, eb), {==}, s_ge(ea, eb, sa, sb, Xx, Xy, n2x, n2y, hsa, hsb, hXx, hXy)))

def x_eq(+ea: Nat, +eb: Nat, +sa: Nat, +sb: Nat, +Xx: Nat, +Xy: Nat, +n2x: {Nat.add(ea, sa) == Nat.add(Xx, 2171n) : Nat}, +n2y: {Nat.add(eb, sb) == Nat.add(Xy, 2171n) : Nat}, +hsa: {Nat.is_le(sa, 53n) == True{} : Bool}, +hsb: {Nat.is_le(sb, 53n) == True{} : Bool}, +hXx: {Nat.is_le(1926n, Xx) == True{} : Bool}, +hXy: {Nat.is_le(1926n, Xy) == True{} : Bool}) -> {Nat.add(Nat.sub(Nat.sub(Nat.add(ea, eb), Nat.add(F.off(), 1023n)), 2180n), 2180n) == Nat.sub(Nat.add(ea, eb), Nat.add(F.off(), 1023n)) : Nat}:
  +h = N.le_trans(2180n, 2244n, Nat.sub(Nat.add(ea, eb), Nat.add(F.off(), 1023n)), {==}, e0_ge(ea, eb, sa, sb, Xx, Xy, n2x, n2y, hsa, hsb, hXx, hXy))
  Equal.trans(Nat, Nat.add(Nat.sub(Nat.sub(Nat.add(ea, eb), Nat.add(F.off(), 1023n)), 2180n), 2180n), Nat.add(2180n, Nat.sub(Nat.sub(Nat.add(ea, eb), Nat.add(F.off(), 1023n)), 2180n)), Nat.sub(Nat.add(ea, eb), Nat.add(F.off(), 1023n)), NA.add_comm(Nat.sub(Nat.sub(Nat.add(ea, eb), Nat.add(F.off(), 1023n)), 2180n), 2180n), N.sub_add(Nat.sub(Nat.add(ea, eb), Nat.add(F.off(), 1023n)), 2180n, h))

def x_ge(+ea: Nat, +eb: Nat, +sa: Nat, +sb: Nat, +Xx: Nat, +Xy: Nat, +n2x: {Nat.add(ea, sa) == Nat.add(Xx, 2171n) : Nat}, +n2y: {Nat.add(eb, sb) == Nat.add(Xy, 2171n) : Nat}, +hsa: {Nat.is_le(sa, 53n) == True{} : Bool}, +hsb: {Nat.is_le(sb, 53n) == True{} : Bool}, +hXx: {Nat.is_le(1926n, Xx) == True{} : Bool}, +hXy: {Nat.is_le(1926n, Xy) == True{} : Bool}) -> {Nat.is_le(64n, Nat.sub(Nat.sub(Nat.add(ea, eb), Nat.add(F.off(), 1023n)), 2180n)) == True{} : Bool}:
  RT.le_sub(64n, 2180n, Nat.sub(Nat.add(ea, eb), Nat.add(F.off(), 1023n)), e0_ge(ea, eb, sa, sb, Xx, Xy, n2x, n2y, hsa, hsb, hXx, hXy))

def x0_eq(+ea: Nat, +eb: Nat, +sa: Nat, +sb: Nat, +Xx: Nat, +Xy: Nat, +n2x: {Nat.add(ea, sa) == Nat.add(Xx, 2171n) : Nat}, +n2y: {Nat.add(eb, sb) == Nat.add(Xy, 2171n) : Nat}, +hsa: {Nat.is_le(sa, 53n) == True{} : Bool}, +hsb: {Nat.is_le(sb, 53n) == True{} : Bool}, +hXx: {Nat.is_le(1926n, Xx) == True{} : Bool}, +hXy: {Nat.is_le(1926n, Xy) == True{} : Bool}) -> {Nat.add(Nat.sub(Nat.sub(Nat.sub(Nat.add(ea, eb), Nat.add(F.off(), 1023n)), 2180n), 64n), 64n) == Nat.sub(Nat.sub(Nat.add(ea, eb), Nat.add(F.off(), 1023n)), 2180n) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.sub(Nat.sub(Nat.sub(Nat.add(ea, eb), Nat.add(F.off(), 1023n)), 2180n), 64n), 64n), Nat.add(64n, Nat.sub(Nat.sub(Nat.sub(Nat.add(ea, eb), Nat.add(F.off(), 1023n)), 2180n), 64n)), Nat.sub(Nat.sub(Nat.add(ea, eb), Nat.add(F.off(), 1023n)), 2180n), NA.add_comm(Nat.sub(Nat.sub(Nat.sub(Nat.add(ea, eb), Nat.add(F.off(), 1023n)), 2180n), 64n), 64n), N.sub_add(Nat.sub(Nat.sub(Nat.add(ea, eb), Nat.add(F.off(), 1023n)), 2180n), 64n, x_ge(ea, eb, sa, sb, Xx, Xy, n2x, n2y, hsa, hsb, hXx, hXy)))

# x0 + 21 + sa + sb is the spec's product exponent
def mexp(+ea: Nat, +eb: Nat, +sa: Nat, +sb: Nat, +Xx: Nat, +Xy: Nat, +n2x: {Nat.add(ea, sa) == Nat.add(Xx, 2171n) : Nat}, +n2y: {Nat.add(eb, sb) == Nat.add(Xy, 2171n) : Nat}, +hsa: {Nat.is_le(sa, 53n) == True{} : Bool}, +hsb: {Nat.is_le(sb, 53n) == True{} : Bool}, +hXx: {Nat.is_le(1926n, Xx) == True{} : Bool}, +hXy: {Nat.is_le(1926n, Xy) == True{} : Bool}) -> {Nat.add(Nat.add(Nat.sub(Nat.sub(Nat.sub(Nat.add(ea, eb), Nat.add(F.off(), 1023n)), 2180n), 64n), 21n), Nat.add(sa, sb)) == Nat.sub(Nat.add(Xx, Xy), SF.zb()) : Nat}:
  +ex0 = x0_eq(ea, eb, sa, sb, Xx, Xy, n2x, n2y, hsa, hsb, hXx, hXy)
  +exx = x_eq(ea, eb, sa, sb, Xx, Xy, n2x, n2y, hsa, hsb, hXx, hXy)
  +eS0 = Equal.trans(Nat, Nat.add(Nat.sub(Nat.add(ea, eb), Nat.add(F.off(), 1023n)), 5119n), Nat.add(5119n, Nat.sub(Nat.add(ea, eb), Nat.add(F.off(), 1023n))), Nat.add(ea, eb), NA.add_comm(Nat.sub(Nat.add(ea, eb), Nat.add(F.off(), 1023n)), 5119n), N.sub_add(Nat.add(ea, eb), 5119n, N.le_trans(5119n, 8088n, Nat.add(ea, eb), {==}, s_ge(ea, eb, sa, sb, Xx, Xy, n2x, n2y, hsa, hsb, hXx, hXy))))
  +eS = Equal.trans(Nat, Nat.add(ea, eb), Nat.add(Nat.sub(Nat.add(ea, eb), Nat.add(F.off(), 1023n)), 5119n), Nat.add(Nat.sub(Nat.sub(Nat.sub(Nat.add(ea, eb), Nat.add(F.off(), 1023n)), 2180n), 64n), 7363n), Equal.sym(Nat, Nat.add(Nat.sub(Nat.add(ea, eb), Nat.add(F.off(), 1023n)), 5119n), Nat.add(ea, eb), eS0), Equal.trans(Nat, Nat.add(Nat.sub(Nat.add(ea, eb), Nat.add(F.off(), 1023n)), 5119n), Nat.add(Nat.add(Nat.sub(Nat.sub(Nat.add(ea, eb), Nat.add(F.off(), 1023n)), 2180n), 2180n), 5119n), Nat.add(Nat.sub(Nat.sub(Nat.sub(Nat.add(ea, eb), Nat.add(F.off(), 1023n)), 2180n), 64n), 7363n), Equal.cong(Nat, Nat, z => Nat.add(z, 5119n), Nat.sub(Nat.add(ea, eb), Nat.add(F.off(), 1023n)), Nat.add(Nat.sub(Nat.sub(Nat.add(ea, eb), Nat.add(F.off(), 1023n)), 2180n), 2180n), Equal.sym(Nat, Nat.add(Nat.sub(Nat.sub(Nat.add(ea, eb), Nat.add(F.off(), 1023n)), 2180n), 2180n), Nat.sub(Nat.add(ea, eb), Nat.add(F.off(), 1023n)), exx)), Equal.trans(Nat, Nat.add(Nat.add(Nat.sub(Nat.sub(Nat.add(ea, eb), Nat.add(F.off(), 1023n)), 2180n), 2180n), 5119n), Nat.add(Nat.add(Nat.add(Nat.sub(Nat.sub(Nat.sub(Nat.add(ea, eb), Nat.add(F.off(), 1023n)), 2180n), 64n), 64n), 2180n), 5119n), Nat.add(Nat.sub(Nat.sub(Nat.sub(Nat.add(ea, eb), Nat.add(F.off(), 1023n)), 2180n), 64n), 7363n), Equal.cong(Nat, Nat, z => Nat.add(Nat.add(z, 2180n), 5119n), Nat.sub(Nat.sub(Nat.add(ea, eb), Nat.add(F.off(), 1023n)), 2180n), Nat.add(Nat.sub(Nat.sub(Nat.sub(Nat.add(ea, eb), Nat.add(F.off(), 1023n)), 2180n), 64n), 64n), Equal.sym(Nat, Nat.add(Nat.sub(Nat.sub(Nat.sub(Nat.add(ea, eb), Nat.add(F.off(), 1023n)), 2180n), 64n), 64n), Nat.sub(Nat.sub(Nat.add(ea, eb), Nat.add(F.off(), 1023n)), 2180n), ex0)), Equal.trans(Nat, Nat.add(Nat.add(Nat.add(Nat.sub(Nat.sub(Nat.sub(Nat.add(ea, eb), Nat.add(F.off(), 1023n)), 2180n), 64n), 64n), 2180n), 5119n), Nat.add(Nat.add(Nat.sub(Nat.sub(Nat.sub(Nat.add(ea, eb), Nat.add(F.off(), 1023n)), 2180n), 64n), 64n), 7299n), Nat.add(Nat.sub(Nat.sub(Nat.sub(Nat.add(ea, eb), Nat.add(F.off(), 1023n)), 2180n), 64n), 7363n), NA.add_assoc(Nat.add(Nat.sub(Nat.sub(Nat.sub(Nat.add(ea, eb), Nat.add(F.off(), 1023n)), 2180n), 64n), 64n), 2180n, 5119n), NA.add_assoc(Nat.sub(Nat.sub(Nat.sub(Nat.add(ea, eb), Nat.add(F.off(), 1023n)), 2180n), 64n), 64n, 7299n)))))
  +e1 = Equal.trans(Nat, Nat.add(Nat.add(ea, sa), Nat.add(eb, sb)), Nat.add(Nat.add(Xx, 2171n), Nat.add(eb, sb)), Nat.add(Nat.add(Xx, 2171n), Nat.add(Xy, 2171n)), Equal.cong(Nat, Nat, z => Nat.add(z, Nat.add(eb, sb)), Nat.add(ea, sa), Nat.add(Xx, 2171n), n2x), Equal.cong(Nat, Nat, z => Nat.add(Nat.add(Xx, 2171n), z), Nat.add(eb, sb), Nat.add(Xy, 2171n), n2y))
  +e2 = W64M.add4(ea, sa, eb, sb)
  +e3 = W64M.add4(Xx, 2171n, Xy, 2171n)
  +T2 = Nat.add(sa, sb)
  +W = Nat.add(Nat.add(Nat.sub(Nat.sub(Nat.sub(Nat.add(ea, eb), Nat.add(F.off(), 1023n)), 2180n), 64n), 21n), T2)
  +e4 = Equal.trans(Nat, Nat.add(Nat.add(W, 3000n), 4342n), Nat.add(W, 7342n), Nat.add(Nat.add(Xx, Xy), 4342n), NA.add_assoc(W, 3000n, 4342n), Equal.trans(Nat, Nat.add(W, 7342n), Nat.add(Nat.add(Nat.sub(Nat.sub(Nat.sub(Nat.add(ea, eb), Nat.add(F.off(), 1023n)), 2180n), 64n), 21n), Nat.add(T2, 7342n)), Nat.add(Nat.add(Xx, Xy), 4342n), NA.add_assoc(Nat.add(Nat.sub(Nat.sub(Nat.sub(Nat.add(ea, eb), Nat.add(F.off(), 1023n)), 2180n), 64n), 21n), T2, 7342n), Equal.trans(Nat, Nat.add(Nat.add(Nat.sub(Nat.sub(Nat.sub(Nat.add(ea, eb), Nat.add(F.off(), 1023n)), 2180n), 64n), 21n), Nat.add(T2, 7342n)), Nat.add(Nat.add(Nat.sub(Nat.sub(Nat.sub(Nat.add(ea, eb), Nat.add(F.off(), 1023n)), 2180n), 64n), 21n), Nat.add(7342n, T2)), Nat.add(Nat.add(Xx, Xy), 4342n), Equal.cong(Nat, Nat, z => Nat.add(Nat.add(Nat.sub(Nat.sub(Nat.sub(Nat.add(ea, eb), Nat.add(F.off(), 1023n)), 2180n), 64n), 21n), z), Nat.add(T2, 7342n), Nat.add(7342n, T2), NA.add_comm(T2, 7342n)), Equal.trans(Nat, Nat.add(Nat.add(Nat.sub(Nat.sub(Nat.sub(Nat.add(ea, eb), Nat.add(F.off(), 1023n)), 2180n), 64n), 21n), Nat.add(7342n, T2)), Nat.add(Nat.add(Nat.add(Nat.sub(Nat.sub(Nat.sub(Nat.add(ea, eb), Nat.add(F.off(), 1023n)), 2180n), 64n), 21n), 7342n), T2), Nat.add(Nat.add(Xx, Xy), 4342n), Equal.sym(Nat, Nat.add(Nat.add(Nat.add(Nat.sub(Nat.sub(Nat.sub(Nat.add(ea, eb), Nat.add(F.off(), 1023n)), 2180n), 64n), 21n), 7342n), T2), Nat.add(Nat.add(Nat.sub(Nat.sub(Nat.sub(Nat.add(ea, eb), Nat.add(F.off(), 1023n)), 2180n), 64n), 21n), Nat.add(7342n, T2)), NA.add_assoc(Nat.add(Nat.sub(Nat.sub(Nat.sub(Nat.add(ea, eb), Nat.add(F.off(), 1023n)), 2180n), 64n), 21n), 7342n, T2)), Equal.trans(Nat, Nat.add(Nat.add(Nat.add(Nat.sub(Nat.sub(Nat.sub(Nat.add(ea, eb), Nat.add(F.off(), 1023n)), 2180n), 64n), 21n), 7342n), T2), Nat.add(Nat.add(Nat.sub(Nat.sub(Nat.sub(Nat.add(ea, eb), Nat.add(F.off(), 1023n)), 2180n), 64n), 7363n), T2), Nat.add(Nat.add(Xx, Xy), 4342n), Equal.cong(Nat, Nat, z => Nat.add(z, T2), Nat.add(Nat.add(Nat.sub(Nat.sub(Nat.sub(Nat.add(ea, eb), Nat.add(F.off(), 1023n)), 2180n), 64n), 21n), 7342n), Nat.add(Nat.sub(Nat.sub(Nat.sub(Nat.add(ea, eb), Nat.add(F.off(), 1023n)), 2180n), 64n), 7363n), NA.add_assoc(Nat.sub(Nat.sub(Nat.sub(Nat.add(ea, eb), Nat.add(F.off(), 1023n)), 2180n), 64n), 21n, 7342n)), Equal.trans(Nat, Nat.add(Nat.add(Nat.sub(Nat.sub(Nat.sub(Nat.add(ea, eb), Nat.add(F.off(), 1023n)), 2180n), 64n), 7363n), T2), Nat.add(Nat.add(ea, eb), T2), Nat.add(Nat.add(Xx, Xy), 4342n), Equal.cong(Nat, Nat, z => Nat.add(z, T2), Nat.add(Nat.sub(Nat.sub(Nat.sub(Nat.add(ea, eb), Nat.add(F.off(), 1023n)), 2180n), 64n), 7363n), Nat.add(ea, eb), Equal.sym(Nat, Nat.add(ea, eb), Nat.add(Nat.sub(Nat.sub(Nat.sub(Nat.add(ea, eb), Nat.add(F.off(), 1023n)), 2180n), 64n), 7363n), eS)), Equal.trans(Nat, Nat.add(Nat.add(ea, eb), T2), Nat.add(Nat.add(ea, sa), Nat.add(eb, sb)), Nat.add(Nat.add(Xx, Xy), 4342n), Equal.sym(Nat, Nat.add(Nat.add(ea, sa), Nat.add(eb, sb)), Nat.add(Nat.add(ea, eb), T2), e2), Equal.trans(Nat, Nat.add(Nat.add(ea, sa), Nat.add(eb, sb)), Nat.add(Nat.add(Xx, 2171n), Nat.add(Xy, 2171n)), Nat.add(Nat.add(Xx, Xy), 4342n), e1, e3))))))))
  +e5 = A.add_cancel_r(Nat.add(W, 3000n), Nat.add(Xx, Xy), 4342n, e4)
  Equal.sym(Nat, Nat.sub(Nat.add(Xx, Xy), SF.zb()), W, Equal.trans(Nat, Nat.sub(Nat.add(Xx, Xy), 3000n), Nat.sub(Nat.add(W, 3000n), 3000n), W, Equal.cong(Nat, Nat, z => Nat.sub(z, 3000n), Nat.add(Xx, Xy), Nat.add(W, 3000n), Equal.sym(Nat, Nat.add(W, 3000n), Nat.add(Xx, Xy), e5)), FR.sub_add_l(W, 3000n)))
