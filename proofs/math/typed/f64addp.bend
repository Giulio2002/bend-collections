import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/math/w64.bend as SW
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../natural/arith.bend as NR
import ./width.bend as WW
import ../../lib/u32alg.bend as A
import ./u32laws.bend as LW
import ./w64sh.bend as SH
import ./natcmp.bend as NC
import ./f64round.bend as FR

# The sticky bit under addition and subtraction of an even term: SoftFloat's
# addMagsF64/subMagsF64 add or subtract the jammed smaller operand, which is
# the jam of the exact sum or difference (the bits below the guard bits
# never meet the even larger operand).

def jam_add(+t: Nat, +h: Nat, +l: Nat) -> {SW.jam(Nat.add(h, Nat.double(t)), l) == Nat.add(SW.jam(h, l), Nat.double(t)) : Nat}:
  +mn = Nat.min(l, 1n)
  +q = Nat.add(h, Nat.double(t))
  Equal.trans(Nat, SW.jam(q, l), Nat.add(Nat.max(C.bit(q), mn), Nat.double(C.half(q))), Nat.add(SW.jam(h, l), Nat.double(t)), FR.jam_form(q, l), Equal.trans(Nat, Nat.add(Nat.max(C.bit(q), mn), Nat.double(C.half(q))), Nat.add(Nat.max(C.bit(h), mn), Nat.double(C.half(q))), Nat.add(SW.jam(h, l), Nat.double(t)), Equal.cong(Nat, Nat, z => Nat.add(Nat.max(z, mn), Nat.double(C.half(q))), C.bit(q), C.bit(h), WW.bit_dbl(h, t)), Equal.trans(Nat, Nat.add(Nat.max(C.bit(h), mn), Nat.double(C.half(q))), Nat.add(Nat.max(C.bit(h), mn), Nat.double(Nat.add(C.half(h), t))), Nat.add(SW.jam(h, l), Nat.double(t)), Equal.cong(Nat, Nat, z => Nat.add(Nat.max(C.bit(h), mn), Nat.double(z)), C.half(q), Nat.add(C.half(h), t), WW.half_dbl(h, t)), Equal.trans(Nat, Nat.add(Nat.max(C.bit(h), mn), Nat.double(Nat.add(C.half(h), t))), Nat.add(Nat.max(C.bit(h), mn), Nat.add(Nat.double(C.half(h)), Nat.double(t))), Nat.add(SW.jam(h, l), Nat.double(t)), Equal.cong(Nat, Nat, z => Nat.add(Nat.max(C.bit(h), mn), z), Nat.double(Nat.add(C.half(h), t)), Nat.add(Nat.double(C.half(h)), Nat.double(t)), NA.double_add(C.half(h), t)), Equal.trans(Nat, Nat.add(Nat.max(C.bit(h), mn), Nat.add(Nat.double(C.half(h)), Nat.double(t))), Nat.add(Nat.add(Nat.max(C.bit(h), mn), Nat.double(C.half(h))), Nat.double(t)), Nat.add(SW.jam(h, l), Nat.double(t)), Equal.sym(Nat, Nat.add(Nat.add(Nat.max(C.bit(h), mn), Nat.double(C.half(h))), Nat.double(t)), Nat.add(Nat.max(C.bit(h), mn), Nat.add(Nat.double(C.half(h)), Nat.double(t))), NA.add_assoc(Nat.max(C.bit(h), mn), Nat.double(C.half(h)), Nat.double(t))), Equal.cong(Nat, Nat, z => Nat.add(z, Nat.double(t)), Nat.add(Nat.max(C.bit(h), mn), Nat.double(C.half(h))), SW.jam(h, l), Equal.sym(Nat, SW.jam(h, l), Nat.add(Nat.max(C.bit(h), mn), Nat.double(C.half(h))), FR.jam_form(h, l))))))))

def jam_z(+h: Nat) -> {SW.jam(h, 0n) == h : Nat}:
  SH.jam0_m(h, Nat.mod(h, 2n), {==}, NR.dm_lt(1n, h))

def jam_nz(+h: Nat, +l: Nat, +hl: {Nat.is_eq(l, 0n) == False{} : Bool}) -> {SW.jam(h, l) == 1n+Nat.double(C.half(h)) : Nat}:
  match l:
    case 0n:
      Empty.absurd({SW.jam(h, 0n) == 1n+Nat.double(C.half(h)) : Nat}, LW.true_ne_false(hl))
    case 1n+ +lp:
      SH.jam1_m(h, lp)

def sub_shift(+d: Nat, +a: Nat, +b: Nat, +h: {Nat.is_le(b, a) == True{} : Bool}) -> {Nat.sub(C.shift(d, a), C.shift(d, b)) == C.shift(d, Nat.sub(a, b)) : Nat}:
  +ea = N.sub_add(a, b, h)
  Equal.trans(Nat, Nat.sub(C.shift(d, a), C.shift(d, b)), Nat.sub(C.shift(d, Nat.add(b, Nat.sub(a, b))), C.shift(d, b)), C.shift(d, Nat.sub(a, b)), Equal.cong(Nat, Nat, z => Nat.sub(C.shift(d, z), C.shift(d, b)), a, Nat.add(b, Nat.sub(a, b)), Equal.sym(Nat, Nat.add(b, Nat.sub(a, b)), a, ea)), Equal.trans(Nat, Nat.sub(C.shift(d, Nat.add(b, Nat.sub(a, b))), C.shift(d, b)), Nat.sub(Nat.add(C.shift(d, b), C.shift(d, Nat.sub(a, b))), C.shift(d, b)), C.shift(d, Nat.sub(a, b)), Equal.cong(Nat, Nat, z => Nat.sub(z, C.shift(d, b)), C.shift(d, Nat.add(b, Nat.sub(a, b))), Nat.add(C.shift(d, b), C.shift(d, Nat.sub(a, b))), WW.shift_add(d, b, Nat.sub(a, b))), N.add_sub_cancel(C.shift(d, b), C.shift(d, Nat.sub(a, b)))))

def half_lt(+k: Nat, +t: Nat, +h: {Nat.is_lt(Nat.double(k), Nat.double(t)) == True{} : Bool}) -> {Nat.is_lt(k, t) == True{} : Bool}:
  Equal.trans(Bool, Nat.is_lt(k, t), Nat.is_lt(Nat.double(k), Nat.double(t)), True{}, Equal.cong(Cmp, Bool, c => Cmp.is_lt(c), Nat.cmp(k, t), Nat.cmp(Nat.double(k), Nat.double(t)), Equal.sym(Cmp, Nat.cmp(Nat.double(k), Nat.double(t)), Nat.cmp(k, t), NC.cmp_dbl(k, t))), h)

def lt_add_l(+l: Nat, +r: Nat, +hl: {Nat.is_eq(l, 0n) == False{} : Bool}) -> {Nat.is_lt(r, Nat.add(l, r)) == True{} : Bool}:
  match l:
    case 0n:
      Empty.absurd({Nat.is_lt(r, Nat.add(0n, r)) == True{} : Bool}, LW.true_ne_false(hl))
    case 1n+ +lp:
      N.le_lt_succ(r, Nat.add(lp, r), L.subst(Nat, z => {Nat.is_le(r, z) == True{} : Bool}, Nat.add(r, lp), Nat.add(lp, r), NA.add_comm(r, lp), N.le_add_right(r, lp)))

def rnz_c(+l: Nat, +R: Nat, +S: Nat, +e: {Nat.add(l, R) == S : Nat}, +hl: {Nat.is_lt(l, S) == True{} : Bool}, +c: Bool, +hc: {Nat.is_eq(R, 0n) == c : Bool}) -> {c == False{} : Bool}:
  match c:
    case True{}:
      +e0 = N.eq_from_is_eq(R, 0n, hc)
      +el = Equal.trans(Nat, l, Nat.add(l, 0n), S, Equal.sym(Nat, Nat.add(l, 0n), l, N.add_zero(l)), Equal.trans(Nat, Nat.add(l, 0n), Nat.add(l, R), S, Equal.cong(Nat, Nat, z => Nat.add(l, z), 0n, R, Equal.sym(Nat, R, 0n, e0)), e))
      Empty.absurd({True{} == False{} : Bool}, LW.true_ne_false(Equal.trans(Bool, True{}, Nat.is_lt(l, S), False{}, Equal.sym(Bool, Nat.is_lt(l, S), True{}, hl), L.subst(Nat, z => {Nat.is_lt(l, z) == False{} : Bool}, l, S, el, N.lt_irrefl(l)))))
    case False{}:
      {==}

def hg_c(+u: Nat, +g: Nat, +b: Nat, +e: {Nat.add(b, 1n+g) == 2n+Nat.double(u) : Nat}, +hb: {Nat.is_le(b, 1n) == True{} : Bool}) -> {C.half(g) == u : Nat}:
  match b:
    case 0n:
      +eg = N.succ_inj(g, 1n+Nat.double(u), e)
      Equal.trans(Nat, C.half(g), C.half(1n+Nat.double(u)), u, Equal.cong(Nat, Nat, z => C.half(z), g, 1n+Nat.double(u), eg), WW.half_dbl(1n, u))
    case 1n:
      +eg = N.succ_inj(g, Nat.double(u), N.succ_inj(1n+g, 1n+Nat.double(u), e))
      Equal.trans(Nat, C.half(g), C.half(Nat.double(u)), u, Equal.cong(Nat, Nat, z => C.half(z), g, Nat.double(u), eg), WW.half_dbl(0n, u))
    case 2n+ +q:
      NC.absurd_tf({C.half(g) == u : Nat}, hb)

# T - jam(h, l) is the jam of T * 2^d - (l + h * 2^d) when 0 < l < 2^d, h < T, T even
def jsub(+t: Nat, +d: Nat, +h: Nat, +l: Nat, +hl0: {Nat.is_eq(l, 0n) == False{} : Bool}, +hld: {C.fits(d, l) == True{} : Bool}, +hh: {Nat.is_lt(h, Nat.double(t)) == True{} : Bool}) -> {Nat.sub(Nat.double(t), SW.jam(h, l)) == SW.jam(C.high(d, Nat.sub(C.shift(d, Nat.double(t)), Nat.add(l, C.shift(d, h)))), C.low(d, Nat.sub(C.shift(d, Nat.double(t)), Nat.add(l, C.shift(d, h))))) : Nat}:
  +hTh = N.lt_le(h, Nat.double(t), hh)
  +h1 = FR.lt_sub_pos(h, Nat.double(t), hh)
  +eg1 = N.sub_add(Nat.sub(Nat.double(t), h), 1n, h1)
  +ehg = Equal.trans(Nat, Nat.add(h, 1n+Nat.sub(Nat.sub(Nat.double(t), h), 1n)), Nat.add(h, Nat.sub(Nat.double(t), h)), Nat.double(t), Equal.cong(Nat, Nat, z => Nat.add(h, z), 1n+Nat.sub(Nat.sub(Nat.double(t), h), 1n), Nat.sub(Nat.double(t), h), eg1), N.sub_add(Nat.double(t), h, hTh))
  +hl1 = WW.lt_one(d, 1n, {==}, l, hld)
  +er = N.sub_add(C.shift(d, 1n), l, N.lt_le(l, C.shift(d, 1n), hl1))
  +hr = L.subst(Nat, z => {Nat.is_lt(Nat.sub(C.shift(d, 1n), l), z) == True{} : Bool}, Nat.add(l, Nat.sub(C.shift(d, 1n), l)), C.shift(d, 1n), er, lt_add_l(l, Nat.sub(C.shift(d, 1n), l), hl0))
  +fr = WW.fits_one(d, 1n, {==}, Nat.sub(C.shift(d, 1n), l), hr)
  +rnz = rnz_c(l, Nat.sub(C.shift(d, 1n), l), C.shift(d, 1n), er, hl1, Nat.is_eq(Nat.sub(C.shift(d, 1n), l), 0n), {==})
  +sh = C.shift(d, h)
  +sg = C.shift(d, Nat.sub(Nat.sub(Nat.double(t), h), 1n))
  +eW0 = Equal.trans(Nat, C.shift(d, Nat.double(t)), C.shift(d, Nat.add(h, 1n+Nat.sub(Nat.sub(Nat.double(t), h), 1n))), Nat.add(Nat.add(l, sh), Nat.add(Nat.sub(C.shift(d, 1n), l), sg)), Equal.cong(Nat, Nat, z => C.shift(d, z), Nat.double(t), Nat.add(h, 1n+Nat.sub(Nat.sub(Nat.double(t), h), 1n)), Equal.sym(Nat, Nat.add(h, 1n+Nat.sub(Nat.sub(Nat.double(t), h), 1n)), Nat.double(t), ehg)), Equal.trans(Nat, C.shift(d, Nat.add(h, 1n+Nat.sub(Nat.sub(Nat.double(t), h), 1n))), Nat.add(sh, C.shift(d, 1n+Nat.sub(Nat.sub(Nat.double(t), h), 1n))), Nat.add(Nat.add(l, sh), Nat.add(Nat.sub(C.shift(d, 1n), l), sg)), WW.shift_add(d, h, 1n+Nat.sub(Nat.sub(Nat.double(t), h), 1n)), Equal.trans(Nat, Nat.add(sh, C.shift(d, 1n+Nat.sub(Nat.sub(Nat.double(t), h), 1n))), Nat.add(sh, Nat.add(C.shift(d, 1n), sg)), Nat.add(Nat.add(l, sh), Nat.add(Nat.sub(C.shift(d, 1n), l), sg)), Equal.cong(Nat, Nat, z => Nat.add(sh, z), C.shift(d, 1n+Nat.sub(Nat.sub(Nat.double(t), h), 1n)), Nat.add(C.shift(d, 1n), sg), WW.shift_add(d, 1n, Nat.sub(Nat.sub(Nat.double(t), h), 1n))), Equal.trans(Nat, Nat.add(sh, Nat.add(C.shift(d, 1n), sg)), Nat.add(sh, Nat.add(Nat.add(l, Nat.sub(C.shift(d, 1n), l)), sg)), Nat.add(Nat.add(l, sh), Nat.add(Nat.sub(C.shift(d, 1n), l), sg)), Equal.cong(Nat, Nat, z => Nat.add(sh, Nat.add(z, sg)), C.shift(d, 1n), Nat.add(l, Nat.sub(C.shift(d, 1n), l)), Equal.sym(Nat, Nat.add(l, Nat.sub(C.shift(d, 1n), l)), C.shift(d, 1n), er)), Equal.trans(Nat, Nat.add(sh, Nat.add(Nat.add(l, Nat.sub(C.shift(d, 1n), l)), sg)), Nat.add(sh, Nat.add(l, Nat.add(Nat.sub(C.shift(d, 1n), l), sg))), Nat.add(Nat.add(l, sh), Nat.add(Nat.sub(C.shift(d, 1n), l), sg)), Equal.cong(Nat, Nat, z => Nat.add(sh, z), Nat.add(Nat.add(l, Nat.sub(C.shift(d, 1n), l)), sg), Nat.add(l, Nat.add(Nat.sub(C.shift(d, 1n), l), sg)), NA.add_assoc(l, Nat.sub(C.shift(d, 1n), l), sg)), Equal.trans(Nat, Nat.add(sh, Nat.add(l, Nat.add(Nat.sub(C.shift(d, 1n), l), sg))), Nat.add(Nat.add(sh, l), Nat.add(Nat.sub(C.shift(d, 1n), l), sg)), Nat.add(Nat.add(l, sh), Nat.add(Nat.sub(C.shift(d, 1n), l), sg)), Equal.sym(Nat, Nat.add(Nat.add(sh, l), Nat.add(Nat.sub(C.shift(d, 1n), l), sg)), Nat.add(sh, Nat.add(l, Nat.add(Nat.sub(C.shift(d, 1n), l), sg))), NA.add_assoc(sh, l, Nat.add(Nat.sub(C.shift(d, 1n), l), sg))), Equal.cong(Nat, Nat, z => Nat.add(z, Nat.add(Nat.sub(C.shift(d, 1n), l), sg)), Nat.add(sh, l), Nat.add(l, sh), NA.add_comm(sh, l))))))))
  +eW = Equal.trans(Nat, Nat.sub(C.shift(d, Nat.double(t)), Nat.add(l, C.shift(d, h))), Nat.sub(Nat.add(Nat.add(l, sh), Nat.add(Nat.sub(C.shift(d, 1n), l), sg)), Nat.add(l, sh)), Nat.add(Nat.sub(C.shift(d, 1n), l), sg), Equal.cong(Nat, Nat, z => Nat.sub(z, Nat.add(l, sh)), C.shift(d, Nat.double(t)), Nat.add(Nat.add(l, sh), Nat.add(Nat.sub(C.shift(d, 1n), l), sg)), eW0), N.add_sub_cancel(Nat.add(l, sh), Nat.add(Nat.sub(C.shift(d, 1n), l), sg)))
  +eH = Equal.trans(Nat, C.high(d, Nat.sub(C.shift(d, Nat.double(t)), Nat.add(l, C.shift(d, h)))), C.high(d, Nat.add(Nat.sub(C.shift(d, 1n), l), sg)), Nat.sub(Nat.sub(Nat.double(t), h), 1n), Equal.cong(Nat, Nat, z => C.high(d, z), Nat.sub(C.shift(d, Nat.double(t)), Nat.add(l, C.shift(d, h))), Nat.add(Nat.sub(C.shift(d, 1n), l), sg), eW), WW.high_u(d, Nat.sub(C.shift(d, 1n), l), Nat.sub(Nat.sub(Nat.double(t), h), 1n), fr))
  +eL = Equal.trans(Nat, C.low(d, Nat.sub(C.shift(d, Nat.double(t)), Nat.add(l, C.shift(d, h)))), C.low(d, Nat.add(Nat.sub(C.shift(d, 1n), l), sg)), Nat.sub(C.shift(d, 1n), l), Equal.cong(Nat, Nat, z => C.low(d, z), Nat.sub(C.shift(d, Nat.double(t)), Nat.add(l, C.shift(d, h))), Nat.add(Nat.sub(C.shift(d, 1n), l), sg), eW), WW.low_u(d, Nat.sub(C.shift(d, 1n), l), Nat.sub(Nat.sub(Nat.double(t), h), 1n), fr))
  +rhs = Equal.trans(Nat, SW.jam(C.high(d, Nat.sub(C.shift(d, Nat.double(t)), Nat.add(l, C.shift(d, h)))), C.low(d, Nat.sub(C.shift(d, Nat.double(t)), Nat.add(l, C.shift(d, h))))), SW.jam(Nat.sub(Nat.sub(Nat.double(t), h), 1n), C.low(d, Nat.sub(C.shift(d, Nat.double(t)), Nat.add(l, C.shift(d, h))))), 1n+Nat.double(C.half(Nat.sub(Nat.sub(Nat.double(t), h), 1n))), Equal.cong(Nat, Nat, z => SW.jam(z, C.low(d, Nat.sub(C.shift(d, Nat.double(t)), Nat.add(l, C.shift(d, h))))), C.high(d, Nat.sub(C.shift(d, Nat.double(t)), Nat.add(l, C.shift(d, h)))), Nat.sub(Nat.sub(Nat.double(t), h), 1n), eH), Equal.trans(Nat, SW.jam(Nat.sub(Nat.sub(Nat.double(t), h), 1n), C.low(d, Nat.sub(C.shift(d, Nat.double(t)), Nat.add(l, C.shift(d, h))))), SW.jam(Nat.sub(Nat.sub(Nat.double(t), h), 1n), Nat.sub(C.shift(d, 1n), l)), 1n+Nat.double(C.half(Nat.sub(Nat.sub(Nat.double(t), h), 1n))), Equal.cong(Nat, Nat, z => SW.jam(Nat.sub(Nat.sub(Nat.double(t), h), 1n), z), C.low(d, Nat.sub(C.shift(d, Nat.double(t)), Nat.add(l, C.shift(d, h)))), Nat.sub(C.shift(d, 1n), l), eL), jam_nz(Nat.sub(Nat.sub(Nat.double(t), h), 1n), Nat.sub(C.shift(d, 1n), l), rnz)))
  +ehk = WW.hb(h)
  +hdk = N.le_lt_trans(Nat.double(C.half(h)), h, Nat.double(t), L.subst(Nat, z => {Nat.is_le(Nat.double(C.half(h)), z) == True{} : Bool}, Nat.add(Nat.double(C.half(h)), C.bit(h)), h, Equal.trans(Nat, Nat.add(Nat.double(C.half(h)), C.bit(h)), Nat.add(C.bit(h), Nat.double(C.half(h))), h, NA.add_comm(Nat.double(C.half(h)), C.bit(h)), Equal.sym(Nat, h, Nat.add(C.bit(h), Nat.double(C.half(h))), ehk)), N.le_add_right(Nat.double(C.half(h)), C.bit(h))), hh)
  +hk = half_lt(C.half(h), t, hdk)
  +et = N.sub_add(t, 1n+C.half(h), N.lt_succ_le_succ(C.half(h), t, hk))
  +eT = Equal.trans(Nat, Nat.double(t), Nat.double(Nat.add(1n+C.half(h), Nat.sub(t, 1n+C.half(h)))), Nat.add(1n+Nat.double(C.half(h)), 1n+Nat.double(Nat.sub(t, 1n+C.half(h)))), Equal.cong(Nat, Nat, z => Nat.double(z), t, Nat.add(1n+C.half(h), Nat.sub(t, 1n+C.half(h))), Equal.sym(Nat, Nat.add(1n+C.half(h), Nat.sub(t, 1n+C.half(h))), t, et)), Equal.trans(Nat, Nat.double(Nat.add(1n+C.half(h), Nat.sub(t, 1n+C.half(h)))), Nat.add(2n+Nat.double(C.half(h)), Nat.double(Nat.sub(t, 1n+C.half(h)))), Nat.add(1n+Nat.double(C.half(h)), 1n+Nat.double(Nat.sub(t, 1n+C.half(h)))), NA.double_add(1n+C.half(h), Nat.sub(t, 1n+C.half(h))), Equal.cong(Nat, Nat, z => 1n+z, 1n+Nat.add(Nat.double(C.half(h)), Nat.double(Nat.sub(t, 1n+C.half(h)))), Nat.add(Nat.double(C.half(h)), 1n+Nat.double(Nat.sub(t, 1n+C.half(h)))), Equal.sym(Nat, Nat.add(Nat.double(C.half(h)), 1n+Nat.double(Nat.sub(t, 1n+C.half(h)))), 1n+Nat.add(Nat.double(C.half(h)), Nat.double(Nat.sub(t, 1n+C.half(h)))), N.add_succ(Nat.double(C.half(h)), Nat.double(Nat.sub(t, 1n+C.half(h))))))))
  +lhs = Equal.trans(Nat, Nat.sub(Nat.double(t), SW.jam(h, l)), Nat.sub(Nat.double(t), 1n+Nat.double(C.half(h))), 1n+Nat.double(Nat.sub(t, 1n+C.half(h))), Equal.cong(Nat, Nat, z => Nat.sub(Nat.double(t), z), SW.jam(h, l), 1n+Nat.double(C.half(h)), jam_nz(h, l, hl0)), Equal.trans(Nat, Nat.sub(Nat.double(t), 1n+Nat.double(C.half(h))), Nat.sub(Nat.add(1n+Nat.double(C.half(h)), 1n+Nat.double(Nat.sub(t, 1n+C.half(h)))), 1n+Nat.double(C.half(h))), 1n+Nat.double(Nat.sub(t, 1n+C.half(h))), Equal.cong(Nat, Nat, z => Nat.sub(z, 1n+Nat.double(C.half(h))), Nat.double(t), Nat.add(1n+Nat.double(C.half(h)), 1n+Nat.double(Nat.sub(t, 1n+C.half(h)))), eT), N.add_sub_cancel(1n+Nat.double(C.half(h)), 1n+Nat.double(Nat.sub(t, 1n+C.half(h))))))
  +b = C.bit(h)
  +e1 = Equal.trans(Nat, Nat.add(Nat.add(b, 1n+Nat.sub(Nat.sub(Nat.double(t), h), 1n)), Nat.double(C.half(h))), Nat.add(Nat.add(b, Nat.double(C.half(h))), 1n+Nat.sub(Nat.sub(Nat.double(t), h), 1n)), Nat.add(Nat.add(1n, 1n+Nat.double(Nat.sub(t, 1n+C.half(h)))), Nat.double(C.half(h))), A.add_rot(b, 1n+Nat.sub(Nat.sub(Nat.double(t), h), 1n), Nat.double(C.half(h))), Equal.trans(Nat, Nat.add(Nat.add(b, Nat.double(C.half(h))), 1n+Nat.sub(Nat.sub(Nat.double(t), h), 1n)), Nat.add(h, 1n+Nat.sub(Nat.sub(Nat.double(t), h), 1n)), Nat.add(Nat.add(1n, 1n+Nat.double(Nat.sub(t, 1n+C.half(h)))), Nat.double(C.half(h))), Equal.cong(Nat, Nat, z => Nat.add(z, 1n+Nat.sub(Nat.sub(Nat.double(t), h), 1n)), Nat.add(b, Nat.double(C.half(h))), h, Equal.sym(Nat, h, Nat.add(b, Nat.double(C.half(h))), ehk)), Equal.trans(Nat, Nat.add(h, 1n+Nat.sub(Nat.sub(Nat.double(t), h), 1n)), Nat.double(t), Nat.add(Nat.add(1n, 1n+Nat.double(Nat.sub(t, 1n+C.half(h)))), Nat.double(C.half(h))), ehg, Equal.trans(Nat, Nat.double(t), Nat.add(1n+Nat.double(C.half(h)), 1n+Nat.double(Nat.sub(t, 1n+C.half(h)))), Nat.add(Nat.add(1n, 1n+Nat.double(Nat.sub(t, 1n+C.half(h)))), Nat.double(C.half(h))), eT, Equal.cong(Nat, Nat, z => 1n+z, Nat.add(Nat.double(C.half(h)), 1n+Nat.double(Nat.sub(t, 1n+C.half(h)))), Nat.add(1n+Nat.double(Nat.sub(t, 1n+C.half(h))), Nat.double(C.half(h))), NA.add_comm(Nat.double(C.half(h)), 1n+Nat.double(Nat.sub(t, 1n+C.half(h)))))))))
  +e2 = A.add_cancel_r(Nat.add(b, 1n+Nat.sub(Nat.sub(Nat.double(t), h), 1n)), Nat.add(1n, 1n+Nat.double(Nat.sub(t, 1n+C.half(h)))), Nat.double(C.half(h)), e1)
  +ehalf = hg_c(Nat.sub(t, 1n+C.half(h)), Nat.sub(Nat.sub(Nat.double(t), h), 1n), b, e2, WW.bit_le1(h))
  Equal.trans(Nat, Nat.sub(Nat.double(t), SW.jam(h, l)), 1n+Nat.double(Nat.sub(t, 1n+C.half(h))), SW.jam(C.high(d, Nat.sub(C.shift(d, Nat.double(t)), Nat.add(l, C.shift(d, h)))), C.low(d, Nat.sub(C.shift(d, Nat.double(t)), Nat.add(l, C.shift(d, h))))), lhs, Equal.sym(Nat, SW.jam(C.high(d, Nat.sub(C.shift(d, Nat.double(t)), Nat.add(l, C.shift(d, h)))), C.low(d, Nat.sub(C.shift(d, Nat.double(t)), Nat.add(l, C.shift(d, h))))), 1n+Nat.double(Nat.sub(t, 1n+C.half(h))), Equal.trans(Nat, SW.jam(C.high(d, Nat.sub(C.shift(d, Nat.double(t)), Nat.add(l, C.shift(d, h)))), C.low(d, Nat.sub(C.shift(d, Nat.double(t)), Nat.add(l, C.shift(d, h))))), 1n+Nat.double(C.half(Nat.sub(Nat.sub(Nat.double(t), h), 1n))), 1n+Nat.double(Nat.sub(t, 1n+C.half(h))), rhs, Equal.cong(Nat, Nat, z => 1n+Nat.double(z), C.half(Nat.sub(Nat.sub(Nat.double(t), h), 1n)), Nat.sub(t, 1n+C.half(h)), ehalf))))
