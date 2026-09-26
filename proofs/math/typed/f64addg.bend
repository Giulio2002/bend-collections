import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/math/f64.bend as SF
import ../../../src/math/f64.bend as F
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ./width.bend as WW
import ./natcmp.bend as NC
import ./f64round.bend as FR

# Scale and significand bookkeeping for Add.value: the spec's common-scale
# operands of two finite doubles, and the order of an aligned pair.

def posz(+n: Nat, +h: {Nat.is_le(1n, n) == True{} : Bool}) -> {Nat.is_eq(n, 0n) == False{} : Bool}:
  match n:
    case 0n:
      NC.absurd_tf({Nat.is_eq(0n, 0n) == False{} : Bool}, h)
    case 1n+ +np:
      {==}

def shmk(+a: Nat, +b: Nat, +x: Nat, +h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(C.shift(a, x), C.shift(b, x)) == True{} : Bool}:
  +h0 = WW.shift_mono(a, x, C.shift(Nat.sub(b, a), x), WW.shift_ge(Nat.sub(b, a), x))
  L.subst(Nat, z => {Nat.is_le(C.shift(a, x), z) == True{} : Bool}, C.shift(a, C.shift(Nat.sub(b, a), x)), C.shift(b, x), Equal.sym(Nat, C.shift(b, x), C.shift(a, C.shift(Nat.sub(b, a), x)), NC.sh_split(b, a, x, h)), h0)

def f53(+one: Nat, +h1: {one == 1n : Nat}, +Fr: Nat, +hF: {C.fits(52n, Fr) == True{} : Bool}) -> {C.fits(53n, Nat.add(Fr, C.shift(52n, one))) == True{} : Bool}:
  WW.limbs_fit(52n, 1n, Fr, one, hF, L.subst(Nat, z => {C.fits(1n, z) == True{} : Bool}, 1n, one, Equal.sym(Nat, one, 1n, h1), {==}))

def v(+x: U32) -> Nat:
  U32.to_nat(x)

# the scale and significand of a finite double with exponent field e
def xe(+e: Nat) -> Nat:
  SF.pick(Nat, Nat.is_eq(e, 0n), Nat.sub(SF.zb(), 1074n), Nat.sub(Nat.add(e, SF.zb()), 1075n))

def mt(+e: Nat, +F: Nat) -> Nat:
  Nat.add(F, C.shift(52n, SF.b2n(Bool.not(Nat.is_eq(e, 0n)))))

def xe_z(+e: Nat, +hz: {Nat.is_eq(e, 0n) == True{} : Bool}) -> {xe(e) == 1926n : Nat}:
  Equal.cong(Bool, Nat, t => SF.pick(Nat, t, Nat.sub(SF.zb(), 1074n), Nat.sub(Nat.add(e, SF.zb()), 1075n)), Nat.is_eq(e, 0n), True{}, hz)

def xe_n(+e: Nat, +hz: {Nat.is_eq(e, 0n) == False{} : Bool}) -> {xe(e) == Nat.add(1925n, e) : Nat}:
  +e1 = Equal.cong(Bool, Nat, t => SF.pick(Nat, t, Nat.sub(SF.zb(), 1074n), Nat.sub(Nat.add(e, SF.zb()), 1075n)), Nat.is_eq(e, 0n), False{}, hz)
  +e2 = Equal.cong(Nat, Nat, z => Nat.sub(z, 1075n), Nat.add(e, 3000n), Nat.add(3000n, e), NA.add_comm(e, 3000n))
  Equal.trans(Nat, xe(e), Nat.sub(Nat.add(e, 3000n), 1075n), Nat.add(1925n, e), e1, Equal.trans(Nat, Nat.sub(Nat.add(e, 3000n), 1075n), Nat.sub(Nat.add(3000n, e), 1075n), Nat.add(1925n, e), e2, FR.sub_add_r(3000n, e, 1075n, {==})))

def mt_z(+e: Nat, +F: Nat, +hz: {Nat.is_eq(e, 0n) == True{} : Bool}) -> {mt(e, F) == F : Nat}:
  Equal.trans(Nat, mt(e, F), Nat.add(F, 0n), F, Equal.cong(Bool, Nat, t => Nat.add(F, C.shift(52n, SF.b2n(Bool.not(t)))), Nat.is_eq(e, 0n), True{}, hz), N.add_zero(F))

def mt_n(+one: Nat, +h1: {one == 1n : Nat}, +e: Nat, +F: Nat, +hz: {Nat.is_eq(e, 0n) == False{} : Bool}) -> {mt(e, F) == Nat.add(F, C.shift(52n, one)) : Nat}:
  +ec = Equal.trans(Nat, SF.b2n(Bool.not(Nat.is_eq(e, 0n))), 1n, one, Equal.cong(Bool, Nat, t => SF.b2n(Bool.not(t)), Nat.is_eq(e, 0n), False{}, hz), Equal.sym(Nat, one, 1n, h1))
  Equal.cong(Nat, Nat, z => Nat.add(F, C.shift(52n, z)), SF.b2n(Bool.not(Nat.is_eq(e, 0n))), one, ec)

def min_l(+a: Nat, +b: Nat, +h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.min(a, b) == a : Nat}:
  match a b:
    case 0n _:
      {==}
    case 1n+ +ap 0n:
      NC.absurd_tf({Nat.min(1n+ap, 0n) == 1n+ap : Nat}, h)
    case 1n+ +ap 1n+ +bp:
      N.succ_cong(Nat.min(ap, bp), ap, min_l(ap, bp, h))

def min_r(+a: Nat, +b: Nat, +h: {Nat.is_le(b, a) == True{} : Bool}) -> {Nat.min(a, b) == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+ +bp:
      NC.absurd_tf({Nat.min(0n, 1n+bp) == 1n+bp : Nat}, h)
    case 1n+ +ap 0n:
      {==}
    case 1n+ +ap 1n+ +bp:
      N.succ_cong(Nat.min(ap, bp), bp, min_r(ap, bp, h))

def sub_kk(+k: Nat, +a: Nat, +b: Nat) -> {Nat.sub(Nat.add(k, a), Nat.add(k, b)) == Nat.sub(a, b) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+ +kp:
      sub_kk(kp, a, b)

def sub_le(+a: Nat, +b: Nat) -> {Nat.is_le(Nat.sub(a, b), a) == True{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+ +bp:
      {==}
    case 1n+ +ap 0n:
      N.le_refl(1n+ap)
    case 1n+ +ap 1n+ +bp:
      N.le_trans(Nat.sub(ap, bp), ap, 1n+ap, sub_le(ap, bp), N.le_succ(ap))

def pred_eq(+n: Nat, +hz: {Nat.is_eq(n, 0n) == False{} : Bool}) -> {1n+N.pred(n) == n : Nat}:
  match n:
    case 0n:
      NC.absurd_tf({1n+N.pred(0n) == 0n : Nat}, Equal.sym(Bool, True{}, False{}, hz))
    case 1n+ +np:
      {==}

# the sign of a difference of opposite signs
def sgn(+sa: Bool, +sb: Bool, +h: {Bool.not(Bool.xor(sa, sb)) == False{} : Bool}) -> {Bool.not(sa) == sb : Bool}:
  match sa sb:
    case True{} True{}:
      NC.absurd_tf({False{} == True{} : Bool}, Equal.sym(Bool, True{}, False{}, h))
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      NC.absurd_tf({True{} == False{} : Bool}, Equal.sym(Bool, True{}, False{}, h))

def zero_v(+s: Bool) -> {F.zero(s) == SF.zero(s) : F.F64}:
  match s:
    case True{}:
      {==}
    case False{}:
      {==}

def rca(+s: Bool, +a: Nat, +a2: Nat, +ha: {a == a2 : Nat}, +k: Nat, +k2: Nat, +hk: {k == k2 : Nat}, +m: Nat, +m2: Nat, +hm: {m == m2 : Nat}, +x: Nat, +x2: Nat, +hx: {x == x2 : Nat}) -> {SF.round(s, Nat.add(a, C.shift(k, m)), x) == SF.round(s, Nat.add(a2, C.shift(k2, m2)), x2) : F.F64}:
  +e1 = L.subst(Nat, z => {SF.round(s, Nat.add(a, C.shift(k, m)), x) == SF.round(s, Nat.add(z, C.shift(k, m)), x) : F.F64}, a, a2, ha, {==})
  +e2 = L.subst(Nat, z => {SF.round(s, Nat.add(a, C.shift(k, m)), x) == SF.round(s, Nat.add(a2, C.shift(z, m)), x) : F.F64}, k, k2, hk, e1)
  +e3 = L.subst(Nat, z => {SF.round(s, Nat.add(a, C.shift(k, m)), x) == SF.round(s, Nat.add(a2, C.shift(k2, z)), x) : F.F64}, m, m2, hm, e2)
  L.subst(Nat, z => {SF.round(s, Nat.add(a, C.shift(k, m)), x) == SF.round(s, Nat.add(a2, C.shift(k2, m2)), z) : F.F64}, x, x2, hx, e3)

def rcs(+s: Bool, +a: Nat, +a2: Nat, +ha: {a == a2 : Nat}, +k: Nat, +k2: Nat, +hk: {k == k2 : Nat}, +m: Nat, +m2: Nat, +hm: {m == m2 : Nat}, +x: Nat, +x2: Nat, +hx: {x == x2 : Nat}) -> {SF.round(s, Nat.sub(C.shift(k, m), a), x) == SF.round(s, Nat.sub(C.shift(k2, m2), a2), x2) : F.F64}:
  +e1 = L.subst(Nat, z => {SF.round(s, Nat.sub(C.shift(k, m), a), x) == SF.round(s, Nat.sub(C.shift(k, m), z), x) : F.F64}, a, a2, ha, {==})
  +e2 = L.subst(Nat, z => {SF.round(s, Nat.sub(C.shift(k, m), a), x) == SF.round(s, Nat.sub(C.shift(z, m), a2), x) : F.F64}, k, k2, hk, e1)
  +e3 = L.subst(Nat, z => {SF.round(s, Nat.sub(C.shift(k, m), a), x) == SF.round(s, Nat.sub(C.shift(k2, z), a2), x) : F.F64}, m, m2, hm, e2)
  L.subst(Nat, z => {SF.round(s, Nat.sub(C.shift(k, m), a), x) == SF.round(s, Nat.sub(C.shift(k2, m2), a2), z) : F.F64}, x, x2, hx, e3)

def bigcmp_c(+one: Nat, +h1: {one == 1n : Nat}, +el: Nat, +es: Nat, +Fl: Nat, +Fs: Nat, +hFl: {C.fits(52n, Fl) == True{} : Bool}, +hFs: {C.fits(52n, Fs) == True{} : Bool}, +hlt: {Nat.is_lt(es, el) == True{} : Bool}, +z: Bool, +hz: {Nat.is_eq(es, 0n) == z : Bool}) -> {Nat.is_lt(mt(es, Fs), C.shift(Nat.sub(xe(el), xe(es)), mt(el, Fl))) == True{} : Bool}:
  match z:
    case True{}:
      +hl1 = N.lt_succ_le_succ(es, el, hlt)
      +hel = posz(el, N.le_trans(1n, 1n+es, el, N.zero_le(es), hl1))
      +ml = mt_n(one, h1, el, Fl, hel)
      +hPl = L.subst(Nat, w => {Nat.is_le(C.shift(52n, one), w) == True{} : Bool}, Nat.add(C.shift(52n, one), Fl), Nat.add(Fl, C.shift(52n, one)), NA.add_comm(C.shift(52n, one), Fl), N.le_add_right(C.shift(52n, one), Fl))
      +hPm = L.subst(Nat, w => {Nat.is_le(C.shift(52n, one), w) == True{} : Bool}, Nat.add(Fl, C.shift(52n, one)), mt(el, Fl), Equal.sym(Nat, mt(el, Fl), Nat.add(Fl, C.shift(52n, one)), ml), hPl)
      +ms = mt_z(es, Fs, hz)
      +l0 = Equal.trans(Bool, Nat.is_lt(Fs, C.shift(52n, one)), C.fits(52n, Fs), True{}, FR.lt_fit(52n, one, h1, Fs), hFs)
      +l1 = N.lt_le_trans(Fs, C.shift(52n, one), C.shift(Nat.sub(xe(el), xe(es)), mt(el, Fl)), l0, N.le_trans(C.shift(52n, one), mt(el, Fl), C.shift(Nat.sub(xe(el), xe(es)), mt(el, Fl)), hPm, WW.shift_ge(Nat.sub(xe(el), xe(es)), mt(el, Fl))))
      L.subst(Nat, w => {Nat.is_lt(w, C.shift(Nat.sub(xe(el), xe(es)), mt(el, Fl))) == True{} : Bool}, Fs, mt(es, Fs), Equal.sym(Nat, mt(es, Fs), Fs, ms), l1)
    case False{}:
      +hl1 = N.lt_succ_le_succ(es, el, hlt)
      +hel = posz(el, N.le_trans(1n, 1n+es, el, N.zero_le(es), hl1))
      +ml = mt_n(one, h1, el, Fl, hel)
      +hPl = L.subst(Nat, w => {Nat.is_le(C.shift(52n, one), w) == True{} : Bool}, Nat.add(C.shift(52n, one), Fl), Nat.add(Fl, C.shift(52n, one)), NA.add_comm(C.shift(52n, one), Fl), N.le_add_right(C.shift(52n, one), Fl))
      +hPm = L.subst(Nat, w => {Nat.is_le(C.shift(52n, one), w) == True{} : Bool}, Nat.add(Fl, C.shift(52n, one)), mt(el, Fl), Equal.sym(Nat, mt(el, Fl), Nat.add(Fl, C.shift(52n, one)), ml), hPl)
      +ms = mt_n(one, h1, es, Fs, hz)
      +xs = xe_n(es, hz)
      +xl = xe_n(el, hel)
      +ed = Equal.trans(Nat, Nat.sub(xe(el), xe(es)), Nat.sub(Nat.add(1925n, el), Nat.add(1925n, es)), Nat.sub(el, es), Equal.trans(Nat, Nat.sub(xe(el), xe(es)), Nat.sub(Nat.add(1925n, el), xe(es)), Nat.sub(Nat.add(1925n, el), Nat.add(1925n, es)), Equal.cong(Nat, Nat, w => Nat.sub(w, xe(es)), xe(el), Nat.add(1925n, el), xl), Equal.cong(Nat, Nat, w => Nat.sub(Nat.add(1925n, el), w), xe(es), Nat.add(1925n, es), xs)), sub_kk(1925n, el, es))
      +hd = L.subst(Nat, w => {Nat.is_le(1n, w) == True{} : Bool}, Nat.sub(el, es), Nat.sub(xe(el), xe(es)), Equal.sym(Nat, Nat.sub(xe(el), xe(es)), Nat.sub(el, es), ed), FR.lt_sub_pos(es, el, hlt))
      +l0 = Equal.trans(Bool, Nat.is_lt(Nat.add(Fs, C.shift(52n, one)), C.shift(53n, one)), C.fits(53n, Nat.add(Fs, C.shift(52n, one))), True{}, FR.lt_fit(53n, one, h1, Nat.add(Fs, C.shift(52n, one))), f53(one, h1, Fs, hFs))
      +l2 = N.le_trans(C.shift(1n, C.shift(52n, one)), C.shift(1n, mt(el, Fl)), C.shift(Nat.sub(xe(el), xe(es)), mt(el, Fl)), WW.shift_mono(1n, C.shift(52n, one), mt(el, Fl), hPm), shmk(1n, Nat.sub(xe(el), xe(es)), mt(el, Fl), hd))
      +l1 = N.lt_le_trans(Nat.add(Fs, C.shift(52n, one)), C.shift(53n, one), C.shift(Nat.sub(xe(el), xe(es)), mt(el, Fl)), l0, l2)
      L.subst(Nat, w => {Nat.is_lt(w, C.shift(Nat.sub(xe(el), xe(es)), mt(el, Fl))) == True{} : Bool}, Nat.add(Fs, C.shift(52n, one)), mt(es, Fs), Equal.sym(Nat, mt(es, Fs), Nat.add(Fs, C.shift(52n, one)), ms), l1)

def bigcmp(+one: Nat, +h1: {one == 1n : Nat}, +el: Nat, +es: Nat, +Fl: Nat, +Fs: Nat, +hFl: {C.fits(52n, Fl) == True{} : Bool}, +hFs: {C.fits(52n, Fs) == True{} : Bool}, +hlt: {Nat.is_lt(es, el) == True{} : Bool}) -> {Nat.cmp(mt(es, Fs), C.shift(Nat.sub(xe(el), xe(es)), mt(el, Fl))) == LT{} : Cmp}:
  NC.cmp_lt(mt(es, Fs), C.shift(Nat.sub(xe(el), xe(es)), mt(el, Fl)), bigcmp_c(one, h1, el, es, Fl, Fs, hFl, hFs, hlt, Nat.is_eq(es, 0n), {==}))

