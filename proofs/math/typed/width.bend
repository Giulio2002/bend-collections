import Base
import ../../../spec/lib/common.bend as C
import ../../lib/nat.bend as N
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../../lib/logic.bend as L
import ../natural/arith.bend as NR

# The width vocabulary of spec/lib/common.bend (shift, high, low, fits: k
# doublings or halvings, never a literal 2^k) against the powers of two, for
# a symbolic k. The shape is Mathlib's Nat.shiftLeft_eq / Nat.shiftRight_eq_div_pow
# / Nat.lt_pow_two_of_testBit (Mathlib.Data.Nat.Bits): a shift is a
# multiplication or division by 2^k.

# half(n) < m exactly when n < 2m
def lt_half(+n: Nat, +m: Nat) -> {Nat.is_lt(C.half(n), m) == Nat.is_lt(n, Nat.double(m)) : Bool}:
  match n m:
    case 0n 0n:
      {==}
    case 0n 1n+mp:
      {==}
    case 1n 0n:
      {==}
    case 1n 1n+mp:
      {==}
    case 2n+ +q 0n:
      {==}
    case 2n+ +q 1n+ +mp:
      lt_half(q, mp)

# fits(k, n) is n < 2^k
def fits_lt(+k: Nat, +n: Nat) -> {C.fits(k, n) == Nat.is_lt(n, C.pow2(k)) : Bool}:
  match k:
    case 0n:
      match n:
        case 0n:
          {==}
        case 1n+ +np:
          Equal.sym(Bool, Nat.is_lt(np, 0n), False{}, N.not_lt_zero(np))
    case 1n+ +p:
      %Equal.sym(Bool, C.fits(p, C.half(n)), Nat.is_lt(C.half(n), C.pow2(p)), fits_lt(p, C.half(n))) : {_ == Nat.is_lt(n, Nat.double(C.pow2(p))) : Bool}
      lt_half(n, C.pow2(p))

# ---- n == bit(n) + 2 half(n), and the halves of r + 2 x ----

def hb(+n: Nat) -> {n == Nat.add(C.bit(n), Nat.double(C.half(n))) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n+ +q:
      +e = hb(q)
      Equal.trans(Nat, 2n+q, 2n+Nat.add(C.bit(q), Nat.double(C.half(q))), Nat.add(C.bit(q), 2n+Nat.double(C.half(q))), Equal.cong(Nat, Nat, t => 2n+t, q, Nat.add(C.bit(q), Nat.double(C.half(q))), e), Equal.sym(Nat, Nat.add(C.bit(q), 2n+Nat.double(C.half(q))), 2n+Nat.add(C.bit(q), Nat.double(C.half(q))), Equal.trans(Nat, Nat.add(C.bit(q), 2n+Nat.double(C.half(q))), 1n+Nat.add(C.bit(q), 1n+Nat.double(C.half(q))), 2n+Nat.add(C.bit(q), Nat.double(C.half(q))), NA.add_succ(C.bit(q), 1n+Nat.double(C.half(q))), Equal.cong(Nat, Nat, t => 1n+t, Nat.add(C.bit(q), 1n+Nat.double(C.half(q))), 1n+Nat.add(C.bit(q), Nat.double(C.half(q))), NA.add_succ(C.bit(q), Nat.double(C.half(q)))))))

def half_dbl(+r: Nat, +x: Nat) -> {C.half(Nat.add(r, Nat.double(x))) == Nat.add(C.half(r), x) : Nat}:
  match r:
    case 0n:
      match x:
        case 0n:
          {==}
        case 1n+ +y:
          Equal.cong(Nat, Nat, t => 1n+t, C.half(Nat.double(y)), y, half_dbl(0n, y))
    case 1n:
      match x:
        case 0n:
          {==}
        case 1n+ +y:
          Equal.cong(Nat, Nat, t => 1n+t, C.half(1n+Nat.double(y)), y, half_dbl(1n, y))
    case 2n+ +s:
      Equal.cong(Nat, Nat, t => 1n+t, C.half(Nat.add(s, Nat.double(x))), Nat.add(C.half(s), x), half_dbl(s, x))

def bit_dbl(+r: Nat, +x: Nat) -> {C.bit(Nat.add(r, Nat.double(x))) == C.bit(r) : Nat}:
  match r:
    case 0n:
      match x:
        case 0n:
          {==}
        case 1n+ +y:
          bit_dbl(0n, y)
    case 1n:
      match x:
        case 0n:
          {==}
        case 1n+ +y:
          bit_dbl(1n, y)
    case 2n+ +s:
      bit_dbl(s, x)

# ---- n == low(k, n) + shift(k, high(k, n)), low(k, n) < 2^k, and uniqueness ----

def low_high(+k: Nat, +n: Nat) -> {n == Nat.add(C.low(k, n), C.shift(k, C.high(k, n))) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+ +p:
      +h = C.half(n)
      +l = C.low(p, h)
      +s = C.shift(p, C.high(p, h))
      +e1 = Equal.trans(Nat, n, Nat.add(C.bit(n), Nat.double(h)), Nat.add(C.bit(n), Nat.double(Nat.add(l, s))), hb(n), Equal.cong(Nat, Nat, t => Nat.add(C.bit(n), Nat.double(t)), h, Nat.add(l, s), low_high(p, h)))
      +e2 = Equal.trans(Nat, Nat.add(C.bit(n), Nat.double(Nat.add(l, s))), Nat.add(C.bit(n), Nat.add(Nat.double(l), Nat.double(s))), Nat.add(Nat.add(C.bit(n), Nat.double(l)), Nat.double(s)), Equal.cong(Nat, Nat, t => Nat.add(C.bit(n), t), Nat.double(Nat.add(l, s)), Nat.add(Nat.double(l), Nat.double(s)), NA.double_add(l, s)), Equal.sym(Nat, Nat.add(Nat.add(C.bit(n), Nat.double(l)), Nat.double(s)), Nat.add(C.bit(n), Nat.add(Nat.double(l), Nat.double(s))), NA.add_assoc(C.bit(n), Nat.double(l), Nat.double(s))))
      Equal.trans(Nat, n, Nat.add(C.bit(n), Nat.double(Nat.add(l, s))), Nat.add(Nat.add(C.bit(n), Nat.double(l)), Nat.double(s)), e1, e2)

def bit_le1(+n: Nat) -> {Nat.is_le(C.bit(n), 1n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n+ +q:
      bit_le1(q)

def le_add_r(+a: Nat, +b: Nat, +c: Nat, +h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(Nat.add(a, c), Nat.add(b, c)) == True{} : Bool}:
  +h1 = L.subst(Nat, z => {Nat.is_le(z, Nat.add(c, b)) == True{} : Bool}, Nat.add(c, a), Nat.add(a, c), N.add_comm(c, a), N.le_add_left(a, b, c, h))
  L.subst(Nat, z => {Nat.is_le(Nat.add(a, c), z) == True{} : Bool}, Nat.add(c, b), Nat.add(b, c), N.add_comm(c, b), h1)

def low_lt(+k: Nat, +n: Nat) -> {Nat.is_lt(C.low(k, n), C.pow2(k)) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+ +p:
      +l = C.low(p, C.half(n))
      +ih = low_lt(p, C.half(n))
      +b = C.bit(n)
      +hb1 = bit_le1(n)
      +h2 = N.lt_succ_le_succ(l, C.pow2(p), ih)
      +h3 = N.double_le(1n+l, C.pow2(p), h2)
      +h4 = L.subst(Nat, z => {Nat.is_le(z, Nat.double(C.pow2(p))) == True{} : Bool}, Nat.double(1n+l), Nat.add(2n, Nat.double(l)), N.double_succ(l), h3)
      +h5 = N.le_lt_trans(Nat.add(b, Nat.double(l)), Nat.add(1n, Nat.double(l)), Nat.add(2n, Nat.double(l)), le_add_r(b, 1n, Nat.double(l), hb1), N.lt_succ(1n+Nat.double(l)))
      N.lt_le_trans(Nat.add(b, Nat.double(l)), Nat.add(2n, Nat.double(l)), Nat.double(C.pow2(p)), h5, h4)

# r < 2^k: low(k, r + shift(k, q)) == r and high(k, r + shift(k, q)) == q
def low_uniq(+k: Nat, +r: Nat, +q: Nat, +hr: {Nat.is_lt(r, C.pow2(k)) == True{} : Bool}) -> {C.low(k, Nat.add(r, C.shift(k, q))) == r : Nat}:
  match k:
    case 0n:
      match r:
        case 0n:
          {==}
        case 1n+ +rp:
          Empty.absurd({C.low(0n, Nat.add(1n+rp, C.shift(0n, q))) == 1n+rp : Nat}, N.lt_zero_absurd(rp, hr))
    case 1n+ +p:
      +eh = half_dbl(r, C.shift(p, q))
      +eb = bit_dbl(r, C.shift(p, q))
      +hr2 = Equal.trans(Bool, Nat.is_lt(C.half(r), C.pow2(p)), Nat.is_lt(r, Nat.double(C.pow2(p))), True{}, lt_half(r, C.pow2(p)), hr)
      +ih = low_uniq(p, C.half(r), q, hr2)
      +el = Equal.trans(Nat, C.low(p, C.half(Nat.add(r, Nat.double(C.shift(p, q))))), C.low(p, Nat.add(C.half(r), C.shift(p, q))), C.half(r), Equal.cong(Nat, Nat, t => C.low(p, t), C.half(Nat.add(r, Nat.double(C.shift(p, q)))), Nat.add(C.half(r), C.shift(p, q)), eh), ih)
      Equal.trans(Nat, Nat.add(C.bit(Nat.add(r, Nat.double(C.shift(p, q)))), Nat.double(C.low(p, C.half(Nat.add(r, Nat.double(C.shift(p, q))))))), Nat.add(C.bit(r), Nat.double(C.half(r))), r, Equal.trans(Nat, Nat.add(C.bit(Nat.add(r, Nat.double(C.shift(p, q)))), Nat.double(C.low(p, C.half(Nat.add(r, Nat.double(C.shift(p, q))))))), Nat.add(C.bit(r), Nat.double(C.low(p, C.half(Nat.add(r, Nat.double(C.shift(p, q))))))), Nat.add(C.bit(r), Nat.double(C.half(r))), Equal.cong(Nat, Nat, t => Nat.add(t, Nat.double(C.low(p, C.half(Nat.add(r, Nat.double(C.shift(p, q))))))), C.bit(Nat.add(r, Nat.double(C.shift(p, q)))), C.bit(r), eb), Equal.cong(Nat, Nat, t => Nat.add(C.bit(r), Nat.double(t)), C.low(p, C.half(Nat.add(r, Nat.double(C.shift(p, q))))), C.half(r), el)), Equal.sym(Nat, r, Nat.add(C.bit(r), Nat.double(C.half(r))), hb(r)))

def high_uniq(+k: Nat, +r: Nat, +q: Nat, +hr: {Nat.is_lt(r, C.pow2(k)) == True{} : Bool}) -> {C.high(k, Nat.add(r, C.shift(k, q))) == q : Nat}:
  match k:
    case 0n:
      match r:
        case 0n:
          {==}
        case 1n+ +rp:
          Empty.absurd({C.high(0n, Nat.add(1n+rp, C.shift(0n, q))) == q : Nat}, N.lt_zero_absurd(rp, hr))
    case 1n+ +p:
      +eh = half_dbl(r, C.shift(p, q))
      +hr2 = Equal.trans(Bool, Nat.is_lt(C.half(r), C.pow2(p)), Nat.is_lt(r, Nat.double(C.pow2(p))), True{}, lt_half(r, C.pow2(p)), hr)
      Equal.trans(Nat, C.high(p, C.half(Nat.add(r, Nat.double(C.shift(p, q))))), C.high(p, Nat.add(C.half(r), C.shift(p, q))), q, Equal.cong(Nat, Nat, t => C.high(p, t), C.half(Nat.add(r, Nat.double(C.shift(p, q)))), Nat.add(C.half(r), C.shift(p, q)), eh), high_uniq(p, C.half(r), q, hr2))

# ---- shift(k, x) is x 2^k ----

def shift_zero(+k: Nat) -> {C.shift(k, 0n) == 0n : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+ +p:
      Equal.cong(Nat, Nat, t => Nat.double(t), C.shift(p, 0n), 0n, shift_zero(p))

def shift_add(+k: Nat, +x: Nat, +y: Nat) -> {C.shift(k, Nat.add(x, y)) == Nat.add(C.shift(k, x), C.shift(k, y)) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+ +p:
      Equal.trans(Nat, Nat.double(C.shift(p, Nat.add(x, y))), Nat.double(Nat.add(C.shift(p, x), C.shift(p, y))), Nat.add(Nat.double(C.shift(p, x)), Nat.double(C.shift(p, y))), Equal.cong(Nat, Nat, t => Nat.double(t), C.shift(p, Nat.add(x, y)), Nat.add(C.shift(p, x), C.shift(p, y)), shift_add(p, x, y)), NA.double_add(C.shift(p, x), C.shift(p, y)))

def shift_one(+k: Nat) -> {C.shift(k, 1n) == C.pow2(k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+ +p:
      Equal.cong(Nat, Nat, t => Nat.double(t), C.shift(p, 1n), C.pow2(p), shift_one(p))

def shift_comp(+a: Nat, +b: Nat, +x: Nat) -> {C.shift(Nat.add(a, b), x) == C.shift(a, C.shift(b, x)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+ +p:
      Equal.cong(Nat, Nat, t => Nat.double(t), C.shift(Nat.add(p, b), x), C.shift(p, C.shift(b, x)), shift_comp(p, b, x))

def shift_mono(+k: Nat, +x: Nat, +y: Nat, +h: {Nat.is_le(x, y) == True{} : Bool}) -> {Nat.is_le(C.shift(k, x), C.shift(k, y)) == True{} : Bool}:
  match k:
    case 0n:
      h
    case 1n+ +p:
      N.double_le(C.shift(p, x), C.shift(p, y), shift_mono(p, x, y, h))

# shift(a, 2^b) == 2^(a + b)
def shift_pow2(+a: Nat, +b: Nat) -> {C.shift(a, C.pow2(b)) == C.pow2(Nat.add(a, b)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+ +p:
      Equal.cong(Nat, Nat, t => Nat.double(t), C.shift(p, C.pow2(b)), C.pow2(Nat.add(p, b)), shift_pow2(p, b))

# r < 2^k, x < 2^j: r + shift(k, x) < 2^(k + j)
def two_limb_lt(+k: Nat, +j: Nat, +r: Nat, +x: Nat, +hr: {Nat.is_lt(r, C.pow2(k)) == True{} : Bool}, +hx: {Nat.is_lt(x, C.pow2(j)) == True{} : Bool}) -> {Nat.is_lt(Nat.add(r, C.shift(k, x)), C.pow2(Nat.add(k, j))) == True{} : Bool}:
  +h1 = N.lt_add_r2(r, C.pow2(k), C.shift(k, x), hr)
  +e1 = Equal.trans(Nat, Nat.add(C.pow2(k), C.shift(k, x)), Nat.add(C.shift(k, 1n), C.shift(k, x)), C.shift(k, 1n+x), Equal.cong(Nat, Nat, t => Nat.add(t, C.shift(k, x)), C.pow2(k), C.shift(k, 1n), Equal.sym(Nat, C.shift(k, 1n), C.pow2(k), shift_one(k))), Equal.sym(Nat, C.shift(k, Nat.add(1n, x)), Nat.add(C.shift(k, 1n), C.shift(k, x)), shift_add(k, 1n, x)))
  +h2 = L.subst(Nat, z => {Nat.is_lt(Nat.add(r, C.shift(k, x)), z) == True{} : Bool}, Nat.add(C.pow2(k), C.shift(k, x)), C.shift(k, 1n+x), e1, h1)
  +h3 = shift_mono(k, 1n+x, C.pow2(j), N.lt_succ_le_succ(x, C.pow2(j), hx))
  N.lt_le_trans(Nat.add(r, C.shift(k, x)), C.shift(k, 1n+x), C.pow2(Nat.add(k, j)), h2, L.subst(Nat, z => {Nat.is_le(C.shift(k, 1n+x), z) == True{} : Bool}, C.shift(k, C.pow2(j)), C.pow2(Nat.add(k, j)), shift_pow2(k, j), h3))

# ---- the same in fits form (no pow2 in the statement, safe at k == 64) ----

def lt_of_fits(+k: Nat, +r: Nat, +h: {C.fits(k, r) == True{} : Bool}) -> {Nat.is_lt(r, C.pow2(k)) == True{} : Bool}:
  Equal.trans(Bool, Nat.is_lt(r, C.pow2(k)), C.fits(k, r), True{}, Equal.sym(Bool, C.fits(k, r), Nat.is_lt(r, C.pow2(k)), fits_lt(k, r)), h)

def fits_of_lt(+k: Nat, +r: Nat, +h: {Nat.is_lt(r, C.pow2(k)) == True{} : Bool}) -> {C.fits(k, r) == True{} : Bool}:
  Equal.trans(Bool, C.fits(k, r), Nat.is_lt(r, C.pow2(k)), True{}, fits_lt(k, r), h)

def low_u(+k: Nat, +r: Nat, +q: Nat, +hr: {C.fits(k, r) == True{} : Bool}) -> {C.low(k, Nat.add(r, C.shift(k, q))) == r : Nat}:
  low_uniq(k, r, q, lt_of_fits(k, r, hr))

def high_u(+k: Nat, +r: Nat, +q: Nat, +hr: {C.fits(k, r) == True{} : Bool}) -> {C.high(k, Nat.add(r, C.shift(k, q))) == q : Nat}:
  high_uniq(k, r, q, lt_of_fits(k, r, hr))

def low_fits(+k: Nat, +n: Nat) -> {C.fits(k, C.low(k, n)) == True{} : Bool}:
  fits_of_lt(k, C.low(k, n), low_lt(k, n))

# r fits k bits, x fits j bits: r + shift(k, x) fits k + j bits
def limbs_fit(+k: Nat, +j: Nat, +r: Nat, +x: Nat, +hr: {C.fits(k, r) == True{} : Bool}, +hx: {C.fits(j, x) == True{} : Bool}) -> {C.fits(Nat.add(k, j), Nat.add(r, C.shift(k, x))) == True{} : Bool}:
  fits_of_lt(Nat.add(k, j), Nat.add(r, C.shift(k, x)), two_limb_lt(k, j, r, x, lt_of_fits(k, r, hr), lt_of_fits(j, x, hx)))

# shift(k, q) with q >= 1 does not fit k bits added to anything
def unfit_shift(+k: Nat, +r: Nat, +qp: Nat) -> {C.fits(k, Nat.add(r, C.shift(k, 1n+qp))) == False{} : Bool}:
  +h1 = N.le_trans(C.pow2(k), C.shift(k, 1n+qp), Nat.add(r, C.shift(k, 1n+qp)), L.subst(Nat, z => {Nat.is_le(z, C.shift(k, 1n+qp)) == True{} : Bool}, C.shift(k, 1n), C.pow2(k), shift_one(k), shift_mono(k, 1n, 1n+qp, N.zero_le(qp))), L.subst(Nat, z => {Nat.is_le(C.shift(k, 1n+qp), z) == True{} : Bool}, Nat.add(C.shift(k, 1n+qp), r), Nat.add(r, C.shift(k, 1n+qp)), N.add_comm(C.shift(k, 1n+qp), r), N.le_add_right(C.shift(k, 1n+qp), r)))
  Equal.trans(Bool, C.fits(k, Nat.add(r, C.shift(k, 1n+qp))), Nat.is_lt(Nat.add(r, C.shift(k, 1n+qp)), C.pow2(k)), False{}, fits_lt(k, Nat.add(r, C.shift(k, 1n+qp))), N.le_not_lt(Nat.add(r, C.shift(k, 1n+qp)), C.pow2(k), h1))

def shift_ge(+k: Nat, +x: Nat) -> {Nat.is_le(x, C.shift(k, x)) == True{} : Bool}:
  match k:
    case 0n:
      N.le_refl(x)
    case 1n+ +p:
      N.le_trans(x, C.shift(p, x), Nat.double(C.shift(p, x)), shift_ge(p, x), N.double_self_le(C.shift(p, x)))

# with a symbolic one == 1 (so no closed 2^k appears where these are used)
def unfit_one(+k: Nat, +one: Nat, +h1: {one == 1n : Nat}, +r: Nat) -> {C.fits(k, Nat.add(r, C.shift(k, one))) == False{} : Bool}:
  L.subst(Nat, z => {C.fits(k, Nat.add(r, C.shift(k, z))) == False{} : Bool}, 1n, one, Equal.sym(Nat, one, 1n, h1), unfit_shift(k, r, 0n))

def lt_one(+k: Nat, +one: Nat, +h1: {one == 1n : Nat}, +x: Nat, +h: {C.fits(k, x) == True{} : Bool}) -> {Nat.is_lt(x, C.shift(k, one)) == True{} : Bool}:
  +h2 = L.subst(Nat, z => {Nat.is_lt(x, z) == True{} : Bool}, C.pow2(k), C.shift(k, 1n), Equal.sym(Nat, C.shift(k, 1n), C.pow2(k), shift_one(k)), lt_of_fits(k, x, h))
  L.subst(Nat, z => {Nat.is_lt(x, C.shift(k, z)) == True{} : Bool}, 1n, one, Equal.sym(Nat, one, 1n, h1), h2)

def dbl_eq0(+z: Nat) -> {Nat.is_eq(Nat.double(z), 0n) == Nat.is_eq(z, 0n) : Bool}:
  match z:
    case 0n:
      {==}
    case 1n+ +w:
      L.subst(Nat, t => {Nat.is_eq(t, 0n) == False{} : Bool}, Nat.add(2n, Nat.double(w)), Nat.double(1n+w), Equal.sym(Nat, Nat.double(1n+w), Nat.add(2n, Nat.double(w)), N.double_succ(w)), {==})

def shift_eq0(+k: Nat, +y: Nat) -> {Nat.is_eq(C.shift(k, y), 0n) == Nat.is_eq(y, 0n) : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+ +p:
      Equal.trans(Bool, Nat.is_eq(Nat.double(C.shift(p, y)), 0n), Nat.is_eq(C.shift(p, y), 0n), Nat.is_eq(y, 0n), dbl_eq0(C.shift(p, y)), shift_eq0(p, y))

# ---- comparing two-limb numbers x + shift(k, y), x fitting k bits ----

def lt_cancel_l(+d: Nat, +x: Nat, +y: Nat) -> {Nat.is_lt(Nat.add(d, x), Nat.add(d, y)) == Nat.is_lt(x, y) : Bool}:
  match d:
    case 0n:
      {==}
    case 1n+ +e:
      lt_cancel_l(e, x, y)

def lt_cancel_r(+x: Nat, +y: Nat, +s: Nat) -> {Nat.is_lt(Nat.add(x, s), Nat.add(y, s)) == Nat.is_lt(x, y) : Bool}:
  +e = Equal.trans(Bool, Nat.is_lt(Nat.add(x, s), Nat.add(y, s)), Nat.is_lt(Nat.add(s, x), Nat.add(y, s)), Nat.is_lt(Nat.add(s, x), Nat.add(s, y)), Equal.cong(Nat, Bool, t => Nat.is_lt(t, Nat.add(y, s)), Nat.add(x, s), Nat.add(s, x), N.add_comm(x, s)), Equal.cong(Nat, Bool, t => Nat.is_lt(Nat.add(s, x), t), Nat.add(y, s), Nat.add(s, y), N.add_comm(y, s)))
  Equal.trans(Bool, Nat.is_lt(Nat.add(x, s), Nat.add(y, s)), Nat.is_lt(Nat.add(s, x), Nat.add(s, y)), Nat.is_lt(x, y), e, lt_cancel_l(s, x, y))

# y1 < y2: x1 + shift(k, y1) < x2 + shift(k, y2)
def lt_hi(+k: Nat, +x1: Nat, +y1: Nat, +x2: Nat, +y2: Nat, +hx1: {C.fits(k, x1) == True{} : Bool}, +h: {Nat.is_lt(y1, y2) == True{} : Bool}) -> {Nat.is_lt(Nat.add(x1, C.shift(k, y1)), Nat.add(x2, C.shift(k, y2))) == True{} : Bool}:
  +h1 = L.subst(Nat, z => {Nat.is_lt(x1, z) == True{} : Bool}, C.pow2(k), C.shift(k, 1n), Equal.sym(Nat, C.shift(k, 1n), C.pow2(k), shift_one(k)), lt_of_fits(k, x1, hx1))
  +h2 = N.lt_add_r2(x1, C.shift(k, 1n), C.shift(k, y1), h1)
  +e2 = Equal.sym(Nat, C.shift(k, Nat.add(1n, y1)), Nat.add(C.shift(k, 1n), C.shift(k, y1)), shift_add(k, 1n, y1))
  +h3 = L.subst(Nat, z => {Nat.is_lt(Nat.add(x1, C.shift(k, y1)), z) == True{} : Bool}, Nat.add(C.shift(k, 1n), C.shift(k, y1)), C.shift(k, 1n+y1), e2, h2)
  +h4 = shift_mono(k, 1n+y1, y2, N.lt_succ_le_succ(y1, y2, h))
  +h5 = L.subst(Nat, z => {Nat.is_le(C.shift(k, y2), z) == True{} : Bool}, Nat.add(C.shift(k, y2), x2), Nat.add(x2, C.shift(k, y2)), N.add_comm(C.shift(k, y2), x2), N.le_add_right(C.shift(k, y2), x2))
  N.lt_le_trans(Nat.add(x1, C.shift(k, y1)), C.shift(k, 1n+y1), Nat.add(x2, C.shift(k, y2)), h3, N.le_trans(C.shift(k, 1n+y1), C.shift(k, y2), Nat.add(x2, C.shift(k, y2)), h4, h5))

def lt_limbs_c(+k: Nat, +x1: Nat, +y1: Nat, +x2: Nat, +y2: Nat, +hx1: {C.fits(k, x1) == True{} : Bool}, +hx2: {C.fits(k, x2) == True{} : Bool}, +c: Bool, +d: Bool, +hc: {Nat.is_lt(y1, y2) == c : Bool}, +hd: {Nat.is_eq(y1, y2) == d : Bool}) -> {Bool.or(c, Bool.and(d, Nat.is_lt(x1, x2))) == Nat.is_lt(Nat.add(x1, C.shift(k, y1)), Nat.add(x2, C.shift(k, y2))) : Bool}:
  match c d:
    case True{} _:
      Equal.sym(Bool, Nat.is_lt(Nat.add(x1, C.shift(k, y1)), Nat.add(x2, C.shift(k, y2))), True{}, lt_hi(k, x1, y1, x2, y2, hx1, hc))
    case False{} True{}:
      +ey = N.eq_from_is_eq(y1, y2, hd)
      +e1 = L.subst(Nat, z => {Nat.is_lt(Nat.add(x1, C.shift(k, y1)), Nat.add(x2, C.shift(k, z))) == Nat.is_lt(x1, x2) : Bool}, y1, y2, ey, lt_cancel_r(x1, x2, C.shift(k, y1)))
      Equal.sym(Bool, Nat.is_lt(Nat.add(x1, C.shift(k, y1)), Nat.add(x2, C.shift(k, y2))), Nat.is_lt(x1, x2), e1)
    case False{} False{}:
      +h21 = N.lt_or_eq(y2, y1, N.not_lt_le(y1, y2, hc), N.is_eq_sym_false(y1, y2, hd))
      +hb = lt_hi(k, x2, y2, x1, y1, hx2, h21)
      Equal.sym(Bool, Nat.is_lt(Nat.add(x1, C.shift(k, y1)), Nat.add(x2, C.shift(k, y2))), False{}, N.le_not_lt(Nat.add(x1, C.shift(k, y1)), Nat.add(x2, C.shift(k, y2)), N.lt_le(Nat.add(x2, C.shift(k, y2)), Nat.add(x1, C.shift(k, y1)), hb)))

def lt_limbs(+k: Nat, +x1: Nat, +y1: Nat, +x2: Nat, +y2: Nat, +hx1: {C.fits(k, x1) == True{} : Bool}, +hx2: {C.fits(k, x2) == True{} : Bool}) -> {Bool.or(Nat.is_lt(y1, y2), Bool.and(Nat.is_eq(y1, y2), Nat.is_lt(x1, x2))) == Nat.is_lt(Nat.add(x1, C.shift(k, y1)), Nat.add(x2, C.shift(k, y2))) : Bool}:
  lt_limbs_c(k, x1, y1, x2, y2, hx1, hx2, Nat.is_lt(y1, y2), Nat.is_eq(y1, y2), {==}, {==})

def eq_limbs_f(+k: Nat, +x1: Nat, +y1: Nat, +x2: Nat, +y2: Nat, +d1: Bool, +d2: Bool, +h1: {Nat.is_eq(x1, x2) == d1 : Bool}, +h2: {Nat.is_eq(y1, y2) == d2 : Bool}, +he: {Nat.is_eq(Nat.add(x1, C.shift(k, y1)), Nat.add(x2, C.shift(k, y2))) == False{} : Bool}) -> {Bool.and(d1, d2) == False{} : Bool}:
  match d1 d2:
    case True{} True{}:
      +ex = N.eq_from_is_eq(x1, x2, h1)
      +ey = N.eq_from_is_eq(y1, y2, h2)
      +e = L.subst(Nat, z => {Nat.is_eq(Nat.add(x1, C.shift(k, y1)), Nat.add(z, C.shift(k, y1))) == False{} : Bool}, x2, x1, Equal.sym(Nat, x1, x2, ex), L.subst(Nat, z => {Nat.is_eq(Nat.add(x1, C.shift(k, y1)), Nat.add(x2, C.shift(k, z))) == False{} : Bool}, y2, y1, Equal.sym(Nat, y1, y2, ey), he))
      Empty.absurd({True{} == False{} : Bool}, L.false_true(Equal.trans(Bool, False{}, Nat.is_eq(Nat.add(x1, C.shift(k, y1)), Nat.add(x1, C.shift(k, y1))), True{}, Equal.sym(Bool, Nat.is_eq(Nat.add(x1, C.shift(k, y1)), Nat.add(x1, C.shift(k, y1))), False{}, e), N.is_eq_refl(Nat.add(x1, C.shift(k, y1))))))
    case True{} False{}:
      {==}
    case False{} _:
      {==}

def eq_limbs_c(+k: Nat, +x1: Nat, +y1: Nat, +x2: Nat, +y2: Nat, +hx1: {C.fits(k, x1) == True{} : Bool}, +hx2: {C.fits(k, x2) == True{} : Bool}, +c: Bool, +hc: {Nat.is_eq(Nat.add(x1, C.shift(k, y1)), Nat.add(x2, C.shift(k, y2))) == c : Bool}) -> {Bool.and(Nat.is_eq(x1, x2), Nat.is_eq(y1, y2)) == c : Bool}:
  match c:
    case True{}:
      +e = N.eq_from_is_eq(Nat.add(x1, C.shift(k, y1)), Nat.add(x2, C.shift(k, y2)), hc)
      +ex = Equal.trans(Nat, x1, C.low(k, Nat.add(x1, C.shift(k, y1))), x2, Equal.sym(Nat, C.low(k, Nat.add(x1, C.shift(k, y1))), x1, low_u(k, x1, y1, hx1)), Equal.trans(Nat, C.low(k, Nat.add(x1, C.shift(k, y1))), C.low(k, Nat.add(x2, C.shift(k, y2))), x2, Equal.cong(Nat, Nat, t => C.low(k, t), Nat.add(x1, C.shift(k, y1)), Nat.add(x2, C.shift(k, y2)), e), low_u(k, x2, y2, hx2)))
      +ey = Equal.trans(Nat, y1, C.high(k, Nat.add(x1, C.shift(k, y1))), y2, Equal.sym(Nat, C.high(k, Nat.add(x1, C.shift(k, y1))), y1, high_u(k, x1, y1, hx1)), Equal.trans(Nat, C.high(k, Nat.add(x1, C.shift(k, y1))), C.high(k, Nat.add(x2, C.shift(k, y2))), y2, Equal.cong(Nat, Nat, t => C.high(k, t), Nat.add(x1, C.shift(k, y1)), Nat.add(x2, C.shift(k, y2)), e), high_u(k, x2, y2, hx2)))
      +a = L.subst(Nat, z => {Nat.is_eq(x1, z) == True{} : Bool}, x1, x2, ex, N.is_eq_refl(x1))
      +b = L.subst(Nat, z => {Nat.is_eq(y1, z) == True{} : Bool}, y1, y2, ey, N.is_eq_refl(y1))
      Equal.trans(Bool, Bool.and(Nat.is_eq(x1, x2), Nat.is_eq(y1, y2)), Bool.and(True{}, Nat.is_eq(y1, y2)), True{}, Equal.cong(Bool, Bool, t => Bool.and(t, Nat.is_eq(y1, y2)), Nat.is_eq(x1, x2), True{}, a), b)
    case False{}:
      eq_limbs_f(k, x1, y1, x2, y2, Nat.is_eq(x1, x2), Nat.is_eq(y1, y2), {==}, {==}, hc)

def eq_limbs(+k: Nat, +x1: Nat, +y1: Nat, +x2: Nat, +y2: Nat, +hx1: {C.fits(k, x1) == True{} : Bool}, +hx2: {C.fits(k, x2) == True{} : Bool}) -> {Bool.and(Nat.is_eq(x1, x2), Nat.is_eq(y1, y2)) == Nat.is_eq(Nat.add(x1, C.shift(k, y1)), Nat.add(x2, C.shift(k, y2))) : Bool}:
  eq_limbs_c(k, x1, y1, x2, y2, hx1, hx2, Nat.is_eq(Nat.add(x1, C.shift(k, y1)), Nat.add(x2, C.shift(k, y2))), {==})

# ---- parity: bit is mod 2, and shift(1 + p, y) is even ----

def bit_mod(+n: Nat) -> {C.bit(n) == Nat.mod(n, 2n) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n+ +q:
      Equal.trans(Nat, C.bit(q), Nat.mod(q, 2n), Nat.mod(2n+q, 2n), bit_mod(q), Equal.sym(Nat, Nat.mod(2n+q, 2n), Nat.mod(q, 2n), NR.absorb(1n, 1n, q)))

def odd_limb(+p: Nat, +x: Nat, +y: Nat) -> {Nat.mod(Nat.add(x, C.shift(1n+p, y)), 2n) == Nat.mod(x, 2n) : Nat}:
  Equal.trans(Nat, Nat.mod(Nat.add(x, Nat.double(C.shift(p, y))), 2n), C.bit(Nat.add(x, Nat.double(C.shift(p, y)))), Nat.mod(x, 2n), Equal.sym(Nat, C.bit(Nat.add(x, Nat.double(C.shift(p, y)))), Nat.mod(Nat.add(x, Nat.double(C.shift(p, y))), 2n), bit_mod(Nat.add(x, Nat.double(C.shift(p, y))))), Equal.trans(Nat, C.bit(Nat.add(x, Nat.double(C.shift(p, y)))), C.bit(x), Nat.mod(x, 2n), bit_dbl(x, C.shift(p, y)), bit_mod(x)))

# ---- halving a two-limb number ----

def shift_dbl(+k: Nat, +z: Nat) -> {C.shift(k, Nat.double(z)) == Nat.double(C.shift(k, z)) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+ +p:
      Equal.cong(Nat, Nat, t => Nat.double(t), C.shift(p, Nat.double(z)), Nat.double(C.shift(p, z)), shift_dbl(p, z))

def dbl_mul(+x: Nat, +y: Nat) -> {Nat.double(Nat.mul(x, y)) == Nat.mul(x, Nat.double(y)) : Nat}:
  Equal.trans(Nat, Nat.double(Nat.mul(x, y)), Nat.add(Nat.mul(x, y), Nat.mul(x, y)), Nat.mul(x, Nat.double(y)), NA.double_self(Nat.mul(x, y)), Equal.trans(Nat, Nat.add(Nat.mul(x, y), Nat.mul(x, y)), Nat.mul(x, Nat.add(y, y)), Nat.mul(x, Nat.double(y)), Equal.sym(Nat, Nat.mul(x, Nat.add(y, y)), Nat.add(Nat.mul(x, y), Nat.mul(x, y)), NA.mul_add_left(x, y, y)), Equal.cong(Nat, Nat, t => Nat.mul(x, t), Nat.add(y, y), Nat.double(y), Equal.sym(Nat, Nat.double(y), Nat.add(y, y), NA.double_self(y)))))

def shift_mul(+k: Nat, +x: Nat) -> {C.shift(k, x) == Nat.mul(x, C.shift(k, 1n)) : Nat}:
  match k:
    case 0n:
      Equal.sym(Nat, Nat.mul(x, 1n), x, NA.mul_one(x))
    case 1n+ +p:
      Equal.trans(Nat, Nat.double(C.shift(p, x)), Nat.double(Nat.mul(x, C.shift(p, 1n))), Nat.mul(x, Nat.double(C.shift(p, 1n))), Equal.cong(Nat, Nat, t => Nat.double(t), C.shift(p, x), Nat.mul(x, C.shift(p, 1n)), shift_mul(p, x)), dbl_mul(x, C.shift(p, 1n)))

# half(x + shift(1 + p, y)) == half(x) + bit(y) shift(p, one) + shift(1 + p, half(y))
def half_limbs(+p: Nat, +one: Nat, +h1: {one == 1n : Nat}, +x: Nat, +y: Nat) -> {C.half(Nat.add(x, C.shift(1n+p, y))) == Nat.add(Nat.add(C.half(x), Nat.mul(C.bit(y), C.shift(p, one))), C.shift(1n+p, C.half(y))) : Nat}:
  +hx = C.half(x)
  +b = C.bit(y)
  +hy = C.half(y)
  +e1 = half_dbl(x, C.shift(p, y))
  +e2 = Equal.trans(Nat, C.shift(p, y), C.shift(p, Nat.add(b, Nat.double(hy))), Nat.add(C.shift(p, b), C.shift(p, Nat.double(hy))), Equal.cong(Nat, Nat, t => C.shift(p, t), y, Nat.add(b, Nat.double(hy)), hb(y)), shift_add(p, b, Nat.double(hy)))
  +e3 = Equal.trans(Nat, Nat.add(C.shift(p, b), C.shift(p, Nat.double(hy))), Nat.add(Nat.mul(b, C.shift(p, 1n)), C.shift(p, Nat.double(hy))), Nat.add(Nat.mul(b, C.shift(p, one)), Nat.double(C.shift(p, hy))), Equal.cong(Nat, Nat, t => Nat.add(t, C.shift(p, Nat.double(hy))), C.shift(p, b), Nat.mul(b, C.shift(p, 1n)), shift_mul(p, b)), Equal.trans(Nat, Nat.add(Nat.mul(b, C.shift(p, 1n)), C.shift(p, Nat.double(hy))), Nat.add(Nat.mul(b, C.shift(p, one)), C.shift(p, Nat.double(hy))), Nat.add(Nat.mul(b, C.shift(p, one)), Nat.double(C.shift(p, hy))), Equal.cong(Nat, Nat, t => Nat.add(Nat.mul(b, C.shift(p, t)), C.shift(p, Nat.double(hy))), 1n, one, Equal.sym(Nat, one, 1n, h1)), Equal.cong(Nat, Nat, t => Nat.add(Nat.mul(b, C.shift(p, one)), t), C.shift(p, Nat.double(hy)), Nat.double(C.shift(p, hy)), shift_dbl(p, hy))))
  +e4 = Equal.cong(Nat, Nat, t => Nat.add(hx, t), C.shift(p, y), Nat.add(Nat.mul(b, C.shift(p, one)), Nat.double(C.shift(p, hy))), Equal.trans(Nat, C.shift(p, y), Nat.add(C.shift(p, b), C.shift(p, Nat.double(hy))), Nat.add(Nat.mul(b, C.shift(p, one)), Nat.double(C.shift(p, hy))), e2, e3))
  Equal.trans(Nat, C.half(Nat.add(x, Nat.double(C.shift(p, y)))), Nat.add(hx, C.shift(p, y)), Nat.add(Nat.add(hx, Nat.mul(b, C.shift(p, one))), Nat.double(C.shift(p, hy))), e1, Equal.trans(Nat, Nat.add(hx, C.shift(p, y)), Nat.add(hx, Nat.add(Nat.mul(b, C.shift(p, one)), Nat.double(C.shift(p, hy)))), Nat.add(Nat.add(hx, Nat.mul(b, C.shift(p, one))), Nat.double(C.shift(p, hy))), e4, Equal.sym(Nat, Nat.add(Nat.add(hx, Nat.mul(b, C.shift(p, one))), Nat.double(C.shift(p, hy))), Nat.add(hx, Nat.add(Nat.mul(b, C.shift(p, one)), Nat.double(C.shift(p, hy)))), NA.add_assoc(hx, Nat.mul(b, C.shift(p, one)), Nat.double(C.shift(p, hy))))))

def fits_one(+k: Nat, +one: Nat, +h1: {one == 1n : Nat}, +x: Nat, +h: {Nat.is_lt(x, C.shift(k, one)) == True{} : Bool}) -> {C.fits(k, x) == True{} : Bool}:
  +h2 = L.subst(Nat, z => {Nat.is_lt(x, C.shift(k, z)) == True{} : Bool}, one, 1n, h1, h)
  fits_of_lt(k, x, L.subst(Nat, z => {Nat.is_lt(x, z) == True{} : Bool}, C.shift(k, 1n), C.pow2(k), shift_one(k), h2))

# a nonzero multiple of 2^k added: does not fit k bits
def unfit_nz(+k: Nat, +r: Nat, +q: Nat, +hq: {Nat.is_eq(q, 0n) == False{} : Bool}) -> {C.fits(k, Nat.add(r, C.shift(k, q))) == False{} : Bool}:
  match q:
    case 0n:
      Empty.absurd({C.fits(k, Nat.add(r, C.shift(k, 0n))) == False{} : Bool}, L.false_true(Equal.sym(Bool, True{}, False{}, hq)))
    case 1n+ +qp:
      unfit_shift(k, r, qp)

# ---- products of two-limb numbers ----

def shift_mul_l(+k: Nat, +x: Nat, +y: Nat) -> {Nat.mul(C.shift(k, x), y) == C.shift(k, Nat.mul(x, y)) : Nat}:
  +s1 = C.shift(k, 1n)
  Equal.trans(Nat, Nat.mul(C.shift(k, x), y), Nat.mul(Nat.mul(x, s1), y), C.shift(k, Nat.mul(x, y)), Equal.cong(Nat, Nat, t => Nat.mul(t, y), C.shift(k, x), Nat.mul(x, s1), shift_mul(k, x)), Equal.trans(Nat, Nat.mul(Nat.mul(x, s1), y), Nat.mul(x, Nat.mul(s1, y)), C.shift(k, Nat.mul(x, y)), NA.mul_assoc(x, s1, y), Equal.trans(Nat, Nat.mul(x, Nat.mul(s1, y)), Nat.mul(x, Nat.mul(y, s1)), C.shift(k, Nat.mul(x, y)), Equal.cong(Nat, Nat, t => Nat.mul(x, t), Nat.mul(s1, y), Nat.mul(y, s1), NA.mul_comm(s1, y)), Equal.trans(Nat, Nat.mul(x, Nat.mul(y, s1)), Nat.mul(Nat.mul(x, y), s1), C.shift(k, Nat.mul(x, y)), Equal.sym(Nat, Nat.mul(Nat.mul(x, y), s1), Nat.mul(x, Nat.mul(y, s1)), NA.mul_assoc(x, y, s1)), Equal.sym(Nat, C.shift(k, Nat.mul(x, y)), Nat.mul(Nat.mul(x, y), s1), shift_mul(k, Nat.mul(x, y)))))))

def shift_mul_r(+k: Nat, +x: Nat, +y: Nat) -> {Nat.mul(x, C.shift(k, y)) == C.shift(k, Nat.mul(x, y)) : Nat}:
  Equal.trans(Nat, Nat.mul(x, C.shift(k, y)), Nat.mul(C.shift(k, y), x), C.shift(k, Nat.mul(x, y)), NA.mul_comm(x, C.shift(k, y)), Equal.trans(Nat, Nat.mul(C.shift(k, y), x), C.shift(k, Nat.mul(y, x)), C.shift(k, Nat.mul(x, y)), shift_mul_l(k, y, x), Equal.cong(Nat, Nat, t => C.shift(k, t), Nat.mul(y, x), Nat.mul(x, y), NA.mul_comm(y, x))))

def low_add_shift(+k: Nat, +x: Nat, +y: Nat) -> {C.low(k, Nat.add(x, C.shift(k, y))) == C.low(k, x) : Nat}:
  +l = C.low(k, x)
  +h = C.high(k, x)
  +e = Equal.trans(Nat, Nat.add(x, C.shift(k, y)), Nat.add(Nat.add(l, C.shift(k, h)), C.shift(k, y)), Nat.add(l, C.shift(k, Nat.add(h, y))), Equal.cong(Nat, Nat, t => Nat.add(t, C.shift(k, y)), x, Nat.add(l, C.shift(k, h)), low_high(k, x)), Equal.trans(Nat, Nat.add(Nat.add(l, C.shift(k, h)), C.shift(k, y)), Nat.add(l, Nat.add(C.shift(k, h), C.shift(k, y))), Nat.add(l, C.shift(k, Nat.add(h, y))), NA.add_assoc(l, C.shift(k, h), C.shift(k, y)), Equal.cong(Nat, Nat, t => Nat.add(l, t), Nat.add(C.shift(k, h), C.shift(k, y)), C.shift(k, Nat.add(h, y)), Equal.sym(Nat, C.shift(k, Nat.add(h, y)), Nat.add(C.shift(k, h), C.shift(k, y)), shift_add(k, h, y)))))
  Equal.trans(Nat, C.low(k, Nat.add(x, C.shift(k, y))), C.low(k, Nat.add(l, C.shift(k, Nat.add(h, y)))), l, Equal.cong(Nat, Nat, t => C.low(k, t), Nat.add(x, C.shift(k, y)), Nat.add(l, C.shift(k, Nat.add(h, y))), e), low_u(k, l, Nat.add(h, y), low_fits(k, x)))

def expand_k(+k: Nat, +al: Nat, +ah: Nat, +bl: Nat, +bh: Nat) -> {Nat.mul(Nat.add(al, C.shift(k, ah)), Nat.add(bl, C.shift(k, bh))) == Nat.add(Nat.add(Nat.mul(al, bl), C.shift(k, Nat.mul(al, bh))), Nat.add(C.shift(k, Nat.mul(ah, bl)), C.shift(k, C.shift(k, Nat.mul(ah, bh))))) : Nat}:
  Equal.trans(Nat, Nat.mul(Nat.add(al, C.shift(k, ah)), Nat.add(bl, C.shift(k, bh))), Nat.add(Nat.mul(al, Nat.add(bl, C.shift(k, bh))), Nat.mul(C.shift(k, ah), Nat.add(bl, C.shift(k, bh)))), Nat.add(Nat.add(Nat.mul(al, bl), C.shift(k, Nat.mul(al, bh))), Nat.add(C.shift(k, Nat.mul(ah, bl)), C.shift(k, C.shift(k, Nat.mul(ah, bh))))), NA.mul_add_right(al, C.shift(k, ah), Nat.add(bl, C.shift(k, bh))), Equal.trans(Nat, Nat.add(Nat.mul(al, Nat.add(bl, C.shift(k, bh))), Nat.mul(C.shift(k, ah), Nat.add(bl, C.shift(k, bh)))), Nat.add(Nat.add(Nat.mul(al, bl), Nat.mul(al, C.shift(k, bh))), Nat.mul(C.shift(k, ah), Nat.add(bl, C.shift(k, bh)))), Nat.add(Nat.add(Nat.mul(al, bl), C.shift(k, Nat.mul(al, bh))), Nat.add(C.shift(k, Nat.mul(ah, bl)), C.shift(k, C.shift(k, Nat.mul(ah, bh))))), Equal.cong(Nat, Nat, t => Nat.add(t, Nat.mul(C.shift(k, ah), Nat.add(bl, C.shift(k, bh)))), Nat.mul(al, Nat.add(bl, C.shift(k, bh))), Nat.add(Nat.mul(al, bl), Nat.mul(al, C.shift(k, bh))), NA.mul_add_left(al, bl, C.shift(k, bh))), Equal.trans(Nat, Nat.add(Nat.add(Nat.mul(al, bl), Nat.mul(al, C.shift(k, bh))), Nat.mul(C.shift(k, ah), Nat.add(bl, C.shift(k, bh)))), Nat.add(Nat.add(Nat.mul(al, bl), C.shift(k, Nat.mul(al, bh))), Nat.mul(C.shift(k, ah), Nat.add(bl, C.shift(k, bh)))), Nat.add(Nat.add(Nat.mul(al, bl), C.shift(k, Nat.mul(al, bh))), Nat.add(C.shift(k, Nat.mul(ah, bl)), C.shift(k, C.shift(k, Nat.mul(ah, bh))))), Equal.cong(Nat, Nat, t => Nat.add(Nat.add(Nat.mul(al, bl), t), Nat.mul(C.shift(k, ah), Nat.add(bl, C.shift(k, bh)))), Nat.mul(al, C.shift(k, bh)), C.shift(k, Nat.mul(al, bh)), shift_mul_r(k, al, bh)), Equal.trans(Nat, Nat.add(Nat.add(Nat.mul(al, bl), C.shift(k, Nat.mul(al, bh))), Nat.mul(C.shift(k, ah), Nat.add(bl, C.shift(k, bh)))), Nat.add(Nat.add(Nat.mul(al, bl), C.shift(k, Nat.mul(al, bh))), Nat.add(Nat.mul(C.shift(k, ah), bl), Nat.mul(C.shift(k, ah), C.shift(k, bh)))), Nat.add(Nat.add(Nat.mul(al, bl), C.shift(k, Nat.mul(al, bh))), Nat.add(C.shift(k, Nat.mul(ah, bl)), C.shift(k, C.shift(k, Nat.mul(ah, bh))))), Equal.cong(Nat, Nat, t => Nat.add(Nat.add(Nat.mul(al, bl), C.shift(k, Nat.mul(al, bh))), t), Nat.mul(C.shift(k, ah), Nat.add(bl, C.shift(k, bh))), Nat.add(Nat.mul(C.shift(k, ah), bl), Nat.mul(C.shift(k, ah), C.shift(k, bh))), NA.mul_add_left(C.shift(k, ah), bl, C.shift(k, bh))), Equal.trans(Nat, Nat.add(Nat.add(Nat.mul(al, bl), C.shift(k, Nat.mul(al, bh))), Nat.add(Nat.mul(C.shift(k, ah), bl), Nat.mul(C.shift(k, ah), C.shift(k, bh)))), Nat.add(Nat.add(Nat.mul(al, bl), C.shift(k, Nat.mul(al, bh))), Nat.add(C.shift(k, Nat.mul(ah, bl)), Nat.mul(C.shift(k, ah), C.shift(k, bh)))), Nat.add(Nat.add(Nat.mul(al, bl), C.shift(k, Nat.mul(al, bh))), Nat.add(C.shift(k, Nat.mul(ah, bl)), C.shift(k, C.shift(k, Nat.mul(ah, bh))))), Equal.cong(Nat, Nat, t => Nat.add(Nat.add(Nat.mul(al, bl), C.shift(k, Nat.mul(al, bh))), Nat.add(t, Nat.mul(C.shift(k, ah), C.shift(k, bh)))), Nat.mul(C.shift(k, ah), bl), C.shift(k, Nat.mul(ah, bl)), shift_mul_l(k, ah, bl)), Equal.trans(Nat, Nat.add(Nat.add(Nat.mul(al, bl), C.shift(k, Nat.mul(al, bh))), Nat.add(C.shift(k, Nat.mul(ah, bl)), Nat.mul(C.shift(k, ah), C.shift(k, bh)))), Nat.add(Nat.add(Nat.mul(al, bl), C.shift(k, Nat.mul(al, bh))), Nat.add(C.shift(k, Nat.mul(ah, bl)), C.shift(k, Nat.mul(ah, C.shift(k, bh))))), Nat.add(Nat.add(Nat.mul(al, bl), C.shift(k, Nat.mul(al, bh))), Nat.add(C.shift(k, Nat.mul(ah, bl)), C.shift(k, C.shift(k, Nat.mul(ah, bh))))), Equal.cong(Nat, Nat, t => Nat.add(Nat.add(Nat.mul(al, bl), C.shift(k, Nat.mul(al, bh))), Nat.add(C.shift(k, Nat.mul(ah, bl)), t)), Nat.mul(C.shift(k, ah), C.shift(k, bh)), C.shift(k, Nat.mul(ah, C.shift(k, bh))), shift_mul_l(k, ah, C.shift(k, bh))), Equal.cong(Nat, Nat, t => Nat.add(Nat.add(Nat.mul(al, bl), C.shift(k, Nat.mul(al, bh))), Nat.add(C.shift(k, Nat.mul(ah, bl)), C.shift(k, t))), Nat.mul(ah, C.shift(k, bh)), C.shift(k, Nat.mul(ah, bh)), shift_mul_r(k, ah, bh))))))))

# (al + 2^k ah)(bl + 2^k bh) == al bl + 2^k t + 2^(2k) (kc + ah bh) when al bh + ah bl == t + 2^k kc
def mul_k(+k: Nat, +al: Nat, +ah: Nat, +bl: Nat, +bh: Nat, +t: Nat, +kc: Nat, +e: {Nat.add(t, C.shift(k, kc)) == Nat.add(Nat.mul(al, bh), Nat.mul(ah, bl)) : Nat}) -> {Nat.mul(Nat.add(al, C.shift(k, ah)), Nat.add(bl, C.shift(k, bh))) == Nat.add(Nat.add(Nat.mul(al, bl), C.shift(k, t)), C.shift(k, C.shift(k, Nat.add(kc, Nat.mul(ah, bh))))) : Nat}:
  Equal.trans(Nat, Nat.mul(Nat.add(al, C.shift(k, ah)), Nat.add(bl, C.shift(k, bh))), Nat.add(Nat.add(Nat.mul(al, bl), C.shift(k, Nat.mul(al, bh))), Nat.add(C.shift(k, Nat.mul(ah, bl)), C.shift(k, C.shift(k, Nat.mul(ah, bh))))), Nat.add(Nat.add(Nat.mul(al, bl), C.shift(k, t)), C.shift(k, C.shift(k, Nat.add(kc, Nat.mul(ah, bh))))), expand_k(k, al, ah, bl, bh), Equal.trans(Nat, Nat.add(Nat.add(Nat.mul(al, bl), C.shift(k, Nat.mul(al, bh))), Nat.add(C.shift(k, Nat.mul(ah, bl)), C.shift(k, C.shift(k, Nat.mul(ah, bh))))), Nat.add(Nat.mul(al, bl), Nat.add(C.shift(k, Nat.mul(al, bh)), Nat.add(C.shift(k, Nat.mul(ah, bl)), C.shift(k, C.shift(k, Nat.mul(ah, bh)))))), Nat.add(Nat.add(Nat.mul(al, bl), C.shift(k, t)), C.shift(k, C.shift(k, Nat.add(kc, Nat.mul(ah, bh))))), NA.add_assoc(Nat.mul(al, bl), C.shift(k, Nat.mul(al, bh)), Nat.add(C.shift(k, Nat.mul(ah, bl)), C.shift(k, C.shift(k, Nat.mul(ah, bh))))), Equal.trans(Nat, Nat.add(Nat.mul(al, bl), Nat.add(C.shift(k, Nat.mul(al, bh)), Nat.add(C.shift(k, Nat.mul(ah, bl)), C.shift(k, C.shift(k, Nat.mul(ah, bh)))))), Nat.add(Nat.mul(al, bl), Nat.add(Nat.add(C.shift(k, Nat.mul(al, bh)), C.shift(k, Nat.mul(ah, bl))), C.shift(k, C.shift(k, Nat.mul(ah, bh))))), Nat.add(Nat.add(Nat.mul(al, bl), C.shift(k, t)), C.shift(k, C.shift(k, Nat.add(kc, Nat.mul(ah, bh))))), Equal.cong(Nat, Nat, z => Nat.add(Nat.mul(al, bl), z), Nat.add(C.shift(k, Nat.mul(al, bh)), Nat.add(C.shift(k, Nat.mul(ah, bl)), C.shift(k, C.shift(k, Nat.mul(ah, bh))))), Nat.add(Nat.add(C.shift(k, Nat.mul(al, bh)), C.shift(k, Nat.mul(ah, bl))), C.shift(k, C.shift(k, Nat.mul(ah, bh)))), Equal.sym(Nat, Nat.add(Nat.add(C.shift(k, Nat.mul(al, bh)), C.shift(k, Nat.mul(ah, bl))), C.shift(k, C.shift(k, Nat.mul(ah, bh)))), Nat.add(C.shift(k, Nat.mul(al, bh)), Nat.add(C.shift(k, Nat.mul(ah, bl)), C.shift(k, C.shift(k, Nat.mul(ah, bh))))), NA.add_assoc(C.shift(k, Nat.mul(al, bh)), C.shift(k, Nat.mul(ah, bl)), C.shift(k, C.shift(k, Nat.mul(ah, bh)))))), Equal.trans(Nat, Nat.add(Nat.mul(al, bl), Nat.add(Nat.add(C.shift(k, Nat.mul(al, bh)), C.shift(k, Nat.mul(ah, bl))), C.shift(k, C.shift(k, Nat.mul(ah, bh))))), Nat.add(Nat.mul(al, bl), Nat.add(C.shift(k, Nat.add(Nat.mul(al, bh), Nat.mul(ah, bl))), C.shift(k, C.shift(k, Nat.mul(ah, bh))))), Nat.add(Nat.add(Nat.mul(al, bl), C.shift(k, t)), C.shift(k, C.shift(k, Nat.add(kc, Nat.mul(ah, bh))))), Equal.cong(Nat, Nat, z => Nat.add(Nat.mul(al, bl), Nat.add(z, C.shift(k, C.shift(k, Nat.mul(ah, bh))))), Nat.add(C.shift(k, Nat.mul(al, bh)), C.shift(k, Nat.mul(ah, bl))), C.shift(k, Nat.add(Nat.mul(al, bh), Nat.mul(ah, bl))), Equal.sym(Nat, C.shift(k, Nat.add(Nat.mul(al, bh), Nat.mul(ah, bl))), Nat.add(C.shift(k, Nat.mul(al, bh)), C.shift(k, Nat.mul(ah, bl))), shift_add(k, Nat.mul(al, bh), Nat.mul(ah, bl)))), Equal.trans(Nat, Nat.add(Nat.mul(al, bl), Nat.add(C.shift(k, Nat.add(Nat.mul(al, bh), Nat.mul(ah, bl))), C.shift(k, C.shift(k, Nat.mul(ah, bh))))), Nat.add(Nat.mul(al, bl), Nat.add(C.shift(k, Nat.add(t, C.shift(k, kc))), C.shift(k, C.shift(k, Nat.mul(ah, bh))))), Nat.add(Nat.add(Nat.mul(al, bl), C.shift(k, t)), C.shift(k, C.shift(k, Nat.add(kc, Nat.mul(ah, bh))))), Equal.cong(Nat, Nat, z => Nat.add(Nat.mul(al, bl), Nat.add(C.shift(k, z), C.shift(k, C.shift(k, Nat.mul(ah, bh))))), Nat.add(Nat.mul(al, bh), Nat.mul(ah, bl)), Nat.add(t, C.shift(k, kc)), Equal.sym(Nat, Nat.add(t, C.shift(k, kc)), Nat.add(Nat.mul(al, bh), Nat.mul(ah, bl)), e)), Equal.trans(Nat, Nat.add(Nat.mul(al, bl), Nat.add(C.shift(k, Nat.add(t, C.shift(k, kc))), C.shift(k, C.shift(k, Nat.mul(ah, bh))))), Nat.add(Nat.mul(al, bl), Nat.add(Nat.add(C.shift(k, t), C.shift(k, C.shift(k, kc))), C.shift(k, C.shift(k, Nat.mul(ah, bh))))), Nat.add(Nat.add(Nat.mul(al, bl), C.shift(k, t)), C.shift(k, C.shift(k, Nat.add(kc, Nat.mul(ah, bh))))), Equal.cong(Nat, Nat, z => Nat.add(Nat.mul(al, bl), Nat.add(z, C.shift(k, C.shift(k, Nat.mul(ah, bh))))), C.shift(k, Nat.add(t, C.shift(k, kc))), Nat.add(C.shift(k, t), C.shift(k, C.shift(k, kc))), shift_add(k, t, C.shift(k, kc))), Equal.trans(Nat, Nat.add(Nat.mul(al, bl), Nat.add(Nat.add(C.shift(k, t), C.shift(k, C.shift(k, kc))), C.shift(k, C.shift(k, Nat.mul(ah, bh))))), Nat.add(Nat.mul(al, bl), Nat.add(C.shift(k, t), Nat.add(C.shift(k, C.shift(k, kc)), C.shift(k, C.shift(k, Nat.mul(ah, bh)))))), Nat.add(Nat.add(Nat.mul(al, bl), C.shift(k, t)), C.shift(k, C.shift(k, Nat.add(kc, Nat.mul(ah, bh))))), Equal.cong(Nat, Nat, z => Nat.add(Nat.mul(al, bl), z), Nat.add(Nat.add(C.shift(k, t), C.shift(k, C.shift(k, kc))), C.shift(k, C.shift(k, Nat.mul(ah, bh)))), Nat.add(C.shift(k, t), Nat.add(C.shift(k, C.shift(k, kc)), C.shift(k, C.shift(k, Nat.mul(ah, bh))))), NA.add_assoc(C.shift(k, t), C.shift(k, C.shift(k, kc)), C.shift(k, C.shift(k, Nat.mul(ah, bh))))), Equal.trans(Nat, Nat.add(Nat.mul(al, bl), Nat.add(C.shift(k, t), Nat.add(C.shift(k, C.shift(k, kc)), C.shift(k, C.shift(k, Nat.mul(ah, bh)))))), Nat.add(Nat.mul(al, bl), Nat.add(C.shift(k, t), C.shift(k, Nat.add(C.shift(k, kc), C.shift(k, Nat.mul(ah, bh)))))), Nat.add(Nat.add(Nat.mul(al, bl), C.shift(k, t)), C.shift(k, C.shift(k, Nat.add(kc, Nat.mul(ah, bh))))), Equal.cong(Nat, Nat, z => Nat.add(Nat.mul(al, bl), Nat.add(C.shift(k, t), z)), Nat.add(C.shift(k, C.shift(k, kc)), C.shift(k, C.shift(k, Nat.mul(ah, bh)))), C.shift(k, Nat.add(C.shift(k, kc), C.shift(k, Nat.mul(ah, bh)))), Equal.sym(Nat, C.shift(k, Nat.add(C.shift(k, kc), C.shift(k, Nat.mul(ah, bh)))), Nat.add(C.shift(k, C.shift(k, kc)), C.shift(k, C.shift(k, Nat.mul(ah, bh)))), shift_add(k, C.shift(k, kc), C.shift(k, Nat.mul(ah, bh))))), Equal.trans(Nat, Nat.add(Nat.mul(al, bl), Nat.add(C.shift(k, t), C.shift(k, Nat.add(C.shift(k, kc), C.shift(k, Nat.mul(ah, bh)))))), Nat.add(Nat.mul(al, bl), Nat.add(C.shift(k, t), C.shift(k, C.shift(k, Nat.add(kc, Nat.mul(ah, bh)))))), Nat.add(Nat.add(Nat.mul(al, bl), C.shift(k, t)), C.shift(k, C.shift(k, Nat.add(kc, Nat.mul(ah, bh))))), Equal.cong(Nat, Nat, z => Nat.add(Nat.mul(al, bl), Nat.add(C.shift(k, t), C.shift(k, z))), Nat.add(C.shift(k, kc), C.shift(k, Nat.mul(ah, bh))), C.shift(k, Nat.add(kc, Nat.mul(ah, bh))), Equal.sym(Nat, C.shift(k, Nat.add(kc, Nat.mul(ah, bh))), Nat.add(C.shift(k, kc), C.shift(k, Nat.mul(ah, bh))), shift_add(k, kc, Nat.mul(ah, bh)))), Equal.sym(Nat, Nat.add(Nat.add(Nat.mul(al, bl), C.shift(k, t)), C.shift(k, C.shift(k, Nat.add(kc, Nat.mul(ah, bh))))), Nat.add(Nat.mul(al, bl), Nat.add(C.shift(k, t), C.shift(k, C.shift(k, Nat.add(kc, Nat.mul(ah, bh)))))), NA.add_assoc(Nat.mul(al, bl), C.shift(k, t), C.shift(k, C.shift(k, Nat.add(kc, Nat.mul(ah, bh)))))))))))))))

def low_fit(+k: Nat, +r: Nat, +hr: {C.fits(k, r) == True{} : Bool}) -> {C.low(k, r) == r : Nat}:
  +e = Equal.trans(Nat, Nat.add(r, C.shift(k, 0n)), Nat.add(r, 0n), r, Equal.cong(Nat, Nat, t => Nat.add(r, t), C.shift(k, 0n), 0n, shift_zero(k)), N.add_zero(r))
  L.subst(Nat, z => {C.low(k, z) == r : Nat}, Nat.add(r, C.shift(k, 0n)), r, e, low_u(k, r, 0n, hr))

def pow2_sq(+k: Nat) -> {Nat.mul(C.pow2(k), C.pow2(k)) == C.pow2(Nat.add(k, k)) : Nat}:
  Equal.trans(Nat, Nat.mul(C.pow2(k), C.pow2(k)), Nat.mul(C.pow2(k), C.shift(k, 1n)), C.pow2(Nat.add(k, k)), Equal.cong(Nat, Nat, t => Nat.mul(C.pow2(k), t), C.pow2(k), C.shift(k, 1n), Equal.sym(Nat, C.shift(k, 1n), C.pow2(k), shift_one(k))), Equal.trans(Nat, Nat.mul(C.pow2(k), C.shift(k, 1n)), C.shift(k, C.pow2(k)), C.pow2(Nat.add(k, k)), Equal.sym(Nat, C.shift(k, C.pow2(k)), Nat.mul(C.pow2(k), C.shift(k, 1n)), shift_mul(k, C.pow2(k))), shift_pow2(k, k)))

def shift_mul_one(+k: Nat, +one: Nat, +h1: {one == 1n : Nat}, +x: Nat) -> {C.shift(k, x) == Nat.mul(x, C.shift(k, one)) : Nat}:
  L.subst(Nat, z => {C.shift(k, x) == Nat.mul(x, C.shift(k, z)) : Nat}, 1n, one, Equal.sym(Nat, one, 1n, h1), shift_mul(k, x))

def shift_lt(+k: Nat, +a: Nat, +b: Nat, +h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_lt(C.shift(k, a), C.shift(k, b)) == True{} : Bool}:
  match k:
    case 0n:
      h
    case 1n+ +p:
      N.double_lt(C.shift(p, a), C.shift(p, b), shift_lt(p, a, b, h))

# ---- shifting two-limb numbers ----

def high_add_shift(+k: Nat, +x: Nat, +z: Nat) -> {C.high(k, Nat.add(x, C.shift(k, z))) == Nat.add(C.high(k, x), z) : Nat}:
  +l = C.low(k, x)
  +h = C.high(k, x)
  +e = Equal.trans(Nat, Nat.add(x, C.shift(k, z)), Nat.add(Nat.add(l, C.shift(k, h)), C.shift(k, z)), Nat.add(l, C.shift(k, Nat.add(h, z))), Equal.cong(Nat, Nat, t => Nat.add(t, C.shift(k, z)), x, Nat.add(l, C.shift(k, h)), low_high(k, x)), Equal.trans(Nat, Nat.add(Nat.add(l, C.shift(k, h)), C.shift(k, z)), Nat.add(l, Nat.add(C.shift(k, h), C.shift(k, z))), Nat.add(l, C.shift(k, Nat.add(h, z))), NA.add_assoc(l, C.shift(k, h), C.shift(k, z)), Equal.cong(Nat, Nat, t => Nat.add(l, t), Nat.add(C.shift(k, h), C.shift(k, z)), C.shift(k, Nat.add(h, z)), Equal.sym(Nat, C.shift(k, Nat.add(h, z)), Nat.add(C.shift(k, h), C.shift(k, z)), shift_add(k, h, z)))))
  Equal.trans(Nat, C.high(k, Nat.add(x, C.shift(k, z))), C.high(k, Nat.add(l, C.shift(k, Nat.add(h, z)))), Nat.add(h, z), Equal.cong(Nat, Nat, t => C.high(k, t), Nat.add(x, C.shift(k, z)), Nat.add(l, C.shift(k, Nat.add(h, z))), e), high_u(k, l, Nat.add(h, z), low_fits(k, x)))

def high_comp(+a: Nat, +b: Nat, +n: Nat) -> {C.high(Nat.add(b, a), n) == C.high(a, C.high(b, n)) : Nat}:
  match b:
    case 0n:
      {==}
    case 1n+ +p:
      high_comp(a, p, C.half(n))

# high(k, n) is n div 2^k, low(k, n) is n mod 2^k
def high_div(+k: Nat, +n: Nat, +pp: Nat, +hp: {C.pow2(k) == 1n+pp : Nat}) -> {C.high(k, n) == Nat.div(n, 1n+pp) : Nat}:
  +l = C.low(k, n)
  +h = C.high(k, n)
  +eS = Equal.trans(Nat, C.shift(k, h), Nat.mul(h, C.shift(k, 1n)), Nat.mul(h, 1n+pp), shift_mul(k, h), Equal.cong(Nat, Nat, t => Nat.mul(h, t), C.shift(k, 1n), 1n+pp, Equal.trans(Nat, C.shift(k, 1n), C.pow2(k), 1n+pp, shift_one(k), hp)))
  +e = Equal.trans(Nat, Nat.add(Nat.mul(h, 1n+pp), l), Nat.add(l, Nat.mul(h, 1n+pp)), n, N.add_comm(Nat.mul(h, 1n+pp), l), Equal.trans(Nat, Nat.add(l, Nat.mul(h, 1n+pp)), Nat.add(l, C.shift(k, h)), n, Equal.cong(Nat, Nat, t => Nat.add(l, t), Nat.mul(h, 1n+pp), C.shift(k, h), Equal.sym(Nat, C.shift(k, h), Nat.mul(h, 1n+pp), eS)), Equal.sym(Nat, n, Nat.add(l, C.shift(k, h)), low_high(k, n))))
  +hl = L.subst(Nat, t => {Nat.is_lt(l, t) == True{} : Bool}, C.pow2(k), 1n+pp, hp, low_lt(k, n))
  Equal.trans(Nat, h, Nat.div(Nat.add(Nat.mul(h, 1n+pp), l), 1n+pp), Nat.div(n, 1n+pp), Equal.sym(Nat, Nat.div(Nat.add(Nat.mul(h, 1n+pp), l), 1n+pp), h, NR.div_of(h, pp, l, hl)), Equal.cong(Nat, Nat, t => Nat.div(t, 1n+pp), Nat.add(Nat.mul(h, 1n+pp), l), n, e))

# low(s + t, shift(s, y)) == shift(s, low(t, y))
def low_shift(+s: Nat, +t: Nat, +y: Nat) -> {C.low(Nat.add(s, t), C.shift(s, y)) == C.shift(s, C.low(t, y)) : Nat}:
  +l = C.low(t, y)
  +h = C.high(t, y)
  +e = Equal.trans(Nat, C.shift(s, y), C.shift(s, Nat.add(l, C.shift(t, h))), Nat.add(C.shift(s, l), C.shift(Nat.add(s, t), h)), Equal.cong(Nat, Nat, z => C.shift(s, z), y, Nat.add(l, C.shift(t, h)), low_high(t, y)), Equal.trans(Nat, C.shift(s, Nat.add(l, C.shift(t, h))), Nat.add(C.shift(s, l), C.shift(s, C.shift(t, h))), Nat.add(C.shift(s, l), C.shift(Nat.add(s, t), h)), shift_add(s, l, C.shift(t, h)), Equal.cong(Nat, Nat, z => Nat.add(C.shift(s, l), z), C.shift(s, C.shift(t, h)), C.shift(Nat.add(s, t), h), Equal.sym(Nat, C.shift(Nat.add(s, t), h), C.shift(s, C.shift(t, h)), shift_comp(s, t, h)))))
  +hf = fits_of_lt(Nat.add(s, t), C.shift(s, l), L.subst(Nat, z => {Nat.is_lt(C.shift(s, l), z) == True{} : Bool}, C.shift(s, C.pow2(t)), C.pow2(Nat.add(s, t)), shift_pow2(s, t), shift_lt(s, l, C.pow2(t), low_lt(t, y))))
  Equal.trans(Nat, C.low(Nat.add(s, t), C.shift(s, y)), C.low(Nat.add(s, t), Nat.add(C.shift(s, l), C.shift(Nat.add(s, t), h))), C.shift(s, l), Equal.cong(Nat, Nat, z => C.low(Nat.add(s, t), z), C.shift(s, y), Nat.add(C.shift(s, l), C.shift(Nat.add(s, t), h)), e), low_u(Nat.add(s, t), C.shift(s, l), h, hf))

# a < b, c <= a: a - c < b - c
def sub_lt_sub(+a: Nat, +b: Nat, +c: Nat, +h: {Nat.is_lt(a, b) == True{} : Bool}, +hc: {Nat.is_le(c, a) == True{} : Bool}) -> {Nat.is_lt(Nat.sub(a, c), Nat.sub(b, c)) == True{} : Bool}:
  +ea = N.sub_add(a, c, hc)
  +eb = N.sub_add(b, c, N.le_trans(c, a, b, hc, N.lt_le(a, b, h)))
  +h2 = L.subst(Nat, z => {Nat.is_lt(z, Nat.add(c, Nat.sub(b, c))) == True{} : Bool}, a, Nat.add(c, Nat.sub(a, c)), Equal.sym(Nat, Nat.add(c, Nat.sub(a, c)), a, ea), L.subst(Nat, z => {Nat.is_lt(a, z) == True{} : Bool}, b, Nat.add(c, Nat.sub(b, c)), Equal.sym(Nat, Nat.add(c, Nat.sub(b, c)), b, eb), h))
  Equal.trans(Bool, Nat.is_lt(Nat.sub(a, c), Nat.sub(b, c)), Nat.is_lt(Nat.add(c, Nat.sub(a, c)), Nat.add(c, Nat.sub(b, c))), True{}, Equal.sym(Bool, Nat.is_lt(Nat.add(c, Nat.sub(a, c)), Nat.add(c, Nat.sub(b, c))), Nat.is_lt(Nat.sub(a, c), Nat.sub(b, c)), lt_cancel_l(c, Nat.sub(a, c), Nat.sub(b, c))), h2)
