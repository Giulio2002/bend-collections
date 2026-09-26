import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/math/f64.bend as SF
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ./width.bend as WW
import ./u32laws.bend as LW

# Comparisons of naturals (Nat.cmp), lexicographic pairs and common scales:
# the order facts behind the f64 comparison and rounding proofs.

def absurd_tf(-T: Type, +h: {False{} == True{} : Bool}) -> T:
  Empty.absurd(T, LW.true_ne_false(Equal.sym(Bool, False{}, True{}, h)))

def lex(c: Cmp, d: Cmp) -> Cmp:
  match c:
    case LT{}:
      LT{}
    case EQ{}:
      d
    case GT{}:
      GT{}

def cmp_dbl(+a: Nat, +b: Nat) -> {Nat.cmp(Nat.double(a), Nat.double(b)) == Nat.cmp(a, b) : Cmp}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+ +bp:
      {==}
    case 1n+ +ap 0n:
      {==}
    case 1n+ +ap 1n+ +bp:
      cmp_dbl(ap, bp)

def cmp_shift(+k: Nat, +a: Nat, +b: Nat) -> {Nat.cmp(C.shift(k, a), C.shift(k, b)) == Nat.cmp(a, b) : Cmp}:
  match k:
    case 0n:
      {==}
    case 1n+ +p:
      Equal.trans(Cmp, Nat.cmp(Nat.double(C.shift(p, a)), Nat.double(C.shift(p, b))), Nat.cmp(C.shift(p, a), C.shift(p, b)), Nat.cmp(a, b), cmp_dbl(C.shift(p, a), C.shift(p, b)), cmp_shift(p, a, b))

def cmp_add(+d: Nat, +a: Nat, +b: Nat) -> {Nat.cmp(Nat.add(d, a), Nat.add(d, b)) == Nat.cmp(a, b) : Cmp}:
  match d:
    case 0n:
      {==}
    case 1n+ +dp:
      cmp_add(dp, a, b)

def cmp_addr(+a: Nat, +b: Nat, +s: Nat) -> {Nat.cmp(Nat.add(a, s), Nat.add(b, s)) == Nat.cmp(a, b) : Cmp}:
  +e1 = Equal.cong(Nat, Cmp, z => Nat.cmp(z, Nat.add(b, s)), Nat.add(a, s), Nat.add(s, a), NA.add_comm(a, s))
  +e2 = Equal.cong(Nat, Cmp, z => Nat.cmp(Nat.add(s, a), z), Nat.add(b, s), Nat.add(s, b), NA.add_comm(b, s))
  Equal.trans(Cmp, Nat.cmp(Nat.add(a, s), Nat.add(b, s)), Nat.cmp(Nat.add(s, a), Nat.add(b, s)), Nat.cmp(a, b), e1, Equal.trans(Cmp, Nat.cmp(Nat.add(s, a), Nat.add(b, s)), Nat.cmp(Nat.add(s, a), Nat.add(s, b)), Nat.cmp(a, b), e2, cmp_add(s, a, b)))

def lt_c(+c: Cmp, +h: {Cmp.is_lt(c) == True{} : Bool}) -> {c == LT{} : Cmp}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      absurd_tf({EQ{} == LT{} : Cmp}, h)
    case GT{}:
      absurd_tf({GT{} == LT{} : Cmp}, h)

def eq_c(+c: Cmp, +h: {Cmp.is_eq(c) == True{} : Bool}) -> {c == EQ{} : Cmp}:
  match c:
    case LT{}:
      absurd_tf({LT{} == EQ{} : Cmp}, h)
    case EQ{}:
      {==}
    case GT{}:
      absurd_tf({GT{} == EQ{} : Cmp}, h)

def cmp_lt(+a: Nat, +b: Nat, +h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.cmp(a, b) == LT{} : Cmp}:
  lt_c(Nat.cmp(a, b), h)

def cmp_flip(+a: Nat, +b: Nat) -> {SF.flip(Nat.cmp(a, b)) == Nat.cmp(b, a) : Cmp}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+ +bp:
      {==}
    case 1n+ +ap 0n:
      {==}
    case 1n+ +ap 1n+ +bp:
      cmp_flip(ap, bp)

def cmp_gt(+a: Nat, +b: Nat, +h: {Nat.is_lt(b, a) == True{} : Bool}) -> {Nat.cmp(a, b) == GT{} : Cmp}:
  Equal.trans(Cmp, Nat.cmp(a, b), SF.flip(Nat.cmp(b, a)), GT{}, Equal.sym(Cmp, SF.flip(Nat.cmp(b, a)), Nat.cmp(a, b), cmp_flip(b, a)), Equal.cong(Cmp, Cmp, t => SF.flip(t), Nat.cmp(b, a), LT{}, cmp_lt(b, a, h)))

def cmp_refl(+a: Nat) -> {Nat.cmp(a, a) == EQ{} : Cmp}:
  eq_c(Nat.cmp(a, a), N.is_eq_refl(a))

def eq_of_cmp(+a: Nat, +b: Nat, +h: {Nat.cmp(a, b) == EQ{} : Cmp}) -> {a == b : Nat}:
  N.eq_from_is_eq(a, b, Equal.cong(Cmp, Bool, t => Cmp.is_eq(t), Nat.cmp(a, b), EQ{}, h))

def lt_of_cmp(+a: Nat, +b: Nat, +h: {Nat.cmp(a, b) == LT{} : Cmp}) -> {Nat.is_lt(a, b) == True{} : Bool}:
  Equal.cong(Cmp, Bool, t => Cmp.is_lt(t), Nat.cmp(a, b), LT{}, h)

def lt_of_gt(+a: Nat, +b: Nat, +h: {Nat.cmp(a, b) == GT{} : Cmp}) -> {Nat.is_lt(b, a) == True{} : Bool}:
  lt_of_cmp(b, a, Equal.trans(Cmp, Nat.cmp(b, a), SF.flip(Nat.cmp(a, b)), LT{}, Equal.sym(Cmp, SF.flip(Nat.cmp(a, b)), Nat.cmp(b, a), cmp_flip(a, b)), Equal.cong(Cmp, Cmp, t => SF.flip(t), Nat.cmp(a, b), GT{}, h)))

# two limbs compare lexicographically
def cl_c(+k: Nat, +x1: Nat, +y1: Nat, +x2: Nat, +y2: Nat, +hx1: {C.fits(k, x1) == True{} : Bool}, +hx2: {C.fits(k, x2) == True{} : Bool}, +c: Cmp, +hc: {Nat.cmp(y1, y2) == c : Cmp}) -> {Nat.cmp(Nat.add(x1, C.shift(k, y1)), Nat.add(x2, C.shift(k, y2))) == lex(c, Nat.cmp(x1, x2)) : Cmp}:
  match c:
    case LT{}:
      cmp_lt(Nat.add(x1, C.shift(k, y1)), Nat.add(x2, C.shift(k, y2)), WW.lt_hi(k, x1, y1, x2, y2, hx1, lt_of_cmp(y1, y2, hc)))
    case GT{}:
      cmp_gt(Nat.add(x1, C.shift(k, y1)), Nat.add(x2, C.shift(k, y2)), WW.lt_hi(k, x2, y2, x1, y1, hx2, lt_of_gt(y1, y2, hc)))
    case EQ{}:
      L.subst(Nat, z => {Nat.cmp(Nat.add(x1, C.shift(k, y1)), Nat.add(x2, C.shift(k, z))) == Nat.cmp(x1, x2) : Cmp}, y1, y2, eq_of_cmp(y1, y2, hc), cmp_addr(x1, x2, C.shift(k, y1)))

def cmp_limbs(+k: Nat, +x1: Nat, +y1: Nat, +x2: Nat, +y2: Nat, +hx1: {C.fits(k, x1) == True{} : Bool}, +hx2: {C.fits(k, x2) == True{} : Bool}) -> {Nat.cmp(Nat.add(x1, C.shift(k, y1)), Nat.add(x2, C.shift(k, y2))) == lex(Nat.cmp(y1, y2), Nat.cmp(x1, x2)) : Cmp}:
  cl_c(k, x1, y1, x2, y2, hx1, hx2, Nat.cmp(y1, y2), {==})

def min_le_l(+a: Nat, +b: Nat) -> {Nat.is_le(Nat.min(a, b), a) == True{} : Bool}:
  match a b:
    case 0n _:
      {==}
    case 1n+ +ap 0n:
      {==}
    case 1n+ +ap 1n+ +bp:
      min_le_l(ap, bp)

def min_le_r(+a: Nat, +b: Nat) -> {Nat.is_le(Nat.min(a, b), b) == True{} : Bool}:
  match a b:
    case 0n _:
      N.zero_le(b)
    case 1n+ +ap 0n:
      {==}
    case 1n+ +ap 1n+ +bp:
      min_le_r(ap, bp)

# shift(a, p) = shift(m, shift(a - m, p)) for m <= a
def sh_split(+a: Nat, +m: Nat, +p: Nat, +h: {Nat.is_le(m, a) == True{} : Bool}) -> {C.shift(a, p) == C.shift(m, C.shift(Nat.sub(a, m), p)) : Nat}:
  Equal.trans(Nat, C.shift(a, p), C.shift(Nat.add(m, Nat.sub(a, m)), p), C.shift(m, C.shift(Nat.sub(a, m), p)), Equal.cong(Nat, Nat, z => C.shift(z, p), a, Nat.add(m, Nat.sub(a, m)), Equal.sym(Nat, Nat.add(m, Nat.sub(a, m)), a, N.sub_add(a, m, h))), WW.shift_comp(m, Nat.sub(a, m), p))

# a common scale 2^min cancels
def cmp_min(+a: Nat, +b: Nat, +p: Nat, +q: Nat) -> {Nat.cmp(C.shift(Nat.sub(a, Nat.min(a, b)), p), C.shift(Nat.sub(b, Nat.min(a, b)), q)) == Nat.cmp(C.shift(a, p), C.shift(b, q)) : Cmp}:
  +m = Nat.min(a, b)
  +X0 = C.shift(Nat.sub(a, m), p)
  +Y0 = C.shift(Nat.sub(b, m), q)
  +e1 = Equal.cong(Nat, Cmp, z => Nat.cmp(z, C.shift(b, q)), C.shift(a, p), C.shift(m, X0), sh_split(a, m, p, min_le_l(a, b)))
  +e2 = Equal.cong(Nat, Cmp, z => Nat.cmp(C.shift(m, X0), z), C.shift(b, q), C.shift(m, Y0), sh_split(b, m, q, min_le_r(a, b)))
  Equal.sym(Cmp, Nat.cmp(C.shift(a, p), C.shift(b, q)), Nat.cmp(X0, Y0), Equal.trans(Cmp, Nat.cmp(C.shift(a, p), C.shift(b, q)), Nat.cmp(C.shift(m, X0), C.shift(b, q)), Nat.cmp(X0, Y0), e1, Equal.trans(Cmp, Nat.cmp(C.shift(m, X0), C.shift(b, q)), Nat.cmp(C.shift(m, X0), C.shift(m, Y0)), Nat.cmp(X0, Y0), e2, cmp_shift(m, X0, Y0))))

