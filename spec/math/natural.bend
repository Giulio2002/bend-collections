import Base
import ../lib/common.bend as C
import ../../src/math/natural.bend as M

# Specification of src/math/natural.bend: Python's exact integer functions
# (math.gcd, lcm, isqrt, factorial, perm, comb, prod, the three-argument
# pow, pow(a, -1, m), divmod, int.bit_length) on the natural numbers.
#
# The reference definitions (factorial, desc, choose, lsum, lprod) are
# structural recursions in the shape of Lean 4 Mathlib; the clauses mirror
# Mathlib's statements, the Why3 gallery's (isqrt, fast exponentiation) and
# HACL*'s (Lib.Exponentiation). Python semantics follow
# python_style_math_stdlib_design.pdf: the error model (section 2.3: an
# invalid argument is an error value, never a wrapped or partial result),
# the exact integer functions (4.2), isqrt (8.5), factorial/comb/perm (8.6),
# gcd, modular exponentiation and inverse (8.7), divmod and pow (3.1).
# Divisibility "d divides a" is dvd(d, a): a quotient k with a == k d.
#
#   function     clauses                                         mirrors
#   gcd          Gcd.divides_left, Gcd.divides_right,           Mathlib Nat.gcd_dvd_left/right,
#                Gcd.greatest, Gcd.mul_left                      Nat.dvd_gcd, Nat.gcd_mul_left
#   lcm          Lcm.divides_left, Lcm.divides_right,           Nat.dvd_lcm_left/right,
#                Lcm.least, Lcm.gcd_mul_lcm                      Nat.lcm_dvd, Nat.gcd_mul_lcm
#   gcd_all      GcdAll.divides, GcdAll.greatest                 Finset.gcd_dvd, Finset.dvd_gcd
#   lcm_all      LcmAll.divides, LcmAll.least                    Finset.dvd_lcm, Finset.lcm_dvd
#   sum, prod    Sum.value, Prod.value                           List.sum, List.prod
#   factorial    Factorial.value                                 Nat.factorial_succ
#   perm         Perm.value, Perm.self                           Nat.descFactorial, _self
#   comb         Comb.value, Comb.pascal, Comb.factorials,       Nat.choose_succ_succ,
#                Comb.zero                                       Nat.choose_mul_factorial_mul_factorial,
#                                                                Nat.choose_eq_zero_of_lt
#   isqrt        Isqrt.le, Isqrt.lt_succ                         Nat.sqrt_le', Nat.lt_succ_sqrt'
#   iroot        Iroot.done, Iroot.le, Iroot.lt_succ,            Why3 isqrt generalised;
#                Iroot.zero_degree                               PDF 4.2
#   ilog         Ilog.done, Ilog.pow_le, Ilog.lt_pow_succ,       Nat.pow_log_le_self,
#                Ilog.zero, Ilog.small_base                      Nat.lt_pow_succ_log_self; PDF 4.2
#   bit_length   BitLength.lt, BitLength.le                      Nat.lt_size_self, Nat.size_le
#   pow_mod      PowMod.value, PowMod.zero_modulus               Nat.pow_mod; HACL* Lib.Exponentiation
#   mod_inverse  ModInverse.inverse, ModInverse.reduced,         Nat.gcdA, ZMod.mul_inv_of_unit,
#                ModInverse.not_coprime, ModInverse.zero_modulus Nat.Coprime; PDF 8.7
#   divmod       DivMod.value, DivMod.euclid, DivMod.rem_lt,     Nat.div_add_mod, Nat.mod_lt;
#                DivMod.zero_divisor                             PDF 3.1
#   clamp        Clamp.value, Clamp.ge, Clamp.le, Clamp.id,      PDF 10 (clamp is a gap Python
#                Clamp.domain                                    leaves; lo > hi is a Domain error)
#
# Proved in proofs/math/natural/ (proof.bend, one definition per clause
# under the clause's name).

# ---- reference definitions ----

# Mathlib/Data/Nat/Factorial/Basic (Nat.factorial_succ)
def factorial(n: Nat) -> Nat:
  match n:
    case 0n:
      1n
    case 1n+ +p:
      Nat.mul(1n+p, factorial(p))

# n.descFactorial k: (n - k) * n.descFactorial k at k + 1
def desc(+n: Nat, k: Nat) -> Nat:
  match k:
    case 0n:
      1n
    case 1n+ +j:
      Nat.mul(Nat.sub(n, j), desc(n, j))

# Mathlib/Data/Nat/Choose/Basic (Pascal's rule, Nat.choose_succ_succ)
def choose(n: Nat, k: Nat) -> Nat:
  match n k:
    case 0n 0n:
      1n
    case 0n 1n+j:
      0n
    case 1n+m 0n:
      1n
    case 1n+ +m 1n+ +j:
      Nat.add(choose(m, j), choose(m, 1n+j))

# List.sum and List.prod as right folds
def lsum(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{x, t}:
      Nat.add(x, lsum(t))

def lprod(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      1n
    case Con{x, t}:
      Nat.mul(x, lprod(t))

# d divides a: a quotient k with a == k d (Mathlib's Dvd on Nat)
def dvd(+d: Nat, +a: Nat) -> Type:
  Sigma<&1, &1, Nat, k => {a == Nat.mul(k, d) : Nat}>

# xs[i], or dflt past the end
def nth0(+xs: List<&2, Nat>, +i: Nat, +dflt: Nat) -> Nat:
  match xs i:
    case Nil{} i0:
      dflt
    case Con{x, t} 0n:
      x
    case Con{x, t} 1n+j:
      nth0(t, j, dflt)

# d divides every element, with the quotients given: xs[i] == ks[i] d
def dvd_with(+d: Nat, +xs: List<&2, Nat>, +ks: List<&2, Nat>) -> Type:
  match xs ks:
    case Nil{} Nil{}:
      Unit
    case Nil{} Con{k, kt}:
      Unit
    case Con{x, t} Nil{}:
      Empty
    case Con{+x, +t} Con{+k, +kt}:
      {x == Nat.mul(k, d) : Nat} & dvd_with(d, t, kt)

# m is a multiple of every element, with the quotients given: m == ks[i] xs[i]
def mul_with(+m: Nat, +xs: List<&2, Nat>, +ks: List<&2, Nat>) -> Type:
  match xs ks:
    case Nil{} Nil{}:
      Unit
    case Nil{} Con{k, kt}:
      Unit
    case Con{x, t} Nil{}:
      Empty
    case Con{+x, +t} Con{+k, +kt}:
      {m == Nat.mul(k, x) : Nat} & mul_with(m, t, kt)

# ---- gcd, lcm ----

def Gcd.divides_left(+a: Nat, +b: Nat) -> Type:
  dvd(M.gcd(a, b), a)

def Gcd.divides_right(+a: Nat, +b: Nat) -> Type:
  dvd(M.gcd(a, b), b)

# every common divisor divides the gcd
def Gcd.greatest(+a: Nat, +b: Nat, +d: Nat, +ka: Nat, +kb: Nat, +ea: {a == Nat.mul(ka, d) : Nat}, +eb: {b == Nat.mul(kb, d) : Nat}) -> Type:
  dvd(d, M.gcd(a, b))

def Gcd.mul_left(+c: Nat, +a: Nat, +b: Nat) -> Type:
  {M.gcd(Nat.mul(c, a), Nat.mul(c, b)) == Nat.mul(c, M.gcd(a, b)) : Nat}

def Lcm.divides_left(+a: Nat, +b: Nat) -> Type:
  dvd(a, M.lcm(a, b))

def Lcm.divides_right(+a: Nat, +b: Nat) -> Type:
  dvd(b, M.lcm(a, b))

# the lcm divides every common multiple
def Lcm.least(+a: Nat, +b: Nat, +m: Nat, +x: Nat, +y: Nat, +ex: {m == Nat.mul(x, a) : Nat}, +ey: {m == Nat.mul(y, b) : Nat}) -> Type:
  dvd(M.lcm(a, b), m)

def Lcm.gcd_mul_lcm(+a: Nat, +b: Nat) -> Type:
  {Nat.mul(M.gcd(a, b), M.lcm(a, b)) == Nat.mul(a, b) : Nat}

# ---- lists ----

def GcdAll.divides(+xs: List<&2, Nat>, +i: Nat) -> Type:
  dvd(M.gcd_all(xs), nth0(xs, i, 0n))

def GcdAll.greatest(+d: Nat, +xs: List<&2, Nat>, +ks: List<&2, Nat>, h: dvd_with(d, xs, ks)) -> Type:
  dvd(d, M.gcd_all(xs))

def LcmAll.divides(+xs: List<&2, Nat>, +i: Nat) -> Type:
  dvd(nth0(xs, i, 1n), M.lcm_all(xs))

def LcmAll.least(+m: Nat, +xs: List<&2, Nat>, +ks: List<&2, Nat>, h: mul_with(m, xs, ks)) -> Type:
  dvd(M.lcm_all(xs), m)

def Sum.value(+xs: List<&2, Nat>) -> Type:
  {M.sum(xs) == lsum(xs) : Nat}

def Prod.value(+xs: List<&2, Nat>) -> Type:
  {M.prod(xs) == lprod(xs) : Nat}

# ---- factorial, perm, comb ----

def Factorial.value(+n: Nat) -> Type:
  {M.factorial(n) == factorial(n) : Nat}

def Perm.value(+n: Nat, +k: Nat) -> Type:
  {M.perm(n, k) == desc(n, k) : Nat}

def Perm.self(+n: Nat) -> Type:
  {M.perm(n, n) == factorial(n) : Nat}

def Comb.value(+n: Nat, +k: Nat) -> Type:
  {M.comb(n, k) == choose(n, k) : Nat}

# Pascal's rule on the implementation itself
def Comb.pascal(+m: Nat, +j: Nat) -> Type:
  {M.comb(1n+m, 1n+j) == Nat.add(M.comb(m, j), M.comb(m, 1n+j)) : Nat}

def Comb.factorials(+n: Nat, +k: Nat, +h: {Nat.is_le(k, n) == True{} : Bool}) -> Type:
  {Nat.mul(M.comb(n, k), Nat.mul(factorial(k), factorial(Nat.sub(n, k)))) == factorial(n) : Nat}

# PDF 8.6: comb(n, k) is 0 for k > n, not an error
def Comb.zero(+n: Nat, +k: Nat, +h: {Nat.is_lt(n, k) == True{} : Bool}) -> Type:
  {M.comb(n, k) == 0n : Nat}

# ---- roots, logarithms, bits ----

def Isqrt.le(+n: Nat) -> Type:
  {Nat.is_le(Nat.pow(M.isqrt(n), 2n), n) == True{} : Bool}

def Isqrt.lt_succ(+n: Nat) -> Type:
  {Nat.is_lt(n, Nat.pow(1n+M.isqrt(n), 2n)) == True{} : Bool}

# a positive degree always has a root
def Iroot.done(+n: Nat, +kp: Nat) -> Type:
  Sigma<&1, &1, Nat, r => {M.iroot(n, 1n+kp) == Done{r} : Result<&2, &2, M.MathError, Nat>}>

def Iroot.le(+n: Nat, +kp: Nat, +r: Nat, +h: {M.iroot(n, 1n+kp) == Done{r} : Result<&2, &2, M.MathError, Nat>}) -> Type:
  {Nat.is_le(Nat.pow(r, 1n+kp), n) == True{} : Bool}

def Iroot.lt_succ(+n: Nat, +kp: Nat, +r: Nat, +h: {M.iroot(n, 1n+kp) == Done{r} : Result<&2, &2, M.MathError, Nat>}) -> Type:
  {Nat.is_lt(n, Nat.pow(1n+r, 1n+kp)) == True{} : Bool}

# PDF 2.3: the zeroth root is a domain error
def Iroot.zero_degree(+n: Nat) -> Type:
  {M.iroot(n, 0n) == Fail{M.Domain{}} : Result<&2, &2, M.MathError, Nat>}

# a positive argument and a base of at least 2 always have a logarithm
def Ilog.done(+np: Nat, +bq: Nat) -> Type:
  Sigma<&1, &1, Nat, r => {M.ilog(1n+np, 2n+bq) == Done{r} : Result<&2, &2, M.MathError, Nat>}>

def Ilog.pow_le(+np: Nat, +bq: Nat, +r: Nat, +h: {M.ilog(1n+np, 2n+bq) == Done{r} : Result<&2, &2, M.MathError, Nat>}) -> Type:
  {Nat.is_le(Nat.pow(2n+bq, r), 1n+np) == True{} : Bool}

def Ilog.lt_pow_succ(+np: Nat, +bq: Nat, +r: Nat, +h: {M.ilog(1n+np, 2n+bq) == Done{r} : Result<&2, &2, M.MathError, Nat>}) -> Type:
  {Nat.is_lt(1n+np, Nat.pow(2n+bq, 1n+r)) == True{} : Bool}

# PDF 2.3 / 4.5: log(0) is a domain error, as is a base below 2
def Ilog.zero(+b: Nat) -> Type:
  {M.ilog(0n, b) == Fail{M.Domain{}} : Result<&2, &2, M.MathError, Nat>}

def Ilog.small_base(+n: Nat, +b: Nat, +hb: {Nat.is_lt(b, 2n) == True{} : Bool}) -> Type:
  {M.ilog(n, b) == Fail{M.Domain{}} : Result<&2, &2, M.MathError, Nat>}

def BitLength.lt(+n: Nat) -> Type:
  {Nat.is_lt(n, C.pow2(M.bit_length(n))) == True{} : Bool}

def BitLength.le(+np: Nat) -> Type:
  {Nat.is_le(C.pow2(M.bit_length(1n+np)), Nat.double(1n+np)) == True{} : Bool}

# ---- modular arithmetic ----

def PowMod.value(+b: Nat, +e: Nat, +mp: Nat) -> Type:
  {M.pow_mod(b, e, 1n+mp) == Done{Nat.mod(Nat.pow(b, e), 1n+mp)} : Result<&2, &2, M.MathError, Nat>}

# PDF 8.7: pow(b, e, 0) raises ValueError; here ZeroDivision
def PowMod.zero_modulus(+b: Nat, +e: Nat) -> Type:
  {M.pow_mod(b, e, 0n) == Fail{M.ZeroDivision{}} : Result<&2, &2, M.MathError, Nat>}

def ModInverse.inverse(+a: Nat, +mp: Nat, +x: Nat, +h: {M.mod_inverse(a, 1n+mp) == Done{x} : Result<&2, &2, M.MathError, Nat>}) -> Type:
  {Nat.mod(Nat.mul(a, x), 1n+mp) == Nat.mod(1n, 1n+mp) : Nat}

def ModInverse.reduced(+a: Nat, +mp: Nat, +x: Nat, +h: {M.mod_inverse(a, 1n+mp) == Done{x} : Result<&2, &2, M.MathError, Nat>}) -> Type:
  {Nat.is_lt(x, 1n+mp) == True{} : Bool}

# PDF 8.7: no inverse exactly when a and m share a factor g >= 2
def ModInverse.not_coprime(+a: Nat, +mp: Nat, +h: {M.mod_inverse(a, 1n+mp) == Fail{M.NotInvertible{}} : Result<&2, &2, M.MathError, Nat>}) -> Type:
  Sigma<&1, &1, Nat, g => {Nat.is_le(2n, g) == True{} : Bool} & (dvd(g, a) & dvd(g, 1n+mp))>

def ModInverse.zero_modulus(+a: Nat) -> Type:
  {M.mod_inverse(a, 0n) == Fail{M.ZeroDivision{}} : Result<&2, &2, M.MathError, Nat>}

# ---- divmod and clamp ----

def DivMod.value(+a: Nat, +bp: Nat) -> Type:
  {M.divmod(a, 1n+bp) == Done{M.QR{Nat.div(a, 1n+bp), Nat.mod(a, 1n+bp)}} : Result<&2, &2, M.MathError, M.QuotRem>}

def DivMod.euclid(+a: Nat, +bp: Nat) -> Type:
  {a == Nat.add(Nat.mul(Nat.div(a, 1n+bp), 1n+bp), Nat.mod(a, 1n+bp)) : Nat}

def DivMod.rem_lt(+a: Nat, +bp: Nat) -> Type:
  {Nat.is_lt(Nat.mod(a, 1n+bp), 1n+bp) == True{} : Bool}

# PDF 3.1: divmod(a, 0) raises ZeroDivisionError
def DivMod.zero_divisor(+a: Nat) -> Type:
  {M.divmod(a, 0n) == Fail{M.ZeroDivision{}} : Result<&2, &2, M.MathError, M.QuotRem>}

def Clamp.value(+x: Nat, +lo: Nat, +hi: Nat, +h: {Nat.is_le(lo, hi) == True{} : Bool}) -> Type:
  {M.clamp(x, lo, hi) == Done{Nat.min(Nat.max(x, lo), hi)} : Result<&2, &2, M.MathError, Nat>}

def Clamp.ge(+x: Nat, +lo: Nat, +hi: Nat, +h: {Nat.is_le(lo, hi) == True{} : Bool}) -> Type:
  {Nat.is_le(lo, Nat.min(Nat.max(x, lo), hi)) == True{} : Bool}

def Clamp.le(+x: Nat, +lo: Nat, +hi: Nat) -> Type:
  {Nat.is_le(Nat.min(Nat.max(x, lo), hi), hi) == True{} : Bool}

def Clamp.id(+x: Nat, +lo: Nat, +hi: Nat, +h1: {Nat.is_le(lo, x) == True{} : Bool}, +h2: {Nat.is_le(x, hi) == True{} : Bool}) -> Type:
  {Nat.min(Nat.max(x, lo), hi) == x : Nat}

def Clamp.domain(+x: Nat, +lo: Nat, +hi: Nat, +h: {Nat.is_lt(hi, lo) == True{} : Bool}) -> Type:
  {M.clamp(x, lo, hi) == Fail{M.Domain{}} : Result<&2, &2, M.MathError, Nat>}
