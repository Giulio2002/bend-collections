import Base
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/lemmas/proofs/nat_algebra.bend as A
import ../../../src/math/natural.bend as M
import ./arith.bend as R
import ./lcm.bend as LC
import ./bits.bend as B

# pow_mod(b, e, m) == Done{b^e mod m} for m > 0, ZeroDivision for m == 0.
# The spec is Lean 4 Mathlib's Nat.pow_mod and the functional
# correctness statement of HACL*'s Lib.NatMod / Hacl.Spec.Exponentiation
# (exp_lr / exp_rl equal pow modulo n); the proof is the right-to-left
# binary-exponentiation invariant acc * base^e == b^e0 (mod m) of the Why3
# gallery's fast_exponentiation.

# (x mod m)^k == x^k (mod m)   (Mathlib Nat.pow_mod)
def mod_pow(+mp: Nat, +x: Nat, +k: Nat) -> {Nat.mod(Nat.pow(Nat.mod(x, 1n+mp), k), 1n+mp) == Nat.mod(Nat.pow(x, k), 1n+mp) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+ +kp:
      +m = {1n+mp : Nat}
      +y = Nat.mod(x, m)
      Equal.trans(Nat, Nat.mod(Nat.mul(y, Nat.pow(y, kp)), m), Nat.mod(Nat.mul(x, Nat.pow(y, kp)), m), Nat.mod(Nat.mul(x, Nat.pow(x, kp)), m), R.mod_mul_l(mp, x, Nat.pow(y, kp)),
        Equal.trans(Nat, Nat.mod(Nat.mul(x, Nat.pow(y, kp)), m), Nat.mod(Nat.mul(x, Nat.mod(Nat.pow(y, kp), m)), m), Nat.mod(Nat.mul(x, Nat.pow(x, kp)), m), Equal.sym(Nat, Nat.mod(Nat.mul(x, Nat.mod(Nat.pow(y, kp), m)), m), Nat.mod(Nat.mul(x, Nat.pow(y, kp)), m), R.mod_mul_r(mp, x, Nat.pow(y, kp))),
          Equal.trans(Nat, Nat.mod(Nat.mul(x, Nat.mod(Nat.pow(y, kp), m)), m), Nat.mod(Nat.mul(x, Nat.mod(Nat.pow(x, kp), m)), m), Nat.mod(Nat.mul(x, Nat.pow(x, kp)), m), Equal.cong(Nat, Nat, z => Nat.mod(Nat.mul(x, z), m), Nat.mod(Nat.pow(y, kp), m), Nat.mod(Nat.pow(x, kp), m), mod_pow(mp, x, kp)), R.mod_mul_r(mp, x, Nat.pow(x, kp)))))

# x^(2 y) == (x x)^y
def pow_double(+x: Nat, +y: Nat) -> {Nat.pow(x, Nat.double(y)) == Nat.pow(Nat.mul(x, x), y) : Nat}:
  match y:
    case 0n:
      {==}
    case 1n+ +yp:
      Equal.trans(Nat, Nat.mul(x, Nat.mul(x, Nat.pow(x, Nat.double(yp)))), Nat.mul(Nat.mul(x, x), Nat.pow(x, Nat.double(yp))), Nat.mul(Nat.mul(x, x), Nat.pow(Nat.mul(x, x), yp)),
        Equal.sym(Nat, Nat.mul(Nat.mul(x, x), Nat.pow(x, Nat.double(yp))), Nat.mul(x, Nat.mul(x, Nat.pow(x, Nat.double(yp)))), A.mul_assoc(x, x, Nat.pow(x, Nat.double(yp)))),
        Equal.cong(Nat, Nat, z => Nat.mul(Nat.mul(x, x), z), Nat.pow(x, Nat.double(yp)), Nat.pow(Nat.mul(x, x), yp), pow_double(x, yp)))

# the squared base, reduced, is x^(2 e2) under any factor c
def same_sq(+mp: Nat, +c: Nat, +base: Nat, +e2: Nat) -> {Nat.mod(Nat.mul(c, Nat.pow(Nat.mod(Nat.mul(base, base), 1n+mp), e2)), 1n+mp) == Nat.mod(Nat.mul(c, Nat.pow(base, Nat.double(e2))), 1n+mp) : Nat}:
  +m = {1n+mp : Nat}
  +bb = Nat.mul(base, base)
  +x = Nat.pow(Nat.mod(bb, m), e2)
  %Equal.sym(Nat, Nat.pow(base, Nat.double(e2)), Nat.pow(bb, e2), pow_double(base, e2)) : {Nat.mod(Nat.mul(c, x), m) == Nat.mod(Nat.mul(c, _), m) : Nat}
  Equal.trans(Nat, Nat.mod(Nat.mul(c, x), m), Nat.mod(Nat.mul(c, Nat.mod(x, m)), m), Nat.mod(Nat.mul(c, Nat.pow(bb, e2)), m), Equal.sym(Nat, Nat.mod(Nat.mul(c, Nat.mod(x, m)), m), Nat.mod(Nat.mul(c, x), m), R.mod_mul_r(mp, c, x)),
    Equal.trans(Nat, Nat.mod(Nat.mul(c, Nat.mod(x, m)), m), Nat.mod(Nat.mul(c, Nat.mod(Nat.pow(bb, e2), m)), m), Nat.mod(Nat.mul(c, Nat.pow(bb, e2)), m), Equal.cong(Nat, Nat, z => Nat.mod(Nat.mul(c, z), m), Nat.mod(x, m), Nat.mod(Nat.pow(bb, e2), m), mod_pow(mp, bb, e2)), R.mod_mul_r(mp, c, Nat.pow(bb, e2))))

# one step: the odd bit multiplies acc by base
def pm_bit(+mp: Nat, +e2: Nat, +bit: Nat, +hbit: {Nat.is_lt(bit, 2n) == True{} : Bool}, +base: Nat, +acc: Nat) -> {Nat.mod(Nat.mul(M.pow_mod_odd(1n+mp, bit, base, acc), Nat.pow(Nat.mod(Nat.mul(base, base), 1n+mp), e2)), 1n+mp) == Nat.mod(Nat.mul(acc, Nat.pow(base, Nat.add(Nat.double(e2), bit))), 1n+mp) : Nat}:
  match bit:
    case 0n:
      %Equal.sym(Nat, Nat.add(Nat.double(e2), 0n), Nat.double(e2), A.add_zero(Nat.double(e2))) : {Nat.mod(Nat.mul(acc, Nat.pow(Nat.mod(Nat.mul(base, base), 1n+mp), e2)), 1n+mp) == Nat.mod(Nat.mul(acc, Nat.pow(base, _)), 1n+mp) : Nat}
      same_sq(mp, acc, base, e2)
    case 1n:
      +m = {1n+mp : Nat}
      +d = Nat.double(e2)
      +x = Nat.pow(Nat.mod(Nat.mul(base, base), m), e2)
      %Equal.sym(Nat, Nat.pow(base, Nat.add(d, 1n)), Nat.mul(Nat.pow(base, d), Nat.pow(base, 1n)), R.pow_add(base, d, 1n)) : {Nat.mod(Nat.mul(Nat.mod(Nat.mul(acc, base), m), x), m) == Nat.mod(Nat.mul(acc, _), m) : Nat}
      %Equal.sym(Nat, Nat.pow(base, 1n), base, A.mul_one(base)) : {Nat.mod(Nat.mul(Nat.mod(Nat.mul(acc, base), m), x), m) == Nat.mod(Nat.mul(acc, Nat.mul(Nat.pow(base, d), _)), m) : Nat}
      %Equal.sym(Nat, Nat.mul(acc, Nat.mul(Nat.pow(base, d), base)), Nat.mul(Nat.mul(acc, base), Nat.pow(base, d)), Equal.trans(Nat, Nat.mul(acc, Nat.mul(Nat.pow(base, d), base)), Nat.mul(acc, Nat.mul(base, Nat.pow(base, d))), Nat.mul(Nat.mul(acc, base), Nat.pow(base, d)), Equal.cong(Nat, Nat, z => Nat.mul(acc, z), Nat.mul(Nat.pow(base, d), base), Nat.mul(base, Nat.pow(base, d)), A.mul_comm(Nat.pow(base, d), base)), Equal.sym(Nat, Nat.mul(Nat.mul(acc, base), Nat.pow(base, d)), Nat.mul(acc, Nat.mul(base, Nat.pow(base, d))), A.mul_assoc(acc, base, Nat.pow(base, d))))) : {Nat.mod(Nat.mul(Nat.mod(Nat.mul(acc, base), m), x), m) == Nat.mod(_, m) : Nat}
      Equal.trans(Nat, Nat.mod(Nat.mul(Nat.mod(Nat.mul(acc, base), m), x), m), Nat.mod(Nat.mul(Nat.mul(acc, base), x), m), Nat.mod(Nat.mul(Nat.mul(acc, base), Nat.pow(base, d)), m), R.mod_mul_l(mp, Nat.mul(acc, base), x), same_sq(mp, Nat.mul(acc, base), base, e2))
    case 2n+z:
      Empty.absurd({Nat.mod(Nat.mul(M.pow_mod_odd(1n+mp, 2n+z, base, acc), Nat.pow(Nat.mod(Nat.mul(base, base), 1n+mp), e2)), 1n+mp) == Nat.mod(Nat.mul(acc, Nat.pow(base, Nat.add(Nat.double(e2), 2n+z))), 1n+mp) : Nat}, N.lt_zero_absurd(z, hbit))

def odd_lt(+mp: Nat, +bit: Nat, +base: Nat, +acc: Nat, +hacc: {Nat.is_lt(acc, 1n+mp) == True{} : Bool}) -> {Nat.is_lt(M.pow_mod_odd(1n+mp, bit, base, acc), 1n+mp) == True{} : Bool}:
  match bit:
    case 0n:
      hacc
    case 1n+z:
      R.dm_lt(mp, Nat.mul(acc, base))

# the loop: acc < m, e <= fuel give pow_mod_go == acc base^e mod m
def pm_go(fuel: Nat, +mp: Nat, +e: Nat, +base: Nat, +acc: Nat, +he: {Nat.is_le(e, fuel) == True{} : Bool}, +hacc: {Nat.is_lt(acc, 1n+mp) == True{} : Bool}) -> {M.pow_mod_go(fuel, 1n+mp, e, base, acc) == Nat.mod(Nat.mul(acc, Nat.pow(base, e)), 1n+mp) : Nat}:
  match fuel e:
    case 0n 0n:
      %Equal.sym(Nat, Nat.mul(acc, 1n), acc, A.mul_one(acc)) : {acc == Nat.mod(_, 1n+mp) : Nat}
      Equal.sym(Nat, Nat.mod(acc, 1n+mp), acc, R.mod_of(0n, mp, acc, hacc))
    case 0n 1n+ep:
      Empty.absurd({M.pow_mod_go(0n, 1n+mp, 1n+ep, base, acc) == Nat.mod(Nat.mul(acc, Nat.pow(base, 1n+ep)), 1n+mp) : Nat}, L.false_true(he))
    case 1n+f 0n:
      %Equal.sym(Nat, Nat.mul(acc, 1n), acc, A.mul_one(acc)) : {acc == Nat.mod(_, 1n+mp) : Nat}
      Equal.sym(Nat, Nat.mod(acc, 1n+mp), acc, R.mod_of(0n, mp, acc, hacc))
    case 1n+ +f 1n+ +ep:
      +m = {1n+mp : Nat}
      +e2 = Nat.div(1n+ep, 2n)
      +bit = Nat.mod(1n+ep, 2n)
      +b2 = Nat.mod(Nat.mul(base, base), m)
      +acc2 = M.pow_mod_odd(m, bit, base, acc)
      +ih = pm_go(f, mp, e2, b2, acc2, N.le_trans(e2, ep, f, N.lt_succ_le(e2, ep, B.half_lt(ep)), he), odd_lt(mp, bit, base, acc, hacc))
      %Equal.sym(Nat, 1n+ep, Nat.add(Nat.double(e2), bit), B.half_eq(1n+ep)) : {M.pow_mod_go(f, m, e2, b2, acc2) == Nat.mod(Nat.mul(acc, Nat.pow(base, _)), m) : Nat}
      Equal.trans(Nat, M.pow_mod_go(f, m, e2, b2, acc2), Nat.mod(Nat.mul(acc2, Nat.pow(b2, e2)), m), Nat.mod(Nat.mul(acc, Nat.pow(base, Nat.add(Nat.double(e2), bit))), m), ih, pm_bit(mp, e2, bit, B.half_rem(1n+ep), base, acc))

# pow_mod(b, e, m) == Done{b^e mod m}   (Mathlib Nat.pow_mod; Python pow(b, e, m))
def pow_mod_ok(+b: Nat, +e: Nat, +mp: Nat) -> {M.pow_mod(b, e, 1n+mp) == Done{Nat.mod(Nat.pow(b, e), 1n+mp)} : Result<&2, &2, M.MathError, Nat>}:
  +m = {1n+mp : Nat}
  +v = Equal.trans(Nat, M.pow_mod_go(e, m, e, Nat.mod(b, m), Nat.mod(1n, m)), Nat.mod(Nat.mul(Nat.mod(1n, m), Nat.pow(Nat.mod(b, m), e)), m), Nat.mod(Nat.pow(b, e), m), pm_go(e, mp, e, Nat.mod(b, m), Nat.mod(1n, m), N.le_refl(e), R.dm_lt(mp, 1n)),
    Equal.trans(Nat, Nat.mod(Nat.mul(Nat.mod(1n, m), Nat.pow(Nat.mod(b, m), e)), m), Nat.mod(Nat.mul(1n, Nat.pow(Nat.mod(b, m), e)), m), Nat.mod(Nat.pow(b, e), m), R.mod_mul_l(mp, 1n, Nat.pow(Nat.mod(b, m), e)),
      Equal.trans(Nat, Nat.mod(Nat.mul(1n, Nat.pow(Nat.mod(b, m), e)), m), Nat.mod(Nat.pow(Nat.mod(b, m), e), m), Nat.mod(Nat.pow(b, e), m), Equal.cong(Nat, Nat, z => Nat.mod(z, m), Nat.mul(1n, Nat.pow(Nat.mod(b, m), e)), Nat.pow(Nat.mod(b, m), e), LC.one_mul(Nat.pow(Nat.mod(b, m), e))), mod_pow(mp, b, e))))
  Equal.cong(Nat, Result<&2, &2, M.MathError, Nat>, z => Done{z}, M.pow_mod_go(e, m, e, Nat.mod(b, m), Nat.mod(1n, m)), Nat.mod(Nat.pow(b, e), m), v)

def pow_mod_zero(+b: Nat, +e: Nat) -> {M.pow_mod(b, e, 0n) == Fail{M.ZeroDivision{}} : Result<&2, &2, M.MathError, Nat>}:
  {==}
