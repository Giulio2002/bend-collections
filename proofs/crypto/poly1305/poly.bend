import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/crypto/poly1305.bend as R
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../../math/natural/arith.bend as NR
import ./modp.bend as MP
import ./mac.bend as M

# The accumulator of spec/crypto/poly1305.bend (reduced mod p after every
# block) is the polynomial of the blocks evaluated at r, reduced once:
#   absorb(bs, r, 0) == poly(bs, r) mod (2^130 - 5)
# (Horner's rule, then "reduction commutes with + and *", Mathlib's
# Nat.add_mod / Nat.mul_mod; the modulus is written 1 + bp throughout, with
# 1 + bp == 2^130 - 5 from modp.bend).

# Horner's rule without reduction.
def horner(bs: List<&2, List<&2, U32>>, +r: Nat, a: Nat) -> Nat:
  match bs:
    case Nil{}: a
    case b <> rest: horner(rest, r, Nat.mul(r, Nat.add(a, R.coeff(b))))

def len(+bs: List<&2, List<&2, U32>>) -> Nat:
  List.length(&2, List<&2, U32>, bs)

# (r (a + n)) X == a (r X) + n (r X)
law step_alg:
  for +r: Nat
  for +a: Nat
  for +n: Nat
  for +x: Nat
  for +p: Nat
  {Nat.add(Nat.mul(Nat.mul(r, Nat.add(a, n)), x), p) == Nat.add(Nat.mul(a, Nat.mul(r, x)), Nat.add(Nat.mul(n, Nat.mul(r, x)), p)) : Nat}

def step_alg(r, a, n, x, p):
  +RX = Nat.mul(r, x)
  +e1 = Equal.trans(Nat, Nat.mul(Nat.mul(r, Nat.add(a, n)), x), Nat.mul(Nat.mul(Nat.add(a, n), r), x), Nat.mul(Nat.add(a, n), RX),
    Equal.cong(Nat, Nat, z => Nat.mul(z, x), Nat.mul(r, Nat.add(a, n)), Nat.mul(Nat.add(a, n), r), NA.mul_comm(r, Nat.add(a, n))),
    NA.mul_assoc(Nat.add(a, n), r, x))
  +e2 = Equal.trans(Nat, Nat.mul(Nat.mul(r, Nat.add(a, n)), x), Nat.mul(Nat.add(a, n), RX), Nat.add(Nat.mul(a, RX), Nat.mul(n, RX)), e1, NA.mul_add_right(a, n, RX))
  Equal.trans(Nat, Nat.add(Nat.mul(Nat.mul(r, Nat.add(a, n)), x), p), Nat.add(Nat.add(Nat.mul(a, RX), Nat.mul(n, RX)), p), Nat.add(Nat.mul(a, RX), Nat.add(Nat.mul(n, RX), p)),
    Equal.cong(Nat, Nat, z => Nat.add(z, p), Nat.mul(Nat.mul(r, Nat.add(a, n)), x), Nat.add(Nat.mul(a, RX), Nat.mul(n, RX)), e2),
    NA.add_assoc(Nat.mul(a, RX), Nat.mul(n, RX), p))

# horner(bs, r, a) == a r^q + poly(bs, r)
law horner_poly:
  for +bs: List<&2, List<&2, U32>>
  for +r: Nat
  for +a: Nat
  {horner(bs, r, a) == Nat.add(Nat.mul(a, Nat.pow(r, len(bs))), R.poly(bs, r)) : Nat}

def horner_poly(bs, r, a):
  match bs:
    case Nil{}:
      Equal.sym(Nat, Nat.add(Nat.mul(a, 1n), 0n), a, Equal.trans(Nat, Nat.add(Nat.mul(a, 1n), 0n), Nat.mul(a, 1n), a, NA.add_zero(Nat.mul(a, 1n)), NA.mul_one(a)))
    case b <> rest:
      +x = Nat.mul(r, Nat.add(a, R.coeff(b)))
      Equal.trans(Nat, horner(rest, r, x), Nat.add(Nat.mul(x, Nat.pow(r, len(rest))), R.poly(rest, r)), Nat.add(Nat.mul(a, Nat.mul(r, Nat.pow(r, len(rest)))), Nat.add(Nat.mul(R.coeff(b), Nat.mul(r, Nat.pow(r, len(rest)))), R.poly(rest, r))),
        horner_poly(rest, r, x),
        step_alg(r, a, R.coeff(b), Nat.pow(r, len(rest)), R.poly(rest, r)))

# horner only depends on its start value mod n.
law horner_mod:
  for +bp: Nat
  for +bs: List<&2, List<&2, U32>>
  for +r: Nat
  for +x: Nat
  {Nat.mod(horner(bs, r, Nat.mod(x, 1n+bp)), 1n+bp) == Nat.mod(horner(bs, r, x), 1n+bp) : Nat}

def next_mod(+bp: Nat, +r: Nat, +x: Nat, +n: Nat) -> {Nat.mod(Nat.mul(r, Nat.add(Nat.mod(x, 1n+bp), n)), 1n+bp) == Nat.mod(Nat.mul(r, Nat.add(x, n)), 1n+bp) : Nat}:
  +m = {1n+bp : Nat}
  Equal.trans(Nat, Nat.mod(Nat.mul(r, Nat.add(Nat.mod(x, m), n)), m), Nat.mod(Nat.mul(r, Nat.mod(Nat.add(Nat.mod(x, m), n), m)), m), Nat.mod(Nat.mul(r, Nat.add(x, n)), m),
    Equal.sym(Nat, Nat.mod(Nat.mul(r, Nat.mod(Nat.add(Nat.mod(x, m), n), m)), m), Nat.mod(Nat.mul(r, Nat.add(Nat.mod(x, m), n)), m), NR.mod_mul_r(bp, r, Nat.add(Nat.mod(x, m), n))),
    Equal.trans(Nat, Nat.mod(Nat.mul(r, Nat.mod(Nat.add(Nat.mod(x, m), n), m)), m), Nat.mod(Nat.mul(r, Nat.mod(Nat.add(x, n), m)), m), Nat.mod(Nat.mul(r, Nat.add(x, n)), m),
      Equal.cong(Nat, Nat, z => Nat.mod(Nat.mul(r, z), m), Nat.mod(Nat.add(Nat.mod(x, m), n), m), Nat.mod(Nat.add(x, n), m), NR.mod_add_l(bp, x, n)),
      NR.mod_mul_r(bp, r, Nat.add(x, n))))

def horner_mod(bp, bs, r, x):
  match bs:
    case Nil{}: NR.mod_mod(bp, x)
    case b <> rest:
      +m = {1n+bp : Nat}
      +y1 = Nat.mul(r, Nat.add(Nat.mod(x, m), R.coeff(b)))
      +y2 = Nat.mul(r, Nat.add(x, R.coeff(b)))
      Equal.trans(Nat, Nat.mod(horner(rest, r, y1), m), Nat.mod(horner(rest, r, Nat.mod(y1, m)), m), Nat.mod(horner(rest, r, y2), m),
        Equal.sym(Nat, Nat.mod(horner(rest, r, Nat.mod(y1, m)), m), Nat.mod(horner(rest, r, y1), m), horner_mod(bp, rest, r, y1)),
        Equal.trans(Nat, Nat.mod(horner(rest, r, Nat.mod(y1, m)), m), Nat.mod(horner(rest, r, Nat.mod(y2, m)), m), Nat.mod(horner(rest, r, y2), m),
          Equal.cong(Nat, Nat, z => Nat.mod(horner(rest, r, z), m), Nat.mod(y1, m), Nat.mod(y2, m), next_mod(bp, r, x, R.coeff(b))),
          horner_mod(bp, rest, r, y2)))

# absorb(bs, r, a) == horner(bs, r, a) mod p, for a < p.
law absorb_horner:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  for +bs: List<&2, List<&2, U32>>
  for +r: Nat
  for +a: Nat
  for +ha: {Nat.is_lt(a, 1n+M.bpv(one)) == True{} : Bool}
  {R.absorb(bs, r, a) == Nat.mod(horner(bs, r, a), 1n+M.bpv(one)) : Nat}

def absorb_horner(one, h1, bs, r, a, ha):
  match bs:
    case Nil{}: Equal.sym(Nat, Nat.mod(a, 1n+M.bpv(one)), a, NR.mod_of(0n, M.bpv(one), a, ha))
    case b <> rest:
      +bp = M.bpv(one)
      +m = {1n+bp : Nat}
      +y = Nat.mul(r, Nat.add(a, R.coeff(b)))
      +em = MP.modp_mod(one, h1, bp, M.bp5(one, h1), y)
      Equal.trans(Nat, R.absorb(rest, r, R.modp(y)), R.absorb(rest, r, Nat.mod(y, m)), Nat.mod(horner(rest, r, y), m),
        Equal.cong(Nat, Nat, z => R.absorb(rest, r, z), R.modp(y), Nat.mod(y, m), em),
        Equal.trans(Nat, R.absorb(rest, r, Nat.mod(y, m)), Nat.mod(horner(rest, r, Nat.mod(y, m)), m), Nat.mod(horner(rest, r, y), m),
          absorb_horner(one, h1, rest, r, Nat.mod(y, m), NR.dm_lt(bp, y)),
          horner_mod(bp, rest, r, y)))

# The accumulator is the polynomial at r, reduced mod 2^130 - 5.
law absorb_poly:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  for +bs: List<&2, List<&2, U32>>
  for +r: Nat
  {R.absorb(bs, r, 0n) == Nat.mod(R.poly(bs, r), Nat.sub(C.shift(130n, one), 5n)) : Nat}

def absorb_poly(one, h1, bs, r):
  +m = {1n+M.bpv(one) : Nat}
  Equal.trans(Nat, R.absorb(bs, r, 0n), Nat.mod(horner(bs, r, 0n), m), Nat.mod(R.poly(bs, r), Nat.sub(C.shift(130n, one), 5n)),
    absorb_horner(one, h1, bs, r, 0n, {==}),
    Equal.trans(Nat, Nat.mod(horner(bs, r, 0n), m), Nat.mod(R.poly(bs, r), m), Nat.mod(R.poly(bs, r), Nat.sub(C.shift(130n, one), 5n)),
      Equal.cong(Nat, Nat, z => Nat.mod(z, m), horner(bs, r, 0n), R.poly(bs, r), horner_poly(bs, r, 0n)),
      Equal.cong(Nat, Nat, z => Nat.mod(R.poly(bs, r), z), m, Nat.sub(C.shift(130n, one), 5n), Equal.sym(Nat, Nat.sub(C.shift(130n, one), 5n), m, M.pp_eq(one, h1, M.bpv(one), M.bp5(one, h1))))))
