# secp256k1 group law: plan, method, status

Goal: prove the elliptic-curve group law for the specification
`spec/crypto/secp256k1/curve.bend` (complete projective Renes-Costello-Batina
addition `padd`, doubling `pdbl`, MSB-first double-and-add `pmul`) so that
faster scalar multiplication (tables, windows, wNAF, Shamir/Strauss, GLV) can
be proved equal to the specification, and so that ECDSA's
`verify(pk(sk), m, sign(sk, m))` and `recover` can be proved.

## What the checker can and cannot do (measured, Bend 2.0.34, `bend-local`)

- `Nat` is unary and `U32` is a 32-cell bit list inside the checker: a loop of
  12 000 `U32` multiply-adds takes 30 s. No 256-bit constant may be written as
  a closed `Nat` (the spec keeps `one` symbolic for that reason).
- Closed computation on *binary* data types defined in the proof is fast:
  32 modular squarings of 256-bit numbers (a little-endian bit type `Bn`,
  shift-and-add product, bit-serial remainder) check in 6 s and 217 MB.
- Proof by reflection works: a sparse polynomial normalizer written in Bend
  (sorted term lists, binary signed coefficients) evaluated by `{==}` checks
  the full projective associativity cross-product identity of the RCB formulas
  (3 symbolic points, symbolic b, reduction modulo the three curve equations,
  about 4 500 monomials) in 9 s and 346 MB.

So the algebra is done by reflection (one soundness proof, then every identity
is a closed computation), and the number theory certificates by closed
computation on `Bn`, each root kept under 60 s and 1000 MB.

## Method

1. **Reflective ring normalizer** (`proofs/crypto/secp256k1/group/`).
   Polynomials are sorted lists of terms (coefficient, exponent vector); the
   coefficients are signed binary numbers. `eval(env, P)` interprets a
   polynomial in Z/mZ with the spec's own `FS.madd`, `FS.msub`, `FS.mmul`, for
   any modulus m. Proved once: `eval` of the sum, difference, product is the
   `madd`/`msub`/`mmul` of the `eval`s, and the reduction by the curve
   equations X^3 -> Y^2 Z - b Z^3 (a Groebner basis: the leading monomials
   X1^3, X2^3, X3^3 are coprime, so the normal form is canonical and the zero
   test is complete) keeps `eval` under the hypotheses that the points are on
   the curve. A symbolic run of the spec's register programs (`add_prog`,
   `dbl_prog` are data) gives the polynomials of `padd`/`pdbl`; one lemma by
   induction over the program says they evaluate to the spec's registers.
2. **Polynomial identities** (no primality needed, any modulus): `padd` is
   commutative exactly; `padd(P, Q)` is on the curve; the three cross products
   of `padd(padd(P, Q), R)` and `padd(P, padd(Q, R))` agree (associativity up
   to projective scaling, one uniform identity with no case analysis thanks
   to completeness); `pdbl(P)` is proportional to `padd(P, P)`;
   `padd(P, O) = Y P`; `padd(P, -P) = (0, Y', 0)`; `padd` is homogeneous of
   degree 2 in each argument.
3. **p is prime**: Pocklington certificates (p - 1 = 2 3 7 13441 q1,
   q1 - 1 = 2 3 5 29^2 31 7723 r1 r2, then r2, ... down to trial division),
   each step a closed `Bn` computation (a^(N-1) = 1, a Bezout witness for
   gcd(a^((N-1)/q) - 1, N) = 1, q^2 > N); the theorem (every prime factor of
   N is 1 mod q) from Fermat's little theorem for the unknown factor.
   Fermat's little theorem by the binomial theorem modulo a prime.
4. **Field facts**: no zero divisors (Euclid's lemma), inverses
   (`FS.minv` is the inverse, by Fermat), -7 is not a cube and 3 is not a
   square mod p ((-7)^((p-1)/3) != 1 and 3^((p-1)/2) != 1 by `Bn`
   computation, then Fermat).
5. **Completeness and the group**: for points on the curve that are not
   (0, 0, 0), `padd` never returns (0, 0, 0) (Groebner certificates reduce an
   exceptional pair to a cube root of -7 or a square root of 3); projective
   equivalence (equal cross products) is an equivalence relation on such
   points and `padd`, `pdbl` respect it; O = (0 : 1 : 0) is the identity,
   (X : -Y : Z) the inverse, associativity and commutativity up to
   equivalence.
6. **Scalar multiplication**: `pmul(k, P)` is equivalent to k-fold addition;
   [a + b]P = [a]P + [b]P, [a b]P = [a]([b]P), [n]G = O (a closed `Bn`
   computation of the spec's own ladder, split across roots).
7. **Affine law** (SEC 1 2.2.1 chord and tangent, with the point at infinity)
   and `to_affine(padd(P, Q)) = aadd(to_affine(P), to_affine(Q))`; the affine
   group laws follow from the projective ones.
8. Stretch: n prime, `verify(pk(sk), m, sign(sk, m))`, `recover`, GLV.

## Status

Done: all of the plan, including n prime, [n] G = O, the affine law, the
SEC 1 round trip, ECDSA sign/verify/recover, BIP-340 and GLV on multiples of
G. The clauses and check times are in the secp256k1 section of
`docs/CRYPTO_CONTRACTS.md`.
