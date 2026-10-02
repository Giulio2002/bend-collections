# The group law of edwards25519: method, theorems, roots

Goal: prove the group law of the twisted Edwards curve
`-x^2 + y^2 = 1 + d x^2 y^2` over GF(2^255 - 19) for the specification of
Ed25519 (`spec/crypto/ed25519.bend`: RFC 8032's addition and doubling in
extended coordinates, double-and-add), so that faster scalar multiplications
(base-point tables, fixed and signed windows, Strauss/Shamir) can be proved
equal to the specification, and so that `verify(pk(sk), m, sign(sk, m))` can
be proved. Everything below is proved for every input, with no holes, axioms
or unsafe code, on stock Bend 2.0.34.

## Statements

`spec/crypto/curve25519/edwards.bend` (the affine group, for a modulus
`p = 1 + mp`; `G.Curve(mp, d)`: p an odd prime, d nonzero and not a square
(Euler's criterion), `sqm1(p)^2 == -1`):

| Clause | Statement (a, b, c on the curve) |
|---|---|
| `Group.closure`, `Group.zero_on`, `Group.neg_on`, `Group.nmul_on` | a + b, (0, 1), -a, [k] a are on the curve |
| `Group.comm` | a + b == b + a (every a, b) |
| `Group.zero`, `Group.neg` | a + (0, 1) == a, a + (-a) == (0, 1) |
| `Group.assoc` | (a + b) + c == a + (b + c) |
| `Group.nmul_add`, `Group.nmul_mul`, `Group.nmul_dist` | [j + k] a == [j] a + [k] a, [j k] a == [j] ([k] a), [k] (a + b) == [k] a + [k] b |

The addition is the twisted Edwards law with division as multiplication by
the Fermat inverse; the points are pairs of residues, so the laws are
equations between points (no projective equivalence). Completeness (the
denominators `1 +- d x1 x2 y1 y2` never vanish on the curve: Bernstein and
Lange) is `glaw.bend`'s `compl_x`, `compl_y`.

`spec/crypto/ed25519_group.bend` (the specification's extended coordinates,
at `p = FS.prime(one)`, `d = ED.dconst(one, p)`; `Valid`: Z != 0, (X/Z, Y/Z)
on the curve, T Z == X Y):

| Clause | Statement (a, b valid) |
|---|---|
| `Ed25519.add_affine`, `Ed25519.add_valid` | `affine(add(a, b)) == affine(a) + affine(b)`, and `add(a, b)` is valid: every input, no exceptional case |
| `Ed25519.double_affine`, `Ed25519.double_valid` | the same for `double(a)` and `affine(a) + affine(a)` |
| `Ed25519.identity`, `Ed25519.identity_valid` | `affine(identity()) == (0, 1)` |
| `Ed25519.mul_affine`, `Ed25519.mul_valid` | `affine(mul(k, a)) == [k mod 2^256] affine(a)` (the double-and-add of the specification is the scalar multiple) |
| `Ed25519.affine_on` | the affine point of a valid point is on the curve |

and, in `proofs/crypto/ed25519/group/` (stated for `1 + mp`):
`dec.bend` `decode_valid`, `some_valid`, `base_valid` (whatever `decode`
returns, and the base point, are valid); `dec2.bend` `dec_rt` (x recovery:
for a point (x, y) of the curve the decoder on y and the parity of x returns
(x : y : 1 : x y), p = 8 m + 5); `vs.bend` `veq`
(`[(r + k s) mod l] b == [r] b + [k] ([s] b)` when `[l] b == (0, 1)`),
`equal_aff` (valid points with the same affine point are `ED.equal`);
`vs2.bend` `check_eq` (the verification equation of RFC 8032 5.1.7 holds for
S = (r + k s) mod l).

How a faster scalar multiplication is proved equal to the specification:
show that its result is valid and has the affine point `[k] affine(a)` (each
of its additions and doublings by `add_affine` / `double_affine`, its table
entries by `mul_affine`, the recombination by `Group.nmul_add`,
`Group.nmul_mul`, `Group.assoc`, `Group.comm`); `mul_affine` gives the same
affine point for `ED.mul`; then the encodings are equal (`vs2.bend`
`encode_aff`: `ED.encode` reads only the affine point) and `ED.equal` holds
(`equal_aff`).

## Method

1. **Identities by reflection.** The sibling secp256k1 proof's sparse
   polynomial normalizer (`proofs/crypto/secp256k1/group/poly.bend`,
   `pev.bend`, `zm.bend`, `ident.bend`) is reused as it is. Added here:
   `redm.bend`, reduction by a rule "monomial -> polynomial" (the curve
   equation as `x^2 y^2 -> e (y^2 - x^2 - 1)` with e the inverse of d, and
   `d e -> 1`: coprime leading monomials, so a Groebner basis and a complete
   zero test), proved sound for every modulus; `ex.bend`, ring expressions
   as data with one soundness theorem (an identity instance is two
   expression literals and a `{==}` check that the reduced difference is
   `[]`; this keeps the checker's memory flat); `idm.bend` (rule hypotheses).
   `tools/generators/ed25519_group/gen_ids.py` writes the instances
   (`id_*.bend`) and checks each identity in Python first.
2. **Fractions.** A quotient `n / d` of the specification is
   `n * FS.finv(p, d)`; `fq.bend` turns a polynomial identity
   `n1 d2 == n2 d1` and nonzero denominators into an equation between the
   quotients (`frac_eq`, `frac_val`, `frac_mul`), so the affine laws follow
   from cross-multiplied identities: associativity is
   `(N_L D_R - N_R D_L) (dx12 dy12 dx23 dy23) == 0` modulo the three curve
   equations, with the inner sums entering through `x12 dx12 == nx12`
   (cofactors written by the generator). This is Hales's route ("The group
   law for Edwards curves", 2016): polynomial identities plus completeness.
3. **Completeness.** If `1 +- d x1 x2 y1 y2 == 0` then
   `(i x1 +- y1)^2 == d (x1 y1 (i x2 +- y2))^2` (four identities), so by
   `fq.bend`'s `nonsq` (d^((p-1)/2) != 1, Fermat) `x1 y1 (i x2 +- y2) == 0`
   for both signs, which gives `2 == 0`.
4. **Number theory.** `proofs/math/number/nt_*.bend` (primes, Euclid,
   Fermat, Pocklington: the sibling's) and its Pocklington chains on binary
   numbers; here `cert_*.bend` (p, L prime; `d^((p-1)/2) == -1`;
   `2^((p-1)/4)`), `pfacts.bend`, `lfacts.bend` (the literals are the
   specification's constants), `cpar.bend` (`G.Curve` for edwards25519 from
   the certificates).
5. **Extended coordinates** (`ext.bend`): with the rules `X -> x Z`,
   `Y -> y Z`, `T -> x y Z` the RFC's formulas give `X3 dx == nx Z3`,
   `Y3 dy == ny Z3`, `Z3 == 4 (Z1 Z2)^2 dx dy` (nonzero by completeness).
6. **Double-and-add** (`smul.bend`): by induction over the bit count,
   `affine(smul(n, k, a, q)) == [2^n] affine(q) + [k mod 2^n] affine(a)`.

## Roots

A root re-checks all its imports (there is no cache), so the heavy
certificates are independent roots and the theorems that use them take
their conclusions as hypotheses (`G.Curve(mp, d)`, `FS.prime(one) == 1 + mp`):
the composition of a theorem with its certificates is an application, but
no single root contains both.

The group files import pruned copies of the libraries they use
(`proofs/crypto/ed25519/group/lite/`, written by
`tools/generators/ed25519_group/shake_ed.py`, the secp256k1 `shake.py` for
this tree): the number theory otherwise drags in the trial-division proof
of small primes (about 300 MB per root).

Every Ed25519 root, checked on the server (Bend 2.0.34, two at a time,
each inside a 1000 MB memory limit, `BUN_JSC_forceRAMSize` = 1000 MB):

| root | peak MB | s |
|---|---|---|
| `ed25519/group/cert_d0.bend` | 614 | 35 |
| `ed25519/group/cert_l1.bend` | 631 | 24 |
| `ed25519/group/cert_q.bend` | 625 | 24 |
| `ed25519/group/cert_q1.bend` | 625 | 20 |
| `ed25519/group/cert_q2.bend` | 490 | 6 |
| `ed25519/group/certa.bend` | 665 | 27 |
| `ed25519/group/certda.bend` | 686 | 33 |
| `ed25519/group/certia.bend` | 690 | 25 |
| `ed25519/group/certla.bend` | 729 | 19 |
| `ed25519/group/id_madd.bend` | 405 | 6 |
| `ed25519/group/id_mdbl.bend` | 394 | 7 |
| `ed25519/group/id_mpu.bend` | 335 | 1 |
| `ed25519/group/inst.bend` | 551 | 19 |
| `ed25519/group/inst2.bend` | 639 | 25 |
| `ed25519/group/laws.bend` | 520 | 20 |
| `ed25519/group/lb_00.bend` | 359 | 31 |
| `ed25519/group/lb_01.bend` | 377 | 27 |
| `ed25519/group/lb_02.bend` | 387 | 29 |
| `ed25519/group/lb_03.bend` | 361 | 31 |
| `ed25519/group/lb_04.bend` | 365 | 33 |
| `ed25519/group/lb_05.bend` | 364 | 32 |
| `ed25519/group/lb_06.bend` | 342 | 31 |
| `ed25519/group/lb_07.bend` | 379 | 31 |
| `ed25519/group/lb_08.bend` | 351 | 32 |
| `ed25519/group/lb_09.bend` | 362 | 33 |
| `ed25519/group/lb_10.bend` | 368 | 37 |
| `ed25519/group/lb_11.bend` | 364 | 43 |
| `ed25519/group/lb_12.bend` | 342 | 49 |
| `ed25519/group/lb_13.bend` | 378 | 50 |
| `ed25519/group/lb_14.bend` | 358 | 51 |
| `ed25519/group/lb_15.bend` | 360 | 50 |
| `ed25519/group/lb_16.bend` | 356 | 50 |
| `ed25519/group/lb_17.bend` | 347 | 48 |
| `ed25519/group/lbs.bend` | 668 | 35 |
| `ed25519/group/lbz.bend` | 655 | 22 |
| `ed25519/group/scalar.bend` | 254 | 0 |
| `ed25519/proof_keys.bend` | 505 | 7 |
| `ed25519/proof_law.bend` | 839 | 23 |
| `ed25519/proof_sign_facade.bend` | 568 | 11 |
| `ed25519/proof_sign.bend` | 528 | 10 |
| `ed25519/proof_verify.bend` | 518 | 10 |
| `ed25519/proof.bend` | 460 | 6 |
| `proofs/math/number/proof_nt.bend` | 287 | 2 |
