# Math contracts

The contract of each `src/math` module is part of its specification,
`spec/math/<module>.bend`, in the same form as the containers' SPARK
contracts (`docs/SPARK_CONTRACTS.md`): one `<Function>.<clause>` definition,
a proposition, per guarantee, under a table at the top of the spec that maps
each function to its clauses and to the verified development whose
statement it mirrors (Lean 4 Mathlib, the Why3 gallery, HACL*, Flocq,
SoftFloat). Python semantics (errors as values, `Overflow` for fixed widths,
ties, special values) cite the design reference
`python_style_math_stdlib_design.pdf` by section.

Two strengths of evidence:

- **proved**: `proofs/math/` proves the clause for every input, under the
  clause's name (`proofs/math/natural/proof.bend` for `natural`,
  `proofs/math/proof.bend` for `u64`, `hash`, `pow2`,
  `proofs/math/number/proof.bend` for `number` and `fixed`, and
  `proofs/math/typed/u32.bend` for the five selection clauses at U32:
  `Abs.identity`, `Min.agrees`, `Max.agrees`, `Sign.agrees`,
  `Clamp.agrees`). No holes, no axioms.
- **stated + tested**: the clause is stated in the spec and exercised, not
  proved: `tools/check_generic.py` (every typed function against Python,
  naming the clause of each case), `tools/check_f64.py` and
  `tools/check_f64x.py` (the software binary64 against the machine's
  doubles and CPython's math module), `tools/check_f64_spec.py` (the
  binary64 specification itself against the machine's doubles), and
  `proofs/math/typed/examples.bend`, where the proof checker evaluates the
  integer clauses and the instance laws at concrete U32 inputs (U64 values,
  large U32 values and F32/F64 are beyond what the checker evaluates in
  reasonable time).

## Per module

| Spec | Clauses | Evidence |
|---|---:|---|
| `spec/math/natural.bend` (Nat) | 49 | proved |
| `spec/math/u64.bend` (the 64-bit word of `u64.bend`) | 7 | proved |
| `spec/math/hash.bend` | 2 | proved |
| `spec/math/pow2.bend` | 1 | proved |
| `spec/math/generic.bend` (the templated functions per type) | 30 | proved: the 22 integer clauses at U32 and U64 (`proofs/math/typed/u32int.bend`, `u64int.bend`), the 8 float clauses at F32 and F64 (`float.bend`) |
| `spec/math/instances.bend` (what each instance operation computes) | 17 | proved at U32 and U64 (`proofs/math/typed/u32laws.bend`, `u64laws.bend`) |
| `spec/math/w64.bend` (U64 arithmetic) | 24 | proved (`proofs/math/typed/w64*.bend`) |
| `spec/math/f64.bend` (software binary64) | 45 | proved (bit fields, order, `OfNat`, `Add`, `Sub`, `Mul`, `Div`, `Sqrt`, and the 28 rounding / conversion / exponent / neighbour / remainder / closeness / ratio clauses; `proofs/math/typed/f64*.bend`); the reference itself tested against the machine |
| `spec/math/random.bend` (Go's math/rand/v2: ChaCha8, PCG, bounded draws, shuffles, floats) | 18 | proved (`proofs/math/random/proof.bend`, `proof_draws.bend`, `proof_pcg.bend`, `proof_float.bend`); see [Random numbers](#random-numbers) |

`src/math/num.bend` is the numeric interface's types; its laws are the
instance clauses of `spec/math/instances.bend`.

## Function by type

`Nat` is `src/math/natural.bend`; `U32`, `U64`, `F32`, `F64` are the
templated functions of `src/math/generic.bend` at each instance. **P** is
proved, **T** stated + tested, **T+e** stated + tested + checker-evaluated
examples, **—** not defined for that type.

| Function | Nat clauses | Nat | U32 | U64 | F32 | F64 | Typed clause |
|---|---|:-:|:-:|:-:|:-:|:-:|---|
| gcd | `Gcd.divides_left`, `Gcd.divides_right`, `Gcd.greatest`, `Gcd.mul_left` | P | P | P | — | — | `Gcd.agrees` |
| lcm | `Lcm.divides_left`, `Lcm.divides_right`, `Lcm.least`, `Lcm.gcd_mul_lcm` | P | P | P | — | — | `Lcm.checked` |
| gcd_all | `GcdAll.divides`, `GcdAll.greatest` | P | P | P | — | — | `GcdAll.agrees` |
| lcm_all | `LcmAll.divides`, `LcmAll.least` | P | P | P | — | — | `LcmAll.checked` |
| isqrt | `Isqrt.le`, `Isqrt.lt_succ` | P | P | P | — | — | `Isqrt.agrees` |
| iroot | `Iroot.done`, `Iroot.le`, `Iroot.lt_succ`, `Iroot.zero_degree` | P | P | P | — | — | `Iroot.agrees` |
| ilog | `Ilog.done`, `Ilog.pow_le`, `Ilog.lt_pow_succ`, `Ilog.zero`, `Ilog.small_base` | P | P | P | — | — | `Ilog.agrees` |
| factorial | `Factorial.value` | P | P | P | — | — | `Factorial.checked` |
| perm | `Perm.value`, `Perm.self` | P | P | P | — | — | `Perm.checked` |
| comb | `Comb.value`, `Comb.pascal`, `Comb.factorials`, `Comb.zero` | P | P | P | — | — | `Comb.checked` |
| pow_mod | `PowMod.value`, `PowMod.zero_modulus` | P | P | P | — | — | `PowMod.agrees` |
| mod_inverse | `ModInverse.inverse`, `ModInverse.reduced`, `ModInverse.not_coprime`, `ModInverse.zero_modulus` | P | P | P | — | — | `ModInverse.agrees` |
| divmod | `DivMod.value`, `DivMod.euclid`, `DivMod.rem_lt`, `DivMod.zero_divisor` | P | P | P | — | — | `DivMod.agrees` |
| bit_length | `BitLength.lt`, `BitLength.le` | P | P | P | — | — | `BitLength.agrees` |
| clamp | `Clamp.value`, `Clamp.ge`, `Clamp.le`, `Clamp.id`, `Clamp.domain` | P | P | P | P | P | `Clamp.agrees` / `FClamp.select` |
| sum | `Sum.value` | P | P | P | P | P | `Sum.checked` / `FSum.fold` |
| prod | `Prod.value` | P | P | P | P | P | `Prod.checked` / `FProd.fold` |
| min, max | — (Base's `Nat.min`, `Nat.max`) | — | P | P | P | P | `Min.agrees`, `Max.agrees` / `FMin.select`, `FMax.select` |
| abs | — | — | P | P | P | P | `Abs.identity` / `FAbs.value` |
| sign | — | — | P | P | P | P | `Sign.agrees` / `FSign.select` |
| pow | — (Base's `Nat.pow`) | — | P | P | P | P | `Pow.checked` / `FPow.binary` |

The integer clauses say that a typed result is the proved Nat function's
result (`agrees`), or, where the value can outgrow the width (`checked`),
that result when it fits and `Fail{Overflow}` exactly when it does not
(prefix-wise for `prod` and `lcm_all`, where a later 0 can shrink the
value). The float clauses state the result through the type's own IEEE
operations: `sum` and `prod` as left folds with every step rounded, `pow` as
right-to-left binary exponentiation, the selections through the type's IEEE
`<` (false on NaN).

## The binary64 and the 64-bit words

| Module | Functions | Clauses | Evidence |
|---|---|---|---|
| `f64.bend` | add, sub, mul, div, sqrt | `Add.value`, `Sub.value`, `Mul.value`, `Div.value`, `Sqrt.value`: equal to `spec/math/f64.bend`'s exact-then-round reference | P (`f64addv.bend`, `f64mulv.bend`, `f64divc.bend`, `f64sqc.bend`) |
| | lt, le, eq | `Lt.value`, `Le.value`, `Eq.value`: the extended-real order, false on NaN, +0 == -0 | P (`f64cmp.bend`) |
| | neg, abs, copysign, classification, of_nat | `Neg.value`, `Abs.value`, `Copysign.value`, `IsNan.value`, `IsInf.value`, `IsFinite.value`, `IsZero.value`, `Signbit.value`, `OfNat.value` | P (`f64bits.bend`, `f64ofnat.bend`) |
| | trunc, floor, ceil, round (ties to even) | `Trunc.value`, `Floor.value`, `Ceil.value`, `Round.value`: IEEE roundToIntegral of m 2^-k (the integer part, plus one by the direction's rule) | P (`f64rint.bend`) |
| | to_u64, to_u32, floor_u64, ceil_u64, round_u64, of_u64, of_u32 | `ToU64.value`, `ToU32.value`, `FloorU64.value`, `CeilU64.value`, `RoundU64.value`, `OfU64.value`, `OfU32.value`: truncation toward zero as a checked unsigned integer (`BadDomain` for NaN, `Overflow` outside [0, 2^w)), the double nearest to an integer | P (`f64conv.bend`, `f64misc.bend`) |
| | frexp, ldexp, ulp | `Frexp.value`, `Ldexp.value`, `Ulp.value`: significand scaled into [1/2, 1), x 2^e rounded once (overflow, gradual underflow), the weight of the last bit | P (`f64exp.bend`, `f64misc.bend`) |
| | nextafter, fmin, fmax | `Nextafter.value`, `Fmin.value`, `Fmax.value`: one step of the magnitude bits toward y; IEEE minimumNumber / maximumNumber (NaN ignored, -0 < +0) | P (`f64next.bend`) |
| | is_normal, is_subnormal, to_bits, of_bits64, is_integer | `IsNormal.value`, `IsSubnormal.value`, `Bits.value`, `Bits.roundtrip`, `Bits.inverse`, `IsInteger.value` | P (`f64misc.bend`, `f64next.bend`) |
| | modf, fmod, remainder | `Modf.value`, `Fmod.value`, `Remainder.value`: exact, the remainder of the significands at their common scale (ten-bit long division, invariant r = N mod B and the quotient's parity) | P (`f64modf.bend`, `f64fmod.bend`) |
| | isclose, as_integer_ratio | `IsClose.value` (CPython's algorithm on the proved operations), `AsIntegerRatio.value` (lowest terms, the denominator as a power of two) | P (`f64close.bend`, `f64ratio.bend`) |
| `w64.bend` | mul32, add, sub, mul, div32, quot/rem, mulmod, isqrt, shifts, clz, comparisons | 24 clauses: each the Nat operation on the values modulo 2^64 | P (`w64*.bend`) |
| `u64.bend` | is_zero, le_signed, add, neg, div_small, div_small_signed | `IsZero.value`, `LeSigned.value`, `Add.bits`, `Add.modular`, `Neg.bits`, `DivSmall.quotient`, `DivSmallSigned.quotient` | P |

## Fixed-width integers and number theory

`src/math/fixed.bend` (U32 and U64) and `src/math/number.bend` (Nat); gate
`proofs/math/number/proof.bend`, every clause under its name at both widths.

| Module | Functions | Clauses | Mirrors | Evidence |
|---|---|---|---|---|
| `number.bend` | bit_count | `BitCount.value` | Python `int.bit_count`; Mathlib `Nat.bits` | P (`number/bitcount.bend`) |
| | egcd | `Egcd.gcd`, `Egcd.bezout` | Knuth 4.5.2 Algorithm X; Mathlib `Nat.xgcd`, `Nat.gcd_eq_gcd_ab` | P (`number/egcd.bend`) |
| | is_prime | `IsPrime.value` | Mathlib `Nat.Prime`; bound `Nat.minFac_sq_le_self` | P (`number/prime.bend`) |
| `fixed.bend` | checked_{add,sub,mul,div,rem,pow,shl,shr} | `Checked*.value`: Some exact result exactly when it fits / the divisor is nonzero / the shift is below w | Rust `u32::checked_*`, `u64::checked_*` | P (`typed/fix32.bend`, `typed/fix64.bend`) |
| | wrapping_{add,sub,mul,pow,shl,shr} | `Wrapping*.value`: the result mod 2^w (`WrappingSub`: r + b == a + 2^w [a < b]) | Rust `wrapping_*`; HACL* `Lib.IntTypes` modular semantics | P (same) |
| | saturating_{add,sub,mul,pow} | `Saturating*.value`: the result when it fits, else the largest value | Rust `saturating_*` | P (same) |
| | overflowing_{add,sub,mul,pow,shl,shr} | `Overflowing*.value` (the wrapping value), `Overflowing*.flag` | Rust `overflowing_*` | P (same) |
| | bit_count | `BitCount.value`: `ones(w, value)` | Rust `count_ones` | P (`typed/fixbits.bend`) |
| | is_prime, next_prime (U32) | `IsPrime.value`, `NextPrime.found` (a prime above n, none in between), `NextPrime.none` (no prime left below 2^32) | Mathlib `Nat.Prime`, `Nat.find` | P (`number/fixprime.bend`) |
| | to_bytes_le/be, from_bytes_le/be | `ToBytes.le`, `ToBytes.be` (the w/8 base-256 digits), `FromBytes.le`, `FromBytes.be` (the value of exactly w/8 digits below 256, else None) | Python `int.to_bytes`/`from_bytes`; Rust `to_le_bytes`/`from_le_bytes`; Mathlib `Nat.digits` | P (`typed/fixbytes.bend`) |

Not provided, and why: `div_euclid`/`rem_euclid` equal `div`/`rem` on
unsigned types, and unsigned `wrapping_`/`saturating_`/`overflowing_`
`div`/`rem` equal plain division (it never overflows); `egcd` is Nat-only
(a typed version would add nothing but coefficient-width checks);
`is_prime`/`next_prime` at U64 would need deterministic Miller-Rabin, whose
correctness rests on the base-set theorem (the first 12 prime bases decide
every n < 2^64), a computation over all 64-bit strong pseudoprimes that
cannot be proved here without an axiom; exact trial division is too slow at
64 bits.

## Random numbers

`src/math/random.bend` is Go's `math/rand/v2` (bit for bit: Go's own test
vectors pass, `tools/check_random.py`): sources are values built from a seed
the caller chooses, threaded explicitly; every function of
`src/math/random/rand.bend` is written once for any source, a state type `S`
with `~next: S -> U64 & S` passed as templates (the Source interface; a
later math/statistics module is written the same way, and its laws can be
proved for an arbitrary `~next`, as `Uint64n.lt` and `Shuffle.permutation`
are). The contract is `spec/math/random.bend`; the executable
specifications are `spec/math/random/chacha8rand.bend` (C2SP chacha8rand
with the RFC 8439 ChaCha block at 8 rounds), `pcg.bend` (the 128-bit LCG and
DXSM on naturals), `rand.bend` (Go's `uint64n` decision, Lemire's
acceptance, the bounded draw, occurrence counts) and `source.bend` (a
source's output sequence). Gates, every clause under its name, for every
input: `proofs/math/random/proof.bend` (ChaCha8, Lemire, shuffle, perm),
`proof_draws.bend` (uint64n and the fixed-width and bounded wrappers),
`proof_pcg.bend` (PCG) and `proof_float.bend` (float64); each root checks
only the lemma files its clauses need, in under 25 s each on bend-local.

| Function | Clause | Statement | Mirrors | Evidence |
|---|---|---|---|---|
| ChaCha8 `of_key`, `next` | `ChaCha8.stream` | the n outputs of the generator keyed by k are C2SP's stream keyed by k's eight words (every key, every n: blocks, subtractions, interleaving, 992-byte key erasure) | C2SP chacha8rand; Go `internal/chacha8rand`; HACL* `Spec.Chacha20` for the block | P (`chacha8/rounds.bend`, `block.bend`, `stream.bend`) |
| ChaCha8 `new` | `ChaCha8.seeded` | None unless the seed is 32 bytes below 256; otherwise the stream of its little-endian words | Go `NewChaCha8([32]byte)` | P (`chacha8/seed.bend`) |
| PCG `step_with` | `PCG.step` | one step is s * mul + inc mod 2^128, for every multiplier and increment | Go `pcg.go` `next`; O'Neill 2014 | P (`proof_pcg.bend`, `pcg/step.bend`, `pcg/impl.bend`) |
| PCG `dxsm_with` | `PCG.output` | the output is DXSM of the state on naturals, for every multiplier: `dxsm3(t, lo)` for the first half's value `t = dxsm1(cm, hi)` (stated through `t` so the checker never compares two copies of the nested 64-bit recursion; `t := dxsm1(cm, hi)` gives the composed form) | Go `(*PCG).Uint64` | P (`proof_pcg.bend`, `pcg/xor.bend`) |
| PCG `next` | `PCG.constants` | `next` is the step and output with Go's constants | Go `pcg.go` | P |
| `uint64n` | `Uint64n.value` | for every source, state and bound, the value of `uint64n(n)` is the specification's bounded draw: the first of at most 128 draws Go's `uint64n` accepts (n = 0 read as 2^64, powers of two masked, else Lemire) | Go `rand.go` `uint64n`; Lemire 2019 Algorithm 5 | P (`uint64n.bend`, `bits.bend`) |
| `uint64n` | `Uint64n.lt` | `uint64n(n) < n` for n > 0, every source | Go `Uint64N` | P (`below.bend`) |
| Lemire's rejection | `Lemire.unbiased` | for every width w, 0 < n < 2^w and k < n, exactly floor(2^w / n) of the 2^w outputs x draw k (both branches: the mask and the multiply-and-reject), so a uniform source gives an exactly uniform result | Lemire 2019, section 4 (the count of accepted x per k) | P (`lemire.bend`) |
| `shuffle` | `Shuffle.permutation` | for every relation `rel` and value v, the result has as many elements related to v as the input, for every source: with an equality this is Mathlib's `List.Perm` through `List.perm_iff_count` (`l₁ ~ l₂ ↔ ∀ a, count a l₁ = count a l₂`); the argument is the one of Isabelle's verified Fisher-Yates (each step is a swap, and a swap keeps every count) | Go `Shuffle`; Mathlib `List.Perm`; Isabelle AFP Fisher-Yates (Eberl) | P (`shuffle.bend`) |
| `perm` | `Perm.permutation` | `perm(n)` holds every i < n exactly once and nothing else | Go `Perm` | P (`shuffle.bend`) |
| `uint32`, `int64`, `int32` | `Uint32.value`, `Int64.value`, `Int32.value` | the top 32, low 63 and top 31 bits of the source output | Go `Uint32`, `Int64`, `Int32` | P (`wrappers.bend`) |
| `uint32n` | `Uint32n.lt` | `uint32n(n) < n` for n > 0 | Go `Uint32N` | P (`wrappers.bend`) |
| `intn` | `Intn.lt` | `intn(n) < n` for 0 < n < 2^64 (its U64 is `nat64(n)`, proved to denote n) | Go `IntN` | P (`wrappers.bend`) |
| `int_range` | `IntRange.bounds` | `lo <= int_range(lo, hi) < hi` for lo < hi | lo + Go `IntN(hi - lo)` | P (`wrappers.bend`) |
| `float64` | `Float64.value` | the double m 2^-53, m the low 53 bits of the output: `spec/math/f64.bend`'s `round(False, m, zb - 53)` (stated for any xv equal to zb - 53) | Go `Float64` | P (`float.bend`, `fround.bend`) |
| `float64` | `Float64.lt_one` | `float64 < 1.0` | Go `Float64` | P (`float.bend`) |

Uniformity. `Lemire.unbiased` is the exact form of "uint64n of a uniform
source is uniform": in Mathlib's probability vocabulary, the pushforward of
the uniform `PMF` on the 2^w source words, conditioned on acceptance, is the
uniform `PMF` on `[0, n)`, because every k has the same number
(floor(2^w / n)) of accepted preimages. It is stated as the count, which
needs no measure theory.

What is tested rather than stated (there is no clause to prove):

- **Go's exact outputs.** The specifications are transcriptions of C2SP and
  Go's source; `tools/check_random.py` checks that they (and the
  implementation, proved equal to them) are Go's generator bit for bit:
  Go's published vectors (`chacha8_test.go` 372 outputs through three key
  erasures and the Read transcript hash, `pcg_test.go`, and
  `regress_test.go`'s golden values for Float64, Int, Int32, Int32N, Int64,
  Int64N, IntN, Perm, Uint32, Uint32N, Uint64, Uint64N, UintN), then random
  keys, seeds and call sequences against a Python mirror of Go.
- **The rejection bound.** Go's `uint64n` retries forever; Bend requires
  termination, so at most 128 draws are made (`Uint64n.value` states exactly
  this bounded draw). A uniform source rejects with probability below 1/2
  per draw, so a 128th rejection has probability below 2^-128; the result is
  below n even then (`Uint64n.lt`).
- **Statistical quality of the sources** (not a theorem for any PRNG):
  a chi-square smoke test of `uint64n` buckets for ChaCha8, PCG and the
  crypto generator.

## Not proved, and why

Every clause in `spec/math` is proved. The float clauses of
`spec/math/generic.bend` state how each generic function combines the
instance's own operations, so `proofs/math/typed/float.bend` proves them once
for any instance without overflow tests and reads them at F32 and F64. What
F32's primitives compute (Base's IEEE binary32) is not specified here: the
checker does not evaluate primitive floats, so for F32 the arithmetic itself
is only tested. F64's arithmetic is `src/math/f64.bend`, proved against
`spec/math/f64.bend`'s exact-then-round reference (Flocq-style, SoftFloat's
`roundPackToF64` shown equal to round-to-nearest-even on the exact value).
