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
  `proofs/math/proof.bend` for `u64`, `hash`, `pow2`, and
  `proofs/math/typed/u32.bend` for the five selection clauses at U32:
  `Abs.identity`, `Min.agrees`, `Max.agrees`, `Sign.agrees`,
  `Clamp.agrees`). No holes, no axioms.
- **stated + tested**: the clause is stated in the spec and exercised, not
  proved: `tools/check_generic.py` (every typed function against Python,
  naming the clause of each case), `tools/check_f64.py` (the software
  binary64 against the machine's doubles), `tools/check_f64_spec.py` (the
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
| `spec/math/f64.bend` (software binary64) | 17 | proved (bit fields, order, `OfNat`, `Add`, `Sub`, `Mul`, `Div`, `Sqrt`; `proofs/math/typed/f64*.bend`); the reference itself tested against the machine |

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
| `w64.bend` | mul32, add, sub, mul, div32, quot/rem, mulmod, isqrt, shifts, clz, comparisons | 24 clauses: each the Nat operation on the values modulo 2^64 | P (`w64*.bend`) |
| `u64.bend` | is_zero, le_signed, add, neg, div_small, div_small_signed | `IsZero.value`, `LeSigned.value`, `Add.bits`, `Add.modular`, `Neg.bits`, `DivSmall.quotient`, `DivSmallSigned.quotient` | P |

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
