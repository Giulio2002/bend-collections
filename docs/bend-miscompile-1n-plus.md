# Released Bend 2.0.28: `1n+U32.to_nat(x)` wraps at 2^32 in compiled code

Found while testing the U64 math on the released toolchain (`bend 2.0.28`,
native C backend). Not yet reported upstream.

## Reproduction

```bend
import Base

def b(+x: U32) -> String:
  U32.show(x) ++ " " ++ Nat.show(1n+U32.to_nat(x))

def main() -> IO(Unit):
  IO.print(b(4294967295) ++ "\n")
```

```
$ bend min.bend              # interpreted
4294967295 4294967296
$ bend min.bend -o min && ./min --threads 1
4294967295 0
```

The compiled program prints `0` where the result is `2^32 = 4294967296`.

## Trigger

The U32 value has to be used more than once in the function, so the compiler
keeps it as an unboxed `u32` local. Then the Nat successor is emitted as
32-bit arithmetic before the Nat range check, for example
`nat_chk(e, _x_1 + 1)` with `u32 _x_1`, and `2^32 - 1 + 1` wraps to `0`.

| Expression (x, y used more than once) | Compiled result at x = y = 2^32 - 1 | Correct |
|---|---|---|
| `1n+U32.to_nat(x)` | 0 | 4294967296 |
| `2n+U32.to_nat(x)` | 1 | 4294967297 |
| `Nat.add(U32.to_nat(x), U32.to_nat(y))` | 4294967294 | 8589934590 |
| `Nat.add(U32.to_nat(x), 1n)` | 4294967296 | 4294967296 (correct) |
| `Nat.mul(U32.to_nat(x), 2n)` | 8589934590 | 8589934590 (correct) |
| `1n+U32.to_nat(x)` with x used once | 4294967296 | 4294967296 (correct) |
| a `Nat` helper `def s(+a: Nat) = 1n+a` called on `U32.to_nat(x)` | 4294967296 | 4294967296 (correct) |

The interpreter is correct in every case. The proof checker checks the
source and the source is right, so proofs cannot catch this.

## Impact on this repository

Loop fuel is written `1n+U32.to_nat(q)` wherever a loop may run up to `q`
times from any estimate. At `q = 2^32 - 1` the fuel became `0`, so the loop
did not run at all.

- `w64.q_fix` (U64 division correction): wrong quotients, for example
  `0xFFFFFFFF_FFFFFFFE / 0x1_00000001` gave `0xFFFFFFFF` instead of
  `0xFFFFFFFE`. Fixed in #11.
- `fixed.u32_next_prime`: fixed in #11.
- `w64.isqrt32_fix`, `w64.isqrt32_est`, `w64.isqrt64_fix`,
  `w64.isqrt_newton` (the integer square roots): fixed here. With the
  estimators the library actually uses, these loops never reach the wrapping
  value (213,492 targeted isqrt inputs gave 0 wrong answers before the fix).
  But the proved "correct from any estimate" guarantee did not hold for the
  compiled code.

## Workaround used here

Write the successor with a Nat literal: `X.fuel(x) = Nat.add(U32.to_nat(x), 1n)`
(`src/math/w64.bend`). The proofs bridge it to `1n+U32.to_nat(x)` with
`W64S.fuel_succ`. `tools/check_generic.py` and `tools/check_fixed.py` run a
fixed grid of word-boundary values (0, 1, 2, 2^16±1, 2^31, 2^32-1, 2^32,
2^32+1, 2^48-1, 2^48, 2^63, 2^64-2, 2^64-1) on every seed. With the #11
division fix reverted, the grid fails 2 fixed-width and 49 generic cases.
