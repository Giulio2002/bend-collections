# Backend divergences

Every clause of this library is proved about the Bend **source**. The compiler
that turns the source into C and JavaScript is not verified, so a proved
function can still compute a wrong answer in a build. It has happened:
[bendlang/bend#1142](https://github.com/bendlang/bend/issues/1142) wrapped
`1n + U32.to_nat(x)` at 2^32 in the C backend only, which gave a wrong 64-bit
division in proved code (the library now writes `Nat.add(U32.to_nat(x), 1n)`,
which keeps every proof).

`tools/backend_diff.py` tests that gap. It runs every public module on the
same seeded random and edge-case inputs through the three execution paths of
the toolchain and fails when two of them print different lines:

| Path | Command | Engine |
|---|---|---|
| `run` | `bend driver.bend -- args` | the runtime bundled in the `bend` binary |
| `c` | `bend driver.bend -o bin`, then `bin -- args` | the native C backend (clang) |
| `js` | `bend driver.bend -o out.js`, then `node out.js -- args` | the JavaScript backend (V8) |

```sh
python3 tools/backend_diff.py             # every module, about 35 minutes
python3 tools/backend_diff.py --quick     # about 4 minutes
python3 tools/backend_diff.py --only fixed --seed 7 --case 3 --show
```

This file records what it has found on Bend 2.0.34 (x86-64 Linux, clang 21,
node 22). None of the entries below is a wrong result of a function of this
library: on the inputs of the run recorded at the end, the three paths agree
on every line that every path produced. They are differences in the
primitives underneath, which a caller can run into.

## 1. `char-range`: the JavaScript paths reject a `Char` that is not a Unicode scalar value

`Char` is `Chr{code: U32}` in Base: every `U32` is a `Char` in the source
language, and every proof about `String` quantifies over such strings. The
native build agrees. `bend file.bend` and the JavaScript build stop with
`bend: 55296 is not a Unicode scalar value` as soon as a string holds a code
in `0xD800..0xDFFF` or above `0x10FFFF`.

Repro: [`tests/backend_diff/repro/char_range.bend`](../tests/backend_diff/repro/char_range.bend)

```python
def codes(s: String) -> String:
  match s:
    case SNil{}:
      ""
    case SCon{Chr{c}, t}:
      " " ++ U32.show(c) ++ codes(t)

def show(+s: String) -> String:
  Nat.show(String.length(s)) ++ codes(s)

def main() -> IO(Unit):
  IO.print(show(SCon{Chr{55296}, SNil{}}))
```

| Path | Output |
|---|---|
| `c` | `1 55296` |
| `run` | `bend: 55296 is not a Unicode scalar value` (exit 1) |
| `js` | `bend: 55296 is not a Unicode scalar value` (exit 1) |

Which path is wrong: the JavaScript ones. The definition of `Char` has no
such restriction, and the string is never printed.

In this library: the String-keyed containers (`hash_table.bend`, `lru.bend`)
are proved for every key. On the JavaScript paths a key holding such a `Char`
stops the program; it never gives a wrong answer. `tests/lru_spec/main.bend`
uses the key `Chr{3000000000}` on purpose and therefore runs on the native
build only. No workaround: restricting the key type would change the proved
statements, and the failure is fail-stop.

## 2. `nan-bits`: the bit pattern of an F32 NaN depends on the path

The F32 operations are laws without a body in Base (axioms implemented by the
host), so there is no definition to be wrong against; but `F32.bits` makes the
difference observable. The sign and the payload of a NaN are whatever the host
produced, and all three paths differ from each other.

Repro: [`tests/backend_diff/repro/nan_bits.bend`](../tests/backend_diff/repro/nan_bits.bend)
prints the bits of `0/0`, `sqrt(-1)`, `log(-1)`, `inf - inf`, `pow(-2, 0.5)`:

| Path | Output |
|---|---|
| `run` | `4290772992 4290772992 2143289344 4290772992 4290772992` |
| `c` | `2143289344 4290772992 4290772992 2143289344 2143289344` |
| `js` | `2143289344 4290772992 2145386496 4290772992 2145386496` |

(`2143289344 = 0x7FC00000`, `4290772992 = 0xFFC00000`, `2145386496 = 0x7FE00000`.)

In this library: the F32 instance of the templated math (`src/math/instances.bend`)
returns host NaNs, so code that needs to recognise one must test
`F32.is_ne(x, x)` and never compare bit patterns. The software binary64
(`src/math/f64.bend`) is not affected: it is integer code and its NaNs are
the ones the specification fixes. The harness replaces F32 NaN patterns by
`NaN` before comparing (3318 lines of the full run had path-dependent NaNs).

## 3. `f32-show-tie`: `F32.show` rounds a tie in the 8th significant digit differently

`F32.show` prints at most eight significant digits. When the value lies
exactly halfway between two such decimals, the native build rounds to even and
the JavaScript paths round up.

Repro: `IO.print(F32.show(x))` for a binary32 `x` with nine significant
decimal digits, the last one a 5:

| `x` | `c` | `run` | `js` |
|---|---|---|---|
| `45566.3125` | `45566.312` | `45566.313` | `45566.313` |
| `1048576.25` | `1048576.2` | `1048576.3` | `1048576.3` |
| `262144.625` | `262144.62` | `262144.63` | `262144.63` |
| `1024.03125` | `1024.0312` | `1024.0313` | `1024.0313` |
| `12345.6875` (odd digit before the 5) | `12345.688` | `12345.688` | `12345.688` |

`F32.show` is also a law without a body, so neither answer contradicts a
definition. Nothing in `src/` calls `F32.show`, `F32.read` or `F32.bits`. The
harness keeps such values out of its random inputs and probes five of them as
known divergences.

## 4. `recursion-depth`: the JavaScript paths have a machine stack

A recursion that is not a tail call is bounded by the heap in the native
runtime and by the machine stack on the JavaScript paths.

Repro: [`tests/backend_diff/repro/recursion_depth.bend`](../tests/backend_diff/repro/recursion_depth.bend)
(`deep(n) = 1n + deep(n - 1)`, the depth as the first argument), default
settings, 8 MB stack:

| Depth | `run` | `c` | `js` (node) |
|---|---|---|---|
| 5 000 | ok | ok | ok |
| 10 000 | ok | ok | `memory fault (machine stack overflow?)` |
| 20 000 | ok | ok | stack overflow |
| 50 000 | stack overflow | ok | stack overflow |
| 1 000 000 | stack overflow | ok | stack overflow |

This is a limit, not a miscompile, and it is fail-stop. On the JavaScript
paths it bounds the input size of any function that recurses once per element
without a tail call, in this library and in its callers. The harness raises
the stack (`ulimit -s` 1 GB, `node --stack-size=50000`); with that, its
inputs (histories of up to 2500 operations, byte lists of up to 6000 bytes,
arrays of up to 8192 bytes) run on all three paths. It counts a case where a
path overflows and the others agree as `resource-limit`, which fails only
with `--strict`; the one such case of a run is the probe of depth 100 000.

## Not reproduced: bendlang/bend#1142

The shapes of #1142 (a U32 local used more than once and then converted to
Nat, `1n + U32.to_nat(x)` at `x = 2^32 - 1`, 64-bit division and remainder
with operands around 2^32 and 2^48) are part of every run, in the `codegen`
and `fixed` modules. On Bend 2.0.34 the three paths agree on all of them.
Every path also refuses a Nat past 2^48 - 1 with the same error; none wraps.

## The run this file records

Bend 2.0.34, seed 2026, `python3 tools/backend_diff.py -j 4`: 7383 cases, 1 028 251 output lines compared across `run`, `c` and `js`, 0 disagreements, 1954 s.
The counts per module are in
[`tools/README.md`](../tools/README.md#backend-differential-harness).

None of these entries has been reported to bendlang/bend from this repository.
