# Crypto contracts

Each `src/crypto` module has an executable specification in `spec/crypto/`,
transcribed from its standard and sharing nothing with the implementation
but neutral record types (the model is HACL*'s `Spec.*` modules), and a
proof package in `proofs/crypto/<pkg>/` whose `proof.bend` proves every
clause under its name. `python3 proofs/prove.py <pkg>` checks a package; the
evidence is one of

- **proved**: the clause holds for every input, checked by stock Bend
  (2.0.32, bendlang/bend main b2111cf4). No holes, no axioms, no `@unsafe`.
- **tested**: the clause is exercised, not proved (the table says why).

## Random numbers: `src/crypto/random.bend`

A cryptographically secure generator: ChaCha8Rand (C2SP chacha8rand), the
generator behind Go's runtime, `math/rand/v2` top-level functions and its
`ChaCha8` source, with Go's `ChaCha8.Read` byte order.

| API | Meaning |
|---|---|
| `new(seed)` | `Some{g}` for a 32-byte seed (a list of 32 bytes below 256), `None` otherwise; deterministic, for tests and reproducible runs |
| `from_os()` | IO: a generator keyed with 32 bytes of operating-system entropy (eight `IO.random_u32`: getrandom / arc4random / crypto.getRandomValues) |
| `bytes(g, n)` | n random bytes and the new generator (Go's `ChaCha8.Read`: the little-endian bytes of successive 64-bit outputs; a partly used output's remaining bytes are served first by the next call) |
| `uint64(g)`, `uint_below(g, n)` | a uniform 64-bit word; a uniform value below n > 0 (Lemire, unbiased) |
| `shuffle(g, items)` | a uniform permutation (Fisher-Yates) |
| `next(g)` | the Source step: every function of `src/math/random/rand.bend` runs on it (`R.float64(~CR.Gen, ~CR.next, g)`) |

The contract is `spec/crypto/random.bend`; gate
`proofs/crypto/random/proof.bend` (it builds on
`proofs/math/random/proof.bend`).

| Clause | Statement | Evidence |
|---|---|---|
| `Random.stream` | the 64-bit outputs of the generator keyed by eight words are C2SP's ChaCha8Rand stream keyed by them, for every key and length (pending bytes never change the word stream) | P |
| `Random.seeded` | `new(seed)` is None unless the seed is 32 bytes below 256, and otherwise outputs the stream of the seed's little-endian words | P |
| `Random.bytes` | `bytes(g, n)` are the first n of the pending bytes followed by the little-endian bytes (Go's `binary.LittleEndian.PutUint64`) of the next outputs, for every generator and n | P (`bytes.bend`) |
| `Random.bytes_lt` | every byte is below 256 (when the pending ones are, as `new` and `from_os` leave them) | P |
| `Random.uint_below` | `uint_below(g, n) < n` for n > 0 | P (the math `Uint64n.lt` at this source) |
| `Random.shuffle` | `shuffle(g, items)` is a permutation of `items` (every count kept) | P (the math `Shuffle.permutation`) |

The math contract (`docs/MATH_CONTRACTS.md`, Random numbers) adds that
`uint_below` is Go's `uint64n` decision exactly and that Lemire's rejection
is exactly unbiased (`Uint64n.value`, `Lemire.unbiased`). Tested:
`tools/check_random.py` compares 2976 bytes read at once, in one-byte reads
and in random chunks with Go's `TestChaCha8Read` transcript hash, and random
keys and call mixes with a Python mirror of Go.

### Security, and what is not proved

- **Pseudorandomness is an assumption, not a theorem.** The output is
  ChaCha8 keyed by the seed. That it is indistinguishable from uniform to
  anyone without the seed is the standard assumption that ChaCha8 is a PRF
  (eight rounds: Aumasson, "Too Much Crypto", 2019; C2SP's rationale). The
  proofs establish that the code computes exactly C2SP's function, so the
  assumption about ChaCha8 transfers to this code, and nothing more.
- **Forward secrecy.** Every 992 bytes of output the key is replaced by the
  last 32 bytes of the iteration (C2SP fast key erasure, as Go's
  `(*State).Refill`), and the old key is no longer in the generator: a
  generator value captured later cannot recompute outputs of earlier
  iterations. Within the current iteration it can (the state holds the key
  and the unread words), as in Go. Bend values are immutable: an old
  generator value still in the program's hands replays its outputs, so
  always continue from the returned generator and drop the old one.
- **Seeds.** `new(seed)` is only as secret as the seed: use `from_os()` for
  secrets, and `new` with a secret uniform 32-byte seed or for reproducible
  tests. `from_os` fails the program (IO.try) if the OS source fails.
- **Constant time** cannot be proved in Bend (no timing model). The
  generator does not branch on secret data except where Go does:
  `uint_below`'s rejection loop takes a data-dependent number of draws,
  which reveals nothing about the accepted value (rejected draws are
  independent of it); the Lemire division runs only on the rare path, as in
  Go.
- **Go's `crypto/rand`.** Go's `crypto/rand.Read` reads the operating
  system; its ChaCha8Rand use is the runtime's `rand` (and `math/rand/v2`'s
  top-level functions). This module is that generator made explicit: keyed
  once from the OS by `from_os`, then deterministic.
