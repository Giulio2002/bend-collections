import Base
import ../../lib/common.bend as C
import ../../../src/math/u64.bend as W
import ../w64.bend as SW
import ./source.bend as SRC

# Executable specification of the bounded draws, shuffles and permutations
# of src/math/random/rand.bend, on natural numbers, transcribed from Go's
# math/rand/v2 rand.go (uint64n, Shuffle, Perm) and Lemire, "Fast Random
# Integer Generation in an Interval" (ACM TOMACS 29(1), 2019, Algorithm 5).
# Widths are parameters: w = 64 for Uint64N (a 32-bit variant is w = 32);
# no constant 2^w is ever formed (C.low, C.high, C.fits and pow2mod work on
# a symbolic w), as spec/lib/common.bend explains.
#
#   and_bits(w, a, b)        the bitwise and of the low w bits
#   pow2mod(w, n)            2^w mod n (Go's -n % n = (2^w - n) mod n)
#   draw(w, x, n)            Go's uint64n decision for one source output x:
#                            n == 0 (read as 2^w): Some{x}; n a power of two
#                            (n & (n - 1) == 0): Some{x & (n - 1)}; otherwise
#                            x * n = hi * 2^w + lo is accepted with hi unless
#                            lo < n and lo < 2^w mod n (rejected: None)
#   count(w, n, k, N)        #{x < N : draw(w, x, n) == Some{k}}
#   below(~S, ~next, f, n, s)  the bounded draw from a source: the first
#                            accepted draw among 1 + f draws (Go's loop,
#                            which is unbounded; the last candidate if every
#                            draw is rejected)
#   occurrences(~rel, v, xs) #{i : rel(xs[i], v)}: two lists are permutations
#                            of each other when these agree for an equality
#                            rel and every v

def b2n(b: Bool) -> Nat:
  match b:
    case True{}:
      1n
    case False{}:
      0n

def and_bits(w: Nat, +a: Nat, +b: Nat) -> Nat:
  match w:
    case 0n:
      0n
    case 1n+k:
      Nat.add(Nat.mul(C.bit(a), C.bit(b)), Nat.double(and_bits(k, C.half(a), C.half(b))))

def pow2mod(w: Nat, +n: Nat) -> Nat:
  match w:
    case 0n:
      Nat.mod(1n, n)
    case 1n+k:
      Nat.mod(Nat.double(pow2mod(k, n)), n)

def accept(+hi: Nat, ok: Bool) -> Maybe<&2, Nat>:
  match ok:
    case True{}:
      Some{hi}
    case False{}:
      None{}

# Lemire: the product x * n = hi * 2^w + lo
def lemire(+w: Nat, +n: Nat, +hi: Nat, +lo: Nat) -> Maybe<&2, Nat>:
  accept(hi, Bool.not(Bool.and(Nat.is_lt(lo, n), Nat.is_lt(lo, pow2mod(w, n)))))

def draw_pos(+w: Nat, +x: Nat, +n: Nat, +m: Nat, pow2: Bool) -> Maybe<&2, Nat>:
  match pow2:
    case True{}:
      Some{and_bits(w, x, m)}
    case False{}:
      lemire(w, n, C.high(w, Nat.mul(x, n)), C.low(w, Nat.mul(x, n)))

def draw(+w: Nat, +x: Nat, n: Nat) -> Maybe<&2, Nat>:
  match n:
    case 0n:
      Some{x}
    case 1n+ +m:
      draw_pos(w, x, 1n+m, m, Nat.is_eq(and_bits(w, 1n+m, m), 0n))

def hit(m: Maybe<&2, Nat>, +k: Nat) -> Nat:
  match m:
    case None{}:
      0n
    case Some{v}:
      b2n(Nat.is_eq(v, k))

# the number of source outputs x < N that draw k
def count(+w: Nat, +n: Nat, +k: Nat, N: Nat) -> Nat:
  match N:
    case 0n:
      0n
    case 1n+ +x:
      Nat.add(count(w, n, k, x), hit(draw(w, x, n), k))

# the bounded draw once a draw of x (with verdict m) has left state s: m if
# accepted, else (while fuel lasts) the next draw; with no fuel left, the
# last candidate floor(x n / 2^64). The verdict is matched before the
# recursion, so a draw that is not yet decided keeps the rest unexpanded.
def below_go(~S: Data, ~next: S -> W.U64 & S, fuel: Nat, +n: Nat, m: Maybe<&2, Nat>, +x: Nat, +s: S) -> Nat & S:
  match fuel m:
    case 0n Some{k}:
      (k, s)
    case 0n None{}:
      (C.high(64n, Nat.mul(x, n)), s)
    case 1n+f Some{k}:
      (k, s)
    case 1n+f None{}:
      below_go(~S, ~next, f, n, draw(64n, SW.value(SRC.fst64(S, next(s))), n), SW.value(SRC.fst64(S, next(s))), SRC.snd64(S, next(s)))

# the first accepted draw of 64-bit outputs among fuel + 1 draws
def below(~S: Data, ~next: S -> W.U64 & S, fuel: Nat, +n: Nat, +s: S) -> Nat & S:
  below_go(~S, ~next, fuel, n, draw(64n, SW.value(SRC.fst64(S, next(s))), n), SW.value(SRC.fst64(S, next(s))), SRC.snd64(S, next(s)))

def occurrences(~A: Data, ~V: Data, ~rel: A -> V -> Bool, +v: V, xs: List<&2, A>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{+x, rest}:
      Nat.add(b2n(rel(x, v)), occurrences(~A, ~V, ~rel, v, rest))

# the array of an (array, source) pair
def afst(-A: Data, -S: Data, p: Array<A> & S) -> Array<A>:
  (a, s) = p
  a
