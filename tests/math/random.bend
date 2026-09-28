import Base
import ../../src/math/u64.bend as W
import ../../src/math/w64.bend as XW
import ../../src/math/f64.bend as F
import ../../src/math/random.bend as R
import ../../src/math/random/rand.bend as RR
import ../../src/math/random/chacha8.bend as C8
import ../../src/math/random/chacha8/block.bend as B
import ../../src/math/random/pcg.bend as P
import ../../src/crypto/random.bend as CR
import ../support/text.bend as X

# Differential driver for src/math/random.bend and src/crypto/random.bend,
# checked by tools/check_random.py against Go's published vectors and a
# Python mirror of Go's math/rand/v2. The first argument picks a source:
#
#   c8:k0:...:k7        ChaCha8 keyed by eight little-endian words
#   c8b:b0:...:b31      ChaCha8 from a 32-byte seed (R.chacha8)
#   pcg:h1_l1:h2_l2     PCG with seeds seed1, seed2 (a U64 is "hi_lo")
#   cr:k0:...:k7        crypto/random's generator keyed by eight words
#   crb:b0:...:b31      crypto/random's generator from a 32-byte seed
#
# and every further argument is one call, printing one line:
#
#   u64 u32 i64 i32     raw words (a U64 prints "hi_lo")
#   n:h_l               uint64n       m:N   uint32n
#   i:N                 intn          r:LO:HI   int_range
#   f                   float64 (the binary64 bits, "hi_lo")
#   p:N                 perm(N)       s:N   shuffle of [100, 101, ..., 99 + N]
#   b:N                 N bytes (crypto/random only)
#   c:N:K               chi-square counts: K draws of uint64n(N), N counts

def u64_show(a: W.U64) -> String:
  match a:
    case W.U64{lo, hi}:
      U32.show(hi) ++ "_" ++ U32.show(lo)

def f64_show(a: F.F64) -> String:
  match a:
    case F.Bits{lo, hi}:
      U32.show(hi) ++ "_" ++ U32.show(lo)

def u64_parts(xs: List<&2, String>) -> W.U64:
  match xs:
    case Con{h, Con{l, t}}:
      W.U64{X.u32_of(l), X.u32_of(h)}
    case _:
      W.U64{0, 0}

def u64_read(s: String) -> W.U64:
  u64_parts(String.split(s, '_'))

def u32s(xs: List<&2, String>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{X.u32_of(h), u32s(t)}

def u32_range(n: Nat, +i: U32) -> List<&2, U32>:
  match n:
    case 0n:
      []
    case 1n+p:
      Con{i, u32_range(p, U32.add(i, 1))}

def zeros(n: Nat) -> List<&2, Nat>:
  match n:
    case 0n:
      []
    case 1n+p:
      Con{0n, zeros(p)}

def bump(xs: List<&2, Nat>, i: Nat) -> List<&2, Nat>:
  match xs i:
    case Nil{} _:
      Nil{}
    case Con{h, t} 0n:
      Con{Nat.add(h, 1n), t}
    case Con{h, t} 1n+p:
      Con{h, bump(t, p)}

type Acc<-S: Data> is Data:
  A{lines: List<&2, String>, s: S}

def emit(~T: Data, ~S: Data, ~sh: T -> String, acc: List<&2, String>, r: T & S) -> Acc<S>:
  (x, s) = r
  A{Con{sh(x), acc}, s}

def count_one(-S: Data, cs: List<&2, Nat>, r: W.U64 & S) -> List<&2, Nat> & S:
  (+x, s) = r
  (bump(cs, U32.to_nat(XW.lo(x))), s)

def chi_step(~S: Data, ~next: S -> W.U64 & S, +n: W.U64, st: List<&2, Nat> & S) -> List<&2, Nat> & S:
  (cs, s) = st
  count_one(S, cs, RR.uint64n(~S, ~next, s, n))

def chi(~S: Data, ~next: S -> W.U64 & S, k: Nat, +n: W.U64, st: List<&2, Nat> & S) -> List<&2, Nat> & S:
  match k:
    case 0n:
      st
    case 1n+p:
      chi(~S, ~next, p, n, chi_step(~S, ~next, n, st))

def chi_or(~S: Data, ~next: S -> W.U64 & S, +parts: List<&2, String>, acc: List<&2, String>, s: S, c: Bool) -> Acc<S>:
  match c:
    case True{}:
      emit(~List<&2, Nat>, ~S, ~X.join_nat, acc, chi(~S, ~next, X.nat_field(parts, 2n), W.U64{X.u32_field(parts, 1n), 0}, (zeros(X.nat_field(parts, 1n)), s)))
    case False{}:
      A{Con{"?", acc}, s}

def pick(~S: Data, ~next: S -> W.U64 & S, +parts: List<&2, String>, acc: List<&2, String>, s: S, is_c: Bool, a: Bool, b: Bool, c: Bool, d: Bool, e: Bool, f: Bool, g: Bool, h: Bool, i: Bool, j: Bool, k: Bool) -> Acc<S>:
  match a b c d e f g h i j k:
    case True{} _ _ _ _ _ _ _ _ _ _:
      emit(~W.U64, ~S, ~u64_show, acc, R.uint64(~S, ~next, s))
    case _ True{} _ _ _ _ _ _ _ _ _:
      emit(~U32, ~S, ~U32.show, acc, R.uint32(~S, ~next, s))
    case _ _ True{} _ _ _ _ _ _ _ _:
      emit(~W.U64, ~S, ~u64_show, acc, R.int64(~S, ~next, s))
    case _ _ _ True{} _ _ _ _ _ _ _:
      emit(~U32, ~S, ~U32.show, acc, R.int32(~S, ~next, s))
    case _ _ _ _ True{} _ _ _ _ _ _:
      emit(~W.U64, ~S, ~u64_show, acc, R.uint64n(~S, ~next, s, u64_read(X.field(parts, 1n))))
    case _ _ _ _ _ True{} _ _ _ _ _:
      emit(~U32, ~S, ~U32.show, acc, R.uint32n(~S, ~next, s, X.u32_field(parts, 1n)))
    case _ _ _ _ _ _ True{} _ _ _ _:
      emit(~Nat, ~S, ~Nat.show, acc, R.intn(~S, ~next, s, X.nat_field(parts, 1n)))
    case _ _ _ _ _ _ _ True{} _ _ _:
      emit(~Nat, ~S, ~Nat.show, acc, R.int_range(~S, ~next, s, X.nat_field(parts, 1n), X.nat_field(parts, 2n)))
    case _ _ _ _ _ _ _ _ True{} _ _:
      emit(~F.F64, ~S, ~f64_show, acc, R.float64(~S, ~next, s))
    case _ _ _ _ _ _ _ _ _ True{} _:
      emit(~List<&2, Nat>, ~S, ~X.join_nat, acc, R.perm(~S, ~next, s, X.nat_field(parts, 1n)))
    case _ _ _ _ _ _ _ _ _ _ True{}:
      emit(~List<&2, U32>, ~S, ~X.join_u32, acc, R.shuffle(~U32, ~S, ~next, s, u32_range(X.nat_field(parts, 1n), 100)))
    case _ _ _ _ _ _ _ _ _ _ _:
      chi_or(~S, ~next, parts, acc, s, is_c)

def apply(~S: Data, ~next: S -> W.U64 & S, tok: String, st: Acc<S>) -> Acc<S>:
  match st:
    case A{acc, s}:
      +parts = X.fields(tok)
      +op = X.field(parts, 0n)
      pick(~S, ~next, parts, acc, s, String.eq(op, "c"), String.eq(op, "u64"), String.eq(op, "u32"), String.eq(op, "i64"), String.eq(op, "i32"), String.eq(op, "n"), String.eq(op, "m"), String.eq(op, "i"), String.eq(op, "r"), String.eq(op, "f"), String.eq(op, "p"), String.eq(op, "s"))

def run(~S: Data, ~next: S -> W.U64 & S, toks: List<&2, String>, st: Acc<S>) -> Acc<S>:
  match toks:
    case Nil{}:
      st
    case Con{t, rest}:
      run(~S, ~next, rest, apply(~S, ~next, t, st))

def lines(-S: Data, st: Acc<S>) -> List<&2, String>:
  match st:
    case A{acc, s}:
      List.reverse(&2, String, acc)

def go(~S: Data, ~next: S -> W.U64 & S, s: S, toks: List<&2, String>) -> List<&2, String>:
  lines(S, run(~S, ~next, toks, A{[], s}))

# crypto/random: "b:N" reads bytes, everything else is the generic call
def bytes_op(+parts: List<&2, String>, st: Acc<CR.Gen>) -> Acc<CR.Gen>:
  match st:
    case A{acc, g}:
      emit(~List<&2, U32>, ~CR.Gen, ~X.join_u32, acc, CR.bytes(g, X.nat_field(parts, 1n)))

def apply_cr_b(+parts: List<&2, String>, tok: String, st: Acc<CR.Gen>, b: Bool) -> Acc<CR.Gen>:
  match b:
    case True{}:
      bytes_op(parts, st)
    case False{}:
      apply(~CR.Gen, ~CR.next, tok, st)

def apply_cr(+tok: String, st: Acc<CR.Gen>) -> Acc<CR.Gen>:
  +parts = X.fields(tok)
  apply_cr_b(parts, tok, st, String.eq(X.field(parts, 0n), "b"))

def run_cr(toks: List<&2, String>, st: Acc<CR.Gen>) -> Acc<CR.Gen>:
  match toks:
    case Nil{}:
      st
    case Con{t, rest}:
      run_cr(rest, apply_cr(t, st))

def key(+ps: List<&2, String>) -> B.Key:
  B.K{X.u32_field(ps, 1n), X.u32_field(ps, 2n), X.u32_field(ps, 3n), X.u32_field(ps, 4n), X.u32_field(ps, 5n), X.u32_field(ps, 6n), X.u32_field(ps, 7n), X.u32_field(ps, 8n)}

def tail(xs: List<&2, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      t

def c8b(m: Maybe<&2, C8.ChaCha8>, toks: List<&2, String>) -> List<&2, String>:
  match m:
    case None{}:
      ["bad seed"]
    case Some{g}:
      go(~C8.ChaCha8, ~R.chacha8_next, g, toks)

def crb(m: Maybe<&2, CR.Gen>, toks: List<&2, String>) -> List<&2, String>:
  match m:
    case None{}:
      ["bad seed"]
    case Some{g}:
      lines(CR.Gen, run_cr(toks, A{[], g}))

def by_kind(+ps: List<&2, String>, toks: List<&2, String>, a: Bool, b: Bool, c: Bool, d: Bool, e: Bool) -> List<&2, String>:
  match a b c d e:
    case True{} _ _ _ _:
      go(~C8.ChaCha8, ~R.chacha8_next, C8.of_key(key(ps)), toks)
    case _ True{} _ _ _:
      c8b(R.chacha8(u32s(tail(ps))), toks)
    case _ _ True{} _ _:
      go(~P.PCG, ~R.pcg_next, R.pcg(u64_read(X.field(ps, 1n)), u64_read(X.field(ps, 2n))), toks)
    case _ _ _ True{} _:
      lines(CR.Gen, run_cr(toks, A{[], CR.of_words(X.u32_field(ps, 1n), X.u32_field(ps, 2n), X.u32_field(ps, 3n), X.u32_field(ps, 4n), X.u32_field(ps, 5n), X.u32_field(ps, 6n), X.u32_field(ps, 7n), X.u32_field(ps, 8n))}))
    case _ _ _ _ True{}:
      crb(CR.new(u32s(tail(ps))), toks)
    case _ _ _ _ _:
      ["unknown source"]

def all(args: List<&2, String>) -> List<&2, String>:
  match args:
    case Nil{}:
      ["usage: source ops..."]
    case Con{src, toks}:
      +ps = X.fields(src)
      +kind = X.field(ps, 0n)
      by_kind(ps, toks, String.eq(kind, "c8"), String.eq(kind, "c8b"), String.eq(kind, "pcg"), String.eq(kind, "cr"), String.eq(kind, "crb"))

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    X.print_lines(all(X.program_args(args)))
