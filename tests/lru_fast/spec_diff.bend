import Base
import ../../src/lru/fast.bend as F
import ../../src/lru/wide.bend as W
import ../../types/lru_model.bend as T
import ../../types/lru_fast.bend as E
import ../../spec/lru_fast.bend as S

# Differential test of the indexed LRU runtime (src/lru/fast.bend) against
# its independent specification (spec/lru_fast.bend): random operation
# histories over a small key pool, with lifetimes, expiry, capacity changes
# and purges, compared observation by observation. Prints the number of
# mismatching observations per seed (expected 0).

def lcg(s: U32) -> U32:
  U32.add(U32.mul(s, 1664525), 1013904223)

def key_n(n: Nat) -> String:
  match n:
    case 0n:
      "a"
    case 1n:
      "b"
    case 2n:
      "c"
    case 3n:
      "dd"
    case 4n:
      "e"
    case _:
      "f"

def key_of(+r: U32) -> String:
  key_n(U32.to_nat(U32.mod(U32.shr(r), 6)))

def time_of(+r: U32) -> T.Int64:
  T.I64{W.pack(U32.mod(U32.shr(U32.shr(r)), 6), 0)}

def life_n(n: Nat) -> T.Int64:
  match n:
    case 0n:
      T.I64{W.pack(0, 0)}
    case 1n:
      T.I64{W.pack(1000000, 0)}
    case _:
      T.I64{W.pack(2000000, 0)}

def life_of(+r: U32) -> T.Int64:
  life_n(U32.to_nat(U32.mod(U32.shr(r), 3)))

def op_n(+r: U32, n: Nat) -> E.Op<U32>:
  match n:
    case 0n:
      E.Len{}
    case 1n:
      E.Capacity{}
    case 2n:
      E.SetLifetime{life_of(lcg(r))}
    case 3n:
      E.Metrics{}
    case 4n:
      E.Get{key_of(lcg(r)), time_of(lcg(lcg(r)))}
    case 5n:
      E.Peek{key_of(lcg(r)), time_of(lcg(lcg(r)))}
    case 6n:
      E.Contains{key_of(lcg(r)), time_of(lcg(lcg(r)))}
    case 7n:
      E.Remove{key_of(lcg(r))}
    case 8n:
      E.Purge{}
    case 9n:
      E.Resize{U32.mod(U32.shr(lcg(r)), 5)}
    case 10n:
      E.Keys{time_of(lcg(r))}
    case _:
      E.Add{key_of(lcg(r)), U32.shr(lcg(lcg(r))), time_of(lcg(lcg(lcg(r))))}

def op_of(+r: U32) -> E.Op<U32>:
  op_n(r, U32.to_nat(U32.mod(r, 16)))

def ops_go(n: Nat, +r: U32) -> List<&2, E.Op<U32>>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      Con{op_of(r), ops_go(p, lcg(lcg(lcg(lcg(r)))))}

def weq(a: Word(64n), b: Word(64n)) -> Bool:
  Cmp.is_eq(Word.cmp(64n, a, b))

def ws_eq(a: List<&2, Word(64n)>, b: List<&2, Word(64n)>) -> Bool:
  match a b:
    case Nil{} Nil{}:
      True{}
    case Con{x, xs} Con{y, ys}:
      weq(x, y) && ws_eq(xs, ys)
    case _ _:
      False{}

def ks_eq(a: List<&2, String>, b: List<&2, String>) -> Bool:
  match a b:
    case Nil{} Nil{}:
      True{}
    case Con{x, xs} Con{y, ys}:
      String.eq(x, y) && ks_eq(xs, ys)
    case _ _:
      False{}

def mv_eq(a: Maybe<&2, U32>, b: Maybe<&2, U32>) -> Bool:
  match a b:
    case None{} None{}:
      True{}
    case Some{x} Some{y}:
      U32.is_eq(x, y)
    case _ _:
      False{}

def rs_eq(a: Result<&2, &2, String, U32>, b: Result<&2, &2, String, U32>) -> Bool:
  match a b:
    case Fail{x} Fail{y}:
      String.eq(x, y)
    case Done{x} Done{y}:
      U32.is_eq(x, y)
    case _ _:
      False{}

def bool_eq(a: Bool, b: Bool) -> Bool:
  match a b:
    case True{} True{}:
      True{}
    case False{} False{}:
      True{}
    case _ _:
      False{}

def obs_eq(a: E.Obs<U32>, b: E.Obs<U32>) -> Bool:
  match a b:
    case E.ONum{x} E.ONum{y}:
      U32.is_eq(x, y)
    case E.OMetrics{T.Counts{x}} E.OMetrics{T.Counts{y}}:
      ws_eq(x, y)
    case E.OFlag{x} E.OFlag{y}:
      bool_eq(x, y)
    case E.OVal{x} E.OVal{y}:
      mv_eq(x, y)
    case E.OResized{x} E.OResized{y}:
      rs_eq(x, y)
    case E.OKeys{x} E.OKeys{y}:
      ks_eq(x, y)
    case E.OUnit{} E.OUnit{}:
      True{}
    case _ _:
      False{}

def bad1(b: Bool) -> Nat:
  match b:
    case True{}:
      0n
    case False{}:
      1n

def count_bad(a: List<&2, E.Obs<U32>>, b: List<&2, E.Obs<U32>>) -> Nat:
  match a b:
    case Nil{} Nil{}:
      0n
    case Con{x, xs} Con{y, ys}:
      Nat.add(bad1(obs_eq(x, y)), count_bad(xs, ys))
    case _ _:
      1000n

def fast_obs(r: F.Fast<U32> & List<&2, E.Obs<U32>>) -> List<&2, E.Obs<U32>>:
  (f, os) = r
  os

def spec_obs(r: S.Model<U32> & List<&2, E.Obs<U32>>) -> List<&2, E.Obs<U32>>:
  (s, os) = r
  os

def run_seed(+cap: U32, +seed: U32, +n: Nat) -> Nat:
  count_bad(fast_obs(F.run(~U32, ops_go(n, seed), F.init(~U32, cap))),
            spec_obs(S.run(U32, ops_go(n, seed), S.LM{cap, S.zero_time(), Nil{}, T.zero_metrics()})))

def main() -> List<&2, Nat>:
  [run_seed(1, 7, 300n), run_seed(2, 11, 300n), run_seed(3, 23, 300n), run_seed(4, 37, 300n), run_seed(3, 101, 300n), run_seed(5, 202, 300n)]
