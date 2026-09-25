import Base
import ../../src/containers/lru.bend as LR
import ../../src/math/u64.bend as W
import ../../spec/containers/lru.bend as SP
import ../support/text.bend as X

# Differential check of the LRU against its specification
# (spec/containers/lru.bend): argv = seed, operation count. Random operations on a
# small key set, with lifetimes and a moving clock; after every operation the
# results, the length and the five counters must agree. Prints "OK <n>" or
# "MISMATCH <op index> <op>".

def lcg(+x: U32) -> U32:
  U32.add(U32.mul(x, 1664525), 1013904223)

def nth(n: Nat, xs: List<&2, String>) -> String:
  match n xs:
    case 0n Con{x, t}:
      x
    case 1n+p Con{x, t}:
      nth(p, t)
    case _ Nil{}:
      "zz"

def key_of(+i: U32) -> String:
  nth(U32.to_nat(U32.and(i, 7)), Con{"a", Con{"b", Con{"", Con{"ab", Con{"hello", Con{SCon{Chr{3000000000}, SNil{}}, Con{"c", Con{"zz", Nil{}}}}}}}}})

def m_eq(a: Maybe<&2, U32>, b: Maybe<&2, U32>) -> Bool:
  match a b:
    case None{} None{}:
      True{}
    case Some{+x} Some{+y}:
      U32.is_eq(x, y)
    case _ _:
      False{}

def u64_eq(a: W.U64, b: W.U64) -> Bool:
  match a b:
    case W.U64{+x, +y} W.U64{+z, +w}:
      Bool.and(U32.is_eq(x, z), U32.is_eq(y, w))

def keys_eq(a: List<&2, String>, b: List<&2, String>) -> Bool:
  match a b:
    case Nil{} Nil{}:
      True{}
    case Con{x, s} Con{y, t}:
      Bool.and(String.eq(x, y), keys_eq(s, t))
    case _ _:
      False{}

def rz_eq(a: Result<&2, &2, String, U32>, b: Result<&2, &2, String, U32>) -> Bool:
  match a b:
    case Done{+x} Done{+y}:
      U32.is_eq(x, y)
    case Fail{s} Fail{t}:
      String.eq(s, t)
    case _ _:
      False{}

def hi64(+lo: U32, r: Array<U32> & U32) -> Array<U32> & W.U64:
  (m, +hi) = r
  (m, W.U64{lo, hi})

def lo64(+i: U32, r: Array<U32> & U32) -> Array<U32> & W.U64:
  (m, +lo) = r
  hi64(lo, Array.get(U32, m, U32.inc(i)))

def get64(m: Array<U32>, +i: U32) -> Array<U32> & W.U64:
  lo64(i, Array.get(U32, m, i))

def c_fin(x: W.U64, r: Array<U32> & W.U64, +ok: Bool) -> Array<U32> & Bool:
  (m, y) = r
  (m, Bool.and(ok, u64_eq(x, y)))

def c_at(m: Array<U32>, +i: U32, x: W.U64, +ok: Bool) -> Array<U32> & Bool:
  c_fin(x, get64(m, i), ok)

def c_all(r: Array<U32> & Bool) -> Bool:
  (m, b) = r
  b

def c_on(x: W.U64, +i: U32, r: Array<U32> & Bool) -> Array<U32> & Bool:
  (m, +ok) = r
  c_at(m, i, x, ok)

def ctr_eq(m: Array<U32>, c: SP.Ctr) -> Bool:
  SP.CT{a, b, d, e, g} = c
  c_all(c_on(g, 24, c_on(e, 22, c_on(d, 20, c_on(b, 18, c_at(m, 16, a, True{}))))))

type St is Type:
  S{f: LR.LRU<&2, U32>, l: SP.Lru<U32>, ok: Bool}

def ck_c(+l: SP.Lru<U32>, +n: U32, +ok: Bool, r: LR.LRU<&2, U32> & Array<U32>) -> St:
  (f, m) = r
  S{f, l, Bool.and(ok, Bool.and(U32.is_eq(n, SP.len(~U32, l)), ctr_eq(m, SP.counters(~U32, l))))}

def ck_n(l: SP.Lru<U32>, +ok: Bool, r: LR.LRU<&2, U32> & U32) -> St:
  (f, +n) = r
  ck_c(l, n, ok, LR.counters(&2, U32, f))

# after every operation: the length and the counters agree
def check(s: St) -> St:
  S{f, l, +ok} = s
  ck_n(l, ok, LR.len(&2, U32, f))

def beq(+b: Bool, +c: Bool) -> Bool:
  Bool.or(Bool.and(b, c), Bool.and(Bool.not(b), Bool.not(c)))

def r_b(+ok: Bool, x: LR.LRU<&2, U32> & Bool, y: SP.Lru<U32> & Bool) -> St:
  (f, +b) = x
  (l, +c) = y
  S{f, l, Bool.and(ok, beq(b, c))}

def r_m(+ok: Bool, x: LR.LRU<&2, U32> & Maybe<&2, U32>, y: SP.Lru<U32> & Maybe<&2, U32>) -> St:
  (f, a) = x
  (l, b) = y
  S{f, l, Bool.and(ok, m_eq(a, b))}

def r_k(+ok: Bool, x: LR.LRU<&2, U32> & List<&2, String>, y: SP.Lru<U32> & List<&2, String>) -> St:
  (f, a) = x
  (l, b) = y
  S{f, l, Bool.and(ok, keys_eq(a, b))}

def r_z(+ok: Bool, x: LR.LRU<&2, U32> & Result<&2, &2, String, U32>, y: SP.Lru<U32> & Result<&2, &2, String, U32>) -> St:
  (f, a) = x
  (l, b) = y
  S{f, l, Bool.and(ok, rz_eq(a, b))}

def r_u(+ok: Bool, x: LR.LRU<&2, U32> & U32, y: SP.Lru<U32> & U32) -> St:
  (f, +a) = x
  (l, +b) = y
  S{f, l, Bool.and(ok, U32.is_eq(a, b))}

def op(+k: Nat, f: LR.LRU<&2, U32>, l: SP.Lru<U32>, +ok: Bool, +key: String, +v: U32, +now: W.U64, +r: U32) -> St:
  match k:
    case 0n:
      r_b(ok, LR.add(&2, U32, f, key, v, now), SP.add(~U32, l, key, v, now))
    case 1n:
      r_m(ok, LR.get(U32, f, key, now), SP.get(~U32, l, key, now))
    case 2n:
      r_m(ok, LR.peek(U32, f, key, now), SP.peek(~U32, l, key, now))
    case 3n:
      r_b(ok, LR.contains(&2, U32, f, key, now), SP.contains(~U32, l, key, now))
    case 4n:
      r_m(ok, LR.remove(&2, U32, f, key), SP.remove(~U32, l, key))
    case 5n:
      r_k(ok, LR.keys(&2, U32, f, now), SP.keys(~U32, l, now))
    case 6n:
      r_z(ok, LR.resize(&2, U32, f, U32.and(r, 3)), SP.resize(~U32, l, U32.and(r, 3)))
    case 7n:
      S{LR.set_lifetime_packed(&2, U32, f, W.U64{U32.mul(U32.and(r, 3), 1500000), 0}), SP.set_lifetime(~U32, l, W.U64{U32.mul(U32.and(r, 3), 1500000), 0}), ok}
    case 8n:
      r_u(ok, LR.purge(&2, U32, f), SP.purge(~U32, l))
    case _:
      r_m(ok, LR.get(U32, f, key, now), SP.get(~U32, l, key, now))

def op_of(+x: Nat) -> Nat:
  match x:
    case 0n:
      8n
    case 1n:
      6n
    case 2n:
      7n
    case _:
      Nat.mod(x, 6n)

def pick_op(+r: U32) -> Nat:
  op_of(U32.to_nat(U32.and(U32.shr(U32.shr(U32.shr(r))), 15)))

def sh(+n: Nat, +x: U32) -> U32:
  match n:
    case 0n:
      x
    case 1n+p:
      sh(p, U32.shr(x))

def op_s(+k: Nat, s: St, +key: String, +v: U32, +now: W.U64, +r: U32) -> St:
  S{f, l, +ok} = s
  op(k, f, l, ok, key, v, now, r)

# bad = 0 (no mismatch) or 1 + 16 * step + op of the first failing step
def fin(+i: Nat, +bad: Nat) -> String:
  match bad:
    case 0n:
      "OK " ++ Nat.show(i)
    case 1n+j:
      "MISMATCH step " ++ Nat.show(Nat.div(j, 16n)) ++ " op " ++ Nat.show(Nat.mod(j, 16n))

def first(+ok: Bool, +bad: Nat, +x: Nat) -> Nat:
  match ok:
    case True{}:
      bad
    case False{}:
      match bad:
        case 0n:
          1n+x
        case 1n+j:
          1n+j

# s is the state after step i - 1, whose op was pk
def run(fuel: Nat, s: St, +rng: U32, +t: U32, +i: Nat, +pk: Nat, +bad: Nat) -> String:
  match fuel s:
    case 0n S{f, l, +ok}:
      fin(i, first(ok, bad, Nat.add(Nat.mul(Nat.sub(i, 1n), 16n), pk)))
    case 1n+p S{f, l, +ok}:
      +r = lcg(rng)
      +k = pick_op(r)
      +t2 = U32.add(t, U32.and(sh(5n, r), 1))
      run(p, check(op(k, f, l, True{}, key_of(sh(8n, r)), U32.and(r, 65535), W.U64{t2, 0}, U32.shr(r))), r, t2, 1n+i, k, first(ok, bad, Nat.add(Nat.mul(Nat.sub(i, 1n), 16n), pk)))

def made(m: LR.Made<&2, U32>) -> LR.LRU<&2, U32>:
  match m:
    case LR.Made{f}:
      f
    case LR.Rejected{r}:
      LR.init(&2, U32, 3)

def go(+a: List<&2, String>) -> List<&2, String>:
  Con{run(X.nat_field(a, 1n), S{made(LR.new(&2, U32, 3)), SP.L{3, 0, W.zero(), Nil{}, SP.zero_ctr()}, True{}}, U32.from_nat(X.nat_field(a, 0n)), 1, 0n, 0n, 0n), Nil{}}

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    X.print_lines(go(X.shared(args)))
