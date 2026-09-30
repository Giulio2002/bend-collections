import Base
import ../../src/containers/lru.bend as LR
import ../../src/math/u64.bend as W
import ../support/text.bend as X
import ./lib.bend as L

# Backend-differential driver (tools/backend_diff.py): src/containers/lru.bend.
# argv = [capacity, op tokens...]; one LRU<U32> is threaded through the
# tokens "code:key:v:now_lo:now_hi:r" and every token prints one line.
#
#   0 add(key, v, now)   1 get(key, now)   2 peek(key, now)   3 contains(key, now)
#   4 remove(key)        5 keys(now)       6 resize(r)        7 set_lifetime(r)
#   8 purge              9 len             10 the ten counter words

def show_m(m: Maybe<&2, U32>) -> String:
  match m:
    case None{}:
      "-"
    case Some{v}:
      U32.show(v)

def show_z(r: Result<&2, &2, String, U32>) -> String:
  match r:
    case Fail{s}:
      "ERR " ++ s
    case Done{n}:
      "OK " ++ U32.show(n)

def ctr_go(n: Nat, +i: U32, r: Array<U32> & U32, acc: String) -> String:
  match n:
    case 0n:
      (m, x) = r
      acc ++ U32.show(x)
    case 1n+p:
      (m, x) = r
      ctr_go(p, U32.inc(i), Array.get(U32, m, U32.inc(i)), acc ++ U32.show(x) ++ ",")

def o_b(acc: List<&2, String>, x: LR.LRU<&2, U32> & Bool) -> LR.LRU<&2, U32> & List<&2, String>:
  (f, b) = x
  (f, Con{L.bool(b), acc})

def o_m(acc: List<&2, String>, x: LR.LRU<&2, U32> & Maybe<&2, U32>) -> LR.LRU<&2, U32> & List<&2, String>:
  (f, m) = x
  (f, Con{show_m(m), acc})

def o_k(acc: List<&2, String>, x: LR.LRU<&2, U32> & List<&2, String>) -> LR.LRU<&2, U32> & List<&2, String>:
  (f, ks) = x
  (f, Con{"K " ++ String.join(ks, ","), acc})

def o_z(acc: List<&2, String>, x: LR.LRU<&2, U32> & Result<&2, &2, String, U32>) -> LR.LRU<&2, U32> & List<&2, String>:
  (f, r) = x
  (f, Con{show_z(r), acc})

def o_u(acc: List<&2, String>, x: LR.LRU<&2, U32> & U32) -> LR.LRU<&2, U32> & List<&2, String>:
  (f, n) = x
  (f, Con{U32.show(n), acc})

def o_c(acc: List<&2, String>, x: LR.LRU<&2, U32> & Array<U32>) -> LR.LRU<&2, U32> & List<&2, String>:
  (f, m) = x
  (f, Con{ctr_go(9n, 16, Array.get(U32, m, 16), ""), acc})

def op(k: Nat, f: LR.LRU<&2, U32>, acc: List<&2, String>, key: String, v: U32, now: W.U64, +r: U32) -> LR.LRU<&2, U32> & List<&2, String>:
  match k:
    case 0n:
      o_b(acc, LR.add(&2, U32, f, key, v, now))
    case 1n:
      o_m(acc, LR.get(U32, f, key, now))
    case 2n:
      o_m(acc, LR.peek(U32, f, key, now))
    case 3n:
      o_b(acc, LR.contains(&2, U32, f, key, now))
    case 4n:
      o_m(acc, LR.remove(&2, U32, f, key))
    case 5n:
      o_k(acc, LR.keys(&2, U32, f, now))
    case 6n:
      o_z(acc, LR.resize(&2, U32, f, r))
    case 7n:
      (LR.set_lifetime_packed(&2, U32, f, W.U64{r, 0}), Con{"ok", acc})
    case 8n:
      o_u(acc, LR.purge(&2, U32, f))
    case 9n:
      o_u(acc, LR.len(&2, U32, f))
    case 10n+x:
      o_c(acc, LR.counters(&2, U32, f))

def step(tok: String, s: LR.LRU<&2, U32> & List<&2, String>) -> LR.LRU<&2, U32> & List<&2, String>:
  (f, acc) = s
  +p = X.fields(tok)
  op(X.nat_field(p, 0n), f, acc, X.field(p, 1n), X.u32_field(p, 2n), W.U64{X.u32_field(p, 3n), X.u32_field(p, 4n)}, X.u32_field(p, 5n))

def fin(s: LR.LRU<&2, U32> & List<&2, String>) -> List<&2, String>:
  (f, acc) = s
  List.reverse(&2, String, acc)

def go(xs: List<&2, String>, s: LR.LRU<&2, U32> & List<&2, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      fin(s)
    case Con{h, t}:
      go(t, step(h, s))

def made(m: LR.Made<&2, U32>) -> LR.LRU<&2, U32> & List<&2, String>:
  match m:
    case LR.Made{f}:
      (f, Con{"made", Nil{}})
    case LR.Rejected{r}:
      (LR.init(&2, U32, 3), Con{"rejected", Nil{}})

def start(xs: List<&2, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      go(t, made(LR.new(&2, U32, X.u32_of(h))))

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    X.print_lines(start(X.program_args(args)))
