# Map.get floor probe (docs/C_EQUIVALENCE.md, lru): 10^6 native Map.get on
# 1-character String keys over maps of 64 and 262144 keys. Prints the two
# elapsed millisecond counts (the second includes building the large map).
import Base

def key(+i: U32) -> String:
  SCon{Chr{U32.add(i, 65536)}, SNil{}}

def build(k: Nat, m: Map<&2, U32>, +i: U32) -> Map<&2, U32>:
  match k:
    case 0n:
      m
    case 1n+p:
      build(p, Map.set(&2, U32, m, key(i), i), U32.inc(i))

def fin(+c: U32, +r: U32, p: Map<&2, U32> & U32) -> Map<&2, U32> & U32:
  (m, v) = p
  (m, U32.add(U32.mul(c, 31), v))

def pc(st: Map<&2, U32> & U32) -> U32:
  (m, c) = st
  c

def step(st: Map<&2, U32> & U32, +r: U32, +n: U32) -> Map<&2, U32> & U32:
  (m, +c) = st
  fin(c, r, Map.get(U32, 0, m, key(U32.mod(r, n))))

def loop(k: Nat, st: Map<&2, U32> & U32, +r: U32, +n: U32) -> U32:
  match k:
    case 0n:
      pc(st)
    case 1n+p:
      loop(p, step(st, r, n), U32.add(U32.mul(r, 1664525), 1013904223), n)

def go(+n: U32, +k: Nat) -> U32:
  loop(k, (build(U32.to_nat(n), Map.new(&2, U32), 0), 0), 7, n)

def main() -> IO(Unit):
  do IO<Unit>:
    raw : List<String> <- IO.args()
    t0 : Nat <- IO.now()
    IO.print_err(U32.show(go(64, 1000000n)))
    t1 : Nat <- IO.now()
    d1 : Nat = Nat.sub(t1, t0)
    t2 : Nat <- IO.now()
    IO.print_err(U32.show(go(262144, 1000000n)))
    t3 : Nat <- IO.now()
    IO.print(String.append(Nat.show(d1), String.append(" ", Nat.show(Nat.sub(t3, t2)))))
