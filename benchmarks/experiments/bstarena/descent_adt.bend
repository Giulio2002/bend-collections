import Base

# EXPERIMENT ONLY (not a gate input, not evidence for acceptance).
#
# The ADT counterpart of benchmarks/experiments/bstarena/descent.bend: the
# SAME data dependent six level descent, over a SHARED algebraic tree instead
# of a native indexed block. The tree is `+`-reusable (as every read of
# reference/legacy_balanced_search_tree.bend's persistent tree is), so opening a node has
# to retain its fields and release the ones the walk does not follow. The
# difference between the two programs is the cost of that reference counting.

def lcg(+x: U32) -> U32:
  U32.add(U32.mul(x, 1664525), 1013904223)

type T is Data:
  L{v: U32}
  N{l: T, v: U32, r: T}

def build(d: Nat, +v: U32) -> T:
  match d:
    case 0n:
      L{v}
    case 1n+ +p:
      N{build(p, v), v, build(p, U32.inc(v))}

type Dn is Data:
  DN{t: T, cur: U32, r: U32}

def dn_pick(l: T, +v: U32, r2: T, +cur: U32, +r: U32, +b: U32) -> Dn:
  match b:
    case 0:
      DN{l, cur, r}
    case _:
      DN{r2, cur, r}

def dn_go(t: T, +cur: U32, +r: U32, +b: U32) -> Dn:
  match t:
    case L{+v}:
      DN{L{v}, U32.add(cur, v), U32.shrn(r, 1n)}
    case N{l, +v, r2}:
      dn_pick(l, v, r2, U32.add(cur, v), U32.shrn(r, 1n), b)

def dn_one(s: Dn) -> Dn:
  DN{t, +cur, +r} = s
  dn_go(t, cur, r, U32.and(r, 1))

def dn_loop(fuel: Nat, s: Dn) -> Dn:
  match fuel:
    case 0n:
      s
    case 1n+f:
      dn_loop(f, dn_one(s))

# t0 is the ORIGINAL tree, handed back untouched: the walk therefore runs on
# a SHARED tree (the `+t` of `step` makes it reusable and it is used twice),
# exactly as every read of reference/legacy_balanced_search_tree.bend does. Without this
# the walk would consume the tree and destroy it after one iteration.
def step_fin(+c: U32, t0: T, s: Dn) -> T & U32:
  DN{t, +cur, r} = s
  (t0, U32.add(U32.mul(c, 31), cur))

def step(+c: U32, +t: T) -> T & U32:
  step_fin(c, t, dn_loop(6n, DN{t, 0, c}))

def loop_step(p: T & U32) -> T & U32:
  (+t, +c) = p
  step(lcg(c), t)

def loop(k: Nat, p: T & U32) -> T & U32:
  match k:
    case 0n:
      p
    case 1n+j:
      loop(j, loop_step(p))

def fin(p: T & U32) -> U32:
  (t, c) = p
  c

def main() -> IO(Unit):
  do IO<Unit>:
    t0 : Nat <- IO.now()
    IO.print_err(U32.show(fin(loop(10000000n, (build(6n, 1), 12345)))))
    t1 : Nat <- IO.now()
    IO.print(Nat.show(Nat.sub(t1, t0)))
