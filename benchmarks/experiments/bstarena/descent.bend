import Base

# EXPERIMENT ONLY (not a gate input, not evidence for acceptance).
#
# Cost of ONE level of a data dependent descent over a native indexed block,
# to compare with the ADT red-black tree of src/balanced_search_tree.bend.
# `ch` is a block of 2^d child slots holding ch[j] = j mod 64; at each level
# the walk reads ch[2*cur + bit], where bit comes from the pseudo random
# stream, so the SLOT the next load reads is computed from the value the
# previous load returned -- a genuine pointer chase whose addresses vary and
# which the compiler cannot hoist out of the loop. Its ADT counterpart
# descent_adt.bend walks exactly the same six levels over a shared algebraic
# tree.

def lcg(+x: U32) -> U32:
  U32.add(U32.mul(x, 1664525), 1013904223)

type Dn is Type:
  DN{ch: Array<U32>, cur: U32, r: U32}

def dn_at(+r: U32, p: Array<U32> & U32) -> Dn:
  (ch, +nx) = p
  DN{ch, nx, r}

def dn_one(s: Dn) -> Dn:
  DN{ch, +cur, +r} = s
  dn_at(U32.shrn(r, 1n), Array.get(U32, ch, U32.add(U32.mul(cur, 2), U32.and(r, 1))))

def dn_go(fuel: Nat, s: Dn) -> Dn:
  match fuel:
    case 0n:
      s
    case 1n+f:
      dn_go(f, dn_one(s))

def fill(k: Nat, ch: Array<U32>, +m: U32) -> Array<U32>:
  match k:
    case 0n:
      ch
    case 1n+ +j:
      fill(j, Array.set(U32, ch, U32.from_nat(j), U32.and(U32.from_nat(j), m)), m)

def step_fin(+c: U32, s: Dn) -> Array<U32> & U32:
  DN{ch, +cur, r} = s
  (ch, U32.add(U32.mul(c, 31), cur))

def step(+c: U32, ch: Array<U32>) -> Array<U32> & U32:
  step_fin(c, dn_go(6n, DN{ch, 0, c}))

def loop_step(p: Array<U32> & U32) -> Array<U32> & U32:
  (ch, +c) = p
  step(lcg(c), ch)

def loop(k: Nat, p: Array<U32> & U32) -> Array<U32> & U32:
  match k:
    case 0n:
      p
    case 1n+j:
      loop(j, loop_step(p))

def fin(p: Array<U32> & U32) -> U32:
  (ch, c) = p
  c

def main() -> IO(Unit):
  do IO<Unit>:
    t0 : Nat <- IO.now()
    IO.print_err(U32.show(fin(loop(10000000n, (fill(128n, Array.new(U32, 7n, 0), 63), 12345)))))
    t1 : Nat <- IO.now()
    IO.print(Nat.show(Nat.sub(t1, t0)))
