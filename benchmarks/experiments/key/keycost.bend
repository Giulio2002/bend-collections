import Base

# How much does building one ten-character Base String key cost?
# Same characters as benchmarks/bend/prefix_trie.bend and the pinned
# benchmarks/native/prefix_trie.c: 'a' + two bits of the value stream.
# No trie is imported, so no String value is shared anywhere in this program
# and the cells carry no refcount seal.

def lcg(+x: U32) -> U32:
  U32.add(U32.mul(x, 1664525), 1013904223)

def wrap0(b: Bool, +s: U32) -> U32:
  match b:
    case True{}:
      0
    case False{}:
      s

def key_word(wrap: Bool, +w: U32, +r: U32) -> U32:
  match wrap:
    case True{}:
      r
    case False{}:
      U32.shrn(w, 2n)

def key_go(m: Nat, +w: U32, +s: U32, +r: U32) -> String:
  match m:
    case 0n:
      SNil{}
    case 1n+p:
      SCon{Chr{U32.add(97, U32.and(w, 3))}, key_go(p, key_word(U32.is_eq(U32.add(s, 2), 30), w, r), wrap0(U32.is_eq(U32.add(s, 2), 30), U32.add(s, 2)), r)}

def key_of(m: Nat, +r: U32) -> String:
  key_go(m, U32.shrn(r, 16n), 16, r)

def fold_key(k: String, c: U32) -> U32:
  match k:
    case SNil{}:
      c
    case SCon{Chr{x}, t}:
      fold_key(t, U32.add(U32.mul(c, 31), x))

def step(+r: U32, c: U32) -> U32 & U32:
  (lcg(r), fold_key(key_of(10n, r), c))

def loop(k: Nat, +r: U32, c: U32) -> U32:
  match k:
    case 0n:
      c
    case 1n+p:
      loop(p, lcg(r), fold_key(key_of(10n, r), c))

def main() -> IO(Unit):
  do IO<Unit>:
    t0 : Nat <- IO.now()
    IO.print_err(U32.show(loop(1000000n, 12345, 0)))
    t1 : Nat <- IO.now()
    IO.print(Nat.show(Nat.sub(t1, t0)))
