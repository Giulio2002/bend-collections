import Base

# Cost model of the Bend native C backend: what the *primitives* the data
# structures are built from cost, measured the same way on both sides.
#
#   bend benchmarks/micro.bend -o build/bench/micro && build/bench/micro --threads 1
#   cc -O3 -march=native -std=c11 -o build/bench/micro_ref benchmarks/native/micro.c
#
# benchmarks/native/micro.c performs the identical work. tools/costmodel.py
# builds and runs both and writes build/performance/costmodel.json.
#
# Four primitives, each timed over the same number of operations:
#   arith  one LCG step and an add                      (pure U32 arithmetic)
#   array  one indexed read + one indexed write of a 4096-slot Base.Array
#   list   one step of a cons-list traversal            (4096-node lists)
#   alloc  one node of a freshly built + consumed binary tree (4095 nodes)
#
# The point of the table is that `array` is the only one of the four that is
# competitive with C: a structure whose operations are indexed array accesses
# can meet the 2.5x contract, and a structure whose operations allocate and
# walk cons cells or tree nodes cannot.

type Wd is Data:
  W{v: U32}

type Tr is Data:
  Leaf{v: U32}
  Node{l: Tr, r: Tr}

def lcg(s: U32) -> U32:
  U32.add(U32.mul(s, 1664525), 1013904223)

# ---- arithmetic ----

def arith(k: Nat, s: U32, acc: U32) -> U32:
  match k:
    case 0n:
      acc
    case 1n+p:
      +s2 = lcg(s)
      arith(p, s2, U32.add(acc, s2))

# ---- indexed array read + write ----

def bump(r: Array<Wd> & Wd, +i: U32, acc: U32) -> Array<Wd> & U32:
  (a, x) = r
  match x:
    case W{+v}:
      (Array.set(Wd, a, i, W{U32.add(v, 1)}), U32.add(acc, v))

def arr_step(p: Array<Wd> & U32, +i: U32) -> Array<Wd> & U32:
  (a, acc) = p
  bump(Array.get(Wd, a, i), i, acc)

def arr(k: Nat, s: U32, p: Array<Wd> & U32) -> Array<Wd> & U32:
  match k:
    case 0n:
      p
    case 1n+q:
      +s2 = lcg(s)
      arr(q, s2, arr_step(p, U32.mod(s2, 4096)))

def arr_drop(x: U32, xs: List<Wd>) -> U32:
  match xs:
    case Nil{}:
      x
    case Con{y, t}:
      arr_drop(x, t)

def arr_fin(p: Array<Wd> & U32) -> U32:
  (a, x) = p
  arr_drop(x, Array.to_list(~Wd, a))

# ---- cons-list traversal ----

def mklist(n: Nat, +v: U32) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      Con{v, mklist(p, v)}

def walk(xs: List<&2, U32>, acc: U32) -> U32:
  match xs:
    case Nil{}:
      acc
    case Con{x, t}:
      walk(t, U32.add(acc, x))

def list_rounds(k: Nat, +xs: List<&2, U32>, acc: U32) -> U32:
  match k:
    case 0n:
      acc
    case 1n+p:
      list_rounds(p, xs, walk(xs, acc))

# The same traversal of a list that is built fresh and consumed once, so no
# copy of it is kept: allocation plus a linear walk, without the duplication
# that walking a retained (&2) list pays for.
def fresh_rounds(k: Nat, +n: Nat, +v: U32, acc: U32) -> U32:
  match k:
    case 0n:
      acc
    case 1n+p:
      fresh_rounds(p, n, v, walk(mklist(n, v), acc))

# ---- allocating and consuming tree nodes ----

def mktree(d: Nat, +v: U32) -> Tr:
  match d:
    case 0n:
      Leaf{v}
    case 1n+ +p:
      Node{mktree(p, v), mktree(p, U32.add(v, 1))}

def sumtree(t: Tr, acc: U32) -> U32:
  match t:
    case Leaf{v}:
      U32.add(acc, v)
    case Node{l, r}:
      sumtree(r, sumtree(l, acc))

def tree_rounds(k: Nat, +d: Nat, +acc: U32) -> U32:
  match k:
    case 0n:
      acc
    case 1n+p:
      tree_rounds(p, d, sumtree(mktree(d, acc), acc))

def go() -> IO(Unit):
  do IO<Unit>:
    t0 : Nat <- IO.now()
    IO.print_err(U32.show(arith(20000000n, 7, 0)))
    t1 : Nat <- IO.now()
    d1 : Nat = Nat.sub(t1, t0)
    t2 : Nat <- IO.now()
    IO.print_err(U32.show(arr_fin(arr(20000000n, 7, (Array.new(Wd, 12n, W{0}), 0)))))
    t3 : Nat <- IO.now()
    d2 : Nat = Nat.sub(t3, t2)
    t4 : Nat <- IO.now()
    IO.print_err(U32.show(list_rounds(5000n, mklist(4096n, 3), 0)))
    t5 : Nat <- IO.now()
    d3 : Nat = Nat.sub(t5, t4)
    t6 : Nat <- IO.now()
    IO.print_err(U32.show(tree_rounds(5000n, 12n, 1)))
    t7 : Nat <- IO.now()
    d4 : Nat = Nat.sub(t7, t6)
    t8 : Nat <- IO.now()
    IO.print_err(U32.show(fresh_rounds(5000n, 4096n, 3, 0)))
    t9 : Nat <- IO.now()
    d5 : Nat = Nat.sub(t9, t8)
    IO.print(String.append("arith_ms=", String.append(Nat.show(d1),
      String.append(" array_ms=", String.append(Nat.show(d2),
      String.append(" list_ms=", String.append(Nat.show(d3),
      String.append(" alloc_ms=", String.append(Nat.show(d4),
      String.append(" fresh_ms=", Nat.show(d5)))))))))))

def main() -> IO(Unit):
  go()
