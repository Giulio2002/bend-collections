import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/u32.bend as U
import ../lib/array.bend as AR
import ../lib/array2.bend as A2
import ../balanced_search_tree/sorted.bend as SO
import ../../spec/common.bend as SC
import ../../spec/balanced_search_tree.bend as S
import ../../spec/graph.bend as GS
import ../../src/graph.bend as G
import ../../types/balanced_search_tree.bend as BE
import ../../types/graph.bend as E
import ./shift.bend as SH
import ./search.bend as SE

# Shadow (Data) description of a reachable graph, and the abstraction into
# the independent model of spec/graph.bend.
#
# The runtime state is linear (two `Base.Array`s), so -- exactly as in
# proofs/binary_heap and proofs/bitset -- every law is stated about the graph
# BUILT from a Data mirror: `real(sh)`.

type Shadow is Data:
  Sh{dir: Bool, lo: Nat, hi: Nat, depth: Nat, ids: AR.Tree<U32>, adj: AR.Tree<AR.Tree<U32>>}

def real(sh: Shadow) -> G.Graph:
  match sh:
    case Sh{+dir, +lo, +hi, +depth, it, at}:
      G.G{dir, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(depth), depth, AR.thaw(U32, it), A2.thaw2(at)}

# ---- windows ----

# The k entries of xs starting at `from`.
def win(-T: Data, +xs: List<&2, T>, +from: Nat, +k: Nat) -> List<&2, T>:
  SC.take(T, SC.drop(T, xs, from), k)

# An adjacency block's header and entries.
def bdeg(+b: AR.Tree<U32>) -> Nat:
  U32.to_nat(SH.val_at(AR.slots(U32, b), 0n))

def bsize(+b: AR.Tree<U32>) -> Nat:
  U32.to_nat(SH.val_at(AR.slots(U32, b), 1n))

def blcap(+b: AR.Tree<U32>) -> Nat:
  U32.to_nat(SH.val_at(AR.slots(U32, b), 2n))

def bents(+b: AR.Tree<U32>) -> List<&2, U32>:
  win(U32, AR.slots(U32, b), 3n, bdeg(b))

# ---- abstraction ----

# A neighbour list as the specification's Unit-valued ordered map.
def uset(+ws: List<&2, U32>) -> List<&2, BE.Entry<U32, Unit>>:
  match ws:
    case Nil{}:
      Nil{}
    case Con{+w, t}:
      Con{BE.Entry{w, Unit{}}, uset(t)}

# The adjacency of the window: vertex id paired with its neighbour set.
def amodel(+ks: List<&2, U32>, +bs: List<&2, AR.Tree<U32>>) -> List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>:
  match ks bs:
    case Con{+k, kt} Con{+b, bt}:
      Con{BE.Entry{k, uset(bents(b))}, amodel(kt, bt)}
    case _ _:
      Nil{}

def kwin(sh: Shadow) -> List<&2, U32>:
  match sh:
    case Sh{dir, +lo, +hi, depth, +it, at}:
      win(U32, AR.slots(U32, it), lo, Nat.sub(hi, lo))

def bwin(sh: Shadow) -> List<&2, AR.Tree<U32>>:
  match sh:
    case Sh{dir, +lo, +hi, depth, it, +at}:
      win(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), lo, Nat.sub(hi, lo))

def model(sh: Shadow) -> GS.Model:
  match sh:
    case Sh{+dir, +lo, +hi, +depth, +it, +at}:
      GS.GM{dir, amodel(win(U32, AR.slots(U32, it), lo, Nat.sub(hi, lo)), win(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), lo, Nat.sub(hi, lo)))}

# ---- the representation invariant ----

# A block is well formed: its header agrees with its shape, its entries fit
# and are strictly ascending.
def above(+w: U32, +ws: List<&2, U32>) -> Bool:
  match ws:
    case Nil{}:
      True{}
    case Con{+x, t}:
      Bool.and(Cmp.is_lt(U32.cmp(w, x)), above(w, t))

def asc(+ws: List<&2, U32>) -> Bool:
  match ws:
    case Nil{}:
      True{}
    case Con{+w, +t}:
      Bool.and(above(w, t), asc(t))

def blk_ok(+b: AR.Tree<U32>) -> Bool:
  Bool.and(AR.perfect(U32, blcap(b), b),
    Bool.and(Nat.is_le(blcap(b), 31n),
      Bool.and(Nat.is_eq(bsize(b), SC.pow2(blcap(b))),
        Bool.and(Nat.is_le(Nat.add(3n, bdeg(b)), bsize(b)), asc(bents(b))))))

# Every neighbour of every vertex is a vertex, and no vertex is its own
# neighbour (the SelfLoop policy).
def mem(+w: U32, +ws: List<&2, U32>) -> Bool:
  match ws:
    case Nil{}:
      False{}
    case Con{+x, t}:
      Bool.or(Cmp.is_eq(U32.cmp(w, x)), mem(w, t))

def closed_in(+ws: List<&2, U32>, +ks: List<&2, U32>) -> Bool:
  match ws:
    case Nil{}:
      True{}
    case Con{+w, t}:
      Bool.and(mem(w, ks), closed_in(t, ks))

def loopfree_at(+k: U32, +ws: List<&2, U32>) -> Bool:
  match ws:
    case Nil{}:
      True{}
    case Con{+w, t}:
      Bool.and(Bool.not(Cmp.is_eq(U32.cmp(k, w))), loopfree_at(k, t))

def blocks_ok(+ks: List<&2, U32>, +bs: List<&2, AR.Tree<U32>>, +all: List<&2, U32>) -> Bool:
  match ks bs:
    case Con{+k, kt} Con{+b, bt}:
      Bool.and(blk_ok(b), Bool.and(closed_in(bents(b), all), Bool.and(loopfree_at(k, bents(b)), blocks_ok(kt, bt, all))))
    case Nil{} Nil{}:
      True{}
    case _ _:
      False{}

def good(sh: Shadow) -> Bool:
  match sh:
    case Sh{dir, +lo, +hi, +depth, +it, +at}:
      Bool.and(Nat.is_le(depth, 31n),
        Bool.and(AR.perfect(U32, depth, it),
          Bool.and(AR.perfect(AR.Tree<U32>, depth, at),
            Bool.and(Nat.is_le(lo, hi),
              Bool.and(Nat.is_le(hi, SC.pow2(depth)),
                Bool.and(SE.asc_at(Nat.sub(hi, lo), AR.slots(U32, it), lo),
                  blocks_ok(win(U32, AR.slots(U32, it), lo, Nat.sub(hi, lo)), win(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), lo, Nat.sub(hi, lo)), win(U32, AR.slots(U32, it), lo, Nat.sub(hi, lo)))))))))

# ---- the empty graph ----

def empty_blk_tree() -> AR.Tree<U32>:
  AR.TNode{AR.TNode{AR.TLeaf{0}, AR.TLeaf{4}}, AR.TNode{AR.TLeaf{2}, AR.TLeaf{0}}}

def empty_shadow(+dir: Bool) -> Shadow:
  Sh{dir, 0n, 0n, 0n, AR.TLeaf{0}, AR.TLeaf{AR.TLeaf{0}}}

def new_real(+dir: Bool) -> {G.new(dir) == real(empty_shadow(dir)) : G.Graph}:
  %Equal.sym(Array<U32>, Array.new(U32, 0n, 0), AR.thaw(U32, AR.trep(U32, 0n, 0)), AR.new(U32, 0n, 0)) : {G.G{dir, 0, 0, 1, 0n, _, ALeaf{Array.new(U32, 0n, 0)}} == real(empty_shadow(dir)) : G.Graph}
  %Equal.sym(Array<U32>, Array.new(U32, 0n, 0), AR.thaw(U32, AR.trep(U32, 0n, 0)), AR.new(U32, 0n, 0)) : {G.G{dir, 0, 0, 1, 0n, AR.thaw(U32, AR.trep(U32, 0n, 0)), ALeaf{_}} == real(empty_shadow(dir)) : G.Graph}
  {==}

def new_model(+dir: Bool) -> {model(empty_shadow(dir)) == GS.new(dir) : GS.Model}:
  {==}

def new_good(+dir: Bool) -> {good(empty_shadow(dir)) == True{} : Bool}:
  {==}
