import Base
import ../../src/internal/vec.bend as V

# The PROOF MODEL of the flat segment-tree arrays: the perfect binary tree
# of sums and lazy tags that the two arrays realise.
#
# `src/segment_tree.bend` stores that tree in two flat `Base.Array`s indexed
# by block split point; the mathematics of model.bend and ops.bend is about
# the abstract tree, and proofs/segment_tree/walk.bend proves that the index
# walks implement exactly these functions. This is the same arrangement as
# proofs/bitset/model.bend and proofs/fenwick_tree/model.bend: the
# representation changed, the mathematics did not. These definitions are
# identical to the ones the tree-shaped implementation used before the
# migration (see docs/archive/).

type Node is Data:
  SLeaf{value: U32}
  SNode{sum: U32, lazy: U32, lo: Node, hi: Node}

def total(t: Node) -> U32:
  match t:
    case SLeaf{x}:
      x
    case SNode{s, z, l, r}:
      s

# Internal node over children of depth p with tag z.
def node(+p: Nat, +l: Node, +r: Node, +z: U32) -> Node:
  SNode{U32.add(U32.add(total(l), total(r)), U32.shln(z, 1n+p)), z, l, r}

def zeros(d: Nat) -> Node:
  match d:
    case 0n:
      SLeaf{0}
    case 1n+p:
      +k = zeros(p)
      SNode{0, 0, k, k}

# Add v to every value of a depth-d subtree (lazily).
def tagall(d: Nat, t: Node, +v: U32) -> Node:
  match d t:
    case 0n SLeaf{x}:
      SLeaf{U32.add(x, v)}
    case 0n SNode{s, z, l, r}:
      SNode{s, z, l, r}
    case 1n+p SLeaf{x}:
      SLeaf{x}
    case 1n+p SNode{s, z, l, r}:
      SNode{U32.add(s, U32.shln(v, 1n+p)), U32.add(z, v), l, r}

def get_go(d: Nat, t: Node, +i: Nat, +a: U32, left: Bool) -> U32:
  match d t left:
    case 0n SLeaf{x} _:
      U32.add(x, a)
    case 0n SNode{s, z, l, r} _:
      0
    case 1n+p SLeaf{x} _:
      0
    case 1n+ +p SNode{s, +z, l, r} True{}:
      get_go(p, l, i, U32.add(a, z), V.dec(p, i))
    case 1n+ +p SNode{s, +z, l, r} False{}:
      get_go(p, r, Nat.sub(i, V.pow2(p)), U32.add(a, z), V.dec(p, Nat.sub(i, V.pow2(p))))

def set_go(d: Nat, t: Node, +i: Nat, +v: U32, +a: U32, left: Bool) -> Node:
  match d t left:
    case 0n SLeaf{x} _:
      SLeaf{U32.sub(v, a)}
    case 0n SNode{s, z, l, r} _:
      SNode{s, z, l, r}
    case 1n+p SLeaf{x} _:
      SLeaf{x}
    case 1n+ +p SNode{s, +z, l, r} True{}:
      node(p, set_go(p, l, i, v, U32.add(a, z), V.dec(p, i)), r, z)
    case 1n+ +p SNode{s, +z, l, r} False{}:
      node(p, l, set_go(p, r, Nat.sub(i, V.pow2(p)), v, U32.add(a, z), V.dec(p, Nat.sub(i, V.pow2(p)))), z)

def leaf_prefix(x: U32, i: Nat) -> U32:
  match i:
    case 0n:
      0
    case 1n+j:
      x

# Sum of the first i values of a depth-d subtree whose ancestors' tags add a.
def prefix_go(d: Nat, t: Node, +i: Nat, +a: U32, left: Bool) -> U32:
  match d t left:
    case 0n SLeaf{x} _:
      leaf_prefix(U32.add(x, a), i)
    case 0n SNode{s, z, l, r} _:
      0
    case 1n+p SLeaf{x} _:
      0
    case 1n+ +p SNode{s, +z, +l, r} True{}:
      prefix_go(p, l, i, U32.add(a, z), V.dec(p, i))
    case 1n+ +p SNode{s, +z, +l, r} False{}:
      U32.add(U32.add(total(l), U32.shln(U32.add(a, z), p)), prefix_go(p, r, Nat.sub(i, V.pow2(p)), U32.add(a, z), V.dec(p, Nat.sub(i, V.pow2(p)))))

def leaf_padd(+x: U32, i: Nat, +v: U32) -> Node:
  match i:
    case 0n:
      SLeaf{x}
    case 1n+j:
      SLeaf{U32.add(x, v)}

# Add v to the first i values of a depth-d subtree.
def padd_go(d: Nat, t: Node, +i: Nat, +v: U32, left: Bool) -> Node:
  match d t left:
    case 0n SLeaf{x} _:
      leaf_padd(x, i, v)
    case 0n SNode{s, z, l, r} _:
      SNode{s, z, l, r}
    case 1n+p SLeaf{x} _:
      SLeaf{x}
    case 1n+ +p SNode{s, +z, l, r} True{}:
      node(p, padd_go(p, l, i, v, V.dec(p, i)), r, z)
    case 1n+ +p SNode{s, +z, l, r} False{}:
      node(p, tagall(p, l, v), padd_go(p, r, Nat.sub(i, V.pow2(p)), v, V.dec(p, Nat.sub(i, V.pow2(p)))), z)

def prefix(+d: Nat, t: Node, +i: Nat) -> U32:
  prefix_go(d, t, i, 0, V.dec(d, i))

def padd(+d: Nat, t: Node, +i: Nat, +v: U32) -> Node:
  padd_go(d, t, i, v, V.dec(d, i))
