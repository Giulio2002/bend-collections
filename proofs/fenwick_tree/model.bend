import Base
import ../../spec/common.bend as SC

# The PROOF MODEL of the flat Fenwick array: the perfect binary tree of
# partial sums that the array realises.
#
# `src/fenwick_tree.bend` stores the tree in one flat `Base.Array` indexed
# `k -> 2k / 2k+1`; the mathematics below (and all of tree.bend) is about the
# abstract tree, and `proofs/fenwick_tree/arr.bend` proves that the array
# walk implements exactly these functions. This is the same arrangement as
# `proofs/bitset/model.bend`, which keeps the old word-list walks as the
# model the array operations are shown to implement: the representation
# changed, the mathematics did not.
#
# These definitions are identical to the ones the tree-shaped implementation
# used before the migration (see docs/archive/), so none of the Fenwick
# mathematics had to be re-derived.

# Branch decision at a node whose children have depth d: True = lower half.
def dec(d: Nat, +j: Nat) -> Bool:
  match d:
    case 0n:
      False{}
    case 1n+q:
      Nat.is_lt(j, SC.pow2(q))

type Node is Data:
  FLeaf{value: U32}
  FNode{left_sum: U32, lo: Node, hi: Node}

def zeros(d: Nat) -> Node:
  match d:
    case 0n:
      FLeaf{0}
    case 1n+p:
      +z = zeros(p)
      FNode{0, z, z}

# Add v to leaf i, updating the stored left sums on the path.
def add_go(d: Nat, t: Node, +i: Nat, +v: U32, left: Bool) -> Node:
  match d t left:
    case 0n FLeaf{x} _:
      FLeaf{U32.add(x, v)}
    case 0n FNode{s, l, r} _:
      FNode{s, l, r}
    case 1n+p FLeaf{x} _:
      FLeaf{x}
    case 1n+ +p FNode{s, l, r} True{}:
      FNode{U32.add(s, v), add_go(p, l, i, v, dec(p, i)), r}
    case 1n+ +p FNode{s, l, r} False{}:
      FNode{s, l, add_go(p, r, Nat.sub(i, SC.pow2(p)), v, dec(p, Nat.sub(i, SC.pow2(p))))}

def leaf_prefix(x: U32, i: Nat) -> U32:
  match i:
    case 0n:
      0
    case 1n+j:
      x

# Sum of the first i leaves (i <= 2^d).
def prefix_go(d: Nat, t: Node, +i: Nat, left: Bool) -> U32:
  match d t left:
    case 0n FLeaf{x} _:
      leaf_prefix(x, i)
    case 0n FNode{s, l, r} _:
      0
    case 1n+p FLeaf{x} _:
      0
    case 1n+ +p FNode{s, l, r} True{}:
      prefix_go(p, l, i, dec(p, i))
    case 1n+ +p FNode{s, l, r} False{}:
      U32.add(s, prefix_go(p, r, Nat.sub(i, SC.pow2(p)), dec(p, Nat.sub(i, SC.pow2(p)))))

def prefix(+d: Nat, t: Node, +e: Nat) -> U32:
  prefix_go(d, t, e, dec(d, e))
