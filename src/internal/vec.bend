import Base

# Persistent fixed-size vector: a perfect binary tree of depth d holding
# 2^d slots, slot j addressed by comparing j with 2^(d-1) at each level.
# get/set cost O(d) = O(log size); the tree is immutable Data, so updates
# share all untouched subtrees. Shared by structures that need indexed
# storage (union_find). Do not instantiate with U32 payloads through this
# erased-generic code (see docs/VALIDATION.md, runtime defects).

type Vec<-T: Data> is Data:
  VLeaf{value: T}
  VNode{lo: Vec<T>, hi: Vec<T>}

def pow2(k: Nat) -> Nat:
  match k:
    case 0n:
      1n
    case 1n+p:
      Nat.double(pow2(p))

# Branch decision at a node of depth d for slot j: True = lower half.
def dec(d: Nat, +j: Nat) -> Bool:
  match d:
    case 0n:
      False{}
    case 1n+q:
      Nat.is_lt(j, pow2(q))

def get_go(-T: Data, d: Nat, t: Vec<T>, +j: Nat, left: Bool) -> Maybe<&2, T>:
  match d t left:
    case 0n VLeaf{x} _:
      Some{x}
    case 0n VNode{l, r} _:
      None{}
    case 1n+p VLeaf{x} _:
      None{}
    case 1n+ +p VNode{l, r} True{}:
      get_go(T, p, l, j, dec(p, j))
    case 1n+ +p VNode{l, r} False{}:
      get_go(T, p, r, Nat.sub(j, pow2(p)), dec(p, Nat.sub(j, pow2(p))))

# Slot j of a depth-d vector (None only for a malformed tree).
def get(-T: Data, +d: Nat, t: Vec<T>, +j: Nat) -> Maybe<&2, T>:
  get_go(T, d, t, j, dec(d, j))

def set_go(-T: Data, d: Nat, t: Vec<T>, +j: Nat, +v: T, left: Bool) -> Vec<T>:
  match d t left:
    case 0n VLeaf{x} _:
      VLeaf{v}
    case 0n VNode{l, r} _:
      VNode{l, r}
    case 1n+p VLeaf{x} _:
      VLeaf{x}
    case 1n+ +p VNode{l, r} True{}:
      VNode{set_go(T, p, l, j, v, dec(p, j)), r}
    case 1n+ +p VNode{l, r} False{}:
      VNode{l, set_go(T, p, r, Nat.sub(j, pow2(p)), v, dec(p, Nat.sub(j, pow2(p))))}

# Replace slot j (j < 2^d).
def set(-T: Data, +d: Nat, t: Vec<T>, +j: Nat, +v: T) -> Vec<T>:
  set_go(T, d, t, j, v, dec(d, j))

# Smallest depth whose capacity covers n more slots: `room` counts the free
# slots left at the current depth (capacity 2^d).
def depth_go(n: Nat, +d: Nat, room: Nat) -> Nat:
  match n room:
    case 0n _:
      d
    case 1n+p 0n:
      depth_go(p, 1n+d, Nat.sub(pow2(d), 1n))
    case 1n+p 1n+r:
      depth_go(p, d, r)

def depth_for(n: Nat) -> Nat:
  depth_go(n, 0n, 1n)
