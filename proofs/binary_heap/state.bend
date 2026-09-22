import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/order.bend as O
import ../lib/u32.bend as U
import ../lib/array.bend as AR
import ../spec/common.bend as SC
import ../spec/binary_heap.bend as S
import ../../src/containers/binary_heap.bend as H
import ../../src/containers/types/binary_heap.bend as E
import ./idx.bend as IX
import ./slots.bend as SL
import ./vals.bend as V
import ./root.bend as RT

# Shadow (Data) description of a reachable heap: the number of elements, the
# depth of the block and the mirror tree of its Base.Array. The array itself
# is linear, so -- exactly as in proofs/dynamic_array and proofs/bitset --
# every law is stated about the heap BUILT from a Data mirror tree.

type Shadow<-A: Data> is Data:
  Sh{size: Nat, depth: Nat, tree: AR.Tree<Maybe<&2, A>>}

def real(~A: Data, sh: Shadow<A>) -> H.Heap<A>:
  match sh:
    case Sh{+size, +depth, t}:
      H.BH{size, U32.from_nat(size), depth, U.pow2u(depth), AR.thaw(Maybe<&2, A>, t)}

# Representation invariant: the block is a perfect tree of `depth` levels, the
# elements occupy exactly the slots [0, size), and heap order holds over them.
def good(~A: Data, ~cmp: A -> A -> Cmp, sh: Shadow<A>) -> Bool:
  match sh:
    case Sh{+size, +depth, +t}:
      Bool.and(Nat.is_le(depth, 31n),
        Bool.and(AR.perfect(Maybe<&2, A>, depth, t),
          Bool.and(SL.lay(~A, AR.slots(Maybe<&2, A>, t), size),
            Bool.and(SL.ho_upto(~A, ~cmp, AR.slots(Maybe<&2, A>, t), size),
              Nat.is_le(size, SC.pow2(depth))))))

# Abstraction: the multiset of the occupied slots, sorted -- which is what
# the specification calls a priority queue.
def model(~A: Data, ~cmp: A -> A -> Cmp, sh: Shadow<A>) -> List<&2, A>:
  match sh:
    case Sh{+size, +depth, +t}:
      V.msort(~A, ~cmp, V.vals(~A, AR.slots(Maybe<&2, A>, t), size))

# Abstraction of an actual heap (proof level; reads the Base.Array through
# AR.freeze).
def abs(~A: Data, ~cmp: A -> A -> Cmp, h: H.Heap<A>) -> List<&2, A>:
  match h:
    case H.BH{+size, n, depth, cap, arr}:
      V.msort(~A, ~cmp, V.vals(~A, AR.slots(Maybe<&2, A>, AR.freeze(Maybe<&2, A>, arr)), size))

def abs_real(~A: Data, ~cmp: A -> A -> Cmp, +sh: Shadow<A>) -> {abs(~A, ~cmp, real(~A, sh)) == model(~A, ~cmp, sh) : List<&2, A>}:
  match sh:
    case Sh{+size, +depth, +t}:
      %Equal.sym(AR.Tree<Maybe<&2, A>>, AR.freeze(Maybe<&2, A>, AR.thaw(Maybe<&2, A>, t)), t, AR.freeze_thaw(Maybe<&2, A>, t)) : {V.msort(~A, ~cmp, V.vals(~A, AR.slots(Maybe<&2, A>, _), size)) == V.msort(~A, ~cmp, V.vals(~A, AR.slots(Maybe<&2, A>, t), size)) : List<&2, A>}
      {==}

# Invariant of an actual heap: it is the realization of a good shadow.
def Inv(~A: Data, ~cmp: A -> A -> Cmp, h: H.Heap<A>) -> Type:
  Sigma<&1, &1, Shadow<A>, sh => {h == real(~A, sh) : H.Heap<A>} & {good(~A, ~cmp, sh) == True{} : Bool}>

# ---- projections ----

def g_depth(~A: Data, ~cmp: A -> A -> Cmp, +size: Nat, +depth: Nat, +t: AR.Tree<Maybe<&2, A>>, +g: {good(~A, ~cmp, Sh{size, depth, t}) == True{} : Bool}) -> {Nat.is_le(depth, 31n) == True{} : Bool}:
  L.and_left(Nat.is_le(depth, 31n), Bool.and(AR.perfect(Maybe<&2, A>, depth, t), Bool.and(SL.lay(~A, AR.slots(Maybe<&2, A>, t), size), Bool.and(SL.ho_upto(~A, ~cmp, AR.slots(Maybe<&2, A>, t), size), Nat.is_le(size, SC.pow2(depth))))), g)

def g_rest1(~A: Data, ~cmp: A -> A -> Cmp, +size: Nat, +depth: Nat, +t: AR.Tree<Maybe<&2, A>>, +g: {good(~A, ~cmp, Sh{size, depth, t}) == True{} : Bool}) -> {Bool.and(AR.perfect(Maybe<&2, A>, depth, t), Bool.and(SL.lay(~A, AR.slots(Maybe<&2, A>, t), size), Bool.and(SL.ho_upto(~A, ~cmp, AR.slots(Maybe<&2, A>, t), size), Nat.is_le(size, SC.pow2(depth))))) == True{} : Bool}:
  L.and_right(Nat.is_le(depth, 31n), Bool.and(AR.perfect(Maybe<&2, A>, depth, t), Bool.and(SL.lay(~A, AR.slots(Maybe<&2, A>, t), size), Bool.and(SL.ho_upto(~A, ~cmp, AR.slots(Maybe<&2, A>, t), size), Nat.is_le(size, SC.pow2(depth))))), g)

def g_perfect(~A: Data, ~cmp: A -> A -> Cmp, +size: Nat, +depth: Nat, +t: AR.Tree<Maybe<&2, A>>, +g: {good(~A, ~cmp, Sh{size, depth, t}) == True{} : Bool}) -> {AR.perfect(Maybe<&2, A>, depth, t) == True{} : Bool}:
  L.and_left(AR.perfect(Maybe<&2, A>, depth, t), Bool.and(SL.lay(~A, AR.slots(Maybe<&2, A>, t), size), Bool.and(SL.ho_upto(~A, ~cmp, AR.slots(Maybe<&2, A>, t), size), Nat.is_le(size, SC.pow2(depth)))), g_rest1(~A, ~cmp, size, depth, t, g))

def g_rest2(~A: Data, ~cmp: A -> A -> Cmp, +size: Nat, +depth: Nat, +t: AR.Tree<Maybe<&2, A>>, +g: {good(~A, ~cmp, Sh{size, depth, t}) == True{} : Bool}) -> {Bool.and(SL.lay(~A, AR.slots(Maybe<&2, A>, t), size), Bool.and(SL.ho_upto(~A, ~cmp, AR.slots(Maybe<&2, A>, t), size), Nat.is_le(size, SC.pow2(depth)))) == True{} : Bool}:
  L.and_right(AR.perfect(Maybe<&2, A>, depth, t), Bool.and(SL.lay(~A, AR.slots(Maybe<&2, A>, t), size), Bool.and(SL.ho_upto(~A, ~cmp, AR.slots(Maybe<&2, A>, t), size), Nat.is_le(size, SC.pow2(depth)))), g_rest1(~A, ~cmp, size, depth, t, g))

def g_lay(~A: Data, ~cmp: A -> A -> Cmp, +size: Nat, +depth: Nat, +t: AR.Tree<Maybe<&2, A>>, +g: {good(~A, ~cmp, Sh{size, depth, t}) == True{} : Bool}) -> {SL.lay(~A, AR.slots(Maybe<&2, A>, t), size) == True{} : Bool}:
  L.and_left(SL.lay(~A, AR.slots(Maybe<&2, A>, t), size), Bool.and(SL.ho_upto(~A, ~cmp, AR.slots(Maybe<&2, A>, t), size), Nat.is_le(size, SC.pow2(depth))), g_rest2(~A, ~cmp, size, depth, t, g))

def g_rest3(~A: Data, ~cmp: A -> A -> Cmp, +size: Nat, +depth: Nat, +t: AR.Tree<Maybe<&2, A>>, +g: {good(~A, ~cmp, Sh{size, depth, t}) == True{} : Bool}) -> {Bool.and(SL.ho_upto(~A, ~cmp, AR.slots(Maybe<&2, A>, t), size), Nat.is_le(size, SC.pow2(depth))) == True{} : Bool}:
  L.and_right(SL.lay(~A, AR.slots(Maybe<&2, A>, t), size), Bool.and(SL.ho_upto(~A, ~cmp, AR.slots(Maybe<&2, A>, t), size), Nat.is_le(size, SC.pow2(depth))), g_rest2(~A, ~cmp, size, depth, t, g))

def g_ho(~A: Data, ~cmp: A -> A -> Cmp, +size: Nat, +depth: Nat, +t: AR.Tree<Maybe<&2, A>>, +g: {good(~A, ~cmp, Sh{size, depth, t}) == True{} : Bool}) -> {SL.ho_upto(~A, ~cmp, AR.slots(Maybe<&2, A>, t), size) == True{} : Bool}:
  L.and_left(SL.ho_upto(~A, ~cmp, AR.slots(Maybe<&2, A>, t), size), Nat.is_le(size, SC.pow2(depth)), g_rest3(~A, ~cmp, size, depth, t, g))

def g_size(~A: Data, ~cmp: A -> A -> Cmp, +size: Nat, +depth: Nat, +t: AR.Tree<Maybe<&2, A>>, +g: {good(~A, ~cmp, Sh{size, depth, t}) == True{} : Bool}) -> {Nat.is_le(size, SC.pow2(depth)) == True{} : Bool}:
  L.and_right(SL.ho_upto(~A, ~cmp, AR.slots(Maybe<&2, A>, t), size), Nat.is_le(size, SC.pow2(depth)), g_rest3(~A, ~cmp, size, depth, t, g))

def good_intro(~A: Data, ~cmp: A -> A -> Cmp, +size: Nat, +depth: Nat, +t: AR.Tree<Maybe<&2, A>>, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, A>, depth, t) == True{} : Bool}, +hlay: {SL.lay(~A, AR.slots(Maybe<&2, A>, t), size) == True{} : Bool}, +hho: {SL.ho_upto(~A, ~cmp, AR.slots(Maybe<&2, A>, t), size) == True{} : Bool}, +hs: {Nat.is_le(size, SC.pow2(depth)) == True{} : Bool}) -> {good(~A, ~cmp, Sh{size, depth, t}) == True{} : Bool}:
  L.and_intro(Nat.is_le(depth, 31n), Bool.and(AR.perfect(Maybe<&2, A>, depth, t), Bool.and(SL.lay(~A, AR.slots(Maybe<&2, A>, t), size), Bool.and(SL.ho_upto(~A, ~cmp, AR.slots(Maybe<&2, A>, t), size), Nat.is_le(size, SC.pow2(depth))))), hd,
    L.and_intro(AR.perfect(Maybe<&2, A>, depth, t), Bool.and(SL.lay(~A, AR.slots(Maybe<&2, A>, t), size), Bool.and(SL.ho_upto(~A, ~cmp, AR.slots(Maybe<&2, A>, t), size), Nat.is_le(size, SC.pow2(depth)))), pf,
      L.and_intro(SL.lay(~A, AR.slots(Maybe<&2, A>, t), size), Bool.and(SL.ho_upto(~A, ~cmp, AR.slots(Maybe<&2, A>, t), size), Nat.is_le(size, SC.pow2(depth))), hlay,
        L.and_intro(SL.ho_upto(~A, ~cmp, AR.slots(Maybe<&2, A>, t), size), Nat.is_le(size, SC.pow2(depth)), hho, hs))))

def sh_depth(~A: Data, sh: Shadow<A>) -> Nat:
  match sh:
    case Sh{+size, +depth, +t}:
      depth

def sh_size(~A: Data, sh: Shadow<A>) -> Nat:
  match sh:
    case Sh{+size, +depth, +t}:
      size

# depth <= 31 in the form the U32 bridges want it
def depth_lt32(+depth: Nat, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}) -> {Nat.is_lt(depth, 32n) == True{} : Bool}:
  N.le_lt_succ(depth, 31n, hd)

# ---- the constructor ----

def initial(~A: Data) -> Shadow<A>:
  Sh{0n, 0n, AR.TLeaf{None{}}}

def new_real(~A: Data) -> {H.new(~A) == real(~A, initial(~A)) : H.Heap<A>}:
  Equal.cong(Array<Maybe<&2, A>>, H.Heap<A>, a => H.BH{0n, 0, 0n, 1, a}, H.empty_slots(~A, 0n), AR.thaw(Maybe<&2, A>, AR.TLeaf{None{}}), AR.new(Maybe<&2, A>, 0n, None{}))

def new_good(~A: Data, ~cmp: A -> A -> Cmp) -> {good(~A, ~cmp, initial(~A)) == True{} : Bool}:
  {==}

def new_model(~A: Data, ~cmp: A -> A -> Cmp) -> {model(~A, ~cmp, initial(~A)) == Nil{} : List<&2, A>}:
  {==}
