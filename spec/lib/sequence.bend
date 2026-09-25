import Base
import ./common.bend as SC

# The model of SPARK's formal vectors, over the lists every sequence
# specification here uses. SPARKlib spark-containers-formal-vectors.ads
# (AdaCore/SPARKlib 46ec319, lines 104-280, package Formal_Model) states each
# postcondition with a few predicates on the functional sequence
# M.Sequence (spark-containers-functional-vectors.ads):
#   M.Length, Element             SC.length, SC.nth
#   M.Range_Equal (L, R, F, Lst)   RangeEqual(l, r, f, lst+1)
#   M.Range_Shifted (.., Offset)   RangeShifted(l, r, f, lst+1, off)
#   M.Equal_Prefix (L, R)          EqualPrefix(l, r)
#   M.Equal_Except (L, R, P)       EqualExcept(l, r, p)
#   M.Constant_Range (C, F, L, E)  ConstantRange(c, f, lst+1, e)
#   M_Elements_Reversed (L, R)     ElementsReversed(l, r)
# Two translations: indices start at 0 (Index_Type'First), and every range
# is half open [fst, en), so the empty range needs no Index_Type'Base.
# The lemmas about these predicates are in proofs/lib/sequence.bend.

def RangeEqual(-A: Data, l: List<&2, A>, r: List<&2, A>, fst: Nat, en: Nat) -> Type:
  @+i: Nat -> @+h1: {Nat.is_le(fst, i) == True{} : Bool} -> @+h2: {Nat.is_lt(i, en) == True{} : Bool} -> {SC.nth(A, l, i) == SC.nth(A, r, i) : Maybe<&2, A>}

def RangeShifted(-A: Data, l: List<&2, A>, r: List<&2, A>, fst: Nat, en: Nat, off: Nat) -> Type:
  @+i: Nat -> @+h1: {Nat.is_le(fst, i) == True{} : Bool} -> @+h2: {Nat.is_lt(i, en) == True{} : Bool} -> {SC.nth(A, l, i) == SC.nth(A, r, Nat.add(i, off)) : Maybe<&2, A>}

def EqualPrefix(-A: Data, l: List<&2, A>, r: List<&2, A>) -> Type:
  {Nat.is_le(SC.length(A, l), SC.length(A, r)) == True{} : Bool} & RangeEqual(A, l, r, 0n, SC.length(A, l))

def EqualExcept(-A: Data, l: List<&2, A>, r: List<&2, A>, p: Nat) -> Type:
  {SC.length(A, l) == SC.length(A, r) : Nat} & (@+i: Nat -> @+h: {Nat.is_eq(p, i) == False{} : Bool} -> {SC.nth(A, l, i) == SC.nth(A, r, i) : Maybe<&2, A>})

def ConstantRange(-A: Data, c: List<&2, A>, fst: Nat, en: Nat, x: A) -> Type:
  @+i: Nat -> @+h1: {Nat.is_le(fst, i) == True{} : Bool} -> @+h2: {Nat.is_lt(i, en) == True{} : Bool} -> {SC.nth(A, c, i) == Some{x} : Maybe<&2, A>}

def ElementsReversed(-A: Data, l: List<&2, A>, r: List<&2, A>) -> Type:
  {SC.length(A, l) == SC.length(A, r) : Nat} & (@+i: Nat -> @+h: {Nat.is_lt(i, SC.length(A, l)) == True{} : Bool} -> {SC.nth(A, r, i) == SC.nth(A, l, Nat.sub(Nat.sub(SC.length(A, l), 1n), i)) : Maybe<&2, A>})

# Last_Element: the element at Last_Index = Length - 1
def last_elem(-A: Data, +xs: List<&2, A>) -> Maybe<&2, A>:
  SC.nth(A, xs, Nat.sub(SC.length(A, xs), 1n))
