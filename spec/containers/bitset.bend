import Base
import ../lib/common.bend as C
import ../../src/containers/types/bitset.bend as E

# Independent model: a bitset of logical size n is a sequence of n Booleans
# (bit 0 first). Nothing here refers to words, shifts or masks.

def new(n: Nat) -> List<&2, Bool>:
  C.replicate(Bool, n, False{})

# Number of True bits.
def count(xs: List<&2, Bool>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{False{}, t}:
      count(t)
    case Con{True{}, t}:
      1n+count(t)

# Indices (offset by off) of True bits, ascending.
def members(xs: List<&2, Bool>, +off: Nat) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{False{}, t}:
      members(t, 1n+off)
    case Con{True{}, t}:
      Con{off, members(t, 1n+off)}

# Element-wise combination of two sequences (truncates to the shorter one).
def zip_or(xs: List<&2, Bool>, ys: List<&2, Bool>) -> List<&2, Bool>:
  match xs ys:
    case Con{a, s} Con{b, t}:
      Con{Bool.or(a, b), zip_or(s, t)}
    case _ _:
      Nil{}

def zip_and(xs: List<&2, Bool>, ys: List<&2, Bool>) -> List<&2, Bool>:
  match xs ys:
    case Con{a, s} Con{b, t}:
      Con{Bool.and(a, b), zip_and(s, t)}
    case _ _:
      Nil{}

def zip_diff(xs: List<&2, Bool>, ys: List<&2, Bool>) -> List<&2, Bool>:
  match xs ys:
    case Con{a, s} Con{b, t}:
      Con{Bool.and(a, Bool.not(b)), zip_diff(s, t)}
    case _ _:
      Nil{}

def zip_xor(xs: List<&2, Bool>, ys: List<&2, Bool>) -> List<&2, Bool>:
  match xs ys:
    case Con{a, s} Con{b, t}:
      Con{Bool.xor(a, b), zip_xor(s, t)}
    case _ _:
      Nil{}

def bit(x: Maybe<&2, Bool>) -> Result<&2, &2, E.Error, Bool>:
  match x:
    case None{}:
      Fail{E.IndexOutOfRange{}}
    case Some{b}:
      Done{b}

def get(xs: List<&2, Bool>, i: Nat) -> Result<&2, &2, E.Error, Bool>:
  bit(C.nth(Bool, xs, i))

# Assign bit i; out of range leaves the sequence unchanged and fails.
def assign_at(x: Maybe<&2, Bool>, +xs: List<&2, Bool>, i: Nat, v: Bool) -> List<&2, Bool> & E.Obs:
  match x:
    case None{}:
      (xs, E.OUnit{Fail{E.IndexOutOfRange{}}})
    case Some{b}:
      (C.update(Bool, xs, i, v), E.OUnit{Done{Unit{}}})

def assign(+xs: List<&2, Bool>, +i: Nat, v: Bool) -> List<&2, Bool> & E.Obs:
  assign_at(C.nth(Bool, xs, i), xs, i, v)

# Combine with an operand of the same logical size; a size mismatch leaves
# the sequence unchanged and fails.
def combine_if(same: Bool, xs: List<&2, Bool>, r: List<&2, Bool>) -> List<&2, Bool> & E.Obs:
  match same:
    case False{}:
      (xs, E.OUnit{Fail{E.LengthMismatch{}}})
    case True{}:
      (r, E.OUnit{Done{Unit{}}})

def combine(+xs: List<&2, Bool>, ys: List<&2, Bool>, r: List<&2, Bool>) -> List<&2, Bool> & E.Obs:
  combine_if(Nat.is_eq(C.length(Bool, xs), C.length(Bool, ys)), xs, r)

def step(+xs: List<&2, Bool>, op: E.Op) -> List<&2, Bool> & E.Obs:
  match op:
    case E.Length{}:
      (xs, E.ONat{C.length(Bool, xs)})
    case E.Get{+i}:
      (xs, E.OBit{get(xs, i)})
    case E.Set{+i}:
      assign(xs, i, True{})
    case E.Clear{+i}:
      assign(xs, i, False{})
    case E.Count{}:
      (xs, E.ONat{count(xs)})
    case E.Union{+ys}:
      combine(xs, ys, zip_or(xs, ys))
    case E.Intersection{+ys}:
      combine(xs, ys, zip_and(xs, ys))
    case E.Difference{+ys}:
      combine(xs, ys, zip_diff(xs, ys))
    case E.Xor{+ys}:
      combine(xs, ys, zip_xor(xs, ys))
    case E.ToList{}:
      (xs, E.OList{members(xs, 0n)})

def cons_obs(o: E.Obs, r: List<&2, Bool> & List<&2, E.Obs>) -> List<&2, Bool> & List<&2, E.Obs>:
  (m, os) = r
  (m, Con{o, os})

def run(ops: List<&2, E.Op>, +xs: List<&2, Bool>) -> List<&2, Bool> & List<&2, E.Obs>:
  match ops:
    case Nil{}:
      (xs, Nil{})
    case Con{+op, rest}:
      cons_obs(Pair.snd(List<&2, Bool>, E.Obs, step(xs, op)), run(rest, Pair.fst(List<&2, Bool>, E.Obs, step(xs, op))))

# ---- contract (SPARK formal containers) ----
# Each `<Subprogram>.<clause>` definition below states one Post clause of
# that SPARK subprogram, as a proposition on this model; the table names the
# clauses. proofs/containers/bitset/ proves every clause under its clause name,
# and its `impl` lemma carries them to the implementation.
#
# Contracts of the bitset in the style of SPARK's formal ordered sets
# (SPARKlib src/full/spark-containers-formal-ordered_sets.ads, AdaCore/SPARKlib
# 46ec319). A bitset over the universe [0, n) is the set of the indices of
# its True bits: SPARK's Model (M.Set, membership) is inset, its Length is
# the number of members (S.count), its Elements (the ascending sequence of
# members) is S.members, and our length (the universe size n) is the
# capacity. Each lemma is one Post clause of step; `impl` (via P.step_ok)
# carries every clause to the implementation.
#
#   SPARK subprogram (.ads line)          ours          clauses
#   Length (112)                          count         count_result, count_frame
#   Capacity                              length        length_result, length_frame
#   Empty_Set (99)                        new n         new_contains, new_count, new_length
#   Contains (1717)                       get           get_result, get_frame, get_outside
#   Include (831) / Insert (777)          set           set_contains, set_others,
#                                                       set_count, set_universe, set_outside
#   Exclude (953) / Delete (1051)         clear         clear_contains, clear_others,
#                                                       clear_count, clear_universe, clear_outside
#   Union (1235)                          union         union_contains, union_mismatch
#   Intersection (1307)                   intersection  intersection_contains, intersection_mismatch
#   Difference (1369)                     difference    difference_contains, difference_mismatch
#   Symmetric_Difference (1451)           xor           symmetric_difference_contains, xor_mismatch
#   Elements / iteration (Iter_Model)     to_list       to_list_result, to_list_frame,
#                                                       elements_contains, elements_length
#   implementation                        B.step        impl
# Insert's and Delete's Pre (not Contains / Contains) select one case of
# set_count / clear_count; Include's and Exclude's Contract_Cases are the two
# cases of the pick. Not in this API: "=", Equivalent_Sets, To_Set,
# Assign/Copy/Move, Element/Replace_Element/Replace (a member is its index),
# Delete_First/Delete_Last, the Union/Intersection/... functions that return
# a new set ("or", "and", "-", "xor": the procedures above), Overlap,
# Is_Subset, First/First_Element/Last/Last_Element, Next/Previous,
# Find/Floor/Ceiling (no cursors), Has_Element. SPARK's Pre on the index
# (in range) is a defensive check: out of range the operation returns
# IndexOutOfRange and changes nothing; binary operations on sets of
# different sizes return LengthMismatch and change nothing.

def ins(x: Maybe<&2, Bool>) -> Bool:
  match x:
    case None{}:
      False{}
    case Some{b}:
      b

# Contains (Model, k)
def inset(xs: List<&2, Bool>, k: Nat) -> Bool:
  ins(C.nth(Bool, xs, k))

def nx(+xs: List<&2, Bool>, +op: E.Op) -> List<&2, Bool>:
  Pair.fst(List<&2, Bool>, E.Obs, step(xs, op))

def ob(+xs: List<&2, Bool>, +op: E.Op) -> E.Obs:
  Pair.snd(List<&2, Bool>, E.Obs, step(xs, op))

# ---- Elements: to_list is the ascending sequence of the members ----
def nmem(+k: Nat, ys: List<&2, Nat>) -> Bool:
  match ys:
    case Nil{}:
      False{}
    case Con{+h, t}:
      Bool.or(Nat.is_eq(h, k), nmem(k, t))

# Contains (1717)
def Contains.get_result(+xs: List<&2, Bool>, +i: Nat, +h: {Nat.is_lt(i, C.length(Bool, xs)) == True{} : Bool}) -> Type:
  {ob(xs, E.Get{i}) == E.OBit{Done{inset(xs, i)}} : E.Obs}

# Contains (1717)
def Contains.get_frame(+xs: List<&2, Bool>, +i: Nat) -> Type:
  {nx(xs, E.Get{i}) == xs : List<&2, Bool>}

# Contains (1717)
def Contains.get_outside(+xs: List<&2, Bool>, +i: Nat, +h: {Nat.is_le(C.length(Bool, xs), i) == True{} : Bool}) -> Type:
  {ob(xs, E.Get{i}) == E.OBit{Fail{E.IndexOutOfRange{}}} : E.Obs}

# Length (112)
def Length.count_result(+xs: List<&2, Bool>) -> Type:
  {ob(xs, E.Count{}) == E.ONat{count(xs)} : E.Obs}

# Length (112)
def Length.count_frame(+xs: List<&2, Bool>) -> Type:
  {nx(xs, E.Count{}) == xs : List<&2, Bool>}

# Capacity
def Capacity.length_result(+xs: List<&2, Bool>) -> Type:
  {ob(xs, E.Length{}) == E.ONat{C.length(Bool, xs)} : E.Obs}

# Capacity
def Capacity.length_frame(+xs: List<&2, Bool>) -> Type:
  {nx(xs, E.Length{}) == xs : List<&2, Bool>}

# Empty_Set (99)
def Empty_Set.new_contains(+n: Nat, +k: Nat) -> Type:
  {inset(new(n), k) == False{} : Bool}

# Empty_Set (99)
def Empty_Set.new_count(+n: Nat) -> Type:
  {count(new(n)) == 0n : Nat}

# Empty_Set (99)
def Empty_Set.new_length(+n: Nat) -> Type:
  {C.length(Bool, new(n)) == n : Nat}

# Include (831) / Insert (777)
def Include.set_contains(+xs: List<&2, Bool>, +i: Nat, +h: {Nat.is_lt(i, C.length(Bool, xs)) == True{} : Bool}) -> Type:
  {inset(nx(xs, E.Set{i}), i) == True{} : Bool}

# Include (831) / Insert (777)
def Include.set_others(+xs: List<&2, Bool>, +i: Nat, +h: {Nat.is_lt(i, C.length(Bool, xs)) == True{} : Bool}, +j: Nat, +ne: {Nat.is_eq(i, j) == False{} : Bool}) -> Type:
  {inset(nx(xs, E.Set{i}), j) == inset(xs, j) : Bool}

# Include (831) / Insert (777)
def Include.set_universe(+xs: List<&2, Bool>, +i: Nat, +h: {Nat.is_lt(i, C.length(Bool, xs)) == True{} : Bool}) -> Type:
  {C.length(Bool, nx(xs, E.Set{i})) == C.length(Bool, xs) : Nat}

# Include (831) / Insert (777)
def Include.set_outside(+xs: List<&2, Bool>, +i: Nat, +h: {Nat.is_le(C.length(Bool, xs), i) == True{} : Bool}) -> Type:
  {step(xs, E.Set{i}) == (xs, E.OUnit{Fail{E.IndexOutOfRange{}}}) : List<&2, Bool> & E.Obs}

# Exclude (953) / Delete (1051)
def Exclude.clear_contains(+xs: List<&2, Bool>, +i: Nat, +h: {Nat.is_lt(i, C.length(Bool, xs)) == True{} : Bool}) -> Type:
  {inset(nx(xs, E.Clear{i}), i) == False{} : Bool}

# Exclude (953) / Delete (1051)
def Exclude.clear_others(+xs: List<&2, Bool>, +i: Nat, +h: {Nat.is_lt(i, C.length(Bool, xs)) == True{} : Bool}, +j: Nat, +ne: {Nat.is_eq(i, j) == False{} : Bool}) -> Type:
  {inset(nx(xs, E.Clear{i}), j) == inset(xs, j) : Bool}

# Exclude (953) / Delete (1051)
def Exclude.clear_universe(+xs: List<&2, Bool>, +i: Nat, +h: {Nat.is_lt(i, C.length(Bool, xs)) == True{} : Bool}) -> Type:
  {C.length(Bool, nx(xs, E.Clear{i})) == C.length(Bool, xs) : Nat}

# Exclude (953) / Delete (1051)
def Exclude.clear_outside(+xs: List<&2, Bool>, +i: Nat, +h: {Nat.is_le(C.length(Bool, xs), i) == True{} : Bool}) -> Type:
  {step(xs, E.Clear{i}) == (xs, E.OUnit{Fail{E.IndexOutOfRange{}}}) : List<&2, Bool> & E.Obs}

# Include (831) / Insert (777)
def Include.set_count(+xs: List<&2, Bool>, +i: Nat, +h: {Nat.is_lt(i, C.length(Bool, xs)) == True{} : Bool}) -> Type:
  {count(nx(xs, E.Set{i})) == Bool.pick(Nat, inset(xs, i), count(xs), 1n+count(xs)) : Nat}

# Exclude (953) / Delete (1051)
def Exclude.clear_count(+xs: List<&2, Bool>, +i: Nat, +h: {Nat.is_lt(i, C.length(Bool, xs)) == True{} : Bool}) -> Type:
  {count(xs) == Bool.pick(Nat, inset(xs, i), 1n+count(nx(xs, E.Clear{i})), count(nx(xs, E.Clear{i}))) : Nat}

# Union (1235)
def Union.union_contains(+xs: List<&2, Bool>, +ys: List<&2, Bool>, +k: Nat, +h: {C.length(Bool, xs) == C.length(Bool, ys) : Nat}) -> Type:
  {inset(nx(xs, E.Union{ys}), k) == Bool.or(inset(xs, k), inset(ys, k)) : Bool}

# Union (1235)
def Union.union_mismatch(+xs: List<&2, Bool>, +ys: List<&2, Bool>, +h: {Nat.is_eq(C.length(Bool, xs), C.length(Bool, ys)) == False{} : Bool}) -> Type:
  {step(xs, E.Union{ys}) == (xs, E.OUnit{Fail{E.LengthMismatch{}}}) : List<&2, Bool> & E.Obs}

# Intersection (1307)
def Intersection.intersection_contains(+xs: List<&2, Bool>, +ys: List<&2, Bool>, +k: Nat, +h: {C.length(Bool, xs) == C.length(Bool, ys) : Nat}) -> Type:
  {inset(nx(xs, E.Intersection{ys}), k) == Bool.and(inset(xs, k), inset(ys, k)) : Bool}

# Intersection (1307)
def Intersection.intersection_mismatch(+xs: List<&2, Bool>, +ys: List<&2, Bool>, +h: {Nat.is_eq(C.length(Bool, xs), C.length(Bool, ys)) == False{} : Bool}) -> Type:
  {step(xs, E.Intersection{ys}) == (xs, E.OUnit{Fail{E.LengthMismatch{}}}) : List<&2, Bool> & E.Obs}

# Difference (1369)
def Difference.difference_contains(+xs: List<&2, Bool>, +ys: List<&2, Bool>, +k: Nat, +h: {C.length(Bool, xs) == C.length(Bool, ys) : Nat}) -> Type:
  {inset(nx(xs, E.Difference{ys}), k) == Bool.and(inset(xs, k), Bool.not(inset(ys, k))) : Bool}

# Difference (1369)
def Difference.difference_mismatch(+xs: List<&2, Bool>, +ys: List<&2, Bool>, +h: {Nat.is_eq(C.length(Bool, xs), C.length(Bool, ys)) == False{} : Bool}) -> Type:
  {step(xs, E.Difference{ys}) == (xs, E.OUnit{Fail{E.LengthMismatch{}}}) : List<&2, Bool> & E.Obs}

# Symmetric_Difference (1451)
def Symmetric_Difference.symmetric_difference_contains(+xs: List<&2, Bool>, +ys: List<&2, Bool>, +k: Nat, +h: {C.length(Bool, xs) == C.length(Bool, ys) : Nat}) -> Type:
  {inset(nx(xs, E.Xor{ys}), k) == Bool.xor(inset(xs, k), inset(ys, k)) : Bool}

# Symmetric_Difference (1451)
def Symmetric_Difference.xor_mismatch(+xs: List<&2, Bool>, +ys: List<&2, Bool>, +h: {Nat.is_eq(C.length(Bool, xs), C.length(Bool, ys)) == False{} : Bool}) -> Type:
  {step(xs, E.Xor{ys}) == (xs, E.OUnit{Fail{E.LengthMismatch{}}}) : List<&2, Bool> & E.Obs}

# Elements / iteration (Iter_Model)
def Elements.to_list_result(+xs: List<&2, Bool>) -> Type:
  {ob(xs, E.ToList{}) == E.OList{members(xs, 0n)} : E.Obs}

# Elements / iteration (Iter_Model)
def Elements.to_list_frame(+xs: List<&2, Bool>) -> Type:
  {nx(xs, E.ToList{}) == xs : List<&2, Bool>}

# Elements / iteration (Iter_Model)
def Elements.elements_contains(+xs: List<&2, Bool>, +k: Nat) -> Type:
  {nmem(k, members(xs, 0n)) == inset(xs, k) : Bool}

# Elements / iteration (Iter_Model)
def Elements.elements_length(+xs: List<&2, Bool>, +off: Nat) -> Type:
  {C.length(Nat, members(xs, off)) == count(xs) : Nat}
