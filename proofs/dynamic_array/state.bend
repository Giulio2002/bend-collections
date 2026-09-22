import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/u32.bend as U
import ../lib/array.bend as AR
import ../../spec/common.bend as SC
import ../../spec/dynamic_array.bend as S
import ../../src/dynamic_array.bend as DA
import ./layout.bend as LY
import ../../types/dynamic_array.bend as E

# Shadow (Data) description of a reachable dynamic array: limit, depth,
# length and the mirror tree t of its Base.Array (the array is thaw(t)).

type Shadow<-T: Data> is Data:
  Sh{limit: Nat, depth: Nat, len: Nat, tree: AR.Tree<Maybe<&2, T>>}

def real(-T: Data, sh: Shadow<T>) -> DA.DynArray<&2, T>:
  match sh:
    case Sh{l, +d, n, t}:
      DA.DA{l, d, SC.pow2(d), n, AR.thaw(Maybe<&2, T>, t)}

# Representation invariant.
def good(-T: Data, sh: Shadow<T>) -> Bool:
  match sh:
    case Sh{+l, +d, +n, +t}:
      Bool.and(Nat.is_le(l, 31n), Bool.and(Nat.is_le(d, l), Bool.and(AR.perfect(Maybe<&2, T>, d, t), LY.lay(T, AR.slots(Maybe<&2, T>, t), n))))

def model(-T: Data, sh: Shadow<T>) -> S.Model<T>:
  match sh:
    case Sh{l, d, n, t}:
      S.M{l, d, LY.somes(T, AR.slots(Maybe<&2, T>, t))}

# Abstraction of an actual dynamic array (proof-level; reads the Base.Array
# tree through AR.freeze).
def abs(-T: Data, da: DA.DynArray<&2, T>) -> S.Model<T>:
  match da:
    case DA.DA{l, d, c, n, arr}:
      S.M{l, d, LY.somes(T, AR.slots(Maybe<&2, T>, AR.freeze(Maybe<&2, T>, arr)))}

def abs_real(-T: Data, +sh: Shadow<T>) -> {abs(T, real(T, sh)) == model(T, sh) : S.Model<T>}:
  match sh:
    case Sh{+l, +d, +n, +t}:
      %Equal.sym(AR.Tree<Maybe<&2, T>>, AR.freeze(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, t)), t, AR.freeze_thaw(Maybe<&2, T>, t)) : {S.M{l, d, LY.somes(T, AR.slots(Maybe<&2, T>, _))} == S.M{l, d, LY.somes(T, AR.slots(Maybe<&2, T>, t))} : S.Model<T>}
      {==}

# Invariant of an actual array: it is the realization of a good shadow.
def Inv(-T: Data, da: DA.DynArray<&2, T>) -> Type:
  Sigma<&1, &1, Shadow<T>, sh => {da == real(T, sh) : DA.DynArray<&2, T>} & {good(T, sh) == True{} : Bool}>

# ---- projections of good ----

def g_limit(-T: Data, +l: Nat, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +g: {good(T, Sh{l, d, n, t}) == True{} : Bool}) -> {Nat.is_le(l, 31n) == True{} : Bool}:
  L.and_left(Nat.is_le(l, 31n), Bool.and(Nat.is_le(d, l), Bool.and(AR.perfect(Maybe<&2, T>, d, t), LY.lay(T, AR.slots(Maybe<&2, T>, t), n))), g)

def g_rest1(-T: Data, +l: Nat, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +g: {good(T, Sh{l, d, n, t}) == True{} : Bool}) -> {Bool.and(Nat.is_le(d, l), Bool.and(AR.perfect(Maybe<&2, T>, d, t), LY.lay(T, AR.slots(Maybe<&2, T>, t), n))) == True{} : Bool}:
  L.and_right(Nat.is_le(l, 31n), Bool.and(Nat.is_le(d, l), Bool.and(AR.perfect(Maybe<&2, T>, d, t), LY.lay(T, AR.slots(Maybe<&2, T>, t), n))), g)

def g_depth(-T: Data, +l: Nat, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +g: {good(T, Sh{l, d, n, t}) == True{} : Bool}) -> {Nat.is_le(d, l) == True{} : Bool}:
  L.and_left(Nat.is_le(d, l), Bool.and(AR.perfect(Maybe<&2, T>, d, t), LY.lay(T, AR.slots(Maybe<&2, T>, t), n)), g_rest1(T, l, d, n, t, g))

def g_rest2(-T: Data, +l: Nat, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +g: {good(T, Sh{l, d, n, t}) == True{} : Bool}) -> {Bool.and(AR.perfect(Maybe<&2, T>, d, t), LY.lay(T, AR.slots(Maybe<&2, T>, t), n)) == True{} : Bool}:
  L.and_right(Nat.is_le(d, l), Bool.and(AR.perfect(Maybe<&2, T>, d, t), LY.lay(T, AR.slots(Maybe<&2, T>, t), n)), g_rest1(T, l, d, n, t, g))

def g_perfect(-T: Data, +l: Nat, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +g: {good(T, Sh{l, d, n, t}) == True{} : Bool}) -> {AR.perfect(Maybe<&2, T>, d, t) == True{} : Bool}:
  L.and_left(AR.perfect(Maybe<&2, T>, d, t), LY.lay(T, AR.slots(Maybe<&2, T>, t), n), g_rest2(T, l, d, n, t, g))

def g_lay(-T: Data, +l: Nat, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +g: {good(T, Sh{l, d, n, t}) == True{} : Bool}) -> {LY.lay(T, AR.slots(Maybe<&2, T>, t), n) == True{} : Bool}:
  L.and_right(AR.perfect(Maybe<&2, T>, d, t), LY.lay(T, AR.slots(Maybe<&2, T>, t), n), g_rest2(T, l, d, n, t, g))

def good_intro(-T: Data, +l: Nat, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +a: {Nat.is_le(l, 31n) == True{} : Bool}, +b: {Nat.is_le(d, l) == True{} : Bool}, +c: {AR.perfect(Maybe<&2, T>, d, t) == True{} : Bool}, +e: {LY.lay(T, AR.slots(Maybe<&2, T>, t), n) == True{} : Bool}) -> {good(T, Sh{l, d, n, t}) == True{} : Bool}:
  L.and_intro(Nat.is_le(l, 31n), Bool.and(Nat.is_le(d, l), Bool.and(AR.perfect(Maybe<&2, T>, d, t), LY.lay(T, AR.slots(Maybe<&2, T>, t), n))), a,
    L.and_intro(Nat.is_le(d, l), Bool.and(AR.perfect(Maybe<&2, T>, d, t), LY.lay(T, AR.slots(Maybe<&2, T>, t), n)), b,
      L.and_intro(AR.perfect(Maybe<&2, T>, d, t), LY.lay(T, AR.slots(Maybe<&2, T>, t), n), c, e)))

# ---- derived facts ----

def lt32(+d: Nat, +l: Nat, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hl: {Nat.is_le(l, 31n) == True{} : Bool}) -> {Nat.is_lt(d, 32n) == True{} : Bool}:
  N.le_lt_succ(d, 31n, N.le_trans(d, l, 31n, hd, hl))

def le32(+d: Nat, +l: Nat, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hl: {Nat.is_le(l, 31n) == True{} : Bool}) -> {Nat.is_le(d, 32n) == True{} : Bool}:
  N.lt_le(d, 32n, lt32(d, l, hd, hl))

def pow2_src(+d: Nat) -> {DA.pow2(d) == SC.pow2(d) : Nat}:
  match d:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, Nat.double, DA.pow2(p), SC.pow2(p), pow2_src(p))

def slot_item(-T: Data, +m: Maybe<&2, T>) -> {DA.slot_result(T, m) == S.item_result(T, m) : Result<&2, &2, E.Error, T>}:
  match m:
    case None{}:
      {==}
    case Some{x}:
      {==}

def empty_eq(-T: Data, +d: Nat) -> {DA.empty_slots(T, d) == AR.thaw(Maybe<&2, T>, AR.trep(Maybe<&2, T>, d, None{})) : Array<Maybe<&2, T>>}:
  AR.new(Maybe<&2, T>, d, None{})

def grown_eq(-T: Data, +d: Nat, +t: AR.Tree<Maybe<&2, T>>) -> {DA.grown(T, d, AR.thaw(Maybe<&2, T>, t)) == AR.thaw(Maybe<&2, T>, AR.TNode{t, AR.trep(Maybe<&2, T>, d, None{})}) : Array<Maybe<&2, T>>}:
  %Equal.sym(Array<Maybe<&2, T>>, DA.empty_slots(T, d), AR.thaw(Maybe<&2, T>, AR.trep(Maybe<&2, T>, d, None{})), empty_eq(T, d)) : {ANode{AR.thaw(Maybe<&2, T>, t), _} == ANode{AR.thaw(Maybe<&2, T>, t), AR.thaw(Maybe<&2, T>, AR.trep(Maybe<&2, T>, d, None{}))} : Array<Maybe<&2, T>>}
  {==}

def slots_grown(-T: Data, +d: Nat, +t: AR.Tree<Maybe<&2, T>>) -> {AR.slots(Maybe<&2, T>, AR.TNode{t, AR.trep(Maybe<&2, T>, d, None{})}) == SC.append(Maybe<&2, T>, AR.slots(Maybe<&2, T>, t), SC.replicate(Maybe<&2, T>, SC.pow2(d), None{})) : List<&2, Maybe<&2, T>>}:
  %Equal.sym(List<&2, Maybe<&2, T>>, AR.slots(Maybe<&2, T>, AR.trep(Maybe<&2, T>, d, None{})), SC.replicate(Maybe<&2, T>, SC.pow2(d), None{}), AR.trep_slots(Maybe<&2, T>, d, None{})) : {SC.append(Maybe<&2, T>, AR.slots(Maybe<&2, T>, t), _) == SC.append(Maybe<&2, T>, AR.slots(Maybe<&2, T>, t), SC.replicate(Maybe<&2, T>, SC.pow2(d), None{})) : List<&2, Maybe<&2, T>>}
  {==}
