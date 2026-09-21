import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/u32.bend as U
import ../lib/array.bend as AR
import ../../spec/common.bend as SC
import ../../spec/doubly_linked_list.bend as DS
import ../../src/doubly_linked_list.bend as D
import ../../types/doubly_linked_list.bend as E

# Doubly linked list on parallel indexed arenas: the proof shadow.
#
# The three arenas are linear Base.Arrays, so -- as for the other
# array-backed structures -- the statements are about the list BUILT from a
# Data mirror: three perfect trees (values, prev links, next links) plus the
# element ids IN LIST ORDER (`ord`), a ghost list that never exists at run
# time. The runtime count, head and tail are functions of `ord`.
#
#   real(sh)   the runtime DList the shadow describes
#   model(sh)  the specification model: the (id, value) items along `ord`
#   good(sh)   ids below `fresh <= 2^depth <= 2^31`, no id twice, the value
#              arena holds Some exactly at the issued ids that are in `ord`,
#              and the prev/next arenas link `ord` in both directions

type Shadow<-T: Data> is Data:
  Sh{tag: U32, fresh: Nat, depth: Nat, tv: AR.Tree<Maybe<&2, T>>, tp: AR.Tree<U32>, tn: AR.Tree<U32>, ord: List<&2, Nat>}

# The link to the element with id p (links are id + 1; 0 is nil).
def ln(+p: Nat) -> U32:
  U32.from_nat(1n+p)

# ---- the ends of the order, as links ----

def lst_or(t: List<&2, Nat>, +x: Nat) -> Nat:
  match t:
    case Nil{}:
      x
    case Con{+y, r}:
      lst_or(r, y)

def hd(xs: List<&2, Nat>) -> U32:
  match xs:
    case Nil{}:
      D.nil()
    case Con{+x, t}:
      ln(x)

def lst(xs: List<&2, Nat>) -> U32:
  match xs:
    case Nil{}:
      D.nil()
    case Con{+x, t}:
      ln(lst_or(t, x))

# the link to the first id of xs, or e when xs is empty
def hd_or(xs: List<&2, Nat>, +e: U32) -> U32:
  match xs:
    case Nil{}:
      e
    case Con{+x, t}:
      ln(x)

def real(~T: Data, sh: Shadow<T>) -> D.DList<T>:
  match sh:
    case Sh{+tag, +fresh, +depth, tv, tp, tn, +ord}:
      D.DL{tag, U32.from_nat(fresh), SC.length(Nat, ord), hd(ord), lst(ord), depth, U.pow2u(depth), AR.thaw(Maybe<&2, T>, tv), AR.thaw(U32, tp), AR.thaw(U32, tn)}

# ---- reading the arenas at an id ----

def flat(-T: Data, m: Maybe<&2, Maybe<&2, T>>) -> Maybe<&2, T>:
  match m:
    case None{}:
      None{}
    case Some{x}:
      x

def vat(-T: Data, +xs: List<&2, Maybe<&2, T>>, +p: Nat) -> Maybe<&2, T>:
  flat(T, SC.nth(Maybe<&2, T>, xs, p))

def lat(+xs: List<&2, U32>, +p: Nat) -> U32:
  L.some_value(U32, SC.nth(U32, xs, p), 0)

# ---- the abstraction ----

def itm(-T: Data, m: Maybe<&2, T>, +p: Nat, rest: List<&2, E.Item<T>>) -> List<&2, E.Item<T>>:
  match m:
    case None{}:
      rest
    case Some{v}:
      Con{E.Item{U32.from_nat(p), v}, rest}

def items(-T: Data, +xs: List<&2, Maybe<&2, T>>, ord: List<&2, Nat>) -> List<&2, E.Item<T>>:
  match ord:
    case Nil{}:
      Nil{}
    case Con{+p, t}:
      itm(T, vat(T, xs, p), p, items(T, xs, t))

def model(~T: Data, sh: Shadow<T>) -> DS.Model<T>:
  match sh:
    case Sh{+tag, +fresh, +depth, +tv, tp, tn, +ord}:
      DS.DM{tag, fresh, items(T, AR.slots(Maybe<&2, T>, tv), ord)}

# ---- the invariant ----

def lmem(+i: Nat, xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{+x, t}:
      Bool.or(Nat.is_eq(x, i), lmem(i, t))

def nodup(xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, +t}:
      Bool.and(Bool.not(lmem(x, t)), nodup(t))

def alllt(xs: List<&2, Nat>, +n: Nat) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, t}:
      Bool.and(Nat.is_lt(x, n), alllt(t, n))

def beq(a: Bool, b: Bool) -> Bool:
  match a:
    case True{}:
      b
    case False{}:
      Bool.not(b)

def is_some(-T: Data, m: Maybe<&2, T>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{x}:
      True{}

# slots p .. p+k-1 hold Some exactly at the ids that are in ord
def lv(-T: Data, k: Nat, +xs: List<&2, Maybe<&2, T>>, +p: Nat, +ord: List<&2, Nat>) -> Bool:
  match k:
    case 0n:
      True{}
    case 1n+m:
      Bool.and(beq(is_some(T, vat(T, xs, p)), lmem(p, ord)), lv(T, m, xs, 1n+p, ord))

# each id of xs links back to its predecessor (prev) and on to its successor
# (next; the last one on to e)
def lk(xs: List<&2, Nat>, +prev: U32, +e: U32, +ps: List<&2, U32>, +ns: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, +t}:
      Bool.and(U32.is_eq(lat(ps, x), prev), Bool.and(U32.is_eq(lat(ns, x), hd_or(t, e)), lk(t, ln(x), e, ps, ns)))

def good(~T: Data, sh: Shadow<T>) -> Bool:
  match sh:
    case Sh{+tag, +fresh, +depth, +tv, +tp, +tn, +ord}:
      Bool.and(Nat.is_le(depth, 31n),
        Bool.and(AR.perfect(Maybe<&2, T>, depth, tv),
          Bool.and(AR.perfect(U32, depth, tp),
            Bool.and(AR.perfect(U32, depth, tn),
              Bool.and(Nat.is_le(fresh, SC.pow2(depth)),
                Bool.and(alllt(ord, fresh),
                  Bool.and(nodup(ord),
                    Bool.and(lv(T, fresh, AR.slots(Maybe<&2, T>, tv), 0n, ord),
                      lk(ord, D.nil(), D.nil(), AR.slots(U32, tp), AR.slots(U32, tn))))))))))

# ---- the constructor ----

def initial(~T: Data, +tag: U32) -> Shadow<T>:
  Sh{tag, 0n, 0n, AR.TLeaf{None{}}, AR.TLeaf{D.nil()}, AR.TLeaf{D.nil()}, Nil{}}

def new_model(~T: Data, +tag: U32) -> {model(~T, initial(~T, tag)) == DS.new(T, tag) : DS.Model<T>}:
  {==}

def new_good(~T: Data, +tag: U32) -> {good(~T, initial(~T, tag)) == True{} : Bool}:
  {==}

def new_real(~T: Data, +tag: U32) -> {D.new(~T, tag) == real(~T, initial(~T, tag)) : D.DList<T>}:
  %Equal.sym(Array<Maybe<&2, T>>, Array.new(Maybe<&2, T>, 0n, None{}), AR.thaw(Maybe<&2, T>, AR.trep(Maybe<&2, T>, 0n, None{})), AR.new(Maybe<&2, T>, 0n, None{})) : {D.DL{tag, 0, 0n, D.nil(), D.nil(), 0n, 1, _, D.new_links(0n), D.new_links(0n)} == real(~T, initial(~T, tag)) : D.DList<T>}
  %Equal.sym(Array<U32>, Array.new(U32, 0n, D.nil()), AR.thaw(U32, AR.trep(U32, 0n, D.nil())), AR.new(U32, 0n, D.nil())) : {D.DL{tag, 0, 0n, D.nil(), D.nil(), 0n, 1, AR.thaw(Maybe<&2, T>, AR.trep(Maybe<&2, T>, 0n, None{})), _, _} == real(~T, initial(~T, tag)) : D.DList<T>}
  {==}
