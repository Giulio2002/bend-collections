import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/order.bend as O
import ../../spec/common.bend as SC
import ../../spec/binary_heap.bend as S
import ./idx.bend as IX

# The slot list of an array heap, and heap order on it.
#
# Heap order is stated over CHILD indices -- "every j in [1, n) is not smaller
# than the value at par(j)" -- so the predicate never divides an index it does
# not have to, and every fact about it is pointwise: `ho_get` reads one pair
# out of the conjunction and `ho_put` builds the conjunction from a function
# that proves one pair at a time. Everything the sift proofs do is then a case
# analysis on a single index, never an induction over a range.

def unwrap(~A: Data, m: Maybe<&2, Maybe<&2, A>>) -> Maybe<&2, A>:
  match m:
    case None{}:
      None{}
    case Some{s}:
      s

def slot(~A: Data, ss: List<&2, Maybe<&2, A>>, +j: Nat) -> Maybe<&2, A>:
  unwrap(~A, SC.nth(Maybe<&2, A>, ss, j))

# Order between two slots; vacuously true when a slot is empty (the layout
# invariant is what says the slots of interest are occupied).
def mle(~A: Data, ~cmp: A -> A -> Cmp, a: Maybe<&2, A>, b: Maybe<&2, A>) -> Bool:
  match a b:
    case Some{x} Some{y}:
      S.le(~A, ~cmp, x, y)
    case _ _:
      True{}

def pair_ok(~A: Data, ~cmp: A -> A -> Cmp, +ss: List<&2, Maybe<&2, A>>, j: Nat) -> Bool:
  match j:
    case 0n:
      True{}
    case 1n+ +m:
      mle(~A, ~cmp, slot(~A, ss, IX.par(1n+m)), slot(~A, ss, 1n+m))

# Heap order over the children 0 .. k-1 (index 0 has no parent condition).
def ho_upto(~A: Data, ~cmp: A -> A -> Cmp, +ss: List<&2, Maybe<&2, A>>, k: Nat) -> Bool:
  match k:
    case 0n:
      True{}
    case 1n+ +m:
      Bool.and(pair_ok(~A, ~cmp, ss, m), ho_upto(~A, ~cmp, ss, m))

# Every slot of [0, k) is occupied.
def lay(~A: Data, +ss: List<&2, Maybe<&2, A>>, k: Nat) -> Bool:
  match k:
    case 0n:
      True{}
    case 1n+ +m:
      Bool.and(Maybe.is_some(&2, A, slot(~A, ss, m)), lay(~A, ss, m))

# ---- reading one pair out of the conjunction ----

def ho_get_eq(~A: Data, ~cmp: A -> A -> Cmp, +ss: List<&2, Maybe<&2, A>>, +m: Nat, +j: Nat, +e: {Nat.is_eq(j, m) == True{} : Bool}, +hp: {pair_ok(~A, ~cmp, ss, m) == True{} : Bool}) -> {pair_ok(~A, ~cmp, ss, j) == True{} : Bool}:
  L.subst(Nat, z => {pair_ok(~A, ~cmp, ss, z) == True{} : Bool}, m, j, Equal.sym(Nat, j, m, N.eq_from_is_eq(j, m, e)), hp)

def ho_get(~A: Data, ~cmp: A -> A -> Cmp, +ss: List<&2, Maybe<&2, A>>, k: Nat, +j: Nat, +h: {ho_upto(~A, ~cmp, ss, k) == True{} : Bool}, +hj: {Nat.is_lt(j, k) == True{} : Bool}, b: Bool, +eb: {Nat.is_eq(j, N.pred(k)) == b : Bool}) -> {pair_ok(~A, ~cmp, ss, j) == True{} : Bool}:
  match k b:
    case 0n _:
      Empty.absurd({pair_ok(~A, ~cmp, ss, j) == True{} : Bool}, N.lt_zero_absurd(j, hj))
    case 1n+ +m True{}:
      ho_get_eq(~A, ~cmp, ss, m, j, eb, L.and_left(pair_ok(~A, ~cmp, ss, m), ho_upto(~A, ~cmp, ss, m), h))
    case 1n+ +m False{}:
      ho_get(~A, ~cmp, ss, m, j, L.and_right(pair_ok(~A, ~cmp, ss, m), ho_upto(~A, ~cmp, ss, m), h), N.lt_or_eq(j, m, N.lt_succ_le(j, m, hj), eb), Nat.is_eq(j, N.pred(m)), {==})

def ho_at(~A: Data, ~cmp: A -> A -> Cmp, +ss: List<&2, Maybe<&2, A>>, +k: Nat, +j: Nat, +h: {ho_upto(~A, ~cmp, ss, k) == True{} : Bool}, +hj: {Nat.is_lt(j, k) == True{} : Bool}) -> {pair_ok(~A, ~cmp, ss, j) == True{} : Bool}:
  ho_get(~A, ~cmp, ss, k, j, h, hj, Nat.is_eq(j, N.pred(k)), {==})

# ---- updating one slot ----

def slot_same(~A: Data, +ss: List<&2, Maybe<&2, A>>, +i: Nat, +v: Maybe<&2, A>, +hi: {Nat.is_lt(i, SC.length(Maybe<&2, A>, ss)) == True{} : Bool}) -> {slot(~A, SC.update(Maybe<&2, A>, ss, i, v), i) == v : Maybe<&2, A>}:
  %Equal.sym(Maybe<&2, Maybe<&2, A>>, SC.nth(Maybe<&2, A>, SC.update(Maybe<&2, A>, ss, i, v), i), Some{v}, LL.nth_update_same(Maybe<&2, A>, ss, i, v, hi)) : {unwrap(~A, _) == v : Maybe<&2, A>}
  {==}

def slot_other(~A: Data, +ss: List<&2, Maybe<&2, A>>, +i: Nat, +j: Nat, +v: Maybe<&2, A>, +ne: {Nat.is_eq(i, j) == False{} : Bool}) -> {slot(~A, SC.update(Maybe<&2, A>, ss, i, v), j) == slot(~A, ss, j) : Maybe<&2, A>}:
  Equal.cong(Maybe<&2, Maybe<&2, A>>, Maybe<&2, A>, m => unwrap(~A, m), SC.nth(Maybe<&2, A>, SC.update(Maybe<&2, A>, ss, i, v), j), SC.nth(Maybe<&2, A>, ss, j), LL.nth_update_other(Maybe<&2, A>, ss, i, j, v, ne))

def flip_eq(c: Cmp, +h: {Cmp.is_eq(c) == False{} : Bool}) -> {Cmp.is_eq(O.flipc(c)) == False{} : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      Empty.absurd({Cmp.is_eq(O.flipc(EQ{})) == False{} : Bool}, L.true_false(h))
    case GT{}:
      {==}

def ne_sym(+a: Nat, +b: Nat, +h: {Nat.is_eq(b, a) == False{} : Bool}) -> {Nat.is_eq(a, b) == False{} : Bool}:
  %Equal.sym(Cmp, Nat.cmp(a, b), O.flipc(Nat.cmp(b, a)), O.nat_flip(b, a)) : {Cmp.is_eq(_) == False{} : Bool}
  flip_eq(Nat.cmp(b, a), h)

# ---- mle ----

def mle_some(~A: Data, ~cmp: A -> A -> Cmp, +x: A, +y: A, +h: {mle(~A, ~cmp, Some{x}, Some{y}) == True{} : Bool}) -> {S.le(~A, ~cmp, x, y) == True{} : Bool}:
  h

def mle_mk(~A: Data, ~cmp: A -> A -> Cmp, +x: A, +y: A, +h: {S.le(~A, ~cmp, x, y) == True{} : Bool}) -> {mle(~A, ~cmp, Some{x}, Some{y}) == True{} : Bool}:
  h

def mle_none_l(~A: Data, ~cmp: A -> A -> Cmp, +b: Maybe<&2, A>) -> {mle(~A, ~cmp, None{}, b) == True{} : Bool}:
  match b:
    case None{}:
      {==}
    case Some{y}:
      {==}

def mle_none_r(~A: Data, ~cmp: A -> A -> Cmp, +a: Maybe<&2, A>) -> {mle(~A, ~cmp, a, None{}) == True{} : Bool}:
  match a:
    case None{}:
      {==}
    case Some{x}:
      {==}

# transitivity through an OCCUPIED middle slot (with an empty middle there is
# nothing to conclude: `mle` is vacuous there)
def mle_trans(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), a: Maybe<&2, A>, +y: A, c: Maybe<&2, A>, +hab: {mle(~A, ~cmp, a, Some{y}) == True{} : Bool}, +hbc: {mle(~A, ~cmp, Some{y}, c) == True{} : Bool}) -> {mle(~A, ~cmp, a, c) == True{} : Bool}:
  match a c:
    case Some{+x} Some{+z}:
      O.trans(~A, ~cmp, o, x, y, z, hab, hbc)
    case Some{x} None{}:
      {==}
    case None{} Some{z}:
      {==}
    case None{} None{}:
      {==}


# ---- the layout, pointwise ----

def lay_get_eq(~A: Data, +ss: List<&2, Maybe<&2, A>>, +m: Nat, +j: Nat, +e: {Nat.is_eq(j, m) == True{} : Bool}, +hp: {Maybe.is_some(&2, A, slot(~A, ss, m)) == True{} : Bool}) -> {Maybe.is_some(&2, A, slot(~A, ss, j)) == True{} : Bool}:
  L.subst(Nat, z => {Maybe.is_some(&2, A, slot(~A, ss, z)) == True{} : Bool}, m, j, Equal.sym(Nat, j, m, N.eq_from_is_eq(j, m, e)), hp)

def lay_get(~A: Data, +ss: List<&2, Maybe<&2, A>>, k: Nat, +j: Nat, +h: {lay(~A, ss, k) == True{} : Bool}, +hj: {Nat.is_lt(j, k) == True{} : Bool}, b: Bool, +eb: {Nat.is_eq(j, N.pred(k)) == b : Bool}) -> {Maybe.is_some(&2, A, slot(~A, ss, j)) == True{} : Bool}:
  match k b:
    case 0n _:
      Empty.absurd({Maybe.is_some(&2, A, slot(~A, ss, j)) == True{} : Bool}, N.lt_zero_absurd(j, hj))
    case 1n+ +m True{}:
      lay_get_eq(~A, ss, m, j, eb, L.and_left(Maybe.is_some(&2, A, slot(~A, ss, m)), lay(~A, ss, m), h))
    case 1n+ +m False{}:
      lay_get(~A, ss, m, j, L.and_right(Maybe.is_some(&2, A, slot(~A, ss, m)), lay(~A, ss, m), h), N.lt_or_eq(j, m, N.lt_succ_le(j, m, hj), eb), Nat.is_eq(j, N.pred(m)), {==})

def lay_at(~A: Data, +ss: List<&2, Maybe<&2, A>>, +k: Nat, +j: Nat, +h: {lay(~A, ss, k) == True{} : Bool}, +hj: {Nat.is_lt(j, k) == True{} : Bool}) -> {Maybe.is_some(&2, A, slot(~A, ss, j)) == True{} : Bool}:
  lay_get(~A, ss, k, j, h, hj, Nat.is_eq(j, N.pred(k)), {==})

# An occupied slot, as a value.
def slot_some(~A: Data, m: Maybe<&2, A>, +h: {Maybe.is_some(&2, A, m) == True{} : Bool}) -> Sigma<&1, &1, A, v => {m == Some{v} : Maybe<&2, A>}>:
  match m:
    case None{}:
      Empty.absurd(Sigma<&1, &1, A, v => {None{} == Some{v} : Maybe<&2, A>}>, L.false_true(h))
    case Some{+v}:
      (v, {==})

# ---- nth of a slot inside the list ----

def nth_slot(~A: Data, +ss: List<&2, Maybe<&2, A>>, +j: Nat, +hj: {Nat.is_lt(j, SC.length(Maybe<&2, A>, ss)) == True{} : Bool}) -> {SC.nth(Maybe<&2, A>, ss, j) == Some{slot(~A, ss, j)} : Maybe<&2, Maybe<&2, A>>}:
  match ss j:
    case Nil{} _:
      Empty.absurd({None{} == Some{slot(~A, Nil{}, j)} : Maybe<&2, Maybe<&2, A>>}, N.lt_zero_absurd(j, hj))
    case Con{x, r} 0n:
      {==}
    case Con{x, +r} 1n+k:
      nth_slot(~A, r, k, hj)

# ---- heap order with one index excluded ----
#
# `ho_exc(ss, k, i)` is "every pair below k except the one into i holds". It
# is a Bool, not a function over indices: a proof term of function type could
# not be used twice, and a step needs its invariant more than once.

def pair_skip(~A: Data, ~cmp: A -> A -> Cmp, +ss: List<&2, Maybe<&2, A>>, +m: Nat, +i: Nat) -> Bool:
  Bool.pick(Bool, Nat.is_eq(m, i), True{}, pair_ok(~A, ~cmp, ss, m))

def ho_exc(~A: Data, ~cmp: A -> A -> Cmp, +ss: List<&2, Maybe<&2, A>>, k: Nat, +i: Nat) -> Bool:
  match k:
    case 0n:
      True{}
    case 1n+ +m:
      Bool.and(pair_skip(~A, ~cmp, ss, m, i), ho_exc(~A, ~cmp, ss, m, i))

def skip_at(~A: Data, ~cmp: A -> A -> Cmp, +ss: List<&2, Maybe<&2, A>>, +m: Nat, +i: Nat, +hne: {Nat.is_eq(m, i) == False{} : Bool}, +h: {pair_skip(~A, ~cmp, ss, m, i) == True{} : Bool}) -> {pair_ok(~A, ~cmp, ss, m) == True{} : Bool}:
  L.subst(Bool, b => {Bool.pick(Bool, b, True{}, pair_ok(~A, ~cmp, ss, m)) == True{} : Bool}, Nat.is_eq(m, i), False{}, hne, h)

def skip_eq(~A: Data, ~cmp: A -> A -> Cmp, +ss: List<&2, Maybe<&2, A>>, +m: Nat, +i: Nat, +eb: {Nat.is_eq(m, i) == True{} : Bool}) -> {pair_skip(~A, ~cmp, ss, m, i) == True{} : Bool}:
  %Equal.sym(Bool, Nat.is_eq(m, i), True{}, eb) : {Bool.pick(Bool, _, True{}, pair_ok(~A, ~cmp, ss, m)) == True{} : Bool}
  {==}

def skip_ne(~A: Data, ~cmp: A -> A -> Cmp, +ss: List<&2, Maybe<&2, A>>, +m: Nat, +i: Nat, +eb: {Nat.is_eq(m, i) == False{} : Bool}, +h: {pair_ok(~A, ~cmp, ss, m) == True{} : Bool}) -> {pair_skip(~A, ~cmp, ss, m, i) == True{} : Bool}:
  %Equal.sym(Bool, Nat.is_eq(m, i), False{}, eb) : {Bool.pick(Bool, _, True{}, pair_ok(~A, ~cmp, ss, m)) == True{} : Bool}
  h

def exc_get(~A: Data, ~cmp: A -> A -> Cmp, +ss: List<&2, Maybe<&2, A>>, k: Nat, +i: Nat, +j: Nat, +h: {ho_exc(~A, ~cmp, ss, k, i) == True{} : Bool}, +hj: {Nat.is_lt(j, k) == True{} : Bool}, b: Bool, +eb: {Nat.is_eq(j, N.pred(k)) == b : Bool}) -> {pair_skip(~A, ~cmp, ss, j, i) == True{} : Bool}:
  match k b:
    case 0n _:
      Empty.absurd({pair_skip(~A, ~cmp, ss, j, i) == True{} : Bool}, N.lt_zero_absurd(j, hj))
    case 1n+ +m True{}:
      L.subst(Nat, z => {pair_skip(~A, ~cmp, ss, z, i) == True{} : Bool}, m, j, Equal.sym(Nat, j, m, N.eq_from_is_eq(j, m, eb)), L.and_left(pair_skip(~A, ~cmp, ss, m, i), ho_exc(~A, ~cmp, ss, m, i), h))
    case 1n+ +m False{}:
      exc_get(~A, ~cmp, ss, m, i, j, L.and_right(pair_skip(~A, ~cmp, ss, m, i), ho_exc(~A, ~cmp, ss, m, i), h), N.lt_or_eq(j, m, N.lt_succ_le(j, m, hj), eb), Nat.is_eq(j, N.pred(m)), {==})

# one pair out of `ho_exc`
def exc_at(~A: Data, ~cmp: A -> A -> Cmp, +ss: List<&2, Maybe<&2, A>>, +k: Nat, +i: Nat, +j: Nat, +h: {ho_exc(~A, ~cmp, ss, k, i) == True{} : Bool}, +hj: {Nat.is_lt(j, k) == True{} : Bool}, +hne: {Nat.is_eq(j, i) == False{} : Bool}) -> {pair_ok(~A, ~cmp, ss, j) == True{} : Bool}:
  skip_at(~A, ~cmp, ss, j, i, hne, exc_get(~A, ~cmp, ss, k, i, j, h, hj, Nat.is_eq(j, N.pred(k)), {==}))

def pair_of_skip(~A: Data, ~cmp: A -> A -> Cmp, +ss: List<&2, Maybe<&2, A>>, +m: Nat, +i: Nat, +hi: {pair_ok(~A, ~cmp, ss, i) == True{} : Bool}, +h: {pair_skip(~A, ~cmp, ss, m, i) == True{} : Bool}, b: Bool, +eb: {Nat.is_eq(m, i) == b : Bool}) -> {pair_ok(~A, ~cmp, ss, m) == True{} : Bool}:
  match b:
    case True{}:
      ho_get_eq(~A, ~cmp, ss, i, m, eb, hi)
    case False{}:
      skip_at(~A, ~cmp, ss, m, i, eb, h)

# `ho_upto` follows from `ho_exc` plus the excluded pair
def ho_of_exc(~A: Data, ~cmp: A -> A -> Cmp, +ss: List<&2, Maybe<&2, A>>, k: Nat, +i: Nat, +h: {ho_exc(~A, ~cmp, ss, k, i) == True{} : Bool}, +hi: {pair_ok(~A, ~cmp, ss, i) == True{} : Bool}) -> {ho_upto(~A, ~cmp, ss, k) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+ +m:
      L.and_intro(pair_ok(~A, ~cmp, ss, m), ho_upto(~A, ~cmp, ss, m),
        pair_of_skip(~A, ~cmp, ss, m, i, hi, L.and_left(pair_skip(~A, ~cmp, ss, m, i), ho_exc(~A, ~cmp, ss, m, i), h), Nat.is_eq(m, i), {==}),
        ho_of_exc(~A, ~cmp, ss, m, i, L.and_right(pair_skip(~A, ~cmp, ss, m, i), ho_exc(~A, ~cmp, ss, m, i), h), hi))

# ---- the children of one index ----

def kid_le(~A: Data, ~cmp: A -> A -> Cmp, +ss: List<&2, Maybe<&2, A>>, +n: Nat, +u: Nat, +c: Nat) -> Bool:
  Bool.pick(Bool, Nat.is_lt(c, n), mle(~A, ~cmp, slot(~A, ss, u), slot(~A, ss, c)), True{})

def kids_le(~A: Data, ~cmp: A -> A -> Cmp, +ss: List<&2, Maybe<&2, A>>, +n: Nat, +u: Nat, +i: Nat) -> Bool:
  Bool.and(kid_le(~A, ~cmp, ss, n, u, IX.kidl(i)), kid_le(~A, ~cmp, ss, n, u, IX.kidr(i)))

def kid_le_at(~A: Data, ~cmp: A -> A -> Cmp, +ss: List<&2, Maybe<&2, A>>, +n: Nat, +u: Nat, +c: Nat, +hc: {Nat.is_lt(c, n) == True{} : Bool}, +h: {kid_le(~A, ~cmp, ss, n, u, c) == True{} : Bool}) -> {mle(~A, ~cmp, slot(~A, ss, u), slot(~A, ss, c)) == True{} : Bool}:
  L.subst(Bool, b => {Bool.pick(Bool, b, mle(~A, ~cmp, slot(~A, ss, u), slot(~A, ss, c)), True{}) == True{} : Bool}, Nat.is_lt(c, n), True{}, hc, h)

def kid_le_in(~A: Data, ~cmp: A -> A -> Cmp, +ss: List<&2, Maybe<&2, A>>, +n: Nat, +u: Nat, +c: Nat, +eb: {Nat.is_lt(c, n) == True{} : Bool}, +h: {mle(~A, ~cmp, slot(~A, ss, u), slot(~A, ss, c)) == True{} : Bool}) -> {kid_le(~A, ~cmp, ss, n, u, c) == True{} : Bool}:
  %Equal.sym(Bool, Nat.is_lt(c, n), True{}, eb) : {Bool.pick(Bool, _, mle(~A, ~cmp, slot(~A, ss, u), slot(~A, ss, c)), True{}) == True{} : Bool}
  h

def kid_le_out(~A: Data, ~cmp: A -> A -> Cmp, +ss: List<&2, Maybe<&2, A>>, +n: Nat, +u: Nat, +c: Nat, +eb: {Nat.is_lt(c, n) == False{} : Bool}) -> {kid_le(~A, ~cmp, ss, n, u, c) == True{} : Bool}:
  %Equal.sym(Bool, Nat.is_lt(c, n), False{}, eb) : {Bool.pick(Bool, _, mle(~A, ~cmp, slot(~A, ss, u), slot(~A, ss, c)), True{}) == True{} : Bool}
  {==}

# ---- heap order with the two pairs below one index excluded ----
#
# This is what a sift-DOWN carries: the hole may be larger than its children,
# so the two pairs whose parent is the hole are the ones left out.

def kid_of(+m: Nat, +i: Nat) -> Bool:
  Bool.or(Nat.is_eq(m, IX.kidl(i)), Nat.is_eq(m, IX.kidr(i)))

def pair_skip2(~A: Data, ~cmp: A -> A -> Cmp, +ss: List<&2, Maybe<&2, A>>, +m: Nat, +i: Nat) -> Bool:
  Bool.pick(Bool, kid_of(m, i), True{}, pair_ok(~A, ~cmp, ss, m))

def ho_exc2(~A: Data, ~cmp: A -> A -> Cmp, +ss: List<&2, Maybe<&2, A>>, k: Nat, +i: Nat) -> Bool:
  match k:
    case 0n:
      True{}
    case 1n+ +m:
      Bool.and(pair_skip2(~A, ~cmp, ss, m, i), ho_exc2(~A, ~cmp, ss, m, i))

def skip2_eq(~A: Data, ~cmp: A -> A -> Cmp, +ss: List<&2, Maybe<&2, A>>, +m: Nat, +i: Nat, +eb: {kid_of(m, i) == True{} : Bool}) -> {pair_skip2(~A, ~cmp, ss, m, i) == True{} : Bool}:
  %Equal.sym(Bool, kid_of(m, i), True{}, eb) : {Bool.pick(Bool, _, True{}, pair_ok(~A, ~cmp, ss, m)) == True{} : Bool}
  {==}

def skip2_ne(~A: Data, ~cmp: A -> A -> Cmp, +ss: List<&2, Maybe<&2, A>>, +m: Nat, +i: Nat, +eb: {kid_of(m, i) == False{} : Bool}, +h: {pair_ok(~A, ~cmp, ss, m) == True{} : Bool}) -> {pair_skip2(~A, ~cmp, ss, m, i) == True{} : Bool}:
  %Equal.sym(Bool, kid_of(m, i), False{}, eb) : {Bool.pick(Bool, _, True{}, pair_ok(~A, ~cmp, ss, m)) == True{} : Bool}
  h

def skip2_at(~A: Data, ~cmp: A -> A -> Cmp, +ss: List<&2, Maybe<&2, A>>, +m: Nat, +i: Nat, +hne: {kid_of(m, i) == False{} : Bool}, +h: {pair_skip2(~A, ~cmp, ss, m, i) == True{} : Bool}) -> {pair_ok(~A, ~cmp, ss, m) == True{} : Bool}:
  L.subst(Bool, b => {Bool.pick(Bool, b, True{}, pair_ok(~A, ~cmp, ss, m)) == True{} : Bool}, kid_of(m, i), False{}, hne, h)

def exc2_get(~A: Data, ~cmp: A -> A -> Cmp, +ss: List<&2, Maybe<&2, A>>, k: Nat, +i: Nat, +j: Nat, +h: {ho_exc2(~A, ~cmp, ss, k, i) == True{} : Bool}, +hj: {Nat.is_lt(j, k) == True{} : Bool}, b: Bool, +eb: {Nat.is_eq(j, N.pred(k)) == b : Bool}) -> {pair_skip2(~A, ~cmp, ss, j, i) == True{} : Bool}:
  match k b:
    case 0n _:
      Empty.absurd({pair_skip2(~A, ~cmp, ss, j, i) == True{} : Bool}, N.lt_zero_absurd(j, hj))
    case 1n+ +m True{}:
      L.subst(Nat, z => {pair_skip2(~A, ~cmp, ss, z, i) == True{} : Bool}, m, j, Equal.sym(Nat, j, m, N.eq_from_is_eq(j, m, eb)), L.and_left(pair_skip2(~A, ~cmp, ss, m, i), ho_exc2(~A, ~cmp, ss, m, i), h))
    case 1n+ +m False{}:
      exc2_get(~A, ~cmp, ss, m, i, j, L.and_right(pair_skip2(~A, ~cmp, ss, m, i), ho_exc2(~A, ~cmp, ss, m, i), h), N.lt_or_eq(j, m, N.lt_succ_le(j, m, hj), eb), Nat.is_eq(j, N.pred(m)), {==})

def exc2_at(~A: Data, ~cmp: A -> A -> Cmp, +ss: List<&2, Maybe<&2, A>>, +k: Nat, +i: Nat, +j: Nat, +h: {ho_exc2(~A, ~cmp, ss, k, i) == True{} : Bool}, +hj: {Nat.is_lt(j, k) == True{} : Bool}, +hne: {kid_of(j, i) == False{} : Bool}) -> {pair_ok(~A, ~cmp, ss, j) == True{} : Bool}:
  skip2_at(~A, ~cmp, ss, j, i, hne, exc2_get(~A, ~cmp, ss, k, i, j, h, hj, Nat.is_eq(j, N.pred(k)), {==}))

def pair_of_kid(~A: Data, ~cmp: A -> A -> Cmp, +ss: List<&2, Maybe<&2, A>>, +n: Nat, +i: Nat, c: Nat, +epc: {IX.par(c) == i : Nat}, +hcpos: {Nat.is_le(1n, c) == True{} : Bool}, +h: {mle(~A, ~cmp, slot(~A, ss, i), slot(~A, ss, c)) == True{} : Bool}) -> {pair_ok(~A, ~cmp, ss, c) == True{} : Bool}:
  match c:
    case 0n:
      Empty.absurd({pair_ok(~A, ~cmp, ss, 0n) == True{} : Bool}, L.true_not_false(Nat.is_le(1n, 0n), hcpos, {==}))
    case 1n+k:
      %Equal.sym(Nat, IX.par(1n+k), i, epc) : {mle(~A, ~cmp, slot(~A, ss, _), slot(~A, ss, 1n+k)) == True{} : Bool}
      h

# one excluded pair, from "the hole is not larger than that child"
def pair_kid_at(~A: Data, ~cmp: A -> A -> Cmp, +ss: List<&2, Maybe<&2, A>>, +n: Nat, +i: Nat, +j: Nat, +c: Nat, +hjn: {Nat.is_lt(j, n) == True{} : Bool}, +ej: {Nat.is_eq(j, c) == True{} : Bool}, +epc: {IX.par(c) == i : Nat}, +hc: {kid_le(~A, ~cmp, ss, n, i, c) == True{} : Bool}, +hcpos: {Nat.is_le(1n, c) == True{} : Bool}) -> {pair_ok(~A, ~cmp, ss, j) == True{} : Bool}:
  L.subst(Nat, z => {pair_ok(~A, ~cmp, ss, z) == True{} : Bool}, c, j, Equal.sym(Nat, j, c, N.eq_from_is_eq(j, c, ej)),
    pair_of_kid(~A, ~cmp, ss, n, i, c, epc, hcpos, kid_le_at(~A, ~cmp, ss, n, i, c, L.subst(Nat, z => {Nat.is_lt(z, n) == True{} : Bool}, j, c, N.eq_from_is_eq(j, c, ej), hjn), hc)))

# `ho_upto` from `ho_exc2` plus "the hole is not larger than its children"
def ho_of_exc2_at(~A: Data, ~cmp: A -> A -> Cmp, +ss: List<&2, Maybe<&2, A>>, +n: Nat, +k: Nat, +i: Nat, +j: Nat, +hjk: {Nat.is_lt(j, k) == True{} : Bool}, +hjn: {Nat.is_lt(j, n) == True{} : Bool}, +h: {ho_exc2(~A, ~cmp, ss, k, i) == True{} : Bool}, +hkids: {kids_le(~A, ~cmp, ss, n, i, i) == True{} : Bool}, b: Bool, +eb: {Nat.is_eq(j, IX.kidl(i)) == b : Bool}, c: Bool, +ec: {Nat.is_eq(j, IX.kidr(i)) == c : Bool}) -> {pair_ok(~A, ~cmp, ss, j) == True{} : Bool}:
  match b c:
    case True{} _:
      pair_kid_at(~A, ~cmp, ss, n, i, j, IX.kidl(i), hjn, eb, IX.par_kidl(i), L.and_left(kid_le(~A, ~cmp, ss, n, i, IX.kidl(i)), kid_le(~A, ~cmp, ss, n, i, IX.kidr(i)), hkids), IX.kidl_pos1(i))
    case False{} True{}:
      pair_kid_at(~A, ~cmp, ss, n, i, j, IX.kidr(i), hjn, ec, IX.par_kidr(i), L.and_right(kid_le(~A, ~cmp, ss, n, i, IX.kidl(i)), kid_le(~A, ~cmp, ss, n, i, IX.kidr(i)), hkids), IX.kidr_pos1(i))
    case False{} False{}:
      exc2_at(~A, ~cmp, ss, k, i, j, h, hjk, or_false(Nat.is_eq(j, IX.kidl(i)), Nat.is_eq(j, IX.kidr(i)), eb, ec))

def or_false(a: Bool, b: Bool, +ea: {a == False{} : Bool}, +eb: {b == False{} : Bool}) -> {Bool.or(a, b) == False{} : Bool}:
  %Equal.sym(Bool, a, False{}, ea) : {Bool.or(_, b) == False{} : Bool}
  eb

def ho_of_exc2(~A: Data, ~cmp: A -> A -> Cmp, +ss: List<&2, Maybe<&2, A>>, +n: Nat, k: Nat, +i: Nat, +hk: {Nat.is_le(k, n) == True{} : Bool}, +h: {ho_exc2(~A, ~cmp, ss, k, i) == True{} : Bool}, +hkids: {kids_le(~A, ~cmp, ss, n, i, i) == True{} : Bool}) -> {ho_upto(~A, ~cmp, ss, k) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+ +m:
      L.and_intro(pair_ok(~A, ~cmp, ss, m), ho_upto(~A, ~cmp, ss, m),
        ho_of_exc2_at(~A, ~cmp, ss, n, 1n+m, i, m, N.lt_succ(m), N.lt_le_trans(m, 1n+m, n, N.lt_succ(m), hk), h, hkids, Nat.is_eq(m, IX.kidl(i)), {==}, Nat.is_eq(m, IX.kidr(i)), {==}),
        ho_of_exc2(~A, ~cmp, ss, n, m, i, N.le_trans(m, 1n+m, n, N.le_succ(m), hk), L.and_right(pair_skip2(~A, ~cmp, ss, m, i), ho_exc2(~A, ~cmp, ss, m, i), h), hkids))
