import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/order.bend as O
import ../balanced_search_tree/sorted.bend as SO
import ../../spec/common.bend as SC
import ../../spec/balanced_search_tree.bend as S
import ../../types/balanced_search_tree.bend as BE

# The index mathematics the array-backed graph needs: a sorted association
# list, the LOWER BOUND index of a key in it, and the fact that inserting,
# replacing or deleting AT THAT INDEX is exactly the specification's `ins`
# and `del` on the same list.
#
# The runtime finds the lower bound by binary search in a block
# (proofs/graph/search.bend proves the loop computes this index); everything
# here is pure list mathematics at key type U32, independent of arrays.

# The number of entries whose key is strictly below v.
# The number of entries whose key is strictly below v.
def lbx_step(less: Bool, r: Nat) -> Nat:
  match less:
    case True{}:
      1n+r
    case False{}:
      0n

def lbx(-V: Data, +v: U32, xs: List<&2, BE.Entry<U32, V>>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{+e, +t}:
      lbx_step(Cmp.is_lt(U32.cmp(BE.key(U32, V, e), v)), lbx(V, v, t))

def ins_at(-V: Data, xs: List<&2, BE.Entry<U32, V>>, i: Nat, e: BE.Entry<U32, V>) -> List<&2, BE.Entry<U32, V>>:
  match xs i:
    case ys 0n:
      Con{e, ys}
    case Nil{} 1n+p:
      Con{e, Nil{}}
    case Con{h, t} 1n+p:
      Con{h, ins_at(V, t, p, e)}

def upd_at(-V: Data, xs: List<&2, BE.Entry<U32, V>>, i: Nat, e: BE.Entry<U32, V>) -> List<&2, BE.Entry<U32, V>>:
  match xs i:
    case Nil{} 0n:
      Nil{}
    case Con{h, t} 0n:
      Con{e, t}
    case Nil{} 1n+p:
      Nil{}
    case Con{h, t} 1n+p:
      Con{h, upd_at(V, t, p, e)}

def del_at(-V: Data, xs: List<&2, BE.Entry<U32, V>>, i: Nat) -> List<&2, BE.Entry<U32, V>>:
  match xs i:
    case Nil{} 0n:
      Nil{}
    case Con{h, t} 0n:
      t
    case Nil{} 1n+p:
      Nil{}
    case Con{h, t} 1n+p:
      Con{h, del_at(V, t, p)}

# ---- the three comparison cases of a head key against v ----

# `Cmp.is_lt(cmp(k, v))` (what the runtime tests) against `cmp(v, k)` (what
# the specification matches on).
def head_gt(+k: U32, +v: U32, +h: {Cmp.is_lt(U32.cmp(k, v)) == True{} : Bool}) -> {U32.cmp(v, k) == GT{} : Cmp}:
  Equal.trans(Cmp, U32.cmp(v, k), O.flipc(U32.cmp(k, v)), GT{},
    O.u32_flip(k, v),
    Equal.cong(Cmp, Cmp, c => O.flipc(c), U32.cmp(k, v), LT{}, O.lt_is(U32.cmp(k, v), h)))

# ---- lower bound versus the specification ----

# With a strictly sorted list, every key before the lower bound is < v, so
# `ins` walks exactly `lbx` steps before it acts. Insertion of a key that is
# NOT present therefore happens at the lower bound index.
# When v is absent and the head key is not below v, the head key cannot equal
# v either, so `ins` takes its LT branch.
def gt_flip_lt(+v: U32, +k: U32, +ec: {U32.cmp(v, k) == GT{} : Cmp}, +eb: {Cmp.is_lt(U32.cmp(k, v)) == False{} : Bool}) -> {Cmp.is_lt(U32.cmp(k, v)) == True{} : Bool}:
  Equal.cong(Cmp, Bool, c => Cmp.is_lt(c), U32.cmp(k, v), LT{},
    Equal.trans(Cmp, U32.cmp(k, v), O.flipc(U32.cmp(v, k)), LT{},
      O.u32_flip(v, k),
      Equal.cong(Cmp, Cmp, c => O.flipc(c), U32.cmp(v, k), GT{}, ec)))

def not_eq_lt_c(-V: Data, +e: BE.Entry<U32, V>, +t: List<&2, BE.Entry<U32, V>>, +v: U32, c: Cmp, +ec: {U32.cmp(v, BE.key(U32, V, e)) == c : Cmp}, +hf: {S.find(~U32, ~U32.cmp, V, v, Con{e, t}) == None{} : Maybe<&2, V>}, +eb: {Cmp.is_lt(U32.cmp(BE.key(U32, V, e), v)) == False{} : Bool}) -> {U32.cmp(v, BE.key(U32, V, e)) == LT{} : Cmp}:
  match e c:
    case BE.Entry{k, val} LT{}:
      ec
    case BE.Entry{k, val} EQ{}:
      Empty.absurd({U32.cmp(v, BE.key(U32, V, e)) == LT{} : Cmp}, L.none_some(V, val, Equal.sym(Maybe<&2, V>, Some{val}, None{}, L.subst(Cmp, c2 => {S.find_at(U32, V, c2, BE.Entry{k, val}, S.find(~U32, ~U32.cmp, V, v, t)) == None{} : Maybe<&2, V>}, U32.cmp(v, BE.key(U32, V, e)), EQ{}, ec, hf))))
    case BE.Entry{k, val} GT{}:
      Empty.absurd({U32.cmp(v, BE.key(U32, V, e)) == LT{} : Cmp}, L.true_not_false(Cmp.is_lt(U32.cmp(BE.key(U32, V, e), v)), gt_flip_lt(v, k, ec, eb), eb))

# cmp(v, k) = GT gives cmp(k, v) = LT, contradicting `not below`.
def not_eq_lt(-V: Data, +e: BE.Entry<U32, V>, +t: List<&2, BE.Entry<U32, V>>, +v: U32, +hf: {S.find(~U32, ~U32.cmp, V, v, Con{e, t}) == None{} : Maybe<&2, V>}, +eb: {Cmp.is_lt(U32.cmp(BE.key(U32, V, e), v)) == False{} : Bool}) -> {U32.cmp(v, BE.key(U32, V, e)) == LT{} : Cmp}:
  not_eq_lt_c(V, e, t, v, U32.cmp(v, BE.key(U32, V, e)), {==}, hf, eb)

def ins_new_c(-V: Data, +e: BE.Entry<U32, V>, +t: List<&2, BE.Entry<U32, V>>, +v: U32, +val: V, less: Bool, +eb: {Cmp.is_lt(U32.cmp(BE.key(U32, V, e), v)) == less : Bool}, +hf: {S.find(~U32, ~U32.cmp, V, v, Con{e, t}) == None{} : Maybe<&2, V>}, +ih: {ins_at(V, t, lbx(V, v, t), BE.Entry{v, val}) == S.ins(~U32, ~U32.cmp, V, v, val, t) : List<&2, BE.Entry<U32, V>>}) -> {ins_at(V, Con{e, t}, lbx(V, v, Con{e, t}), BE.Entry{v, val}) == S.ins(~U32, ~U32.cmp, V, v, val, Con{e, t}) : List<&2, BE.Entry<U32, V>>}:
  match less:
    case True{}:
      %Equal.sym(Bool, Cmp.is_lt(U32.cmp(BE.key(U32, V, e), v)), True{}, eb) : {ins_at(V, Con{e, t}, lbx_step(_, lbx(V, v, t)), BE.Entry{v, val}) == S.ins(~U32, ~U32.cmp, V, v, val, Con{e, t}) : List<&2, BE.Entry<U32, V>>}
      %Equal.sym(Cmp, U32.cmp(v, BE.key(U32, V, e)), GT{}, head_gt(BE.key(U32, V, e), v, eb)) : {Con{e, ins_at(V, t, lbx(V, v, t), BE.Entry{v, val})} == S.ins_at(~U32, ~U32.cmp, V, _, v, val, e, t, S.ins(~U32, ~U32.cmp, V, v, val, t)) : List<&2, BE.Entry<U32, V>>}
      Equal.cong(List<&2, BE.Entry<U32, V>>, List<&2, BE.Entry<U32, V>>, ys => Con{e, ys}, ins_at(V, t, lbx(V, v, t), BE.Entry{v, val}), S.ins(~U32, ~U32.cmp, V, v, val, t), ih)
    case False{}:
      %Equal.sym(Bool, Cmp.is_lt(U32.cmp(BE.key(U32, V, e), v)), False{}, eb) : {ins_at(V, Con{e, t}, lbx_step(_, lbx(V, v, t)), BE.Entry{v, val}) == S.ins(~U32, ~U32.cmp, V, v, val, Con{e, t}) : List<&2, BE.Entry<U32, V>>}
      %Equal.sym(Cmp, U32.cmp(v, BE.key(U32, V, e)), LT{}, not_eq_lt(V, e, t, v, hf, eb)) : {Con{BE.Entry{v, val}, Con{e, t}} == S.ins_at(~U32, ~U32.cmp, V, _, v, val, e, t, S.ins(~U32, ~U32.cmp, V, v, val, t)) : List<&2, BE.Entry<U32, V>>}
      {==}

# find(v, e :: t) = None gives find(v, t) = None.
def find_tail_c(-V: Data, +e: BE.Entry<U32, V>, +t: List<&2, BE.Entry<U32, V>>, +v: U32, c: Cmp, +ec: {U32.cmp(v, BE.key(U32, V, e)) == c : Cmp}, +hf: {S.find(~U32, ~U32.cmp, V, v, Con{e, t}) == None{} : Maybe<&2, V>}) -> {S.find(~U32, ~U32.cmp, V, v, t) == None{} : Maybe<&2, V>}:
  match e c:
    case BE.Entry{k, val} EQ{}:
      Empty.absurd({S.find(~U32, ~U32.cmp, V, v, t) == None{} : Maybe<&2, V>}, L.none_some(V, val, Equal.sym(Maybe<&2, V>, Some{val}, None{}, L.subst(Cmp, c2 => {S.find_at(U32, V, c2, BE.Entry{k, val}, S.find(~U32, ~U32.cmp, V, v, t)) == None{} : Maybe<&2, V>}, U32.cmp(v, BE.key(U32, V, e)), EQ{}, ec, hf))))
    case BE.Entry{k, val} LT{}:
      L.subst(Cmp, c2 => {S.find_at(U32, V, c2, BE.Entry{k, val}, S.find(~U32, ~U32.cmp, V, v, t)) == None{} : Maybe<&2, V>}, U32.cmp(v, BE.key(U32, V, e)), LT{}, ec, hf)
    case BE.Entry{k, val} GT{}:
      L.subst(Cmp, c2 => {S.find_at(U32, V, c2, BE.Entry{k, val}, S.find(~U32, ~U32.cmp, V, v, t)) == None{} : Maybe<&2, V>}, U32.cmp(v, BE.key(U32, V, e)), GT{}, ec, hf)

def find_tail(-V: Data, +e: BE.Entry<U32, V>, +t: List<&2, BE.Entry<U32, V>>, +v: U32, +hf: {S.find(~U32, ~U32.cmp, V, v, Con{e, t}) == None{} : Maybe<&2, V>}) -> {S.find(~U32, ~U32.cmp, V, v, t) == None{} : Maybe<&2, V>}:
  find_tail_c(V, e, t, v, U32.cmp(v, BE.key(U32, V, e)), {==}, hf)

def ins_new(-V: Data, +xs: List<&2, BE.Entry<U32, V>>, +v: U32, +val: V, +hf: {S.find(~U32, ~U32.cmp, V, v, xs) == None{} : Maybe<&2, V>}) -> {ins_at(V, xs, lbx(V, v, xs), BE.Entry{v, val}) == S.ins(~U32, ~U32.cmp, V, v, val, xs) : List<&2, BE.Entry<U32, V>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      ins_new_c(V, e, t, v, val, Cmp.is_lt(U32.cmp(BE.key(U32, V, e), v)), {==}, hf, ins_new(V, t, v, val, find_tail(V, e, t, v, hf)))

# ---- `find` versus the lower bound ----

def keys_of(-V: Data, +es: List<&2, BE.Entry<U32, V>>) -> List<&2, U32>:
  match es:
    case Nil{}:
      Nil{}
    case Con{+e, t}:
      Con{BE.key(U32, V, e), keys_of(V, t)}

def eqm(m: Maybe<&2, U32>, +v: U32) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{+x}:
      Cmp.is_eq(U32.cmp(x, v))

def eq_at(+ws: List<&2, U32>, +i: Nat, +v: U32) -> Bool:
  eqm(SC.nth(U32, ws, i), v)

# Below every key of the list: `find` cannot succeed.
def lt_le_cmp(+c: Cmp, +h: {c == LT{} : Cmp}) -> {Cmp.is_le(c) == True{} : Bool}:
  L.subst(Cmp, z => {Cmp.is_le(z) == True{} : Bool}, LT{}, c, Equal.sym(Cmp, c, LT{}, h), {==})

def find_none_above(-V: Data, +es: List<&2, BE.Entry<U32, V>>, +v: U32, +k: U32, +hab: {SO.above(~U32, ~U32.cmp, V, es, k) == True{} : Bool}, +hvk: {U32.cmp(v, k) == LT{} : Cmp}) -> {S.find(~U32, ~U32.cmp, V, v, es) == None{} : Maybe<&2, V>}:
  match es:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      +hlt = O.u32_lt_le(v, k, BE.key(U32, V, e), hvk, lt_le_cmp(U32.cmp(k, BE.key(U32, V, e)), SO.ab_head(~U32, ~U32.cmp, V, e, t, k, hab)))
      L.subst(Cmp, c => {S.find_at(U32, V, c, e, S.find(~U32, ~U32.cmp, V, v, t)) == None{} : Maybe<&2, V>}, LT{}, U32.cmp(v, BE.key(U32, V, e)), Equal.sym(Cmp, U32.cmp(v, BE.key(U32, V, e)), LT{}, hlt),
        find_none_above(V, t, v, k, SO.ab_tail(~U32, ~U32.cmp, V, e, t, k, hab), hvk))

# `find` succeeds exactly when the entry at the lower bound has key v.
def eq_not_lt(+a: U32, +b: U32, +h: {U32.cmp(a, b) == EQ{} : Cmp}) -> {Cmp.is_lt(U32.cmp(a, b)) == False{} : Bool}:
  Equal.cong(Cmp, Bool, c => Cmp.is_lt(c), U32.cmp(a, b), EQ{}, h)

def flip_eq(+a: U32, +b: U32, +h: {U32.cmp(a, b) == EQ{} : Cmp}) -> {U32.cmp(b, a) == EQ{} : Cmp}:
  Equal.trans(Cmp, U32.cmp(b, a), O.flipc(U32.cmp(a, b)), EQ{}, O.u32_flip(a, b), Equal.cong(Cmp, Cmp, c => O.flipc(c), U32.cmp(a, b), EQ{}, h))

def eq_is_eq(+a: U32, +b: U32, +h: {U32.cmp(a, b) == EQ{} : Cmp}) -> {Cmp.is_eq(U32.cmp(a, b)) == True{} : Bool}:
  Equal.cong(Cmp, Bool, c => Cmp.is_eq(c), U32.cmp(a, b), EQ{}, h)

def lt_not_gt(+v: U32, +k: U32, +h: {U32.cmp(v, k) == LT{} : Cmp}) -> {Cmp.is_lt(U32.cmp(k, v)) == False{} : Bool}:
  Equal.cong(Cmp, Bool, c => Cmp.is_lt(c), U32.cmp(k, v), GT{},
    Equal.trans(Cmp, U32.cmp(k, v), O.flipc(U32.cmp(v, k)), GT{}, O.u32_flip(v, k), Equal.cong(Cmp, Cmp, c => O.flipc(c), U32.cmp(v, k), LT{}, h)))

def lt_not_eq(+v: U32, +k: U32, +h: {U32.cmp(v, k) == LT{} : Cmp}) -> {Cmp.is_eq(U32.cmp(k, v)) == False{} : Bool}:
  Equal.cong(Cmp, Bool, c => Cmp.is_eq(c), U32.cmp(k, v), GT{},
    Equal.trans(Cmp, U32.cmp(k, v), O.flipc(U32.cmp(v, k)), GT{}, O.u32_flip(v, k), Equal.cong(Cmp, Cmp, c => O.flipc(c), U32.cmp(v, k), LT{}, h)))

def gt_flip(+v: U32, +k: U32, +h: {U32.cmp(v, k) == GT{} : Cmp}) -> {Cmp.is_lt(U32.cmp(k, v)) == True{} : Bool}:
  Equal.cong(Cmp, Bool, c => Cmp.is_lt(c), U32.cmp(k, v), LT{},
    Equal.trans(Cmp, U32.cmp(k, v), O.flipc(U32.cmp(v, k)), LT{}, O.u32_flip(v, k), Equal.cong(Cmp, Cmp, c => O.flipc(c), U32.cmp(v, k), GT{}, h)))

def find_some_c(-V: Data, +k: U32, +val: V, +t: List<&2, BE.Entry<U32, V>>, +v: U32, +hs: {SO.sorted(~U32, ~U32.cmp, V, Con{BE.Entry{k, val}, t}) == True{} : Bool}, c: Cmp, +ec: {U32.cmp(v, k) == c : Cmp}, +ih: {S.is_some(V, S.find(~U32, ~U32.cmp, V, v, t)) == eq_at(keys_of(V, t), lbx(V, v, t), v) : Bool}) -> {S.is_some(V, S.find(~U32, ~U32.cmp, V, v, Con{BE.Entry{k, val}, t})) == eq_at(keys_of(V, Con{BE.Entry{k, val}, t}), lbx(V, v, Con{BE.Entry{k, val}, t}), v) : Bool}:
  match c:
    case EQ{}:
      # the head IS v: `find` stops there and the lower bound is 0
      L.subst(Cmp, z => {S.is_some(V, S.find_at(U32, V, z, BE.Entry{k, val}, S.find(~U32, ~U32.cmp, V, v, t))) == eq_at(keys_of(V, Con{BE.Entry{k, val}, t}), lbx(V, v, Con{BE.Entry{k, val}, t}), v) : Bool}, EQ{}, U32.cmp(v, k), Equal.sym(Cmp, U32.cmp(v, k), EQ{}, ec),
        L.subst(Bool, b => {True{} == eq_at(keys_of(V, Con{BE.Entry{k, val}, t}), lbx_step(b, lbx(V, v, t)), v) : Bool}, False{}, Cmp.is_lt(U32.cmp(k, v)), Equal.sym(Bool, Cmp.is_lt(U32.cmp(k, v)), False{}, eq_not_lt(k, v, flip_eq(v, k, ec))),
          Equal.sym(Bool, Cmp.is_eq(U32.cmp(k, v)), True{}, eq_is_eq(k, v, flip_eq(v, k, ec)))))
    case LT{}:
      # v is below the head, so it is below every key: `find` fails
      L.subst(Cmp, z => {S.is_some(V, S.find_at(U32, V, z, BE.Entry{k, val}, S.find(~U32, ~U32.cmp, V, v, t))) == eq_at(keys_of(V, Con{BE.Entry{k, val}, t}), lbx(V, v, Con{BE.Entry{k, val}, t}), v) : Bool}, LT{}, U32.cmp(v, k), Equal.sym(Cmp, U32.cmp(v, k), LT{}, ec),
        L.subst(Bool, b => {S.is_some(V, S.find(~U32, ~U32.cmp, V, v, t)) == eq_at(keys_of(V, Con{BE.Entry{k, val}, t}), lbx_step(b, lbx(V, v, t)), v) : Bool}, False{}, Cmp.is_lt(U32.cmp(k, v)), Equal.sym(Bool, Cmp.is_lt(U32.cmp(k, v)), False{}, lt_not_gt(v, k, ec)),
          Equal.trans(Bool, S.is_some(V, S.find(~U32, ~U32.cmp, V, v, t)), False{}, Cmp.is_eq(U32.cmp(k, v)),
            Equal.cong(Maybe<&2, V>, Bool, m => S.is_some(V, m), S.find(~U32, ~U32.cmp, V, v, t), None{},
              find_none_above(V, t, v, k, L.and_left(SO.above(~U32, ~U32.cmp, V, t, k), SO.sorted(~U32, ~U32.cmp, V, t), hs), ec)),
            Equal.sym(Bool, Cmp.is_eq(U32.cmp(k, v)), False{}, lt_not_eq(v, k, ec)))))
    case GT{}:
      # the head is below v: both sides move one step along
      L.subst(Cmp, z => {S.is_some(V, S.find_at(U32, V, z, BE.Entry{k, val}, S.find(~U32, ~U32.cmp, V, v, t))) == eq_at(keys_of(V, Con{BE.Entry{k, val}, t}), lbx(V, v, Con{BE.Entry{k, val}, t}), v) : Bool}, GT{}, U32.cmp(v, k), Equal.sym(Cmp, U32.cmp(v, k), GT{}, ec),
        L.subst(Bool, b => {S.is_some(V, S.find(~U32, ~U32.cmp, V, v, t)) == eq_at(keys_of(V, Con{BE.Entry{k, val}, t}), lbx_step(b, lbx(V, v, t)), v) : Bool}, True{}, Cmp.is_lt(U32.cmp(k, v)), Equal.sym(Bool, Cmp.is_lt(U32.cmp(k, v)), True{}, gt_flip(v, k, ec)),
          ih))

# comparison bookkeeping
def find_some(-V: Data, +es: List<&2, BE.Entry<U32, V>>, +v: U32, +hs: {SO.sorted(~U32, ~U32.cmp, V, es) == True{} : Bool}) -> {S.is_some(V, S.find(~U32, ~U32.cmp, V, v, es)) == eq_at(keys_of(V, es), lbx(V, v, es), v) : Bool}:
  match es:
    case Nil{}:
      {==}
    case Con{BE.Entry{+k, +val}, +t}:
      find_some_c(V, k, val, t, v, hs, U32.cmp(v, k), {==},
        find_some(V, t, v, L.and_right(SO.above(~U32, ~U32.cmp, V, t, k), SO.sorted(~U32, ~U32.cmp, V, t), hs)))

# ---- `find` returns the value stored at the lower bound ----

def pickv(-V: Data, b: Bool, x: V) -> Maybe<&2, V>:
  match b:
    case True{}:
      Some{x}
    case False{}:
      None{}

def ent_val(-V: Data, m: Maybe<&2, BE.Entry<U32, V>>, +v: U32) -> Maybe<&2, V>:
  match m:
    case None{}:
      None{}
    case Some{BE.Entry{+k, x}}:
      pickv(V, Cmp.is_eq(U32.cmp(k, v)), x)

def at_val(-V: Data, +es: List<&2, BE.Entry<U32, V>>, +i: Nat, +v: U32) -> Maybe<&2, V>:
  ent_val(V, SC.nth(BE.Entry<U32, V>, es, i), v)

def find_val_c(-V: Data, +k: U32, +val: V, +t: List<&2, BE.Entry<U32, V>>, +v: U32, +hs: {SO.sorted(~U32, ~U32.cmp, V, Con{BE.Entry{k, val}, t}) == True{} : Bool}, c: Cmp, +ec: {U32.cmp(v, k) == c : Cmp}, +ih: {S.find(~U32, ~U32.cmp, V, v, t) == at_val(V, t, lbx(V, v, t), v) : Maybe<&2, V>}) -> {S.find(~U32, ~U32.cmp, V, v, Con{BE.Entry{k, val}, t}) == at_val(V, Con{BE.Entry{k, val}, t}, lbx(V, v, Con{BE.Entry{k, val}, t}), v) : Maybe<&2, V>}:
  match c:
    case EQ{}:
      L.subst(Cmp, z => {S.find_at(U32, V, z, BE.Entry{k, val}, S.find(~U32, ~U32.cmp, V, v, t)) == at_val(V, Con{BE.Entry{k, val}, t}, lbx(V, v, Con{BE.Entry{k, val}, t}), v) : Maybe<&2, V>}, EQ{}, U32.cmp(v, k), Equal.sym(Cmp, U32.cmp(v, k), EQ{}, ec),
        L.subst(Bool, b => {Some{val} == at_val(V, Con{BE.Entry{k, val}, t}, lbx_step(b, lbx(V, v, t)), v) : Maybe<&2, V>}, False{}, Cmp.is_lt(U32.cmp(k, v)), Equal.sym(Bool, Cmp.is_lt(U32.cmp(k, v)), False{}, eq_not_lt(k, v, flip_eq(v, k, ec))),
          L.subst(Bool, b => {Some{val} == pickv(V, b, val) : Maybe<&2, V>}, True{}, Cmp.is_eq(U32.cmp(k, v)), Equal.sym(Bool, Cmp.is_eq(U32.cmp(k, v)), True{}, eq_is_eq(k, v, flip_eq(v, k, ec))), {==})))
    case LT{}:
      L.subst(Cmp, z => {S.find_at(U32, V, z, BE.Entry{k, val}, S.find(~U32, ~U32.cmp, V, v, t)) == at_val(V, Con{BE.Entry{k, val}, t}, lbx(V, v, Con{BE.Entry{k, val}, t}), v) : Maybe<&2, V>}, LT{}, U32.cmp(v, k), Equal.sym(Cmp, U32.cmp(v, k), LT{}, ec),
        L.subst(Bool, b => {S.find(~U32, ~U32.cmp, V, v, t) == at_val(V, Con{BE.Entry{k, val}, t}, lbx_step(b, lbx(V, v, t)), v) : Maybe<&2, V>}, False{}, Cmp.is_lt(U32.cmp(k, v)), Equal.sym(Bool, Cmp.is_lt(U32.cmp(k, v)), False{}, lt_not_gt(v, k, ec)),
          Equal.trans(Maybe<&2, V>, S.find(~U32, ~U32.cmp, V, v, t), None{}, pickv(V, Cmp.is_eq(U32.cmp(k, v)), val),
            find_none_above(V, t, v, k, L.and_left(SO.above(~U32, ~U32.cmp, V, t, k), SO.sorted(~U32, ~U32.cmp, V, t), hs), ec),
            L.subst(Bool, b => {None{} == pickv(V, b, val) : Maybe<&2, V>}, False{}, Cmp.is_eq(U32.cmp(k, v)), Equal.sym(Bool, Cmp.is_eq(U32.cmp(k, v)), False{}, lt_not_eq(v, k, ec)), {==}))))
    case GT{}:
      L.subst(Cmp, z => {S.find_at(U32, V, z, BE.Entry{k, val}, S.find(~U32, ~U32.cmp, V, v, t)) == at_val(V, Con{BE.Entry{k, val}, t}, lbx(V, v, Con{BE.Entry{k, val}, t}), v) : Maybe<&2, V>}, GT{}, U32.cmp(v, k), Equal.sym(Cmp, U32.cmp(v, k), GT{}, ec),
        L.subst(Bool, b => {S.find(~U32, ~U32.cmp, V, v, t) == at_val(V, Con{BE.Entry{k, val}, t}, lbx_step(b, lbx(V, v, t)), v) : Maybe<&2, V>}, True{}, Cmp.is_lt(U32.cmp(k, v)), Equal.sym(Bool, Cmp.is_lt(U32.cmp(k, v)), True{}, gt_flip(v, k, ec)),
          ih))

def find_val(-V: Data, +es: List<&2, BE.Entry<U32, V>>, +v: U32, +hs: {SO.sorted(~U32, ~U32.cmp, V, es) == True{} : Bool}) -> {S.find(~U32, ~U32.cmp, V, v, es) == at_val(V, es, lbx(V, v, es), v) : Maybe<&2, V>}:
  match es:
    case Nil{}:
      {==}
    case Con{BE.Entry{+k, +val}, +t}:
      find_val_c(V, k, val, t, v, hs, U32.cmp(v, k), {==},
        find_val(V, t, v, L.and_right(SO.above(~U32, ~U32.cmp, V, t, k), SO.sorted(~U32, ~U32.cmp, V, t), hs)))
