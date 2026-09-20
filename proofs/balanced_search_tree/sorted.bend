import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/order.bend as O
import ../../spec/common.bend as SC
import ../../spec/balanced_search_tree.bend as S
import ../../types/balanced_search_tree.bend as E

# Strictly sorted entry lists (w.r.t. a comparator with total-order laws
# ~o) and how the specification's map operations act on a list split as
# A ++ [e] ++ R around an entry e.

# ---- comparator facts ----

def is_lt_of(+c: Cmp, +e: {c == LT{} : Cmp}) -> {Cmp.is_lt(c) == True{} : Bool}:
  %Equal.sym(Cmp, c, LT{}, e) : {Cmp.is_lt(_) == True{} : Bool}
  {==}

def gt_of_lt(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +a: K, +b: K, +h: {cmp(a, b) == LT{} : Cmp}) -> {cmp(b, a) == GT{} : Cmp}:
  %Equal.sym(Cmp, cmp(b, a), O.flipc(cmp(a, b)), O.flip(~K, ~cmp, o, a, b)) : {_ == GT{} : Cmp}
  %Equal.sym(Cmp, cmp(a, b), LT{}, h) : {O.flipc(_) == GT{} : Cmp}
  {==}

def lt_of_gt(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +a: K, +b: K, +h: {cmp(a, b) == GT{} : Cmp}) -> {cmp(b, a) == LT{} : Cmp}:
  %Equal.sym(Cmp, cmp(b, a), O.flipc(cmp(a, b)), O.flip(~K, ~cmp, o, a, b)) : {_ == LT{} : Cmp}
  %Equal.sym(Cmp, cmp(a, b), GT{}, h) : {O.flipc(_) == LT{} : Cmp}
  {==}

def le_of_lt(+c: Cmp, +e: {c == LT{} : Cmp}) -> {Cmp.is_le(c) == True{} : Bool}:
  %Equal.sym(Cmp, c, LT{}, e) : {Cmp.is_le(_) == True{} : Bool}
  {==}

def lt_case(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +a: K, +b: K, +c: K, +bc: {cmp(b, c) == LT{} : Cmp}, +ba: {cmp(b, a) == GT{} : Cmp}, +le: {Cmp.is_le(cmp(a, c)) == True{} : Bool}, r: Cmp, +er: {cmp(a, c) == r : Cmp}) -> {cmp(a, c) == LT{} : Cmp}:
  match r:
    case LT{}:
      er
    case EQ{}:
      +eq = O.antisym(~K, ~cmp, o, a, c, er)
      Empty.absurd({cmp(a, c) == LT{} : Cmp}, L.cmp_lt_gt(Equal.trans(Cmp, LT{}, cmp(b, c), GT{}, Equal.sym(Cmp, cmp(b, c), LT{}, bc), L.subst(K, x => {cmp(b, x) == GT{} : Cmp}, a, c, eq, ba))))
    case GT{}:
      Empty.absurd({cmp(a, c) == LT{} : Cmp}, L.true_false(Equal.trans(Bool, True{}, Cmp.is_le(cmp(a, c)), False{}, Equal.sym(Bool, Cmp.is_le(cmp(a, c)), True{}, le), %Equal.sym(Cmp, cmp(a, c), GT{}, er) : {Cmp.is_le(_) == False{} : Bool}
        {==})))

# a < b and b < c give a < c.
def lt_trans(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +a: K, +b: K, +c: K, +ab: {cmp(a, b) == LT{} : Cmp}, +bc: {cmp(b, c) == LT{} : Cmp}) -> {cmp(a, c) == LT{} : Cmp}:
  lt_case(~K, ~cmp, ~o, a, b, c, bc, gt_of_lt(~K, ~cmp, ~o, a, b, ab), O.trans(~K, ~cmp, o, a, b, c, le_of_lt(cmp(a, b), ab), le_of_lt(cmp(b, c), bc)), cmp(a, c), {==})

# a < b and b = c give a < c.
def lt_eq(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +a: K, +b: K, +c: K, +ab: {cmp(a, b) == LT{} : Cmp}, +bc: {cmp(b, c) == EQ{} : Cmp}) -> {cmp(a, c) == LT{} : Cmp}:
  L.subst(K, x => {cmp(a, x) == LT{} : Cmp}, b, c, O.antisym(~K, ~cmp, o, b, c, bc), ab)

# ---- keys below / above a bound; strict sortedness ----

def kk(-K: Data, -V: Data, e: E.Entry<K, V>) -> K:
  E.key(K, V, e)

def below(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, xs: List<&2, E.Entry<K, V>>, +k: K) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{e, t}:
      Bool.and(Cmp.is_lt(cmp(E.key(K, V, e), k)), below(~K, ~cmp, V, t, k))

def above(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, xs: List<&2, E.Entry<K, V>>, +k: K) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{e, t}:
      Bool.and(Cmp.is_lt(cmp(k, E.key(K, V, e))), above(~K, ~cmp, V, t, k))

def sorted(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, xs: List<&2, E.Entry<K, V>>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+e, +t}:
      Bool.and(above(~K, ~cmp, V, t, E.key(K, V, e)), sorted(~K, ~cmp, V, t))

def bl_head(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +e: E.Entry<K, V>, +t: List<&2, E.Entry<K, V>>, +k: K, +h: {below(~K, ~cmp, V, Con{e, t}, k) == True{} : Bool}) -> {cmp(E.key(K, V, e), k) == LT{} : Cmp}:
  O.lt_is(cmp(E.key(K, V, e), k), L.and_left(Cmp.is_lt(cmp(E.key(K, V, e), k)), below(~K, ~cmp, V, t, k), h))

def bl_tail(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +e: E.Entry<K, V>, +t: List<&2, E.Entry<K, V>>, +k: K, +h: {below(~K, ~cmp, V, Con{e, t}, k) == True{} : Bool}) -> {below(~K, ~cmp, V, t, k) == True{} : Bool}:
  L.and_right(Cmp.is_lt(cmp(E.key(K, V, e), k)), below(~K, ~cmp, V, t, k), h)

def ab_head(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +e: E.Entry<K, V>, +t: List<&2, E.Entry<K, V>>, +k: K, +h: {above(~K, ~cmp, V, Con{e, t}, k) == True{} : Bool}) -> {cmp(k, E.key(K, V, e)) == LT{} : Cmp}:
  O.lt_is(cmp(k, E.key(K, V, e)), L.and_left(Cmp.is_lt(cmp(k, E.key(K, V, e))), above(~K, ~cmp, V, t, k), h))

def ab_tail(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +e: E.Entry<K, V>, +t: List<&2, E.Entry<K, V>>, +k: K, +h: {above(~K, ~cmp, V, Con{e, t}, k) == True{} : Bool}) -> {above(~K, ~cmp, V, t, k) == True{} : Bool}:
  L.and_right(Cmp.is_lt(cmp(k, E.key(K, V, e))), above(~K, ~cmp, V, t, k), h)

def so_above(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +e: E.Entry<K, V>, +t: List<&2, E.Entry<K, V>>, +h: {sorted(~K, ~cmp, V, Con{e, t}) == True{} : Bool}) -> {above(~K, ~cmp, V, t, E.key(K, V, e)) == True{} : Bool}:
  L.and_left(above(~K, ~cmp, V, t, E.key(K, V, e)), sorted(~K, ~cmp, V, t), h)

def so_tail(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +e: E.Entry<K, V>, +t: List<&2, E.Entry<K, V>>, +h: {sorted(~K, ~cmp, V, Con{e, t}) == True{} : Bool}) -> {sorted(~K, ~cmp, V, t) == True{} : Bool}:
  L.and_right(above(~K, ~cmp, V, t, E.key(K, V, e)), sorted(~K, ~cmp, V, t), h)

def so_mk(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +e: E.Entry<K, V>, +t: List<&2, E.Entry<K, V>>, +a: {above(~K, ~cmp, V, t, E.key(K, V, e)) == True{} : Bool}, +b: {sorted(~K, ~cmp, V, t) == True{} : Bool}) -> {sorted(~K, ~cmp, V, Con{e, t}) == True{} : Bool}:
  L.and_intro(above(~K, ~cmp, V, t, E.key(K, V, e)), sorted(~K, ~cmp, V, t), a, b)

def above_app(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +xs: List<&2, E.Entry<K, V>>, +ys: List<&2, E.Entry<K, V>>, +k: K, +h: {above(~K, ~cmp, V, SC.append(E.Entry<K, V>, xs, ys), k) == True{} : Bool}) -> {above(~K, ~cmp, V, ys, k) == True{} : Bool}:
  match xs:
    case Nil{}:
      h
    case Con{x, t}:
      above_app(~K, ~cmp, V, t, ys, k, ab_tail(~K, ~cmp, V, x, SC.append(E.Entry<K, V>, t, ys), k, h))

def above_pre(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +xs: List<&2, E.Entry<K, V>>, +ys: List<&2, E.Entry<K, V>>, +k: K, +h: {above(~K, ~cmp, V, SC.append(E.Entry<K, V>, xs, ys), k) == True{} : Bool}) -> {above(~K, ~cmp, V, xs, k) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, t}:
      L.and_intro(Cmp.is_lt(cmp(k, E.key(K, V, x))), above(~K, ~cmp, V, t, k), L.and_left(Cmp.is_lt(cmp(k, E.key(K, V, x))), above(~K, ~cmp, V, SC.append(E.Entry<K, V>, t, ys), k), h), above_pre(~K, ~cmp, V, t, ys, k, ab_tail(~K, ~cmp, V, x, SC.append(E.Entry<K, V>, t, ys), k, h)))

# sorted(A ++ B) gives sorted(A) and sorted(B).
def so_left(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +xs: List<&2, E.Entry<K, V>>, +ys: List<&2, E.Entry<K, V>>, +h: {sorted(~K, ~cmp, V, SC.append(E.Entry<K, V>, xs, ys)) == True{} : Bool}) -> {sorted(~K, ~cmp, V, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, t}:
      so_mk(~K, ~cmp, V, x, t, above_pre(~K, ~cmp, V, t, ys, E.key(K, V, x), so_above(~K, ~cmp, V, x, SC.append(E.Entry<K, V>, t, ys), h)), so_left(~K, ~cmp, V, t, ys, so_tail(~K, ~cmp, V, x, SC.append(E.Entry<K, V>, t, ys), h)))

def so_right(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +xs: List<&2, E.Entry<K, V>>, +ys: List<&2, E.Entry<K, V>>, +h: {sorted(~K, ~cmp, V, SC.append(E.Entry<K, V>, xs, ys)) == True{} : Bool}) -> {sorted(~K, ~cmp, V, ys) == True{} : Bool}:
  match xs:
    case Nil{}:
      h
    case Con{x, t}:
      so_right(~K, ~cmp, V, t, ys, so_tail(~K, ~cmp, V, x, SC.append(E.Entry<K, V>, t, ys), h))

# sorted(A ++ [e] ++ R) gives: every key of A is below key e.
def so_below(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +xs: List<&2, E.Entry<K, V>>, +e: E.Entry<K, V>, +r: List<&2, E.Entry<K, V>>, +h: {sorted(~K, ~cmp, V, SC.append(E.Entry<K, V>, xs, Con{e, r})) == True{} : Bool}) -> {below(~K, ~cmp, V, xs, E.key(K, V, e)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, t}:
      L.and_intro(Cmp.is_lt(cmp(E.key(K, V, x), E.key(K, V, e))), below(~K, ~cmp, V, t, E.key(K, V, e)),
        is_lt_of(cmp(E.key(K, V, x), E.key(K, V, e)), ab_head(~K, ~cmp, V, e, r, E.key(K, V, x), above_app(~K, ~cmp, V, t, Con{e, r}, E.key(K, V, x), so_above(~K, ~cmp, V, x, SC.append(E.Entry<K, V>, t, Con{e, r}), h)))),
        so_below(~K, ~cmp, V, t, e, r, so_tail(~K, ~cmp, V, x, SC.append(E.Entry<K, V>, t, Con{e, r}), h)))

def below_lt(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), -V: Data, +xs: List<&2, E.Entry<K, V>>, +a: K, +b: K, +h: {below(~K, ~cmp, V, xs, a) == True{} : Bool}, +ab: {cmp(a, b) == LT{} : Cmp}) -> {below(~K, ~cmp, V, xs, b) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, t}:
      L.and_intro(Cmp.is_lt(cmp(E.key(K, V, x), b)), below(~K, ~cmp, V, t, b), is_lt_of(cmp(E.key(K, V, x), b), lt_trans(~K, ~cmp, ~o, E.key(K, V, x), a, b, bl_head(~K, ~cmp, V, x, t, a, h), ab)), below_lt(~K, ~cmp, ~o, V, t, a, b, bl_tail(~K, ~cmp, V, x, t, a, h), ab))

def below_eq(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), -V: Data, +xs: List<&2, E.Entry<K, V>>, +a: K, +b: K, +h: {below(~K, ~cmp, V, xs, a) == True{} : Bool}, +ab: {cmp(a, b) == EQ{} : Cmp}) -> {below(~K, ~cmp, V, xs, b) == True{} : Bool}:
  L.subst(K, x => {below(~K, ~cmp, V, xs, x) == True{} : Bool}, a, b, O.antisym(~K, ~cmp, o, a, b, ab), h)

def above_gt(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), -V: Data, +xs: List<&2, E.Entry<K, V>>, +a: K, +b: K, +h: {above(~K, ~cmp, V, xs, a) == True{} : Bool}, +ba: {cmp(b, a) == LT{} : Cmp}) -> {above(~K, ~cmp, V, xs, b) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, t}:
      L.and_intro(Cmp.is_lt(cmp(b, E.key(K, V, x))), above(~K, ~cmp, V, t, b), is_lt_of(cmp(b, E.key(K, V, x)), lt_trans(~K, ~cmp, ~o, b, a, E.key(K, V, x), ba, ab_head(~K, ~cmp, V, x, t, a, h))), above_gt(~K, ~cmp, ~o, V, t, a, b, ab_tail(~K, ~cmp, V, x, t, a, h), ba))

def above_eq(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), -V: Data, +xs: List<&2, E.Entry<K, V>>, +a: K, +b: K, +h: {above(~K, ~cmp, V, xs, a) == True{} : Bool}, +ab: {cmp(a, b) == EQ{} : Cmp}) -> {above(~K, ~cmp, V, xs, b) == True{} : Bool}:
  L.subst(K, x => {above(~K, ~cmp, V, xs, x) == True{} : Bool}, a, b, O.antisym(~K, ~cmp, o, a, b, ab), h)
