import Base
import ../../lib/spec_common.bend as C
import ../../../src/containers/balanced_search_tree.bend as M

# Independent model of the indexed TreeMap: a limit exponent (at most
# 2^limit entries) and the entries in key order under the comparator ~cmp.
# Cursors name their next and current entries by key; views are the map with
# a range and a direction. Nothing here refers to nodes, colours, links,
# slots or the free list; only the neutral datatypes of the implementation
# module (M.Entry, M.Rejected, M.Error, M.Bound) are used.

type Model<-K: Data, -V: Data> is Data:
  TM{limit: Nat, es: List<&2, M.Entry<K, V>>}

type Cursor<-K: Data, -V: Data> is Data:
  CR{map: Model<K, V>, next: Maybe<&2, K>, current: Maybe<&2, K>, lower: M.Bound<K>, upper: M.Bound<K>, forward: Bool}

type View<-K: Data, -V: Data> is Data:
  VW{map: Model<K, V>, lower: M.Bound<K>, upper: M.Bound<K>, descending: Bool}

type InvalidView<-K: Data, -V: Data> is Data:
  IV{map: Model<K, V>, error: M.Error}

def pick(-T: Type, +b: Bool, x: T, y: T) -> T:
  match b:
    case True{}:
      x
    case False{}:
      y

def new(-K: Data, -V: Data) -> Model<K, V>:
  TM{31n, Nil{}}

def with_limit(-K: Data, -V: Data, +k: Nat) -> Model<K, V>:
  TM{pick(Nat, Nat.is_lt(k, 31n), k, 31n), Nil{}}

def key(-K: Data, -V: Data, e: M.Entry<K, V>) -> K:
  match e:
    case M.Entry{k, v}:
      k

def val(-K: Data, -V: Data, e: M.Entry<K, V>) -> V:
  match e:
    case M.Entry{k, v}:
      v

def keys(-K: Data, -V: Data, es: List<&2, M.Entry<K, V>>) -> List<&2, K>:
  match es:
    case Nil{}:
      Nil{}
    case Con{e, t}:
      Con{key(K, V, e), keys(K, V, t)}

def is_eq(c: Cmp) -> Bool:
  match c:
    case EQ{}:
      True{}
    case _:
      False{}

# ---- the entry of a key ----

# the first entry whose key is equal to k
def find_e(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +k: K, es: List<&2, M.Entry<K, V>>) -> Maybe<&2, M.Entry<K, V>>:
  match es:
    case Nil{}:
      None{}
    case Con{+e, +t}:
      pick(Maybe<&2, M.Entry<K, V>>, is_eq(cmp(k, key(K, V, e))), Some{e}, find_e(~K, ~V, ~cmp, k, t))

def val_m(-K: Data, -V: Data, m: Maybe<&2, M.Entry<K, V>>) -> Maybe<&2, V>:
  match m:
    case None{}:
      None{}
    case Some{e}:
      Some{val(K, V, e)}

def key_m(-K: Data, -V: Data, m: Maybe<&2, M.Entry<K, V>>) -> Maybe<&2, K>:
  match m:
    case None{}:
      None{}
    case Some{e}:
      Some{key(K, V, e)}

def find(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +k: K, es: List<&2, M.Entry<K, V>>) -> Maybe<&2, V>:
  val_m(K, V, find_e(~K, ~V, ~cmp, k, es))

def is_some(-X: Data, m: Maybe<&2, X>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{x}:
      True{}

# ---- changes ----

# k, absent, inserted before the first entry with a greater key
def ins(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +k: K, +v: V, es: List<&2, M.Entry<K, V>>) -> List<&2, M.Entry<K, V>>:
  match es:
    case Nil{}:
      Con{M.Entry{k, v}, Nil{}}
    case Con{+e, +t}:
      pick(List<&2, M.Entry<K, V>>, Cmp.is_lt(cmp(k, key(K, V, e))), Con{M.Entry{k, v}, Con{e, t}}, Con{e, ins(~K, ~V, ~cmp, k, v, t)})

# the value of the first entry equal to k replaced (its key is kept)
def set_val(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +k: K, +v: V, es: List<&2, M.Entry<K, V>>) -> List<&2, M.Entry<K, V>>:
  match es:
    case Nil{}:
      Nil{}
    case Con{+e, +t}:
      pick(List<&2, M.Entry<K, V>>, is_eq(cmp(k, key(K, V, e))), Con{M.Entry{key(K, V, e), v}, t}, Con{e, set_val(~K, ~V, ~cmp, k, v, t)})

# the first entry equal to k removed
def del(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +k: K, es: List<&2, M.Entry<K, V>>) -> List<&2, M.Entry<K, V>>:
  match es:
    case Nil{}:
      Nil{}
    case Con{+e, +t}:
      pick(List<&2, M.Entry<K, V>>, is_eq(cmp(k, key(K, V, e))), t, Con{e, del(~K, ~V, ~cmp, k, t)})

# ---- ranges ----

def ordering_ok(c: Cmp, inclusive: Bool) -> Bool:
  match c:
    case LT{}:
      True{}
    case EQ{}:
      inclusive
    case GT{}:
      False{}

def above_lower(~K: Data, ~cmp: K -> K -> Cmp, +k: K, b: M.Bound<K>) -> Bool:
  match b:
    case M.Unbounded{}:
      True{}
    case M.Inclusive{lo}:
      ordering_ok(cmp(lo, k), True{})
    case M.Exclusive{lo}:
      ordering_ok(cmp(lo, k), False{})

def below_upper(~K: Data, ~cmp: K -> K -> Cmp, +k: K, b: M.Bound<K>) -> Bool:
  match b:
    case M.Unbounded{}:
      True{}
    case M.Inclusive{hi}:
      ordering_ok(cmp(k, hi), True{})
    case M.Exclusive{hi}:
      ordering_ok(cmp(k, hi), False{})

def in_range(~K: Data, ~cmp: K -> K -> Cmp, +k: K, lo: M.Bound<K>, hi: M.Bound<K>) -> Bool:
  Bool.and(above_lower(~K, ~cmp, k, lo), below_upper(~K, ~cmp, k, hi))

# a view's bounds are valid when neither is past the other
def bounds_valid(~K: Data, ~cmp: K -> K -> Cmp, lo: M.Bound<K>, hi: M.Bound<K>) -> Bool:
  match lo hi:
    case M.Unbounded{} _:
      True{}
    case _ M.Unbounded{}:
      True{}
    case M.Inclusive{a} M.Inclusive{b}:
      ordering_ok(cmp(a, b), True{})
    case M.Inclusive{a} M.Exclusive{b}:
      ordering_ok(cmp(a, b), True{})
    case M.Exclusive{a} M.Inclusive{b}:
      ordering_ok(cmp(a, b), True{})
    case M.Exclusive{a} M.Exclusive{b}:
      ordering_ok(cmp(a, b), True{})

def within(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +lo: M.Bound<K>, +hi: M.Bound<K>, es: List<&2, M.Entry<K, V>>) -> List<&2, M.Entry<K, V>>:
  match es:
    case Nil{}:
      Nil{}
    case Con{+e, +t}:
      pick(List<&2, M.Entry<K, V>>, in_range(~K, ~cmp, key(K, V, e), lo, hi), Con{e, within(~K, ~V, ~cmp, lo, hi, t)}, within(~K, ~V, ~cmp, lo, hi, t))

def outside(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +lo: M.Bound<K>, +hi: M.Bound<K>, es: List<&2, M.Entry<K, V>>) -> List<&2, M.Entry<K, V>>:
  match es:
    case Nil{}:
      Nil{}
    case Con{+e, +t}:
      pick(List<&2, M.Entry<K, V>>, in_range(~K, ~cmp, key(K, V, e), lo, hi), outside(~K, ~V, ~cmp, lo, hi, t), Con{e, outside(~K, ~V, ~cmp, lo, hi, t)})

# ---- order queries ----

# the first entry e with keep(cmp(k, e.key))
def first_where(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +k: K, +inclusive: Bool, es: List<&2, M.Entry<K, V>>) -> Maybe<&2, M.Entry<K, V>>:
  match es:
    case Nil{}:
      None{}
    case Con{+e, +t}:
      pick(Maybe<&2, M.Entry<K, V>>, ordering_ok(cmp(k, key(K, V, e)), inclusive), Some{e}, first_where(~K, ~V, ~cmp, k, inclusive, t))

# the last entry e below k (or equal, when inclusive)
def last_where(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +k: K, +inclusive: Bool, es: List<&2, M.Entry<K, V>>, +best: Maybe<&2, M.Entry<K, V>>) -> Maybe<&2, M.Entry<K, V>>:
  match es:
    case Nil{}:
      best
    case Con{+e, t}:
      last_where(~K, ~V, ~cmp, k, inclusive, t, pick(Maybe<&2, M.Entry<K, V>>, ordering_ok(cmp(key(K, V, e), k), inclusive), Some{e}, best))

def head(-X: Data, xs: List<&2, X>) -> Maybe<&2, X>:
  match xs:
    case Nil{}:
      None{}
    case Con{x, t}:
      Some{x}

def last(-X: Data, xs: List<&2, X>) -> Maybe<&2, X>:
  C.last(X, xs)

# ceiling (higher: strict) when up, floor (lower: strict) otherwise
def nav(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +k: K, +up: Bool, +inclusive: Bool, es: List<&2, M.Entry<K, V>>) -> Maybe<&2, M.Entry<K, V>>:
  match up:
    case True{}:
      first_where(~K, ~V, ~cmp, k, inclusive, es)
    case False{}:
      last_where(~K, ~V, ~cmp, k, inclusive, es, None{})

# the key after (forward) or before k
def succ(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +k: K, +forward: Bool, es: List<&2, M.Entry<K, V>>) -> Maybe<&2, K>:
  key_m(K, V, nav(~K, ~V, ~cmp, k, forward, False{}, es))

# the first entry past a bound, in a direction
def start(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, b: M.Bound<K>, +forward: Bool, es: List<&2, M.Entry<K, V>>) -> Maybe<&2, K>:
  match b forward:
    case M.Unbounded{} True{}:
      key_m(K, V, head(M.Entry<K, V>, es))
    case M.Unbounded{} False{}:
      key_m(K, V, last(M.Entry<K, V>, es))
    case M.Inclusive{+x} _:
      key_m(K, V, nav(~K, ~V, ~cmp, x, forward, True{}, es))
    case M.Exclusive{+x} _:
      key_m(K, V, nav(~K, ~V, ~cmp, x, forward, False{}, es))

# ---- the map ----


def size(-K: Data, -V: Data, m: Model<K, V>) -> Model<K, V> & Nat:
  match m:
    case TM{+l, +es}:
      (TM{l, es}, C.length(M.Entry<K, V>, es))

def is_empty(-K: Data, -V: Data, m: Model<K, V>) -> Model<K, V> & Bool:
  match m:
    case TM{+l, +es}:
      (TM{l, es}, Nat.is_eq(C.length(M.Entry<K, V>, es), 0n))

def put_new(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +l: Nat, +es: List<&2, M.Entry<K, V>>, +k: K, +v: V) -> Model<K, V> & Result<&2, &2, M.Rejected<K, V>, Maybe<&2, V>>:
  pick(Model<K, V> & Result<&2, &2, M.Rejected<K, V>, Maybe<&2, V>>, Nat.is_lt(C.length(M.Entry<K, V>, es), C.pow2(l)), (TM{l, ins(~K, ~V, ~cmp, k, v, es)}, Done{None{}}), (TM{l, es}, Fail{M.Rejected{M.CapacityExceeded{}, k, v}}))

def put_at(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +l: Nat, +es: List<&2, M.Entry<K, V>>, +k: K, +v: V, old: Maybe<&2, V>) -> Model<K, V> & Result<&2, &2, M.Rejected<K, V>, Maybe<&2, V>>:
  match old:
    case Some{+o}:
      (TM{l, set_val(~K, ~V, ~cmp, k, v, es)}, Done{Some{o}})
    case None{}:
      put_new(~K, ~V, ~cmp, l, es, k, v)

# k mapped to v: replaced when present, inserted when there is room
def put(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, m: Model<K, V>, +k: K, +v: V) -> Model<K, V> & Result<&2, &2, M.Rejected<K, V>, Maybe<&2, V>>:
  match m:
    case TM{+l, +es}:
      put_at(~K, ~V, ~cmp, l, es, k, v, find(~K, ~V, ~cmp, k, es))

def absent_at(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +l: Nat, +es: List<&2, M.Entry<K, V>>, +k: K, +v: V, old: Maybe<&2, V>) -> Model<K, V> & Result<&2, &2, M.Rejected<K, V>, Maybe<&2, V>>:
  match old:
    case Some{+o}:
      (TM{l, es}, Done{Some{o}})
    case None{}:
      put_new(~K, ~V, ~cmp, l, es, k, v)

def put_if_absent(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, m: Model<K, V>, +k: K, +v: V) -> Model<K, V> & Result<&2, &2, M.Rejected<K, V>, Maybe<&2, V>>:
  match m:
    case TM{+l, +es}:
      absent_at(~K, ~V, ~cmp, l, es, k, v, find(~K, ~V, ~cmp, k, es))

def get(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, m: Model<K, V>, +k: K) -> Model<K, V> & Maybe<&2, V>:
  match m:
    case TM{+l, +es}:
      (TM{l, es}, find(~K, ~V, ~cmp, k, es))

def or_default(-V: Data, m: Maybe<&2, V>, fallback: V) -> V:
  match m:
    case None{}:
      fallback
    case Some{v}:
      v

def get_or_default(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, m: Model<K, V>, +k: K, fallback: V) -> Model<K, V> & V:
  match m:
    case TM{+l, +es}:
      (TM{l, es}, or_default(V, find(~K, ~V, ~cmp, k, es), fallback))

def contains_key(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, m: Model<K, V>, +k: K) -> Model<K, V> & Bool:
  match m:
    case TM{+l, +es}:
      (TM{l, es}, is_some(V, find(~K, ~V, ~cmp, k, es)))

def remove(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, m: Model<K, V>, +k: K) -> Model<K, V> & Maybe<&2, V>:
  match m:
    case TM{+l, +es}:
      (TM{l, del(~K, ~V, ~cmp, k, es)}, find(~K, ~V, ~cmp, k, es))

def replace_at(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +l: Nat, +es: List<&2, M.Entry<K, V>>, +k: K, +v: V, old: Maybe<&2, V>) -> Model<K, V> & Maybe<&2, V>:
  match old:
    case Some{+o}:
      (TM{l, set_val(~K, ~V, ~cmp, k, v, es)}, Some{o})
    case None{}:
      (TM{l, es}, None{})

def replace(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, m: Model<K, V>, +k: K, +v: V) -> Model<K, V> & Maybe<&2, V>:
  match m:
    case TM{+l, +es}:
      replace_at(~K, ~V, ~cmp, l, es, k, v, find(~K, ~V, ~cmp, k, es))

def any_value(~K: Data, ~V: Data, ~eq: V -> V -> Bool, +w: V, es: List<&2, M.Entry<K, V>>) -> Bool:
  match es:
    case Nil{}:
      False{}
    case Con{e, t}:
      Bool.or(eq(val(K, V, e), w), any_value(~K, ~V, ~eq, w, t))

def contains_value(~K: Data, ~V: Data, ~eq: V -> V -> Bool, m: Model<K, V>, +w: V) -> Model<K, V> & Bool:
  match m:
    case TM{+l, +es}:
      (TM{l, es}, any_value(~K, ~V, ~eq, w, es))

def remove_if_at(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~eq: V -> V -> Bool, +l: Nat, +es: List<&2, M.Entry<K, V>>, +k: K, +expected: V, old: Maybe<&2, V>) -> Model<K, V> & Bool:
  match old:
    case None{}:
      (TM{l, es}, False{})
    case Some{o}:
      pick(Model<K, V> & Bool, eq(o, expected), (TM{l, del(~K, ~V, ~cmp, k, es)}, True{}), (TM{l, es}, False{}))

def remove_if_equal(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~eq: V -> V -> Bool, m: Model<K, V>, +k: K, +expected: V) -> Model<K, V> & Bool:
  match m:
    case TM{+l, +es}:
      remove_if_at(~K, ~V, ~cmp, ~eq, l, es, k, expected, find(~K, ~V, ~cmp, k, es))

def replace_if_at(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~eq: V -> V -> Bool, +l: Nat, +es: List<&2, M.Entry<K, V>>, +k: K, +expected: V, +replacement: V, old: Maybe<&2, V>) -> Model<K, V> & Bool:
  match old:
    case None{}:
      (TM{l, es}, False{})
    case Some{o}:
      pick(Model<K, V> & Bool, eq(o, expected), (TM{l, set_val(~K, ~V, ~cmp, k, replacement, es)}, True{}), (TM{l, es}, False{}))

def replace_if_equal(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~eq: V -> V -> Bool, m: Model<K, V>, +k: K, +expected: V, +replacement: V) -> Model<K, V> & Bool:
  match m:
    case TM{+l, +es}:
      replace_if_at(~K, ~V, ~cmp, ~eq, l, es, k, expected, replacement, find(~K, ~V, ~cmp, k, es))

def clear(-K: Data, -V: Data, m: Model<K, V>) -> Model<K, V>:
  match m:
    case TM{+l, es}:
      TM{l, Nil{}}

def first_entry(-K: Data, -V: Data, m: Model<K, V>) -> Model<K, V> & Maybe<&2, M.Entry<K, V>>:
  match m:
    case TM{+l, +es}:
      (TM{l, es}, head(M.Entry<K, V>, es))

def last_entry(-K: Data, -V: Data, m: Model<K, V>) -> Model<K, V> & Maybe<&2, M.Entry<K, V>>:
  match m:
    case TM{+l, +es}:
      (TM{l, es}, last(M.Entry<K, V>, es))

def first_key(-K: Data, -V: Data, m: Model<K, V>) -> Model<K, V> & Maybe<&2, K>:
  match m:
    case TM{+l, +es}:
      (TM{l, es}, key_m(K, V, head(M.Entry<K, V>, es)))

def last_key(-K: Data, -V: Data, m: Model<K, V>) -> Model<K, V> & Maybe<&2, K>:
  match m:
    case TM{+l, +es}:
      (TM{l, es}, key_m(K, V, last(M.Entry<K, V>, es)))

# lower/floor (up False) and ceiling/higher (up True) entries
def nav_entry(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, m: Model<K, V>, +k: K, +up: Bool, +inclusive: Bool) -> Model<K, V> & Maybe<&2, M.Entry<K, V>>:
  match m:
    case TM{+l, +es}:
      (TM{l, es}, nav(~K, ~V, ~cmp, k, up, inclusive, es))

def nav_key(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, m: Model<K, V>, +k: K, +up: Bool, +inclusive: Bool) -> Model<K, V> & Maybe<&2, K>:
  match m:
    case TM{+l, +es}:
      (TM{l, es}, key_m(K, V, nav(~K, ~V, ~cmp, k, up, inclusive, es)))

def poll_first_entry(-K: Data, -V: Data, m: Model<K, V>) -> Model<K, V> & Maybe<&2, M.Entry<K, V>>:
  match m:
    case TM{+l, es}:
      match es:
        case Nil{}:
          (TM{l, Nil{}}, None{})
        case Con{e, t}:
          (TM{l, t}, Some{e})

def poll_last_entry(-K: Data, -V: Data, m: Model<K, V>) -> Model<K, V> & Maybe<&2, M.Entry<K, V>>:
  match m:
    case TM{+l, +es}:
      (TM{l, C.init(M.Entry<K, V>, es)}, last(M.Entry<K, V>, es))

# ---- cursors ----


def iterator(-K: Data, -V: Data, m: Model<K, V>) -> Cursor<K, V>:
  match m:
    case TM{+l, +es}:
      CR{TM{l, es}, key_m(K, V, head(M.Entry<K, V>, es)), None{}, M.Unbounded{}, M.Unbounded{}, True{}}

def descending_iterator(-K: Data, -V: Data, m: Model<K, V>) -> Cursor<K, V>:
  match m:
    case TM{+l, +es}:
      CR{TM{l, es}, key_m(K, V, last(M.Entry<K, V>, es)), None{}, M.Unbounded{}, M.Unbounded{}, False{}}

def next_at(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +l: Nat, +es: List<&2, M.Entry<K, V>>, +current: Maybe<&2, K>, +lo: M.Bound<K>, +hi: M.Bound<K>, +forward: Bool, found: Maybe<&2, M.Entry<K, V>>) -> Cursor<K, V> & Maybe<&2, M.Entry<K, V>>:
  match found:
    case None{}:
      (CR{TM{l, es}, None{}, current, lo, hi, forward}, None{})
    case Some{M.Entry{+k, +v}}:
      pick(Cursor<K, V> & Maybe<&2, M.Entry<K, V>>, in_range(~K, ~cmp, k, lo, hi), (CR{TM{l, es}, succ(~K, ~V, ~cmp, k, forward, es), Some{k}, lo, hi, forward}, Some{M.Entry{k, v}}), (CR{TM{l, es}, None{}, current, lo, hi, forward}, None{}))

def iterator_next(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, c: Cursor<K, V>) -> Cursor<K, V> & Maybe<&2, M.Entry<K, V>>:
  match c:
    case CR{TM{+l, +es}, next, +current, +lo, +hi, +forward}:
      match next:
        case None{}:
          (CR{TM{l, es}, None{}, current, lo, hi, forward}, None{})
        case Some{+k}:
          next_at(~K, ~V, ~cmp, l, es, current, lo, hi, forward, find_e(~K, ~V, ~cmp, k, es))

def iterator_has_next(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, c: Cursor<K, V>) -> Cursor<K, V> & Bool:
  match c:
    case CR{m, next, current, +lo, +hi, forward}:
      match next:
        case None{}:
          (CR{m, None{}, current, lo, hi, forward}, False{})
        case Some{+k}:
          (CR{m, Some{k}, current, lo, hi, forward}, in_range(~K, ~cmp, k, lo, hi))

def set_value_at(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +l: Nat, +es: List<&2, M.Entry<K, V>>, next: Maybe<&2, K>, +k: K, lo: M.Bound<K>, hi: M.Bound<K>, +forward: Bool, +v: V, old: Maybe<&2, V>) -> Cursor<K, V> & Result<&2, &2, M.Error, V>:
  match old:
    case None{}:
      (CR{TM{l, es}, next, Some{k}, lo, hi, forward}, Fail{M.NoCurrent{}})
    case Some{o}:
      (CR{TM{l, set_val(~K, ~V, ~cmp, k, v, es)}, next, Some{k}, lo, hi, forward}, Done{o})

def iterator_set_value(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, c: Cursor<K, V>, +v: V) -> Cursor<K, V> & Result<&2, &2, M.Error, V>:
  match c:
    case CR{TM{+l, +es}, next, current, lo, hi, +forward}:
      match current:
        case None{}:
          (CR{TM{l, es}, next, None{}, lo, hi, forward}, Fail{M.NoCurrent{}})
        case Some{+k}:
          set_value_at(~K, ~V, ~cmp, l, es, next, k, lo, hi, forward, v, find(~K, ~V, ~cmp, k, es))

def iterator_remove(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, c: Cursor<K, V>) -> Cursor<K, V> & Maybe<&2, V>:
  match c:
    case CR{TM{+l, +es}, next, current, lo, hi, forward}:
      match current:
        case None{}:
          (CR{TM{l, es}, next, None{}, lo, hi, forward}, None{})
        case Some{+k}:
          (CR{TM{l, del(~K, ~V, ~cmp, k, es)}, next, None{}, lo, hi, forward}, find(~K, ~V, ~cmp, k, es))

def iterator_finish(-K: Data, -V: Data, c: Cursor<K, V>) -> Model<K, V>:
  match c:
    case CR{m, next, current, lo, hi, forward}:
      m

def key_result(-K: Data, -V: Data, r: Cursor<K, V> & Maybe<&2, M.Entry<K, V>>) -> Cursor<K, V> & Maybe<&2, K>:
  match r:
    case Tuple{c2, m}:
      (c2, key_m(K, V, m))

def value_result(-K: Data, -V: Data, r: Cursor<K, V> & Maybe<&2, M.Entry<K, V>>) -> Cursor<K, V> & Maybe<&2, V>:
  match r:
    case Tuple{c2, m}:
      (c2, val_m(K, V, m))

def iterator_next_key(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, c: Cursor<K, V>) -> Cursor<K, V> & Maybe<&2, K>:
  key_result(K, V, iterator_next(~K, ~V, ~cmp, c))

def iterator_next_value(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, c: Cursor<K, V>) -> Cursor<K, V> & Maybe<&2, V>:
  value_result(K, V, iterator_next(~K, ~V, ~cmp, c))

# ---- views ----


def view_checked(-K: Data, -V: Data, m: Model<K, V>, lo: M.Bound<K>, hi: M.Bound<K>, valid: Bool) -> Result<&1, &1, InvalidView<K, V>, View<K, V>>:
  match valid:
    case True{}:
      Done{VW{m, lo, hi, False{}}}
    case False{}:
      Fail{IV{m, M.InvalidBounds{}}}

def sub_map(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, m: Model<K, V>, +lo: M.Bound<K>, +hi: M.Bound<K>) -> Result<&1, &1, InvalidView<K, V>, View<K, V>>:
  view_checked(K, V, m, lo, hi, bounds_valid(~K, ~cmp, lo, hi))

def head_map(-K: Data, -V: Data, m: Model<K, V>, hi: M.Bound<K>) -> View<K, V>:
  VW{m, M.Unbounded{}, hi, False{}}

def tail_map(-K: Data, -V: Data, m: Model<K, V>, lo: M.Bound<K>) -> View<K, V>:
  VW{m, lo, M.Unbounded{}, False{}}

def descending_map(-K: Data, -V: Data, m: Model<K, V>) -> View<K, V>:
  VW{m, M.Unbounded{}, M.Unbounded{}, True{}}

def view_reverse(-K: Data, -V: Data, w: View<K, V>) -> View<K, V>:
  match w:
    case VW{m, lo, hi, +d}:
      VW{m, lo, hi, Bool.not(d)}

def view_finish(-K: Data, -V: Data, w: View<K, V>) -> Model<K, V>:
  match w:
    case VW{m, lo, hi, d}:
      m

def view_get(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, w: View<K, V>, +k: K) -> View<K, V> & Maybe<&2, V>:
  match w:
    case VW{TM{+l, +es}, +lo, +hi, +d}:
      (VW{TM{l, es}, lo, hi, d}, pick(Maybe<&2, V>, in_range(~K, ~cmp, k, lo, hi), find(~K, ~V, ~cmp, k, es), None{}))

def contained(-K: Data, -V: Data, r: View<K, V> & Maybe<&2, V>) -> View<K, V> & Bool:
  match r:
    case Tuple{w2, m}:
      (w2, is_some(V, m))

def view_contains_key(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, w: View<K, V>, +k: K) -> View<K, V> & Bool:
  contained(K, V, view_get(~K, ~V, ~cmp, w, k))

def rewrap_put(-K: Data, -V: Data, lo: M.Bound<K>, hi: M.Bound<K>, +d: Bool, r: Model<K, V> & Result<&2, &2, M.Rejected<K, V>, Maybe<&2, V>>) -> View<K, V> & Result<&2, &2, M.Rejected<K, V>, Maybe<&2, V>>:
  match r:
    case Tuple{m2, x}:
      (VW{m2, lo, hi, d}, x)

def view_put_at(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, m: Model<K, V>, +k: K, +v: V, lo: M.Bound<K>, hi: M.Bound<K>, +d: Bool, valid: Bool) -> View<K, V> & Result<&2, &2, M.Rejected<K, V>, Maybe<&2, V>>:
  match valid:
    case True{}:
      rewrap_put(K, V, lo, hi, d, put(~K, ~V, ~cmp, m, k, v))
    case False{}:
      (VW{m, lo, hi, d}, Fail{M.Rejected{M.OutOfRange{}, k, v}})

def view_put(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, w: View<K, V>, +k: K, +v: V) -> View<K, V> & Result<&2, &2, M.Rejected<K, V>, Maybe<&2, V>>:
  match w:
    case VW{m, +lo, +hi, +d}:
      view_put_at(~K, ~V, ~cmp, m, k, v, lo, hi, d, in_range(~K, ~cmp, k, lo, hi))

def rewrap_val(-K: Data, -V: Data, lo: M.Bound<K>, hi: M.Bound<K>, +d: Bool, r: Model<K, V> & Maybe<&2, V>) -> View<K, V> & Maybe<&2, V>:
  match r:
    case Tuple{m2, x}:
      (VW{m2, lo, hi, d}, x)

def view_remove_at(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, m: Model<K, V>, +k: K, lo: M.Bound<K>, hi: M.Bound<K>, +d: Bool, valid: Bool) -> View<K, V> & Maybe<&2, V>:
  match valid:
    case True{}:
      rewrap_val(K, V, lo, hi, d, remove(~K, ~V, ~cmp, m, k))
    case False{}:
      (VW{m, lo, hi, d}, None{})

def view_remove(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, w: View<K, V>, +k: K) -> View<K, V> & Maybe<&2, V>:
  match w:
    case VW{m, +lo, +hi, +d}:
      view_remove_at(~K, ~V, ~cmp, m, k, lo, hi, d, in_range(~K, ~cmp, k, lo, hi))

def view_size(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, w: View<K, V>) -> View<K, V> & Nat:
  match w:
    case VW{TM{+l, +es}, +lo, +hi, +d}:
      (VW{TM{l, es}, lo, hi, d}, C.length(M.Entry<K, V>, within(~K, ~V, ~cmp, lo, hi, es)))

def view_clear(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, w: View<K, V>) -> View<K, V>:
  match w:
    case VW{TM{+l, +es}, +lo, +hi, +d}:
      VW{TM{l, outside(~K, ~V, ~cmp, lo, hi, es)}, lo, hi, d}

# the view's first (or last) entry in its own direction
def view_extreme(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, w: View<K, V>, +first: Bool) -> View<K, V> & Maybe<&2, M.Entry<K, V>>:
  match w:
    case VW{TM{+l, +es}, +lo, +hi, +d}:
      (VW{TM{l, es}, lo, hi, d}, pick(Maybe<&2, M.Entry<K, V>>, pick(Bool, d, Bool.not(first), first), head(M.Entry<K, V>, within(~K, ~V, ~cmp, lo, hi, es)), last(M.Entry<K, V>, within(~K, ~V, ~cmp, lo, hi, es))))

def view_first_entry(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, w: View<K, V>) -> View<K, V> & Maybe<&2, M.Entry<K, V>>:
  view_extreme(~K, ~V, ~cmp, w, True{})

def view_last_entry(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, w: View<K, V>) -> View<K, V> & Maybe<&2, M.Entry<K, V>>:
  view_extreme(~K, ~V, ~cmp, w, False{})

# the view's lower/floor (higher False) or ceiling/higher (higher True)
# entry, in the view's own direction
def view_nav(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, w: View<K, V>, +k: K, +higher: Bool, +inclusive: Bool) -> View<K, V> & Maybe<&2, M.Entry<K, V>>:
  match w:
    case VW{TM{+l, +es}, +lo, +hi, +d}:
      (VW{TM{l, es}, lo, hi, d}, nav(~K, ~V, ~cmp, k, pick(Bool, d, Bool.not(higher), higher), inclusive, within(~K, ~V, ~cmp, lo, hi, es)))

def view_iterator(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, w: View<K, V>) -> Cursor<K, V>:
  match w:
    case VW{TM{+l, +es}, +lo, +hi, +d}:
      CR{TM{l, es}, start(~K, ~V, ~cmp, pick(M.Bound<K>, d, hi, lo), Bool.not(d), es), None{}, lo, hi, Bool.not(d)}
