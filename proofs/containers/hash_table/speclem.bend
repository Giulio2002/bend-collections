import Base
import ../../lib/logic.bend as L
import ./spec.bend as S
import ./keys.bend as K

# Facts about the specification's association-list map.

def pick_t(~A: Data, +c: Bool, +h: {c == True{} : Bool}, +x: A, +y: A) -> {Bool.pick(A, c, x, y) == x : A}:
  match c:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({Bool.pick(A, False{}, x, y) == x : A}, L.false_true(h))

def pick_f(~A: Data, +c: Bool, +h: {c == False{} : Bool}, +x: A, +y: A) -> {Bool.pick(A, c, x, y) == y : A}:
  match c:
    case True{}:
      Empty.absurd({Bool.pick(A, True{}, x, y) == y : A}, L.true_false(h))
    case False{}:
      {==}

# two keys equal to the same key are equal to each other, by str_eq
def eq_tr(+a: String, +b: String, +c: String, +hab: {S.str_eq(a, b) == True{} : Bool}, +e: Bool, +he: {S.str_eq(b, c) == e : Bool}) -> {S.str_eq(a, c) == e : Bool}:
  L.subst(String, z => {S.str_eq(z, c) == e : Bool}, b, a, Equal.sym(String, a, b, K.str_eq_of(a, b, hab)), he)

# comparing with keys equal by str_eq agrees
def eq_tr2(+j: String, +key: String, +q: String, +hq: {S.str_eq(key, q) == True{} : Bool}) -> {S.str_eq(j, key) == S.str_eq(j, q) : Bool}:
  Equal.cong(String, Bool, z => S.str_eq(j, z), key, q, K.str_eq_of(key, q, hq))

# ---- set ----

def ls_same_c(~V: Data, +j: String, +v: V, +t: List<&2, S.Entry<V>>, +key: String, +x: V, +q: String, +hq: {S.str_eq(key, q) == True{} : Bool}, +c: Bool, +hc: {S.str_eq(j, key) == c : Bool}, rec: @hc2: {S.str_eq(j, key) == False{} : Bool} -> {S.lookup(~V, S.set(~V, t, key, x), q) == Some{x} : Maybe<&2, V>}) -> {S.lookup(~V, Bool.pick(List<&2, S.Entry<V>>, c, Con{S.E{key, x}, t}, Con{S.E{j, v}, S.set(~V, t, key, x)}), q) == Some{x} : Maybe<&2, V>}:
  match c:
    case True{}:
      pick_t(~Maybe<&2, V>, S.str_eq(key, q), hq, Some{x}, S.lookup(~V, t, q))
    case False{}:
      +jq = eq_tr(q, key, j, K.str_eq_true(q, key, Equal.sym(String, key, q, K.str_eq_of(key, q, hq))), False{}, Equal.trans(Bool, S.str_eq(key, j), S.str_eq(j, key), False{}, K.str_sym(key, j), hc))
      +jq2 = Equal.trans(Bool, S.str_eq(j, q), S.str_eq(q, j), False{}, K.str_sym(j, q), jq)
      Equal.trans(Maybe<&2, V>, Bool.pick(Maybe<&2, V>, S.str_eq(j, q), Some{v}, S.lookup(~V, S.set(~V, t, key, x), q)), S.lookup(~V, S.set(~V, t, key, x), q), Some{x}, pick_f(~Maybe<&2, V>, S.str_eq(j, q), jq2, Some{v}, S.lookup(~V, S.set(~V, t, key, x), q)), rec(hc))

# looking up the key just set (or any key equal to it)
def lookup_set_same(~V: Data, +m: List<&2, S.Entry<V>>, +key: String, +x: V, +q: String, +hq: {S.str_eq(key, q) == True{} : Bool}) -> {S.lookup(~V, S.set(~V, m, key, x), q) == Some{x} : Maybe<&2, V>}:
  match m:
    case Nil{}:
      pick_t(~Maybe<&2, V>, S.str_eq(key, q), hq, Some{x}, None{})
    case Con{S.E{+j, +v}, +t}:
      ls_same_c(~V, j, v, t, key, x, q, hq, S.str_eq(j, key), {==}, hc2 => lookup_set_same(~V, t, key, x, q, hq))

def ls_other_c(~V: Data, +j: String, +v: V, +t: List<&2, S.Entry<V>>, +key: String, +x: V, +q: String, +hq: {S.str_eq(key, q) == False{} : Bool}, +c: Bool, +hc: {S.str_eq(j, key) == c : Bool}, +ih: {S.lookup(~V, S.set(~V, t, key, x), q) == S.lookup(~V, t, q) : Maybe<&2, V>}) -> {S.lookup(~V, Bool.pick(List<&2, S.Entry<V>>, c, Con{S.E{key, x}, t}, Con{S.E{j, v}, S.set(~V, t, key, x)}), q) == Bool.pick(Maybe<&2, V>, S.str_eq(j, q), Some{v}, S.lookup(~V, t, q)) : Maybe<&2, V>}:
  match c:
    case True{}:
      +jq = eq_tr(j, key, q, hc, False{}, hq)
      Equal.trans(Maybe<&2, V>, Bool.pick(Maybe<&2, V>, S.str_eq(key, q), Some{x}, S.lookup(~V, t, q)), S.lookup(~V, t, q), Bool.pick(Maybe<&2, V>, S.str_eq(j, q), Some{v}, S.lookup(~V, t, q)), pick_f(~Maybe<&2, V>, S.str_eq(key, q), hq, Some{x}, S.lookup(~V, t, q)), Equal.sym(Maybe<&2, V>, Bool.pick(Maybe<&2, V>, S.str_eq(j, q), Some{v}, S.lookup(~V, t, q)), S.lookup(~V, t, q), pick_f(~Maybe<&2, V>, S.str_eq(j, q), jq, Some{v}, S.lookup(~V, t, q))))
    case False{}:
      Equal.cong(Maybe<&2, V>, Maybe<&2, V>, z => Bool.pick(Maybe<&2, V>, S.str_eq(j, q), Some{v}, z), S.lookup(~V, S.set(~V, t, key, x), q), S.lookup(~V, t, q), ih)

# setting key leaves every other key's lookup
def lookup_set_other(~V: Data, +m: List<&2, S.Entry<V>>, +key: String, +x: V, +q: String, +hq: {S.str_eq(key, q) == False{} : Bool}) -> {S.lookup(~V, S.set(~V, m, key, x), q) == S.lookup(~V, m, q) : Maybe<&2, V>}:
  match m:
    case Nil{}:
      pick_f(~Maybe<&2, V>, S.str_eq(key, q), hq, Some{x}, None{})
    case Con{S.E{+j, +v}, +t}:
      ls_other_c(~V, j, v, t, key, x, q, hq, S.str_eq(j, key), {==}, lookup_set_other(~V, t, key, x, q, hq))

def lr_other_c(~V: Data, +j: String, +v: V, +t: List<&2, S.Entry<V>>, +key: String, +q: String, +hq: {S.str_eq(key, q) == False{} : Bool}, +c: Bool, +hc: {S.str_eq(j, key) == c : Bool}, +ih: {S.lookup(~V, S.remove(~V, t, key), q) == S.lookup(~V, t, q) : Maybe<&2, V>}) -> {S.lookup(~V, Bool.pick(List<&2, S.Entry<V>>, c, t, Con{S.E{j, v}, S.remove(~V, t, key)}), q) == Bool.pick(Maybe<&2, V>, S.str_eq(j, q), Some{v}, S.lookup(~V, t, q)) : Maybe<&2, V>}:
  match c:
    case True{}:
      Equal.sym(Maybe<&2, V>, Bool.pick(Maybe<&2, V>, S.str_eq(j, q), Some{v}, S.lookup(~V, t, q)), S.lookup(~V, t, q), pick_f(~Maybe<&2, V>, S.str_eq(j, q), eq_tr(j, key, q, hc, False{}, hq), Some{v}, S.lookup(~V, t, q)))
    case False{}:
      Equal.cong(Maybe<&2, V>, Maybe<&2, V>, z => Bool.pick(Maybe<&2, V>, S.str_eq(j, q), Some{v}, z), S.lookup(~V, S.remove(~V, t, key), q), S.lookup(~V, t, q), ih)

# removing key leaves every other key's lookup
def lookup_remove_other(~V: Data, +m: List<&2, S.Entry<V>>, +key: String, +q: String, +hq: {S.str_eq(key, q) == False{} : Bool}) -> {S.lookup(~V, S.remove(~V, m, key), q) == S.lookup(~V, m, q) : Maybe<&2, V>}:
  match m:
    case Nil{}:
      {==}
    case Con{S.E{+j, +v}, +t}:
      lr_other_c(~V, j, v, t, key, q, hq, S.str_eq(j, key), {==}, lookup_remove_other(~V, t, key, q, hq))

def or_false_l(+a: Bool, +b: Bool, +h: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, L.true_false(h))
    case False{}:
      {==}

def or_false_r(+a: Bool, +b: Bool, +h: {Bool.or(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({b == False{} : Bool}, L.true_false(h))
    case False{}:
      h

# a key not among the keys has no value
def lookup_not_mem(~V: Data, +m: List<&2, S.Entry<V>>, +q: String, +h: {S.mem(q, S.keys(~V, m)) == False{} : Bool}) -> {S.lookup(~V, m, q) == None{} : Maybe<&2, V>}:
  match m:
    case Nil{}:
      {==}
    case Con{S.E{+j, +v}, +t}:
      Equal.trans(Maybe<&2, V>, Bool.pick(Maybe<&2, V>, S.str_eq(j, q), Some{v}, S.lookup(~V, t, q)), S.lookup(~V, t, q), None{}, pick_f(~Maybe<&2, V>, S.str_eq(j, q), or_false_l(S.str_eq(j, q), S.mem(q, S.keys(~V, t)), h), Some{v}, S.lookup(~V, t, q)), lookup_not_mem(~V, t, q, or_false_r(S.str_eq(j, q), S.mem(q, S.keys(~V, t)), h)))

def lr_same_c(~V: Data, +j: String, +v: V, +t: List<&2, S.Entry<V>>, +key: String, +q: String, +hq: {S.str_eq(key, q) == True{} : Bool}, +hnm: {Bool.not(S.mem(j, S.keys(~V, t))) == True{} : Bool}, +c: Bool, +hc: {S.str_eq(j, key) == c : Bool}, rec: @hc2: {S.str_eq(j, key) == False{} : Bool} -> {S.lookup(~V, S.remove(~V, t, key), q) == None{} : Maybe<&2, V>}) -> {S.lookup(~V, Bool.pick(List<&2, S.Entry<V>>, c, t, Con{S.E{j, v}, S.remove(~V, t, key)}), q) == None{} : Maybe<&2, V>}:
  match c:
    case True{}:
      +ejq = K.str_eq_of(j, q, eq_tr(j, key, q, hc, True{}, hq))
      lookup_not_mem(~V, t, q, L.subst(String, z => {S.mem(z, S.keys(~V, t)) == False{} : Bool}, j, q, ejq, K.not_true_eq(S.mem(j, S.keys(~V, t)), hnm)))
    case False{}:
      +jq = Equal.trans(Bool, S.str_eq(j, q), S.str_eq(j, key), False{}, Equal.sym(Bool, S.str_eq(j, key), S.str_eq(j, q), eq_tr2(j, key, q, hq)), hc)
      Equal.trans(Maybe<&2, V>, Bool.pick(Maybe<&2, V>, S.str_eq(j, q), Some{v}, S.lookup(~V, S.remove(~V, t, key), q)), S.lookup(~V, S.remove(~V, t, key), q), None{}, pick_f(~Maybe<&2, V>, S.str_eq(j, q), jq, Some{v}, S.lookup(~V, S.remove(~V, t, key), q)), rec(hc))

# with keys unique, a removed key has no value
def lookup_remove_same(~V: Data, +m: List<&2, S.Entry<V>>, +key: String, +q: String, +hq: {S.str_eq(key, q) == True{} : Bool}, +hnd: {S.nodup(S.keys(~V, m)) == True{} : Bool}) -> {S.lookup(~V, S.remove(~V, m, key), q) == None{} : Maybe<&2, V>}:
  match m:
    case Nil{}:
      {==}
    case Con{S.E{+j, +v}, +t}:
      lr_same_c(~V, j, v, t, key, q, hq, L.and_left(Bool.not(S.mem(j, S.keys(~V, t))), S.nodup(S.keys(~V, t)), hnd), S.str_eq(j, key), {==}, hc2 => lookup_remove_same(~V, t, key, q, hq, L.and_right(Bool.not(S.mem(j, S.keys(~V, t))), S.nodup(S.keys(~V, t)), hnd)))

# ---- sizes ----

def none_pick(~V: Data, +c: Bool, +v: V, +r: Maybe<&2, V>, +h: {Bool.pick(Maybe<&2, V>, c, Some{v}, r) == None{} : Maybe<&2, V>}) -> {c == False{} : Bool} & {r == None{} : Maybe<&2, V>}:
  match c:
    case True{}:
      Empty.absurd({True{} == False{} : Bool} & {r == None{} : Maybe<&2, V>}, L.none_some(V, v, Equal.sym(Maybe<&2, V>, Some{v}, None{}, h)))
    case False{}:
      ({==}, h)

def ssn_c(~V: Data, +j: String, +v: V, +t: List<&2, S.Entry<V>>, +key: String, +x: V, +c: Bool, +hc: {c == False{} : Bool}, +ih: {S.size(~V, S.set(~V, t, key, x)) == 1n+S.size(~V, t) : Nat}) -> {S.size(~V, Bool.pick(List<&2, S.Entry<V>>, c, Con{S.E{key, x}, t}, Con{S.E{j, v}, S.set(~V, t, key, x)})) == 2n+S.size(~V, t) : Nat}:
  match c:
    case True{}:
      Empty.absurd({S.size(~V, Con{S.E{key, x}, t}) == 2n+S.size(~V, t) : Nat}, L.true_false(hc))
    case False{}:
      Equal.cong(Nat, Nat, z => 1n+z, S.size(~V, S.set(~V, t, key, x)), 1n+S.size(~V, t), ih)

# setting an absent key adds one entry
def size_set_new(~V: Data, +m: List<&2, S.Entry<V>>, +key: String, +x: V, +h: {S.lookup(~V, m, key) == None{} : Maybe<&2, V>}) -> {S.size(~V, S.set(~V, m, key, x)) == 1n+S.size(~V, m) : Nat}:
  match m:
    case Nil{}:
      {==}
    case Con{S.E{+j, +v}, +t}:
      +c0 = Pair.fst({S.str_eq(j, key) == False{} : Bool}, {S.lookup(~V, t, key) == None{} : Maybe<&2, V>}, none_pick(~V, S.str_eq(j, key), v, S.lookup(~V, t, key), h))
      +r0 = Pair.snd({S.str_eq(j, key) == False{} : Bool}, {S.lookup(~V, t, key) == None{} : Maybe<&2, V>}, none_pick(~V, S.str_eq(j, key), v, S.lookup(~V, t, key), h))
      ssn_c(~V, j, v, t, key, x, S.str_eq(j, key), c0, size_set_new(~V, t, key, x, r0))

def sso_c(~V: Data, +j: String, +v: V, +t: List<&2, S.Entry<V>>, +key: String, +x: V, +v0: V, +c: Bool, +h: {Bool.pick(Maybe<&2, V>, c, Some{v}, S.lookup(~V, t, key)) == Some{v0} : Maybe<&2, V>}, rec: @h2: {S.lookup(~V, t, key) == Some{v0} : Maybe<&2, V>} -> {S.size(~V, S.set(~V, t, key, x)) == S.size(~V, t) : Nat}) -> {S.size(~V, Bool.pick(List<&2, S.Entry<V>>, c, Con{S.E{key, x}, t}, Con{S.E{j, v}, S.set(~V, t, key, x)})) == 1n+S.size(~V, t) : Nat}:
  match c:
    case True{}:
      {==}
    case False{}:
      Equal.cong(Nat, Nat, z => 1n+z, S.size(~V, S.set(~V, t, key, x)), S.size(~V, t), rec(h))

# setting a present key keeps the size
def size_set_old(~V: Data, +m: List<&2, S.Entry<V>>, +key: String, +x: V, +v0: V, +h: {S.lookup(~V, m, key) == Some{v0} : Maybe<&2, V>}) -> {S.size(~V, S.set(~V, m, key, x)) == S.size(~V, m) : Nat}:
  match m:
    case Nil{}:
      Empty.absurd({S.size(~V, S.set(~V, Nil{}, key, x)) == S.size(~V, Nil{}) : Nat}, L.none_some(V, v0, h))
    case Con{S.E{+j, +v}, +t}:
      sso_c(~V, j, v, t, key, x, v0, S.str_eq(j, key), h, h2 => size_set_old(~V, t, key, x, v0, h2))

def sro_c(~V: Data, +j: String, +v: V, +t: List<&2, S.Entry<V>>, +key: String, +v0: V, +c: Bool, +h: {Bool.pick(Maybe<&2, V>, c, Some{v}, S.lookup(~V, t, key)) == Some{v0} : Maybe<&2, V>}, rec: @h2: {S.lookup(~V, t, key) == Some{v0} : Maybe<&2, V>} -> {1n+S.size(~V, S.remove(~V, t, key)) == S.size(~V, t) : Nat}) -> {1n+S.size(~V, Bool.pick(List<&2, S.Entry<V>>, c, t, Con{S.E{j, v}, S.remove(~V, t, key)})) == 1n+S.size(~V, t) : Nat}:
  match c:
    case True{}:
      {==}
    case False{}:
      Equal.cong(Nat, Nat, z => 1n+z, 1n+S.size(~V, S.remove(~V, t, key)), S.size(~V, t), rec(h))

# removing a present key drops one entry
def size_remove_old(~V: Data, +m: List<&2, S.Entry<V>>, +key: String, +v0: V, +h: {S.lookup(~V, m, key) == Some{v0} : Maybe<&2, V>}) -> {1n+S.size(~V, S.remove(~V, m, key)) == S.size(~V, m) : Nat}:
  match m:
    case Nil{}:
      Empty.absurd({1n+S.size(~V, S.remove(~V, Nil{}, key)) == S.size(~V, Nil{}) : Nat}, L.none_some(V, v0, h))
    case Con{S.E{+j, +v}, +t}:
      sro_c(~V, j, v, t, key, v0, S.str_eq(j, key), h, h2 => size_remove_old(~V, t, key, v0, h2))

def rn_c(~V: Data, +j: String, +v: V, +t: List<&2, S.Entry<V>>, +key: String, +c: Bool, +hc: {c == False{} : Bool}, +ih: {S.remove(~V, t, key) == t : List<&2, S.Entry<V>>}) -> {Bool.pick(List<&2, S.Entry<V>>, c, t, Con{S.E{j, v}, S.remove(~V, t, key)}) == Con{S.E{j, v}, t} : List<&2, S.Entry<V>>}:
  match c:
    case True{}:
      Empty.absurd({t == Con{S.E{j, v}, t} : List<&2, S.Entry<V>>}, L.true_false(hc))
    case False{}:
      Equal.cong(List<&2, S.Entry<V>>, List<&2, S.Entry<V>>, z => Con{S.E{j, v}, z}, S.remove(~V, t, key), t, ih)

# removing an absent key changes nothing
def remove_none(~V: Data, +m: List<&2, S.Entry<V>>, +key: String, +h: {S.lookup(~V, m, key) == None{} : Maybe<&2, V>}) -> {S.remove(~V, m, key) == m : List<&2, S.Entry<V>>}:
  match m:
    case Nil{}:
      {==}
    case Con{S.E{+j, +v}, +t}:
      +c0 = Pair.fst({S.str_eq(j, key) == False{} : Bool}, {S.lookup(~V, t, key) == None{} : Maybe<&2, V>}, none_pick(~V, S.str_eq(j, key), v, S.lookup(~V, t, key), h))
      +r0 = Pair.snd({S.str_eq(j, key) == False{} : Bool}, {S.lookup(~V, t, key) == None{} : Maybe<&2, V>}, none_pick(~V, S.str_eq(j, key), v, S.lookup(~V, t, key), h))
      rn_c(~V, j, v, t, key, S.str_eq(j, key), c0, remove_none(~V, t, key, r0))
