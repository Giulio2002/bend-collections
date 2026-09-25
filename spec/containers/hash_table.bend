import Base
import ../lib/common.bend as SC
import ../../src/containers/hash_table.bend as H

# Independent model: a map from String keys to values is an association
# list with at most one entry per key. Nothing here refers to buckets,
# hashing, probing or slots.

type Entry<-V: Data> is Data:
  E{key: String, val: V}

def chr_eq(a: Char, b: Char) -> Bool:
  match a b:
    case Chr{x} Chr{y}:
      U32.is_eq(x, y)

def str_eq(a: String, b: String) -> Bool:
  match a b:
    case SNil{} SNil{}:
      True{}
    case SNil{} SCon{h, t}:
      False{}
    case SCon{h, t} SNil{}:
      False{}
    case SCon{x, s} SCon{y, t}:
      Bool.and(chr_eq(x, y), str_eq(s, t))

def lookup(~V: Data, m: List<&2, Entry<V>>, +k: String) -> Maybe<&2, V>:
  match m:
    case Nil{}:
      None{}
    case Con{E{+j, +v}, t}:
      Bool.pick(Maybe<&2, V>, str_eq(j, k), Some{v}, lookup(~V, t, k))

def is_some(~V: Data, m: Maybe<&2, V>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{v}:
      True{}

def has(~V: Data, m: List<&2, Entry<V>>, +k: String) -> Bool:
  is_some(~V, lookup(~V, m, k))

# Replace the entry of k in place, or add it at the end.
def set(~V: Data, m: List<&2, Entry<V>>, +k: String, +x: V) -> List<&2, Entry<V>>:
  match m:
    case Nil{}:
      Con{E{k, x}, Nil{}}
    case Con{E{+j, +v}, +t}:
      Bool.pick(List<&2, Entry<V>>, str_eq(j, k), Con{E{k, x}, t}, Con{E{j, v}, set(~V, t, k, x)})

def remove(~V: Data, m: List<&2, Entry<V>>, +k: String) -> List<&2, Entry<V>>:
  match m:
    case Nil{}:
      Nil{}
    case Con{E{+j, +v}, +t}:
      Bool.pick(List<&2, Entry<V>>, str_eq(j, k), t, Con{E{j, v}, remove(~V, t, k)})

def keys(~V: Data, m: List<&2, Entry<V>>) -> List<&2, String>:
  match m:
    case Nil{}:
      Nil{}
    case Con{E{j, v}, t}:
      Con{j, keys(~V, t)}

def size(~V: Data, m: List<&2, Entry<V>>) -> Nat:
  match m:
    case Nil{}:
      0n
    case Con{e, t}:
      1n+size(~V, t)

def mem(+k: String, ks: List<&2, String>) -> Bool:
  match ks:
    case Nil{}:
      False{}
    case Con{j, t}:
      Bool.or(str_eq(j, k), mem(k, t))

def nodup(ks: List<&2, String>) -> Bool:
  match ks:
    case Nil{}:
      True{}
    case Con{+j, +t}:
      Bool.and(Bool.not(mem(j, t)), nodup(t))

def get_m(~V: Data, dflt: V, m: Maybe<&2, V>) -> V:
  match m:
    case None{}:
      dflt
    case Some{v}:
      v

# the value of key, or dflt
def get(~V: Data, dflt: V, m: List<&2, Entry<V>>, +key: String) -> V:
  get_m(~V, dflt, lookup(~V, m, key))

# ---- contract (SPARK formal containers) ----
# Each `<Subprogram>.<clause>` definition below states one Post clause of
# that SPARK subprogram, as a proposition on this model; the table names the
# clauses. proofs/containers/hash_table/ proves every clause under its clause name,
# and its `impl` lemma carries them to the implementation.
#
# Contracts of the hash map in the style of SPARK's formal hashed maps
# (SPARKlib spark-containers-formal-hashed_maps.ads). The proofs in
# set/pop/keysw.bend relate every operation to the specification's
# association list; this module states, per operation, what changes and
# what is preserved, over three views of a map sh:
#   Model   S.lookup(ST.model(sh), q)  the value of every key q
#   Length  S.size(ST.model(sh))
#   Keys    S.keys(ST.model(sh))       the keys, in iteration order
# Keys are compared by S.str_eq, which is an equivalence under which equal
# keys are identical strings (so, like SPARK's Equivalent_Keys, every
# function of a key, the hash included, agrees on equivalent keys).
# SPARK's cursor model (Positions) has no counterpart: the map has no
# cursors.
#
#   SPARK subprogram (hashed_maps.ads line, AdaCore/SPARKlib master)   ours   lemmas
#   Empty_Map (103)                   new     new_model, new_length, new_absent
#   Length (117)                      size    length_value, length_frame (P.size_ok)
#   Element (Key) (1039)              get     element_value, element_default (P.get_ok)
#   Contains (1032)                   has     contains_value (P.has_ok)
#   Include (729)                     set     SetContract / SetPost (set_post)
#   Delete (Key) (891), Exclude (851) pop, del  PopContract, DelContract / DelPost
#   Iter_Model / Keys (1078)          keys    KeysContract / KeysPost
#   Equivalent_Keys                   str_eq  key_refl, key_sym, key_trans, key_same, key_respect
# Not in this API: "=", Capacity, Reserve_Capacity, Is_Empty, Clear,
# Assign/Copy/Move, Replace_Element/Reference (by cursor), Insert (fails
# if present) and Replace (fails if absent), which Include subsumes,
# First/Next/Has_Element/Key (cursors), Find, Default_Modulus.

# ---- keys ----
# The key sequence (SPARK's Keys): no key twice, as long as the map, and
# holding exactly the keys the model has.
def KeysPost(~V: Data, m: List<&2, Entry<V>>) -> Type:
  {nodup(keys(~V, m)) == True{} : Bool} & ({SC.length(String, keys(~V, m)) == size(~V, m) : Nat} & (@+q: String -> {mem(q, keys(~V, m)) == has(~V, m, q) : Bool}))

# ---- set (SPARK's Include: insert, or replace the value) ----
def SetPost(~V: Data, m: List<&2, Entry<V>>, m2: List<&2, Entry<V>>, key: String, x: V) -> Type:
  {has(~V, m2, key) == True{} : Bool} & ((@+q: String -> @+hq: {str_eq(key, q) == True{} : Bool} -> {lookup(~V, m2, q) == Some{x} : Maybe<&2, V>}) & ((@+q: String -> @+hq: {str_eq(key, q) == False{} : Bool} -> {lookup(~V, m2, q) == lookup(~V, m, q) : Maybe<&2, V>}) & ({size(~V, m2) == Bool.pick(Nat, has(~V, m, key), size(~V, m), 1n+size(~V, m)) : Nat} & ((@+q: String -> {mem(q, keys(~V, m2)) == Bool.or(str_eq(key, q), mem(q, keys(~V, m))) : Bool}) & ({nodup(keys(~V, m2)) == True{} : Bool} & (@+hp: {has(~V, m, key) == True{} : Bool} -> {keys(~V, m2) == keys(~V, m) : List<&2, String>}))))))

# ---- pop and del (SPARK's Delete/Exclude) ----
def DelPost(~V: Data, m: List<&2, Entry<V>>, m2: List<&2, Entry<V>>, key: String) -> Type:
  {has(~V, m2, key) == False{} : Bool} & ((@+q: String -> @+hq: {str_eq(key, q) == False{} : Bool} -> {lookup(~V, m2, q) == lookup(~V, m, q) : Maybe<&2, V>}) & ((@+hn: {has(~V, m, key) == False{} : Bool} -> @+q: String -> {lookup(~V, m2, q) == lookup(~V, m, q) : Maybe<&2, V>}) & ({Bool.pick(Nat, has(~V, m, key), 1n+size(~V, m2), size(~V, m2)) == size(~V, m) : Nat} & ((@+q: String -> {mem(q, keys(~V, m2)) == Bool.and(Bool.not(str_eq(key, q)), mem(q, keys(~V, m))) : Bool}) & {nodup(keys(~V, m2)) == True{} : Bool}))))

# Equivalent_Keys
def Equivalent_Keys.key_refl(+a: String) -> Type:
  {str_eq(a, a) == True{} : Bool}

# Equivalent_Keys
def Equivalent_Keys.key_sym(+a: String, +b: String) -> Type:
  {str_eq(a, b) == str_eq(b, a) : Bool}

# Equivalent_Keys
def Equivalent_Keys.key_trans(+a: String, +b: String, +c: String, +hab: {str_eq(a, b) == True{} : Bool}, +hbc: {str_eq(b, c) == True{} : Bool}) -> Type:
  {str_eq(a, c) == True{} : Bool}

# Equivalent_Keys
def Equivalent_Keys.key_same(+a: String, +b: String, +h: {str_eq(a, b) == True{} : Bool}) -> Type:
  {a == b : String}

# Equivalent_Keys
def Equivalent_Keys.key_respect(~A: Data, ~f: String -> A, +a: String, +b: String, +h: {str_eq(a, b) == True{} : Bool}) -> Type:
  {f(a) == f(b) : A}

# Include (729)
def Include.set_post(~V: Data, ~m: List<&2, Entry<V>>, ~m2: List<&2, Entry<V>>, ~key: String, ~x: V, ~hp: (@+q: String -> {lookup(~V, m2, q) == lookup(~V, set(~V, m, key, x), q) : Maybe<&2, V>}) & {size(~V, m2) == size(~V, set(~V, m, key, x)) : Nat}, +hnd: {nodup(keys(~V, m2)) == True{} : Bool}, hk: @+hq0: {has(~V, m, key) == True{} : Bool} -> {keys(~V, m2) == keys(~V, m) : List<&2, String>}) -> Type:
  SetPost(~V, m, m2, key, x)

# The queries are stated on what they return: `r` is the value the operation
# produces on a map whose model is `m` (the proof package instantiates it with
# the implementation's result).

# Element (SPARKlib formal-hashed-maps.ads): Element (Container, Key) = Get (Model, Key)
def Element.element_value(~V: Data, m: List<&2, Entry<V>>, +key: String, +x: V, +hl: {lookup(~V, m, key) == Some{x} : Maybe<&2, V>}, r: V) -> Type:
  {r == x : V}

# Element without the key: get returns the caller's default (the Pre of
# Element is Contains; here the absent case is defined, not excluded)
def Element.element_default(~V: Data, m: List<&2, Entry<V>>, +key: String, +dflt: V, +hl: {lookup(~V, m, key) == None{} : Maybe<&2, V>}, r: V) -> Type:
  {r == dflt : V}

# Contains: Contains (Container, Key) = Has_Key (Model, Key)
def Contains.contains_value(~V: Data, m: List<&2, Entry<V>>, +key: String, r: Bool) -> Type:
  {r == is_some(~V, lookup(~V, m, key)) : Bool}

# Length: Length (Container) = M.Length (Model)
def Length.length_value(~V: Data, m: List<&2, Entry<V>>, +n: Nat) -> Type:
  {n == SC.length(String, keys(~V, m)) : Nat}

# Length is a query: the map is returned unchanged
def Length.length_frame(~V: Data, a: H.HashMap<&2, V>, b: H.HashMap<&2, V>) -> Type:
  {b == a : H.HashMap<&2, V>}

# Empty_Map: Is_Empty (Model), Length = 0, no key present
def Empty_Map.new_model(~V: Data, m: List<&2, Entry<V>>) -> Type:
  {m == Nil{} : List<&2, Entry<V>>}

def Empty_Map.new_length(~V: Data, m: List<&2, Entry<V>>) -> Type:
  {size(~V, m) == 0n : Nat}

def Empty_Map.new_absent(~V: Data, m: List<&2, Entry<V>>, +key: String) -> Type:
  {lookup(~V, m, key) == None{} : Maybe<&2, V>}
