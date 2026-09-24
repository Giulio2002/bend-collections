import Base
import ../../lib/logic.bend as L
import ../../lib/spec_common.bend as SC
import ../../lib/u32div.bend as UD
import ../../../src/containers/hash_table.bend as H
import ./spec.bend as S
import ./keys.bend as K
import ./speclem.bend as SL
import ./state.bend as ST
import ./table.bend as TB
import ./poplem.bend as PL
import ../../lib/array.bend as AR
import ./set.bend as ST2
import ./pop.bend as PO
import ./keysw.bend as KW

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

# ---- key equivalence ----

def key_refl(+a: String) -> {S.str_eq(a, a) == True{} : Bool}:
  K.str_refl(a)

def key_sym(+a: String, +b: String) -> {S.str_eq(a, b) == S.str_eq(b, a) : Bool}:
  K.str_sym(a, b)

def key_trans(+a: String, +b: String, +c: String, +hab: {S.str_eq(a, b) == True{} : Bool}, +hbc: {S.str_eq(b, c) == True{} : Bool}) -> {S.str_eq(a, c) == True{} : Bool}:
  SL.eq_tr(a, b, c, hab, True{}, hbc)

# equivalent keys are the same string
def key_same(+a: String, +b: String, +h: {S.str_eq(a, b) == True{} : Bool}) -> {a == b : String}:
  K.str_eq_of(a, b, h)

# and so every function of a key (the hash included) agrees on them
def key_respect(~A: Data, ~f: String -> A, +a: String, +b: String, +h: {S.str_eq(a, b) == True{} : Bool}) -> {f(a) == f(b) : A}:
  Equal.cong(String, A, f, a, b, K.str_eq_of(a, b, h))

# ---- facts about the specification ----

def mh_c(~V: Data, +j: String, +v: V, +t: List<&2, S.Entry<V>>, +q: String, +c: Bool, +hc: {S.str_eq(j, q) == c : Bool}, +ih: {S.mem(q, S.keys(~V, t)) == S.has(~V, t, q) : Bool}) -> {Bool.or(S.str_eq(j, q), S.mem(q, S.keys(~V, t))) == S.is_some(~V, Bool.pick(Maybe<&2, V>, S.str_eq(j, q), Some{v}, S.lookup(~V, t, q))) : Bool}:
  match c:
    case True{}:
      %Equal.sym(Bool, S.str_eq(j, q), True{}, hc) : {Bool.or(_, S.mem(q, S.keys(~V, t))) == S.is_some(~V, Bool.pick(Maybe<&2, V>, _, Some{v}, S.lookup(~V, t, q))) : Bool}
      {==}
    case False{}:
      %Equal.sym(Bool, S.str_eq(j, q), False{}, hc) : {Bool.or(_, S.mem(q, S.keys(~V, t))) == S.is_some(~V, Bool.pick(Maybe<&2, V>, _, Some{v}, S.lookup(~V, t, q))) : Bool}
      ih

# a key is in the key sequence exactly when the model has it
def mem_has(~V: Data, +m: List<&2, S.Entry<V>>, +q: String) -> {S.mem(q, S.keys(~V, m)) == S.has(~V, m, q) : Bool}:
  match m:
    case Nil{}:
      {==}
    case Con{S.E{+j, +v}, +t}:
      mh_c(~V, j, v, t, q, S.str_eq(j, q), {==}, mem_has(~V, t, q))

# the key sequence is as long as the map
def keys_len(~V: Data, +m: List<&2, S.Entry<V>>) -> {SC.length(String, S.keys(~V, m)) == S.size(~V, m) : Nat}:
  match m:
    case Nil{}:
      {==}
    case Con{S.E{+j, +v}, +t}:
      Equal.cong(Nat, Nat, z => 1n+z, SC.length(String, S.keys(~V, t)), S.size(~V, t), keys_len(~V, t))

# has is false exactly when the lookup is None
def none_of(~V: Data, +mv: Maybe<&2, V>, +h: {S.is_some(~V, mv) == False{} : Bool}) -> {mv == None{} : Maybe<&2, V>}:
  match mv:
    case None{}:
      {==}
    case Some{v}:
      Empty.absurd({Some{v} == None{} : Maybe<&2, V>}, L.true_false(h))

def ssp(~V: Data, +m: List<&2, S.Entry<V>>, +key: String, +x: V, +mv: Maybe<&2, V>, +hmv: {S.lookup(~V, m, key) == mv : Maybe<&2, V>}) -> {S.size(~V, S.set(~V, m, key, x)) == Bool.pick(Nat, S.has(~V, m, key), S.size(~V, m), 1n+S.size(~V, m)) : Nat}:
  match mv:
    case None{}:
      %Equal.sym(Maybe<&2, V>, S.lookup(~V, m, key), None{}, hmv) : {S.size(~V, S.set(~V, m, key, x)) == Bool.pick(Nat, S.is_some(~V, _), S.size(~V, m), 1n+S.size(~V, m)) : Nat}
      SL.size_set_new(~V, m, key, x, hmv)
    case Some{+v0}:
      %Equal.sym(Maybe<&2, V>, S.lookup(~V, m, key), Some{v0}, hmv) : {S.size(~V, S.set(~V, m, key, x)) == Bool.pick(Nat, S.is_some(~V, _), S.size(~V, m), 1n+S.size(~V, m)) : Nat}
      SL.size_set_old(~V, m, key, x, v0, hmv)

# set grows the map by one exactly when the key was absent
def size_set(~V: Data, +m: List<&2, S.Entry<V>>, +key: String, +x: V) -> {S.size(~V, S.set(~V, m, key, x)) == Bool.pick(Nat, S.has(~V, m, key), S.size(~V, m), 1n+S.size(~V, m)) : Nat}:
  ssp(~V, m, key, x, S.lookup(~V, m, key), {==})

def srp(~V: Data, +m: List<&2, S.Entry<V>>, +key: String, +mv: Maybe<&2, V>, +hmv: {S.lookup(~V, m, key) == mv : Maybe<&2, V>}) -> {Bool.pick(Nat, S.has(~V, m, key), 1n+S.size(~V, S.remove(~V, m, key)), S.size(~V, S.remove(~V, m, key))) == S.size(~V, m) : Nat}:
  match mv:
    case None{}:
      %Equal.sym(Maybe<&2, V>, S.lookup(~V, m, key), None{}, hmv) : {Bool.pick(Nat, S.is_some(~V, _), 1n+S.size(~V, S.remove(~V, m, key)), S.size(~V, S.remove(~V, m, key))) == S.size(~V, m) : Nat}
      Equal.cong(List<&2, S.Entry<V>>, Nat, z => S.size(~V, z), S.remove(~V, m, key), m, SL.remove_none(~V, m, key, hmv))
    case Some{+v0}:
      %Equal.sym(Maybe<&2, V>, S.lookup(~V, m, key), Some{v0}, hmv) : {Bool.pick(Nat, S.is_some(~V, _), 1n+S.size(~V, S.remove(~V, m, key)), S.size(~V, S.remove(~V, m, key))) == S.size(~V, m) : Nat}
      SL.size_remove_old(~V, m, key, v0, hmv)

# remove shrinks the map by one exactly when the key was present
def size_remove(~V: Data, +m: List<&2, S.Entry<V>>, +key: String) -> {Bool.pick(Nat, S.has(~V, m, key), 1n+S.size(~V, S.remove(~V, m, key)), S.size(~V, S.remove(~V, m, key))) == S.size(~V, m) : Nat}:
  srp(~V, m, key, S.lookup(~V, m, key), {==})

def hso_c(~V: Data, +m: List<&2, S.Entry<V>>, +key: String, +x: V, +q: String, +c: Bool, +hc: {S.str_eq(key, q) == c : Bool}) -> {S.has(~V, S.set(~V, m, key, x), q) == Bool.or(c, S.mem(q, S.keys(~V, m))) : Bool}:
  match c:
    case True{}:
      %Equal.sym(Maybe<&2, V>, S.lookup(~V, S.set(~V, m, key, x), q), Some{x}, SL.lookup_set_same(~V, m, key, x, q, hc)) : {S.is_some(~V, _) == Bool.or(True{}, S.mem(q, S.keys(~V, m))) : Bool}
      {==}
    case False{}:
      %Equal.sym(Maybe<&2, V>, S.lookup(~V, S.set(~V, m, key, x), q), S.lookup(~V, m, q), SL.lookup_set_other(~V, m, key, x, q, hc)) : {S.is_some(~V, _) == Bool.or(False{}, S.mem(q, S.keys(~V, m))) : Bool}
      Equal.sym(Bool, S.mem(q, S.keys(~V, m)), S.has(~V, m, q), mem_has(~V, m, q))

def hro_c(~V: Data, +m: List<&2, S.Entry<V>>, +key: String, +q: String, +hnd: {S.nodup(S.keys(~V, m)) == True{} : Bool}, +c: Bool, +hc: {S.str_eq(key, q) == c : Bool}) -> {S.has(~V, S.remove(~V, m, key), q) == Bool.and(Bool.not(c), S.mem(q, S.keys(~V, m))) : Bool}:
  match c:
    case True{}:
      %Equal.sym(Maybe<&2, V>, S.lookup(~V, S.remove(~V, m, key), q), None{}, SL.lookup_remove_same(~V, m, key, q, hc, hnd)) : {S.is_some(~V, _) == Bool.and(Bool.not(True{}), S.mem(q, S.keys(~V, m))) : Bool}
      {==}
    case False{}:
      %Equal.sym(Maybe<&2, V>, S.lookup(~V, S.remove(~V, m, key), q), S.lookup(~V, m, q), SL.lookup_remove_other(~V, m, key, q, hc)) : {S.is_some(~V, _) == Bool.and(Bool.not(False{}), S.mem(q, S.keys(~V, m))) : Bool}
      Equal.sym(Bool, S.mem(q, S.keys(~V, m)), S.has(~V, m, q), mem_has(~V, m, q))

# ---- the invariant keeps keys unique ----

def model_nodup(~V: Data, +sh: ST.Sh<V>, +hg: {ST.good(~V, sh) == True{} : Bool}) -> {S.nodup(S.keys(~V, ST.model(~V, sh))) == True{} : Bool}:
  match sh:
    case ST.HS{+n, +k, +td, +fresh, +sz, +sd, +sdU, +free, +tabT, +ksT, +vsT, +nxT}:
      PL.nodup_model(~V, TB.buckets(AR.slots(U32, tabT), AR.slots(String, ksT), SC.pow2(k)), AR.slots(Maybe<&2, V>, vsT), UD.v(fresh), SC.pow2(k), ST.g_clive(~V, n, k, td, fresh, sz, sd, sdU, free, tabT, AR.slots(String, ksT), AR.perfect(String, sd, ksT), vsT, nxT, hg), ST.g_cuniq(~V, n, k, td, fresh, sz, sd, sdU, free, tabT, AR.slots(String, ksT), AR.perfect(String, sd, ksT), vsT, nxT, hg))

# ---- keys ----

# The key sequence (SPARK's Keys): no key twice, as long as the map, and
# holding exactly the keys the model has.
def KeysPost(~V: Data, m: List<&2, S.Entry<V>>) -> Type:
  {S.nodup(S.keys(~V, m)) == True{} : Bool} & ({SC.length(String, S.keys(~V, m)) == S.size(~V, m) : Nat} & (@+q: String -> {S.mem(q, S.keys(~V, m)) == S.has(~V, m, q) : Bool}))

def keys_post(~V: Data, +sh: ST.Sh<V>, +hg: {ST.good(~V, sh) == True{} : Bool}) -> KeysPost(~V, ST.model(~V, sh)):
  (model_nodup(~V, sh, hg), (keys_len(~V, ST.model(~V, sh)), q => mem_has(~V, ST.model(~V, sh), q)))

# keys returns the key sequence and changes nothing
def KeysContract(~V: Data, +sh: ST.Sh<V>, r: H.HashMap<&2, V> & List<&2, String>) -> Type:
  Sigma<&1, &1, ST.Sh<V>, sh2 => {r == (ST.real(~V, sh2), S.keys(~V, ST.model(~V, sh))) : H.HashMap<&2, V> & List<&2, String>} & (({ST.good(~V, sh2) == True{} : Bool} & {ST.model(~V, sh2) == ST.model(~V, sh) : List<&2, S.Entry<V>>}) & KeysPost(~V, ST.model(~V, sh)))>

def kc_from(~V: Data, +sh: ST.Sh<V>, +hg: {ST.good(~V, sh) == True{} : Bool}, -r: H.HashMap<&2, V> & List<&2, String>, ko: KW.KeysOK(~V, sh, r)) -> KeysContract(~V, sh, r):
  match ko:
    case Tuple{+sh2, Tuple{+e, rest}}:
      (sh2, (e, (rest, keys_post(~V, sh, hg))))

# ---- set (SPARK's Include: insert, or replace the value) ----

def SetPost(~V: Data, m: List<&2, S.Entry<V>>, m2: List<&2, S.Entry<V>>, key: String, x: V) -> Type:
  {S.has(~V, m2, key) == True{} : Bool} & ((@+q: String -> @+hq: {S.str_eq(key, q) == True{} : Bool} -> {S.lookup(~V, m2, q) == Some{x} : Maybe<&2, V>}) & ((@+q: String -> @+hq: {S.str_eq(key, q) == False{} : Bool} -> {S.lookup(~V, m2, q) == S.lookup(~V, m, q) : Maybe<&2, V>}) & ({S.size(~V, m2) == Bool.pick(Nat, S.has(~V, m, key), S.size(~V, m), 1n+S.size(~V, m)) : Nat} & ((@+q: String -> {S.mem(q, S.keys(~V, m2)) == Bool.or(S.str_eq(key, q), S.mem(q, S.keys(~V, m))) : Bool}) & {S.nodup(S.keys(~V, m2)) == True{} : Bool}))))

def SetContract(~V: Data, +sh: ST.Sh<V>, +key: String, +x: V, r: H.HashMap<&2, V>) -> Type:
  Sigma<&1, &1, ST.Sh<V>, sh2 => {r == ST.real(~V, sh2) : H.HashMap<&2, V>} & ({ST.good(~V, sh2) == True{} : Bool} & SetPost(~V, ST.model(~V, sh), ST.model(~V, sh2), key, x))>

def set_same(~V: Data, +m: List<&2, S.Entry<V>>, +m2: List<&2, S.Entry<V>>, +key: String, +x: V, +q: String, +hq: {S.str_eq(key, q) == True{} : Bool}, +hl: {S.lookup(~V, m2, q) == S.lookup(~V, S.set(~V, m, key, x), q) : Maybe<&2, V>}) -> {S.lookup(~V, m2, q) == Some{x} : Maybe<&2, V>}:
  Equal.trans(Maybe<&2, V>, S.lookup(~V, m2, q), S.lookup(~V, S.set(~V, m, key, x), q), Some{x}, hl, SL.lookup_set_same(~V, m, key, x, q, hq))

def set_other(~V: Data, +m: List<&2, S.Entry<V>>, +m2: List<&2, S.Entry<V>>, +key: String, +x: V, +q: String, +hq: {S.str_eq(key, q) == False{} : Bool}, +hl: {S.lookup(~V, m2, q) == S.lookup(~V, S.set(~V, m, key, x), q) : Maybe<&2, V>}) -> {S.lookup(~V, m2, q) == S.lookup(~V, m, q) : Maybe<&2, V>}:
  Equal.trans(Maybe<&2, V>, S.lookup(~V, m2, q), S.lookup(~V, S.set(~V, m, key, x), q), S.lookup(~V, m, q), hl, SL.lookup_set_other(~V, m, key, x, q, hq))

def set_mem(~V: Data, +m: List<&2, S.Entry<V>>, +m2: List<&2, S.Entry<V>>, +key: String, +x: V, +q: String, +hl: {S.lookup(~V, m2, q) == S.lookup(~V, S.set(~V, m, key, x), q) : Maybe<&2, V>}) -> {S.mem(q, S.keys(~V, m2)) == Bool.or(S.str_eq(key, q), S.mem(q, S.keys(~V, m))) : Bool}:
  Equal.trans(Bool, S.mem(q, S.keys(~V, m2)), S.has(~V, m2, q), Bool.or(S.str_eq(key, q), S.mem(q, S.keys(~V, m))), mem_has(~V, m2, q),
    Equal.trans(Bool, S.has(~V, m2, q), S.has(~V, S.set(~V, m, key, x), q), Bool.or(S.str_eq(key, q), S.mem(q, S.keys(~V, m))), Equal.cong(Maybe<&2, V>, Bool, z => S.is_some(~V, z), S.lookup(~V, m2, q), S.lookup(~V, S.set(~V, m, key, x), q), hl), hso_c(~V, m, key, x, q, S.str_eq(key, q), {==})))

def set_post(~V: Data, ~m: List<&2, S.Entry<V>>, ~m2: List<&2, S.Entry<V>>, ~key: String, ~x: V, ~hp: (@+q: String -> {S.lookup(~V, m2, q) == S.lookup(~V, S.set(~V, m, key, x), q) : Maybe<&2, V>}) & {S.size(~V, m2) == S.size(~V, S.set(~V, m, key, x)) : Nat}, +hnd: {S.nodup(S.keys(~V, m2)) == True{} : Bool}) -> SetPost(~V, m, m2, key, x):
  (Equal.cong(Maybe<&2, V>, Bool, z => S.is_some(~V, z), S.lookup(~V, m2, key), Some{x}, set_same(~V, m, m2, key, x, key, K.str_refl(key), Pair.fst(@+q: String -> {S.lookup(~V, m2, q) == S.lookup(~V, S.set(~V, m, key, x), q) : Maybe<&2, V>}, {S.size(~V, m2) == S.size(~V, S.set(~V, m, key, x)) : Nat}, hp)(key))),
   (q => hq => set_same(~V, m, m2, key, x, q, hq, Pair.fst(@+q: String -> {S.lookup(~V, m2, q) == S.lookup(~V, S.set(~V, m, key, x), q) : Maybe<&2, V>}, {S.size(~V, m2) == S.size(~V, S.set(~V, m, key, x)) : Nat}, hp)(q)),
    (q => hq => set_other(~V, m, m2, key, x, q, hq, Pair.fst(@+q: String -> {S.lookup(~V, m2, q) == S.lookup(~V, S.set(~V, m, key, x), q) : Maybe<&2, V>}, {S.size(~V, m2) == S.size(~V, S.set(~V, m, key, x)) : Nat}, hp)(q)),
     (Equal.trans(Nat, S.size(~V, m2), S.size(~V, S.set(~V, m, key, x)), Bool.pick(Nat, S.has(~V, m, key), S.size(~V, m), 1n+S.size(~V, m)), Pair.snd(@+q: String -> {S.lookup(~V, m2, q) == S.lookup(~V, S.set(~V, m, key, x), q) : Maybe<&2, V>}, {S.size(~V, m2) == S.size(~V, S.set(~V, m, key, x)) : Nat}, hp), size_set(~V, m, key, x)),
      (q => set_mem(~V, m, m2, key, x, q, Pair.fst(@+q: String -> {S.lookup(~V, m2, q) == S.lookup(~V, S.set(~V, m, key, x), q) : Maybe<&2, V>}, {S.size(~V, m2) == S.size(~V, S.set(~V, m, key, x)) : Nat}, hp)(q)), hnd)))))

def sc_from(~V: Data, +sh: ST.Sh<V>, +key: String, +x: V, -r: H.HashMap<&2, V>, so: ST2.SetOK(~V, sh, key, x, r)) -> SetContract(~V, sh, key, x, r):
  match so:
    case Tuple{+sh2, Tuple{+e, rest}}:
      (+hg2, rest2) = rest
      (sh2, (e, (hg2, set_post(~V, ~ST.model(~V, sh), ~ST.model(~V, sh2), ~key, ~x, ~rest2, model_nodup(~V, sh2, hg2)))))

# ---- pop and del (SPARK's Delete/Exclude) ----

def DelPost(~V: Data, m: List<&2, S.Entry<V>>, m2: List<&2, S.Entry<V>>, key: String) -> Type:
  {S.has(~V, m2, key) == False{} : Bool} & ((@+q: String -> @+hq: {S.str_eq(key, q) == False{} : Bool} -> {S.lookup(~V, m2, q) == S.lookup(~V, m, q) : Maybe<&2, V>}) & ((@+hn: {S.has(~V, m, key) == False{} : Bool} -> @+q: String -> {S.lookup(~V, m2, q) == S.lookup(~V, m, q) : Maybe<&2, V>}) & ({Bool.pick(Nat, S.has(~V, m, key), 1n+S.size(~V, m2), S.size(~V, m2)) == S.size(~V, m) : Nat} & ((@+q: String -> {S.mem(q, S.keys(~V, m2)) == Bool.and(Bool.not(S.str_eq(key, q)), S.mem(q, S.keys(~V, m))) : Bool}) & {S.nodup(S.keys(~V, m2)) == True{} : Bool}))))

def PopContract(~V: Data, +sh: ST.Sh<V>, +key: String, r: H.HashMap<&2, V> & Maybe<&2, V>) -> Type:
  Sigma<&1, &1, ST.Sh<V>, sh2 => {r == (ST.real(~V, sh2), S.lookup(~V, ST.model(~V, sh), key)) : H.HashMap<&2, V> & Maybe<&2, V>} & ({ST.good(~V, sh2) == True{} : Bool} & DelPost(~V, ST.model(~V, sh), ST.model(~V, sh2), key))>

def DelContract(~V: Data, +sh: ST.Sh<V>, +key: String, r: H.HashMap<&2, V>) -> Type:
  Sigma<&1, &1, ST.Sh<V>, sh2 => {r == ST.real(~V, sh2) : H.HashMap<&2, V>} & ({ST.good(~V, sh2) == True{} : Bool} & DelPost(~V, ST.model(~V, sh), ST.model(~V, sh2), key))>

def del_absent(~V: Data, +m: List<&2, S.Entry<V>>, +m2: List<&2, S.Entry<V>>, +key: String, +hn: {S.has(~V, m, key) == False{} : Bool}, +q: String, +hl: {S.lookup(~V, m2, q) == S.lookup(~V, S.remove(~V, m, key), q) : Maybe<&2, V>}) -> {S.lookup(~V, m2, q) == S.lookup(~V, m, q) : Maybe<&2, V>}:
  Equal.trans(Maybe<&2, V>, S.lookup(~V, m2, q), S.lookup(~V, S.remove(~V, m, key), q), S.lookup(~V, m, q), hl, Equal.cong(List<&2, S.Entry<V>>, Maybe<&2, V>, z => S.lookup(~V, z, q), S.remove(~V, m, key), m, SL.remove_none(~V, m, key, none_of(~V, S.lookup(~V, m, key), hn))))

def del_other(~V: Data, +m: List<&2, S.Entry<V>>, +m2: List<&2, S.Entry<V>>, +key: String, +q: String, +hq: {S.str_eq(key, q) == False{} : Bool}, +hl: {S.lookup(~V, m2, q) == S.lookup(~V, S.remove(~V, m, key), q) : Maybe<&2, V>}) -> {S.lookup(~V, m2, q) == S.lookup(~V, m, q) : Maybe<&2, V>}:
  Equal.trans(Maybe<&2, V>, S.lookup(~V, m2, q), S.lookup(~V, S.remove(~V, m, key), q), S.lookup(~V, m, q), hl, SL.lookup_remove_other(~V, m, key, q, hq))

def del_mem(~V: Data, +m: List<&2, S.Entry<V>>, +m2: List<&2, S.Entry<V>>, +key: String, +hnd: {S.nodup(S.keys(~V, m)) == True{} : Bool}, +q: String, +hl: {S.lookup(~V, m2, q) == S.lookup(~V, S.remove(~V, m, key), q) : Maybe<&2, V>}) -> {S.mem(q, S.keys(~V, m2)) == Bool.and(Bool.not(S.str_eq(key, q)), S.mem(q, S.keys(~V, m))) : Bool}:
  Equal.trans(Bool, S.mem(q, S.keys(~V, m2)), S.has(~V, m2, q), Bool.and(Bool.not(S.str_eq(key, q)), S.mem(q, S.keys(~V, m))), mem_has(~V, m2, q),
    Equal.trans(Bool, S.has(~V, m2, q), S.has(~V, S.remove(~V, m, key), q), Bool.and(Bool.not(S.str_eq(key, q)), S.mem(q, S.keys(~V, m))), Equal.cong(Maybe<&2, V>, Bool, z => S.is_some(~V, z), S.lookup(~V, m2, q), S.lookup(~V, S.remove(~V, m, key), q), hl), hro_c(~V, m, key, q, hnd, S.str_eq(key, q), {==})))

def del_post(~V: Data, ~m: List<&2, S.Entry<V>>, ~m2: List<&2, S.Entry<V>>, ~key: String, ~hp: (@+q: String -> {S.lookup(~V, m2, q) == S.lookup(~V, S.remove(~V, m, key), q) : Maybe<&2, V>}) & {S.size(~V, m2) == S.size(~V, S.remove(~V, m, key)) : Nat}, +hnd: {S.nodup(S.keys(~V, m)) == True{} : Bool}, +hnd2: {S.nodup(S.keys(~V, m2)) == True{} : Bool}) -> DelPost(~V, m, m2, key):
  (Equal.cong(Maybe<&2, V>, Bool, z => S.is_some(~V, z), S.lookup(~V, m2, key), None{}, Equal.trans(Maybe<&2, V>, S.lookup(~V, m2, key), S.lookup(~V, S.remove(~V, m, key), key), None{}, Pair.fst(@+q: String -> {S.lookup(~V, m2, q) == S.lookup(~V, S.remove(~V, m, key), q) : Maybe<&2, V>}, {S.size(~V, m2) == S.size(~V, S.remove(~V, m, key)) : Nat}, hp)(key), SL.lookup_remove_same(~V, m, key, key, K.str_refl(key), hnd))),
   (q => hq => del_other(~V, m, m2, key, q, hq, Pair.fst(@+q: String -> {S.lookup(~V, m2, q) == S.lookup(~V, S.remove(~V, m, key), q) : Maybe<&2, V>}, {S.size(~V, m2) == S.size(~V, S.remove(~V, m, key)) : Nat}, hp)(q)),
    (hn => q => del_absent(~V, m, m2, key, hn, q, Pair.fst(@+q: String -> {S.lookup(~V, m2, q) == S.lookup(~V, S.remove(~V, m, key), q) : Maybe<&2, V>}, {S.size(~V, m2) == S.size(~V, S.remove(~V, m, key)) : Nat}, hp)(q)),
     (%Equal.sym(Nat, S.size(~V, m2), S.size(~V, S.remove(~V, m, key)), Pair.snd(@+q: String -> {S.lookup(~V, m2, q) == S.lookup(~V, S.remove(~V, m, key), q) : Maybe<&2, V>}, {S.size(~V, m2) == S.size(~V, S.remove(~V, m, key)) : Nat}, hp)) : {Bool.pick(Nat, S.has(~V, m, key), 1n+_, _) == S.size(~V, m) : Nat}
      size_remove(~V, m, key),
      (q => del_mem(~V, m, m2, key, hnd, q, Pair.fst(@+q: String -> {S.lookup(~V, m2, q) == S.lookup(~V, S.remove(~V, m, key), q) : Maybe<&2, V>}, {S.size(~V, m2) == S.size(~V, S.remove(~V, m, key)) : Nat}, hp)(q)), hnd2)))))

def pc_from(~V: Data, +sh: ST.Sh<V>, +hg: {ST.good(~V, sh) == True{} : Bool}, +key: String, -r: H.HashMap<&2, V> & Maybe<&2, V>, po: PO.PopOK(~V, sh, key, r)) -> PopContract(~V, sh, key, r):
  match po:
    case Tuple{+sh2, Tuple{+e, rest}}:
      (+hg2, rest2) = rest
      (sh2, (e, (hg2, del_post(~V, ~ST.model(~V, sh), ~ST.model(~V, sh2), ~key, ~rest2, model_nodup(~V, sh, hg), model_nodup(~V, sh2, hg2)))))

def dc_from(~V: Data, +sh: ST.Sh<V>, +hg: {ST.good(~V, sh) == True{} : Bool}, +key: String, -r: H.HashMap<&2, V>, po: PO.DelOK(~V, sh, key, r)) -> DelContract(~V, sh, key, r):
  match po:
    case Tuple{+sh2, Tuple{+e, rest}}:
      (+hg2, rest2) = rest
      (sh2, (e, (hg2, del_post(~V, ~ST.model(~V, sh), ~ST.model(~V, sh2), ~key, ~rest2, model_nodup(~V, sh, hg), model_nodup(~V, sh2, hg2)))))
