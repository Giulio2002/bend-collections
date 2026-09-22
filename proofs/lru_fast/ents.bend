import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../../spec/common.bend as SC
import ../../spec/lru_fast.bend as S
import ../../src/lru/fast.bend as F
import ./state.bend as ST
import ./table.bend as TB

# The specification's list operations on the abstraction ents(ks, es, ord):
# the entries of the live slots, in recency order.

def ent_app(-V: Data, +k: String, e: F.Slot<V>, +r: List<&2, S.Ent<V>>, +c: List<&2, S.Ent<V>>) -> {ST.ent_at(V, k, e, SC.append(S.Ent<V>, r, c)) == SC.append(S.Ent<V>, ST.ent_at(V, k, e, r), c) : List<&2, S.Ent<V>>}:
  match e:
    case F.Vacant{}:
      {==}
    case F.Live{v}:
      {==}
    case F.Timed{v, d}:
      {==}

def ents_app(-V: Data, +ks: List<&2, String>, +es: List<&2, F.Slot<V>>, +a: List<&2, Nat>, +c: List<&2, Nat>) -> {ST.ents(V, ks, es, SC.append(Nat, a, c)) == SC.append(S.Ent<V>, ST.ents(V, ks, es, a), ST.ents(V, ks, es, c)) : List<&2, S.Ent<V>>}:
  match a:
    case Nil{}:
      {==}
    case Con{+s, +t}:
      Equal.trans(List<&2, S.Ent<V>>, ST.ent_at(V, ST.kat(ks, s), ST.sat(V, es, s), ST.ents(V, ks, es, SC.append(Nat, t, c))), ST.ent_at(V, ST.kat(ks, s), ST.sat(V, es, s), SC.append(S.Ent<V>, ST.ents(V, ks, es, t), ST.ents(V, ks, es, c))), SC.append(S.Ent<V>, ST.ent_at(V, ST.kat(ks, s), ST.sat(V, es, s), ST.ents(V, ks, es, t)), ST.ents(V, ks, es, c)),
        Equal.cong(List<&2, S.Ent<V>>, List<&2, S.Ent<V>>, z => ST.ent_at(V, ST.kat(ks, s), ST.sat(V, es, s), z), ST.ents(V, ks, es, SC.append(Nat, t, c)), SC.append(S.Ent<V>, ST.ents(V, ks, es, t), ST.ents(V, ks, es, c)), ents_app(V, ks, es, t, c)),
        ent_app(V, ST.kat(ks, s), ST.sat(V, es, s), ST.ents(V, ks, es, t), ST.ents(V, ks, es, c)))

def snoc_app(-V: Data, +xs: List<&2, S.Ent<V>>, +y: S.Ent<V>) -> {S.snoc(V, xs, y) == SC.append(S.Ent<V>, xs, Con{y, Nil{}}) : List<&2, S.Ent<V>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      LL.cons_cong(S.Ent<V>, x, S.snoc(V, t, y), SC.append(S.Ent<V>, t, Con{y, Nil{}}), snoc_app(V, t, y))

# ---- find ----

def find_ent_skip(-V: Data, +k: String, e: F.Slot<V>, +rest: List<&2, S.Ent<V>>, +q: String, +hne: {String.eq(k, q) == False{} : Bool}) -> {S.find(V, ST.ent_at(V, k, e, rest), q) == S.find(V, rest, q) : Maybe<&2, S.Ent<V>>}:
  match e:
    case F.Vacant{}:
      {==}
    case F.Live{v}:
      L.subst(Bool, b => {S.find_at(V, b, S.En{k, v, S.zero_time()}, S.find(V, rest, q)) == S.find(V, rest, q) : Maybe<&2, S.Ent<V>>}, False{}, String.eq(k, q), Equal.sym(Bool, String.eq(k, q), False{}, hne), {==})
    case F.Timed{v, d}:
      L.subst(Bool, b => {S.find_at(V, b, S.En{k, v, F.stamp_int(d)}, S.find(V, rest, q)) == S.find(V, rest, q) : Maybe<&2, S.Ent<V>>}, False{}, String.eq(k, q), Equal.sym(Bool, String.eq(k, q), False{}, hne), {==})

# find passes over live slots whose keys are not q
def find_skip(-V: Data, +ks: List<&2, String>, +es: List<&2, F.Slot<V>>, +xs: List<&2, Nat>, +rest: List<&2, S.Ent<V>>, +q: String, +hnk: {TB.none_key(ks, xs, q) == True{} : Bool}) -> {S.find(V, SC.append(S.Ent<V>, ST.ents(V, ks, es, xs), rest), q) == S.find(V, rest, q) : Maybe<&2, S.Ent<V>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+s, +t}:
      +k = ST.kat(ks, s)
      +hne = TB.not_false(String.eq(k, q), L.and_left(Bool.not(String.eq(k, q)), TB.none_key(ks, t, q), hnk))
      Equal.trans(Maybe<&2, S.Ent<V>>, S.find(V, SC.append(S.Ent<V>, ST.ent_at(V, k, ST.sat(V, es, s), ST.ents(V, ks, es, t)), rest), q), S.find(V, ST.ent_at(V, k, ST.sat(V, es, s), SC.append(S.Ent<V>, ST.ents(V, ks, es, t), rest)), q), S.find(V, rest, q),
        Equal.cong(List<&2, S.Ent<V>>, Maybe<&2, S.Ent<V>>, z => S.find(V, z, q), SC.append(S.Ent<V>, ST.ent_at(V, k, ST.sat(V, es, s), ST.ents(V, ks, es, t)), rest), ST.ent_at(V, k, ST.sat(V, es, s), SC.append(S.Ent<V>, ST.ents(V, ks, es, t), rest)), Equal.sym(List<&2, S.Ent<V>>, ST.ent_at(V, k, ST.sat(V, es, s), SC.append(S.Ent<V>, ST.ents(V, ks, es, t), rest)), SC.append(S.Ent<V>, ST.ent_at(V, k, ST.sat(V, es, s), ST.ents(V, ks, es, t)), rest), ent_app(V, k, ST.sat(V, es, s), ST.ents(V, ks, es, t), rest))),
        Equal.trans(Maybe<&2, S.Ent<V>>, S.find(V, ST.ent_at(V, k, ST.sat(V, es, s), SC.append(S.Ent<V>, ST.ents(V, ks, es, t), rest)), q), S.find(V, SC.append(S.Ent<V>, ST.ents(V, ks, es, t), rest), q), S.find(V, rest, q),
          find_ent_skip(V, k, ST.sat(V, es, s), SC.append(S.Ent<V>, ST.ents(V, ks, es, t), rest), q, hne),
          find_skip(V, ks, es, t, rest, q, L.and_right(Bool.not(String.eq(k, q)), TB.none_key(ks, t, q), hnk))))

def find_none(-V: Data, +ks: List<&2, String>, +es: List<&2, F.Slot<V>>, +xs: List<&2, Nat>, +q: String, +hnk: {TB.none_key(ks, xs, q) == True{} : Bool}) -> {S.find(V, ST.ents(V, ks, es, xs), q) == None{} : Maybe<&2, S.Ent<V>>}:
  Equal.trans(Maybe<&2, S.Ent<V>>, S.find(V, ST.ents(V, ks, es, xs), q), S.find(V, SC.append(S.Ent<V>, ST.ents(V, ks, es, xs), Nil{}), q), None{},
    Equal.cong(List<&2, S.Ent<V>>, Maybe<&2, S.Ent<V>>, z => S.find(V, z, q), ST.ents(V, ks, es, xs), SC.append(S.Ent<V>, ST.ents(V, ks, es, xs), Nil{}), Equal.sym(List<&2, S.Ent<V>>, SC.append(S.Ent<V>, ST.ents(V, ks, es, xs), Nil{}), ST.ents(V, ks, es, xs), LL.append_nil(S.Ent<V>, ST.ents(V, ks, es, xs)))),
    find_skip(V, ks, es, xs, Nil{}, q, hnk))

# the entry a live slot denotes
def ent1(-V: Data, +k: String, e: F.Slot<V>) -> Maybe<&2, S.Ent<V>>:
  match e:
    case F.Vacant{}:
      None{}
    case F.Live{v}:
      Some{S.En{k, v, S.zero_time()}}
    case F.Timed{v, d}:
      Some{S.En{k, v, F.stamp_int(d)}}

def find_here(-V: Data, +k: String, e: F.Slot<V>, +rest: List<&2, S.Ent<V>>, +q: String, +heq: {String.eq(k, q) == True{} : Bool}, +ho: {ST.is_occ(V, e) == True{} : Bool}) -> {S.find(V, ST.ent_at(V, k, e, rest), q) == ent1(V, k, e) : Maybe<&2, S.Ent<V>>}:
  match e:
    case F.Vacant{}:
      Empty.absurd({S.find(V, rest, q) == None{} : Maybe<&2, S.Ent<V>>}, L.false_true(ho))
    case F.Live{v}:
      L.subst(Bool, b => {S.find_at(V, b, S.En{k, v, S.zero_time()}, S.find(V, rest, q)) == Some{S.En{k, v, S.zero_time()}} : Maybe<&2, S.Ent<V>>}, True{}, String.eq(k, q), Equal.sym(Bool, String.eq(k, q), True{}, heq), {==})
    case F.Timed{v, d}:
      L.subst(Bool, b => {S.find_at(V, b, S.En{k, v, F.stamp_int(d)}, S.find(V, rest, q)) == Some{S.En{k, v, F.stamp_int(d)}} : Maybe<&2, S.Ent<V>>}, True{}, String.eq(k, q), Equal.sym(Bool, String.eq(k, q), True{}, heq), {==})

# find in a ++ [s] ++ b, q the key of s and no key of a
def find_at_slot(-V: Data, +ks: List<&2, String>, +es: List<&2, F.Slot<V>>, +a: List<&2, Nat>, +s: Nat, +b: List<&2, Nat>, +q: String, +hnk: {TB.none_key(ks, a, q) == True{} : Bool}, +heq: {String.eq(ST.kat(ks, s), q) == True{} : Bool}, +ho: {ST.is_occ(V, ST.sat(V, es, s)) == True{} : Bool}) -> {S.find(V, ST.ents(V, ks, es, SC.append(Nat, a, Con{s, b})), q) == ent1(V, ST.kat(ks, s), ST.sat(V, es, s)) : Maybe<&2, S.Ent<V>>}:
  Equal.trans(Maybe<&2, S.Ent<V>>, S.find(V, ST.ents(V, ks, es, SC.append(Nat, a, Con{s, b})), q), S.find(V, SC.append(S.Ent<V>, ST.ents(V, ks, es, a), ST.ents(V, ks, es, Con{s, b})), q), ent1(V, ST.kat(ks, s), ST.sat(V, es, s)),
    Equal.cong(List<&2, S.Ent<V>>, Maybe<&2, S.Ent<V>>, z => S.find(V, z, q), ST.ents(V, ks, es, SC.append(Nat, a, Con{s, b})), SC.append(S.Ent<V>, ST.ents(V, ks, es, a), ST.ents(V, ks, es, Con{s, b})), ents_app(V, ks, es, a, Con{s, b})),
    Equal.trans(Maybe<&2, S.Ent<V>>, S.find(V, SC.append(S.Ent<V>, ST.ents(V, ks, es, a), ST.ents(V, ks, es, Con{s, b})), q), S.find(V, ST.ents(V, ks, es, Con{s, b}), q), ent1(V, ST.kat(ks, s), ST.sat(V, es, s)),
      find_skip(V, ks, es, a, ST.ents(V, ks, es, Con{s, b}), q, hnk),
      find_here(V, ST.kat(ks, s), ST.sat(V, es, s), ST.ents(V, ks, es, b), q, heq, ho)))

# ---- drop ----

def drop_ent_skip(-V: Data, +k: String, e: F.Slot<V>, +rest: List<&2, S.Ent<V>>, +q: String, +hne: {String.eq(k, q) == False{} : Bool}) -> {S.drop(V, ST.ent_at(V, k, e, rest), q) == ST.ent_at(V, k, e, S.drop(V, rest, q)) : List<&2, S.Ent<V>>}:
  match e:
    case F.Vacant{}:
      {==}
    case F.Live{v}:
      L.subst(Bool, b => {S.drop_at(V, b, S.En{k, v, S.zero_time()}, S.drop(V, rest, q)) == Con{S.En{k, v, S.zero_time()}, S.drop(V, rest, q)} : List<&2, S.Ent<V>>}, False{}, String.eq(k, q), Equal.sym(Bool, String.eq(k, q), False{}, hne), {==})
    case F.Timed{v, d}:
      L.subst(Bool, b => {S.drop_at(V, b, S.En{k, v, F.stamp_int(d)}, S.drop(V, rest, q)) == Con{S.En{k, v, F.stamp_int(d)}, S.drop(V, rest, q)} : List<&2, S.Ent<V>>}, False{}, String.eq(k, q), Equal.sym(Bool, String.eq(k, q), False{}, hne), {==})

def drop_skip(-V: Data, +ks: List<&2, String>, +es: List<&2, F.Slot<V>>, +xs: List<&2, Nat>, +rest: List<&2, S.Ent<V>>, +q: String, +hnk: {TB.none_key(ks, xs, q) == True{} : Bool}) -> {S.drop(V, SC.append(S.Ent<V>, ST.ents(V, ks, es, xs), rest), q) == SC.append(S.Ent<V>, ST.ents(V, ks, es, xs), S.drop(V, rest, q)) : List<&2, S.Ent<V>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+s, +t}:
      +k = ST.kat(ks, s)
      +e = ST.sat(V, es, s)
      +hne = TB.not_false(String.eq(k, q), L.and_left(Bool.not(String.eq(k, q)), TB.none_key(ks, t, q), hnk))
      +et = ST.ents(V, ks, es, t)
      Equal.trans(List<&2, S.Ent<V>>, S.drop(V, SC.append(S.Ent<V>, ST.ent_at(V, k, e, et), rest), q), S.drop(V, ST.ent_at(V, k, e, SC.append(S.Ent<V>, et, rest)), q), SC.append(S.Ent<V>, ST.ent_at(V, k, e, et), S.drop(V, rest, q)),
        Equal.cong(List<&2, S.Ent<V>>, List<&2, S.Ent<V>>, z => S.drop(V, z, q), SC.append(S.Ent<V>, ST.ent_at(V, k, e, et), rest), ST.ent_at(V, k, e, SC.append(S.Ent<V>, et, rest)), Equal.sym(List<&2, S.Ent<V>>, ST.ent_at(V, k, e, SC.append(S.Ent<V>, et, rest)), SC.append(S.Ent<V>, ST.ent_at(V, k, e, et), rest), ent_app(V, k, e, et, rest))),
        Equal.trans(List<&2, S.Ent<V>>, S.drop(V, ST.ent_at(V, k, e, SC.append(S.Ent<V>, et, rest)), q), ST.ent_at(V, k, e, S.drop(V, SC.append(S.Ent<V>, et, rest), q)), SC.append(S.Ent<V>, ST.ent_at(V, k, e, et), S.drop(V, rest, q)),
          drop_ent_skip(V, k, e, SC.append(S.Ent<V>, et, rest), q, hne),
          Equal.trans(List<&2, S.Ent<V>>, ST.ent_at(V, k, e, S.drop(V, SC.append(S.Ent<V>, et, rest), q)), ST.ent_at(V, k, e, SC.append(S.Ent<V>, et, S.drop(V, rest, q))), SC.append(S.Ent<V>, ST.ent_at(V, k, e, et), S.drop(V, rest, q)),
            Equal.cong(List<&2, S.Ent<V>>, List<&2, S.Ent<V>>, z => ST.ent_at(V, k, e, z), S.drop(V, SC.append(S.Ent<V>, et, rest), q), SC.append(S.Ent<V>, et, S.drop(V, rest, q)), drop_skip(V, ks, es, t, rest, q, L.and_right(Bool.not(String.eq(k, q)), TB.none_key(ks, t, q), hnk))),
            ent_app(V, k, e, et, S.drop(V, rest, q)))))

def drop_here(-V: Data, +k: String, e: F.Slot<V>, +rest: List<&2, S.Ent<V>>, +q: String, +heq: {String.eq(k, q) == True{} : Bool}, +ho: {ST.is_occ(V, e) == True{} : Bool}) -> {S.drop(V, ST.ent_at(V, k, e, rest), q) == S.drop(V, rest, q) : List<&2, S.Ent<V>>}:
  match e:
    case F.Vacant{}:
      Empty.absurd({S.drop(V, rest, q) == S.drop(V, rest, q) : List<&2, S.Ent<V>>}, L.false_true(ho))
    case F.Live{v}:
      L.subst(Bool, b => {S.drop_at(V, b, S.En{k, v, S.zero_time()}, S.drop(V, rest, q)) == S.drop(V, rest, q) : List<&2, S.Ent<V>>}, True{}, String.eq(k, q), Equal.sym(Bool, String.eq(k, q), True{}, heq), {==})
    case F.Timed{v, d}:
      L.subst(Bool, b => {S.drop_at(V, b, S.En{k, v, F.stamp_int(d)}, S.drop(V, rest, q)) == S.drop(V, rest, q) : List<&2, S.Ent<V>>}, True{}, String.eq(k, q), Equal.sym(Bool, String.eq(k, q), True{}, heq), {==})

def drop_none(-V: Data, +ks: List<&2, String>, +es: List<&2, F.Slot<V>>, +xs: List<&2, Nat>, +q: String, +hnk: {TB.none_key(ks, xs, q) == True{} : Bool}) -> {S.drop(V, ST.ents(V, ks, es, xs), q) == ST.ents(V, ks, es, xs) : List<&2, S.Ent<V>>}:
  Equal.trans(List<&2, S.Ent<V>>, S.drop(V, ST.ents(V, ks, es, xs), q), S.drop(V, SC.append(S.Ent<V>, ST.ents(V, ks, es, xs), Nil{}), q), ST.ents(V, ks, es, xs),
    Equal.cong(List<&2, S.Ent<V>>, List<&2, S.Ent<V>>, z => S.drop(V, z, q), ST.ents(V, ks, es, xs), SC.append(S.Ent<V>, ST.ents(V, ks, es, xs), Nil{}), Equal.sym(List<&2, S.Ent<V>>, SC.append(S.Ent<V>, ST.ents(V, ks, es, xs), Nil{}), ST.ents(V, ks, es, xs), LL.append_nil(S.Ent<V>, ST.ents(V, ks, es, xs)))),
    Equal.trans(List<&2, S.Ent<V>>, S.drop(V, SC.append(S.Ent<V>, ST.ents(V, ks, es, xs), Nil{}), q), SC.append(S.Ent<V>, ST.ents(V, ks, es, xs), Nil{}), ST.ents(V, ks, es, xs),
      drop_skip(V, ks, es, xs, Nil{}, q, hnk),
      LL.append_nil(S.Ent<V>, ST.ents(V, ks, es, xs))))

# drop in a ++ [s] ++ b, q the key of s and of no other live slot
def drop_at_slot(-V: Data, +ks: List<&2, String>, +es: List<&2, F.Slot<V>>, +a: List<&2, Nat>, +s: Nat, +b: List<&2, Nat>, +q: String, +hna: {TB.none_key(ks, a, q) == True{} : Bool}, +hnb: {TB.none_key(ks, b, q) == True{} : Bool}, +heq: {String.eq(ST.kat(ks, s), q) == True{} : Bool}, +ho: {ST.is_occ(V, ST.sat(V, es, s)) == True{} : Bool}) -> {S.drop(V, ST.ents(V, ks, es, SC.append(Nat, a, Con{s, b})), q) == ST.ents(V, ks, es, SC.append(Nat, a, b)) : List<&2, S.Ent<V>>}:
  +ea = ST.ents(V, ks, es, a)
  +eb = ST.ents(V, ks, es, b)
  Equal.trans(List<&2, S.Ent<V>>, S.drop(V, ST.ents(V, ks, es, SC.append(Nat, a, Con{s, b})), q), S.drop(V, SC.append(S.Ent<V>, ea, ST.ents(V, ks, es, Con{s, b})), q), ST.ents(V, ks, es, SC.append(Nat, a, b)),
    Equal.cong(List<&2, S.Ent<V>>, List<&2, S.Ent<V>>, z => S.drop(V, z, q), ST.ents(V, ks, es, SC.append(Nat, a, Con{s, b})), SC.append(S.Ent<V>, ea, ST.ents(V, ks, es, Con{s, b})), ents_app(V, ks, es, a, Con{s, b})),
    Equal.trans(List<&2, S.Ent<V>>, S.drop(V, SC.append(S.Ent<V>, ea, ST.ents(V, ks, es, Con{s, b})), q), SC.append(S.Ent<V>, ea, S.drop(V, ST.ents(V, ks, es, Con{s, b}), q)), ST.ents(V, ks, es, SC.append(Nat, a, b)),
      drop_skip(V, ks, es, a, ST.ents(V, ks, es, Con{s, b}), q, hna),
      Equal.trans(List<&2, S.Ent<V>>, SC.append(S.Ent<V>, ea, S.drop(V, ST.ents(V, ks, es, Con{s, b}), q)), SC.append(S.Ent<V>, ea, eb), ST.ents(V, ks, es, SC.append(Nat, a, b)),
        Equal.cong(List<&2, S.Ent<V>>, List<&2, S.Ent<V>>, z => SC.append(S.Ent<V>, ea, z), S.drop(V, ST.ents(V, ks, es, Con{s, b}), q), eb,
          Equal.trans(List<&2, S.Ent<V>>, S.drop(V, ST.ent_at(V, ST.kat(ks, s), ST.sat(V, es, s), eb), q), S.drop(V, eb, q), eb, drop_here(V, ST.kat(ks, s), ST.sat(V, es, s), eb, q, heq, ho), drop_none(V, ks, es, b, q, hnb))),
        Equal.sym(List<&2, S.Ent<V>>, ST.ents(V, ks, es, SC.append(Nat, a, b)), SC.append(S.Ent<V>, ea, eb), ents_app(V, ks, es, a, b)))))

# ---- length, keys, tail ----

def ent_len(-V: Data, +k: String, e: F.Slot<V>, +rest: List<&2, S.Ent<V>>, +ho: {ST.is_occ(V, e) == True{} : Bool}) -> {S.len(V, ST.ent_at(V, k, e, rest)) == 1n+S.len(V, rest) : Nat}:
  match e:
    case F.Vacant{}:
      Empty.absurd({S.len(V, rest) == 1n+S.len(V, rest) : Nat}, L.false_true(ho))
    case F.Live{v}:
      {==}
    case F.Timed{v, d}:
      {==}

def len_ents(-V: Data, +ks: List<&2, String>, +es: List<&2, F.Slot<V>>, +xs: List<&2, Nat>, +ho: {ST.all_occ(V, es, xs) == True{} : Bool}) -> {S.len(V, ST.ents(V, ks, es, xs)) == SC.length(Nat, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+s, +t}:
      Equal.trans(Nat, S.len(V, ST.ent_at(V, ST.kat(ks, s), ST.sat(V, es, s), ST.ents(V, ks, es, t))), 1n+S.len(V, ST.ents(V, ks, es, t)), 1n+SC.length(Nat, t),
        ent_len(V, ST.kat(ks, s), ST.sat(V, es, s), ST.ents(V, ks, es, t), L.and_left(ST.is_occ(V, ST.sat(V, es, s)), ST.all_occ(V, es, t), ho)),
        N.succ_cong(S.len(V, ST.ents(V, ks, es, t)), SC.length(Nat, t), len_ents(V, ks, es, t, L.and_right(ST.is_occ(V, ST.sat(V, es, s)), ST.all_occ(V, es, t), ho))))

def ent_keys(-V: Data, +k: String, e: F.Slot<V>, +rest: List<&2, S.Ent<V>>, +ho: {ST.is_occ(V, e) == True{} : Bool}) -> {S.keys(V, ST.ent_at(V, k, e, rest)) == Con{k, S.keys(V, rest)} : List<&2, String>}:
  match e:
    case F.Vacant{}:
      Empty.absurd({S.keys(V, rest) == Con{k, S.keys(V, rest)} : List<&2, String>}, L.false_true(ho))
    case F.Live{v}:
      {==}
    case F.Timed{v, d}:
      {==}

def keys_ents(-V: Data, +ks: List<&2, String>, +es: List<&2, F.Slot<V>>, +xs: List<&2, Nat>, +ho: {ST.all_occ(V, es, xs) == True{} : Bool}) -> {S.keys(V, ST.ents(V, ks, es, xs)) == ST.keys_at(ks, xs) : List<&2, String>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+s, +t}:
      Equal.trans(List<&2, String>, S.keys(V, ST.ent_at(V, ST.kat(ks, s), ST.sat(V, es, s), ST.ents(V, ks, es, t))), Con{ST.kat(ks, s), S.keys(V, ST.ents(V, ks, es, t))}, Con{ST.kat(ks, s), ST.keys_at(ks, t)},
        ent_keys(V, ST.kat(ks, s), ST.sat(V, es, s), ST.ents(V, ks, es, t), L.and_left(ST.is_occ(V, ST.sat(V, es, s)), ST.all_occ(V, es, t), ho)),
        LL.cons_cong(String, ST.kat(ks, s), S.keys(V, ST.ents(V, ks, es, t)), ST.keys_at(ks, t), keys_ents(V, ks, es, t, L.and_right(ST.is_occ(V, ST.sat(V, es, s)), ST.all_occ(V, es, t), ho))))

def ent_tail(-V: Data, +k: String, e: F.Slot<V>, +rest: List<&2, S.Ent<V>>, +ho: {ST.is_occ(V, e) == True{} : Bool}) -> {S.tail(V, ST.ent_at(V, k, e, rest)) == rest : List<&2, S.Ent<V>>}:
  match e:
    case F.Vacant{}:
      Empty.absurd({S.tail(V, rest) == rest : List<&2, S.Ent<V>>}, L.false_true(ho))
    case F.Live{v}:
      {==}
    case F.Timed{v, d}:
      {==}
