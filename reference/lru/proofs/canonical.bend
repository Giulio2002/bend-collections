import Base
import ../spec/cache.bend as S
import ../spec/operations.bend as O
import ../spec/equivalence.bend as E
import ../types/model.bend as T
import ./map_routing.bend as Routing

# Generic algebra of the independent canonical model form (spec/equivalence).
# Key equality contracts are explicit; the String instance discharges them.

def reflects(~K: Data, ~same: K -> K -> Bool) -> Type:
  @+a: K -> @+b: K -> {same(a)(b) == True{} : Bool} -> {a == b : K}

def reflexive(~K: Data, ~same: K -> K -> Bool) -> Type:
  @+a: K -> {same(a)(a) == True{} : Bool}

def clash(x: Bool, yes: {x == True{} : Bool}, no: {x == False{} : Bool}) -> Empty:
  Routing.false_true(Equal.trans(Bool, False{}, x, True{}, Equal.sym(Bool, x, False{}, no), yes))

def moved(~K: Data, ~same: K -> K -> Bool, order: List<&2, K>, +key: K) -> List<&2, K>:
  List.append(&2, K, S.unlist(~K, ~same, order, key), Con{key, Nil{}})

def or_false(b: Bool) -> {Bool.or(b, False{}) == b : Bool}:
  match b:
    case False{}: {==}
    case True{}: {==}

def or_true(b: Bool) -> {Bool.or(b, True{}) == True{} : Bool}:
  match b:
    case False{}: {==}
    case True{}: {==}

# Symmetry of an inequality from reflection and reflexivity.
def symmetric_decide(~K: Data, ~same: K -> K -> Bool, ~refl: reflects(~K, ~same), ~rfx: reflexive(~K, ~same), +a: K, +b: K, no: {same(a)(b) == False{} : Bool}, r: Bool, e: {same(b)(a) == r : Bool}) -> {same(b)(a) == False{} : Bool}:
  match r:
    case False{}: e
    case True{}:
      eq = refl(b, a, e)
      self = Equal.trans(Bool, same(a)(a), same(a)(b), False{}, Equal.cong(K, Bool, x => same(a)(x), a, b, Equal.sym(K, b, a, eq)), no)
      Empty.absurd({same(b)(a) == False{} : Bool}, clash(same(a)(a), rfx(a), self))

def symmetric_false(~K: Data, ~same: K -> K -> Bool, ~refl: reflects(~K, ~same), ~rfx: reflexive(~K, ~same), +a: K, +b: K, no: {same(a)(b) == False{} : Bool}) -> {same(b)(a) == False{} : Bool}:
  symmetric_decide(~K, ~same, ~refl, ~rfx, a, b, no, same(b)(a), {==})

# A binding matching q is not removed by erasing a key different from q.
def erase_other_step(~K: Data, ~same: K -> K -> Bool, ~refl: reflects(~K, ~same), -V: Data, +k: K, +v: V, +d: T.Int64, +t: List<&2, T.Entry<K, V>>, +key: K, +q: K, +h: {same(q)(key) == False{} : Bool}, x: Bool, +ex: {same(k)(key) == x : Bool}, y: Bool, +ey: {same(k)(q) == y : Bool}, ih: {S.find(~K, ~same, V, S.erase(~K, ~same, V, t, key), q) == S.find(~K, ~same, V, t, q) : Maybe<&2, T.Entry<K, V>>}) -> {S.find(~K, ~same, V, S.omit_entry(K, V, T.Item{k, v, d}, S.erase(~K, ~same, V, t, key), x), q) == S.choose_entry(K, V, T.Item{k, v, d}, S.find(~K, ~same, V, t, q), y) : Maybe<&2, T.Entry<K, V>>}:
  match x:
    case True{}:
      match y:
        case False{}: ih
        case True{}:
          eq = refl(k, q, ey)
          bad = Equal.trans(Bool, same(q)(key), same(k)(key), True{}, Equal.cong(K, Bool, z => same(z)(key), q, k, Equal.sym(K, k, q, eq)), ex)
          Empty.absurd({S.find(~K, ~same, V, S.erase(~K, ~same, V, t, key), q) == Some{T.Item{k, v, d}} : Maybe<&2, T.Entry<K, V>>}, clash(same(q)(key), bad, h))
    case False{}:
      %Equal.sym(Bool, same(k)(q), y, ey) : {S.choose_entry(K, V, T.Item{k, v, d}, S.find(~K, ~same, V, S.erase(~K, ~same, V, t, key), q), _) == S.choose_entry(K, V, T.Item{k, v, d}, S.find(~K, ~same, V, t, q), y) : Maybe<&2, T.Entry<K, V>>}
      Equal.cong(Maybe<&2, T.Entry<K, V>>, Maybe<&2, T.Entry<K, V>>, rest => S.choose_entry(K, V, T.Item{k, v, d}, rest, y), S.find(~K, ~same, V, S.erase(~K, ~same, V, t, key), q), S.find(~K, ~same, V, t, q), ih)

def find_erase_other(~K: Data, ~same: K -> K -> Bool, ~refl: reflects(~K, ~same), -V: Data, b: List<&2, T.Entry<K, V>>, +key: K, +q: K, +h: {same(q)(key) == False{} : Bool}) -> {S.find(~K, ~same, V, S.erase(~K, ~same, V, b, key), q) == S.find(~K, ~same, V, b, q) : Maybe<&2, T.Entry<K, V>>}:
  match b:
    case Nil{}: {==}
    case Con{T.Item{+k, +v, +d}, +t}:
      erase_other_step(~K, ~same, ~refl, V, k, v, d, t, key, q, h, same(k)(key), {==}, same(k)(q), {==}, find_erase_other(~K, ~same, ~refl, V, t, key, q, h))

# Removing a key from the recency list does not change membership of others.
def member_unlist_skip(~K: Data, ~same: K -> K -> Bool, ~refl: reflects(~K, ~same), +oi: K, +ot: List<&2, K>, +key: K, +k: K, +h: {same(k)(key) == False{} : Bool}, +ex: {same(oi)(key) == True{} : Bool}, y: Bool, +ey: {same(oi)(k) == y : Bool}, ih: {E.member(~K, ~same, S.unlist(~K, ~same, ot, key), k) == E.member(~K, ~same, ot, k) : Bool}) -> {E.member(~K, ~same, S.unlist(~K, ~same, ot, key), k) == Bool.or(y, E.member(~K, ~same, ot, k)) : Bool}:
  match y:
    case False{}: ih
    case True{}:
      eq = refl(oi, k, ey)
      bad = Equal.trans(Bool, same(k)(key), same(oi)(key), True{}, Equal.cong(K, Bool, z => same(z)(key), k, oi, Equal.sym(K, oi, k, eq)), ex)
      Empty.absurd({E.member(~K, ~same, S.unlist(~K, ~same, ot, key), k) == True{} : Bool}, clash(same(k)(key), bad, h))

def member_unlist_step(~K: Data, ~same: K -> K -> Bool, ~refl: reflects(~K, ~same), +oi: K, +ot: List<&2, K>, +key: K, +k: K, +h: {same(k)(key) == False{} : Bool}, x: Bool, +ex: {same(oi)(key) == x : Bool}, ih: {E.member(~K, ~same, S.unlist(~K, ~same, ot, key), k) == E.member(~K, ~same, ot, k) : Bool}) -> {E.member(~K, ~same, S.omit_key(K, oi, S.unlist(~K, ~same, ot, key), x), k) == Bool.or(same(oi)(k), E.member(~K, ~same, ot, k)) : Bool}:
  match x:
    case False{}: Equal.cong(Bool, Bool, m => Bool.or(same(oi)(k), m), E.member(~K, ~same, S.unlist(~K, ~same, ot, key), k), E.member(~K, ~same, ot, k), ih)
    case True{}: member_unlist_skip(~K, ~same, ~refl, oi, ot, key, k, h, ex, same(oi)(k), {==}, ih)

def member_unlist(~K: Data, ~same: K -> K -> Bool, ~refl: reflects(~K, ~same), o: List<&2, K>, +key: K, +k: K, +h: {same(k)(key) == False{} : Bool}) -> {E.member(~K, ~same, S.unlist(~K, ~same, o, key), k) == E.member(~K, ~same, o, k) : Bool}:
  match o:
    case Nil{}: {==}
    case Con{+oi, +ot}:
      member_unlist_step(~K, ~same, ~refl, oi, ot, key, k, h, same(oi)(key), {==}, member_unlist(~K, ~same, ~refl, ot, key, k, h))

def or_assoc(a: Bool, b: Bool, c: Bool) -> {Bool.or(Bool.or(a, b), c) == Bool.or(a, Bool.or(b, c)) : Bool}:
  match a:
    case True{}: {==}
    case False{}: {==}

def member_append(~K: Data, ~same: K -> K -> Bool, xs: List<&2, K>, +ys: List<&2, K>, +k: K) -> {E.member(~K, ~same, List.append(&2, K, xs, ys), k) == Bool.or(E.member(~K, ~same, xs, k), E.member(~K, ~same, ys, k)) : Bool}:
  match xs:
    case Nil{}: {==}
    case Con{+x, +rest}:
      Equal.trans(Bool, Bool.or(same(x)(k), E.member(~K, ~same, List.append(&2, K, rest, ys), k)), Bool.or(same(x)(k), Bool.or(E.member(~K, ~same, rest, k), E.member(~K, ~same, ys, k))), Bool.or(Bool.or(same(x)(k), E.member(~K, ~same, rest, k)), E.member(~K, ~same, ys, k)), Equal.cong(Bool, Bool, m => Bool.or(same(x)(k), m), E.member(~K, ~same, List.append(&2, K, rest, ys), k), Bool.or(E.member(~K, ~same, rest, k), E.member(~K, ~same, ys, k)), member_append(~K, ~same, rest, ys, k)), Equal.sym(Bool, Bool.or(Bool.or(same(x)(k), E.member(~K, ~same, rest, k)), E.member(~K, ~same, ys, k)), Bool.or(same(x)(k), Bool.or(E.member(~K, ~same, rest, k), E.member(~K, ~same, ys, k))), or_assoc(same(x)(k), E.member(~K, ~same, rest, k), E.member(~K, ~same, ys, k))))

# Membership in the moved recency list (key re-appended at the newest end).
def member_moved_other(~K: Data, ~same: K -> K -> Bool, ~refl: reflects(~K, ~same), ~rfx: reflexive(~K, ~same), +o: List<&2, K>, +key: K, +k: K, +h: {same(k)(key) == False{} : Bool}) -> {E.member(~K, ~same, moved(~K, ~same, o, key), k) == E.member(~K, ~same, o, k) : Bool}:
  %Equal.sym(Bool, E.member(~K, ~same, List.append(&2, K, S.unlist(~K, ~same, o, key), Con{key, Nil{}}), k), Bool.or(E.member(~K, ~same, S.unlist(~K, ~same, o, key), k), Bool.or(same(key)(k), False{})), member_append(~K, ~same, S.unlist(~K, ~same, o, key), Con{key, Nil{}}, k)) : {_ == E.member(~K, ~same, o, k) : Bool}
  %Equal.sym(Bool, same(key)(k), False{}, symmetric_false(~K, ~same, ~refl, ~rfx, k, key, h)) : {Bool.or(E.member(~K, ~same, S.unlist(~K, ~same, o, key), k), Bool.or(_, False{})) == E.member(~K, ~same, o, k) : Bool}
  %Equal.sym(Bool, E.member(~K, ~same, S.unlist(~K, ~same, o, key), k), E.member(~K, ~same, o, k), member_unlist(~K, ~same, ~refl, o, key, k, h)) : {Bool.or(_, False{}) == E.member(~K, ~same, o, k) : Bool}
  or_false(E.member(~K, ~same, o, k))

def member_moved_key(~K: Data, ~same: K -> K -> Bool, ~rfx: reflexive(~K, ~same), +o: List<&2, K>, +key: K) -> {E.member(~K, ~same, moved(~K, ~same, o, key), key) == True{} : Bool}:
  %Equal.sym(Bool, E.member(~K, ~same, List.append(&2, K, S.unlist(~K, ~same, o, key), Con{key, Nil{}}), key), Bool.or(E.member(~K, ~same, S.unlist(~K, ~same, o, key), key), Bool.or(same(key)(key), False{})), member_append(~K, ~same, S.unlist(~K, ~same, o, key), Con{key, Nil{}}, key)) : {_ == True{} : Bool}
  %Equal.sym(Bool, same(key)(key), True{}, rfx(key)) : {Bool.or(E.member(~K, ~same, S.unlist(~K, ~same, o, key), key), Bool.or(_, False{})) == True{} : Bool}
  or_true(E.member(~K, ~same, S.unlist(~K, ~same, o, key), key))

def member_moved_same(~K: Data, ~same: K -> K -> Bool, ~refl: reflects(~K, ~same), ~rfx: reflexive(~K, ~same), +o: List<&2, K>, +key: K, +k: K, +h: {same(k)(key) == True{} : Bool}) -> {E.member(~K, ~same, moved(~K, ~same, o, key), k) == True{} : Bool}:
  %Equal.sym(K, k, key, refl(k, key, h)) : {E.member(~K, ~same, moved(~K, ~same, o, key), _) == True{} : Bool}
  member_moved_key(~K, ~same, ~rfx, o, key)

# ---------------------------------------------------------------------------
# Lookups at recency keys after removing/moving a key.
def keep_or_drop(-K: Data, -V: Data, l: Maybe<&2, T.Entry<K, V>>, rest: List<&2, Maybe<&2, T.Entry<K, V>>>, drop: Bool) -> List<&2, Maybe<&2, T.Entry<K, V>>>:
  match drop:
    case True{}: rest
    case False{}: Con{l, rest}

def ldrop(~K: Data, ~same: K -> K -> Bool, -V: Data, o: List<&2, K>, xs: List<&2, Maybe<&2, T.Entry<K, V>>>, +key: K) -> List<&2, Maybe<&2, T.Entry<K, V>>>:
  match o xs:
    case Con{oi, ot} Con{l, lt}: keep_or_drop(K, V, l, ldrop(~K, ~same, V, ot, lt, key), same(oi)(key))
    case a b: Nil{}

def lookups_unlist_step(~K: Data, ~same: K -> K -> Bool, -V: Data, +oi: K, +ot: List<&2, K>, +b: List<&2, T.Entry<K, V>>, +key: K, x: Bool, ih: {E.lookups(~K, ~same, V, S.unlist(~K, ~same, ot, key), b) == ldrop(~K, ~same, V, ot, E.lookups(~K, ~same, V, ot, b), key) : List<&2, Maybe<&2, T.Entry<K, V>>>}) -> {E.lookups(~K, ~same, V, S.omit_key(K, oi, S.unlist(~K, ~same, ot, key), x), b) == keep_or_drop(K, V, S.find(~K, ~same, V, b, oi), ldrop(~K, ~same, V, ot, E.lookups(~K, ~same, V, ot, b), key), x) : List<&2, Maybe<&2, T.Entry<K, V>>>}:
  match x:
    case True{}: ih
    case False{}: Equal.cong(List<&2, Maybe<&2, T.Entry<K, V>>>, List<&2, Maybe<&2, T.Entry<K, V>>>, zs => Con{S.find(~K, ~same, V, b, oi), zs}, E.lookups(~K, ~same, V, S.unlist(~K, ~same, ot, key), b), ldrop(~K, ~same, V, ot, E.lookups(~K, ~same, V, ot, b), key), ih)

def lookups_unlist(~K: Data, ~same: K -> K -> Bool, -V: Data, o: List<&2, K>, +b: List<&2, T.Entry<K, V>>, +key: K) -> {E.lookups(~K, ~same, V, S.unlist(~K, ~same, o, key), b) == ldrop(~K, ~same, V, o, E.lookups(~K, ~same, V, o, b), key) : List<&2, Maybe<&2, T.Entry<K, V>>>}:
  match o:
    case Nil{}: {==}
    case Con{+oi, +ot}: lookups_unlist_step(~K, ~same, V, oi, ot, b, key, same(oi)(key), lookups_unlist(~K, ~same, V, ot, b, key))

def lookups_unlist_erase_step(~K: Data, ~same: K -> K -> Bool, ~refl: reflects(~K, ~same), -V: Data, +oi: K, +ot: List<&2, K>, +b: List<&2, T.Entry<K, V>>, +key: K, x: Bool, +ex: {same(oi)(key) == x : Bool}, ih: {E.lookups(~K, ~same, V, S.unlist(~K, ~same, ot, key), S.erase(~K, ~same, V, b, key)) == ldrop(~K, ~same, V, ot, E.lookups(~K, ~same, V, ot, b), key) : List<&2, Maybe<&2, T.Entry<K, V>>>}) -> {E.lookups(~K, ~same, V, S.omit_key(K, oi, S.unlist(~K, ~same, ot, key), x), S.erase(~K, ~same, V, b, key)) == keep_or_drop(K, V, S.find(~K, ~same, V, b, oi), ldrop(~K, ~same, V, ot, E.lookups(~K, ~same, V, ot, b), key), x) : List<&2, Maybe<&2, T.Entry<K, V>>>}:
  match x:
    case True{}: ih
    case False{}:
      %Equal.sym(Maybe<&2, T.Entry<K, V>>, S.find(~K, ~same, V, S.erase(~K, ~same, V, b, key), oi), S.find(~K, ~same, V, b, oi), find_erase_other(~K, ~same, ~refl, V, b, key, oi, ex)) : {Con{_, E.lookups(~K, ~same, V, S.unlist(~K, ~same, ot, key), S.erase(~K, ~same, V, b, key))} == Con{S.find(~K, ~same, V, b, oi), ldrop(~K, ~same, V, ot, E.lookups(~K, ~same, V, ot, b), key)} : List<&2, Maybe<&2, T.Entry<K, V>>>}
      Equal.cong(List<&2, Maybe<&2, T.Entry<K, V>>>, List<&2, Maybe<&2, T.Entry<K, V>>>, zs => Con{S.find(~K, ~same, V, b, oi), zs}, E.lookups(~K, ~same, V, S.unlist(~K, ~same, ot, key), S.erase(~K, ~same, V, b, key)), ldrop(~K, ~same, V, ot, E.lookups(~K, ~same, V, ot, b), key), ih)

def lookups_unlist_erase(~K: Data, ~same: K -> K -> Bool, ~refl: reflects(~K, ~same), -V: Data, o: List<&2, K>, +b: List<&2, T.Entry<K, V>>, +key: K) -> {E.lookups(~K, ~same, V, S.unlist(~K, ~same, o, key), S.erase(~K, ~same, V, b, key)) == ldrop(~K, ~same, V, o, E.lookups(~K, ~same, V, o, b), key) : List<&2, Maybe<&2, T.Entry<K, V>>>}:
  match o:
    case Nil{}: {==}
    case Con{+oi, +ot}: lookups_unlist_erase_step(~K, ~same, ~refl, V, oi, ot, b, key, same(oi)(key), {==}, lookups_unlist_erase(~K, ~same, ~refl, V, ot, b, key))

def lookups_append(~K: Data, ~same: K -> K -> Bool, -V: Data, o1: List<&2, K>, +o2: List<&2, K>, +b: List<&2, T.Entry<K, V>>) -> {E.lookups(~K, ~same, V, List.append(&2, K, o1, o2), b) == List.append(&2, Maybe<&2, T.Entry<K, V>>, E.lookups(~K, ~same, V, o1, b), E.lookups(~K, ~same, V, o2, b)) : List<&2, Maybe<&2, T.Entry<K, V>>>}:
  match o1:
    case Nil{}: {==}
    case Con{+x, +rest}: Equal.cong(List<&2, Maybe<&2, T.Entry<K, V>>>, List<&2, Maybe<&2, T.Entry<K, V>>>, zs => Con{S.find(~K, ~same, V, b, x), zs}, E.lookups(~K, ~same, V, List.append(&2, K, rest, o2), b), List.append(&2, Maybe<&2, T.Entry<K, V>>, E.lookups(~K, ~same, V, rest, b), E.lookups(~K, ~same, V, o2, b)), lookups_append(~K, ~same, V, rest, o2, b))

def lookups_prepend_step(~K: Data, ~same: K -> K -> Bool, ~refl: reflects(~K, ~same), ~rfx: reflexive(~K, ~same), -V: Data, +oi: K, +ot: List<&2, K>, +key: K, +v: V, +d: T.Int64, +rest: List<&2, T.Entry<K, V>>, x: Bool, +ex: {same(oi)(key) == x : Bool}, ih: {E.lookups(~K, ~same, V, S.unlist(~K, ~same, ot, key), Con{T.Item{key, v, d}, rest}) == E.lookups(~K, ~same, V, S.unlist(~K, ~same, ot, key), rest) : List<&2, Maybe<&2, T.Entry<K, V>>>}) -> {E.lookups(~K, ~same, V, S.omit_key(K, oi, S.unlist(~K, ~same, ot, key), x), Con{T.Item{key, v, d}, rest}) == E.lookups(~K, ~same, V, S.omit_key(K, oi, S.unlist(~K, ~same, ot, key), x), rest) : List<&2, Maybe<&2, T.Entry<K, V>>>}:
  match x:
    case True{}: ih
    case False{}:
      %Equal.sym(Bool, same(key)(oi), False{}, symmetric_false(~K, ~same, ~refl, ~rfx, oi, key, ex)) : {Con{S.choose_entry(K, V, T.Item{key, v, d}, S.find(~K, ~same, V, rest, oi), _), E.lookups(~K, ~same, V, S.unlist(~K, ~same, ot, key), Con{T.Item{key, v, d}, rest})} == Con{S.find(~K, ~same, V, rest, oi), E.lookups(~K, ~same, V, S.unlist(~K, ~same, ot, key), rest)} : List<&2, Maybe<&2, T.Entry<K, V>>>}
      Equal.cong(List<&2, Maybe<&2, T.Entry<K, V>>>, List<&2, Maybe<&2, T.Entry<K, V>>>, zs => Con{S.find(~K, ~same, V, rest, oi), zs}, E.lookups(~K, ~same, V, S.unlist(~K, ~same, ot, key), Con{T.Item{key, v, d}, rest}), E.lookups(~K, ~same, V, S.unlist(~K, ~same, ot, key), rest), ih)

# A new binding for key is invisible at the other (unlisted) recency keys.
def lookups_prepend(~K: Data, ~same: K -> K -> Bool, ~refl: reflects(~K, ~same), ~rfx: reflexive(~K, ~same), -V: Data, o: List<&2, K>, +key: K, +v: V, +d: T.Int64, +rest: List<&2, T.Entry<K, V>>) -> {E.lookups(~K, ~same, V, S.unlist(~K, ~same, o, key), Con{T.Item{key, v, d}, rest}) == E.lookups(~K, ~same, V, S.unlist(~K, ~same, o, key), rest) : List<&2, Maybe<&2, T.Entry<K, V>>>}:
  match o:
    case Nil{}: {==}
    case Con{+oi, +ot}: lookups_prepend_step(~K, ~same, ~refl, ~rfx, V, oi, ot, key, v, d, rest, same(oi)(key), {==}, lookups_prepend(~K, ~same, ~refl, ~rfx, V, ot, key, v, d, rest))

# ---------------------------------------------------------------------------
# Stray bindings under erase/unlist/move.
def erase_keep_true(~K: Data, ~same: K -> K -> Bool, -V: Data, +k: K, +v: V, +d: T.Int64, +lhs: List<&2, T.Entry<K, V>>, +st: List<&2, T.Entry<K, V>>, +key: K, +ex: {same(k)(key) == True{} : Bool}, y: Bool, ih: {lhs == S.erase(~K, ~same, V, st, key) : List<&2, T.Entry<K, V>>}) -> {lhs == S.erase(~K, ~same, V, E.keep_stray(K, V, T.Item{k, v, d}, st, y), key) : List<&2, T.Entry<K, V>>}:
  match y:
    case True{}: ih
    case False{}:
      %Equal.sym(Bool, same(k)(key), True{}, ex) : {lhs == S.omit_entry(K, V, T.Item{k, v, d}, S.erase(~K, ~same, V, st, key), _) : List<&2, T.Entry<K, V>>}
      ih

def erase_keep_false(~K: Data, ~same: K -> K -> Bool, -V: Data, +k: K, +v: V, +d: T.Int64, +lhs: List<&2, T.Entry<K, V>>, +st: List<&2, T.Entry<K, V>>, +key: K, +ex: {same(k)(key) == False{} : Bool}, y: Bool, ih: {lhs == S.erase(~K, ~same, V, st, key) : List<&2, T.Entry<K, V>>}) -> {E.keep_stray(K, V, T.Item{k, v, d}, lhs, y) == S.erase(~K, ~same, V, E.keep_stray(K, V, T.Item{k, v, d}, st, y), key) : List<&2, T.Entry<K, V>>}:
  match y:
    case True{}: ih
    case False{}:
      %Equal.sym(Bool, same(k)(key), False{}, ex) : {Con{T.Item{k, v, d}, lhs} == S.omit_entry(K, V, T.Item{k, v, d}, S.erase(~K, ~same, V, st, key), _) : List<&2, T.Entry<K, V>>}
      Equal.cong(List<&2, T.Entry<K, V>>, List<&2, T.Entry<K, V>>, zs => Con{T.Item{k, v, d}, zs}, lhs, S.erase(~K, ~same, V, st, key), ih)

def stray_unlist_erase_step(~K: Data, ~same: K -> K -> Bool, ~refl: reflects(~K, ~same), -V: Data, +o: List<&2, K>, +k: K, +v: V, +d: T.Int64, +t: List<&2, T.Entry<K, V>>, +key: K, x: Bool, +ex: {same(k)(key) == x : Bool}, ih: {E.stray(~K, ~same, V, S.unlist(~K, ~same, o, key), S.erase(~K, ~same, V, t, key)) == S.erase(~K, ~same, V, E.stray(~K, ~same, V, o, t), key) : List<&2, T.Entry<K, V>>}) -> {E.stray(~K, ~same, V, S.unlist(~K, ~same, o, key), S.omit_entry(K, V, T.Item{k, v, d}, S.erase(~K, ~same, V, t, key), x)) == S.erase(~K, ~same, V, E.keep_stray(K, V, T.Item{k, v, d}, E.stray(~K, ~same, V, o, t), E.member(~K, ~same, o, k)), key) : List<&2, T.Entry<K, V>>}:
  match x:
    case True{}: erase_keep_true(~K, ~same, V, k, v, d, E.stray(~K, ~same, V, S.unlist(~K, ~same, o, key), S.erase(~K, ~same, V, t, key)), E.stray(~K, ~same, V, o, t), key, ex, E.member(~K, ~same, o, k), ih)
    case False{}:
      %Equal.sym(Bool, E.member(~K, ~same, S.unlist(~K, ~same, o, key), k), E.member(~K, ~same, o, k), member_unlist(~K, ~same, ~refl, o, key, k, ex)) : {E.keep_stray(K, V, T.Item{k, v, d}, E.stray(~K, ~same, V, S.unlist(~K, ~same, o, key), S.erase(~K, ~same, V, t, key)), _) == S.erase(~K, ~same, V, E.keep_stray(K, V, T.Item{k, v, d}, E.stray(~K, ~same, V, o, t), E.member(~K, ~same, o, k)), key) : List<&2, T.Entry<K, V>>}
      erase_keep_false(~K, ~same, V, k, v, d, E.stray(~K, ~same, V, S.unlist(~K, ~same, o, key), S.erase(~K, ~same, V, t, key)), E.stray(~K, ~same, V, o, t), key, ex, E.member(~K, ~same, o, k), ih)

def stray_unlist_erase(~K: Data, ~same: K -> K -> Bool, ~refl: reflects(~K, ~same), -V: Data, +o: List<&2, K>, b: List<&2, T.Entry<K, V>>, +key: K) -> {E.stray(~K, ~same, V, S.unlist(~K, ~same, o, key), S.erase(~K, ~same, V, b, key)) == S.erase(~K, ~same, V, E.stray(~K, ~same, V, o, b), key) : List<&2, T.Entry<K, V>>}:
  match b:
    case Nil{}: {==}
    case Con{T.Item{+k, +v, +d}, +t}: stray_unlist_erase_step(~K, ~same, ~refl, V, o, k, v, d, t, key, same(k)(key), {==}, stray_unlist_erase(~K, ~same, ~refl, V, o, t, key))

def stray_moved_step(~K: Data, ~same: K -> K -> Bool, ~refl: reflects(~K, ~same), ~rfx: reflexive(~K, ~same), -V: Data, +o: List<&2, K>, +k: K, +v: V, +d: T.Int64, +t: List<&2, T.Entry<K, V>>, +key: K, x: Bool, +ex: {same(k)(key) == x : Bool}, ih: {E.stray(~K, ~same, V, moved(~K, ~same, o, key), t) == S.erase(~K, ~same, V, E.stray(~K, ~same, V, o, t), key) : List<&2, T.Entry<K, V>>}) -> {E.keep_stray(K, V, T.Item{k, v, d}, E.stray(~K, ~same, V, moved(~K, ~same, o, key), t), E.member(~K, ~same, moved(~K, ~same, o, key), k)) == S.erase(~K, ~same, V, E.keep_stray(K, V, T.Item{k, v, d}, E.stray(~K, ~same, V, o, t), E.member(~K, ~same, o, k)), key) : List<&2, T.Entry<K, V>>}:
  match x:
    case True{}:
      %Equal.sym(Bool, E.member(~K, ~same, moved(~K, ~same, o, key), k), True{}, member_moved_same(~K, ~same, ~refl, ~rfx, o, key, k, ex)) : {E.keep_stray(K, V, T.Item{k, v, d}, E.stray(~K, ~same, V, moved(~K, ~same, o, key), t), _) == S.erase(~K, ~same, V, E.keep_stray(K, V, T.Item{k, v, d}, E.stray(~K, ~same, V, o, t), E.member(~K, ~same, o, k)), key) : List<&2, T.Entry<K, V>>}
      erase_keep_true(~K, ~same, V, k, v, d, E.stray(~K, ~same, V, moved(~K, ~same, o, key), t), E.stray(~K, ~same, V, o, t), key, ex, E.member(~K, ~same, o, k), ih)
    case False{}:
      %Equal.sym(Bool, E.member(~K, ~same, moved(~K, ~same, o, key), k), E.member(~K, ~same, o, k), member_moved_other(~K, ~same, ~refl, ~rfx, o, key, k, ex)) : {E.keep_stray(K, V, T.Item{k, v, d}, E.stray(~K, ~same, V, moved(~K, ~same, o, key), t), _) == S.erase(~K, ~same, V, E.keep_stray(K, V, T.Item{k, v, d}, E.stray(~K, ~same, V, o, t), E.member(~K, ~same, o, k)), key) : List<&2, T.Entry<K, V>>}
      erase_keep_false(~K, ~same, V, k, v, d, E.stray(~K, ~same, V, moved(~K, ~same, o, key), t), E.stray(~K, ~same, V, o, t), key, ex, E.member(~K, ~same, o, k), ih)

def stray_moved(~K: Data, ~same: K -> K -> Bool, ~refl: reflects(~K, ~same), ~rfx: reflexive(~K, ~same), -V: Data, +o: List<&2, K>, b: List<&2, T.Entry<K, V>>, +key: K) -> {E.stray(~K, ~same, V, moved(~K, ~same, o, key), b) == S.erase(~K, ~same, V, E.stray(~K, ~same, V, o, b), key) : List<&2, T.Entry<K, V>>}:
  match b:
    case Nil{}: {==}
    case Con{T.Item{+k, +v, +d}, +t}: stray_moved_step(~K, ~same, ~refl, ~rfx, V, o, k, v, d, t, key, same(k)(key), {==}, stray_moved(~K, ~same, ~refl, ~rfx, V, o, t, key))

def stray_moved_erase_step(~K: Data, ~same: K -> K -> Bool, ~refl: reflects(~K, ~same), ~rfx: reflexive(~K, ~same), -V: Data, +o: List<&2, K>, +k: K, +v: V, +d: T.Int64, +t: List<&2, T.Entry<K, V>>, +key: K, x: Bool, +ex: {same(k)(key) == x : Bool}, ih: {E.stray(~K, ~same, V, moved(~K, ~same, o, key), S.erase(~K, ~same, V, t, key)) == S.erase(~K, ~same, V, E.stray(~K, ~same, V, o, t), key) : List<&2, T.Entry<K, V>>}) -> {E.stray(~K, ~same, V, moved(~K, ~same, o, key), S.omit_entry(K, V, T.Item{k, v, d}, S.erase(~K, ~same, V, t, key), x)) == S.erase(~K, ~same, V, E.keep_stray(K, V, T.Item{k, v, d}, E.stray(~K, ~same, V, o, t), E.member(~K, ~same, o, k)), key) : List<&2, T.Entry<K, V>>}:
  match x:
    case True{}: erase_keep_true(~K, ~same, V, k, v, d, E.stray(~K, ~same, V, moved(~K, ~same, o, key), S.erase(~K, ~same, V, t, key)), E.stray(~K, ~same, V, o, t), key, ex, E.member(~K, ~same, o, k), ih)
    case False{}:
      %Equal.sym(Bool, E.member(~K, ~same, moved(~K, ~same, o, key), k), E.member(~K, ~same, o, k), member_moved_other(~K, ~same, ~refl, ~rfx, o, key, k, ex)) : {E.keep_stray(K, V, T.Item{k, v, d}, E.stray(~K, ~same, V, moved(~K, ~same, o, key), S.erase(~K, ~same, V, t, key)), _) == S.erase(~K, ~same, V, E.keep_stray(K, V, T.Item{k, v, d}, E.stray(~K, ~same, V, o, t), E.member(~K, ~same, o, k)), key) : List<&2, T.Entry<K, V>>}
      erase_keep_false(~K, ~same, V, k, v, d, E.stray(~K, ~same, V, moved(~K, ~same, o, key), S.erase(~K, ~same, V, t, key)), E.stray(~K, ~same, V, o, t), key, ex, E.member(~K, ~same, o, k), ih)

def stray_moved_erase(~K: Data, ~same: K -> K -> Bool, ~refl: reflects(~K, ~same), ~rfx: reflexive(~K, ~same), -V: Data, +o: List<&2, K>, b: List<&2, T.Entry<K, V>>, +key: K) -> {E.stray(~K, ~same, V, moved(~K, ~same, o, key), S.erase(~K, ~same, V, b, key)) == S.erase(~K, ~same, V, E.stray(~K, ~same, V, o, b), key) : List<&2, T.Entry<K, V>>}:
  match b:
    case Nil{}: {==}
    case Con{T.Item{+k, +v, +d}, +t}: stray_moved_erase_step(~K, ~same, ~refl, ~rfx, V, o, k, v, d, t, key, same(k)(key), {==}, stray_moved_erase(~K, ~same, ~refl, ~rfx, V, o, t, key))

# ---------------------------------------------------------------------------
# Lookup of ANY key from the canonical form.
def choose_lookup(-K: Data, -V: Data, l: Maybe<&2, T.Entry<K, V>>, rest: Maybe<&2, T.Entry<K, V>>, hit: Bool) -> Maybe<&2, T.Entry<K, V>>:
  match hit:
    case True{}: l
    case False{}: rest

def pick(~K: Data, ~same: K -> K -> Bool, -V: Data, o: List<&2, K>, xs: List<&2, Maybe<&2, T.Entry<K, V>>>, +q: K) -> Maybe<&2, T.Entry<K, V>>:
  match o xs:
    case Con{oi, ot} Con{l, lt}: choose_lookup(K, V, l, pick(~K, ~same, V, ot, lt, q), same(oi)(q))
    case a b: None{}

def decide_lookup(-K: Data, -V: Data, bound: Bool, inside: Maybe<&2, T.Entry<K, V>>, outside: Maybe<&2, T.Entry<K, V>>) -> Maybe<&2, T.Entry<K, V>>:
  match bound:
    case True{}: inside
    case False{}: outside

def cfind(~K: Data, ~same: K -> K -> Bool, -V: Data, +o: List<&2, K>, xs: List<&2, Maybe<&2, T.Entry<K, V>>>, x: List<&2, T.Entry<K, V>>, +q: K) -> Maybe<&2, T.Entry<K, V>>:
  decide_lookup(K, V, E.member(~K, ~same, o, q), pick(~K, ~same, V, o, xs, q), S.find(~K, ~same, V, x, q))

def canonical_find(~K: Data, ~same: K -> K -> Bool, -V: Data, c: E.Canonical<K, V>, +q: K) -> Maybe<&2, T.Entry<K, V>>:
  E.Canon{cap, o, l, m, f, xs, x} = c
  cfind(~K, ~same, V, o, xs, x, q)

def bindings(-K: Data, -V: Data, s: S.Model<K, V>) -> List<&2, T.Entry<K, V>>:
  S.Abstract{cap, b, o, l, m, f} = s
  b

def pick_hit(~K: Data, ~same: K -> K -> Bool, ~refl: reflects(~K, ~same), -V: Data, +oi: K, +ot: List<&2, K>, +b: List<&2, T.Entry<K, V>>, +q: K, y: Bool, +ey: {same(oi)(q) == y : Bool}, rest: {Bool.or(y, E.member(~K, ~same, ot, q)) == True{} : Bool}, ih: @h: {E.member(~K, ~same, ot, q) == True{} : Bool} -> {S.find(~K, ~same, V, b, q) == pick(~K, ~same, V, ot, E.lookups(~K, ~same, V, ot, b), q) : Maybe<&2, T.Entry<K, V>>}) -> {S.find(~K, ~same, V, b, q) == choose_lookup(K, V, S.find(~K, ~same, V, b, oi), pick(~K, ~same, V, ot, E.lookups(~K, ~same, V, ot, b), q), y) : Maybe<&2, T.Entry<K, V>>}:
  match y:
    case False{}: ih(rest)
    case True{}: Equal.cong(K, Maybe<&2, T.Entry<K, V>>, z => S.find(~K, ~same, V, b, z), q, oi, Equal.sym(K, oi, q, refl(oi, q, ey)))

def pick_member(~K: Data, ~same: K -> K -> Bool, ~refl: reflects(~K, ~same), -V: Data, o: List<&2, K>, +b: List<&2, T.Entry<K, V>>, +q: K, +h: {E.member(~K, ~same, o, q) == True{} : Bool}) -> {S.find(~K, ~same, V, b, q) == pick(~K, ~same, V, o, E.lookups(~K, ~same, V, o, b), q) : Maybe<&2, T.Entry<K, V>>}:
  match o:
    case Nil{}: Empty.absurd({S.find(~K, ~same, V, b, q) == None{} : Maybe<&2, T.Entry<K, V>>}, Routing.false_true(h))
    case Con{+oi, +ot}: pick_hit(~K, ~same, ~refl, V, oi, ot, b, q, same(oi)(q), {==}, h, hh => pick_member(~K, ~same, ~refl, V, ot, b, q, hh))

def outside_step(~K: Data, ~same: K -> K -> Bool, ~refl: reflects(~K, ~same), -V: Data, +o: List<&2, K>, +k: K, +v: V, +d: T.Int64, +t: List<&2, T.Entry<K, V>>, +q: K, +h: {E.member(~K, ~same, o, q) == False{} : Bool}, y: Bool, +ey: {E.member(~K, ~same, o, k) == y : Bool}, z: Bool, +ez: {same(k)(q) == z : Bool}, ih: {S.find(~K, ~same, V, t, q) == S.find(~K, ~same, V, E.stray(~K, ~same, V, o, t), q) : Maybe<&2, T.Entry<K, V>>}) -> {S.choose_entry(K, V, T.Item{k, v, d}, S.find(~K, ~same, V, t, q), z) == S.find(~K, ~same, V, E.keep_stray(K, V, T.Item{k, v, d}, E.stray(~K, ~same, V, o, t), y), q) : Maybe<&2, T.Entry<K, V>>}:
  match y:
    case True{}:
      match z:
        case False{}: ih
        case True{}:
          bad = Equal.trans(Bool, E.member(~K, ~same, o, q), E.member(~K, ~same, o, k), True{}, Equal.cong(K, Bool, w => E.member(~K, ~same, o, w), q, k, Equal.sym(K, k, q, refl(k, q, ez))), ey)
          Empty.absurd({Some{T.Item{k, v, d}} == S.find(~K, ~same, V, E.stray(~K, ~same, V, o, t), q) : Maybe<&2, T.Entry<K, V>>}, clash(E.member(~K, ~same, o, q), bad, h))
    case False{}:
      %Equal.sym(Bool, same(k)(q), z, ez) : {S.choose_entry(K, V, T.Item{k, v, d}, S.find(~K, ~same, V, t, q), z) == S.choose_entry(K, V, T.Item{k, v, d}, S.find(~K, ~same, V, E.stray(~K, ~same, V, o, t), q), _) : Maybe<&2, T.Entry<K, V>>}
      Equal.cong(Maybe<&2, T.Entry<K, V>>, Maybe<&2, T.Entry<K, V>>, rest => S.choose_entry(K, V, T.Item{k, v, d}, rest, z), S.find(~K, ~same, V, t, q), S.find(~K, ~same, V, E.stray(~K, ~same, V, o, t), q), ih)

def outside_member(~K: Data, ~same: K -> K -> Bool, ~refl: reflects(~K, ~same), -V: Data, +o: List<&2, K>, b: List<&2, T.Entry<K, V>>, +q: K, +h: {E.member(~K, ~same, o, q) == False{} : Bool}) -> {S.find(~K, ~same, V, b, q) == S.find(~K, ~same, V, E.stray(~K, ~same, V, o, b), q) : Maybe<&2, T.Entry<K, V>>}:
  match b:
    case Nil{}: {==}
    case Con{T.Item{+k, +v, +d}, +t}: outside_step(~K, ~same, ~refl, V, o, k, v, d, t, q, h, E.member(~K, ~same, o, k), {==}, same(k)(q), {==}, outside_member(~K, ~same, ~refl, V, o, t, q, h))

def find_decide(~K: Data, ~same: K -> K -> Bool, ~refl: reflects(~K, ~same), -V: Data, +o: List<&2, K>, +b: List<&2, T.Entry<K, V>>, +q: K, m: Bool, +em: {E.member(~K, ~same, o, q) == m : Bool}) -> {S.find(~K, ~same, V, b, q) == decide_lookup(K, V, m, pick(~K, ~same, V, o, E.lookups(~K, ~same, V, o, b), q), S.find(~K, ~same, V, E.stray(~K, ~same, V, o, b), q)) : Maybe<&2, T.Entry<K, V>>}:
  match m:
    case True{}: pick_member(~K, ~same, ~refl, V, o, b, q, em)
    case False{}: outside_member(~K, ~same, ~refl, V, o, b, q, em)

# Every lookup is determined by the canonical form.
def find_canonical(~K: Data, ~same: K -> K -> Bool, ~refl: reflects(~K, ~same), -V: Data, s: S.Model<K, V>, +q: K) -> {S.find(~K, ~same, V, bindings(K, V, s), q) == canonical_find(~K, ~same, V, E.canonical(~K, ~same, V, s), q) : Maybe<&2, T.Entry<K, V>>}:
  S.Abstract{cap, +b, +o, l, m, f} = s
  find_decide(~K, ~same, ~refl, V, o, b, q, E.member(~K, ~same, o, q), {==})

# Meaning of the relation: related models agree on lookup of EVERY key.
def lookup_agreement(~K: Data, ~same: K -> K -> Bool, ~refl: reflects(~K, ~same), -V: Data, +a: S.Model<K, V>, +b: S.Model<K, V>, related: E.states(~K, ~same, V, a, b), +q: K) -> {S.find(~K, ~same, V, bindings(K, V, a), q) == S.find(~K, ~same, V, bindings(K, V, b), q) : Maybe<&2, T.Entry<K, V>>}:
  Equal.trans(Maybe<&2, T.Entry<K, V>>, S.find(~K, ~same, V, bindings(K, V, a), q), canonical_find(~K, ~same, V, E.canonical(~K, ~same, V, a), q), S.find(~K, ~same, V, bindings(K, V, b), q), find_canonical(~K, ~same, ~refl, V, a, q), Equal.trans(Maybe<&2, T.Entry<K, V>>, canonical_find(~K, ~same, V, E.canonical(~K, ~same, V, a), q), canonical_find(~K, ~same, V, E.canonical(~K, ~same, V, b), q), S.find(~K, ~same, V, bindings(K, V, b), q), Equal.cong(E.Canonical<K, V>, Maybe<&2, T.Entry<K, V>>, c => canonical_find(~K, ~same, V, c, q), E.canonical(~K, ~same, V, a), E.canonical(~K, ~same, V, b), related), Equal.sym(Maybe<&2, T.Entry<K, V>>, S.find(~K, ~same, V, bindings(K, V, b), q), canonical_find(~K, ~same, V, E.canonical(~K, ~same, V, b), q), find_canonical(~K, ~same, ~refl, V, b, q))))

# Ordered enumeration (Keys/Values/aggregate input) from the canonical form.
def somes(-K: Data, -V: Data, xs: List<&2, Maybe<&2, T.Entry<K, V>>>) -> List<&2, T.Entry<K, V>>:
  match xs:
    case Nil{}: Nil{}
    case Con{l, lt}: O.collect(K, V, l, somes(K, V, lt))

def ordered_somes(~K: Data, ~same: K -> K -> Bool, -V: Data, o: List<&2, K>, +b: List<&2, T.Entry<K, V>>) -> {O.ordered(~K, ~same, V, o, b) == somes(K, V, E.lookups(~K, ~same, V, o, b)) : List<&2, T.Entry<K, V>>}:
  match o:
    case Nil{}: {==}
    case Con{+k, +t}: Equal.cong(List<&2, T.Entry<K, V>>, List<&2, T.Entry<K, V>>, rest => O.collect(K, V, S.find(~K, ~same, V, b, k), rest), O.ordered(~K, ~same, V, t, b), somes(K, V, E.lookups(~K, ~same, V, t, b)), ordered_somes(~K, ~same, V, t, b))

def canonical_entries(-K: Data, -V: Data, c: E.Canonical<K, V>) -> List<&2, T.Entry<K, V>>:
  E.Canon{cap, o, l, m, f, xs, x} = c
  somes(K, V, xs)

def entries_canonical(~K: Data, ~same: K -> K -> Bool, -V: Data, s: S.Model<K, V>) -> {O.all_entries(~K, ~same, V, s) == canonical_entries(K, V, E.canonical(~K, ~same, V, s)) : List<&2, T.Entry<K, V>>}:
  S.Abstract{cap, +b, +o, l, m, f} = s
  ordered_somes(~K, ~same, V, o, b)

def entries_agreement(~K: Data, ~same: K -> K -> Bool, -V: Data, +a: S.Model<K, V>, +b: S.Model<K, V>, related: E.states(~K, ~same, V, a, b)) -> {O.all_entries(~K, ~same, V, a) == O.all_entries(~K, ~same, V, b) : List<&2, T.Entry<K, V>>}:
  Equal.trans(List<&2, T.Entry<K, V>>, O.all_entries(~K, ~same, V, a), canonical_entries(K, V, E.canonical(~K, ~same, V, a)), O.all_entries(~K, ~same, V, b), entries_canonical(~K, ~same, V, a), Equal.trans(List<&2, T.Entry<K, V>>, canonical_entries(K, V, E.canonical(~K, ~same, V, a)), canonical_entries(K, V, E.canonical(~K, ~same, V, b)), O.all_entries(~K, ~same, V, b), Equal.cong(E.Canonical<K, V>, List<&2, T.Entry<K, V>>, c => canonical_entries(K, V, c), E.canonical(~K, ~same, V, a), E.canonical(~K, ~same, V, b), related), Equal.sym(List<&2, T.Entry<K, V>>, O.all_entries(~K, ~same, V, b), canonical_entries(K, V, E.canonical(~K, ~same, V, b)), entries_canonical(~K, ~same, V, b))))

# ---------------------------------------------------------------------------
# Canonical effect of each primitive state change used by the specification.
def c_drop(~K: Data, ~same: K -> K -> Bool, -V: Data, c: E.Canonical<K, V>, +key: K) -> E.Canonical<K, V>:
  E.Canon{cap, +o, l, m, f, xs, x} = c
  E.Canon{cap, S.unlist(~K, ~same, o, key), l, m, f, ldrop(~K, ~same, V, o, xs, key), S.erase(~K, ~same, V, x, key)}

def c_write(~K: Data, ~same: K -> K -> Bool, -V: Data, c: E.Canonical<K, V>, +key: K, value: V, deadline: T.Int64) -> E.Canonical<K, V>:
  E.Canon{cap, +o, l, m, f, xs, x} = c
  E.Canon{cap, moved(~K, ~same, o, key), l, m, f, List.append(&2, Maybe<&2, T.Entry<K, V>>, ldrop(~K, ~same, V, o, xs, key), Con{Some{T.Item{key, value, deadline}}, Nil{}}), S.erase(~K, ~same, V, x, key)}

def c_move(~K: Data, ~same: K -> K -> Bool, -V: Data, c: E.Canonical<K, V>, +key: K) -> E.Canonical<K, V>:
  E.Canon{cap, +o, l, m, f, +xs, +x} = c
  E.Canon{cap, moved(~K, ~same, o, key), l, m, f, List.append(&2, Maybe<&2, T.Entry<K, V>>, ldrop(~K, ~same, V, o, xs, key), Con{cfind(~K, ~same, V, o, xs, x, key), Nil{}}), S.erase(~K, ~same, V, x, key)}

def c_counts(-K: Data, -V: Data, c: E.Canonical<K, V>, m: T.Metrics) -> E.Canonical<K, V>:
  E.Canon{cap, o, l, old, f, xs, x} = c
  E.Canon{cap, o, l, m, f, xs, x}

def drop_transform(~K: Data, ~same: K -> K -> Bool, ~refl: reflects(~K, ~same), -V: Data, +cap: Nat, +b: List<&2, T.Entry<K, V>>, +o: List<&2, K>, +l: T.Int64, +m: T.Metrics, +f: Bool, +key: K) -> {E.canonical(~K, ~same, V, S.Abstract{cap, S.erase(~K, ~same, V, b, key), S.unlist(~K, ~same, o, key), l, m, f}) == c_drop(~K, ~same, V, E.canonical(~K, ~same, V, S.Abstract{cap, b, o, l, m, f}), key) : E.Canonical<K, V>}:
  %Equal.sym(List<&2, Maybe<&2, T.Entry<K, V>>>, E.lookups(~K, ~same, V, S.unlist(~K, ~same, o, key), S.erase(~K, ~same, V, b, key)), ldrop(~K, ~same, V, o, E.lookups(~K, ~same, V, o, b), key), lookups_unlist_erase(~K, ~same, ~refl, V, o, b, key)) : {E.Canon{cap, S.unlist(~K, ~same, o, key), l, m, f, _, E.stray(~K, ~same, V, S.unlist(~K, ~same, o, key), S.erase(~K, ~same, V, b, key))} == c_drop(~K, ~same, V, E.canonical(~K, ~same, V, S.Abstract{cap, b, o, l, m, f}), key) : E.Canonical<K, V>}
  %Equal.sym(List<&2, T.Entry<K, V>>, E.stray(~K, ~same, V, S.unlist(~K, ~same, o, key), S.erase(~K, ~same, V, b, key)), S.erase(~K, ~same, V, E.stray(~K, ~same, V, o, b), key), stray_unlist_erase(~K, ~same, ~refl, V, o, b, key)) : {E.Canon{cap, S.unlist(~K, ~same, o, key), l, m, f, ldrop(~K, ~same, V, o, E.lookups(~K, ~same, V, o, b), key), _} == c_drop(~K, ~same, V, E.canonical(~K, ~same, V, S.Abstract{cap, b, o, l, m, f}), key) : E.Canonical<K, V>}
  {==}

def write_transform(~K: Data, ~same: K -> K -> Bool, ~refl: reflects(~K, ~same), ~rfx: reflexive(~K, ~same), -V: Data, +cap: Nat, +b: List<&2, T.Entry<K, V>>, +o: List<&2, K>, +l: T.Int64, +m: T.Metrics, +f: Bool, +key: K, +value: V, +deadline: T.Int64) -> {E.canonical(~K, ~same, V, S.Abstract{cap, Con{T.Item{key, value, deadline}, S.erase(~K, ~same, V, b, key)}, moved(~K, ~same, o, key), l, m, f}) == c_write(~K, ~same, V, E.canonical(~K, ~same, V, S.Abstract{cap, b, o, l, m, f}), key, value, deadline) : E.Canonical<K, V>}:
  %Equal.sym(List<&2, Maybe<&2, T.Entry<K, V>>>, E.lookups(~K, ~same, V, List.append(&2, K, S.unlist(~K, ~same, o, key), Con{key, Nil{}}), Con{T.Item{key, value, deadline}, S.erase(~K, ~same, V, b, key)}), List.append(&2, Maybe<&2, T.Entry<K, V>>, E.lookups(~K, ~same, V, S.unlist(~K, ~same, o, key), Con{T.Item{key, value, deadline}, S.erase(~K, ~same, V, b, key)}), E.lookups(~K, ~same, V, Con{key, Nil{}}, Con{T.Item{key, value, deadline}, S.erase(~K, ~same, V, b, key)})), lookups_append(~K, ~same, V, S.unlist(~K, ~same, o, key), Con{key, Nil{}}, Con{T.Item{key, value, deadline}, S.erase(~K, ~same, V, b, key)})) : {E.Canon{cap, moved(~K, ~same, o, key), l, m, f, _, E.stray(~K, ~same, V, moved(~K, ~same, o, key), Con{T.Item{key, value, deadline}, S.erase(~K, ~same, V, b, key)})} == c_write(~K, ~same, V, E.canonical(~K, ~same, V, S.Abstract{cap, b, o, l, m, f}), key, value, deadline) : E.Canonical<K, V>}
  %Equal.sym(List<&2, Maybe<&2, T.Entry<K, V>>>, E.lookups(~K, ~same, V, S.unlist(~K, ~same, o, key), Con{T.Item{key, value, deadline}, S.erase(~K, ~same, V, b, key)}), E.lookups(~K, ~same, V, S.unlist(~K, ~same, o, key), S.erase(~K, ~same, V, b, key)), lookups_prepend(~K, ~same, ~refl, ~rfx, V, o, key, value, deadline, S.erase(~K, ~same, V, b, key))) : {E.Canon{cap, moved(~K, ~same, o, key), l, m, f, List.append(&2, Maybe<&2, T.Entry<K, V>>, _, E.lookups(~K, ~same, V, Con{key, Nil{}}, Con{T.Item{key, value, deadline}, S.erase(~K, ~same, V, b, key)})), E.stray(~K, ~same, V, moved(~K, ~same, o, key), Con{T.Item{key, value, deadline}, S.erase(~K, ~same, V, b, key)})} == c_write(~K, ~same, V, E.canonical(~K, ~same, V, S.Abstract{cap, b, o, l, m, f}), key, value, deadline) : E.Canonical<K, V>}
  %Equal.sym(List<&2, Maybe<&2, T.Entry<K, V>>>, E.lookups(~K, ~same, V, S.unlist(~K, ~same, o, key), S.erase(~K, ~same, V, b, key)), ldrop(~K, ~same, V, o, E.lookups(~K, ~same, V, o, b), key), lookups_unlist_erase(~K, ~same, ~refl, V, o, b, key)) : {E.Canon{cap, moved(~K, ~same, o, key), l, m, f, List.append(&2, Maybe<&2, T.Entry<K, V>>, _, E.lookups(~K, ~same, V, Con{key, Nil{}}, Con{T.Item{key, value, deadline}, S.erase(~K, ~same, V, b, key)})), E.stray(~K, ~same, V, moved(~K, ~same, o, key), Con{T.Item{key, value, deadline}, S.erase(~K, ~same, V, b, key)})} == c_write(~K, ~same, V, E.canonical(~K, ~same, V, S.Abstract{cap, b, o, l, m, f}), key, value, deadline) : E.Canonical<K, V>}
  %Equal.sym(Bool, same(key)(key), True{}, rfx(key)) : {E.Canon{cap, moved(~K, ~same, o, key), l, m, f, List.append(&2, Maybe<&2, T.Entry<K, V>>, ldrop(~K, ~same, V, o, E.lookups(~K, ~same, V, o, b), key), Con{S.choose_entry(K, V, T.Item{key, value, deadline}, S.find(~K, ~same, V, S.erase(~K, ~same, V, b, key), key), _), Nil{}}), E.stray(~K, ~same, V, moved(~K, ~same, o, key), Con{T.Item{key, value, deadline}, S.erase(~K, ~same, V, b, key)})} == c_write(~K, ~same, V, E.canonical(~K, ~same, V, S.Abstract{cap, b, o, l, m, f}), key, value, deadline) : E.Canonical<K, V>}
  %Equal.sym(Bool, E.member(~K, ~same, moved(~K, ~same, o, key), key), True{}, member_moved_key(~K, ~same, ~rfx, o, key)) : {E.Canon{cap, moved(~K, ~same, o, key), l, m, f, List.append(&2, Maybe<&2, T.Entry<K, V>>, ldrop(~K, ~same, V, o, E.lookups(~K, ~same, V, o, b), key), Con{Some{T.Item{key, value, deadline}}, Nil{}}), E.keep_stray(K, V, T.Item{key, value, deadline}, E.stray(~K, ~same, V, moved(~K, ~same, o, key), S.erase(~K, ~same, V, b, key)), _)} == c_write(~K, ~same, V, E.canonical(~K, ~same, V, S.Abstract{cap, b, o, l, m, f}), key, value, deadline) : E.Canonical<K, V>}
  %Equal.sym(List<&2, T.Entry<K, V>>, E.stray(~K, ~same, V, moved(~K, ~same, o, key), S.erase(~K, ~same, V, b, key)), S.erase(~K, ~same, V, E.stray(~K, ~same, V, o, b), key), stray_moved_erase(~K, ~same, ~refl, ~rfx, V, o, b, key)) : {E.Canon{cap, moved(~K, ~same, o, key), l, m, f, List.append(&2, Maybe<&2, T.Entry<K, V>>, ldrop(~K, ~same, V, o, E.lookups(~K, ~same, V, o, b), key), Con{Some{T.Item{key, value, deadline}}, Nil{}}), _} == c_write(~K, ~same, V, E.canonical(~K, ~same, V, S.Abstract{cap, b, o, l, m, f}), key, value, deadline) : E.Canonical<K, V>}
  {==}

def move_transform(~K: Data, ~same: K -> K -> Bool, ~refl: reflects(~K, ~same), ~rfx: reflexive(~K, ~same), -V: Data, +cap: Nat, +b: List<&2, T.Entry<K, V>>, +o: List<&2, K>, +l: T.Int64, +m: T.Metrics, +f: Bool, +key: K) -> {E.canonical(~K, ~same, V, S.Abstract{cap, b, moved(~K, ~same, o, key), l, m, f}) == c_move(~K, ~same, V, E.canonical(~K, ~same, V, S.Abstract{cap, b, o, l, m, f}), key) : E.Canonical<K, V>}:
  %Equal.sym(List<&2, Maybe<&2, T.Entry<K, V>>>, E.lookups(~K, ~same, V, List.append(&2, K, S.unlist(~K, ~same, o, key), Con{key, Nil{}}), b), List.append(&2, Maybe<&2, T.Entry<K, V>>, E.lookups(~K, ~same, V, S.unlist(~K, ~same, o, key), b), E.lookups(~K, ~same, V, Con{key, Nil{}}, b)), lookups_append(~K, ~same, V, S.unlist(~K, ~same, o, key), Con{key, Nil{}}, b)) : {E.Canon{cap, moved(~K, ~same, o, key), l, m, f, _, E.stray(~K, ~same, V, moved(~K, ~same, o, key), b)} == c_move(~K, ~same, V, E.canonical(~K, ~same, V, S.Abstract{cap, b, o, l, m, f}), key) : E.Canonical<K, V>}
  %Equal.sym(List<&2, Maybe<&2, T.Entry<K, V>>>, E.lookups(~K, ~same, V, S.unlist(~K, ~same, o, key), b), ldrop(~K, ~same, V, o, E.lookups(~K, ~same, V, o, b), key), lookups_unlist(~K, ~same, V, o, b, key)) : {E.Canon{cap, moved(~K, ~same, o, key), l, m, f, List.append(&2, Maybe<&2, T.Entry<K, V>>, _, Con{S.find(~K, ~same, V, b, key), Nil{}}), E.stray(~K, ~same, V, moved(~K, ~same, o, key), b)} == c_move(~K, ~same, V, E.canonical(~K, ~same, V, S.Abstract{cap, b, o, l, m, f}), key) : E.Canonical<K, V>}
  %Equal.sym(Maybe<&2, T.Entry<K, V>>, S.find(~K, ~same, V, b, key), decide_lookup(K, V, E.member(~K, ~same, o, key), pick(~K, ~same, V, o, E.lookups(~K, ~same, V, o, b), key), S.find(~K, ~same, V, E.stray(~K, ~same, V, o, b), key)), find_decide(~K, ~same, ~refl, V, o, b, key, E.member(~K, ~same, o, key), {==})) : {E.Canon{cap, moved(~K, ~same, o, key), l, m, f, List.append(&2, Maybe<&2, T.Entry<K, V>>, ldrop(~K, ~same, V, o, E.lookups(~K, ~same, V, o, b), key), Con{_, Nil{}}), E.stray(~K, ~same, V, moved(~K, ~same, o, key), b)} == c_move(~K, ~same, V, E.canonical(~K, ~same, V, S.Abstract{cap, b, o, l, m, f}), key) : E.Canonical<K, V>}
  %Equal.sym(List<&2, T.Entry<K, V>>, E.stray(~K, ~same, V, moved(~K, ~same, o, key), b), S.erase(~K, ~same, V, E.stray(~K, ~same, V, o, b), key), stray_moved(~K, ~same, ~refl, ~rfx, V, o, b, key)) : {E.Canon{cap, moved(~K, ~same, o, key), l, m, f, List.append(&2, Maybe<&2, T.Entry<K, V>>, ldrop(~K, ~same, V, o, E.lookups(~K, ~same, V, o, b), key), Con{cfind(~K, ~same, V, o, E.lookups(~K, ~same, V, o, b), E.stray(~K, ~same, V, o, b), key), Nil{}}), _} == c_move(~K, ~same, V, E.canonical(~K, ~same, V, S.Abstract{cap, b, o, l, m, f}), key) : E.Canonical<K, V>}
  {==}

def stray_of(-K: Data, -V: Data, c: E.Canonical<K, V>) -> List<&2, T.Entry<K, V>>:
  E.Canon{cap, o, l, m, f, xs, x} = c
  x

def c_removed(-K: Data, -V: Data, c: E.Canonical<K, V>) -> E.Canonical<K, V>:
  E.Canon{cap, o, l, T.Counts{i, e, r, h, m}, f, xs, x} = c
  E.Canon{cap, o, l, T.Counts{i, e, Word.inc(64n, r), h, m}, f, xs, x}

def remove_choice(-K: Data, -V: Data, found: Maybe<&2, T.Entry<K, V>>, kept: E.Canonical<K, V>, dropped: E.Canonical<K, V>) -> E.Canonical<K, V>:
  match found:
    case None{}: kept
    case Some{entry}: dropped

def c_remove(~K: Data, ~same: K -> K -> Bool, -V: Data, +c: E.Canonical<K, V>, +key: K) -> E.Canonical<K, V>:
  remove_choice(K, V, canonical_find(~K, ~same, V, c, key), c, c_drop(~K, ~same, V, c_removed(K, V, c), key))

def remove_found_transform(~K: Data, ~same: K -> K -> Bool, ~refl: reflects(~K, ~same), -V: Data, +cap: Nat, +b: List<&2, T.Entry<K, V>>, +o: List<&2, K>, +l: T.Int64, +i: Word(64n), +e: Word(64n), +r: Word(64n), +h: Word(64n), +m: Word(64n), +f: Bool, +key: K, found: Maybe<&2, T.Entry<K, V>>) -> {E.canonical(~K, ~same, V, O.observed_state(K, V, S.remove_decision(~K, ~same, V, S.Abstract{cap, b, o, l, T.Counts{i, e, r, h, m}, f}, key, found))) == remove_choice(K, V, found, E.canonical(~K, ~same, V, S.Abstract{cap, b, o, l, T.Counts{i, e, r, h, m}, f}), c_drop(~K, ~same, V, c_removed(K, V, E.canonical(~K, ~same, V, S.Abstract{cap, b, o, l, T.Counts{i, e, r, h, m}, f})), key)) : E.Canonical<K, V>}:
  match found:
    case None{}: {==}
    case Some{entry}: drop_transform(~K, ~same, ~refl, V, cap, b, o, l, T.Counts{i, e, Word.inc(64n, r), h, m}, f, key)

# Canonical effect of the specification's Remove (either branch).
def remove_transform(~K: Data, ~same: K -> K -> Bool, ~refl: reflects(~K, ~same), -V: Data, s: S.Model<K, V>, +key: K) -> {E.canonical(~K, ~same, V, O.observed_state(K, V, S.remove(~K, ~same, V, s, key))) == c_remove(~K, ~same, V, E.canonical(~K, ~same, V, s), key) : E.Canonical<K, V>}:
  S.Abstract{+cap, +b, +o, +l, T.Counts{+i, +e, +r, +h, +m}, +f} = s
  %Equal.sym(Maybe<&2, T.Entry<K, V>>, S.find(~K, ~same, V, b, key), canonical_find(~K, ~same, V, E.canonical(~K, ~same, V, S.Abstract{cap, b, o, l, T.Counts{i, e, r, h, m}, f}), key), find_canonical(~K, ~same, ~refl, V, S.Abstract{cap, b, o, l, T.Counts{i, e, r, h, m}, f}, key)) : {E.canonical(~K, ~same, V, O.observed_state(K, V, S.remove_decision(~K, ~same, V, S.Abstract{cap, b, o, l, T.Counts{i, e, r, h, m}, f}, key, _))) == c_remove(~K, ~same, V, E.canonical(~K, ~same, V, S.Abstract{cap, b, o, l, T.Counts{i, e, r, h, m}, f}), key) : E.Canonical<K, V>}
  remove_found_transform(~K, ~same, ~refl, V, cap, b, o, l, i, e, r, h, m, f, key, canonical_find(~K, ~same, V, E.canonical(~K, ~same, V, S.Abstract{cap, b, o, l, T.Counts{i, e, r, h, m}, f}), key))

def remove_congruence(~K: Data, ~same: K -> K -> Bool, ~refl: reflects(~K, ~same), -V: Data, +a: S.Model<K, V>, +b: S.Model<K, V>, +key: K, related: E.states(~K, ~same, V, a, b)) -> E.states(~K, ~same, V, O.observed_state(K, V, S.remove(~K, ~same, V, a, key)), O.observed_state(K, V, S.remove(~K, ~same, V, b, key))):
  Equal.trans(E.Canonical<K, V>, E.canonical(~K, ~same, V, O.observed_state(K, V, S.remove(~K, ~same, V, a, key))), c_remove(~K, ~same, V, E.canonical(~K, ~same, V, a), key), E.canonical(~K, ~same, V, O.observed_state(K, V, S.remove(~K, ~same, V, b, key))), remove_transform(~K, ~same, ~refl, V, a, key), Equal.trans(E.Canonical<K, V>, c_remove(~K, ~same, V, E.canonical(~K, ~same, V, a), key), c_remove(~K, ~same, V, E.canonical(~K, ~same, V, b), key), E.canonical(~K, ~same, V, O.observed_state(K, V, S.remove(~K, ~same, V, b, key))), Equal.cong(E.Canonical<K, V>, E.Canonical<K, V>, c => c_remove(~K, ~same, V, c, key), E.canonical(~K, ~same, V, a), E.canonical(~K, ~same, V, b), related), Equal.sym(E.Canonical<K, V>, E.canonical(~K, ~same, V, O.observed_state(K, V, S.remove(~K, ~same, V, b, key))), c_remove(~K, ~same, V, E.canonical(~K, ~same, V, b), key), remove_transform(~K, ~same, ~refl, V, b, key))))
