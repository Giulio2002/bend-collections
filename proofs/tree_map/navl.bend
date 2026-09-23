import Base
import ../lib/logic.bend as L
import ../lib/order.bend as O
import ../spec/common.bend as SC
import ../spec/tree_map.bend as S
import ../../src/containers/balanced_search_tree.bend as M
import ./state.bend as ST
import ./ord.bend as OR

# The specification's first_where and last_where over sorted entries split
# by a key k: entries below k never qualify upward and always downward,
# entries above k the other way round. (source: tools/generators/tm_hand/navl.src)


def fw_app_c(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +k: K, +incl: Bool, +e: M.Entry<K, V>, +t: List<&2, M.Entry<K, V>>, +ys: List<&2, M.Entry<K, V>>, +b: Bool, +hb: {S.ordering_ok(cmp(k, S.key(K, V, e)), incl) == b : Bool}, +ih: {S.first_where(~K, ~V, ~cmp, k, incl, SC.append(M.Entry<K, V>, t, ys)) == OR.orm(M.Entry<K, V>, S.first_where(~K, ~V, ~cmp, k, incl, t), S.first_where(~K, ~V, ~cmp, k, incl, ys)) : Maybe<&2, M.Entry<K, V>>}) -> {S.first_where(~K, ~V, ~cmp, k, incl, SC.append(M.Entry<K, V>, Con{e, t}, ys)) == OR.orm(M.Entry<K, V>, S.first_where(~K, ~V, ~cmp, k, incl, Con{e, t}), S.first_where(~K, ~V, ~cmp, k, incl, ys)) : Maybe<&2, M.Entry<K, V>>}:
  match b:
    case True{}:
      %Equal.sym(Bool, S.ordering_ok(cmp(k, S.key(K, V, e)), incl), True{}, hb) : {S.pick(Maybe<&2, M.Entry<K, V>>, _, Some{e}, S.first_where(~K, ~V, ~cmp, k, incl, SC.append(M.Entry<K, V>, t, ys))) == OR.orm(M.Entry<K, V>, S.pick(Maybe<&2, M.Entry<K, V>>, _, Some{e}, S.first_where(~K, ~V, ~cmp, k, incl, t)), S.first_where(~K, ~V, ~cmp, k, incl, ys)) : Maybe<&2, M.Entry<K, V>>}
      {==}
    case False{}:
      %Equal.sym(Bool, S.ordering_ok(cmp(k, S.key(K, V, e)), incl), False{}, hb) : {S.pick(Maybe<&2, M.Entry<K, V>>, _, Some{e}, S.first_where(~K, ~V, ~cmp, k, incl, SC.append(M.Entry<K, V>, t, ys))) == OR.orm(M.Entry<K, V>, S.pick(Maybe<&2, M.Entry<K, V>>, _, Some{e}, S.first_where(~K, ~V, ~cmp, k, incl, t)), S.first_where(~K, ~V, ~cmp, k, incl, ys)) : Maybe<&2, M.Entry<K, V>>}
      ih

def fw_app(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +k: K, +incl: Bool, +xs: List<&2, M.Entry<K, V>>, +ys: List<&2, M.Entry<K, V>>) -> {S.first_where(~K, ~V, ~cmp, k, incl, SC.append(M.Entry<K, V>, xs, ys)) == OR.orm(M.Entry<K, V>, S.first_where(~K, ~V, ~cmp, k, incl, xs), S.first_where(~K, ~V, ~cmp, k, incl, ys)) : Maybe<&2, M.Entry<K, V>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      fw_app_c(~K, ~V, ~cmp, k, incl, e, t, ys, S.ordering_ok(cmp(k, S.key(K, V, e)), incl), {==}, fw_app(~K, ~V, ~cmp, k, incl, t, ys))

# nothing below k is at or above it
def fw_none(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +k: K, +incl: Bool, +es: List<&2, M.Entry<K, V>>, +h: {OR.ltall(~K, ~V, ~cmp, k, es) == True{} : Bool}) -> {S.first_where(~K, ~V, ~cmp, k, incl, es) == None{} : Maybe<&2, M.Entry<K, V>>}:
  match es:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      %Equal.sym(Cmp, cmp(k, S.key(K, V, e)), GT{}, OR.lt_gt(~K, ~cmp, ~o, S.key(K, V, e), k, L.and_left(Cmp.is_lt(cmp(S.key(K, V, e), k)), OR.ltall(~K, ~V, ~cmp, k, t), h))) : {S.pick(Maybe<&2, M.Entry<K, V>>, S.ordering_ok(_, incl), Some{e}, S.first_where(~K, ~V, ~cmp, k, incl, t)) == None{} : Maybe<&2, M.Entry<K, V>>}
      fw_none(~K, ~V, ~cmp, ~o, k, incl, t, L.and_right(Cmp.is_lt(cmp(S.key(K, V, e), k)), OR.ltall(~K, ~V, ~cmp, k, t), h))

# everything above k qualifies: the first
def fw_head(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +k: K, +incl: Bool, +es: List<&2, M.Entry<K, V>>, +h: {OR.gtall(~K, ~V, ~cmp, k, es) == True{} : Bool}) -> {S.first_where(~K, ~V, ~cmp, k, incl, es) == S.head(M.Entry<K, V>, es) : Maybe<&2, M.Entry<K, V>>}:
  match es:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      %Equal.sym(Cmp, cmp(k, S.key(K, V, e)), LT{}, O.lt_is(cmp(k, S.key(K, V, e)), L.and_left(Cmp.is_lt(cmp(k, S.key(K, V, e))), OR.gtall(~K, ~V, ~cmp, k, t), h))) : {S.pick(Maybe<&2, M.Entry<K, V>>, S.ordering_ok(_, incl), Some{e}, S.first_where(~K, ~V, ~cmp, k, incl, t)) == Some{e} : Maybe<&2, M.Entry<K, V>>}
      {==}

def lw_app(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +k: K, +incl: Bool, +xs: List<&2, M.Entry<K, V>>, +ys: List<&2, M.Entry<K, V>>, +b: Maybe<&2, M.Entry<K, V>>) -> {S.last_where(~K, ~V, ~cmp, k, incl, SC.append(M.Entry<K, V>, xs, ys), b) == S.last_where(~K, ~V, ~cmp, k, incl, ys, S.last_where(~K, ~V, ~cmp, k, incl, xs, b)) : Maybe<&2, M.Entry<K, V>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      lw_app(~K, ~V, ~cmp, k, incl, t, ys, S.pick(Maybe<&2, M.Entry<K, V>>, S.ordering_ok(cmp(S.key(K, V, e), k), incl), Some{e}, b))

# nothing above k is at or below it: the candidate stays
def lw_none(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +k: K, +incl: Bool, +es: List<&2, M.Entry<K, V>>, +b: Maybe<&2, M.Entry<K, V>>, +h: {OR.gtall(~K, ~V, ~cmp, k, es) == True{} : Bool}) -> {S.last_where(~K, ~V, ~cmp, k, incl, es, b) == b : Maybe<&2, M.Entry<K, V>>}:
  match es:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      %Equal.sym(Cmp, cmp(S.key(K, V, e), k), GT{}, OR.lt_gt(~K, ~cmp, ~o, k, S.key(K, V, e), L.and_left(Cmp.is_lt(cmp(k, S.key(K, V, e))), OR.gtall(~K, ~V, ~cmp, k, t), h))) : {S.last_where(~K, ~V, ~cmp, k, incl, t, S.pick(Maybe<&2, M.Entry<K, V>>, S.ordering_ok(_, incl), Some{e}, b)) == b : Maybe<&2, M.Entry<K, V>>}
      lw_none(~K, ~V, ~cmp, ~o, k, incl, t, b, L.and_right(Cmp.is_lt(cmp(k, S.key(K, V, e))), OR.gtall(~K, ~V, ~cmp, k, t), h))

def last_orm(-K: Data, -V: Data, +u: List<&2, M.Entry<K, V>>, +e: M.Entry<K, V>, +a: Maybe<&2, M.Entry<K, V>>, +b: Maybe<&2, M.Entry<K, V>>) -> {OR.orm(M.Entry<K, V>, S.last(M.Entry<K, V>, Con{e, u}), a) == OR.orm(M.Entry<K, V>, S.last(M.Entry<K, V>, Con{e, u}), b) : Maybe<&2, M.Entry<K, V>>}:
  match u:
    case Nil{}:
      {==}
    case Con{+e2, +u2}:
      last_orm(K, V, u2, e2, a, b)

def lw_all_c(-K: Data, -V: Data, +e: M.Entry<K, V>, +t: List<&2, M.Entry<K, V>>, +b: Maybe<&2, M.Entry<K, V>>) -> {OR.orm(M.Entry<K, V>, S.last(M.Entry<K, V>, t), Some{e}) == OR.orm(M.Entry<K, V>, S.last(M.Entry<K, V>, Con{e, t}), b) : Maybe<&2, M.Entry<K, V>>}:
  match t:
    case Nil{}:
      {==}
    case Con{+e2, +u}:
      last_orm(K, V, u, e2, Some{e}, b)

# everything below k qualifies: the last, or the candidate when none
def lw_all(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +k: K, +incl: Bool, +es: List<&2, M.Entry<K, V>>, +b: Maybe<&2, M.Entry<K, V>>, +h: {OR.ltall(~K, ~V, ~cmp, k, es) == True{} : Bool}) -> {S.last_where(~K, ~V, ~cmp, k, incl, es, b) == OR.orm(M.Entry<K, V>, S.last(M.Entry<K, V>, es), b) : Maybe<&2, M.Entry<K, V>>}:
  match es:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      %Equal.sym(Cmp, cmp(S.key(K, V, e), k), LT{}, O.lt_is(cmp(S.key(K, V, e), k), L.and_left(Cmp.is_lt(cmp(S.key(K, V, e), k)), OR.ltall(~K, ~V, ~cmp, k, t), h))) : {S.last_where(~K, ~V, ~cmp, k, incl, t, S.pick(Maybe<&2, M.Entry<K, V>>, S.ordering_ok(_, incl), Some{e}, b)) == OR.orm(M.Entry<K, V>, S.last(M.Entry<K, V>, Con{e, t}), b) : Maybe<&2, M.Entry<K, V>>}
      %Equal.sym(Maybe<&2, M.Entry<K, V>>, S.last_where(~K, ~V, ~cmp, k, incl, t, Some{e}), OR.orm(M.Entry<K, V>, S.last(M.Entry<K, V>, t), Some{e}), lw_all(~K, ~V, ~cmp, k, incl, t, Some{e}, L.and_right(Cmp.is_lt(cmp(S.key(K, V, e), k)), OR.ltall(~K, ~V, ~cmp, k, t), h))) : {_ == OR.orm(M.Entry<K, V>, S.last(M.Entry<K, V>, Con{e, t}), b) : Maybe<&2, M.Entry<K, V>>}
      lw_all_c(K, V, e, t, b)

def ltall_app(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +k: K, +xs: List<&2, M.Entry<K, V>>, +ys: List<&2, M.Entry<K, V>>, +hx: {OR.ltall(~K, ~V, ~cmp, k, xs) == True{} : Bool}, +hy: {OR.ltall(~K, ~V, ~cmp, k, ys) == True{} : Bool}) -> {OR.ltall(~K, ~V, ~cmp, k, SC.append(M.Entry<K, V>, xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      hy
    case Con{+e, +t}:
      L.and_intro(Cmp.is_lt(cmp(S.key(K, V, e), k)), OR.ltall(~K, ~V, ~cmp, k, SC.append(M.Entry<K, V>, t, ys)), L.and_left(Cmp.is_lt(cmp(S.key(K, V, e), k)), OR.ltall(~K, ~V, ~cmp, k, t), hx), ltall_app(~K, ~V, ~cmp, k, t, ys, L.and_right(Cmp.is_lt(cmp(S.key(K, V, e), k)), OR.ltall(~K, ~V, ~cmp, k, t), hx), hy))
