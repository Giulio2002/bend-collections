import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/order.bend as O
import ../../spec/common.bend as SC
import ../../spec/balanced_search_tree.bend as S
import ../../src/balanced_search_tree.bend as B
import ../../types/balanced_search_tree.bend as E
import ./sorted.bend as SO

# The specification's map operations on a list split around an entry, and
# their preservation of strict sortedness and length bookkeeping.

def orM(-V: Data, a: Maybe<&2, V>, b: Maybe<&2, V>) -> Maybe<&2, V>:
  match a:
    case None{}:
      b
    case Some{x}:
      Some{x}

# ---- insertion ----

def ins_left_c(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +a: E.Entry<K, V>, +t: List<&2, E.Entry<K, V>>, +e: E.Entry<K, V>, +r: List<&2, E.Entry<K, V>>, +k: K, +v: V, c: Cmp, +ec: {cmp(k, E.key(K, V, a)) == c : Cmp}, +ih: {S.ins(~K, ~cmp, V, k, v, SC.append(E.Entry<K, V>, t, Con{e, r})) == SC.append(E.Entry<K, V>, S.ins(~K, ~cmp, V, k, v, t), Con{e, r}) : List<&2, E.Entry<K, V>>}) -> {S.ins(~K, ~cmp, V, k, v, SC.append(E.Entry<K, V>, Con{a, t}, Con{e, r})) == SC.append(E.Entry<K, V>, S.ins(~K, ~cmp, V, k, v, Con{a, t}), Con{e, r}) : List<&2, E.Entry<K, V>>}:
  match c:
    case LT{}:
      %Equal.sym(Cmp, cmp(k, E.key(K, V, a)), LT{}, ec) : {S.ins_at(~K, ~cmp, V, _, k, v, a, SC.append(E.Entry<K, V>, t, Con{e, r}), S.ins(~K, ~cmp, V, k, v, SC.append(E.Entry<K, V>, t, Con{e, r}))) == SC.append(E.Entry<K, V>, S.ins_at(~K, ~cmp, V, _, k, v, a, t, S.ins(~K, ~cmp, V, k, v, t)), Con{e, r}) : List<&2, E.Entry<K, V>>}
      {==}
    case EQ{}:
      %Equal.sym(Cmp, cmp(k, E.key(K, V, a)), EQ{}, ec) : {S.ins_at(~K, ~cmp, V, _, k, v, a, SC.append(E.Entry<K, V>, t, Con{e, r}), S.ins(~K, ~cmp, V, k, v, SC.append(E.Entry<K, V>, t, Con{e, r}))) == SC.append(E.Entry<K, V>, S.ins_at(~K, ~cmp, V, _, k, v, a, t, S.ins(~K, ~cmp, V, k, v, t)), Con{e, r}) : List<&2, E.Entry<K, V>>}
      {==}
    case GT{}:
      %Equal.sym(Cmp, cmp(k, E.key(K, V, a)), GT{}, ec) : {S.ins_at(~K, ~cmp, V, _, k, v, a, SC.append(E.Entry<K, V>, t, Con{e, r}), S.ins(~K, ~cmp, V, k, v, SC.append(E.Entry<K, V>, t, Con{e, r}))) == SC.append(E.Entry<K, V>, S.ins_at(~K, ~cmp, V, _, k, v, a, t, S.ins(~K, ~cmp, V, k, v, t)), Con{e, r}) : List<&2, E.Entry<K, V>>}
      LL.cons_cong(E.Entry<K, V>, a, S.ins(~K, ~cmp, V, k, v, SC.append(E.Entry<K, V>, t, Con{e, r})), SC.append(E.Entry<K, V>, S.ins(~K, ~cmp, V, k, v, t), Con{e, r}), ih)

# Inserting a key below e into A ++ [e] ++ R happens inside A.
def ins_left(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +xs: List<&2, E.Entry<K, V>>, +e: E.Entry<K, V>, +r: List<&2, E.Entry<K, V>>, +k: K, +v: V, +h: {cmp(k, E.key(K, V, e)) == LT{} : Cmp}) -> {S.ins(~K, ~cmp, V, k, v, SC.append(E.Entry<K, V>, xs, Con{e, r})) == SC.append(E.Entry<K, V>, S.ins(~K, ~cmp, V, k, v, xs), Con{e, r}) : List<&2, E.Entry<K, V>>}:
  match xs:
    case Nil{}:
      %Equal.sym(Cmp, cmp(k, E.key(K, V, e)), LT{}, h) : {S.ins_at(~K, ~cmp, V, _, k, v, e, r, S.ins(~K, ~cmp, V, k, v, r)) == Con{E.Entry{k, v}, Con{e, r}} : List<&2, E.Entry<K, V>>}
      {==}
    case Con{a, t}:
      ins_left_c(~K, ~cmp, V, a, t, e, r, k, v, cmp(k, E.key(K, V, a)), {==}, ins_left(~K, ~cmp, V, t, e, r, k, v, h))

# Inserting a key above all of A passes over A.
def ins_pass(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), -V: Data, +xs: List<&2, E.Entry<K, V>>, +ys: List<&2, E.Entry<K, V>>, +k: K, +v: V, +h: {SO.below(~K, ~cmp, V, xs, k) == True{} : Bool}) -> {S.ins(~K, ~cmp, V, k, v, SC.append(E.Entry<K, V>, xs, ys)) == SC.append(E.Entry<K, V>, xs, S.ins(~K, ~cmp, V, k, v, ys)) : List<&2, E.Entry<K, V>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{a, t}:
      %Equal.sym(Cmp, cmp(k, E.key(K, V, a)), GT{}, SO.gt_of_lt(~K, ~cmp, ~o, E.key(K, V, a), k, SO.bl_head(~K, ~cmp, V, a, t, k, h))) : {S.ins_at(~K, ~cmp, V, _, k, v, a, SC.append(E.Entry<K, V>, t, ys), S.ins(~K, ~cmp, V, k, v, SC.append(E.Entry<K, V>, t, ys))) == Con{a, SC.append(E.Entry<K, V>, t, S.ins(~K, ~cmp, V, k, v, ys))} : List<&2, E.Entry<K, V>>}
      LL.cons_cong(E.Entry<K, V>, a, S.ins(~K, ~cmp, V, k, v, SC.append(E.Entry<K, V>, t, ys)), SC.append(E.Entry<K, V>, t, S.ins(~K, ~cmp, V, k, v, ys)), ins_pass(~K, ~cmp, ~o, V, t, ys, k, v, SO.bl_tail(~K, ~cmp, V, a, t, k, h)))

def ins_eq(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +e: E.Entry<K, V>, +r: List<&2, E.Entry<K, V>>, +k: K, +v: V, +h: {cmp(k, E.key(K, V, e)) == EQ{} : Cmp}) -> {S.ins(~K, ~cmp, V, k, v, Con{e, r}) == Con{E.Entry{k, v}, r} : List<&2, E.Entry<K, V>>}:
  %Equal.sym(Cmp, cmp(k, E.key(K, V, e)), EQ{}, h) : {S.ins_at(~K, ~cmp, V, _, k, v, e, r, S.ins(~K, ~cmp, V, k, v, r)) == Con{E.Entry{k, v}, r} : List<&2, E.Entry<K, V>>}
  {==}

def ins_gt(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +e: E.Entry<K, V>, +r: List<&2, E.Entry<K, V>>, +k: K, +v: V, +h: {cmp(k, E.key(K, V, e)) == GT{} : Cmp}) -> {S.ins(~K, ~cmp, V, k, v, Con{e, r}) == Con{e, S.ins(~K, ~cmp, V, k, v, r)} : List<&2, E.Entry<K, V>>}:
  %Equal.sym(Cmp, cmp(k, E.key(K, V, e)), GT{}, h) : {S.ins_at(~K, ~cmp, V, _, k, v, e, r, S.ins(~K, ~cmp, V, k, v, r)) == Con{e, S.ins(~K, ~cmp, V, k, v, r)} : List<&2, E.Entry<K, V>>}
  {==}

# ---- deletion ----

def keep_app(-K: Data, -V: Data, b: Bool, +a: E.Entry<K, V>, +xs: List<&2, E.Entry<K, V>>, +ys: List<&2, E.Entry<K, V>>) -> {S.keep_at(K, V, b, a, SC.append(E.Entry<K, V>, xs, ys)) == SC.append(E.Entry<K, V>, S.keep_at(K, V, b, a, xs), ys) : List<&2, E.Entry<K, V>>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def del_app(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +xs: List<&2, E.Entry<K, V>>, +ys: List<&2, E.Entry<K, V>>, +k: K) -> {S.del(~K, ~cmp, V, k, SC.append(E.Entry<K, V>, xs, ys)) == SC.append(E.Entry<K, V>, S.del(~K, ~cmp, V, k, xs), S.del(~K, ~cmp, V, k, ys)) : List<&2, E.Entry<K, V>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{a, t}:
      Equal.trans(List<&2, E.Entry<K, V>>, S.keep_at(K, V, S.keep(cmp(k, E.key(K, V, a))), a, S.del(~K, ~cmp, V, k, SC.append(E.Entry<K, V>, t, ys))), S.keep_at(K, V, S.keep(cmp(k, E.key(K, V, a))), a, SC.append(E.Entry<K, V>, S.del(~K, ~cmp, V, k, t), S.del(~K, ~cmp, V, k, ys))), SC.append(E.Entry<K, V>, S.keep_at(K, V, S.keep(cmp(k, E.key(K, V, a))), a, S.del(~K, ~cmp, V, k, t)), S.del(~K, ~cmp, V, k, ys)),
        Equal.cong(List<&2, E.Entry<K, V>>, List<&2, E.Entry<K, V>>, z => S.keep_at(K, V, S.keep(cmp(k, E.key(K, V, a))), a, z), S.del(~K, ~cmp, V, k, SC.append(E.Entry<K, V>, t, ys)), SC.append(E.Entry<K, V>, S.del(~K, ~cmp, V, k, t), S.del(~K, ~cmp, V, k, ys)), del_app(~K, ~cmp, V, t, ys, k)),
        keep_app(K, V, S.keep(cmp(k, E.key(K, V, a))), a, S.del(~K, ~cmp, V, k, t), S.del(~K, ~cmp, V, k, ys)))

def del_below(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), -V: Data, +xs: List<&2, E.Entry<K, V>>, +k: K, +h: {SO.below(~K, ~cmp, V, xs, k) == True{} : Bool}) -> {S.del(~K, ~cmp, V, k, xs) == xs : List<&2, E.Entry<K, V>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{a, t}:
      %Equal.sym(Cmp, cmp(k, E.key(K, V, a)), GT{}, SO.gt_of_lt(~K, ~cmp, ~o, E.key(K, V, a), k, SO.bl_head(~K, ~cmp, V, a, t, k, h))) : {S.keep_at(K, V, S.keep(_), a, S.del(~K, ~cmp, V, k, t)) == Con{a, t} : List<&2, E.Entry<K, V>>}
      LL.cons_cong(E.Entry<K, V>, a, S.del(~K, ~cmp, V, k, t), t, del_below(~K, ~cmp, ~o, V, t, k, SO.bl_tail(~K, ~cmp, V, a, t, k, h)))

def del_above(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +xs: List<&2, E.Entry<K, V>>, +k: K, +h: {SO.above(~K, ~cmp, V, xs, k) == True{} : Bool}) -> {S.del(~K, ~cmp, V, k, xs) == xs : List<&2, E.Entry<K, V>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{a, t}:
      %Equal.sym(Cmp, cmp(k, E.key(K, V, a)), LT{}, SO.ab_head(~K, ~cmp, V, a, t, k, h)) : {S.keep_at(K, V, S.keep(_), a, S.del(~K, ~cmp, V, k, t)) == Con{a, t} : List<&2, E.Entry<K, V>>}
      LL.cons_cong(E.Entry<K, V>, a, S.del(~K, ~cmp, V, k, t), t, del_above(~K, ~cmp, V, t, k, SO.ab_tail(~K, ~cmp, V, a, t, k, h)))

def del_eq(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +e: E.Entry<K, V>, +r: List<&2, E.Entry<K, V>>, +k: K, +h: {cmp(k, E.key(K, V, e)) == EQ{} : Cmp}) -> {S.del(~K, ~cmp, V, k, Con{e, r}) == S.del(~K, ~cmp, V, k, r) : List<&2, E.Entry<K, V>>}:
  %Equal.sym(Cmp, cmp(k, E.key(K, V, e)), EQ{}, h) : {S.keep_at(K, V, S.keep(_), e, S.del(~K, ~cmp, V, k, r)) == S.del(~K, ~cmp, V, k, r) : List<&2, E.Entry<K, V>>}
  {==}

def del_lt(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +e: E.Entry<K, V>, +r: List<&2, E.Entry<K, V>>, +k: K, +h: {cmp(k, E.key(K, V, e)) == LT{} : Cmp}) -> {S.del(~K, ~cmp, V, k, Con{e, r}) == Con{e, S.del(~K, ~cmp, V, k, r)} : List<&2, E.Entry<K, V>>}:
  %Equal.sym(Cmp, cmp(k, E.key(K, V, e)), LT{}, h) : {S.keep_at(K, V, S.keep(_), e, S.del(~K, ~cmp, V, k, r)) == Con{e, S.del(~K, ~cmp, V, k, r)} : List<&2, E.Entry<K, V>>}
  {==}

def del_gt(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +e: E.Entry<K, V>, +r: List<&2, E.Entry<K, V>>, +k: K, +h: {cmp(k, E.key(K, V, e)) == GT{} : Cmp}) -> {S.del(~K, ~cmp, V, k, Con{e, r}) == Con{e, S.del(~K, ~cmp, V, k, r)} : List<&2, E.Entry<K, V>>}:
  %Equal.sym(Cmp, cmp(k, E.key(K, V, e)), GT{}, h) : {S.keep_at(K, V, S.keep(_), e, S.del(~K, ~cmp, V, k, r)) == Con{e, S.del(~K, ~cmp, V, k, r)} : List<&2, E.Entry<K, V>>}
  {==}

# ---- lookup ----

def find_or(-K: Data, -V: Data, c: Cmp, +a: E.Entry<K, V>, +x: Maybe<&2, V>, +y: Maybe<&2, V>) -> {S.find_at(K, V, c, a, orM(V, x, y)) == orM(V, S.find_at(K, V, c, a, x), y) : Maybe<&2, V>}:
  match c a:
    case EQ{} E.Entry{ak, av}:
      {==}
    case LT{} _:
      {==}
    case GT{} _:
      {==}

def find_app(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +xs: List<&2, E.Entry<K, V>>, +ys: List<&2, E.Entry<K, V>>, +k: K) -> {S.find(~K, ~cmp, V, k, SC.append(E.Entry<K, V>, xs, ys)) == orM(V, S.find(~K, ~cmp, V, k, xs), S.find(~K, ~cmp, V, k, ys)) : Maybe<&2, V>}:
  match xs:
    case Nil{}:
      {==}
    case Con{a, t}:
      Equal.trans(Maybe<&2, V>, S.find_at(K, V, cmp(k, E.key(K, V, a)), a, S.find(~K, ~cmp, V, k, SC.append(E.Entry<K, V>, t, ys))), S.find_at(K, V, cmp(k, E.key(K, V, a)), a, orM(V, S.find(~K, ~cmp, V, k, t), S.find(~K, ~cmp, V, k, ys))), orM(V, S.find_at(K, V, cmp(k, E.key(K, V, a)), a, S.find(~K, ~cmp, V, k, t)), S.find(~K, ~cmp, V, k, ys)),
        Equal.cong(Maybe<&2, V>, Maybe<&2, V>, z => S.find_at(K, V, cmp(k, E.key(K, V, a)), a, z), S.find(~K, ~cmp, V, k, SC.append(E.Entry<K, V>, t, ys)), orM(V, S.find(~K, ~cmp, V, k, t), S.find(~K, ~cmp, V, k, ys)), find_app(~K, ~cmp, V, t, ys, k)),
        find_or(K, V, cmp(k, E.key(K, V, a)), a, S.find(~K, ~cmp, V, k, t), S.find(~K, ~cmp, V, k, ys)))

def find_below(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), -V: Data, +xs: List<&2, E.Entry<K, V>>, +k: K, +h: {SO.below(~K, ~cmp, V, xs, k) == True{} : Bool}) -> {S.find(~K, ~cmp, V, k, xs) == None{} : Maybe<&2, V>}:
  match xs:
    case Nil{}:
      {==}
    case Con{a, t}:
      %Equal.sym(Cmp, cmp(k, E.key(K, V, a)), GT{}, SO.gt_of_lt(~K, ~cmp, ~o, E.key(K, V, a), k, SO.bl_head(~K, ~cmp, V, a, t, k, h))) : {S.find_at(K, V, _, a, S.find(~K, ~cmp, V, k, t)) == None{} : Maybe<&2, V>}
      find_below(~K, ~cmp, ~o, V, t, k, SO.bl_tail(~K, ~cmp, V, a, t, k, h))

def find_above(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +xs: List<&2, E.Entry<K, V>>, +k: K, +h: {SO.above(~K, ~cmp, V, xs, k) == True{} : Bool}) -> {S.find(~K, ~cmp, V, k, xs) == None{} : Maybe<&2, V>}:
  match xs:
    case Nil{}:
      {==}
    case Con{a, t}:
      %Equal.sym(Cmp, cmp(k, E.key(K, V, a)), LT{}, SO.ab_head(~K, ~cmp, V, a, t, k, h)) : {S.find_at(K, V, _, a, S.find(~K, ~cmp, V, k, t)) == None{} : Maybe<&2, V>}
      find_above(~K, ~cmp, V, t, k, SO.ab_tail(~K, ~cmp, V, a, t, k, h))

def find_eq(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +e: E.Entry<K, V>, +r: List<&2, E.Entry<K, V>>, +k: K, +h: {cmp(k, E.key(K, V, e)) == EQ{} : Cmp}) -> {S.find(~K, ~cmp, V, k, Con{e, r}) == Some{E.val(K, V, e)} : Maybe<&2, V>}:
  match e:
    case E.Entry{ek, ev}:
      %Equal.sym(Cmp, cmp(k, ek), EQ{}, h) : {S.find_at(K, V, _, E.Entry{ek, ev}, S.find(~K, ~cmp, V, k, r)) == Some{ev} : Maybe<&2, V>}
      {==}

def find_lt(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +e: E.Entry<K, V>, +r: List<&2, E.Entry<K, V>>, +k: K, +h: {cmp(k, E.key(K, V, e)) == LT{} : Cmp}) -> {S.find(~K, ~cmp, V, k, Con{e, r}) == S.find(~K, ~cmp, V, k, r) : Maybe<&2, V>}:
  %Equal.sym(Cmp, cmp(k, E.key(K, V, e)), LT{}, h) : {S.find_at(K, V, _, e, S.find(~K, ~cmp, V, k, r)) == S.find(~K, ~cmp, V, k, r) : Maybe<&2, V>}
  {==}

def find_gt(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +e: E.Entry<K, V>, +r: List<&2, E.Entry<K, V>>, +k: K, +h: {cmp(k, E.key(K, V, e)) == GT{} : Cmp}) -> {S.find(~K, ~cmp, V, k, Con{e, r}) == S.find(~K, ~cmp, V, k, r) : Maybe<&2, V>}:
  %Equal.sym(Cmp, cmp(k, E.key(K, V, e)), GT{}, h) : {S.find_at(K, V, _, e, S.find(~K, ~cmp, V, k, r)) == S.find(~K, ~cmp, V, k, r) : Maybe<&2, V>}
  {==}

# ---- lower bound ----

def lb_or(-K: Data, -V: Data, c: Cmp, +a: E.Entry<K, V>, +x: Maybe<&2, E.Entry<K, V>>, +y: Maybe<&2, E.Entry<K, V>>) -> {S.lb_at(K, V, c, a, orM(E.Entry<K, V>, x, y)) == orM(E.Entry<K, V>, S.lb_at(K, V, c, a, x), y) : Maybe<&2, E.Entry<K, V>>}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def lower_app(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +xs: List<&2, E.Entry<K, V>>, +ys: List<&2, E.Entry<K, V>>, +k: K) -> {S.lower(~K, ~cmp, V, k, SC.append(E.Entry<K, V>, xs, ys)) == orM(E.Entry<K, V>, S.lower(~K, ~cmp, V, k, xs), S.lower(~K, ~cmp, V, k, ys)) : Maybe<&2, E.Entry<K, V>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{a, t}:
      Equal.trans(Maybe<&2, E.Entry<K, V>>, S.lb_at(K, V, cmp(E.key(K, V, a), k), a, S.lower(~K, ~cmp, V, k, SC.append(E.Entry<K, V>, t, ys))), S.lb_at(K, V, cmp(E.key(K, V, a), k), a, orM(E.Entry<K, V>, S.lower(~K, ~cmp, V, k, t), S.lower(~K, ~cmp, V, k, ys))), orM(E.Entry<K, V>, S.lb_at(K, V, cmp(E.key(K, V, a), k), a, S.lower(~K, ~cmp, V, k, t)), S.lower(~K, ~cmp, V, k, ys)),
        Equal.cong(Maybe<&2, E.Entry<K, V>>, Maybe<&2, E.Entry<K, V>>, z => S.lb_at(K, V, cmp(E.key(K, V, a), k), a, z), S.lower(~K, ~cmp, V, k, SC.append(E.Entry<K, V>, t, ys)), orM(E.Entry<K, V>, S.lower(~K, ~cmp, V, k, t), S.lower(~K, ~cmp, V, k, ys)), lower_app(~K, ~cmp, V, t, ys, k)),
        lb_or(K, V, cmp(E.key(K, V, a), k), a, S.lower(~K, ~cmp, V, k, t), S.lower(~K, ~cmp, V, k, ys)))

def lower_below(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +xs: List<&2, E.Entry<K, V>>, +k: K, +h: {SO.below(~K, ~cmp, V, xs, k) == True{} : Bool}) -> {S.lower(~K, ~cmp, V, k, xs) == None{} : Maybe<&2, E.Entry<K, V>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{a, t}:
      %Equal.sym(Cmp, cmp(E.key(K, V, a), k), LT{}, SO.bl_head(~K, ~cmp, V, a, t, k, h)) : {S.lb_at(K, V, _, a, S.lower(~K, ~cmp, V, k, t)) == None{} : Maybe<&2, E.Entry<K, V>>}
      lower_below(~K, ~cmp, V, t, k, SO.bl_tail(~K, ~cmp, V, a, t, k, h))

def lower_lt(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +e: E.Entry<K, V>, +r: List<&2, E.Entry<K, V>>, +k: K, +h: {cmp(E.key(K, V, e), k) == LT{} : Cmp}) -> {S.lower(~K, ~cmp, V, k, Con{e, r}) == S.lower(~K, ~cmp, V, k, r) : Maybe<&2, E.Entry<K, V>>}:
  %Equal.sym(Cmp, cmp(E.key(K, V, e), k), LT{}, h) : {S.lb_at(K, V, _, e, S.lower(~K, ~cmp, V, k, r)) == S.lower(~K, ~cmp, V, k, r) : Maybe<&2, E.Entry<K, V>>}
  {==}

def lower_eq(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +e: E.Entry<K, V>, +r: List<&2, E.Entry<K, V>>, +k: K, +h: {cmp(E.key(K, V, e), k) == EQ{} : Cmp}) -> {S.lower(~K, ~cmp, V, k, Con{e, r}) == Some{e} : Maybe<&2, E.Entry<K, V>>}:
  %Equal.sym(Cmp, cmp(E.key(K, V, e), k), EQ{}, h) : {S.lb_at(K, V, _, e, S.lower(~K, ~cmp, V, k, r)) == Some{e} : Maybe<&2, E.Entry<K, V>>}
  {==}

def lower_gt(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +e: E.Entry<K, V>, +r: List<&2, E.Entry<K, V>>, +k: K, +h: {cmp(E.key(K, V, e), k) == GT{} : Cmp}) -> {S.lower(~K, ~cmp, V, k, Con{e, r}) == Some{e} : Maybe<&2, E.Entry<K, V>>}:
  %Equal.sym(Cmp, cmp(E.key(K, V, e), k), GT{}, h) : {S.lb_at(K, V, _, e, S.lower(~K, ~cmp, V, k, r)) == Some{e} : Maybe<&2, E.Entry<K, V>>}
  {==}

# ---- range ----

def range_app(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +xs: List<&2, E.Entry<K, V>>, +ys: List<&2, E.Entry<K, V>>, +lo: K, +hi: K) -> {S.range(~K, ~cmp, V, lo, hi, SC.append(E.Entry<K, V>, xs, ys)) == SC.append(E.Entry<K, V>, S.range(~K, ~cmp, V, lo, hi, xs), S.range(~K, ~cmp, V, lo, hi, ys)) : List<&2, E.Entry<K, V>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{a, t}:
      Equal.trans(List<&2, E.Entry<K, V>>, S.keep_at(K, V, S.in_range(cmp(lo, E.key(K, V, a)), cmp(E.key(K, V, a), hi)), a, S.range(~K, ~cmp, V, lo, hi, SC.append(E.Entry<K, V>, t, ys))), S.keep_at(K, V, S.in_range(cmp(lo, E.key(K, V, a)), cmp(E.key(K, V, a), hi)), a, SC.append(E.Entry<K, V>, S.range(~K, ~cmp, V, lo, hi, t), S.range(~K, ~cmp, V, lo, hi, ys))), SC.append(E.Entry<K, V>, S.keep_at(K, V, S.in_range(cmp(lo, E.key(K, V, a)), cmp(E.key(K, V, a), hi)), a, S.range(~K, ~cmp, V, lo, hi, t)), S.range(~K, ~cmp, V, lo, hi, ys)),
        Equal.cong(List<&2, E.Entry<K, V>>, List<&2, E.Entry<K, V>>, z => S.keep_at(K, V, S.in_range(cmp(lo, E.key(K, V, a)), cmp(E.key(K, V, a), hi)), a, z), S.range(~K, ~cmp, V, lo, hi, SC.append(E.Entry<K, V>, t, ys)), SC.append(E.Entry<K, V>, S.range(~K, ~cmp, V, lo, hi, t), S.range(~K, ~cmp, V, lo, hi, ys)), range_app(~K, ~cmp, V, t, ys, lo, hi)),
        keep_app(K, V, S.in_range(cmp(lo, E.key(K, V, a)), cmp(E.key(K, V, a), hi)), a, S.range(~K, ~cmp, V, lo, hi, t), S.range(~K, ~cmp, V, lo, hi, ys)))

# lo >= x and every key of A < x: none of A is in [lo, hi).
def low_c(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +a: K, +x: K, +lo: K, +ax: {cmp(a, x) == LT{} : Cmp}, +hx: {Cmp.is_lt(cmp(lo, x)) == False{} : Bool}, c: Cmp, +ec: {cmp(lo, a) == c : Cmp}) -> {Cmp.is_gt(cmp(lo, a)) == True{} : Bool}:
  match c:
    case GT{}:
      %Equal.sym(Cmp, cmp(lo, a), GT{}, ec) : {Cmp.is_gt(_) == True{} : Bool}
      {==}
    case LT{}:
      Empty.absurd({Cmp.is_gt(cmp(lo, a)) == True{} : Bool}, L.true_false(Equal.trans(Bool, True{}, Cmp.is_lt(cmp(lo, x)), False{}, Equal.sym(Bool, Cmp.is_lt(cmp(lo, x)), True{}, SO.is_lt_of(cmp(lo, x), SO.lt_trans(~K, ~cmp, ~o, lo, a, x, ec, ax))), hx)))
    case EQ{}:
      Empty.absurd({Cmp.is_gt(cmp(lo, a)) == True{} : Bool}, L.true_false(Equal.trans(Bool, True{}, Cmp.is_lt(cmp(lo, x)), False{}, Equal.sym(Bool, Cmp.is_lt(cmp(lo, x)), True{}, SO.is_lt_of(cmp(lo, x), L.subst(K, z => {cmp(z, x) == LT{} : Cmp}, a, lo, Equal.sym(K, lo, a, O.antisym(~K, ~cmp, o, lo, a, ec)), ax))), hx)))

def range_low(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), -V: Data, +xs: List<&2, E.Entry<K, V>>, +lo: K, +hi: K, +x: K, +h: {SO.below(~K, ~cmp, V, xs, x) == True{} : Bool}, +hx: {Cmp.is_lt(cmp(lo, x)) == False{} : Bool}) -> {S.range(~K, ~cmp, V, lo, hi, xs) == Nil{} : List<&2, E.Entry<K, V>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{a, t}:
      %Equal.sym(Bool, Cmp.is_gt(cmp(lo, E.key(K, V, a))), True{}, low_c(~K, ~cmp, ~o, E.key(K, V, a), x, lo, SO.bl_head(~K, ~cmp, V, a, t, x, h), hx, cmp(lo, E.key(K, V, a)), {==})) : {S.keep_at(K, V, Bool.and(Bool.not(_), Cmp.is_lt(cmp(E.key(K, V, a), hi))), a, S.range(~K, ~cmp, V, lo, hi, t)) == Nil{} : List<&2, E.Entry<K, V>>}
      range_low(~K, ~cmp, ~o, V, t, lo, hi, x, SO.bl_tail(~K, ~cmp, V, a, t, x, h), hx)

# hi <= x and every key of R > x: none of R is in [lo, hi).
def high_c(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +a: K, +x: K, +hi: K, +xa: {cmp(x, a) == LT{} : Cmp}, +hx: {Cmp.is_lt(cmp(x, hi)) == False{} : Bool}, c: Cmp, +ec: {cmp(a, hi) == c : Cmp}) -> {Cmp.is_lt(cmp(a, hi)) == False{} : Bool}:
  match c:
    case LT{}:
      Empty.absurd({Cmp.is_lt(cmp(a, hi)) == False{} : Bool}, L.true_false(Equal.trans(Bool, True{}, Cmp.is_lt(cmp(x, hi)), False{}, Equal.sym(Bool, Cmp.is_lt(cmp(x, hi)), True{}, SO.is_lt_of(cmp(x, hi), SO.lt_trans(~K, ~cmp, ~o, x, a, hi, xa, ec))), hx)))
    case EQ{}:
      %Equal.sym(Cmp, cmp(a, hi), EQ{}, ec) : {Cmp.is_lt(_) == False{} : Bool}
      {==}
    case GT{}:
      %Equal.sym(Cmp, cmp(a, hi), GT{}, ec) : {Cmp.is_lt(_) == False{} : Bool}
      {==}

def and_false(+a: Bool) -> {Bool.and(a, False{}) == False{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def range_high(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), -V: Data, +xs: List<&2, E.Entry<K, V>>, +lo: K, +hi: K, +x: K, +h: {SO.above(~K, ~cmp, V, xs, x) == True{} : Bool}, +hx: {Cmp.is_lt(cmp(x, hi)) == False{} : Bool}) -> {S.range(~K, ~cmp, V, lo, hi, xs) == Nil{} : List<&2, E.Entry<K, V>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{a, t}:
      %Equal.sym(Bool, Cmp.is_lt(cmp(E.key(K, V, a), hi)), False{}, high_c(~K, ~cmp, ~o, E.key(K, V, a), x, hi, SO.ab_head(~K, ~cmp, V, a, t, x, h), hx, cmp(E.key(K, V, a), hi), {==})) : {S.keep_at(K, V, Bool.and(Bool.not(Cmp.is_gt(cmp(lo, E.key(K, V, a)))), _), a, S.range(~K, ~cmp, V, lo, hi, t)) == Nil{} : List<&2, E.Entry<K, V>>}
      %Equal.sym(Bool, Bool.and(Bool.not(Cmp.is_gt(cmp(lo, E.key(K, V, a)))), False{}), False{}, and_false(Bool.not(Cmp.is_gt(cmp(lo, E.key(K, V, a)))))) : {S.keep_at(K, V, _, a, S.range(~K, ~cmp, V, lo, hi, t)) == Nil{} : List<&2, E.Entry<K, V>>}
      range_high(~K, ~cmp, ~o, V, t, lo, hi, x, SO.ab_tail(~K, ~cmp, V, a, t, x, h), hx)

# ---- sortedness is preserved ----

def above_ins_c(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +e: E.Entry<K, V>, +t: List<&2, E.Entry<K, V>>, +k: K, +v: V, +x: K, +h: {SO.above(~K, ~cmp, V, Con{e, t}, x) == True{} : Bool}, +hx: {cmp(x, k) == LT{} : Cmp}, c: Cmp, +ec: {cmp(k, E.key(K, V, e)) == c : Cmp}, +ih: {SO.above(~K, ~cmp, V, S.ins(~K, ~cmp, V, k, v, t), x) == True{} : Bool}) -> {SO.above(~K, ~cmp, V, S.ins(~K, ~cmp, V, k, v, Con{e, t}), x) == True{} : Bool}:
  match c:
    case LT{}:
      %Equal.sym(Cmp, cmp(k, E.key(K, V, e)), LT{}, ec) : {SO.above(~K, ~cmp, V, S.ins_at(~K, ~cmp, V, _, k, v, e, t, S.ins(~K, ~cmp, V, k, v, t)), x) == True{} : Bool}
      L.and_intro(Cmp.is_lt(cmp(x, k)), SO.above(~K, ~cmp, V, Con{e, t}, x), SO.is_lt_of(cmp(x, k), hx), h)
    case EQ{}:
      %Equal.sym(Cmp, cmp(k, E.key(K, V, e)), EQ{}, ec) : {SO.above(~K, ~cmp, V, S.ins_at(~K, ~cmp, V, _, k, v, e, t, S.ins(~K, ~cmp, V, k, v, t)), x) == True{} : Bool}
      L.and_intro(Cmp.is_lt(cmp(x, k)), SO.above(~K, ~cmp, V, t, x), SO.is_lt_of(cmp(x, k), hx), SO.ab_tail(~K, ~cmp, V, e, t, x, h))
    case GT{}:
      %Equal.sym(Cmp, cmp(k, E.key(K, V, e)), GT{}, ec) : {SO.above(~K, ~cmp, V, S.ins_at(~K, ~cmp, V, _, k, v, e, t, S.ins(~K, ~cmp, V, k, v, t)), x) == True{} : Bool}
      L.and_intro(Cmp.is_lt(cmp(x, E.key(K, V, e))), SO.above(~K, ~cmp, V, S.ins(~K, ~cmp, V, k, v, t), x), L.and_left(Cmp.is_lt(cmp(x, E.key(K, V, e))), SO.above(~K, ~cmp, V, t, x), h), ih)

def above_ins(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +xs: List<&2, E.Entry<K, V>>, +k: K, +v: V, +x: K, +h: {SO.above(~K, ~cmp, V, xs, x) == True{} : Bool}, +hx: {cmp(x, k) == LT{} : Cmp}) -> {SO.above(~K, ~cmp, V, S.ins(~K, ~cmp, V, k, v, xs), x) == True{} : Bool}:
  match xs:
    case Nil{}:
      L.and_intro(Cmp.is_lt(cmp(x, k)), True{}, SO.is_lt_of(cmp(x, k), hx), {==})
    case Con{e, t}:
      above_ins_c(~K, ~cmp, V, e, t, k, v, x, h, hx, cmp(k, E.key(K, V, e)), {==}, above_ins(~K, ~cmp, V, t, k, v, x, SO.ab_tail(~K, ~cmp, V, e, t, x, h), hx))

def sorted_ins_c(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), -V: Data, +e: E.Entry<K, V>, +t: List<&2, E.Entry<K, V>>, +k: K, +v: V, +s: {SO.sorted(~K, ~cmp, V, Con{e, t}) == True{} : Bool}, c: Cmp, +ec: {cmp(k, E.key(K, V, e)) == c : Cmp}, +ih: {SO.sorted(~K, ~cmp, V, S.ins(~K, ~cmp, V, k, v, t)) == True{} : Bool}) -> {SO.sorted(~K, ~cmp, V, S.ins(~K, ~cmp, V, k, v, Con{e, t})) == True{} : Bool}:
  match c:
    case LT{}:
      +ab = SO.so_above(~K, ~cmp, V, e, t, s)
      %Equal.sym(Cmp, cmp(k, E.key(K, V, e)), LT{}, ec) : {SO.sorted(~K, ~cmp, V, S.ins_at(~K, ~cmp, V, _, k, v, e, t, S.ins(~K, ~cmp, V, k, v, t))) == True{} : Bool}
      SO.so_mk(~K, ~cmp, V, E.Entry{k, v}, Con{e, t}, L.and_intro(Cmp.is_lt(cmp(k, E.key(K, V, e))), SO.above(~K, ~cmp, V, t, k), SO.is_lt_of(cmp(k, E.key(K, V, e)), ec), SO.above_gt(~K, ~cmp, ~o, V, t, E.key(K, V, e), k, ab, ec)), s)
    case EQ{}:
      +ab = SO.so_above(~K, ~cmp, V, e, t, s)
      %Equal.sym(Cmp, cmp(k, E.key(K, V, e)), EQ{}, ec) : {SO.sorted(~K, ~cmp, V, S.ins_at(~K, ~cmp, V, _, k, v, e, t, S.ins(~K, ~cmp, V, k, v, t))) == True{} : Bool}
      SO.so_mk(~K, ~cmp, V, E.Entry{k, v}, t, L.subst(K, z => {SO.above(~K, ~cmp, V, t, z) == True{} : Bool}, E.key(K, V, e), k, Equal.sym(K, k, E.key(K, V, e), O.antisym(~K, ~cmp, o, k, E.key(K, V, e), ec)), ab), SO.so_tail(~K, ~cmp, V, e, t, s))
    case GT{}:
      +ab = SO.so_above(~K, ~cmp, V, e, t, s)
      %Equal.sym(Cmp, cmp(k, E.key(K, V, e)), GT{}, ec) : {SO.sorted(~K, ~cmp, V, S.ins_at(~K, ~cmp, V, _, k, v, e, t, S.ins(~K, ~cmp, V, k, v, t))) == True{} : Bool}
      SO.so_mk(~K, ~cmp, V, e, S.ins(~K, ~cmp, V, k, v, t), above_ins(~K, ~cmp, V, t, k, v, E.key(K, V, e), ab, SO.lt_of_gt(~K, ~cmp, ~o, k, E.key(K, V, e), ec)), ih)

def sorted_ins(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), -V: Data, +xs: List<&2, E.Entry<K, V>>, +k: K, +v: V, +s: {SO.sorted(~K, ~cmp, V, xs) == True{} : Bool}) -> {SO.sorted(~K, ~cmp, V, S.ins(~K, ~cmp, V, k, v, xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{e, t}:
      sorted_ins_c(~K, ~cmp, ~o, V, e, t, k, v, s, cmp(k, E.key(K, V, e)), {==}, sorted_ins(~K, ~cmp, ~o, V, t, k, v, SO.so_tail(~K, ~cmp, V, e, t, s)))

def above_keep(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, b: Bool, +e: E.Entry<K, V>, +t: List<&2, E.Entry<K, V>>, +x: K, +he: {Cmp.is_lt(cmp(x, E.key(K, V, e))) == True{} : Bool}, +ht: {SO.above(~K, ~cmp, V, t, x) == True{} : Bool}) -> {SO.above(~K, ~cmp, V, S.keep_at(K, V, b, e, t), x) == True{} : Bool}:
  match b:
    case True{}:
      L.and_intro(Cmp.is_lt(cmp(x, E.key(K, V, e))), SO.above(~K, ~cmp, V, t, x), he, ht)
    case False{}:
      ht

def above_del(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +xs: List<&2, E.Entry<K, V>>, +k: K, +x: K, +h: {SO.above(~K, ~cmp, V, xs, x) == True{} : Bool}) -> {SO.above(~K, ~cmp, V, S.del(~K, ~cmp, V, k, xs), x) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{e, t}:
      above_keep(~K, ~cmp, V, S.keep(cmp(k, E.key(K, V, e))), e, S.del(~K, ~cmp, V, k, t), x, L.and_left(Cmp.is_lt(cmp(x, E.key(K, V, e))), SO.above(~K, ~cmp, V, t, x), h), above_del(~K, ~cmp, V, t, k, x, SO.ab_tail(~K, ~cmp, V, e, t, x, h)))

def sorted_keep(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, b: Bool, +e: E.Entry<K, V>, +t: List<&2, E.Entry<K, V>>, +ha: {SO.above(~K, ~cmp, V, t, E.key(K, V, e)) == True{} : Bool}, +ht: {SO.sorted(~K, ~cmp, V, t) == True{} : Bool}) -> {SO.sorted(~K, ~cmp, V, S.keep_at(K, V, b, e, t)) == True{} : Bool}:
  match b:
    case True{}:
      SO.so_mk(~K, ~cmp, V, e, t, ha, ht)
    case False{}:
      ht

def sorted_del(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +xs: List<&2, E.Entry<K, V>>, +k: K, +s: {SO.sorted(~K, ~cmp, V, xs) == True{} : Bool}) -> {SO.sorted(~K, ~cmp, V, S.del(~K, ~cmp, V, k, xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{e, t}:
      sorted_keep(~K, ~cmp, V, S.keep(cmp(k, E.key(K, V, e))), e, S.del(~K, ~cmp, V, k, t), above_del(~K, ~cmp, V, t, k, E.key(K, V, e), SO.so_above(~K, ~cmp, V, e, t, s)), sorted_del(~K, ~cmp, V, t, k, SO.so_tail(~K, ~cmp, V, e, t, s)))

# ---- lengths ----

def grow_succ(-V: Data, m: Maybe<&2, V>, +n: Nat) -> {B.grow(V, m, 1n+n) == 1n+B.grow(V, m, n) : Nat}:
  match m:
    case None{}:
      {==}
    case Some{w}:
      {==}

def len_ins_c(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), -V: Data, +e: E.Entry<K, V>, +t: List<&2, E.Entry<K, V>>, +k: K, +v: V, +s: {SO.sorted(~K, ~cmp, V, Con{e, t}) == True{} : Bool}, c: Cmp, +ec: {cmp(k, E.key(K, V, e)) == c : Cmp}, +ih: {SC.length(E.Entry<K, V>, S.ins(~K, ~cmp, V, k, v, t)) == B.grow(V, S.find(~K, ~cmp, V, k, t), SC.length(E.Entry<K, V>, t)) : Nat}) -> {SC.length(E.Entry<K, V>, S.ins(~K, ~cmp, V, k, v, Con{e, t})) == B.grow(V, S.find(~K, ~cmp, V, k, Con{e, t}), SC.length(E.Entry<K, V>, Con{e, t})) : Nat}:
  match c:
    case LT{}:
      %Equal.sym(List<&2, E.Entry<K, V>>, S.ins(~K, ~cmp, V, k, v, Con{e, t}), Con{E.Entry{k, v}, Con{e, t}}, ins_left(~K, ~cmp, V, Nil{}, e, t, k, v, ec)) : {SC.length(E.Entry<K, V>, _) == B.grow(V, S.find(~K, ~cmp, V, k, Con{e, t}), 1n+SC.length(E.Entry<K, V>, t)) : Nat}
      %Equal.sym(Maybe<&2, V>, S.find(~K, ~cmp, V, k, Con{e, t}), S.find(~K, ~cmp, V, k, t), find_lt(~K, ~cmp, V, e, t, k, ec)) : {2n+SC.length(E.Entry<K, V>, t) == B.grow(V, _, 1n+SC.length(E.Entry<K, V>, t)) : Nat}
      %Equal.sym(Maybe<&2, V>, S.find(~K, ~cmp, V, k, t), None{}, find_above(~K, ~cmp, V, t, k, SO.above_gt(~K, ~cmp, ~o, V, t, E.key(K, V, e), k, SO.so_above(~K, ~cmp, V, e, t, s), ec))) : {2n+SC.length(E.Entry<K, V>, t) == B.grow(V, _, 1n+SC.length(E.Entry<K, V>, t)) : Nat}
      {==}
    case EQ{}:
      %Equal.sym(List<&2, E.Entry<K, V>>, S.ins(~K, ~cmp, V, k, v, Con{e, t}), Con{E.Entry{k, v}, t}, ins_eq(~K, ~cmp, V, e, t, k, v, ec)) : {SC.length(E.Entry<K, V>, _) == B.grow(V, S.find(~K, ~cmp, V, k, Con{e, t}), 1n+SC.length(E.Entry<K, V>, t)) : Nat}
      %Equal.sym(Maybe<&2, V>, S.find(~K, ~cmp, V, k, Con{e, t}), Some{E.val(K, V, e)}, find_eq(~K, ~cmp, V, e, t, k, ec)) : {1n+SC.length(E.Entry<K, V>, t) == B.grow(V, _, 1n+SC.length(E.Entry<K, V>, t)) : Nat}
      {==}
    case GT{}:
      %Equal.sym(List<&2, E.Entry<K, V>>, S.ins(~K, ~cmp, V, k, v, Con{e, t}), Con{e, S.ins(~K, ~cmp, V, k, v, t)}, ins_gt(~K, ~cmp, V, e, t, k, v, ec)) : {SC.length(E.Entry<K, V>, _) == B.grow(V, S.find(~K, ~cmp, V, k, Con{e, t}), 1n+SC.length(E.Entry<K, V>, t)) : Nat}
      %Equal.sym(Maybe<&2, V>, S.find(~K, ~cmp, V, k, Con{e, t}), S.find(~K, ~cmp, V, k, t), find_gt(~K, ~cmp, V, e, t, k, ec)) : {1n+SC.length(E.Entry<K, V>, S.ins(~K, ~cmp, V, k, v, t)) == B.grow(V, _, 1n+SC.length(E.Entry<K, V>, t)) : Nat}
      %Equal.sym(Nat, B.grow(V, S.find(~K, ~cmp, V, k, t), 1n+SC.length(E.Entry<K, V>, t)), 1n+B.grow(V, S.find(~K, ~cmp, V, k, t), SC.length(E.Entry<K, V>, t)), grow_succ(V, S.find(~K, ~cmp, V, k, t), SC.length(E.Entry<K, V>, t))) : {1n+SC.length(E.Entry<K, V>, S.ins(~K, ~cmp, V, k, v, t)) == _ : Nat}
      N.succ_cong(SC.length(E.Entry<K, V>, S.ins(~K, ~cmp, V, k, v, t)), B.grow(V, S.find(~K, ~cmp, V, k, t), SC.length(E.Entry<K, V>, t)), ih)

# length(ins k v xs) = length xs + (1 if k absent else 0)
def len_ins(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), -V: Data, +xs: List<&2, E.Entry<K, V>>, +k: K, +v: V, +s: {SO.sorted(~K, ~cmp, V, xs) == True{} : Bool}) -> {SC.length(E.Entry<K, V>, S.ins(~K, ~cmp, V, k, v, xs)) == B.grow(V, S.find(~K, ~cmp, V, k, xs), SC.length(E.Entry<K, V>, xs)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{e, t}:
      len_ins_c(~K, ~cmp, ~o, V, e, t, k, v, s, cmp(k, E.key(K, V, e)), {==}, len_ins(~K, ~cmp, ~o, V, t, k, v, SO.so_tail(~K, ~cmp, V, e, t, s)))

def len_del_c(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), -V: Data, +e: E.Entry<K, V>, +t: List<&2, E.Entry<K, V>>, +k: K, +w: V, +s: {SO.sorted(~K, ~cmp, V, Con{e, t}) == True{} : Bool}, +f: {S.find(~K, ~cmp, V, k, Con{e, t}) == Some{w} : Maybe<&2, V>}, c: Cmp, +ec: {cmp(k, E.key(K, V, e)) == c : Cmp}, ih: @+f2: {S.find(~K, ~cmp, V, k, t) == Some{w} : Maybe<&2, V>} -> {1n+SC.length(E.Entry<K, V>, S.del(~K, ~cmp, V, k, t)) == SC.length(E.Entry<K, V>, t) : Nat}) -> {1n+SC.length(E.Entry<K, V>, S.del(~K, ~cmp, V, k, Con{e, t})) == SC.length(E.Entry<K, V>, Con{e, t}) : Nat}:
  match c:
    case LT{}:
      +none = Equal.trans(Maybe<&2, V>, S.find(~K, ~cmp, V, k, Con{e, t}), S.find(~K, ~cmp, V, k, t), None{}, find_lt(~K, ~cmp, V, e, t, k, ec), find_above(~K, ~cmp, V, t, k, SO.above_gt(~K, ~cmp, ~o, V, t, E.key(K, V, e), k, SO.so_above(~K, ~cmp, V, e, t, s), ec)))
      Empty.absurd({1n+SC.length(E.Entry<K, V>, S.del(~K, ~cmp, V, k, Con{e, t})) == SC.length(E.Entry<K, V>, Con{e, t}) : Nat}, L.none_some(V, w, Equal.trans(Maybe<&2, V>, None{}, S.find(~K, ~cmp, V, k, Con{e, t}), Some{w}, Equal.sym(Maybe<&2, V>, S.find(~K, ~cmp, V, k, Con{e, t}), None{}, none), f)))
    case EQ{}:
      %Equal.sym(List<&2, E.Entry<K, V>>, S.del(~K, ~cmp, V, k, Con{e, t}), S.del(~K, ~cmp, V, k, t), del_eq(~K, ~cmp, V, e, t, k, ec)) : {1n+SC.length(E.Entry<K, V>, _) == 1n+SC.length(E.Entry<K, V>, t) : Nat}
      %Equal.sym(List<&2, E.Entry<K, V>>, S.del(~K, ~cmp, V, k, t), t, del_above(~K, ~cmp, V, t, k, L.subst(K, z => {SO.above(~K, ~cmp, V, t, z) == True{} : Bool}, E.key(K, V, e), k, Equal.sym(K, k, E.key(K, V, e), O.antisym(~K, ~cmp, o, k, E.key(K, V, e), ec)), SO.so_above(~K, ~cmp, V, e, t, s)))) : {1n+SC.length(E.Entry<K, V>, _) == 1n+SC.length(E.Entry<K, V>, t) : Nat}
      {==}
    case GT{}:
      %Equal.sym(List<&2, E.Entry<K, V>>, S.del(~K, ~cmp, V, k, Con{e, t}), Con{e, S.del(~K, ~cmp, V, k, t)}, del_gt(~K, ~cmp, V, e, t, k, ec)) : {1n+SC.length(E.Entry<K, V>, _) == 1n+SC.length(E.Entry<K, V>, t) : Nat}
      N.succ_cong(1n+SC.length(E.Entry<K, V>, S.del(~K, ~cmp, V, k, t)), SC.length(E.Entry<K, V>, t), ih(Equal.trans(Maybe<&2, V>, S.find(~K, ~cmp, V, k, t), S.find(~K, ~cmp, V, k, Con{e, t}), Some{w}, Equal.sym(Maybe<&2, V>, S.find(~K, ~cmp, V, k, Con{e, t}), S.find(~K, ~cmp, V, k, t), find_gt(~K, ~cmp, V, e, t, k, ec)), f)))

# Removing a present key removes exactly one entry.
def len_del(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), -V: Data, +xs: List<&2, E.Entry<K, V>>, +k: K, +w: V, +s: {SO.sorted(~K, ~cmp, V, xs) == True{} : Bool}, +f: {S.find(~K, ~cmp, V, k, xs) == Some{w} : Maybe<&2, V>}) -> {1n+SC.length(E.Entry<K, V>, S.del(~K, ~cmp, V, k, xs)) == SC.length(E.Entry<K, V>, xs) : Nat}:
  match xs:
    case Nil{}:
      Empty.absurd({1n == 0n : Nat}, L.none_some(V, w, f))
    case Con{e, t}:
      len_del_c(~K, ~cmp, ~o, V, e, t, k, w, s, f, cmp(k, E.key(K, V, e)), {==}, f2 => len_del(~K, ~cmp, ~o, V, t, k, w, SO.so_tail(~K, ~cmp, V, e, t, s), f2))
