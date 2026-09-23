import Base
import ../lib/logic.bend as L
import ../lib/order.bend as O
import ../spec/common.bend as SC
import ../spec/tree_map.bend as S
import ../../src/containers/balanced_search_tree.bend as M
import ./state.bend as ST

# Order facts over entry lists for a lawful comparator (O.Order): the keys
# of a sorted list split around each entry, and the specification's lookup
# of a key decided by one comparison. (source: tools/generators/tm_hand/ord.src)


# ---- strict order ----

def lt_le(+c: Cmp, +h: {Cmp.is_lt(c) == True{} : Bool}) -> {Cmp.is_le(c) == True{} : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      Empty.absurd({Cmp.is_le(EQ{}) == True{} : Bool}, L.false_true(h))
    case GT{}:
      Empty.absurd({Cmp.is_le(GT{}) == True{} : Bool}, L.false_true(h))

def lt_flip(+c: Cmp, +h: {Cmp.is_lt(c) == True{} : Bool}) -> {Cmp.is_lt(O.flipc(c)) == False{} : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      Empty.absurd({Cmp.is_lt(O.flipc(EQ{})) == False{} : Bool}, L.false_true(h))
    case GT{}:
      Empty.absurd({Cmp.is_lt(O.flipc(GT{})) == False{} : Bool}, L.false_true(h))

def slt_c(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +a: K, +b: K, +c: K, +hab: {Cmp.is_lt(cmp(a, b)) == True{} : Bool}, +hbc: {Cmp.is_lt(cmp(b, c)) == True{} : Bool}, +x: Cmp, +hx: {cmp(a, c) == x : Cmp}) -> {Cmp.is_lt(x) == True{} : Bool}:
  match x:
    case LT{}:
      {==}
    case GT{}:
      +le = O.trans(~K, ~cmp, o, a, b, c, lt_le(cmp(a, b), hab), lt_le(cmp(b, c), hbc))
      Empty.absurd({Cmp.is_lt(GT{}) == True{} : Bool}, L.false_true(L.subst(Cmp, z => {Cmp.is_le(z) == True{} : Bool}, cmp(a, c), GT{}, hx, le)))
    case EQ{}:
      +e = O.antisym(~K, ~cmp, o, a, c, hx)
      +hba = L.subst(K, z => {Cmp.is_lt(cmp(b, z)) == True{} : Bool}, c, a, Equal.sym(K, a, c, e), hbc)
      +hf = L.subst(Cmp, z => {Cmp.is_lt(z) == True{} : Bool}, cmp(b, a), O.flipc(cmp(a, b)), O.flip(~K, ~cmp, o, a, b), hba)
      Empty.absurd({Cmp.is_lt(EQ{}) == True{} : Bool}, L.true_not_false(Cmp.is_lt(O.flipc(cmp(a, b))), hf, lt_flip(cmp(a, b), hab)))

def slt_trans(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +a: K, +b: K, +c: K, +hab: {Cmp.is_lt(cmp(a, b)) == True{} : Bool}, +hbc: {Cmp.is_lt(cmp(b, c)) == True{} : Bool}) -> {Cmp.is_lt(cmp(a, c)) == True{} : Bool}:
  slt_c(~K, ~cmp, ~o, a, b, c, hab, hbc, cmp(a, c), {==})

# a > b as b < a
def gt_lt(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +a: K, +b: K, +h: {cmp(a, b) == GT{} : Cmp}) -> {Cmp.is_lt(cmp(b, a)) == True{} : Bool}:
  %Equal.sym(Cmp, cmp(b, a), O.flipc(cmp(a, b)), O.flip(~K, ~cmp, o, a, b)) : {Cmp.is_lt(_) == True{} : Bool}
  %Equal.sym(Cmp, cmp(a, b), GT{}, h) : {Cmp.is_lt(O.flipc(_)) == True{} : Bool}
  {==}

# a < b gives cmp(b, a) = GT
def lt_gt(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +a: K, +b: K, +h: {Cmp.is_lt(cmp(a, b)) == True{} : Bool}) -> {cmp(b, a) == GT{} : Cmp}:
  %Equal.sym(Cmp, cmp(b, a), O.flipc(cmp(a, b)), O.flip(~K, ~cmp, o, a, b)) : {_ == GT{} : Cmp}
  %Equal.sym(Cmp, cmp(a, b), LT{}, O.lt_is(cmp(a, b), h)) : {O.flipc(_) == GT{} : Cmp}
  {==}

# ---- all keys above / below a key ----

# k below every key
def gtall(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +k: K, es: List<&2, M.Entry<K, V>>) -> Bool:
  match es:
    case Nil{}:
      True{}
    case Con{+e, t}:
      Bool.and(Cmp.is_lt(cmp(k, S.key(K, V, e))), gtall(~K, ~V, ~cmp, k, t))

# k above every key
def ltall(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +k: K, es: List<&2, M.Entry<K, V>>) -> Bool:
  match es:
    case Nil{}:
      True{}
    case Con{+e, t}:
      Bool.and(Cmp.is_lt(cmp(S.key(K, V, e), k)), ltall(~K, ~V, ~cmp, k, t))


def gtall_mono(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +a: K, +b: K, +hab: {Cmp.is_lt(cmp(a, b)) == True{} : Bool}, +es: List<&2, M.Entry<K, V>>, +h: {gtall(~K, ~V, ~cmp, b, es) == True{} : Bool}) -> {gtall(~K, ~V, ~cmp, a, es) == True{} : Bool}:
  match es:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      +h1 = L.and_left(Cmp.is_lt(cmp(b, S.key(K, V, e))), gtall(~K, ~V, ~cmp, b, t), h)
      +h2 = L.and_right(Cmp.is_lt(cmp(b, S.key(K, V, e))), gtall(~K, ~V, ~cmp, b, t), h)
      L.and_intro(Cmp.is_lt(cmp(a, S.key(K, V, e))), gtall(~K, ~V, ~cmp, a, t), slt_trans(~K, ~cmp, ~o, a, b, S.key(K, V, e), hab, h1), gtall_mono(~K, ~V, ~cmp, ~o, a, b, hab, t, h2))

def ltall_mono(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +a: K, +b: K, +hab: {Cmp.is_lt(cmp(a, b)) == True{} : Bool}, +es: List<&2, M.Entry<K, V>>, +h: {ltall(~K, ~V, ~cmp, a, es) == True{} : Bool}) -> {ltall(~K, ~V, ~cmp, b, es) == True{} : Bool}:
  match es:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      +h1 = L.and_left(Cmp.is_lt(cmp(S.key(K, V, e), a)), ltall(~K, ~V, ~cmp, a, t), h)
      +h2 = L.and_right(Cmp.is_lt(cmp(S.key(K, V, e), a)), ltall(~K, ~V, ~cmp, a, t), h)
      L.and_intro(Cmp.is_lt(cmp(S.key(K, V, e), b)), ltall(~K, ~V, ~cmp, b, t), slt_trans(~K, ~cmp, ~o, S.key(K, V, e), a, b, h1, hab), ltall_mono(~K, ~V, ~cmp, ~o, a, b, hab, t, h2))

def gtall_r(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +k: K, +xs: List<&2, M.Entry<K, V>>, +ys: List<&2, M.Entry<K, V>>, +h: {gtall(~K, ~V, ~cmp, k, SC.append(M.Entry<K, V>, xs, ys)) == True{} : Bool}) -> {gtall(~K, ~V, ~cmp, k, ys) == True{} : Bool}:
  match xs:
    case Nil{}:
      h
    case Con{+e, +t}:
      gtall_r(~K, ~V, ~cmp, k, t, ys, L.and_right(Cmp.is_lt(cmp(k, S.key(K, V, e))), gtall(~K, ~V, ~cmp, k, SC.append(M.Entry<K, V>, t, ys)), h))

def ltall_r(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +k: K, +xs: List<&2, M.Entry<K, V>>, +ys: List<&2, M.Entry<K, V>>, +h: {ltall(~K, ~V, ~cmp, k, SC.append(M.Entry<K, V>, xs, ys)) == True{} : Bool}) -> {ltall(~K, ~V, ~cmp, k, ys) == True{} : Bool}:
  match xs:
    case Nil{}:
      h
    case Con{+e, +t}:
      ltall_r(~K, ~V, ~cmp, k, t, ys, L.and_right(Cmp.is_lt(cmp(S.key(K, V, e), k)), ltall(~K, ~V, ~cmp, k, SC.append(M.Entry<K, V>, t, ys)), h))

def gtall_l(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +k: K, +xs: List<&2, M.Entry<K, V>>, +ys: List<&2, M.Entry<K, V>>, +h: {gtall(~K, ~V, ~cmp, k, SC.append(M.Entry<K, V>, xs, ys)) == True{} : Bool}) -> {gtall(~K, ~V, ~cmp, k, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      L.and_intro(Cmp.is_lt(cmp(k, S.key(K, V, e))), gtall(~K, ~V, ~cmp, k, t), L.and_left(Cmp.is_lt(cmp(k, S.key(K, V, e))), gtall(~K, ~V, ~cmp, k, SC.append(M.Entry<K, V>, t, ys)), h), gtall_l(~K, ~V, ~cmp, k, t, ys, L.and_right(Cmp.is_lt(cmp(k, S.key(K, V, e))), gtall(~K, ~V, ~cmp, k, SC.append(M.Entry<K, V>, t, ys)), h)))

def ltall_l(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +k: K, +xs: List<&2, M.Entry<K, V>>, +ys: List<&2, M.Entry<K, V>>, +h: {ltall(~K, ~V, ~cmp, k, SC.append(M.Entry<K, V>, xs, ys)) == True{} : Bool}) -> {ltall(~K, ~V, ~cmp, k, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      L.and_intro(Cmp.is_lt(cmp(S.key(K, V, e), k)), ltall(~K, ~V, ~cmp, k, t), L.and_left(Cmp.is_lt(cmp(S.key(K, V, e), k)), ltall(~K, ~V, ~cmp, k, SC.append(M.Entry<K, V>, t, ys)), h), ltall_l(~K, ~V, ~cmp, k, t, ys, L.and_right(Cmp.is_lt(cmp(S.key(K, V, e), k)), ltall(~K, ~V, ~cmp, k, SC.append(M.Entry<K, V>, t, ys)), h)))

# ---- sorted lists ----

def ord_tail(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +e: M.Entry<K, V>, +t: List<&2, M.Entry<K, V>>, +h: {ST.ordered(~K, ~V, ~cmp, Con{e, t}) == True{} : Bool}) -> {ST.ordered(~K, ~V, ~cmp, t) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case Con{+e2, +u}:
      L.and_right(Cmp.is_lt(cmp(S.key(K, V, e), S.key(K, V, e2))), ST.ordered(~K, ~V, ~cmp, Con{e2, u}), h)

def ord_gt(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +t: List<&2, M.Entry<K, V>>, +e: M.Entry<K, V>, +h: {ST.ordered(~K, ~V, ~cmp, Con{e, t}) == True{} : Bool}) -> {gtall(~K, ~V, ~cmp, S.key(K, V, e), t) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case Con{+e2, +u}:
      +h1 = L.and_left(Cmp.is_lt(cmp(S.key(K, V, e), S.key(K, V, e2))), ST.ordered(~K, ~V, ~cmp, Con{e2, u}), h)
      +h2 = L.and_right(Cmp.is_lt(cmp(S.key(K, V, e), S.key(K, V, e2))), ST.ordered(~K, ~V, ~cmp, Con{e2, u}), h)
      L.and_intro(Cmp.is_lt(cmp(S.key(K, V, e), S.key(K, V, e2))), gtall(~K, ~V, ~cmp, S.key(K, V, e), u), h1, gtall_mono(~K, ~V, ~cmp, ~o, S.key(K, V, e), S.key(K, V, e2), h1, u, ord_gt(~K, ~V, ~cmp, ~o, u, e2, h2)))

def ord_app_r(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +xs: List<&2, M.Entry<K, V>>, +ys: List<&2, M.Entry<K, V>>, +h: {ST.ordered(~K, ~V, ~cmp, SC.append(M.Entry<K, V>, xs, ys)) == True{} : Bool}) -> {ST.ordered(~K, ~V, ~cmp, ys) == True{} : Bool}:
  match xs:
    case Nil{}:
      h
    case Con{+e, +t}:
      ord_app_r(~K, ~V, ~cmp, t, ys, ord_tail(~K, ~V, ~cmp, e, SC.append(M.Entry<K, V>, t, ys), h))

# the entries before e are below it
def ord_mid_l(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +xs: List<&2, M.Entry<K, V>>, +e: M.Entry<K, V>, +ys: List<&2, M.Entry<K, V>>, +h: {ST.ordered(~K, ~V, ~cmp, SC.append(M.Entry<K, V>, xs, Con{e, ys})) == True{} : Bool}) -> {ltall(~K, ~V, ~cmp, S.key(K, V, e), xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+a, +t}:
      +g = gtall_r(~K, ~V, ~cmp, S.key(K, V, a), t, Con{e, ys}, ord_gt(~K, ~V, ~cmp, ~o, SC.append(M.Entry<K, V>, t, Con{e, ys}), a, h))
      L.and_intro(Cmp.is_lt(cmp(S.key(K, V, a), S.key(K, V, e))), ltall(~K, ~V, ~cmp, S.key(K, V, e), t), L.and_left(Cmp.is_lt(cmp(S.key(K, V, a), S.key(K, V, e))), gtall(~K, ~V, ~cmp, S.key(K, V, a), ys), g), ord_mid_l(~K, ~V, ~cmp, ~o, t, e, ys, ord_tail(~K, ~V, ~cmp, a, SC.append(M.Entry<K, V>, t, Con{e, ys}), h)))

# the entries after e are above it
def ord_mid_r(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +xs: List<&2, M.Entry<K, V>>, +e: M.Entry<K, V>, +ys: List<&2, M.Entry<K, V>>, +h: {ST.ordered(~K, ~V, ~cmp, SC.append(M.Entry<K, V>, xs, Con{e, ys})) == True{} : Bool}) -> {gtall(~K, ~V, ~cmp, S.key(K, V, e), ys) == True{} : Bool}:
  ord_gt(~K, ~V, ~cmp, ~o, ys, e, ord_app_r(~K, ~V, ~cmp, xs, Con{e, ys}, h))

# ---- lookup ----

def orm(-X: Data, m: Maybe<&2, X>, n: Maybe<&2, X>) -> Maybe<&2, X>:
  match m:
    case None{}:
      n
    case Some{x}:
      Some{x}

def orm_none(-X: Data, +m: Maybe<&2, X>) -> {orm(X, m, None{}) == m : Maybe<&2, X>}:
  match m:
    case None{}:
      {==}
    case Some{x}:
      {==}

def find_app_c(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +k: K, +e: M.Entry<K, V>, +t: List<&2, M.Entry<K, V>>, +ys: List<&2, M.Entry<K, V>>, +b: Bool, +hb: {S.is_eq(cmp(k, S.key(K, V, e))) == b : Bool}, +ih: {S.find_e(~K, ~V, ~cmp, k, SC.append(M.Entry<K, V>, t, ys)) == orm(M.Entry<K, V>, S.find_e(~K, ~V, ~cmp, k, t), S.find_e(~K, ~V, ~cmp, k, ys)) : Maybe<&2, M.Entry<K, V>>}) -> {S.find_e(~K, ~V, ~cmp, k, SC.append(M.Entry<K, V>, Con{e, t}, ys)) == orm(M.Entry<K, V>, S.find_e(~K, ~V, ~cmp, k, Con{e, t}), S.find_e(~K, ~V, ~cmp, k, ys)) : Maybe<&2, M.Entry<K, V>>}:
  match b:
    case True{}:
      %Equal.sym(Bool, S.is_eq(cmp(k, S.key(K, V, e))), True{}, hb) : {S.pick(Maybe<&2, M.Entry<K, V>>, _, Some{e}, S.find_e(~K, ~V, ~cmp, k, SC.append(M.Entry<K, V>, t, ys))) == orm(M.Entry<K, V>, S.pick(Maybe<&2, M.Entry<K, V>>, _, Some{e}, S.find_e(~K, ~V, ~cmp, k, t)), S.find_e(~K, ~V, ~cmp, k, ys)) : Maybe<&2, M.Entry<K, V>>}
      {==}
    case False{}:
      %Equal.sym(Bool, S.is_eq(cmp(k, S.key(K, V, e))), False{}, hb) : {S.pick(Maybe<&2, M.Entry<K, V>>, _, Some{e}, S.find_e(~K, ~V, ~cmp, k, SC.append(M.Entry<K, V>, t, ys))) == orm(M.Entry<K, V>, S.pick(Maybe<&2, M.Entry<K, V>>, _, Some{e}, S.find_e(~K, ~V, ~cmp, k, t)), S.find_e(~K, ~V, ~cmp, k, ys)) : Maybe<&2, M.Entry<K, V>>}
      ih

def find_app(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +k: K, +xs: List<&2, M.Entry<K, V>>, +ys: List<&2, M.Entry<K, V>>) -> {S.find_e(~K, ~V, ~cmp, k, SC.append(M.Entry<K, V>, xs, ys)) == orm(M.Entry<K, V>, S.find_e(~K, ~V, ~cmp, k, xs), S.find_e(~K, ~V, ~cmp, k, ys)) : Maybe<&2, M.Entry<K, V>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      find_app_c(~K, ~V, ~cmp, k, e, t, ys, S.is_eq(cmp(k, S.key(K, V, e))), {==}, find_app(~K, ~V, ~cmp, k, t, ys))

def gt_none(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +k: K, +es: List<&2, M.Entry<K, V>>, +h: {gtall(~K, ~V, ~cmp, k, es) == True{} : Bool}) -> {S.find_e(~K, ~V, ~cmp, k, es) == None{} : Maybe<&2, M.Entry<K, V>>}:
  match es:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      %Equal.sym(Cmp, cmp(k, S.key(K, V, e)), LT{}, O.lt_is(cmp(k, S.key(K, V, e)), L.and_left(Cmp.is_lt(cmp(k, S.key(K, V, e))), gtall(~K, ~V, ~cmp, k, t), h))) : {S.pick(Maybe<&2, M.Entry<K, V>>, S.is_eq(_), Some{e}, S.find_e(~K, ~V, ~cmp, k, t)) == None{} : Maybe<&2, M.Entry<K, V>>}
      gt_none(~K, ~V, ~cmp, k, t, L.and_right(Cmp.is_lt(cmp(k, S.key(K, V, e))), gtall(~K, ~V, ~cmp, k, t), h))

def lt_none(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +k: K, +es: List<&2, M.Entry<K, V>>, +h: {ltall(~K, ~V, ~cmp, k, es) == True{} : Bool}) -> {S.find_e(~K, ~V, ~cmp, k, es) == None{} : Maybe<&2, M.Entry<K, V>>}:
  match es:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      %Equal.sym(Cmp, cmp(k, S.key(K, V, e)), GT{}, lt_gt(~K, ~cmp, ~o, S.key(K, V, e), k, L.and_left(Cmp.is_lt(cmp(S.key(K, V, e), k)), ltall(~K, ~V, ~cmp, k, t), h))) : {S.pick(Maybe<&2, M.Entry<K, V>>, S.is_eq(_), Some{e}, S.find_e(~K, ~V, ~cmp, k, t)) == None{} : Maybe<&2, M.Entry<K, V>>}
      lt_none(~K, ~V, ~cmp, ~o, k, t, L.and_right(Cmp.is_lt(cmp(S.key(K, V, e), k)), ltall(~K, ~V, ~cmp, k, t), h))

# the lookup of k around an entry e of a sorted list, by cmp(k, e.key)
def find_mid_lt(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +k: K, +xs: List<&2, M.Entry<K, V>>, +e: M.Entry<K, V>, +ys: List<&2, M.Entry<K, V>>, +h: {ST.ordered(~K, ~V, ~cmp, SC.append(M.Entry<K, V>, xs, Con{e, ys})) == True{} : Bool}, +hc: {cmp(k, S.key(K, V, e)) == LT{} : Cmp}) -> {S.find_e(~K, ~V, ~cmp, k, SC.append(M.Entry<K, V>, xs, Con{e, ys})) == S.find_e(~K, ~V, ~cmp, k, xs) : Maybe<&2, M.Entry<K, V>>}:
  %Equal.sym(Maybe<&2, M.Entry<K, V>>, S.find_e(~K, ~V, ~cmp, k, SC.append(M.Entry<K, V>, xs, Con{e, ys})), orm(M.Entry<K, V>, S.find_e(~K, ~V, ~cmp, k, xs), S.find_e(~K, ~V, ~cmp, k, Con{e, ys})), find_app(~K, ~V, ~cmp, k, xs, Con{e, ys})) : {_ == S.find_e(~K, ~V, ~cmp, k, xs) : Maybe<&2, M.Entry<K, V>>}
  %Equal.sym(Cmp, cmp(k, S.key(K, V, e)), LT{}, hc) : {orm(M.Entry<K, V>, S.find_e(~K, ~V, ~cmp, k, xs), S.pick(Maybe<&2, M.Entry<K, V>>, S.is_eq(_), Some{e}, S.find_e(~K, ~V, ~cmp, k, ys))) == S.find_e(~K, ~V, ~cmp, k, xs) : Maybe<&2, M.Entry<K, V>>}
  +hlt = L.subst(Cmp, z => {Cmp.is_lt(z) == True{} : Bool}, LT{}, cmp(k, S.key(K, V, e)), Equal.sym(Cmp, cmp(k, S.key(K, V, e)), LT{}, hc), {==})
  %Equal.sym(Maybe<&2, M.Entry<K, V>>, S.find_e(~K, ~V, ~cmp, k, ys), None{}, gt_none(~K, ~V, ~cmp, k, ys, gtall_mono(~K, ~V, ~cmp, ~o, k, S.key(K, V, e), hlt, ys, ord_mid_r(~K, ~V, ~cmp, ~o, xs, e, ys, h)))) : {orm(M.Entry<K, V>, S.find_e(~K, ~V, ~cmp, k, xs), _) == S.find_e(~K, ~V, ~cmp, k, xs) : Maybe<&2, M.Entry<K, V>>}
  orm_none(M.Entry<K, V>, S.find_e(~K, ~V, ~cmp, k, xs))

def find_mid_gt(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +k: K, +xs: List<&2, M.Entry<K, V>>, +e: M.Entry<K, V>, +ys: List<&2, M.Entry<K, V>>, +h: {ST.ordered(~K, ~V, ~cmp, SC.append(M.Entry<K, V>, xs, Con{e, ys})) == True{} : Bool}, +hc: {cmp(k, S.key(K, V, e)) == GT{} : Cmp}) -> {S.find_e(~K, ~V, ~cmp, k, SC.append(M.Entry<K, V>, xs, Con{e, ys})) == S.find_e(~K, ~V, ~cmp, k, ys) : Maybe<&2, M.Entry<K, V>>}:
  %Equal.sym(Maybe<&2, M.Entry<K, V>>, S.find_e(~K, ~V, ~cmp, k, SC.append(M.Entry<K, V>, xs, Con{e, ys})), orm(M.Entry<K, V>, S.find_e(~K, ~V, ~cmp, k, xs), S.find_e(~K, ~V, ~cmp, k, Con{e, ys})), find_app(~K, ~V, ~cmp, k, xs, Con{e, ys})) : {_ == S.find_e(~K, ~V, ~cmp, k, ys) : Maybe<&2, M.Entry<K, V>>}
  %Equal.sym(Cmp, cmp(k, S.key(K, V, e)), GT{}, hc) : {orm(M.Entry<K, V>, S.find_e(~K, ~V, ~cmp, k, xs), S.pick(Maybe<&2, M.Entry<K, V>>, S.is_eq(_), Some{e}, S.find_e(~K, ~V, ~cmp, k, ys))) == S.find_e(~K, ~V, ~cmp, k, ys) : Maybe<&2, M.Entry<K, V>>}
  %Equal.sym(Maybe<&2, M.Entry<K, V>>, S.find_e(~K, ~V, ~cmp, k, xs), None{}, lt_none(~K, ~V, ~cmp, ~o, k, xs, ltall_mono(~K, ~V, ~cmp, ~o, S.key(K, V, e), k, gt_lt(~K, ~cmp, ~o, k, S.key(K, V, e), hc), xs, ord_mid_l(~K, ~V, ~cmp, ~o, xs, e, ys, h)))) : {orm(M.Entry<K, V>, _, S.find_e(~K, ~V, ~cmp, k, ys)) == S.find_e(~K, ~V, ~cmp, k, ys) : Maybe<&2, M.Entry<K, V>>}
  {==}

def find_mid_eq(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +k: K, +xs: List<&2, M.Entry<K, V>>, +e: M.Entry<K, V>, +ys: List<&2, M.Entry<K, V>>, +h: {ST.ordered(~K, ~V, ~cmp, SC.append(M.Entry<K, V>, xs, Con{e, ys})) == True{} : Bool}, +hc: {cmp(k, S.key(K, V, e)) == EQ{} : Cmp}) -> {S.find_e(~K, ~V, ~cmp, k, SC.append(M.Entry<K, V>, xs, Con{e, ys})) == Some{e} : Maybe<&2, M.Entry<K, V>>}:
  %Equal.sym(Maybe<&2, M.Entry<K, V>>, S.find_e(~K, ~V, ~cmp, k, SC.append(M.Entry<K, V>, xs, Con{e, ys})), orm(M.Entry<K, V>, S.find_e(~K, ~V, ~cmp, k, xs), S.find_e(~K, ~V, ~cmp, k, Con{e, ys})), find_app(~K, ~V, ~cmp, k, xs, Con{e, ys})) : {_ == Some{e} : Maybe<&2, M.Entry<K, V>>}
  %Equal.sym(Cmp, cmp(k, S.key(K, V, e)), EQ{}, hc) : {orm(M.Entry<K, V>, S.find_e(~K, ~V, ~cmp, k, xs), S.pick(Maybe<&2, M.Entry<K, V>>, S.is_eq(_), Some{e}, S.find_e(~K, ~V, ~cmp, k, ys))) == Some{e} : Maybe<&2, M.Entry<K, V>>}
  +ek = O.antisym(~K, ~cmp, o, k, S.key(K, V, e), hc)
  +hl = L.subst(K, z => {ltall(~K, ~V, ~cmp, z, xs) == True{} : Bool}, S.key(K, V, e), k, Equal.sym(K, k, S.key(K, V, e), ek), ord_mid_l(~K, ~V, ~cmp, ~o, xs, e, ys, h))
  %Equal.sym(Maybe<&2, M.Entry<K, V>>, S.find_e(~K, ~V, ~cmp, k, xs), None{}, lt_none(~K, ~V, ~cmp, ~o, k, xs, hl)) : {orm(M.Entry<K, V>, _, Some{e}) == Some{e} : Maybe<&2, M.Entry<K, V>>}
  {==}
