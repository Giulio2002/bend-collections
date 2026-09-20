import Base
import ../lib/logic.bend as L
import ../lib/list.bend as LL
import ../lib/order.bend as O
import ../../spec/common.bend as SC
import ../../spec/balanced_search_tree.bend as S
import ../../src/balanced_search_tree.bend as B
import ../../types/balanced_search_tree.bend as E
import ./sorted.bend as SO
import ./specops.bend as SP
import ./tree.bend as T

# Queries on a sorted red-black tree agree with the specification applied to
# the tree's in-order entry list.

# ---- Maybe helpers ----

def orM_none(-V: Data, +x: Maybe<&2, V>) -> {SP.orM(V, x, None{}) == x : Maybe<&2, V>}:
  match x:
    case None{}:
      {==}
    case Some{v}:
      {==}

def orelse_orM(-K: Data, -V: Data, +x: Maybe<&2, E.Entry<K, V>>, +e: E.Entry<K, V>) -> {B.orelse(K, V, x, e) == SP.orM(E.Entry<K, V>, x, Some{e}) : Maybe<&2, E.Entry<K, V>>}:
  match x:
    case None{}:
      {==}
    case Some{v}:
      {==}

def oo(-K: Data, -V: Data, +x: Maybe<&2, E.Entry<K, V>>, +a: E.Entry<K, V>, +b: E.Entry<K, V>) -> {B.orelse(K, V, B.orelse(K, V, x, a), b) == B.orelse(K, V, x, a) : Maybe<&2, E.Entry<K, V>>}:
  match x:
    case None{}:
      {==}
    case Some{v}:
      {==}

# ---- find ----

def fd_left(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), -V: Data, +Ls: List<&2, E.Entry<K, V>>, +e: E.Entry<K, V>, +R: List<&2, E.Entry<K, V>>, +k: K, +h: {cmp(k, E.key(K, V, e)) == LT{} : Cmp}, +sab: {SO.above(~K, ~cmp, V, R, E.key(K, V, e)) == True{} : Bool}) -> {S.find(~K, ~cmp, V, k, SC.append(E.Entry<K, V>, Ls, Con{e, R})) == S.find(~K, ~cmp, V, k, Ls) : Maybe<&2, V>}:
  Equal.trans(Maybe<&2, V>, S.find(~K, ~cmp, V, k, SC.append(E.Entry<K, V>, Ls, Con{e, R})), SP.orM(V, S.find(~K, ~cmp, V, k, Ls), S.find(~K, ~cmp, V, k, Con{e, R})), S.find(~K, ~cmp, V, k, Ls),
    SP.find_app(~K, ~cmp, V, Ls, Con{e, R}, k),
    Equal.trans(Maybe<&2, V>, SP.orM(V, S.find(~K, ~cmp, V, k, Ls), S.find(~K, ~cmp, V, k, Con{e, R})), SP.orM(V, S.find(~K, ~cmp, V, k, Ls), None{}), S.find(~K, ~cmp, V, k, Ls),
      Equal.cong(Maybe<&2, V>, Maybe<&2, V>, z => SP.orM(V, S.find(~K, ~cmp, V, k, Ls), z), S.find(~K, ~cmp, V, k, Con{e, R}), None{},
        Equal.trans(Maybe<&2, V>, S.find(~K, ~cmp, V, k, Con{e, R}), S.find(~K, ~cmp, V, k, R), None{}, SP.find_lt(~K, ~cmp, V, e, R, k, h), SP.find_above(~K, ~cmp, V, R, k, SO.above_gt(~K, ~cmp, ~o, V, R, E.key(K, V, e), k, sab, h)))),
      orM_none(V, S.find(~K, ~cmp, V, k, Ls))))

def fd_mid(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), -V: Data, +Ls: List<&2, E.Entry<K, V>>, +e: E.Entry<K, V>, +R: List<&2, E.Entry<K, V>>, +k: K, +h: {cmp(k, E.key(K, V, e)) == EQ{} : Cmp}, +sbl: {SO.below(~K, ~cmp, V, Ls, E.key(K, V, e)) == True{} : Bool}) -> {S.find(~K, ~cmp, V, k, SC.append(E.Entry<K, V>, Ls, Con{e, R})) == Some{E.val(K, V, e)} : Maybe<&2, V>}:
  Equal.trans(Maybe<&2, V>, S.find(~K, ~cmp, V, k, SC.append(E.Entry<K, V>, Ls, Con{e, R})), SP.orM(V, S.find(~K, ~cmp, V, k, Ls), S.find(~K, ~cmp, V, k, Con{e, R})), Some{E.val(K, V, e)},
    SP.find_app(~K, ~cmp, V, Ls, Con{e, R}, k),
    Equal.trans(Maybe<&2, V>, SP.orM(V, S.find(~K, ~cmp, V, k, Ls), S.find(~K, ~cmp, V, k, Con{e, R})), SP.orM(V, None{}, S.find(~K, ~cmp, V, k, Con{e, R})), Some{E.val(K, V, e)},
      Equal.cong(Maybe<&2, V>, Maybe<&2, V>, z => SP.orM(V, z, S.find(~K, ~cmp, V, k, Con{e, R})), S.find(~K, ~cmp, V, k, Ls), None{}, SP.find_below(~K, ~cmp, ~o, V, Ls, k, T.bl_eq(~K, ~cmp, ~o, V, Ls, e, k, sbl, h))),
      SP.find_eq(~K, ~cmp, V, e, R, k, h)))

def fd_right(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), -V: Data, +Ls: List<&2, E.Entry<K, V>>, +e: E.Entry<K, V>, +R: List<&2, E.Entry<K, V>>, +k: K, +h: {cmp(k, E.key(K, V, e)) == GT{} : Cmp}, +sbl: {SO.below(~K, ~cmp, V, Ls, E.key(K, V, e)) == True{} : Bool}) -> {S.find(~K, ~cmp, V, k, SC.append(E.Entry<K, V>, Ls, Con{e, R})) == S.find(~K, ~cmp, V, k, R) : Maybe<&2, V>}:
  Equal.trans(Maybe<&2, V>, S.find(~K, ~cmp, V, k, SC.append(E.Entry<K, V>, Ls, Con{e, R})), SP.orM(V, S.find(~K, ~cmp, V, k, Ls), S.find(~K, ~cmp, V, k, Con{e, R})), S.find(~K, ~cmp, V, k, R),
    SP.find_app(~K, ~cmp, V, Ls, Con{e, R}, k),
    Equal.trans(Maybe<&2, V>, SP.orM(V, S.find(~K, ~cmp, V, k, Ls), S.find(~K, ~cmp, V, k, Con{e, R})), SP.orM(V, None{}, S.find(~K, ~cmp, V, k, Con{e, R})), S.find(~K, ~cmp, V, k, R),
      Equal.cong(Maybe<&2, V>, Maybe<&2, V>, z => SP.orM(V, z, S.find(~K, ~cmp, V, k, Con{e, R})), S.find(~K, ~cmp, V, k, Ls), None{}, SP.find_below(~K, ~cmp, ~o, V, Ls, k, T.bl_gt(~K, ~cmp, ~o, V, Ls, e, k, sbl, h))),
      SP.find_gt(~K, ~cmp, V, e, R, k, h)))

def find_ok(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), -V: Data, +t: B.Tree<K, V>, +k: K, a: Cmp, +ea: {B.c1(~K, ~cmp, V, k, t) == a : Cmp}, +s: {SO.sorted(~K, ~cmp, V, T.io(K, V, t)) == True{} : Bool}) -> {B.find(~K, ~cmp, V, t, k, a) == S.find(~K, ~cmp, V, k, T.io(K, V, t)) : Maybe<&2, V>}:
  match t a:
    case B.Leaf{} _:
      {==}
    case B.Node{+c, +l, +e, +r} LT{}:
      +Lx = T.io(K, V, l)
      +Rx = T.io(K, V, r)
      Equal.trans(Maybe<&2, V>, B.find(~K, ~cmp, V, l, k, B.c1(~K, ~cmp, V, k, l)), S.find(~K, ~cmp, V, k, Lx), S.find(~K, ~cmp, V, k, SC.append(E.Entry<K, V>, Lx, Con{e, Rx})),
        find_ok(~K, ~cmp, ~o, V, l, k, B.c1(~K, ~cmp, V, k, l), {==}, T.s2_l(~K, ~cmp, V, Lx, e, Rx, s)),
        Equal.sym(Maybe<&2, V>, S.find(~K, ~cmp, V, k, SC.append(E.Entry<K, V>, Lx, Con{e, Rx})), S.find(~K, ~cmp, V, k, Lx), fd_left(~K, ~cmp, ~o, V, Lx, e, Rx, k, ea, T.s2_ab(~K, ~cmp, V, Lx, e, Rx, s))))
    case B.Node{+c, +l, +e, +r} EQ{}:
      Equal.sym(Maybe<&2, V>, S.find(~K, ~cmp, V, k, SC.append(E.Entry<K, V>, T.io(K, V, l), Con{e, T.io(K, V, r)})), Some{E.val(K, V, e)}, fd_mid(~K, ~cmp, ~o, V, T.io(K, V, l), e, T.io(K, V, r), k, ea, SO.so_below(~K, ~cmp, V, T.io(K, V, l), e, T.io(K, V, r), s)))
    case B.Node{+c, +l, +e, +r} GT{}:
      +Lx = T.io(K, V, l)
      +Rx = T.io(K, V, r)
      Equal.trans(Maybe<&2, V>, B.find(~K, ~cmp, V, r, k, B.c1(~K, ~cmp, V, k, r)), S.find(~K, ~cmp, V, k, Rx), S.find(~K, ~cmp, V, k, SC.append(E.Entry<K, V>, Lx, Con{e, Rx})),
        find_ok(~K, ~cmp, ~o, V, r, k, B.c1(~K, ~cmp, V, k, r), {==}, T.s2_r(~K, ~cmp, V, Lx, e, Rx, s)),
        Equal.sym(Maybe<&2, V>, S.find(~K, ~cmp, V, k, SC.append(E.Entry<K, V>, Lx, Con{e, Rx})), S.find(~K, ~cmp, V, k, Rx), fd_right(~K, ~cmp, ~o, V, Lx, e, Rx, k, ea, SO.so_below(~K, ~cmp, V, Lx, e, Rx, s))))

# ---- lower bound ----

def lw_left(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), -V: Data, +Ls: List<&2, E.Entry<K, V>>, +e: E.Entry<K, V>, +R: List<&2, E.Entry<K, V>>, +k: K, +h: {cmp(E.key(K, V, e), k) == LT{} : Cmp}, +sbl: {SO.below(~K, ~cmp, V, Ls, E.key(K, V, e)) == True{} : Bool}) -> {S.lower(~K, ~cmp, V, k, SC.append(E.Entry<K, V>, Ls, Con{e, R})) == S.lower(~K, ~cmp, V, k, R) : Maybe<&2, E.Entry<K, V>>}:
  -M = Maybe<&2, E.Entry<K, V>>
  Equal.trans(M, S.lower(~K, ~cmp, V, k, SC.append(E.Entry<K, V>, Ls, Con{e, R})), SP.orM(E.Entry<K, V>, S.lower(~K, ~cmp, V, k, Ls), S.lower(~K, ~cmp, V, k, Con{e, R})), S.lower(~K, ~cmp, V, k, R),
    SP.lower_app(~K, ~cmp, V, Ls, Con{e, R}, k),
    Equal.trans(M, SP.orM(E.Entry<K, V>, S.lower(~K, ~cmp, V, k, Ls), S.lower(~K, ~cmp, V, k, Con{e, R})), SP.orM(E.Entry<K, V>, None{}, S.lower(~K, ~cmp, V, k, Con{e, R})), S.lower(~K, ~cmp, V, k, R),
      Equal.cong(M, M, z => SP.orM(E.Entry<K, V>, z, S.lower(~K, ~cmp, V, k, Con{e, R})), S.lower(~K, ~cmp, V, k, Ls), None{}, SP.lower_below(~K, ~cmp, V, Ls, k, SO.below_lt(~K, ~cmp, ~o, V, Ls, E.key(K, V, e), k, sbl, h))),
      SP.lower_lt(~K, ~cmp, V, e, R, k, h)))

def lw_mid(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), -V: Data, +Ls: List<&2, E.Entry<K, V>>, +e: E.Entry<K, V>, +R: List<&2, E.Entry<K, V>>, +k: K, +h: {cmp(E.key(K, V, e), k) == EQ{} : Cmp}, +sbl: {SO.below(~K, ~cmp, V, Ls, E.key(K, V, e)) == True{} : Bool}) -> {S.lower(~K, ~cmp, V, k, SC.append(E.Entry<K, V>, Ls, Con{e, R})) == Some{e} : Maybe<&2, E.Entry<K, V>>}:
  -M = Maybe<&2, E.Entry<K, V>>
  Equal.trans(M, S.lower(~K, ~cmp, V, k, SC.append(E.Entry<K, V>, Ls, Con{e, R})), SP.orM(E.Entry<K, V>, S.lower(~K, ~cmp, V, k, Ls), S.lower(~K, ~cmp, V, k, Con{e, R})), Some{e},
    SP.lower_app(~K, ~cmp, V, Ls, Con{e, R}, k),
    Equal.trans(M, SP.orM(E.Entry<K, V>, S.lower(~K, ~cmp, V, k, Ls), S.lower(~K, ~cmp, V, k, Con{e, R})), SP.orM(E.Entry<K, V>, None{}, S.lower(~K, ~cmp, V, k, Con{e, R})), Some{e},
      Equal.cong(M, M, z => SP.orM(E.Entry<K, V>, z, S.lower(~K, ~cmp, V, k, Con{e, R})), S.lower(~K, ~cmp, V, k, Ls), None{}, SP.lower_below(~K, ~cmp, V, Ls, k, SO.below_eq(~K, ~cmp, ~o, V, Ls, E.key(K, V, e), k, sbl, h))),
      SP.lower_eq(~K, ~cmp, V, e, R, k, h)))

def lw_right(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +Ls: List<&2, E.Entry<K, V>>, +e: E.Entry<K, V>, +R: List<&2, E.Entry<K, V>>, +k: K, +h: {cmp(E.key(K, V, e), k) == GT{} : Cmp}) -> {S.lower(~K, ~cmp, V, k, SC.append(E.Entry<K, V>, Ls, Con{e, R})) == SP.orM(E.Entry<K, V>, S.lower(~K, ~cmp, V, k, Ls), Some{e}) : Maybe<&2, E.Entry<K, V>>}:
  -M = Maybe<&2, E.Entry<K, V>>
  Equal.trans(M, S.lower(~K, ~cmp, V, k, SC.append(E.Entry<K, V>, Ls, Con{e, R})), SP.orM(E.Entry<K, V>, S.lower(~K, ~cmp, V, k, Ls), S.lower(~K, ~cmp, V, k, Con{e, R})), SP.orM(E.Entry<K, V>, S.lower(~K, ~cmp, V, k, Ls), Some{e}),
    SP.lower_app(~K, ~cmp, V, Ls, Con{e, R}, k),
    Equal.cong(M, M, z => SP.orM(E.Entry<K, V>, S.lower(~K, ~cmp, V, k, Ls), z), S.lower(~K, ~cmp, V, k, Con{e, R}), Some{e}, SP.lower_gt(~K, ~cmp, V, e, R, k, h)))

# orelse(lb(sub), e) against orM(lower(sub list), Some e).
def lw_or(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +x: Maybe<&2, E.Entry<K, V>>, +Ls: List<&2, E.Entry<K, V>>, +e: E.Entry<K, V>, +k: K, +ih: {x == S.lower(~K, ~cmp, V, k, Ls) : Maybe<&2, E.Entry<K, V>>}) -> {B.orelse(K, V, x, e) == SP.orM(E.Entry<K, V>, S.lower(~K, ~cmp, V, k, Ls), Some{e}) : Maybe<&2, E.Entry<K, V>>}:
  %Equal.sym(Maybe<&2, E.Entry<K, V>>, x, S.lower(~K, ~cmp, V, k, Ls), ih) : {B.orelse(K, V, _, e) == SP.orM(E.Entry<K, V>, S.lower(~K, ~cmp, V, k, Ls), Some{e}) : Maybe<&2, E.Entry<K, V>>}
  orelse_orM(K, V, S.lower(~K, ~cmp, V, k, Ls), e)

def lb_ok(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), -V: Data, +t: B.Tree<K, V>, +k: K, a: Cmp, +ea: {B.d1(~K, ~cmp, V, k, t) == a : Cmp}, +s: {SO.sorted(~K, ~cmp, V, T.io(K, V, t)) == True{} : Bool}) -> {B.lb(~K, ~cmp, V, t, k, a) == S.lower(~K, ~cmp, V, k, T.io(K, V, t)) : Maybe<&2, E.Entry<K, V>>}:
  match t a:
    case B.Leaf{} _:
      {==}
    case B.Node{+c, +l, +e, +r} LT{}:
      -M = Maybe<&2, E.Entry<K, V>>
      +Lx = T.io(K, V, l)
      +Rx = T.io(K, V, r)
      Equal.trans(M, B.lb(~K, ~cmp, V, r, k, B.d1(~K, ~cmp, V, k, r)), S.lower(~K, ~cmp, V, k, Rx), S.lower(~K, ~cmp, V, k, SC.append(E.Entry<K, V>, Lx, Con{e, Rx})),
        lb_ok(~K, ~cmp, ~o, V, r, k, B.d1(~K, ~cmp, V, k, r), {==}, T.s2_r(~K, ~cmp, V, Lx, e, Rx, s)),
        Equal.sym(M, S.lower(~K, ~cmp, V, k, SC.append(E.Entry<K, V>, Lx, Con{e, Rx})), S.lower(~K, ~cmp, V, k, Rx), lw_left(~K, ~cmp, ~o, V, Lx, e, Rx, k, ea, SO.so_below(~K, ~cmp, V, Lx, e, Rx, s))))
    case B.Node{+c, +l, +e, +r} EQ{}:
      Equal.sym(Maybe<&2, E.Entry<K, V>>, S.lower(~K, ~cmp, V, k, SC.append(E.Entry<K, V>, T.io(K, V, l), Con{e, T.io(K, V, r)})), Some{e}, lw_mid(~K, ~cmp, ~o, V, T.io(K, V, l), e, T.io(K, V, r), k, ea, SO.so_below(~K, ~cmp, V, T.io(K, V, l), e, T.io(K, V, r), s)))
    case B.Node{+c, +l, +e, +r} GT{}:
      -M = Maybe<&2, E.Entry<K, V>>
      +Lx = T.io(K, V, l)
      +Rx = T.io(K, V, r)
      Equal.trans(M, B.orelse(K, V, B.lb(~K, ~cmp, V, l, k, B.d1(~K, ~cmp, V, k, l)), e), SP.orM(E.Entry<K, V>, S.lower(~K, ~cmp, V, k, Lx), Some{e}), S.lower(~K, ~cmp, V, k, SC.append(E.Entry<K, V>, Lx, Con{e, Rx})),
        lw_or(~K, ~cmp, V, B.lb(~K, ~cmp, V, l, k, B.d1(~K, ~cmp, V, k, l)), Lx, e, k, lb_ok(~K, ~cmp, ~o, V, l, k, B.d1(~K, ~cmp, V, k, l), {==}, T.s2_l(~K, ~cmp, V, Lx, e, Rx, s))),
        Equal.sym(M, S.lower(~K, ~cmp, V, k, SC.append(E.Entry<K, V>, Lx, Con{e, Rx})), SP.orM(E.Entry<K, V>, S.lower(~K, ~cmp, V, k, Lx), Some{e}), lw_right(~K, ~cmp, V, Lx, e, Rx, k, ea)))

# ---- min / max ----

def head_app(-K: Data, -V: Data, +xs: List<&2, E.Entry<K, V>>, +e: E.Entry<K, V>, +R: List<&2, E.Entry<K, V>>) -> {SC.head(E.Entry<K, V>, SC.append(E.Entry<K, V>, xs, Con{e, R})) == B.orelse(K, V, SC.head(E.Entry<K, V>, xs), e) : Maybe<&2, E.Entry<K, V>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{a, t}:
      {==}

def last_cons(-K: Data, -V: Data, +R: List<&2, E.Entry<K, V>>, +e: E.Entry<K, V>) -> {SC.last(E.Entry<K, V>, Con{e, R}) == B.orelse(K, V, SC.last(E.Entry<K, V>, R), e) : Maybe<&2, E.Entry<K, V>>}:
  match R:
    case Nil{}:
      {==}
    case Con{+h2, +t2}:
      -M = Maybe<&2, E.Entry<K, V>>
      Equal.trans(M, SC.last(E.Entry<K, V>, Con{h2, t2}), B.orelse(K, V, SC.last(E.Entry<K, V>, t2), h2), B.orelse(K, V, SC.last(E.Entry<K, V>, Con{h2, t2}), e),
        last_cons(K, V, t2, h2),
        Equal.trans(M, B.orelse(K, V, SC.last(E.Entry<K, V>, t2), h2), B.orelse(K, V, B.orelse(K, V, SC.last(E.Entry<K, V>, t2), h2), e), B.orelse(K, V, SC.last(E.Entry<K, V>, Con{h2, t2}), e),
          Equal.sym(M, B.orelse(K, V, B.orelse(K, V, SC.last(E.Entry<K, V>, t2), h2), e), B.orelse(K, V, SC.last(E.Entry<K, V>, t2), h2), oo(K, V, SC.last(E.Entry<K, V>, t2), h2, e)),
          Equal.cong(M, M, z => B.orelse(K, V, z, e), B.orelse(K, V, SC.last(E.Entry<K, V>, t2), h2), SC.last(E.Entry<K, V>, Con{h2, t2}), Equal.sym(M, SC.last(E.Entry<K, V>, Con{h2, t2}), B.orelse(K, V, SC.last(E.Entry<K, V>, t2), h2), last_cons(K, V, t2, h2)))))

def last_app(-K: Data, -V: Data, +xs: List<&2, E.Entry<K, V>>, +e: E.Entry<K, V>, +R: List<&2, E.Entry<K, V>>) -> {SC.last(E.Entry<K, V>, SC.append(E.Entry<K, V>, xs, Con{e, R})) == B.orelse(K, V, SC.last(E.Entry<K, V>, R), e) : Maybe<&2, E.Entry<K, V>>}:
  match xs:
    case Nil{}:
      last_cons(K, V, R, e)
    case Con{+a, +t}:
      -M = Maybe<&2, E.Entry<K, V>>
      Equal.trans(M, SC.last(E.Entry<K, V>, Con{a, SC.append(E.Entry<K, V>, t, Con{e, R})}), B.orelse(K, V, SC.last(E.Entry<K, V>, SC.append(E.Entry<K, V>, t, Con{e, R})), a), B.orelse(K, V, SC.last(E.Entry<K, V>, R), e),
        last_cons(K, V, SC.append(E.Entry<K, V>, t, Con{e, R}), a),
        Equal.trans(M, B.orelse(K, V, SC.last(E.Entry<K, V>, SC.append(E.Entry<K, V>, t, Con{e, R})), a), B.orelse(K, V, B.orelse(K, V, SC.last(E.Entry<K, V>, R), e), a), B.orelse(K, V, SC.last(E.Entry<K, V>, R), e),
          Equal.cong(M, M, z => B.orelse(K, V, z, a), SC.last(E.Entry<K, V>, SC.append(E.Entry<K, V>, t, Con{e, R})), B.orelse(K, V, SC.last(E.Entry<K, V>, R), e), last_app(K, V, t, e, R)),
          oo(K, V, SC.last(E.Entry<K, V>, R), e, a)))

def min_ok(-K: Data, -V: Data, +t: B.Tree<K, V>) -> {B.min_go(K, V, t) == SC.head(E.Entry<K, V>, T.io(K, V, t)) : Maybe<&2, E.Entry<K, V>>}:
  match t:
    case B.Leaf{}:
      {==}
    case B.Node{+c, +l, +e, +r}:
      -M = Maybe<&2, E.Entry<K, V>>
      Equal.trans(M, B.orelse(K, V, B.min_go(K, V, l), e), B.orelse(K, V, SC.head(E.Entry<K, V>, T.io(K, V, l)), e), SC.head(E.Entry<K, V>, SC.append(E.Entry<K, V>, T.io(K, V, l), Con{e, T.io(K, V, r)})),
        Equal.cong(M, M, z => B.orelse(K, V, z, e), B.min_go(K, V, l), SC.head(E.Entry<K, V>, T.io(K, V, l)), min_ok(K, V, l)),
        Equal.sym(M, SC.head(E.Entry<K, V>, SC.append(E.Entry<K, V>, T.io(K, V, l), Con{e, T.io(K, V, r)})), B.orelse(K, V, SC.head(E.Entry<K, V>, T.io(K, V, l)), e), head_app(K, V, T.io(K, V, l), e, T.io(K, V, r))))

def max_ok(-K: Data, -V: Data, +t: B.Tree<K, V>) -> {B.max_go(K, V, t) == SC.last(E.Entry<K, V>, T.io(K, V, t)) : Maybe<&2, E.Entry<K, V>>}:
  match t:
    case B.Leaf{}:
      {==}
    case B.Node{+c, +l, +e, +r}:
      -M = Maybe<&2, E.Entry<K, V>>
      Equal.trans(M, B.orelse(K, V, B.max_go(K, V, r), e), B.orelse(K, V, SC.last(E.Entry<K, V>, T.io(K, V, r)), e), SC.last(E.Entry<K, V>, SC.append(E.Entry<K, V>, T.io(K, V, l), Con{e, T.io(K, V, r)})),
        Equal.cong(M, M, z => B.orelse(K, V, z, e), B.max_go(K, V, r), SC.last(E.Entry<K, V>, T.io(K, V, r)), max_ok(K, V, r)),
        Equal.sym(M, SC.last(E.Entry<K, V>, SC.append(E.Entry<K, V>, T.io(K, V, l), Con{e, T.io(K, V, r)})), B.orelse(K, V, SC.last(E.Entry<K, V>, T.io(K, V, r)), e), last_app(K, V, T.io(K, V, l), e, T.io(K, V, r))))

# ---- in-order listing ----

def entries_ok(-K: Data, -V: Data, +t: B.Tree<K, V>, +acc: List<&2, E.Entry<K, V>>) -> {B.entries(K, V, t, acc) == SC.append(E.Entry<K, V>, T.io(K, V, t), acc) : List<&2, E.Entry<K, V>>}:
  match t:
    case B.Leaf{}:
      {==}
    case B.Node{+c, +l, +e, +r}:
      -EE = E.Entry<K, V>
      Equal.trans(List<&2, EE>, B.entries(K, V, l, Con{e, B.entries(K, V, r, acc)}), SC.append(EE, T.io(K, V, l), Con{e, B.entries(K, V, r, acc)}), SC.append(EE, SC.append(EE, T.io(K, V, l), Con{e, T.io(K, V, r)}), acc),
        entries_ok(K, V, l, Con{e, B.entries(K, V, r, acc)}),
        Equal.trans(List<&2, EE>, SC.append(EE, T.io(K, V, l), Con{e, B.entries(K, V, r, acc)}), SC.append(EE, T.io(K, V, l), Con{e, SC.append(EE, T.io(K, V, r), acc)}), SC.append(EE, SC.append(EE, T.io(K, V, l), Con{e, T.io(K, V, r)}), acc),
          Equal.cong(List<&2, EE>, List<&2, EE>, z => SC.append(EE, T.io(K, V, l), Con{e, z}), B.entries(K, V, r, acc), SC.append(EE, T.io(K, V, r), acc), entries_ok(K, V, r, acc)),
          Equal.sym(List<&2, EE>, SC.append(EE, SC.append(EE, T.io(K, V, l), Con{e, T.io(K, V, r)}), acc), SC.append(EE, T.io(K, V, l), Con{e, SC.append(EE, T.io(K, V, r), acc)}), LL.append_assoc(EE, T.io(K, V, l), Con{e, T.io(K, V, r)}, acc))))

# ---- range (with subtree pruning) ----

# gz(go, xs) = Nil states "when go is False, xs is empty".
def gz(-K: Data, -V: Data, go: Bool, xs: List<&2, E.Entry<K, V>>) -> List<&2, E.Entry<K, V>>:
  match go:
    case True{}:
      Nil{}
    case False{}:
      xs

def pg_hi(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), -V: Data, +R: List<&2, E.Entry<K, V>>, +x: K, +lo: K, +hi: K, +h: {SO.above(~K, ~cmp, V, R, x) == True{} : Bool}, b: Bool, +eb: {Cmp.is_lt(cmp(x, hi)) == b : Bool}) -> {gz(K, V, Cmp.is_lt(cmp(x, hi)), S.range(~K, ~cmp, V, lo, hi, R)) == Nil{} : List<&2, E.Entry<K, V>>}:
  match b:
    case True{}:
      %Equal.sym(Bool, Cmp.is_lt(cmp(x, hi)), True{}, eb) : {gz(K, V, _, S.range(~K, ~cmp, V, lo, hi, R)) == Nil{} : List<&2, E.Entry<K, V>>}
      {==}
    case False{}:
      %Equal.sym(Bool, Cmp.is_lt(cmp(x, hi)), False{}, eb) : {gz(K, V, _, S.range(~K, ~cmp, V, lo, hi, R)) == Nil{} : List<&2, E.Entry<K, V>>}
      SP.range_high(~K, ~cmp, ~o, V, R, lo, hi, x, h, eb)

def pg_lo(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), -V: Data, +Ls: List<&2, E.Entry<K, V>>, +x: K, +lo: K, +hi: K, +h: {SO.below(~K, ~cmp, V, Ls, x) == True{} : Bool}, b: Bool, +eb: {Cmp.is_lt(cmp(lo, x)) == b : Bool}) -> {gz(K, V, Cmp.is_lt(cmp(lo, x)), S.range(~K, ~cmp, V, lo, hi, Ls)) == Nil{} : List<&2, E.Entry<K, V>>}:
  match b:
    case True{}:
      %Equal.sym(Bool, Cmp.is_lt(cmp(lo, x)), True{}, eb) : {gz(K, V, _, S.range(~K, ~cmp, V, lo, hi, Ls)) == Nil{} : List<&2, E.Entry<K, V>>}
      {==}
    case False{}:
      %Equal.sym(Bool, Cmp.is_lt(cmp(lo, x)), False{}, eb) : {gz(K, V, _, S.range(~K, ~cmp, V, lo, hi, Ls)) == Nil{} : List<&2, E.Entry<K, V>>}
      SP.range_low(~K, ~cmp, ~o, V, Ls, lo, hi, x, h, eb)

def pg_mid(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), -V: Data, +Ms: List<&2, E.Entry<K, V>>, +x1: K, +x2: K, +lo: K, +hi: K, +ha: {SO.above(~K, ~cmp, V, Ms, x1) == True{} : Bool}, +hb: {SO.below(~K, ~cmp, V, Ms, x2) == True{} : Bool}, b1: Bool, +eb1: {Cmp.is_lt(cmp(x1, hi)) == b1 : Bool}, b2: Bool, +eb2: {Cmp.is_lt(cmp(lo, x2)) == b2 : Bool}) -> {gz(K, V, Bool.and(Cmp.is_lt(cmp(x1, hi)), Cmp.is_lt(cmp(lo, x2))), S.range(~K, ~cmp, V, lo, hi, Ms)) == Nil{} : List<&2, E.Entry<K, V>>}:
  match b1 b2:
    case True{} True{}:
      %Equal.sym(Bool, Cmp.is_lt(cmp(x1, hi)), True{}, eb1) : {gz(K, V, Bool.and(_, Cmp.is_lt(cmp(lo, x2))), S.range(~K, ~cmp, V, lo, hi, Ms)) == Nil{} : List<&2, E.Entry<K, V>>}
      %Equal.sym(Bool, Cmp.is_lt(cmp(lo, x2)), True{}, eb2) : {gz(K, V, Bool.and(True{}, _), S.range(~K, ~cmp, V, lo, hi, Ms)) == Nil{} : List<&2, E.Entry<K, V>>}
      {==}
    case True{} False{}:
      %Equal.sym(Bool, Cmp.is_lt(cmp(x1, hi)), True{}, eb1) : {gz(K, V, Bool.and(_, Cmp.is_lt(cmp(lo, x2))), S.range(~K, ~cmp, V, lo, hi, Ms)) == Nil{} : List<&2, E.Entry<K, V>>}
      %Equal.sym(Bool, Cmp.is_lt(cmp(lo, x2)), False{}, eb2) : {gz(K, V, Bool.and(True{}, _), S.range(~K, ~cmp, V, lo, hi, Ms)) == Nil{} : List<&2, E.Entry<K, V>>}
      SP.range_low(~K, ~cmp, ~o, V, Ms, lo, hi, x2, hb, eb2)
    case False{} _:
      %Equal.sym(Bool, Cmp.is_lt(cmp(x1, hi)), False{}, eb1) : {gz(K, V, Bool.and(_, Cmp.is_lt(cmp(lo, x2))), S.range(~K, ~cmp, V, lo, hi, Ms)) == Nil{} : List<&2, E.Entry<K, V>>}
      SP.range_high(~K, ~cmp, ~o, V, Ms, lo, hi, x1, ha, eb1)

def cons_keep(-K: Data, -V: Data, +b: Bool, +e: E.Entry<K, V>, +rest: List<&2, E.Entry<K, V>>) -> {B.cons_if(K, V, b, e, rest) == S.keep_at(K, V, b, e, rest) : List<&2, E.Entry<K, V>>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def stp(-K: Data, -V: Data, +Lr: List<&2, E.Entry<K, V>>, +b: Bool, +e: E.Entry<K, V>, +Rr: List<&2, E.Entry<K, V>>, +acc: List<&2, E.Entry<K, V>>, +X: List<&2, E.Entry<K, V>>, +eX: {X == SC.append(E.Entry<K, V>, Rr, acc) : List<&2, E.Entry<K, V>>}) -> {SC.append(E.Entry<K, V>, Lr, B.cons_if(K, V, b, e, X)) == SC.append(E.Entry<K, V>, SC.append(E.Entry<K, V>, Lr, S.keep_at(K, V, b, e, Rr)), acc) : List<&2, E.Entry<K, V>>}:
  -EE = E.Entry<K, V>
  Equal.trans(List<&2, EE>, SC.append(EE, Lr, B.cons_if(K, V, b, e, X)), SC.append(EE, Lr, S.keep_at(K, V, b, e, SC.append(EE, Rr, acc))), SC.append(EE, SC.append(EE, Lr, S.keep_at(K, V, b, e, Rr)), acc),
    Equal.cong(List<&2, EE>, List<&2, EE>, z => SC.append(EE, Lr, z), B.cons_if(K, V, b, e, X), S.keep_at(K, V, b, e, SC.append(EE, Rr, acc)),
      Equal.trans(List<&2, EE>, B.cons_if(K, V, b, e, X), S.keep_at(K, V, b, e, X), S.keep_at(K, V, b, e, SC.append(EE, Rr, acc)), cons_keep(K, V, b, e, X), Equal.cong(List<&2, EE>, List<&2, EE>, z => S.keep_at(K, V, b, e, z), X, SC.append(EE, Rr, acc), eX))),
    Equal.trans(List<&2, EE>, SC.append(EE, Lr, S.keep_at(K, V, b, e, SC.append(EE, Rr, acc))), SC.append(EE, Lr, SC.append(EE, S.keep_at(K, V, b, e, Rr), acc)), SC.append(EE, SC.append(EE, Lr, S.keep_at(K, V, b, e, Rr)), acc),
      Equal.cong(List<&2, EE>, List<&2, EE>, z => SC.append(EE, Lr, z), S.keep_at(K, V, b, e, SC.append(EE, Rr, acc)), SC.append(EE, S.keep_at(K, V, b, e, Rr), acc), SP.keep_app(K, V, b, e, Rr, acc)),
      Equal.sym(List<&2, EE>, SC.append(EE, SC.append(EE, Lr, S.keep_at(K, V, b, e, Rr)), acc), SC.append(EE, Lr, SC.append(EE, S.keep_at(K, V, b, e, Rr), acc)), LL.append_assoc(EE, Lr, S.keep_at(K, V, b, e, Rr), acc))))

def rng_false(-K: Data, -V: Data, +xs: List<&2, E.Entry<K, V>>, +acc: List<&2, E.Entry<K, V>>, +pg: {xs == Nil{} : List<&2, E.Entry<K, V>>}) -> {acc == SC.append(E.Entry<K, V>, xs, acc) : List<&2, E.Entry<K, V>>}:
  %Equal.sym(List<&2, E.Entry<K, V>>, xs, Nil{}, pg) : {acc == SC.append(E.Entry<K, V>, _, acc) : List<&2, E.Entry<K, V>>}
  {==}

def rng_ok(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), -V: Data, +t: B.Tree<K, V>, +lo: K, +hi: K, +acc: List<&2, E.Entry<K, V>>, go: Bool, +s: {SO.sorted(~K, ~cmp, V, T.io(K, V, t)) == True{} : Bool}, +pg: {gz(K, V, go, S.range(~K, ~cmp, V, lo, hi, T.io(K, V, t))) == Nil{} : List<&2, E.Entry<K, V>>}) -> {B.rng(~K, ~cmp, V, t, lo, hi, acc, go) == SC.append(E.Entry<K, V>, S.range(~K, ~cmp, V, lo, hi, T.io(K, V, t)), acc) : List<&2, E.Entry<K, V>>}:
  match t go:
    case B.Leaf{} True{}:
      {==}
    case B.Leaf{} False{}:
      {==}
    case B.Node{+c, +l, +e, +r} False{}:
      rng_false(K, V, S.range(~K, ~cmp, V, lo, hi, T.io(K, V, B.Node{c, l, e, r})), acc, pg)
    case B.Node{+c, +l, +e, +r} True{}:
      -EE = E.Entry<K, V>
      +Lx = T.io(K, V, l)
      +Rx = T.io(K, V, r)
      +Y = B.rng(~K, ~cmp, V, r, lo, hi, acc, Cmp.is_lt(cmp(E.key(K, V, e), hi)))
      +X = B.cons_if(K, V, B.in_range(~K, ~cmp, lo, hi, E.key(K, V, e)), e, Y)
      Equal.trans(List<&2, EE>, B.rng(~K, ~cmp, V, l, lo, hi, X, Cmp.is_lt(cmp(lo, E.key(K, V, e)))), SC.append(EE, S.range(~K, ~cmp, V, lo, hi, Lx), X), SC.append(EE, S.range(~K, ~cmp, V, lo, hi, SC.append(EE, Lx, Con{e, Rx})), acc),
        rng_ok(~K, ~cmp, ~o, V, l, lo, hi, X, Cmp.is_lt(cmp(lo, E.key(K, V, e))), T.s2_l(~K, ~cmp, V, Lx, e, Rx, s), pg_lo(~K, ~cmp, ~o, V, Lx, E.key(K, V, e), lo, hi, SO.so_below(~K, ~cmp, V, Lx, e, Rx, s), Cmp.is_lt(cmp(lo, E.key(K, V, e))), {==})),
        Equal.trans(List<&2, EE>, SC.append(EE, S.range(~K, ~cmp, V, lo, hi, Lx), X), SC.append(EE, SC.append(EE, S.range(~K, ~cmp, V, lo, hi, Lx), S.keep_at(K, V, B.in_range(~K, ~cmp, lo, hi, E.key(K, V, e)), e, S.range(~K, ~cmp, V, lo, hi, Rx))), acc), SC.append(EE, S.range(~K, ~cmp, V, lo, hi, SC.append(EE, Lx, Con{e, Rx})), acc),
          stp(K, V, S.range(~K, ~cmp, V, lo, hi, Lx), B.in_range(~K, ~cmp, lo, hi, E.key(K, V, e)), e, S.range(~K, ~cmp, V, lo, hi, Rx), acc, Y,
            rng_ok(~K, ~cmp, ~o, V, r, lo, hi, acc, Cmp.is_lt(cmp(E.key(K, V, e), hi)), T.s2_r(~K, ~cmp, V, Lx, e, Rx, s), pg_hi(~K, ~cmp, ~o, V, Rx, E.key(K, V, e), lo, hi, T.s2_ab(~K, ~cmp, V, Lx, e, Rx, s), Cmp.is_lt(cmp(E.key(K, V, e), hi)), {==}))),
          Equal.cong(List<&2, EE>, List<&2, EE>, z => SC.append(EE, z, acc), SC.append(EE, S.range(~K, ~cmp, V, lo, hi, Lx), S.range(~K, ~cmp, V, lo, hi, Con{e, Rx})), S.range(~K, ~cmp, V, lo, hi, SC.append(EE, Lx, Con{e, Rx})), Equal.sym(List<&2, EE>, S.range(~K, ~cmp, V, lo, hi, SC.append(EE, Lx, Con{e, Rx})), SC.append(EE, S.range(~K, ~cmp, V, lo, hi, Lx), S.range(~K, ~cmp, V, lo, hi, Con{e, Rx})), SP.range_app(~K, ~cmp, V, Lx, Con{e, Rx}, lo, hi)))))

def range_ok(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), -V: Data, +t: B.Tree<K, V>, +lo: K, +hi: K, +s: {SO.sorted(~K, ~cmp, V, T.io(K, V, t)) == True{} : Bool}) -> {B.rng(~K, ~cmp, V, t, lo, hi, Nil{}, True{}) == S.range(~K, ~cmp, V, lo, hi, T.io(K, V, t)) : List<&2, E.Entry<K, V>>}:
  Equal.trans(List<&2, E.Entry<K, V>>, B.rng(~K, ~cmp, V, t, lo, hi, Nil{}, True{}), SC.append(E.Entry<K, V>, S.range(~K, ~cmp, V, lo, hi, T.io(K, V, t)), Nil{}), S.range(~K, ~cmp, V, lo, hi, T.io(K, V, t)),
    rng_ok(~K, ~cmp, ~o, V, t, lo, hi, Nil{}, True{}, s, {==}),
    LL.append_nil(E.Entry<K, V>, S.range(~K, ~cmp, V, lo, hi, T.io(K, V, t))))
