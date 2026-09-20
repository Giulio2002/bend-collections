import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../../spec/common.bend as SC
import ../../src/balanced_search_tree.bend as B
import ../../src/doubly_linked_list.bend as D
import ../../types/doubly_linked_list.bend as E
import ../../types/balanced_search_tree.bend as BE
import ./nodes.bend as NS
import ./links.bend as LK

# List facts for the relinking proofs: distinct ids, membership, the
# fresh-id bound, lengths and the head/tail pointers of joined runs.

def allLt(xs: List<&2, Nat>, +n: Nat) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{h, t}:
      Bool.and(Nat.is_lt(h, n), allLt(t, n))

def okM(a: Maybe<&2, Nat>, l: List<&2, Nat>) -> Bool:
  match a:
    case None{}:
      True{}
    case Some{z}:
      NS.mem(z, l)

def or_split_l(+a: Bool, +b: Bool, +h: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  LK.or_false_l(a, b, h)

def or_mid_true(+a: Bool, +b: Bool, +c: Bool, +h: {Bool.or(a, c) == True{} : Bool}) -> {Bool.or(a, Bool.or(b, c)) == True{} : Bool}:
  match a b:
    case True{} _:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      h

def or_left_true(+a: Bool, +b: Bool, +h: {a == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({Bool.or(False{}, b) == True{} : Bool}, L.false_true(h))

def mem_appL(+k: Nat, +xs: List<&2, Nat>, +ys: List<&2, Nat>, +h: {NS.mem(k, xs) == True{} : Bool}) -> {NS.mem(k, SC.append(Nat, xs, ys)) == True{} : Bool}:
  L.subst(Bool, z => {z == True{} : Bool}, Bool.or(NS.mem(k, xs), NS.mem(k, ys)), NS.mem(k, SC.append(Nat, xs, ys)), Equal.sym(Bool, NS.mem(k, SC.append(Nat, xs, ys)), Bool.or(NS.mem(k, xs), NS.mem(k, ys)), NS.mem_app(k, xs, ys)), or_left_true(NS.mem(k, xs), NS.mem(k, ys), h))

def mem_appR(+k: Nat, +xs: List<&2, Nat>, +ys: List<&2, Nat>, +h: {NS.mem(k, ys) == True{} : Bool}) -> {NS.mem(k, SC.append(Nat, xs, ys)) == True{} : Bool}:
  L.subst(Bool, z => {z == True{} : Bool}, Bool.or(NS.mem(k, xs), NS.mem(k, ys)), NS.mem(k, SC.append(Nat, xs, ys)), Equal.sym(Bool, NS.mem(k, SC.append(Nat, xs, ys)), Bool.or(NS.mem(k, xs), NS.mem(k, ys)), NS.mem_app(k, xs, ys)),
    L.subst(Bool, z => {Bool.or(NS.mem(k, xs), z) == True{} : Bool}, True{}, NS.mem(k, ys), Equal.sym(Bool, NS.mem(k, ys), True{}, h), LK.or_true(NS.mem(k, xs))))

def mem_split(+k: Nat, +xs: List<&2, Nat>, +ys: List<&2, Nat>, +h: {NS.mem(k, SC.append(Nat, xs, ys)) == False{} : Bool}) -> {Bool.or(NS.mem(k, xs), NS.mem(k, ys)) == False{} : Bool}:
  Equal.trans(Bool, Bool.or(NS.mem(k, xs), NS.mem(k, ys)), NS.mem(k, SC.append(Nat, xs, ys)), False{}, Equal.sym(Bool, NS.mem(k, SC.append(Nat, xs, ys)), Bool.or(NS.mem(k, xs), NS.mem(k, ys)), NS.mem_app(k, xs, ys)), h)

def mem_self(+j: Nat, +t: List<&2, Nat>) -> {NS.mem(j, Con{j, t}) == True{} : Bool}:
  L.subst(Bool, z => {Bool.or(z, NS.mem(j, t)) == True{} : Bool}, True{}, Nat.is_eq(j, j), Equal.sym(Bool, Nat.is_eq(j, j), True{}, N.is_eq_refl(j)), {==})

def okM_of(a: Maybe<&2, Nat>, +l: List<&2, Nat>, +h: {LK.memM(a, l) == True{} : Bool}) -> {okM(a, l) == True{} : Bool}:
  match a:
    case None{}:
      Empty.absurd({True{} == True{} : Bool}, L.false_true(h))
    case Some{z}:
      h

# ---- distinct ids ----

def dist_l(+xs: List<&2, Nat>, +ys: List<&2, Nat>, +d: {LK.dist(SC.append(Nat, xs, ys)) == True{} : Bool}) -> {LK.dist(xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      +m = LK.dist_head(h, SC.append(Nat, t, ys), d)
      L.and_intro(Bool.not(NS.mem(h, t)), LK.dist(t),
        L.subst(Bool, z => {Bool.not(z) == True{} : Bool}, False{}, NS.mem(h, t), Equal.sym(Bool, NS.mem(h, t), False{}, LK.or_false_l(NS.mem(h, t), NS.mem(h, ys), mem_split(h, t, ys, m))), {==}),
        dist_l(t, ys, LK.dist_tail(h, SC.append(Nat, t, ys), d)))

def dist_r(+xs: List<&2, Nat>, +ys: List<&2, Nat>, +d: {LK.dist(SC.append(Nat, xs, ys)) == True{} : Bool}) -> {LK.dist(ys) == True{} : Bool}:
  match xs:
    case Nil{}:
      d
    case Con{+h, +t}:
      dist_r(t, ys, LK.dist_tail(h, SC.append(Nat, t, ys), d))

# A member of ys is not a member of xs when xs ++ ys is distinct.
def disj_c(+k: Nat, +h: Nat, +t: List<&2, Nat>, +ys: List<&2, Nat>, +mk: {NS.mem(k, ys) == True{} : Bool}, +d: {LK.dist(Con{h, SC.append(Nat, t, ys)}) == True{} : Bool}, +ih: {NS.mem(k, t) == False{} : Bool}) -> {NS.mem(k, Con{h, t}) == False{} : Bool}:
  +ne = LK.ne_flip(h, k, LK.ne_of_mem(h, k, SC.append(Nat, t, ys), mem_appR(k, t, ys, mk), LK.dist_head(h, SC.append(Nat, t, ys), d), Nat.is_eq(h, k), {==}))
  %Equal.sym(Bool, Nat.is_eq(k, h), False{}, ne) : {Bool.or(_, NS.mem(k, t)) == False{} : Bool}
  ih

def disj(+xs: List<&2, Nat>, +ys: List<&2, Nat>, +k: Nat, +d: {LK.dist(SC.append(Nat, xs, ys)) == True{} : Bool}, +mk: {NS.mem(k, ys) == True{} : Bool}) -> {NS.mem(k, xs) == False{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      disj_c(k, h, t, ys, mk, d, disj(t, ys, k, LK.dist_tail(h, SC.append(Nat, t, ys), d), mk))

def disjR_c(+k: Nat, +h: Nat, +t: List<&2, Nat>, +ys: List<&2, Nat>, b: Bool, +eb: {Nat.is_eq(k, h) == b : Bool}, +mk: {NS.mem(k, Con{h, t}) == True{} : Bool}, +d: {LK.dist(Con{h, SC.append(Nat, t, ys)}) == True{} : Bool}, ih: @+m2: {NS.mem(k, t) == True{} : Bool} -> {NS.mem(k, ys) == False{} : Bool}) -> {NS.mem(k, ys) == False{} : Bool}:
  match b:
    case True{}:
      L.subst(Nat, z => {NS.mem(z, ys) == False{} : Bool}, h, k, Equal.sym(Nat, k, h, N.eq_from_is_eq(k, h, eb)), LK.or_false_r(NS.mem(h, t), NS.mem(h, ys), mem_split(h, t, ys, LK.dist_head(h, SC.append(Nat, t, ys), d))))
    case False{}:
      ih(L.subst(Bool, z => {Bool.or(z, NS.mem(k, t)) == True{} : Bool}, Nat.is_eq(k, h), False{}, eb, mk))

def disjR(+xs: List<&2, Nat>, +ys: List<&2, Nat>, +k: Nat, +d: {LK.dist(SC.append(Nat, xs, ys)) == True{} : Bool}, +mk: {NS.mem(k, xs) == True{} : Bool}) -> {NS.mem(k, ys) == False{} : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({NS.mem(k, ys) == False{} : Bool}, L.false_true(mk))
    case Con{+h, +t}:
      disjR_c(k, h, t, ys, Nat.is_eq(k, h), {==}, mk, d, m2 => disjR(t, ys, k, LK.dist_tail(h, SC.append(Nat, t, ys), d), m2))

def dist_mid(+xs: List<&2, Nat>, +n: Nat, +ys: List<&2, Nat>, +d: {LK.dist(SC.append(Nat, xs, ys)) == True{} : Bool}, +m: {NS.mem(n, SC.append(Nat, xs, ys)) == False{} : Bool}) -> {LK.dist(SC.append(Nat, xs, Con{n, ys})) == True{} : Bool}:
  match xs:
    case Nil{}:
      L.and_intro(Bool.not(NS.mem(n, ys)), LK.dist(ys), L.subst(Bool, z => {Bool.not(z) == True{} : Bool}, False{}, NS.mem(n, ys), Equal.sym(Bool, NS.mem(n, ys), False{}, m), {==}), d)
    case Con{+h, +t}:
      +mh = mem_split(h, t, ys, LK.dist_head(h, SC.append(Nat, t, ys), d))
      +mn = m
      +nh = LK.ne_flip(n, h, LK.or_false_l(Nat.is_eq(n, h), NS.mem(n, SC.append(Nat, t, ys)), mn))
      +mf = Equal.trans(Bool, NS.mem(h, SC.append(Nat, t, Con{n, ys})), Bool.or(NS.mem(h, t), NS.mem(h, Con{n, ys})), False{}, NS.mem_app(h, t, Con{n, ys}),
        L.subst(Bool, z => {Bool.or(z, Bool.or(Nat.is_eq(h, n), NS.mem(h, ys))) == False{} : Bool}, False{}, NS.mem(h, t), Equal.sym(Bool, NS.mem(h, t), False{}, LK.or_false_l(NS.mem(h, t), NS.mem(h, ys), mh)),
          L.subst(Bool, z => {Bool.or(z, NS.mem(h, ys)) == False{} : Bool}, False{}, Nat.is_eq(h, n), Equal.sym(Bool, Nat.is_eq(h, n), False{}, nh), LK.or_false_r(NS.mem(h, t), NS.mem(h, ys), mh))))
      L.and_intro(Bool.not(NS.mem(h, SC.append(Nat, t, Con{n, ys}))), LK.dist(SC.append(Nat, t, Con{n, ys})),
        L.subst(Bool, z => {Bool.not(z) == True{} : Bool}, False{}, NS.mem(h, SC.append(Nat, t, Con{n, ys})), Equal.sym(Bool, NS.mem(h, SC.append(Nat, t, Con{n, ys})), False{}, mf), {==}),
        dist_mid(t, n, ys, LK.dist_tail(h, SC.append(Nat, t, ys), d), LK.or_false_r(Nat.is_eq(n, h), NS.mem(n, SC.append(Nat, t, ys)), mn)))

def dist_del(+xs: List<&2, Nat>, +n: Nat, +ys: List<&2, Nat>, +d: {LK.dist(SC.append(Nat, xs, Con{n, ys})) == True{} : Bool}) -> {LK.dist(SC.append(Nat, xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      LK.dist_tail(n, ys, d)
    case Con{+h, +t}:
      +m1 = mem_split(h, t, Con{n, ys}, LK.dist_head(h, SC.append(Nat, t, Con{n, ys}), d))
      +mt = LK.or_false_l(NS.mem(h, t), NS.mem(h, Con{n, ys}), m1)
      +my = LK.or_false_r(Nat.is_eq(h, n), NS.mem(h, ys), LK.or_false_r(NS.mem(h, t), NS.mem(h, Con{n, ys}), m1))
      +mf = Equal.trans(Bool, NS.mem(h, SC.append(Nat, t, ys)), Bool.or(NS.mem(h, t), NS.mem(h, ys)), False{}, NS.mem_app(h, t, ys),
        L.subst(Bool, z => {Bool.or(z, NS.mem(h, ys)) == False{} : Bool}, False{}, NS.mem(h, t), Equal.sym(Bool, NS.mem(h, t), False{}, mt), my))
      L.and_intro(Bool.not(NS.mem(h, SC.append(Nat, t, ys))), LK.dist(SC.append(Nat, t, ys)),
        L.subst(Bool, z => {Bool.not(z) == True{} : Bool}, False{}, NS.mem(h, SC.append(Nat, t, ys)), Equal.sym(Bool, NS.mem(h, SC.append(Nat, t, ys)), False{}, mf), {==}),
        dist_del(t, n, ys, LK.dist_tail(h, SC.append(Nat, t, Con{n, ys}), d)))

# ---- the fresh-id bound ----

def notmem_lt(+l: List<&2, Nat>, +n: Nat, +h: {allLt(l, n) == True{} : Bool}) -> {NS.mem(n, l) == False{} : Bool}:
  match l:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +ne = LK.ne_flip(x, n, N.is_eq_lt(x, n, L.and_left(Nat.is_lt(x, n), allLt(t, n), h)))
      %Equal.sym(Bool, Nat.is_eq(n, x), False{}, ne) : {Bool.or(_, NS.mem(n, t)) == False{} : Bool}
      notmem_lt(t, n, L.and_right(Nat.is_lt(x, n), allLt(t, n), h))

def lt_succ_all(+l: List<&2, Nat>, +k: Nat, +h: {allLt(l, k) == True{} : Bool}) -> {allLt(l, 1n+k) == True{} : Bool}:
  match l:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      L.and_intro(Nat.is_lt(x, 1n+k), allLt(t, 1n+k), N.lt_trans(x, k, 1n+k, L.and_left(Nat.is_lt(x, k), allLt(t, k), h), N.lt_succ(k)), lt_succ_all(t, k, L.and_right(Nat.is_lt(x, k), allLt(t, k), h)))

def lt_mid(+xs: List<&2, Nat>, +ys: List<&2, Nat>, +k: Nat, +h: {allLt(SC.append(Nat, xs, ys), k) == True{} : Bool}) -> {allLt(SC.append(Nat, xs, Con{k, ys}), 1n+k) == True{} : Bool}:
  match xs:
    case Nil{}:
      L.and_intro(Nat.is_lt(k, 1n+k), allLt(ys, 1n+k), N.lt_succ(k), lt_succ_all(ys, k, h))
    case Con{+x, +t}:
      L.and_intro(Nat.is_lt(x, 1n+k), allLt(SC.append(Nat, t, Con{k, ys}), 1n+k), N.lt_trans(x, k, 1n+k, L.and_left(Nat.is_lt(x, k), allLt(SC.append(Nat, t, ys), k), h), N.lt_succ(k)), lt_mid(t, ys, k, L.and_right(Nat.is_lt(x, k), allLt(SC.append(Nat, t, ys), k), h)))

def lt_del(+xs: List<&2, Nat>, +n: Nat, +ys: List<&2, Nat>, +k: Nat, +h: {allLt(SC.append(Nat, xs, Con{n, ys}), k) == True{} : Bool}) -> {allLt(SC.append(Nat, xs, ys), k) == True{} : Bool}:
  match xs:
    case Nil{}:
      L.and_right(Nat.is_lt(n, k), allLt(ys, k), h)
    case Con{+x, +t}:
      L.and_intro(Nat.is_lt(x, k), allLt(SC.append(Nat, t, ys), k), L.and_left(Nat.is_lt(x, k), allLt(SC.append(Nat, t, Con{n, ys}), k), h), lt_del(t, n, ys, k, L.and_right(Nat.is_lt(x, k), allLt(SC.append(Nat, t, Con{n, ys}), k), h)))

def len_mid(-T: Data, +xs: List<&2, E.Item<T>>, +y: E.Item<T>, +ys: List<&2, E.Item<T>>) -> {SC.length(E.Item<T>, SC.append(E.Item<T>, xs, Con{y, ys})) == 1n+SC.length(E.Item<T>, SC.append(E.Item<T>, xs, ys)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      Equal.cong(Nat, Nat, z => 1n+z, SC.length(E.Item<T>, SC.append(E.Item<T>, t, Con{y, ys})), 1n+SC.length(E.Item<T>, SC.append(E.Item<T>, t, ys)), len_mid(T, t, y, ys))

# ---- membership of the new/remaining ids ----

def mem_ext(+k: Nat, +xs: List<&2, Nat>, +n: Nat, +ys: List<&2, Nat>, +m: {NS.mem(k, SC.append(Nat, xs, ys)) == True{} : Bool}) -> {NS.mem(k, SC.append(Nat, xs, Con{n, ys})) == True{} : Bool}:
  L.subst(Bool, z => {z == True{} : Bool}, Bool.or(NS.mem(k, xs), Bool.or(Nat.is_eq(k, n), NS.mem(k, ys))), NS.mem(k, SC.append(Nat, xs, Con{n, ys})), Equal.sym(Bool, NS.mem(k, SC.append(Nat, xs, Con{n, ys})), Bool.or(NS.mem(k, xs), NS.mem(k, Con{n, ys})), NS.mem_app(k, xs, Con{n, ys})),
    or_mid_true(NS.mem(k, xs), Nat.is_eq(k, n), NS.mem(k, ys), L.subst(Bool, z => {z == True{} : Bool}, NS.mem(k, SC.append(Nat, xs, ys)), Bool.or(NS.mem(k, xs), NS.mem(k, ys)), NS.mem_app(k, xs, ys), m)))

def allin_ext(-T: Data, +xs: List<&2, BE.Entry<Nat, D.Node<T>>>, +ls: List<&2, Nat>, +n: Nat, +ys: List<&2, Nat>, +a: {NS.allin(T, xs, SC.append(Nat, ls, ys)) == True{} : Bool}) -> {NS.allin(T, xs, SC.append(Nat, ls, Con{n, ys})) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      L.and_intro(NS.mem(BE.key(Nat, D.Node<T>, e), SC.append(Nat, ls, Con{n, ys})), NS.allin(T, t, SC.append(Nat, ls, Con{n, ys})), mem_ext(BE.key(Nat, D.Node<T>, e), ls, n, ys, L.and_left(NS.mem(BE.key(Nat, D.Node<T>, e), SC.append(Nat, ls, ys)), NS.allin(T, t, SC.append(Nat, ls, ys)), a)), allin_ext(T, t, ls, n, ys, L.and_right(NS.mem(BE.key(Nat, D.Node<T>, e), SC.append(Nat, ls, ys)), NS.allin(T, t, SC.append(Nat, ls, ys)), a)))

def memM_appL(a: Maybe<&2, Nat>, +xs: List<&2, Nat>, +ys: List<&2, Nat>, +h: {LK.memM(a, xs) == True{} : Bool}) -> {okM(a, SC.append(Nat, xs, ys)) == True{} : Bool}:
  match a:
    case None{}:
      {==}
    case Some{+z}:
      mem_appL(z, xs, ys, h)

# The first id of ys and the last id of xs are members of xs ++ (anything) ++ ys.
def ok_fst(+xs: List<&2, Nat>, +ys: List<&2, Nat>) -> {okM(LK.fst(ys, None{}), SC.append(Nat, xs, ys)) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{+j, +t}:
      mem_appR(j, xs, Con{j, t}, mem_self(j, t))

def ok_lst(+xs: List<&2, Nat>, +ys: List<&2, Nat>) -> {okM(LK.lst(xs, None{}), SC.append(Nat, xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+j, +t}:
      memM_appL(LK.lst(t, Some{j}), Con{j, t}, ys, LK.lst_mem(t, j))

def memM_disj(a: Maybe<&2, Nat>, +xs: List<&2, Nat>, +ys: List<&2, Nat>, +d: {LK.dist(SC.append(Nat, xs, ys)) == True{} : Bool}, +h: {LK.memM(a, xs) == True{} : Bool}) -> {LK.memM(a, ys) == False{} : Bool}:
  match a:
    case None{}:
      {==}
    case Some{+z}:
      disjR(xs, ys, z, d, h)

# The neighbours relinked by link/unlink lie outside the other run.
def disj_fst(+xs: List<&2, Nat>, +ys: List<&2, Nat>, +d: {LK.dist(SC.append(Nat, xs, ys)) == True{} : Bool}) -> {LK.memM(LK.fst(ys, None{}), xs) == False{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{+j, +t}:
      disj(xs, Con{j, t}, j, d, mem_self(j, t))

def disj_lst(+xs: List<&2, Nat>, +ys: List<&2, Nat>, +d: {LK.dist(SC.append(Nat, xs, ys)) == True{} : Bool}) -> {LK.memM(LK.lst(xs, None{}), ys) == False{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+j, +t}:
      memM_disj(LK.lst(t, Some{j}), Con{j, t}, ys, d, LK.lst_mem(t, j))

def memM_lst(+xs: List<&2, Nat>) -> {okM(LK.lst(xs, None{}), xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+j, +t}:
      okM_of(LK.lst(t, Some{j}), Con{j, t}, LK.lst_mem(t, j))

# ---- relinking one neighbour ----

def node_sn_skip(-T: Data, +nodes: B.OrdMap<Nat, D.Node<T>>, a: Maybe<&2, Nat>, +q2: Maybe<&2, Nat>, +i: Nat, +l: List<&2, Nat>, +g: {NS.ninv(T, nodes) == True{} : Bool}, +ok: {okM(a, l) == True{} : Bool}, +mi: {NS.mem(i, l) == False{} : Bool}) -> {D.node(T, D.set_next(T, nodes, a, q2), i) == D.node(T, nodes, i) : Maybe<&2, D.Node<T>>}:
  match a:
    case None{}:
      {==}
    case Some{+z}:
      NS.wn_other(T, D.node(T, nodes, z), nodes, z, q2, i, g, LK.ne_of_mem(i, z, l, ok, mi, Nat.is_eq(i, z), {==}))

def node_sp_skip(-T: Data, +nodes: B.OrdMap<Nat, D.Node<T>>, b: Maybe<&2, Nat>, +p2: Maybe<&2, Nat>, +i: Nat, +l: List<&2, Nat>, +g: {NS.ninv(T, nodes) == True{} : Bool}, +ok: {okM(b, l) == True{} : Bool}, +mi: {NS.mem(i, l) == False{} : Bool}) -> {D.node(T, D.set_prev(T, nodes, b, p2), i) == D.node(T, nodes, i) : Maybe<&2, D.Node<T>>}:
  match b:
    case None{}:
      {==}
    case Some{+z}:
      NS.wp_other(T, D.node(T, nodes, z), nodes, z, p2, i, g, LK.ne_of_mem(i, z, l, ok, mi, Nat.is_eq(i, z), {==}))

def allin_wn(-T: Data, m: Maybe<&2, D.Node<T>>, +nodes: B.OrdMap<Nat, D.Node<T>>, +z: Nat, q2: Maybe<&2, Nat>, +l: List<&2, Nat>, +g: {NS.ninv(T, nodes) == True{} : Bool}, +a: {NS.allin(T, NS.nabs(T, nodes), l) == True{} : Bool}, +mz: {NS.mem(z, l) == True{} : Bool}) -> {NS.allin(T, NS.nabs(T, D.with_next(T, m, nodes, z, q2)), l) == True{} : Bool}:
  match m:
    case None{}:
      a
    case Some{D.N{v, p, n}}:
      NS.allin_put(T, nodes, z, D.N{v, p, q2}, l, g, a, mz)

def allin_wp(-T: Data, m: Maybe<&2, D.Node<T>>, +nodes: B.OrdMap<Nat, D.Node<T>>, +z: Nat, p2: Maybe<&2, Nat>, +l: List<&2, Nat>, +g: {NS.ninv(T, nodes) == True{} : Bool}, +a: {NS.allin(T, NS.nabs(T, nodes), l) == True{} : Bool}, +mz: {NS.mem(z, l) == True{} : Bool}) -> {NS.allin(T, NS.nabs(T, D.with_prev(T, m, nodes, z, p2)), l) == True{} : Bool}:
  match m:
    case None{}:
      a
    case Some{D.N{v, p, n}}:
      NS.allin_put(T, nodes, z, D.N{v, p2, n}, l, g, a, mz)

def allin_sn(-T: Data, +nodes: B.OrdMap<Nat, D.Node<T>>, a: Maybe<&2, Nat>, +q2: Maybe<&2, Nat>, +l: List<&2, Nat>, +g: {NS.ninv(T, nodes) == True{} : Bool}, +al: {NS.allin(T, NS.nabs(T, nodes), l) == True{} : Bool}, +ok: {okM(a, l) == True{} : Bool}) -> {NS.allin(T, NS.nabs(T, D.set_next(T, nodes, a, q2)), l) == True{} : Bool}:
  match a:
    case None{}:
      al
    case Some{+z}:
      allin_wn(T, D.node(T, nodes, z), nodes, z, q2, l, g, al, ok)

def allin_sp(-T: Data, +nodes: B.OrdMap<Nat, D.Node<T>>, b: Maybe<&2, Nat>, +p2: Maybe<&2, Nat>, +l: List<&2, Nat>, +g: {NS.ninv(T, nodes) == True{} : Bool}, +al: {NS.allin(T, NS.nabs(T, nodes), l) == True{} : Bool}, +ok: {okM(b, l) == True{} : Bool}) -> {NS.allin(T, NS.nabs(T, D.set_prev(T, nodes, b, p2)), l) == True{} : Bool}:
  match b:
    case None{}:
      al
    case Some{+z}:
      allin_wp(T, D.node(T, nodes, z), nodes, z, p2, l, g, al, ok)

# ---- head and tail pointers ----

def end_link_some(+xs: List<&2, Nat>, +j: Nat, +n: Nat, +e: Maybe<&2, Nat>) -> {D.end_link(LK.lst(xs, Some{j}), n, e) == e : Maybe<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      end_link_some(t, h, n, e)

def end_unlink_some(+xs: List<&2, Nat>, +j: Nat, +b: Maybe<&2, Nat>, +e: Maybe<&2, Nat>) -> {D.end_unlink(LK.lst(xs, Some{j}), b, e) == e : Maybe<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      end_unlink_some(t, h, b, e)

def head_link(-T: Data, +P: List<&2, E.Item<T>>, +Q: List<&2, E.Item<T>>, +n: Nat, +x: T, +head: Maybe<&2, Nat>, +eh: {head == LK.fst(NS.ids(T, SC.append(E.Item<T>, P, Q)), None{}) : Maybe<&2, Nat>}) -> {D.end_link(LK.lst(NS.ids(T, P), None{}), n, head) == LK.fst(NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{n, x}, Q})), None{}) : Maybe<&2, Nat>}:
  match P:
    case Nil{}:
      {==}
    case Con{E.Item{+j, +w}, +t}:
      Equal.trans(Maybe<&2, Nat>, D.end_link(LK.lst(NS.ids(T, t), Some{j}), n, head), head, Some{j}, end_link_some(NS.ids(T, t), j, n, head), eh)

def tail_link(-T: Data, +P: List<&2, E.Item<T>>, +Q: List<&2, E.Item<T>>, +n: Nat, +x: T, +tail: Maybe<&2, Nat>, +et: {tail == LK.lst(NS.ids(T, SC.append(E.Item<T>, P, Q)), None{}) : Maybe<&2, Nat>}) -> {D.end_link(LK.fst(NS.ids(T, Q), None{}), n, tail) == LK.lst(NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{n, x}, Q})), None{}) : Maybe<&2, Nat>}:
  match Q:
    case Nil{}:
      Equal.sym(Maybe<&2, Nat>, LK.lst(NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{n, x}, Nil{}})), None{}), Some{n}, LK.lst_ids_app(T, P, Con{E.Item{n, x}, Nil{}}, None{}))
    case Con{E.Item{+j, +w}, +t}:
      Equal.trans(Maybe<&2, Nat>, tail, LK.lst(NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{j, w}, t})), None{}), LK.lst(NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{n, x}, Con{E.Item{j, w}, t}})), None{}),
        et,
        Equal.trans(Maybe<&2, Nat>, LK.lst(NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{j, w}, t})), None{}), LK.lst(NS.ids(T, t), Some{j}), LK.lst(NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{n, x}, Con{E.Item{j, w}, t}})), None{}),
          LK.lst_ids_app(T, P, Con{E.Item{j, w}, t}, None{}),
          Equal.sym(Maybe<&2, Nat>, LK.lst(NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{n, x}, Con{E.Item{j, w}, t}})), None{}), LK.lst(NS.ids(T, t), Some{j}), LK.lst_ids_app(T, P, Con{E.Item{n, x}, Con{E.Item{j, w}, t}}, None{}))))

def head_unlink(-T: Data, +P: List<&2, E.Item<T>>, +h: Nat, +v: T, +Q: List<&2, E.Item<T>>, +head: Maybe<&2, Nat>, +eh: {head == LK.fst(NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{h, v}, Q})), None{}) : Maybe<&2, Nat>}) -> {D.end_unlink(LK.lst(NS.ids(T, P), None{}), LK.fst(NS.ids(T, Q), None{}), head) == LK.fst(NS.ids(T, SC.append(E.Item<T>, P, Q)), None{}) : Maybe<&2, Nat>}:
  match P:
    case Nil{}:
      {==}
    case Con{E.Item{+j, +w}, +t}:
      Equal.trans(Maybe<&2, Nat>, D.end_unlink(LK.lst(NS.ids(T, t), Some{j}), LK.fst(NS.ids(T, Q), None{}), head), head, Some{j}, end_unlink_some(NS.ids(T, t), j, LK.fst(NS.ids(T, Q), None{}), head), eh)

def tail_unlink(-T: Data, +P: List<&2, E.Item<T>>, +h: Nat, +v: T, +Q: List<&2, E.Item<T>>, +tail: Maybe<&2, Nat>, +et: {tail == LK.lst(NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{h, v}, Q})), None{}) : Maybe<&2, Nat>}) -> {D.end_unlink(LK.fst(NS.ids(T, Q), None{}), LK.lst(NS.ids(T, P), None{}), tail) == LK.lst(NS.ids(T, SC.append(E.Item<T>, P, Q)), None{}) : Maybe<&2, Nat>}:
  match Q:
    case Nil{}:
      Equal.sym(Maybe<&2, Nat>, LK.lst(NS.ids(T, SC.append(E.Item<T>, P, Nil{})), None{}), LK.lst(NS.ids(T, P), None{}), LK.lst_ids_app(T, P, Nil{}, None{}))
    case Con{E.Item{+j, +w}, +t}:
      Equal.trans(Maybe<&2, Nat>, tail, LK.lst(NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{h, v}, Con{E.Item{j, w}, t}})), None{}), LK.lst(NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{j, w}, t})), None{}),
        et,
        Equal.trans(Maybe<&2, Nat>, LK.lst(NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{h, v}, Con{E.Item{j, w}, t}})), None{}), LK.lst(NS.ids(T, t), Some{j}), LK.lst(NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{j, w}, t})), None{}),
          LK.lst_ids_app(T, P, Con{E.Item{h, v}, Con{E.Item{j, w}, t}}, None{}),
          Equal.sym(Maybe<&2, Nat>, LK.lst(NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{j, w}, t})), None{}), LK.lst(NS.ids(T, t), Some{j}), LK.lst_ids_app(T, P, Con{E.Item{j, w}, t}, None{}))))

# ---- the whole representation invariant, for a candidate item sequence ----

def Good(-T: Data, nodes: B.OrdMap<Nat, D.Node<T>>, head: Maybe<&2, Nat>, tail: Maybe<&2, Nat>, count: Nat, fresh: Nat, xs: List<&2, E.Item<T>>) -> Type:
  {NS.ninv(T, nodes) == True{} : Bool} & (LK.lk(T, nodes, xs, None{}, None{}) & ({head == LK.fst(NS.ids(T, xs), None{}) : Maybe<&2, Nat>} & ({tail == LK.lst(NS.ids(T, xs), None{}) : Maybe<&2, Nat>} & ({count == SC.length(E.Item<T>, xs) : Nat} & ({LK.dist(NS.ids(T, xs)) == True{} : Bool} & ({NS.allin(T, NS.nabs(T, nodes), NS.ids(T, xs)) == True{} : Bool} & {allLt(NS.ids(T, xs), fresh) == True{} : Bool}))))))
