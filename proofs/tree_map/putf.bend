import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/order.bend as O
import ../spec/common.bend as SC
import ../spec/tree_map.bend as S
import ../../src/containers/balanced_search_tree.bend as M
import ../hash_table/state.bend as HT
import ../lru/state.bend as LST
import ../lru/lists.bend as LS
import ./state.bend as ST
import ./mirror.bend as MI
import ./ok.bend as OK
import ./tree.bend as TR
import ./find.bend as FI
import ./ends.bend as EN
import ./path.bend as P
import ./plug.bend as PG
import ./prim.bend as PR
import ./ord.bend as OR
import ./slot.bend as SL
import ./alls.bend as AL
import ./dj.bend as DJ
import ./agree.bend as AG
import ./navs.bend as NS
import ./spath.bend as SP

# A key found: the payload at its node is the specification's lookup, and
# exchanging it is the specification's set_val; the invariant holds with the
# new payload list. (source: tools/generators/tm_hand/putf.src)


# setting the value of the entry equal to k
def set_val_mid(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +k: K, +v: V, +xs: List<&2, M.Entry<K, V>>, +e: M.Entry<K, V>, +ys: List<&2, M.Entry<K, V>>, +hl: {OR.ltall(~K, ~V, ~cmp, k, xs) == True{} : Bool}, +hc: {cmp(k, S.key(K, V, e)) == EQ{} : Cmp}) -> {S.set_val(~K, ~V, ~cmp, k, v, SC.append(M.Entry<K, V>, xs, Con{e, ys})) == SC.append(M.Entry<K, V>, xs, Con{M.Entry{S.key(K, V, e), v}, ys}) : List<&2, M.Entry<K, V>>}:
  match xs:
    case Nil{}:
      %Equal.sym(Cmp, cmp(k, S.key(K, V, e)), EQ{}, hc) : {S.pick(List<&2, M.Entry<K, V>>, S.is_eq(_), Con{M.Entry{S.key(K, V, e), v}, ys}, Con{e, S.set_val(~K, ~V, ~cmp, k, v, ys)}) == Con{M.Entry{S.key(K, V, e), v}, ys} : List<&2, M.Entry<K, V>>}
      {==}
    case Con{+a, +t}:
      %Equal.sym(Cmp, cmp(k, S.key(K, V, a)), GT{}, OR.lt_gt(~K, ~cmp, ~o, S.key(K, V, a), k, L.and_left(Cmp.is_lt(cmp(S.key(K, V, a), k)), OR.ltall(~K, ~V, ~cmp, k, t), hl))) : {S.pick(List<&2, M.Entry<K, V>>, S.is_eq(_), Con{M.Entry{S.key(K, V, a), v}, SC.append(M.Entry<K, V>, t, Con{e, ys})}, Con{a, S.set_val(~K, ~V, ~cmp, k, v, SC.append(M.Entry<K, V>, t, Con{e, ys}))}) == Con{a, SC.append(M.Entry<K, V>, t, Con{M.Entry{S.key(K, V, e), v}, ys})} : List<&2, M.Entry<K, V>>}
      %Equal.sym(List<&2, M.Entry<K, V>>, S.set_val(~K, ~V, ~cmp, k, v, SC.append(M.Entry<K, V>, t, Con{e, ys})), SC.append(M.Entry<K, V>, t, Con{M.Entry{S.key(K, V, e), v}, ys}), set_val_mid(~K, ~V, ~cmp, ~o, k, v, t, e, ys, L.and_right(Cmp.is_lt(cmp(S.key(K, V, a), k)), OR.ltall(~K, ~V, ~cmp, k, t), hl), hc)) : {Con{a, _} == Con{a, SC.append(M.Entry<K, V>, t, Con{M.Entry{S.key(K, V, e), v}, ys})} : List<&2, M.Entry<K, V>>}
      {==}

# order reads only keys
def ord_key(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +xs: List<&2, M.Entry<K, V>>, +e: M.Entry<K, V>, +e2: M.Entry<K, V>, +ys: List<&2, M.Entry<K, V>>, +hk: {S.key(K, V, e) == S.key(K, V, e2) : K}, +h: {ST.ordered(~K, ~V, ~cmp, SC.append(M.Entry<K, V>, xs, Con{e, ys})) == True{} : Bool}) -> {ST.ordered(~K, ~V, ~cmp, SC.append(M.Entry<K, V>, xs, Con{e2, ys})) == True{} : Bool}:
  match xs:
    case Nil{}:
      match ys:
        case Nil{}:
          {==}
        case Con{+b, +u}:
          L.subst(K, z => {Bool.and(Cmp.is_lt(cmp(z, S.key(K, V, b))), ST.ordered(~K, ~V, ~cmp, Con{b, u})) == True{} : Bool}, S.key(K, V, e), S.key(K, V, e2), hk, h)
    case Con{+a, +t}:
      match t:
        case Nil{}:
          +h1 = L.and_left(Cmp.is_lt(cmp(S.key(K, V, a), S.key(K, V, e))), ST.ordered(~K, ~V, ~cmp, Con{e, ys}), h)
          +h2 = L.and_right(Cmp.is_lt(cmp(S.key(K, V, a), S.key(K, V, e))), ST.ordered(~K, ~V, ~cmp, Con{e, ys}), h)
          L.and_intro(Cmp.is_lt(cmp(S.key(K, V, a), S.key(K, V, e2))), ST.ordered(~K, ~V, ~cmp, Con{e2, ys}), L.subst(K, z => {Cmp.is_lt(cmp(S.key(K, V, a), z)) == True{} : Bool}, S.key(K, V, e), S.key(K, V, e2), hk, h1), ord_key(~K, ~V, ~cmp, Nil{}, e, e2, ys, hk, h2))
        case Con{+a2, +u}:
          +h1 = L.and_left(Cmp.is_lt(cmp(S.key(K, V, a), S.key(K, V, a2))), ST.ordered(~K, ~V, ~cmp, Con{a2, SC.append(M.Entry<K, V>, u, Con{e, ys})}), h)
          +h2 = L.and_right(Cmp.is_lt(cmp(S.key(K, V, a), S.key(K, V, a2))), ST.ordered(~K, ~V, ~cmp, Con{a2, SC.append(M.Entry<K, V>, u, Con{e, ys})}), h)
          L.and_intro(Cmp.is_lt(cmp(S.key(K, V, a), S.key(K, V, a2))), ST.ordered(~K, ~V, ~cmp, Con{a2, SC.append(M.Entry<K, V>, u, Con{e2, ys})}), h1, ord_key(~K, ~V, ~cmp, Con{a2, u}, e, e2, ys, hk, h2))

# ---- a payload exchanged ----

def some_ex_c(-V: Data, +pl: List<&2, Maybe<&2, V>>, +i: Nat, +w: Maybe<&2, V>, +jj: Nat, +hj: {ST.some2(V, ST.pv(V, pl, 1n+jj)) == True{} : Bool}, +hw: {ST.some2(V, w) == True{} : Bool}, +b: Bool, +hb: {Nat.is_lt(i, SC.length(Maybe<&2, V>, pl)) == b : Bool}, +e: Bool, +he: {Nat.is_eq(i, jj) == e : Bool}) -> {ST.some2(V, ST.nth_or(Maybe<&2, V>, ST.pk(List<&2, Maybe<&2, V>>, b, SC.update(Maybe<&2, V>, pl, i, w), pl), jj, None{})) == True{} : Bool}:
  match b e:
    case True{} True{}:
      +ei = N.eq_from_is_eq(i, jj, he)
      +hin = L.subst(Nat, z => {Nat.is_lt(z, SC.length(Maybe<&2, V>, pl)) == True{} : Bool}, i, jj, ei, hb)
      %Equal.sym(Nat, i, jj, ei) : {ST.some2(V, ST.nth_or(Maybe<&2, V>, SC.update(Maybe<&2, V>, pl, _, w), jj, None{})) == True{} : Bool}
      %Equal.sym(Maybe<&2, V>, ST.nth_or(Maybe<&2, V>, SC.update(Maybe<&2, V>, pl, jj, w), jj, None{}), w, Equal.trans(Maybe<&2, V>, ST.nth_or(Maybe<&2, V>, SC.update(Maybe<&2, V>, pl, jj, w), jj, None{}), PR.or_else(Maybe<&2, V>, SC.nth(Maybe<&2, V>, SC.update(Maybe<&2, V>, pl, jj, w), jj), None{}), w, PR.nth_or_nth(Maybe<&2, V>, SC.update(Maybe<&2, V>, pl, jj, w), jj, None{}), L.subst(Maybe<&2, Maybe<&2, V>>, z => {PR.or_else(Maybe<&2, V>, z, None{}) == w : Maybe<&2, V>}, Some{w}, SC.nth(Maybe<&2, V>, SC.update(Maybe<&2, V>, pl, jj, w), jj), Equal.sym(Maybe<&2, Maybe<&2, V>>, SC.nth(Maybe<&2, V>, SC.update(Maybe<&2, V>, pl, jj, w), jj), Some{w}, LL.nth_update_same(Maybe<&2, V>, pl, jj, w, hin)), {==}))) : {ST.some2(V, _) == True{} : Bool}
      hw
    case True{} False{}:
      %Equal.sym(Maybe<&2, V>, ST.nth_or(Maybe<&2, V>, SC.update(Maybe<&2, V>, pl, i, w), jj, None{}), ST.nth_or(Maybe<&2, V>, pl, jj, None{}), SL.nth_upd_c(Maybe<&2, V>, pl, i, w, jj, None{}, he, True{})) : {ST.some2(V, _) == True{} : Bool}
      hj
    case False{} +e:
      hj

def some_ex(-V: Data, +pl: List<&2, Maybe<&2, V>>, +id: Nat, +w: Maybe<&2, V>, +j: Nat, +hj: {ST.some2(V, ST.pv(V, pl, j)) == True{} : Bool}, +hw: {ST.some2(V, w) == True{} : Bool}) -> {ST.some2(V, ST.pv(V, PR.ex_pl(V, pl, id, w), j)) == True{} : Bool}:
  match id j:
    case 0n +j:
      hj
    case 1n+i 0n:
      Empty.absurd({ST.some2(V, None{}) == True{} : Bool}, L.false_true(hj))
    case 1n+i 1n+jj:
      some_ex_c(V, pl, i, w, jj, hj, hw, Nat.is_lt(i, SC.length(Maybe<&2, V>, pl)), {==}, Nat.is_eq(i, jj), {==})

def pay_ex(~V: Data, +t: ST.Tr, +pl: List<&2, Maybe<&2, V>>, +id: Nat, +w: Maybe<&2, V>, +hp: {ST.pay(~V, t, pl) == True{} : Bool}, +hw: {ST.some2(V, w) == True{} : Bool}) -> {ST.pay(~V, t, PR.ex_pl(V, pl, id, w)) == True{} : Bool}:
  match t:
    case ST.TE{}:
      {==}
    case ST.TN{+i, +a, +b}:
      L.and_intro(ST.some2(V, ST.pv(V, PR.ex_pl(V, pl, id, w), i)), Bool.and(ST.pay(~V, a, PR.ex_pl(V, pl, id, w)), ST.pay(~V, b, PR.ex_pl(V, pl, id, w))), some_ex(V, pl, id, w, i, FI.pay_node(~V, i, a, b, pl, hp), hw), L.and_intro(ST.pay(~V, a, PR.ex_pl(V, pl, id, w)), ST.pay(~V, b, PR.ex_pl(V, pl, id, w)), pay_ex(~V, a, pl, id, w, FI.pay_l(~V, i, a, b, pl, hp), hw), pay_ex(~V, b, pl, id, w, FI.pay_r(~V, i, a, b, pl, hp), hw)))

# ---- the key found: put replaces the value ----


# the entries around a node the path leads to, for a payload list
def ents_at(~K: Data, ~V: Data, +nl: List<&2, M.Node<K>>, +q: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +c: List<&2, P.Fr>, +i: Nat, +a: ST.Tr, +b: ST.Tr, +hbc: {ST.ids(tg) == SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{i, a, b}), P.after(c))) : List<&2, Nat>}) -> {ST.ents(~K, ~V, ST.ids(tg), nl, q) == SC.append(M.Entry<K, V>, ST.ents(~K, ~V, SC.append(Nat, P.before(c), ST.ids(a)), nl, q), ST.cons_m(M.Entry<K, V>, ST.ent(K, V, ST.nd(K, nl, i), ST.pv(V, q, i)), ST.ents(~K, ~V, SC.append(Nat, ST.ids(b), P.after(c)), nl, q))) : List<&2, M.Entry<K, V>>}:
  +e1 = L.subst(List<&2, Nat>, z => {ST.ents(~K, ~V, ST.ids(tg), nl, q) == ST.ents(~K, ~V, z, nl, q) : List<&2, M.Entry<K, V>>}, ST.ids(tg), SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{i, a, b}), P.after(c))), hbc, {==})
  +e2 = L.subst(List<&2, Nat>, z => {ST.ents(~K, ~V, SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{i, a, b}), P.after(c))), nl, q) == ST.ents(~K, ~V, z, nl, q) : List<&2, M.Entry<K, V>>}, SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{i, a, b}), P.after(c))), SC.append(Nat, SC.append(Nat, P.before(c), ST.ids(a)), Con{i, SC.append(Nat, ST.ids(b), P.after(c))}), NS.wh_node(c, i, a, b), {==})
  Equal.trans(List<&2, M.Entry<K, V>>, ST.ents(~K, ~V, ST.ids(tg), nl, q), ST.ents(~K, ~V, SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{i, a, b}), P.after(c))), nl, q), SC.append(M.Entry<K, V>, ST.ents(~K, ~V, SC.append(Nat, P.before(c), ST.ids(a)), nl, q), ST.cons_m(M.Entry<K, V>, ST.ent(K, V, ST.nd(K, nl, i), ST.pv(V, q, i)), ST.ents(~K, ~V, SC.append(Nat, ST.ids(b), P.after(c)), nl, q))), e1, Equal.trans(List<&2, M.Entry<K, V>>, ST.ents(~K, ~V, SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{i, a, b}), P.after(c))), nl, q), ST.ents(~K, ~V, SC.append(Nat, SC.append(Nat, P.before(c), ST.ids(a)), Con{i, SC.append(Nat, ST.ids(b), P.after(c))}), nl, q), SC.append(M.Entry<K, V>, ST.ents(~K, ~V, SC.append(Nat, P.before(c), ST.ids(a)), nl, q), ST.cons_m(M.Entry<K, V>, ST.ent(K, V, ST.nd(K, nl, i), ST.pv(V, q, i)), ST.ents(~K, ~V, SC.append(Nat, ST.ids(b), P.after(c)), nl, q))), e2, FI.ents_app(~K, ~V, SC.append(Nat, P.before(c), ST.ids(a)), Con{i, SC.append(Nat, ST.ids(b), P.after(c))}, nl, q)))


# the node of k found: exchanging its payload for v gives the entries
# set_val(k, v) and keeps the invariant
def hit_core(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +hg: {ST.goodF(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl) == True{} : Bool}, +c: List<&2, P.Fr>, +i: Nat, +a: ST.Tr, +b: ST.Tr, +k: K, +v: V, +hbc: {ST.ids(tg) == SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{i, a, b}), P.after(c))) : List<&2, Nat>}, +hr: {ST.rep(~K, ST.TN{i, a, b}, P.top(c), nl) == True{} : Bool}, +hfin: {SP.fin(~K, ~cmp, k, ST.TN{i, a, b}, nl) == True{} : Bool}, +x: M.Node<K>, +m: Maybe<&2, V>, +hxi: {ST.nd(K, nl, i) == x : M.Node<K>}, +hmi: {ST.pv(V, pl, i) == m : Maybe<&2, V>}, +hx: {ST.is_node(K, x, ST.rid(a), ST.rid(b), P.top(c)) == True{} : Bool}, +hm: {ST.some2(V, m) == True{} : Bool}) -> {ST.ents(~K, ~V, ST.ids(tg), nl, PR.ex_pl(V, pl, i, Some{v})) == S.set_val(~K, ~V, ~cmp, k, v, ST.ents(~K, ~V, ST.ids(tg), nl, pl)) : List<&2, M.Entry<K, V>>} & {ST.goodF(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, PR.ex_pl(V, pl, i, Some{v}), tg, fl) == True{} : Bool}:
  match i x m:
    case 0n +x +m:
      Empty.absurd({ST.ents(~K, ~V, ST.ids(tg), nl, PR.ex_pl(V, pl, 0n, Some{v})) == S.set_val(~K, ~V, ~cmp, k, v, ST.ents(~K, ~V, ST.ids(tg), nl, pl)) : List<&2, M.Entry<K, V>>} & {ST.goodF(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, PR.ex_pl(V, pl, 0n, Some{v}), tg, fl) == True{} : Bool}, L.false_true(L.and_left(Nat.is_lt(0n, 0n), Bool.and(ST.is_node(K, ST.nd(K, nl, 0n), ST.rid(a), ST.rid(b), P.top(c)), Bool.and(ST.rep(~K, a, 0n, nl), ST.rep(~K, b, 0n, nl))), hr)))
    case 1n+j M.Free{f} +m:
      Empty.absurd({ST.ents(~K, ~V, ST.ids(tg), nl, PR.ex_pl(V, pl, 1n+j, Some{v})) == S.set_val(~K, ~V, ~cmp, k, v, ST.ents(~K, ~V, ST.ids(tg), nl, pl)) : List<&2, M.Entry<K, V>>} & {ST.goodF(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, PR.ex_pl(V, pl, 1n+j, Some{v}), tg, fl) == True{} : Bool}, L.false_true(hx))
    case 1n+j M.N{c0, x1, x2, x3, key} None{}:
      Empty.absurd({ST.ents(~K, ~V, ST.ids(tg), nl, PR.ex_pl(V, pl, 1n+j, Some{v})) == S.set_val(~K, ~V, ~cmp, k, v, ST.ents(~K, ~V, ST.ids(tg), nl, pl)) : List<&2, M.Entry<K, V>>} & {ST.goodF(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, PR.ex_pl(V, pl, 1n+j, Some{v}), tg, fl) == True{} : Bool}, L.false_true(hm))
    case 1n+j M.N{+c0, +x1, +x2, +x3, +key} Some{+vi}:
      +hW0 = ents_at(~K, ~V, nl, pl, tg, c, 1n+j, a, b, hbc)
      +eent = L.subst(Maybe<&2, V>, z => {ST.ent(K, V, ST.nd(K, nl, 1n+j), ST.pv(V, pl, 1n+j)) == ST.ent(K, V, M.N{c0, x1, x2, x3, key}, z) : Maybe<&2, M.Entry<K, V>>}, ST.pv(V, pl, 1n+j), Some{vi}, hmi, L.subst(M.Node<K>, z => {ST.ent(K, V, ST.nd(K, nl, 1n+j), ST.pv(V, pl, 1n+j)) == ST.ent(K, V, z, ST.pv(V, pl, 1n+j)) : Maybe<&2, M.Entry<K, V>>}, ST.nd(K, nl, 1n+j), M.N{c0, x1, x2, x3, key}, hxi, {==}))
      +hW = Equal.trans(List<&2, M.Entry<K, V>>, ST.ents(~K, ~V, ST.ids(tg), nl, pl), SC.append(M.Entry<K, V>, ST.ents(~K, ~V, SC.append(Nat, P.before(c), ST.ids(a)), nl, pl), ST.cons_m(M.Entry<K, V>, ST.ent(K, V, ST.nd(K, nl, 1n+j), ST.pv(V, pl, 1n+j)), ST.ents(~K, ~V, SC.append(Nat, ST.ids(b), P.after(c)), nl, pl))), SC.append(M.Entry<K, V>, ST.ents(~K, ~V, SC.append(Nat, P.before(c), ST.ids(a)), nl, pl), Con{M.Entry{key, vi}, ST.ents(~K, ~V, SC.append(Nat, ST.ids(b), P.after(c)), nl, pl)}), hW0, L.subst(Maybe<&2, M.Entry<K, V>>, z => {SC.append(M.Entry<K, V>, ST.ents(~K, ~V, SC.append(Nat, P.before(c), ST.ids(a)), nl, pl), ST.cons_m(M.Entry<K, V>, ST.ent(K, V, ST.nd(K, nl, 1n+j), ST.pv(V, pl, 1n+j)), ST.ents(~K, ~V, SC.append(Nat, ST.ids(b), P.after(c)), nl, pl))) == SC.append(M.Entry<K, V>, ST.ents(~K, ~V, SC.append(Nat, P.before(c), ST.ids(a)), nl, pl), ST.cons_m(M.Entry<K, V>, z, ST.ents(~K, ~V, SC.append(Nat, ST.ids(b), P.after(c)), nl, pl))) : List<&2, M.Entry<K, V>>}, ST.ent(K, V, ST.nd(K, nl, 1n+j), ST.pv(V, pl, 1n+j)), Some{M.Entry{key, vi}}, eent, {==}))
      +hord = L.subst(List<&2, M.Entry<K, V>>, z => {ST.ordered(~K, ~V, ~cmp, z) == True{} : Bool}, ST.ents(~K, ~V, ST.ids(tg), nl, pl), SC.append(M.Entry<K, V>, ST.ents(~K, ~V, SC.append(Nat, P.before(c), ST.ids(a)), nl, pl), Con{M.Entry{key, vi}, ST.ents(~K, ~V, SC.append(Nat, ST.ids(b), P.after(c)), nl, pl)}), hW, ST.g_cord(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg))
      +hc = AG.iseq_eq(cmp(k, key), L.subst(M.Node<K>, z => {S.is_eq(TR.kc(~K, ~cmp, k, z)) == True{} : Bool}, ST.nd(K, nl, 1n+j), M.N{c0, x1, x2, x3, key}, hxi, hfin))
      +ek = O.antisym(~K, ~cmp, o, k, key, hc)
      +hlx = L.subst(K, z => {OR.ltall(~K, ~V, ~cmp, z, ST.ents(~K, ~V, SC.append(Nat, P.before(c), ST.ids(a)), nl, pl)) == True{} : Bool}, key, k, Equal.sym(K, k, key, ek), OR.ord_mid_l(~K, ~V, ~cmp, ~o, ST.ents(~K, ~V, SC.append(Nat, P.before(c), ST.ids(a)), nl, pl), M.Entry{key, vi}, ST.ents(~K, ~V, SC.append(Nat, ST.ids(b), P.after(c)), nl, pl), hord))
      +hnd0 = L.subst(List<&2, Nat>, z => {LST.nodupn(z) == True{} : Bool}, ST.ids(tg), SC.append(Nat, SC.append(Nat, P.before(c), ST.ids(a)), Con{1n+j, SC.append(Nat, ST.ids(b), P.after(c))}), Equal.trans(List<&2, Nat>, ST.ids(tg), SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{1n+j, a, b}), P.after(c))), SC.append(Nat, SC.append(Nat, P.before(c), ST.ids(a)), Con{1n+j, SC.append(Nat, ST.ids(b), P.after(c))}), hbc, NS.wh_node(c, 1n+j, a, b)), DJ.ndl(ST.ids(tg), fl, ST.g_cnd(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg)))
      +nX = DJ.dj_l(SC.append(Nat, P.before(c), ST.ids(a)), Con{1n+j, SC.append(Nat, ST.ids(b), P.after(c))}, hnd0, 1n+j, DJ.mem_hd(1n+j, SC.append(Nat, ST.ids(b), P.after(c))))
      +nY = DJ.nd_head(1n+j, SC.append(Nat, ST.ids(b), P.after(c)), DJ.ndr(SC.append(Nat, P.before(c), ST.ids(a)), Con{1n+j, SC.append(Nat, ST.ids(b), P.after(c))}, hnd0))
      +mi = L.subst(List<&2, Nat>, z => {HT.memn(1n+j, z) == True{} : Bool}, SC.append(Nat, SC.append(Nat, P.before(c), ST.ids(a)), Con{1n+j, SC.append(Nat, ST.ids(b), P.after(c))}), ST.ids(tg), Equal.sym(List<&2, Nat>, ST.ids(tg), SC.append(Nat, SC.append(Nat, P.before(c), ST.ids(a)), Con{1n+j, SC.append(Nat, ST.ids(b), P.after(c))}), Equal.trans(List<&2, Nat>, ST.ids(tg), SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{1n+j, a, b}), P.after(c))), SC.append(Nat, SC.append(Nat, P.before(c), ST.ids(a)), Con{1n+j, SC.append(Nat, ST.ids(b), P.after(c))}), hbc, NS.wh_node(c, 1n+j, a, b))), DJ.mem_r(1n+j, SC.append(Nat, P.before(c), ST.ids(a)), Con{1n+j, SC.append(Nat, ST.ids(b), P.after(c))}, DJ.mem_hd(1n+j, SC.append(Nat, ST.ids(b), P.after(c)))))
      +hib = AL.allin_mem(ST.ids(tg), SC.length(M.Node<K>, nl), 1n+j, AL.allin_l(ST.ids(tg), fl, SC.length(M.Node<K>, nl), ST.g_cin(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg)), mi)
      +hjl = L.subst(Nat, z => {Nat.is_lt(j, z) == True{} : Bool}, SC.length(M.Node<K>, nl), SC.length(Maybe<&2, V>, pl), Equal.sym(Nat, SC.length(Maybe<&2, V>, pl), SC.length(M.Node<K>, nl), N.eq_from_is_eq(SC.length(Maybe<&2, V>, pl), SC.length(M.Node<K>, nl), ST.g_cpl(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg))), N.succ_le_lt(j, SC.length(M.Node<K>, nl), L.and_right(Nat.is_lt(0n, 1n+j), Nat.is_le(1n+j, SC.length(M.Node<K>, nl)), hib)))
      +hW2a = ents_at(~K, ~V, nl, PR.ex_pl(V, pl, 1n+j, Some{v}), tg, c, 1n+j, a, b, hbc)
      +eX2 = SL.ents_pex(~K, ~V, SC.append(Nat, P.before(c), ST.ids(a)), nl, pl, 1n+j, Some{v}, nX)
      +eY2 = SL.ents_pex(~K, ~V, SC.append(Nat, ST.ids(b), P.after(c)), nl, pl, 1n+j, Some{v}, nY)
      +epv = SL.pv_ex_same(V, pl, j, Some{v}, hjl)
      +eent2 = L.subst(Maybe<&2, V>, z => {ST.ent(K, V, ST.nd(K, nl, 1n+j), ST.pv(V, PR.ex_pl(V, pl, 1n+j, Some{v}), 1n+j)) == ST.ent(K, V, M.N{c0, x1, x2, x3, key}, z) : Maybe<&2, M.Entry<K, V>>}, ST.pv(V, PR.ex_pl(V, pl, 1n+j, Some{v}), 1n+j), Some{v}, epv, L.subst(M.Node<K>, z => {ST.ent(K, V, ST.nd(K, nl, 1n+j), ST.pv(V, PR.ex_pl(V, pl, 1n+j, Some{v}), 1n+j)) == ST.ent(K, V, z, ST.pv(V, PR.ex_pl(V, pl, 1n+j, Some{v}), 1n+j)) : Maybe<&2, M.Entry<K, V>>}, ST.nd(K, nl, 1n+j), M.N{c0, x1, x2, x3, key}, hxi, {==}))
      +hW2b = L.subst(Maybe<&2, M.Entry<K, V>>, z => {SC.append(M.Entry<K, V>, ST.ents(~K, ~V, SC.append(Nat, P.before(c), ST.ids(a)), nl, PR.ex_pl(V, pl, 1n+j, Some{v})), ST.cons_m(M.Entry<K, V>, ST.ent(K, V, ST.nd(K, nl, 1n+j), ST.pv(V, PR.ex_pl(V, pl, 1n+j, Some{v}), 1n+j)), ST.ents(~K, ~V, SC.append(Nat, ST.ids(b), P.after(c)), nl, PR.ex_pl(V, pl, 1n+j, Some{v})))) == SC.append(M.Entry<K, V>, ST.ents(~K, ~V, SC.append(Nat, P.before(c), ST.ids(a)), nl, PR.ex_pl(V, pl, 1n+j, Some{v})), ST.cons_m(M.Entry<K, V>, z, ST.ents(~K, ~V, SC.append(Nat, ST.ids(b), P.after(c)), nl, PR.ex_pl(V, pl, 1n+j, Some{v})))) : List<&2, M.Entry<K, V>>}, ST.ent(K, V, ST.nd(K, nl, 1n+j), ST.pv(V, PR.ex_pl(V, pl, 1n+j, Some{v}), 1n+j)), Some{M.Entry{key, v}}, eent2, {==})
      +hW2c = L.subst(List<&2, M.Entry<K, V>>, z => {SC.append(M.Entry<K, V>, ST.ents(~K, ~V, SC.append(Nat, P.before(c), ST.ids(a)), nl, PR.ex_pl(V, pl, 1n+j, Some{v})), Con{M.Entry{key, v}, ST.ents(~K, ~V, SC.append(Nat, ST.ids(b), P.after(c)), nl, PR.ex_pl(V, pl, 1n+j, Some{v}))}) == SC.append(M.Entry<K, V>, z, Con{M.Entry{key, v}, ST.ents(~K, ~V, SC.append(Nat, ST.ids(b), P.after(c)), nl, PR.ex_pl(V, pl, 1n+j, Some{v}))}) : List<&2, M.Entry<K, V>>}, ST.ents(~K, ~V, SC.append(Nat, P.before(c), ST.ids(a)), nl, PR.ex_pl(V, pl, 1n+j, Some{v})), ST.ents(~K, ~V, SC.append(Nat, P.before(c), ST.ids(a)), nl, pl), eX2, {==})
      +hW2d = L.subst(List<&2, M.Entry<K, V>>, z => {SC.append(M.Entry<K, V>, ST.ents(~K, ~V, SC.append(Nat, P.before(c), ST.ids(a)), nl, pl), Con{M.Entry{key, v}, ST.ents(~K, ~V, SC.append(Nat, ST.ids(b), P.after(c)), nl, PR.ex_pl(V, pl, 1n+j, Some{v}))}) == SC.append(M.Entry<K, V>, ST.ents(~K, ~V, SC.append(Nat, P.before(c), ST.ids(a)), nl, pl), Con{M.Entry{key, v}, z}) : List<&2, M.Entry<K, V>>}, ST.ents(~K, ~V, SC.append(Nat, ST.ids(b), P.after(c)), nl, PR.ex_pl(V, pl, 1n+j, Some{v})), ST.ents(~K, ~V, SC.append(Nat, ST.ids(b), P.after(c)), nl, pl), eY2, {==})
      +hW2 = Equal.trans(List<&2, M.Entry<K, V>>, ST.ents(~K, ~V, ST.ids(tg), nl, PR.ex_pl(V, pl, 1n+j, Some{v})), SC.append(M.Entry<K, V>, ST.ents(~K, ~V, SC.append(Nat, P.before(c), ST.ids(a)), nl, PR.ex_pl(V, pl, 1n+j, Some{v})), ST.cons_m(M.Entry<K, V>, ST.ent(K, V, ST.nd(K, nl, 1n+j), ST.pv(V, PR.ex_pl(V, pl, 1n+j, Some{v}), 1n+j)), ST.ents(~K, ~V, SC.append(Nat, ST.ids(b), P.after(c)), nl, PR.ex_pl(V, pl, 1n+j, Some{v})))), SC.append(M.Entry<K, V>, ST.ents(~K, ~V, SC.append(Nat, P.before(c), ST.ids(a)), nl, pl), Con{M.Entry{key, v}, ST.ents(~K, ~V, SC.append(Nat, ST.ids(b), P.after(c)), nl, pl)}), hW2a, Equal.trans(List<&2, M.Entry<K, V>>, SC.append(M.Entry<K, V>, ST.ents(~K, ~V, SC.append(Nat, P.before(c), ST.ids(a)), nl, PR.ex_pl(V, pl, 1n+j, Some{v})), ST.cons_m(M.Entry<K, V>, ST.ent(K, V, ST.nd(K, nl, 1n+j), ST.pv(V, PR.ex_pl(V, pl, 1n+j, Some{v}), 1n+j)), ST.ents(~K, ~V, SC.append(Nat, ST.ids(b), P.after(c)), nl, PR.ex_pl(V, pl, 1n+j, Some{v})))), SC.append(M.Entry<K, V>, ST.ents(~K, ~V, SC.append(Nat, P.before(c), ST.ids(a)), nl, PR.ex_pl(V, pl, 1n+j, Some{v})), Con{M.Entry{key, v}, ST.ents(~K, ~V, SC.append(Nat, ST.ids(b), P.after(c)), nl, PR.ex_pl(V, pl, 1n+j, Some{v}))}), SC.append(M.Entry<K, V>, ST.ents(~K, ~V, SC.append(Nat, P.before(c), ST.ids(a)), nl, pl), Con{M.Entry{key, v}, ST.ents(~K, ~V, SC.append(Nat, ST.ids(b), P.after(c)), nl, pl)}), hW2b, Equal.trans(List<&2, M.Entry<K, V>>, SC.append(M.Entry<K, V>, ST.ents(~K, ~V, SC.append(Nat, P.before(c), ST.ids(a)), nl, PR.ex_pl(V, pl, 1n+j, Some{v})), Con{M.Entry{key, v}, ST.ents(~K, ~V, SC.append(Nat, ST.ids(b), P.after(c)), nl, PR.ex_pl(V, pl, 1n+j, Some{v}))}), SC.append(M.Entry<K, V>, ST.ents(~K, ~V, SC.append(Nat, P.before(c), ST.ids(a)), nl, pl), Con{M.Entry{key, v}, ST.ents(~K, ~V, SC.append(Nat, ST.ids(b), P.after(c)), nl, PR.ex_pl(V, pl, 1n+j, Some{v}))}), SC.append(M.Entry<K, V>, ST.ents(~K, ~V, SC.append(Nat, P.before(c), ST.ids(a)), nl, pl), Con{M.Entry{key, v}, ST.ents(~K, ~V, SC.append(Nat, ST.ids(b), P.after(c)), nl, pl)}), hW2c, hW2d)))
      +hsv = Equal.trans(List<&2, M.Entry<K, V>>, S.set_val(~K, ~V, ~cmp, k, v, ST.ents(~K, ~V, ST.ids(tg), nl, pl)), S.set_val(~K, ~V, ~cmp, k, v, SC.append(M.Entry<K, V>, ST.ents(~K, ~V, SC.append(Nat, P.before(c), ST.ids(a)), nl, pl), Con{M.Entry{key, vi}, ST.ents(~K, ~V, SC.append(Nat, ST.ids(b), P.after(c)), nl, pl)})), SC.append(M.Entry<K, V>, ST.ents(~K, ~V, SC.append(Nat, P.before(c), ST.ids(a)), nl, pl), Con{M.Entry{key, v}, ST.ents(~K, ~V, SC.append(Nat, ST.ids(b), P.after(c)), nl, pl)}), L.subst(List<&2, M.Entry<K, V>>, z => {S.set_val(~K, ~V, ~cmp, k, v, ST.ents(~K, ~V, ST.ids(tg), nl, pl)) == S.set_val(~K, ~V, ~cmp, k, v, z) : List<&2, M.Entry<K, V>>}, ST.ents(~K, ~V, ST.ids(tg), nl, pl), SC.append(M.Entry<K, V>, ST.ents(~K, ~V, SC.append(Nat, P.before(c), ST.ids(a)), nl, pl), Con{M.Entry{key, vi}, ST.ents(~K, ~V, SC.append(Nat, ST.ids(b), P.after(c)), nl, pl)}), hW, {==}), set_val_mid(~K, ~V, ~cmp, ~o, k, v, ST.ents(~K, ~V, SC.append(Nat, P.before(c), ST.ids(a)), nl, pl), M.Entry{key, vi}, ST.ents(~K, ~V, SC.append(Nat, ST.ids(b), P.after(c)), nl, pl), hlx, hc))
      +gcpl = L.subst(Nat, z => {Nat.is_eq(z, SC.length(M.Node<K>, nl)) == True{} : Bool}, SC.length(Maybe<&2, V>, pl), SC.length(Maybe<&2, V>, PR.ex_pl(V, pl, 1n+j, Some{v})), Equal.sym(Nat, SC.length(Maybe<&2, V>, PR.ex_pl(V, pl, 1n+j, Some{v})), SC.length(Maybe<&2, V>, pl), SL.len_ex(V, pl, 1n+j, Some{v})), ST.g_cpl(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg))
      +gcord = L.subst(List<&2, M.Entry<K, V>>, z => {ST.ordered(~K, ~V, ~cmp, z) == True{} : Bool}, SC.append(M.Entry<K, V>, ST.ents(~K, ~V, SC.append(Nat, P.before(c), ST.ids(a)), nl, pl), Con{M.Entry{key, v}, ST.ents(~K, ~V, SC.append(Nat, ST.ids(b), P.after(c)), nl, pl)}), ST.ents(~K, ~V, ST.ids(tg), nl, PR.ex_pl(V, pl, 1n+j, Some{v})), Equal.sym(List<&2, M.Entry<K, V>>, ST.ents(~K, ~V, ST.ids(tg), nl, PR.ex_pl(V, pl, 1n+j, Some{v})), SC.append(M.Entry<K, V>, ST.ents(~K, ~V, SC.append(Nat, P.before(c), ST.ids(a)), nl, pl), Con{M.Entry{key, v}, ST.ents(~K, ~V, SC.append(Nat, ST.ids(b), P.after(c)), nl, pl)}), hW2), ord_key(~K, ~V, ~cmp, ST.ents(~K, ~V, SC.append(Nat, P.before(c), ST.ids(a)), nl, pl), M.Entry{key, vi}, M.Entry{key, v}, ST.ents(~K, ~V, SC.append(Nat, ST.ids(b), P.after(c)), nl, pl), {==}, hord))
      +good = ST.good_intro(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, PR.ex_pl(V, pl, 1n+j, Some{v}), tg, fl, ST.g_cl(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg), ST.g_cd(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg), ST.g_ccap(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg), gcpl, ST.g_crep(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg), pay_ex(~V, tg, pl, 1n+j, Some{v}, ST.g_cpay(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg), {==}), ST.g_cfll(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg), ST.g_cnd(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg), ST.g_cin(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg), ST.g_clen(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg), gcord, ST.g_cblk(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg), ST.g_csz(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg), ST.g_croot(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg), ST.g_clo(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg), ST.g_chi(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg), ST.g_cfree(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg))
      (Equal.trans(List<&2, M.Entry<K, V>>, ST.ents(~K, ~V, ST.ids(tg), nl, PR.ex_pl(V, pl, 1n+j, Some{v})), SC.append(M.Entry<K, V>, ST.ents(~K, ~V, SC.append(Nat, P.before(c), ST.ids(a)), nl, pl), Con{M.Entry{key, v}, ST.ents(~K, ~V, SC.append(Nat, ST.ids(b), P.after(c)), nl, pl)}), S.set_val(~K, ~V, ~cmp, k, v, ST.ents(~K, ~V, ST.ids(tg), nl, pl)), hW2, Equal.sym(List<&2, M.Entry<K, V>>, S.set_val(~K, ~V, ~cmp, k, v, ST.ents(~K, ~V, ST.ids(tg), nl, pl)), SC.append(M.Entry<K, V>, ST.ents(~K, ~V, SC.append(Nat, P.before(c), ST.ids(a)), nl, pl), Con{M.Entry{key, v}, ST.ents(~K, ~V, SC.append(Nat, ST.ids(b), P.after(c)), nl, pl)}), hsv)), good)
