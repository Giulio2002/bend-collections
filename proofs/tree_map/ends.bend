import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../spec/common.bend as SC
import ../spec/tree_map.bend as S
import ../../src/containers/balanced_search_tree.bend as M
import ./state.bend as ST
import ./mirror.bend as MI
import ./tree.bend as TR
import ./find.bend as FI

# The first and last entries: the header's first and last ids are the ends
# of the ghost order, and every id of the tree has an entry, so the entry
# (or key) at them is the head (or last) of the specification's entries.
# (source: tools/generators/tm_hand/ends.src)


# every id has an entry
def oks(~K: Data, ~V: Data, xs: List<&2, Nat>, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, t}:
      Bool.and(S.is_some(M.Entry<K, V>, ST.ent(K, V, ST.nd(K, nl, x), ST.pv(V, pl, x))), oks(~K, ~V, t, nl, pl))


def oks_app(~K: Data, ~V: Data, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +xs: List<&2, Nat>, +ys: List<&2, Nat>, +hx: {oks(~K, ~V, xs, nl, pl) == True{} : Bool}, +hy: {oks(~K, ~V, ys, nl, pl) == True{} : Bool}) -> {oks(~K, ~V, SC.append(Nat, xs, ys), nl, pl) == True{} : Bool}:
  match xs:
    case Nil{}:
      hy
    case Con{+x, +t}:
      L.and_intro(S.is_some(M.Entry<K, V>, ST.ent(K, V, ST.nd(K, nl, x), ST.pv(V, pl, x))), oks(~K, ~V, SC.append(Nat, t, ys), nl, pl), L.and_left(S.is_some(M.Entry<K, V>, ST.ent(K, V, ST.nd(K, nl, x), ST.pv(V, pl, x))), oks(~K, ~V, t, nl, pl), hx), oks_app(~K, ~V, nl, pl, t, ys, L.and_right(S.is_some(M.Entry<K, V>, ST.ent(K, V, ST.nd(K, nl, x), ST.pv(V, pl, x))), oks(~K, ~V, t, nl, pl), hx), hy))

def ent_some(-K: Data, -V: Data, +x: M.Node<K>, +m: Maybe<&2, V>, +a: Nat, +b: Nat, +q: Nat, +hx: {ST.is_node(K, x, a, b, q) == True{} : Bool}, +hm: {ST.some2(V, m) == True{} : Bool}) -> {S.is_some(M.Entry<K, V>, ST.ent(K, V, x, m)) == True{} : Bool}:
  match x m:
    case M.Free{f} _:
      Empty.absurd({S.is_some(M.Entry<K, V>, ST.ent(K, V, M.Free{f}, m)) == True{} : Bool}, L.false_true(hx))
    case M.N{c, x1, x2, x3, key} None{}:
      Empty.absurd({S.is_some(M.Entry<K, V>, ST.ent(K, V, M.N{c, x1, x2, x3, key}, None{})) == True{} : Bool}, L.false_true(hm))
    case M.N{c, x1, x2, x3, key} Some{v}:
      {==}

def oks_tree(~K: Data, ~V: Data, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +t: ST.Tr, +p: Nat, +hr: {ST.rep(~K, t, p, nl) == True{} : Bool}, +hp: {ST.pay(~V, t, pl) == True{} : Bool}) -> {oks(~K, ~V, ST.ids(t), nl, pl) == True{} : Bool}:
  match t:
    case ST.TE{}:
      {==}
    case ST.TN{+i, +tl, +tr}:
      oks_app(~K, ~V, nl, pl, ST.ids(tl), Con{i, ST.ids(tr)}, oks_tree(~K, ~V, nl, pl, tl, i, TR.rep_l(~K, i, tl, tr, p, nl, hr), FI.pay_l(~V, i, tl, tr, pl, hp)), L.and_intro(S.is_some(M.Entry<K, V>, ST.ent(K, V, ST.nd(K, nl, i), ST.pv(V, pl, i))), oks(~K, ~V, ST.ids(tr), nl, pl), ent_some(K, V, ST.nd(K, nl, i), ST.pv(V, pl, i), ST.rid(tl), ST.rid(tr), p, TR.rep_node(~K, i, tl, tr, p, nl, hr), FI.pay_node(~V, i, tl, tr, pl, hp)), oks_tree(~K, ~V, nl, pl, tr, i, TR.rep_r(~K, i, tl, tr, p, nl, hr), FI.pay_r(~V, i, tl, tr, pl, hp))))

# ---- ends of the entries ----

def hd_cm(-K: Data, -V: Data, +m: Maybe<&2, M.Entry<K, V>>, +r: List<&2, M.Entry<K, V>>, +hm: {S.is_some(M.Entry<K, V>, m) == True{} : Bool}) -> {S.head(M.Entry<K, V>, ST.cons_m(M.Entry<K, V>, m, r)) == m : Maybe<&2, M.Entry<K, V>>}:
  match m:
    case None{}:
      Empty.absurd({S.head(M.Entry<K, V>, ST.cons_m(M.Entry<K, V>, None{}, r)) == None{} : Maybe<&2, M.Entry<K, V>>}, L.false_true(hm))
    case Some{e}:
      {==}

def head_ents(~K: Data, ~V: Data, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +xs: List<&2, Nat>, +h: {oks(~K, ~V, xs, nl, pl) == True{} : Bool}) -> {S.head(M.Entry<K, V>, ST.ents(~K, ~V, xs, nl, pl)) == ST.ent(K, V, ST.nd(K, nl, ST.fst0(xs)), ST.pv(V, pl, ST.fst0(xs))) : Maybe<&2, M.Entry<K, V>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      hd_cm(K, V, ST.ent(K, V, ST.nd(K, nl, x), ST.pv(V, pl, x)), ST.ents(~K, ~V, t, nl, pl), L.and_left(S.is_some(M.Entry<K, V>, ST.ent(K, V, ST.nd(K, nl, x), ST.pv(V, pl, x))), oks(~K, ~V, t, nl, pl), h))

def last_cm1(-K: Data, -V: Data, +m: Maybe<&2, M.Entry<K, V>>, +hm: {S.is_some(M.Entry<K, V>, m) == True{} : Bool}) -> {S.last(M.Entry<K, V>, ST.cons_m(M.Entry<K, V>, m, Nil{})) == m : Maybe<&2, M.Entry<K, V>>}:
  match m:
    case None{}:
      Empty.absurd({S.last(M.Entry<K, V>, ST.cons_m(M.Entry<K, V>, None{}, Nil{})) == None{} : Maybe<&2, M.Entry<K, V>>}, L.false_true(hm))
    case Some{e}:
      {==}

def last_cm2(-K: Data, -V: Data, +m1: Maybe<&2, M.Entry<K, V>>, +m2: Maybe<&2, M.Entry<K, V>>, +r: List<&2, M.Entry<K, V>>, +h1: {S.is_some(M.Entry<K, V>, m1) == True{} : Bool}, +h2: {S.is_some(M.Entry<K, V>, m2) == True{} : Bool}) -> {S.last(M.Entry<K, V>, ST.cons_m(M.Entry<K, V>, m1, ST.cons_m(M.Entry<K, V>, m2, r))) == S.last(M.Entry<K, V>, ST.cons_m(M.Entry<K, V>, m2, r)) : Maybe<&2, M.Entry<K, V>>}:
  match m1 m2:
    case None{} _:
      Empty.absurd({S.last(M.Entry<K, V>, ST.cons_m(M.Entry<K, V>, None{}, ST.cons_m(M.Entry<K, V>, m2, r))) == S.last(M.Entry<K, V>, ST.cons_m(M.Entry<K, V>, m2, r)) : Maybe<&2, M.Entry<K, V>>}, L.false_true(h1))
    case Some{e} None{}:
      Empty.absurd({S.last(M.Entry<K, V>, ST.cons_m(M.Entry<K, V>, Some{e}, ST.cons_m(M.Entry<K, V>, None{}, r))) == S.last(M.Entry<K, V>, ST.cons_m(M.Entry<K, V>, None{}, r)) : Maybe<&2, M.Entry<K, V>>}, L.false_true(h2))
    case Some{e} Some{e2}:
      {==}

def last_ents(~K: Data, ~V: Data, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +t: List<&2, Nat>, +x: Nat, +h: {oks(~K, ~V, Con{x, t}, nl, pl) == True{} : Bool}) -> {S.last(M.Entry<K, V>, ST.ents(~K, ~V, Con{x, t}, nl, pl)) == ST.ent(K, V, ST.nd(K, nl, ST.last0(Con{x, t})), ST.pv(V, pl, ST.last0(Con{x, t}))) : Maybe<&2, M.Entry<K, V>>}:
  match t:
    case Nil{}:
      last_cm1(K, V, ST.ent(K, V, ST.nd(K, nl, x), ST.pv(V, pl, x)), L.and_left(S.is_some(M.Entry<K, V>, ST.ent(K, V, ST.nd(K, nl, x), ST.pv(V, pl, x))), True{}, h))
    case Con{+y, +u}:
      +h2 = L.and_right(S.is_some(M.Entry<K, V>, ST.ent(K, V, ST.nd(K, nl, x), ST.pv(V, pl, x))), oks(~K, ~V, Con{y, u}, nl, pl), h)
      %Equal.sym(Maybe<&2, M.Entry<K, V>>, S.last(M.Entry<K, V>, ST.cons_m(M.Entry<K, V>, ST.ent(K, V, ST.nd(K, nl, x), ST.pv(V, pl, x)), ST.cons_m(M.Entry<K, V>, ST.ent(K, V, ST.nd(K, nl, y), ST.pv(V, pl, y)), ST.ents(~K, ~V, u, nl, pl)))), S.last(M.Entry<K, V>, ST.cons_m(M.Entry<K, V>, ST.ent(K, V, ST.nd(K, nl, y), ST.pv(V, pl, y)), ST.ents(~K, ~V, u, nl, pl))), last_cm2(K, V, ST.ent(K, V, ST.nd(K, nl, x), ST.pv(V, pl, x)), ST.ent(K, V, ST.nd(K, nl, y), ST.pv(V, pl, y)), ST.ents(~K, ~V, u, nl, pl), L.and_left(S.is_some(M.Entry<K, V>, ST.ent(K, V, ST.nd(K, nl, x), ST.pv(V, pl, x))), oks(~K, ~V, Con{y, u}, nl, pl), h), L.and_left(S.is_some(M.Entry<K, V>, ST.ent(K, V, ST.nd(K, nl, y), ST.pv(V, pl, y))), oks(~K, ~V, u, nl, pl), h2))) : {_ == ST.ent(K, V, ST.nd(K, nl, ST.last0(Con{y, u})), ST.pv(V, pl, ST.last0(Con{y, u}))) : Maybe<&2, M.Entry<K, V>>}
      last_ents(~K, ~V, nl, pl, u, y, h2)

def last0_some(~K: Data, ~V: Data, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +t: List<&2, Nat>, +x: Nat, +h: {oks(~K, ~V, Con{x, t}, nl, pl) == True{} : Bool}) -> {S.is_some(M.Entry<K, V>, ST.ent(K, V, ST.nd(K, nl, ST.last0(Con{x, t})), ST.pv(V, pl, ST.last0(Con{x, t})))) == True{} : Bool}:
  match t:
    case Nil{}:
      L.and_left(S.is_some(M.Entry<K, V>, ST.ent(K, V, ST.nd(K, nl, x), ST.pv(V, pl, x))), True{}, h)
    case Con{+y, +u}:
      last0_some(~K, ~V, nl, pl, u, y, L.and_right(S.is_some(M.Entry<K, V>, ST.ent(K, V, ST.nd(K, nl, x), ST.pv(V, pl, x))), oks(~K, ~V, Con{y, u}, nl, pl), h))

def km_some(-K: Data, -V: Data, +x: M.Node<K>, +m: Maybe<&2, V>, +h: {S.is_some(M.Entry<K, V>, ST.ent(K, V, x, m)) == True{} : Bool}) -> {S.key_m(K, V, ST.ent(K, V, x, m)) == M.node_key(~K, x) : Maybe<&2, K>}:
  match x m:
    case M.Free{f} _:
      Empty.absurd({S.key_m(K, V, ST.ent(K, V, M.Free{f}, m)) == M.node_key(~K, M.Free{f}) : Maybe<&2, K>}, L.false_true(h))
    case M.N{c, x1, x2, x3, key} None{}:
      Empty.absurd({S.key_m(K, V, ST.ent(K, V, M.N{c, x1, x2, x3, key}, None{})) == M.node_key(~K, M.N{c, x1, x2, x3, key}) : Maybe<&2, K>}, L.false_true(h))
    case M.N{c, x1, x2, x3, key} Some{v}:
      {==}

def first_key_eq(~K: Data, ~V: Data, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +xs: List<&2, Nat>, +h: {oks(~K, ~V, xs, nl, pl) == True{} : Bool}) -> {S.key_m(K, V, S.head(M.Entry<K, V>, ST.ents(~K, ~V, xs, nl, pl))) == M.node_key(~K, ST.nd(K, nl, ST.fst0(xs))) : Maybe<&2, K>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %Equal.sym(Maybe<&2, M.Entry<K, V>>, S.head(M.Entry<K, V>, ST.ents(~K, ~V, Con{x, t}, nl, pl)), ST.ent(K, V, ST.nd(K, nl, x), ST.pv(V, pl, x)), head_ents(~K, ~V, nl, pl, Con{x, t}, h)) : {S.key_m(K, V, _) == M.node_key(~K, ST.nd(K, nl, x)) : Maybe<&2, K>}
      km_some(K, V, ST.nd(K, nl, x), ST.pv(V, pl, x), L.and_left(S.is_some(M.Entry<K, V>, ST.ent(K, V, ST.nd(K, nl, x), ST.pv(V, pl, x))), oks(~K, ~V, t, nl, pl), h))

def last_key_eq(~K: Data, ~V: Data, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +xs: List<&2, Nat>, +h: {oks(~K, ~V, xs, nl, pl) == True{} : Bool}) -> {S.key_m(K, V, S.last(M.Entry<K, V>, ST.ents(~K, ~V, xs, nl, pl))) == M.node_key(~K, ST.nd(K, nl, ST.last0(xs))) : Maybe<&2, K>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %Equal.sym(Maybe<&2, M.Entry<K, V>>, S.last(M.Entry<K, V>, ST.ents(~K, ~V, Con{x, t}, nl, pl)), ST.ent(K, V, ST.nd(K, nl, ST.last0(Con{x, t})), ST.pv(V, pl, ST.last0(Con{x, t}))), last_ents(~K, ~V, nl, pl, t, x, h)) : {S.key_m(K, V, _) == M.node_key(~K, ST.nd(K, nl, ST.last0(Con{x, t}))) : Maybe<&2, K>}
      km_some(K, V, ST.nd(K, nl, ST.last0(Con{x, t})), ST.pv(V, pl, ST.last0(Con{x, t})), last0_some(~K, ~V, nl, pl, t, x, h))

def last_ents_all(~K: Data, ~V: Data, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +xs: List<&2, Nat>, +h: {oks(~K, ~V, xs, nl, pl) == True{} : Bool}) -> {S.last(M.Entry<K, V>, ST.ents(~K, ~V, xs, nl, pl)) == ST.ent(K, V, ST.nd(K, nl, ST.last0(xs)), ST.pv(V, pl, ST.last0(xs))) : Maybe<&2, M.Entry<K, V>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      last_ents(~K, ~V, nl, pl, t, x, h)

# ---- the mirror's reads at an id ----

def ev_m(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +x: M.Node<K>, +m: Maybe<&2, V>) -> {MI.entry_value(~K, ~V, ~cmp, M.node_key(~K, x), (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, m)) == (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, ST.ent(K, V, x, m)) : ST.Sh<K, V> & Maybe<&2, M.Entry<K, V>>}:
  match x m:
    case M.Free{f} None{}:
      {==}
    case M.Free{f} Some{v}:
      {==}
    case M.N{c, x1, x2, x3, key} None{}:
      {==}
    case M.N{c, x1, x2, x3, key} Some{v}:
      {==}


def first_entry_m(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +hg: {ST.goodF(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl) == True{} : Bool}) -> {MI.first_entry(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}) == (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, S.head(M.Entry<K, V>, ST.ents(~K, ~V, ST.ids(tg), nl, pl))) : ST.Sh<K, V> & Maybe<&2, M.Entry<K, V>>}:
  +e = N.eq_from_is_eq(lo, ST.fst0(ST.ids(tg)), ST.g_clo(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg))
  %Equal.sym(ST.Sh<K, V> & Maybe<&2, M.Entry<K, V>>, MI.entry_snapshot(~K, ~V, ~cmp, (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, lo)), (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, ST.ent(K, V, ST.nd(K, nl, lo), ST.pv(V, pl, lo))), ev_m(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, ST.nd(K, nl, lo), ST.pv(V, pl, lo))) : {_ == (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, S.head(M.Entry<K, V>, ST.ents(~K, ~V, ST.ids(tg), nl, pl))) : ST.Sh<K, V> & Maybe<&2, M.Entry<K, V>>}
  %Equal.sym(Nat, lo, ST.fst0(ST.ids(tg)), e) : {(ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, ST.ent(K, V, ST.nd(K, nl, _), ST.pv(V, pl, _))) == (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, S.head(M.Entry<K, V>, ST.ents(~K, ~V, ST.ids(tg), nl, pl))) : ST.Sh<K, V> & Maybe<&2, M.Entry<K, V>>}
  %Equal.sym(Maybe<&2, M.Entry<K, V>>, S.head(M.Entry<K, V>, ST.ents(~K, ~V, ST.ids(tg), nl, pl)), ST.ent(K, V, ST.nd(K, nl, ST.fst0(ST.ids(tg))), ST.pv(V, pl, ST.fst0(ST.ids(tg)))), head_ents(~K, ~V, nl, pl, ST.ids(tg), oks_tree(~K, ~V, nl, pl, tg, 0n, ST.g_crep(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg), ST.g_cpay(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg)))) : {(ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, ST.ent(K, V, ST.nd(K, nl, ST.fst0(ST.ids(tg))), ST.pv(V, pl, ST.fst0(ST.ids(tg))))) == (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, _) : ST.Sh<K, V> & Maybe<&2, M.Entry<K, V>>}
  {==}

def last_entry_m(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +hg: {ST.goodF(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl) == True{} : Bool}) -> {MI.last_entry(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}) == (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, S.last(M.Entry<K, V>, ST.ents(~K, ~V, ST.ids(tg), nl, pl))) : ST.Sh<K, V> & Maybe<&2, M.Entry<K, V>>}:
  +e = N.eq_from_is_eq(hi, ST.last0(ST.ids(tg)), ST.g_chi(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg))
  %Equal.sym(ST.Sh<K, V> & Maybe<&2, M.Entry<K, V>>, MI.entry_snapshot(~K, ~V, ~cmp, (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, hi)), (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, ST.ent(K, V, ST.nd(K, nl, hi), ST.pv(V, pl, hi))), ev_m(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, ST.nd(K, nl, hi), ST.pv(V, pl, hi))) : {_ == (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, S.last(M.Entry<K, V>, ST.ents(~K, ~V, ST.ids(tg), nl, pl))) : ST.Sh<K, V> & Maybe<&2, M.Entry<K, V>>}
  %Equal.sym(Nat, hi, ST.last0(ST.ids(tg)), e) : {(ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, ST.ent(K, V, ST.nd(K, nl, _), ST.pv(V, pl, _))) == (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, S.last(M.Entry<K, V>, ST.ents(~K, ~V, ST.ids(tg), nl, pl))) : ST.Sh<K, V> & Maybe<&2, M.Entry<K, V>>}
  %Equal.sym(Maybe<&2, M.Entry<K, V>>, S.last(M.Entry<K, V>, ST.ents(~K, ~V, ST.ids(tg), nl, pl)), ST.ent(K, V, ST.nd(K, nl, ST.last0(ST.ids(tg))), ST.pv(V, pl, ST.last0(ST.ids(tg)))), last_ents_all(~K, ~V, nl, pl, ST.ids(tg), oks_tree(~K, ~V, nl, pl, tg, 0n, ST.g_crep(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg), ST.g_cpay(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg)))) : {(ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, ST.ent(K, V, ST.nd(K, nl, ST.last0(ST.ids(tg))), ST.pv(V, pl, ST.last0(ST.ids(tg))))) == (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, _) : ST.Sh<K, V> & Maybe<&2, M.Entry<K, V>>}
  {==}

def first_key_m(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +hg: {ST.goodF(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl) == True{} : Bool}) -> {MI.first_key(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}) == (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, S.key_m(K, V, S.head(M.Entry<K, V>, ST.ents(~K, ~V, ST.ids(tg), nl, pl)))) : ST.Sh<K, V> & Maybe<&2, K>}:
  +e = N.eq_from_is_eq(lo, ST.fst0(ST.ids(tg)), ST.g_clo(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg))
  %Equal.sym(Nat, lo, ST.fst0(ST.ids(tg)), e) : {(ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, M.node_key(~K, ST.nd(K, nl, _))) == (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, S.key_m(K, V, S.head(M.Entry<K, V>, ST.ents(~K, ~V, ST.ids(tg), nl, pl)))) : ST.Sh<K, V> & Maybe<&2, K>}
  %Equal.sym(Maybe<&2, K>, S.key_m(K, V, S.head(M.Entry<K, V>, ST.ents(~K, ~V, ST.ids(tg), nl, pl))), M.node_key(~K, ST.nd(K, nl, ST.fst0(ST.ids(tg)))), first_key_eq(~K, ~V, nl, pl, ST.ids(tg), oks_tree(~K, ~V, nl, pl, tg, 0n, ST.g_crep(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg), ST.g_cpay(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg)))) : {(ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, M.node_key(~K, ST.nd(K, nl, ST.fst0(ST.ids(tg))))) == (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, _) : ST.Sh<K, V> & Maybe<&2, K>}
  {==}

def last_key_m(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +hg: {ST.goodF(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl) == True{} : Bool}) -> {MI.last_key(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}) == (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, S.key_m(K, V, S.last(M.Entry<K, V>, ST.ents(~K, ~V, ST.ids(tg), nl, pl)))) : ST.Sh<K, V> & Maybe<&2, K>}:
  +e = N.eq_from_is_eq(hi, ST.last0(ST.ids(tg)), ST.g_chi(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg))
  %Equal.sym(Nat, hi, ST.last0(ST.ids(tg)), e) : {(ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, M.node_key(~K, ST.nd(K, nl, _))) == (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, S.key_m(K, V, S.last(M.Entry<K, V>, ST.ents(~K, ~V, ST.ids(tg), nl, pl)))) : ST.Sh<K, V> & Maybe<&2, K>}
  %Equal.sym(Maybe<&2, K>, S.key_m(K, V, S.last(M.Entry<K, V>, ST.ents(~K, ~V, ST.ids(tg), nl, pl))), M.node_key(~K, ST.nd(K, nl, ST.last0(ST.ids(tg)))), last_key_eq(~K, ~V, nl, pl, ST.ids(tg), oks_tree(~K, ~V, nl, pl, tg, 0n, ST.g_crep(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg), ST.g_cpay(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg)))) : {(ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, M.node_key(~K, ST.nd(K, nl, ST.last0(ST.ids(tg))))) == (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, _) : ST.Sh<K, V> & Maybe<&2, K>}
  {==}
