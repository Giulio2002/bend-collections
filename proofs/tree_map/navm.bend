import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/order.bend as O
import ../spec/common.bend as SC
import ../spec/tree_map.bend as S
import ../../src/containers/balanced_search_tree.bend as M
import ../lru/lists.bend as LS
import ../lru/state.bend as LST
import ./nbr.bend as NB
import ./state.bend as ST
import ./mirror.bend as MI
import ./tree.bend as TR
import ./find.bend as FI
import ./reads.bend as RD
import ./ends.bend as EN
import ./path.bend as P
import ./nav.bend as NV
import ./navs.bend as NS

# Navigation over a good shadow: navigate is the ghost navigation from the
# root with an empty path, so the entry (and the key) at its id is the
# specification's nav. (source: tools/generators/tm_hand/navm.src)


def navigate_m(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +k: K, +h: Bool, +incl: Bool, +hg: {ST.goodF(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl) == True{} : Bool}) -> {MI.navigate(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, k, h, incl) == (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, NV.gnav(~K, ~cmp, tg, Nil{}, nl, k, h, incl)) : ST.Sh<K, V> & Nat}:
  +er = N.eq_from_is_eq(root, ST.rid(tg), ST.g_croot(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg))
  +hnd0 = LS.nd_l(ST.ids(tg), fl, ST.g_cnd(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg))
  +hnd = L.subst(List<&2, Nat>, z => {LST.nodupn(z) == True{} : Bool}, ST.ids(tg), SC.append(Nat, ST.ids(tg), Nil{}), Equal.sym(List<&2, Nat>, SC.append(Nat, ST.ids(tg), Nil{}), ST.ids(tg), LL.append_nil(Nat, ST.ids(tg))), hnd0)
  %Equal.sym(Nat, root, ST.rid(tg), er) : {MI.nav_loop(~K, ~V, ~cmp, 1n+n, k, h, incl, _, 0n, MI.probe(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, _, k)) == (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, NV.gnav(~K, ~cmp, tg, Nil{}, nl, k, h, incl)) : ST.Sh<K, V> & Nat}
  %Equal.sym(Nat, 0n, ST.pk(Nat, h, 0n, 0n), Equal.sym(Nat, ST.pk(Nat, h, 0n, 0n), 0n, NB.pk_same(h, 0n))) : {MI.nav_loop(~K, ~V, ~cmp, 1n+n, k, h, incl, ST.rid(tg), _, MI.probe(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, ST.rid(tg), k)) == (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, NV.gnav(~K, ~cmp, tg, Nil{}, nl, k, h, incl)) : ST.Sh<K, V> & Nat}
  NV.nav_ptr(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, 1n+n, Nil{}, tg, k, h, incl, ST.g_crep(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg), {==}, hnd, Equal.sym(List<&2, Nat>, SC.append(Nat, ST.ids(tg), Nil{}), ST.ids(tg), LL.append_nil(Nat, ST.ids(tg))), N.eq_from_is_eq(n, SC.length(Nat, ST.ids(tg)), ST.g_csz(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg)), RD.fuel_ok(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg))


# the entry at navigate's id is nav's
def gnav_ent(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +k: K, +h: Bool, +incl: Bool, +hg: {ST.goodF(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl) == True{} : Bool}) -> {ST.ent(K, V, ST.nd(K, nl, NV.gnav(~K, ~cmp, tg, Nil{}, nl, k, h, incl)), ST.pv(V, pl, NV.gnav(~K, ~cmp, tg, Nil{}, nl, k, h, incl))) == S.nav(~K, ~V, ~cmp, k, h, incl, ST.ents(~K, ~V, ST.ids(tg), nl, pl)) : Maybe<&2, M.Entry<K, V>>}:
  +ho = L.subst(List<&2, Nat>, z => {ST.ordered(~K, ~V, ~cmp, ST.ents(~K, ~V, z, nl, pl)) == True{} : Bool}, ST.ids(tg), SC.append(Nat, ST.ids(tg), Nil{}), Equal.sym(List<&2, Nat>, SC.append(Nat, ST.ids(tg), Nil{}), ST.ids(tg), LL.append_nil(Nat, ST.ids(tg))), ST.g_cord(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg))
  +hk = L.subst(List<&2, Nat>, z => {EN.oks(~K, ~V, z, nl, pl) == True{} : Bool}, ST.ids(tg), SC.append(Nat, ST.ids(tg), Nil{}), Equal.sym(List<&2, Nat>, SC.append(Nat, ST.ids(tg), Nil{}), ST.ids(tg), LL.append_nil(Nat, ST.ids(tg))), EN.oks_tree(~K, ~V, nl, pl, tg, 0n, ST.g_crep(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg), ST.g_cpay(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg)))
  %Equal.sym(List<&2, Nat>, ST.ids(tg), SC.append(Nat, ST.ids(tg), Nil{}), Equal.sym(List<&2, Nat>, SC.append(Nat, ST.ids(tg), Nil{}), ST.ids(tg), LL.append_nil(Nat, ST.ids(tg)))) : {ST.ent(K, V, ST.nd(K, nl, NV.gnav(~K, ~cmp, tg, Nil{}, nl, k, h, incl)), ST.pv(V, pl, NV.gnav(~K, ~cmp, tg, Nil{}, nl, k, h, incl))) == S.nav(~K, ~V, ~cmp, k, h, incl, ST.ents(~K, ~V, _, nl, pl)) : Maybe<&2, M.Entry<K, V>>}
  NS.gspec(~K, ~V, ~cmp, ~o, nl, pl, tg, Nil{}, k, h, incl, ST.g_crep(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg), ST.g_cpay(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg), ho, hk, {==}, {==})

def nav_entry_m(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +k: K, +h: Bool, +incl: Bool, +hg: {ST.goodF(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl) == True{} : Bool}) -> {MI.entry_snapshot(~K, ~V, ~cmp, MI.navigate(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, k, h, incl)) == (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, S.nav(~K, ~V, ~cmp, k, h, incl, ST.ents(~K, ~V, ST.ids(tg), nl, pl))) : ST.Sh<K, V> & Maybe<&2, M.Entry<K, V>>}:
  %Equal.sym(ST.Sh<K, V> & Nat, MI.navigate(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, k, h, incl), (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, NV.gnav(~K, ~cmp, tg, Nil{}, nl, k, h, incl)), navigate_m(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, k, h, incl, hg)) : {MI.entry_snapshot(~K, ~V, ~cmp, _) == (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, S.nav(~K, ~V, ~cmp, k, h, incl, ST.ents(~K, ~V, ST.ids(tg), nl, pl))) : ST.Sh<K, V> & Maybe<&2, M.Entry<K, V>>}
  %Equal.sym(ST.Sh<K, V> & Maybe<&2, M.Entry<K, V>>, MI.entry_snapshot(~K, ~V, ~cmp, (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, NV.gnav(~K, ~cmp, tg, Nil{}, nl, k, h, incl))), (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, ST.ent(K, V, ST.nd(K, nl, NV.gnav(~K, ~cmp, tg, Nil{}, nl, k, h, incl)), ST.pv(V, pl, NV.gnav(~K, ~cmp, tg, Nil{}, nl, k, h, incl)))), EN.ev_m(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, ST.nd(K, nl, NV.gnav(~K, ~cmp, tg, Nil{}, nl, k, h, incl)), ST.pv(V, pl, NV.gnav(~K, ~cmp, tg, Nil{}, nl, k, h, incl)))) : {_ == (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, S.nav(~K, ~V, ~cmp, k, h, incl, ST.ents(~K, ~V, ST.ids(tg), nl, pl))) : ST.Sh<K, V> & Maybe<&2, M.Entry<K, V>>}
  %Equal.sym(Maybe<&2, M.Entry<K, V>>, ST.ent(K, V, ST.nd(K, nl, NV.gnav(~K, ~cmp, tg, Nil{}, nl, k, h, incl)), ST.pv(V, pl, NV.gnav(~K, ~cmp, tg, Nil{}, nl, k, h, incl))), S.nav(~K, ~V, ~cmp, k, h, incl, ST.ents(~K, ~V, ST.ids(tg), nl, pl)), gnav_ent(~K, ~V, ~cmp, ~o, n, root, lo, hi, free, l, d, nl, pl, tg, fl, k, h, incl, hg)) : {(ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, _) == (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, S.nav(~K, ~V, ~cmp, k, h, incl, ST.ents(~K, ~V, ST.ids(tg), nl, pl))) : ST.Sh<K, V> & Maybe<&2, M.Entry<K, V>>}
  {==}

# ---- keys ----


def keq_fst(~K: Data, ~V: Data, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +xs: List<&2, Nat>, +h: {EN.oks(~K, ~V, xs, nl, pl) == True{} : Bool}) -> {S.key_m(K, V, ST.ent(K, V, ST.nd(K, nl, ST.fst0(xs)), ST.pv(V, pl, ST.fst0(xs)))) == M.node_key(~K, ST.nd(K, nl, ST.fst0(xs))) : Maybe<&2, K>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      EN.km_some(K, V, ST.nd(K, nl, x), ST.pv(V, pl, x), L.and_left(S.is_some(M.Entry<K, V>, ST.ent(K, V, ST.nd(K, nl, x), ST.pv(V, pl, x))), EN.oks(~K, ~V, t, nl, pl), h))

def keq_last(~K: Data, ~V: Data, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +xs: List<&2, Nat>, +h: {EN.oks(~K, ~V, xs, nl, pl) == True{} : Bool}) -> {S.key_m(K, V, ST.ent(K, V, ST.nd(K, nl, ST.last0(xs)), ST.pv(V, pl, ST.last0(xs)))) == M.node_key(~K, ST.nd(K, nl, ST.last0(xs))) : Maybe<&2, K>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      EN.km_some(K, V, ST.nd(K, nl, ST.last0(Con{x, t})), ST.pv(V, pl, ST.last0(Con{x, t})), EN.last0_some(~K, ~V, nl, pl, t, x, h))

def keq_pk(~K: Data, ~V: Data, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +h: Bool, +a: List<&2, Nat>, +b: List<&2, Nat>, +ha: {EN.oks(~K, ~V, a, nl, pl) == True{} : Bool}, +hb: {EN.oks(~K, ~V, b, nl, pl) == True{} : Bool}) -> {S.key_m(K, V, ST.ent(K, V, ST.nd(K, nl, ST.pk(Nat, h, ST.fst0(a), ST.last0(b))), ST.pv(V, pl, ST.pk(Nat, h, ST.fst0(a), ST.last0(b))))) == M.node_key(~K, ST.nd(K, nl, ST.pk(Nat, h, ST.fst0(a), ST.last0(b)))) : Maybe<&2, K>}:
  match h:
    case True{}:
      keq_fst(~K, ~V, nl, pl, a, ha)
    case False{}:
      keq_last(~K, ~V, nl, pl, b, hb)


def keq_eq(~K: Data, ~V: Data, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +c: List<&2, P.Fr>, +i: Nat, +l: ST.Tr, +r: ST.Tr, +h: Bool, +incl: Bool, +hi: {S.key_m(K, V, ST.ent(K, V, ST.nd(K, nl, i), ST.pv(V, pl, i))) == M.node_key(~K, ST.nd(K, nl, i)) : Maybe<&2, K>}, +hx: {EN.oks(~K, ~V, SC.append(Nat, P.before(c), ST.ids(l)), nl, pl) == True{} : Bool}, +hy: {EN.oks(~K, ~V, SC.append(Nat, ST.ids(r), P.after(c)), nl, pl) == True{} : Bool}) -> {S.key_m(K, V, ST.ent(K, V, ST.nd(K, nl, ST.pk(Nat, incl, i, ST.pk(Nat, h, ST.fst0(SC.append(Nat, ST.ids(r), P.after(c))), ST.last0(SC.append(Nat, P.before(c), ST.ids(l)))))), ST.pv(V, pl, ST.pk(Nat, incl, i, ST.pk(Nat, h, ST.fst0(SC.append(Nat, ST.ids(r), P.after(c))), ST.last0(SC.append(Nat, P.before(c), ST.ids(l)))))))) == M.node_key(~K, ST.nd(K, nl, ST.pk(Nat, incl, i, ST.pk(Nat, h, ST.fst0(SC.append(Nat, ST.ids(r), P.after(c))), ST.last0(SC.append(Nat, P.before(c), ST.ids(l))))))) : Maybe<&2, K>}:
  match incl:
    case True{}:
      hi
    case False{}:
      keq_pk(~K, ~V, nl, pl, h, SC.append(Nat, ST.ids(r), P.after(c)), SC.append(Nat, P.before(c), ST.ids(l)), hy, hx)

def keq_c(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +c: List<&2, P.Fr>, +i: Nat, +l: ST.Tr, +r: ST.Tr, +k: K, +h: Bool, +incl: Bool, +ihl: {S.key_m(K, V, ST.ent(K, V, ST.nd(K, nl, NV.gnav(~K, ~cmp, l, Con{P.FR{i, True{}, r}, c}, nl, k, h, incl)), ST.pv(V, pl, NV.gnav(~K, ~cmp, l, Con{P.FR{i, True{}, r}, c}, nl, k, h, incl)))) == M.node_key(~K, ST.nd(K, nl, NV.gnav(~K, ~cmp, l, Con{P.FR{i, True{}, r}, c}, nl, k, h, incl))) : Maybe<&2, K>}, +ihr: {S.key_m(K, V, ST.ent(K, V, ST.nd(K, nl, NV.gnav(~K, ~cmp, r, Con{P.FR{i, False{}, l}, c}, nl, k, h, incl)), ST.pv(V, pl, NV.gnav(~K, ~cmp, r, Con{P.FR{i, False{}, l}, c}, nl, k, h, incl)))) == M.node_key(~K, ST.nd(K, nl, NV.gnav(~K, ~cmp, r, Con{P.FR{i, False{}, l}, c}, nl, k, h, incl))) : Maybe<&2, K>}, +he: {S.key_m(K, V, ST.ent(K, V, ST.nd(K, nl, ST.pk(Nat, incl, i, ST.pk(Nat, h, ST.fst0(SC.append(Nat, ST.ids(r), P.after(c))), ST.last0(SC.append(Nat, P.before(c), ST.ids(l)))))), ST.pv(V, pl, ST.pk(Nat, incl, i, ST.pk(Nat, h, ST.fst0(SC.append(Nat, ST.ids(r), P.after(c))), ST.last0(SC.append(Nat, P.before(c), ST.ids(l)))))))) == M.node_key(~K, ST.nd(K, nl, ST.pk(Nat, incl, i, ST.pk(Nat, h, ST.fst0(SC.append(Nat, ST.ids(r), P.after(c))), ST.last0(SC.append(Nat, P.before(c), ST.ids(l))))))) : Maybe<&2, K>}, +cc: Cmp) -> {S.key_m(K, V, ST.ent(K, V, ST.nd(K, nl, TR.pk3(Nat, cc, NV.gnav(~K, ~cmp, l, Con{P.FR{i, True{}, r}, c}, nl, k, h, incl), NV.gnav(~K, ~cmp, r, Con{P.FR{i, False{}, l}, c}, nl, k, h, incl), ST.pk(Nat, incl, i, ST.pk(Nat, h, ST.fst0(SC.append(Nat, ST.ids(r), P.after(c))), ST.last0(SC.append(Nat, P.before(c), ST.ids(l))))))), ST.pv(V, pl, TR.pk3(Nat, cc, NV.gnav(~K, ~cmp, l, Con{P.FR{i, True{}, r}, c}, nl, k, h, incl), NV.gnav(~K, ~cmp, r, Con{P.FR{i, False{}, l}, c}, nl, k, h, incl), ST.pk(Nat, incl, i, ST.pk(Nat, h, ST.fst0(SC.append(Nat, ST.ids(r), P.after(c))), ST.last0(SC.append(Nat, P.before(c), ST.ids(l))))))))) == M.node_key(~K, ST.nd(K, nl, TR.pk3(Nat, cc, NV.gnav(~K, ~cmp, l, Con{P.FR{i, True{}, r}, c}, nl, k, h, incl), NV.gnav(~K, ~cmp, r, Con{P.FR{i, False{}, l}, c}, nl, k, h, incl), ST.pk(Nat, incl, i, ST.pk(Nat, h, ST.fst0(SC.append(Nat, ST.ids(r), P.after(c))), ST.last0(SC.append(Nat, P.before(c), ST.ids(l)))))))) : Maybe<&2, K>}:
  match cc:
    case LT{}:
      ihl
    case GT{}:
      ihr
    case EQ{}:
      he

# the id navigation returns has a key exactly when it has an entry
def gnav_key(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +t: ST.Tr, +c: List<&2, P.Fr>, +k: K, +h: Bool, +incl: Bool, +hr: {ST.rep(~K, t, P.top(c), nl) == True{} : Bool}, +hp: {ST.pay(~V, t, pl) == True{} : Bool}, +hk: {EN.oks(~K, ~V, SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(t), P.after(c))), nl, pl) == True{} : Bool}) -> {S.key_m(K, V, ST.ent(K, V, ST.nd(K, nl, NV.gnav(~K, ~cmp, t, c, nl, k, h, incl)), ST.pv(V, pl, NV.gnav(~K, ~cmp, t, c, nl, k, h, incl)))) == M.node_key(~K, ST.nd(K, nl, NV.gnav(~K, ~cmp, t, c, nl, k, h, incl))) : Maybe<&2, K>}:
  match t:
    case ST.TE{}:
      keq_pk(~K, ~V, nl, pl, h, P.after(c), P.before(c), NS.oks_r(~K, ~V, nl, pl, P.before(c), P.after(c), hk), NS.oks_l(~K, ~V, nl, pl, P.before(c), P.after(c), hk))
    case ST.TN{+i, +l, +r}:
      +hk2 = L.subst(List<&2, Nat>, z => {EN.oks(~K, ~V, z, nl, pl) == True{} : Bool}, SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{i, l, r}), P.after(c))), SC.append(Nat, SC.append(Nat, P.before(c), ST.ids(l)), Con{i, SC.append(Nat, ST.ids(r), P.after(c))}), NS.wh_node(c, i, l, r), hk)
      +hx = NS.oks_l(~K, ~V, nl, pl, SC.append(Nat, P.before(c), ST.ids(l)), Con{i, SC.append(Nat, ST.ids(r), P.after(c))}, hk2)
      +hy = L.and_right(S.is_some(M.Entry<K, V>, ST.ent(K, V, ST.nd(K, nl, i), ST.pv(V, pl, i))), EN.oks(~K, ~V, SC.append(Nat, ST.ids(r), P.after(c)), nl, pl), NS.oks_r(~K, ~V, nl, pl, SC.append(Nat, P.before(c), ST.ids(l)), Con{i, SC.append(Nat, ST.ids(r), P.after(c))}, hk2))
      +hi = EN.km_some(K, V, ST.nd(K, nl, i), ST.pv(V, pl, i), EN.ent_some(K, V, ST.nd(K, nl, i), ST.pv(V, pl, i), ST.rid(l), ST.rid(r), P.top(c), TR.rep_node(~K, i, l, r, P.top(c), nl, hr), FI.pay_node(~V, i, l, r, pl, hp)))
      +ihl = gnav_key(~K, ~V, ~cmp, nl, pl, l, Con{P.FR{i, True{}, r}, c}, k, h, incl, TR.rep_l(~K, i, l, r, P.top(c), nl, hr), FI.pay_l(~V, i, l, r, pl, hp), L.subst(List<&2, Nat>, z => {EN.oks(~K, ~V, z, nl, pl) == True{} : Bool}, SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{i, l, r}), P.after(c))), SC.append(Nat, P.before(Con{P.FR{i, True{}, r}, c}), SC.append(Nat, ST.ids(l), P.after(Con{P.FR{i, True{}, r}, c}))), P.ids_l(c, i, l, r), hk))
      +ihr = gnav_key(~K, ~V, ~cmp, nl, pl, r, Con{P.FR{i, False{}, l}, c}, k, h, incl, TR.rep_r(~K, i, l, r, P.top(c), nl, hr), FI.pay_r(~V, i, l, r, pl, hp), L.subst(List<&2, Nat>, z => {EN.oks(~K, ~V, z, nl, pl) == True{} : Bool}, SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{i, l, r}), P.after(c))), SC.append(Nat, P.before(Con{P.FR{i, False{}, l}, c}), SC.append(Nat, ST.ids(r), P.after(Con{P.FR{i, False{}, l}, c}))), P.ids_r(c, i, l, r), hk))
      keq_c(~K, ~V, ~cmp, nl, pl, c, i, l, r, k, h, incl, ihl, ihr, keq_eq(~K, ~V, nl, pl, c, i, l, r, h, incl, hi, hx, hy), TR.kc(~K, ~cmp, k, ST.nd(K, nl, i)))

def nav_key_m(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +k: K, +h: Bool, +incl: Bool, +hg: {ST.goodF(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl) == True{} : Bool}) -> {MI.key_id(~K, ~V, ~cmp, MI.navigate(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, k, h, incl)) == (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, S.key_m(K, V, S.nav(~K, ~V, ~cmp, k, h, incl, ST.ents(~K, ~V, ST.ids(tg), nl, pl)))) : ST.Sh<K, V> & Maybe<&2, K>}:
  +hk = L.subst(List<&2, Nat>, z => {EN.oks(~K, ~V, z, nl, pl) == True{} : Bool}, ST.ids(tg), SC.append(Nat, ST.ids(tg), Nil{}), Equal.sym(List<&2, Nat>, SC.append(Nat, ST.ids(tg), Nil{}), ST.ids(tg), LL.append_nil(Nat, ST.ids(tg))), EN.oks_tree(~K, ~V, nl, pl, tg, 0n, ST.g_crep(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg), ST.g_cpay(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg)))
  %Equal.sym(ST.Sh<K, V> & Nat, MI.navigate(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, k, h, incl), (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, NV.gnav(~K, ~cmp, tg, Nil{}, nl, k, h, incl)), navigate_m(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, k, h, incl, hg)) : {MI.key_id(~K, ~V, ~cmp, _) == (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, S.key_m(K, V, S.nav(~K, ~V, ~cmp, k, h, incl, ST.ents(~K, ~V, ST.ids(tg), nl, pl)))) : ST.Sh<K, V> & Maybe<&2, K>}
  %Equal.sym(Maybe<&2, M.Entry<K, V>>, S.nav(~K, ~V, ~cmp, k, h, incl, ST.ents(~K, ~V, ST.ids(tg), nl, pl)), ST.ent(K, V, ST.nd(K, nl, NV.gnav(~K, ~cmp, tg, Nil{}, nl, k, h, incl)), ST.pv(V, pl, NV.gnav(~K, ~cmp, tg, Nil{}, nl, k, h, incl))), Equal.sym(Maybe<&2, M.Entry<K, V>>, ST.ent(K, V, ST.nd(K, nl, NV.gnav(~K, ~cmp, tg, Nil{}, nl, k, h, incl)), ST.pv(V, pl, NV.gnav(~K, ~cmp, tg, Nil{}, nl, k, h, incl))), S.nav(~K, ~V, ~cmp, k, h, incl, ST.ents(~K, ~V, ST.ids(tg), nl, pl)), gnav_ent(~K, ~V, ~cmp, ~o, n, root, lo, hi, free, l, d, nl, pl, tg, fl, k, h, incl, hg))) : {(ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, M.node_key(~K, ST.nd(K, nl, NV.gnav(~K, ~cmp, tg, Nil{}, nl, k, h, incl)))) == (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, S.key_m(K, V, _)) : ST.Sh<K, V> & Maybe<&2, K>}
  %Equal.sym(Maybe<&2, K>, S.key_m(K, V, ST.ent(K, V, ST.nd(K, nl, NV.gnav(~K, ~cmp, tg, Nil{}, nl, k, h, incl)), ST.pv(V, pl, NV.gnav(~K, ~cmp, tg, Nil{}, nl, k, h, incl)))), M.node_key(~K, ST.nd(K, nl, NV.gnav(~K, ~cmp, tg, Nil{}, nl, k, h, incl))), gnav_key(~K, ~V, ~cmp, nl, pl, tg, Nil{}, k, h, incl, ST.g_crep(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg), ST.g_cpay(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg), hk)) : {(ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, M.node_key(~K, ST.nd(K, nl, NV.gnav(~K, ~cmp, tg, Nil{}, nl, k, h, incl)))) == (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, _) : ST.Sh<K, V> & Maybe<&2, K>}
  {==}
