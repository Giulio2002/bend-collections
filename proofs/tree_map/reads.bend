import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/order.bend as O
import ../spec/common.bend as SC
import ../spec/tree_map.bend as S
import ../../src/containers/balanced_search_tree.bend as M
import ./state.bend as ST
import ./mirror.bend as MI
import ./tree.bend as TR
import ./find.bend as FI

# The read-only operations of the mirror over a good shadow: the search
# returns the ghost search from the root (fuel 1+n suffices, the height
# being at most the size), so get, contains_key and get_or_default answer
# the specification's lookup, and size and is_empty its length.
# (source: tools/generators/tm_hand/reads.src)


def fuel_ok(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +hg: {ST.goodF(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl) == True{} : Bool}) -> {Nat.is_lt(TR.ht(tg), 1n+n) == True{} : Bool}:
  +e = N.eq_from_is_eq(n, SC.length(Nat, ST.ids(tg)), ST.g_csz(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg))
  N.le_lt_succ(TR.ht(tg), n, L.subst(Nat, z => {Nat.is_le(TR.ht(tg), z) == True{} : Bool}, SC.length(Nat, ST.ids(tg)), n, Equal.sym(Nat, n, SC.length(Nat, ST.ids(tg)), e), TR.ht_le(tg)))

# the search is the ghost search from the root
def search_m(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +k: K, +hg: {ST.goodF(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl) == True{} : Bool}) -> {MI.search(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, k) == (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, TR.tsearch(~K, ~V, ~cmp, tg, nl, k, 0n, False{})) : ST.Sh<K, V> & M.Search}:
  +er = N.eq_from_is_eq(root, ST.rid(tg), ST.g_croot(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg))
  %Equal.sym(Nat, root, ST.rid(tg), er) : {MI.search_loop(~K, ~V, ~cmp, 1n+n, k, _, 0n, False{}, MI.probe(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, _, k)) == (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, TR.tsearch(~K, ~V, ~cmp, tg, nl, k, 0n, False{})) : ST.Sh<K, V> & M.Search}
  TR.sl(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, 1n+n, tg, 0n, False{}, k, ST.g_crep(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg), fuel_ok(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg))

def gf_m(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +s: M.Search) -> {MI.get_found(~K, ~V, ~cmp, (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, s)) == (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, ST.pv(V, pl, FI.sfound(s))) : ST.Sh<K, V> & Maybe<&2, V>}:
  match s:
    case M.Search{f, p, lf}:
      {==}

def get_m(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +k: K, +hg: {ST.goodF(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl) == True{} : Bool}) -> {MI.get(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, k) == (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, S.find(~K, ~V, ~cmp, k, ST.ents(~K, ~V, ST.ids(tg), nl, pl))) : ST.Sh<K, V> & Maybe<&2, V>}:
  %Equal.sym(ST.Sh<K, V> & M.Search, MI.search(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, k), (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, TR.tsearch(~K, ~V, ~cmp, tg, nl, k, 0n, False{})), search_m(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, k, hg)) : {MI.get_found(~K, ~V, ~cmp, _) == (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, S.find(~K, ~V, ~cmp, k, ST.ents(~K, ~V, ST.ids(tg), nl, pl))) : ST.Sh<K, V> & Maybe<&2, V>}
  %Equal.sym(ST.Sh<K, V> & Maybe<&2, V>, MI.get_found(~K, ~V, ~cmp, (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, TR.tsearch(~K, ~V, ~cmp, tg, nl, k, 0n, False{}))), (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, ST.pv(V, pl, FI.sfound(TR.tsearch(~K, ~V, ~cmp, tg, nl, k, 0n, False{})))), gf_m(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, TR.tsearch(~K, ~V, ~cmp, tg, nl, k, 0n, False{}))) : {_ == (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, S.find(~K, ~V, ~cmp, k, ST.ents(~K, ~V, ST.ids(tg), nl, pl))) : ST.Sh<K, V> & Maybe<&2, V>}
  %Equal.sym(Maybe<&2, V>, ST.pv(V, pl, FI.sfound(TR.tsearch(~K, ~V, ~cmp, tg, nl, k, 0n, False{}))), S.find(~K, ~V, ~cmp, k, ST.ents(~K, ~V, ST.ids(tg), nl, pl)), FI.tfind(~K, ~V, ~cmp, ~o, nl, pl, tg, 0n, False{}, k, ST.g_crep(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg), ST.g_cpay(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg), ST.g_cord(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg))) : {(ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, _) == (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, S.find(~K, ~V, ~cmp, k, ST.ents(~K, ~V, ST.ids(tg), nl, pl))) : ST.Sh<K, V> & Maybe<&2, V>}
  {==}

# ---- contains_key ----

def some_eq(-V: Data, +m: Maybe<&2, V>) -> {S.is_some(V, m) == ST.some2(V, m) : Bool}:
  match m:
    case None{}:
      {==}
    case Some{v}:
      {==}


def ts_some_c(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +i: Nat, +tl: ST.Tr, +tr: ST.Tr, +p: Nat, +left: Bool, +k: K, +hi: {Nat.is_lt(0n, i) == True{} : Bool}, +hs: {ST.some2(V, ST.pv(V, pl, i)) == True{} : Bool}, +ihl: {Nat.is_lt(0n, FI.sfound(TR.tsearch(~K, ~V, ~cmp, tl, nl, k, i, True{}))) == S.is_some(V, ST.pv(V, pl, FI.sfound(TR.tsearch(~K, ~V, ~cmp, tl, nl, k, i, True{})))) : Bool}, +ihr: {Nat.is_lt(0n, FI.sfound(TR.tsearch(~K, ~V, ~cmp, tr, nl, k, i, False{}))) == S.is_some(V, ST.pv(V, pl, FI.sfound(TR.tsearch(~K, ~V, ~cmp, tr, nl, k, i, False{})))) : Bool}, +cc: Cmp) -> {Nat.is_lt(0n, FI.sfound(TR.pk3(M.Search, cc, TR.tsearch(~K, ~V, ~cmp, tl, nl, k, i, True{}), TR.tsearch(~K, ~V, ~cmp, tr, nl, k, i, False{}), M.Search{i, p, left}))) == S.is_some(V, ST.pv(V, pl, FI.sfound(TR.pk3(M.Search, cc, TR.tsearch(~K, ~V, ~cmp, tl, nl, k, i, True{}), TR.tsearch(~K, ~V, ~cmp, tr, nl, k, i, False{}), M.Search{i, p, left})))) : Bool}:
  match cc:
    case LT{}:
      ihl
    case GT{}:
      ihr
    case EQ{}:
      %Equal.sym(Bool, S.is_some(V, ST.pv(V, pl, i)), ST.some2(V, ST.pv(V, pl, i)), some_eq(V, ST.pv(V, pl, i))) : {Nat.is_lt(0n, i) == _ : Bool}
      %Equal.sym(Bool, ST.some2(V, ST.pv(V, pl, i)), True{}, hs) : {Nat.is_lt(0n, i) == _ : Bool}
      hi

# the ghost search's id is nonzero exactly when its node has a value
def ts_some(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +t: ST.Tr, +p: Nat, +left: Bool, +k: K, +hr: {ST.rep(~K, t, p, nl) == True{} : Bool}, +hp: {ST.pay(~V, t, pl) == True{} : Bool}) -> {Nat.is_lt(0n, FI.sfound(TR.tsearch(~K, ~V, ~cmp, t, nl, k, p, left))) == S.is_some(V, ST.pv(V, pl, FI.sfound(TR.tsearch(~K, ~V, ~cmp, t, nl, k, p, left)))) : Bool}:
  match t:
    case ST.TE{}:
      {==}
    case ST.TN{+i, +tl, +tr}:
      +hi = L.and_left(Nat.is_lt(0n, i), Bool.and(ST.is_node(K, ST.nd(K, nl, i), ST.rid(tl), ST.rid(tr), p), Bool.and(ST.rep(~K, tl, i, nl), ST.rep(~K, tr, i, nl))), hr)
      ts_some_c(~K, ~V, ~cmp, nl, pl, i, tl, tr, p, left, k, hi, FI.pay_node(~V, i, tl, tr, pl, hp), ts_some(~K, ~V, ~cmp, nl, pl, tl, i, True{}, k, TR.rep_l(~K, i, tl, tr, p, nl, hr), FI.pay_l(~V, i, tl, tr, pl, hp)), ts_some(~K, ~V, ~cmp, nl, pl, tr, i, False{}, k, TR.rep_r(~K, i, tl, tr, p, nl, hr), FI.pay_r(~V, i, tl, tr, pl, hp)), TR.kc(~K, ~cmp, k, ST.nd(K, nl, i)))

def cf_m(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +s: M.Search) -> {MI.contains_found(~K, ~V, ~cmp, (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, s)) == (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, Nat.is_lt(0n, FI.sfound(s))) : ST.Sh<K, V> & Bool}:
  match s:
    case M.Search{f, p, lf}:
      {==}

def contains_key_m(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +k: K, +hg: {ST.goodF(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl) == True{} : Bool}) -> {MI.contains_key(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, k) == (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, S.is_some(V, S.find(~K, ~V, ~cmp, k, ST.ents(~K, ~V, ST.ids(tg), nl, pl)))) : ST.Sh<K, V> & Bool}:
  %Equal.sym(ST.Sh<K, V> & M.Search, MI.search(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, k), (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, TR.tsearch(~K, ~V, ~cmp, tg, nl, k, 0n, False{})), search_m(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, k, hg)) : {MI.contains_found(~K, ~V, ~cmp, _) == (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, S.is_some(V, S.find(~K, ~V, ~cmp, k, ST.ents(~K, ~V, ST.ids(tg), nl, pl)))) : ST.Sh<K, V> & Bool}
  %Equal.sym(ST.Sh<K, V> & Bool, MI.contains_found(~K, ~V, ~cmp, (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, TR.tsearch(~K, ~V, ~cmp, tg, nl, k, 0n, False{}))), (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, Nat.is_lt(0n, FI.sfound(TR.tsearch(~K, ~V, ~cmp, tg, nl, k, 0n, False{})))), cf_m(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, TR.tsearch(~K, ~V, ~cmp, tg, nl, k, 0n, False{}))) : {_ == (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, S.is_some(V, S.find(~K, ~V, ~cmp, k, ST.ents(~K, ~V, ST.ids(tg), nl, pl)))) : ST.Sh<K, V> & Bool}
  %Equal.sym(Maybe<&2, V>, S.find(~K, ~V, ~cmp, k, ST.ents(~K, ~V, ST.ids(tg), nl, pl)), ST.pv(V, pl, FI.sfound(TR.tsearch(~K, ~V, ~cmp, tg, nl, k, 0n, False{}))), Equal.sym(Maybe<&2, V>, ST.pv(V, pl, FI.sfound(TR.tsearch(~K, ~V, ~cmp, tg, nl, k, 0n, False{}))), S.find(~K, ~V, ~cmp, k, ST.ents(~K, ~V, ST.ids(tg), nl, pl)), FI.tfind(~K, ~V, ~cmp, ~o, nl, pl, tg, 0n, False{}, k, ST.g_crep(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg), ST.g_cpay(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg), ST.g_cord(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg)))) : {(ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, Nat.is_lt(0n, FI.sfound(TR.tsearch(~K, ~V, ~cmp, tg, nl, k, 0n, False{})))) == (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, S.is_some(V, _)) : ST.Sh<K, V> & Bool}
  %Equal.sym(Bool, Nat.is_lt(0n, FI.sfound(TR.tsearch(~K, ~V, ~cmp, tg, nl, k, 0n, False{}))), S.is_some(V, ST.pv(V, pl, FI.sfound(TR.tsearch(~K, ~V, ~cmp, tg, nl, k, 0n, False{})))), ts_some(~K, ~V, ~cmp, nl, pl, tg, 0n, False{}, k, ST.g_crep(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg), ST.g_cpay(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg))) : {(ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, _) == (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, S.is_some(V, ST.pv(V, pl, FI.sfound(TR.tsearch(~K, ~V, ~cmp, tg, nl, k, 0n, False{}))))) : ST.Sh<K, V> & Bool}
  {==}

# ---- get_or_default ----

def dv_m(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +fb: V, +m: Maybe<&2, V>) -> {MI.default_value(~K, ~V, ~cmp, fb, (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, m)) == (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, S.or_default(V, m, fb)) : ST.Sh<K, V> & V}:
  match m:
    case None{}:
      {==}
    case Some{v}:
      {==}

def get_or_default_m(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +k: K, +fb: V, +hg: {ST.goodF(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl) == True{} : Bool}) -> {MI.get_or_default(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, k, fb) == (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, S.or_default(V, S.find(~K, ~V, ~cmp, k, ST.ents(~K, ~V, ST.ids(tg), nl, pl)), fb)) : ST.Sh<K, V> & V}:
  %Equal.sym(ST.Sh<K, V> & Maybe<&2, V>, MI.get(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, k), (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, S.find(~K, ~V, ~cmp, k, ST.ents(~K, ~V, ST.ids(tg), nl, pl))), get_m(~K, ~V, ~cmp, ~o, n, root, lo, hi, free, l, d, nl, pl, tg, fl, k, hg)) : {MI.default_value(~K, ~V, ~cmp, fb, _) == (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, S.or_default(V, S.find(~K, ~V, ~cmp, k, ST.ents(~K, ~V, ST.ids(tg), nl, pl)), fb)) : ST.Sh<K, V> & V}
  dv_m(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, fb, S.find(~K, ~V, ~cmp, k, ST.ents(~K, ~V, ST.ids(tg), nl, pl)))

# ---- size ----

def lcm(-K: Data, -V: Data, +x: M.Node<K>, +m: Maybe<&2, V>, +a: Nat, +b: Nat, +q: Nat, +hx: {ST.is_node(K, x, a, b, q) == True{} : Bool}, +hm: {ST.some2(V, m) == True{} : Bool}, +r: List<&2, M.Entry<K, V>>) -> {SC.length(M.Entry<K, V>, ST.cons_m(M.Entry<K, V>, ST.ent(K, V, x, m), r)) == 1n+SC.length(M.Entry<K, V>, r) : Nat}:
  match x m:
    case M.Free{f} _:
      Empty.absurd({SC.length(M.Entry<K, V>, ST.cons_m(M.Entry<K, V>, ST.ent(K, V, M.Free{f}, m), r)) == 1n+SC.length(M.Entry<K, V>, r) : Nat}, L.false_true(hx))
    case M.N{c, x1, x2, x3, key} None{}:
      Empty.absurd({SC.length(M.Entry<K, V>, ST.cons_m(M.Entry<K, V>, ST.ent(K, V, M.N{c, x1, x2, x3, key}, None{}), r)) == 1n+SC.length(M.Entry<K, V>, r) : Nat}, L.false_true(hm))
    case M.N{c, x1, x2, x3, key} Some{v}:
      {==}


# every id of the tree gives one entry
def len_ents(~K: Data, ~V: Data, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +t: ST.Tr, +p: Nat, +hr: {ST.rep(~K, t, p, nl) == True{} : Bool}, +hp: {ST.pay(~V, t, pl) == True{} : Bool}) -> {SC.length(M.Entry<K, V>, ST.ents(~K, ~V, ST.ids(t), nl, pl)) == SC.length(Nat, ST.ids(t)) : Nat}:
  match t:
    case ST.TE{}:
      {==}
    case ST.TN{+i, +tl, +tr}:
      %Equal.sym(List<&2, M.Entry<K, V>>, ST.ents(~K, ~V, ST.ids(ST.TN{i, tl, tr}), nl, pl), SC.append(M.Entry<K, V>, ST.ents(~K, ~V, ST.ids(tl), nl, pl), ST.cons_m(M.Entry<K, V>, ST.ent(K, V, ST.nd(K, nl, i), ST.pv(V, pl, i)), ST.ents(~K, ~V, ST.ids(tr), nl, pl))), FI.ents_node(~K, ~V, nl, pl, i, tl, tr)) : {SC.length(M.Entry<K, V>, _) == SC.length(Nat, ST.ids(ST.TN{i, tl, tr})) : Nat}
      %Equal.sym(Nat, SC.length(M.Entry<K, V>, SC.append(M.Entry<K, V>, ST.ents(~K, ~V, ST.ids(tl), nl, pl), ST.cons_m(M.Entry<K, V>, ST.ent(K, V, ST.nd(K, nl, i), ST.pv(V, pl, i)), ST.ents(~K, ~V, ST.ids(tr), nl, pl)))), Nat.add(SC.length(M.Entry<K, V>, ST.ents(~K, ~V, ST.ids(tl), nl, pl)), SC.length(M.Entry<K, V>, ST.cons_m(M.Entry<K, V>, ST.ent(K, V, ST.nd(K, nl, i), ST.pv(V, pl, i)), ST.ents(~K, ~V, ST.ids(tr), nl, pl)))), LL.length_append(M.Entry<K, V>, ST.ents(~K, ~V, ST.ids(tl), nl, pl), ST.cons_m(M.Entry<K, V>, ST.ent(K, V, ST.nd(K, nl, i), ST.pv(V, pl, i)), ST.ents(~K, ~V, ST.ids(tr), nl, pl)))) : {_ == SC.length(Nat, ST.ids(ST.TN{i, tl, tr})) : Nat}
      %Equal.sym(Nat, SC.length(M.Entry<K, V>, ST.cons_m(M.Entry<K, V>, ST.ent(K, V, ST.nd(K, nl, i), ST.pv(V, pl, i)), ST.ents(~K, ~V, ST.ids(tr), nl, pl))), 1n+SC.length(M.Entry<K, V>, ST.ents(~K, ~V, ST.ids(tr), nl, pl)), lcm(K, V, ST.nd(K, nl, i), ST.pv(V, pl, i), ST.rid(tl), ST.rid(tr), p, TR.rep_node(~K, i, tl, tr, p, nl, hr), FI.pay_node(~V, i, tl, tr, pl, hp), ST.ents(~K, ~V, ST.ids(tr), nl, pl))) : {Nat.add(SC.length(M.Entry<K, V>, ST.ents(~K, ~V, ST.ids(tl), nl, pl)), _) == SC.length(Nat, ST.ids(ST.TN{i, tl, tr})) : Nat}
      %Equal.sym(Nat, SC.length(M.Entry<K, V>, ST.ents(~K, ~V, ST.ids(tl), nl, pl)), SC.length(Nat, ST.ids(tl)), len_ents(~K, ~V, nl, pl, tl, i, TR.rep_l(~K, i, tl, tr, p, nl, hr), FI.pay_l(~V, i, tl, tr, pl, hp))) : {Nat.add(_, 1n+SC.length(M.Entry<K, V>, ST.ents(~K, ~V, ST.ids(tr), nl, pl))) == SC.length(Nat, ST.ids(ST.TN{i, tl, tr})) : Nat}
      %Equal.sym(Nat, SC.length(M.Entry<K, V>, ST.ents(~K, ~V, ST.ids(tr), nl, pl)), SC.length(Nat, ST.ids(tr)), len_ents(~K, ~V, nl, pl, tr, i, TR.rep_r(~K, i, tl, tr, p, nl, hr), FI.pay_r(~V, i, tl, tr, pl, hp))) : {Nat.add(SC.length(Nat, ST.ids(tl)), 1n+_) == SC.length(Nat, ST.ids(ST.TN{i, tl, tr})) : Nat}
      Equal.sym(Nat, SC.length(Nat, ST.ids(ST.TN{i, tl, tr})), Nat.add(SC.length(Nat, ST.ids(tl)), 1n+SC.length(Nat, ST.ids(tr))), LL.length_append(Nat, ST.ids(tl), Con{i, ST.ids(tr)}))

# the size field is the number of entries
def size_eq(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +hg: {ST.goodF(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl) == True{} : Bool}) -> {n == SC.length(M.Entry<K, V>, ST.ents(~K, ~V, ST.ids(tg), nl, pl)) : Nat}:
  +e = N.eq_from_is_eq(n, SC.length(Nat, ST.ids(tg)), ST.g_csz(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg))
  %Equal.sym(Nat, SC.length(M.Entry<K, V>, ST.ents(~K, ~V, ST.ids(tg), nl, pl)), SC.length(Nat, ST.ids(tg)), len_ents(~K, ~V, nl, pl, tg, 0n, ST.g_crep(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg), ST.g_cpay(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg))) : {n == _ : Nat}
  e
