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
import ./ends.bend as EN
import ./path.bend as P
import ./dj.bend as DJ
import ./nav.bend as NA
import ./navm.bend as NM
import ./cur.bend as CU
import ./cnx.bend as CX
import ./vdef.bend as VD
import ../lib/nat_list.bend as NL

# A view's cursor: it starts at the id of the first (last) entry past its
# bound, which is 0 or an id of the tree, and whose key is the
# specification's start. (source: tools/generators/tm_hand/vit.src)


# ---- navigation returns 0 or an id of the tree ----

def pk_ok(+xs: List<&2, Nat>, +h: Bool, +a: Nat, +b: Nat, +ha: {CU.idok(xs, a) == True{} : Bool}, +hb: {CU.idok(xs, b) == True{} : Bool}) -> {CU.idok(xs, ST.pk(Nat, h, a, b)) == True{} : Bool}:
  match h:
    case True{}:
      ha
    case False{}:
      hb

def pk3_ok(+xs: List<&2, Nat>, +c: Cmp, +a: Nat, +b: Nat, +z: Nat, +ha: {CU.idok(xs, a) == True{} : Bool}, +hb: {CU.idok(xs, b) == True{} : Bool}, +hz: {CU.idok(xs, z) == True{} : Bool}) -> {CU.idok(xs, TR.pk3(Nat, c, a, b, z)) == True{} : Bool}:
  match c:
    case LT{}:
      ha
    case GT{}:
      hb
    case EQ{}:
      hz

def idok_self(+i: Nat, +t: List<&2, Nat>) -> {CU.idok(Con{i, t}, i) == True{} : Bool}:
  CU.or_r(Nat.is_eq(i, 0n), NL.memn(i, Con{i, t}), DJ.mem_hd(i, t))

def gnav_ok(~K: Data, ~cmp: K -> K -> Cmp, +t: ST.Tr, +c: List<&2, P.Fr>, +nl: List<&2, M.Node<K>>, +k: K, +h: Bool, +incl: Bool) -> {CU.idok(SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(t), P.after(c))), NA.gnav(~K, ~cmp, t, c, nl, k, h, incl)) == True{} : Bool}:
  match t:
    case ST.TE{}:
      pk_ok(SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TE{}), P.after(c))), h, ST.fst0(P.after(c)), ST.last0(P.before(c)), CX.idok_suf(P.before(c), P.after(c), ST.fst0(P.after(c)), CU.fst0_ok(P.after(c))), CX.idok_pre(P.before(c), P.after(c), ST.last0(P.before(c)), CU.last0_ok(P.before(c))))
    case ST.TN{+i, +tl, +tr}:
      +er = Equal.sym(List<&2, Nat>, SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{i, tl, tr}), P.after(c))), SC.append(Nat, P.before(Con{P.FR{i, False{}, tl}, c}), SC.append(Nat, ST.ids(tr), P.after(Con{P.FR{i, False{}, tl}, c}))), P.ids_r(c, i, tl, tr))
      +el = Equal.sym(List<&2, Nat>, SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{i, tl, tr}), P.after(c))), SC.append(Nat, P.before(Con{P.FR{i, True{}, tr}, c}), SC.append(Nat, ST.ids(tl), P.after(Con{P.FR{i, True{}, tr}, c}))), P.ids_l(c, i, tl, tr))
      +ihl = L.subst(List<&2, Nat>, z => {CU.idok(z, NA.gnav(~K, ~cmp, tl, Con{P.FR{i, True{}, tr}, c}, nl, k, h, incl)) == True{} : Bool}, SC.append(Nat, P.before(Con{P.FR{i, True{}, tr}, c}), SC.append(Nat, ST.ids(tl), P.after(Con{P.FR{i, True{}, tr}, c}))), SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{i, tl, tr}), P.after(c))), el, gnav_ok(~K, ~cmp, tl, Con{P.FR{i, True{}, tr}, c}, nl, k, h, incl))
      +ihr = L.subst(List<&2, Nat>, z => {CU.idok(z, NA.gnav(~K, ~cmp, tr, Con{P.FR{i, False{}, tl}, c}, nl, k, h, incl)) == True{} : Bool}, SC.append(Nat, P.before(Con{P.FR{i, False{}, tl}, c}), SC.append(Nat, ST.ids(tr), P.after(Con{P.FR{i, False{}, tl}, c}))), SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{i, tl, tr}), P.after(c))), er, gnav_ok(~K, ~cmp, tr, Con{P.FR{i, False{}, tl}, c}, nl, k, h, incl))
      +hi = L.subst(List<&2, Nat>, z => {CU.idok(z, i) == True{} : Bool}, SC.append(Nat, P.before(Con{P.FR{i, False{}, tl}, c}), SC.append(Nat, ST.ids(tr), P.after(Con{P.FR{i, False{}, tl}, c}))), SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{i, tl, tr}), P.after(c))), er, CX.idok_pre(P.before(Con{P.FR{i, False{}, tl}, c}), SC.append(Nat, ST.ids(tr), P.after(c)), i, CX.idok_suf(P.before(c), SC.append(Nat, ST.ids(tl), Con{i, Nil{}}), i, CX.idok_suf(ST.ids(tl), Con{i, Nil{}}, i, idok_self(i, Nil{})))))
      +hnf = L.subst(List<&2, Nat>, z => {CU.idok(z, ST.fst0(SC.append(Nat, ST.ids(tr), P.after(c)))) == True{} : Bool}, SC.append(Nat, P.before(Con{P.FR{i, False{}, tl}, c}), SC.append(Nat, ST.ids(tr), P.after(Con{P.FR{i, False{}, tl}, c}))), SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{i, tl, tr}), P.after(c))), er, CX.idok_suf(P.before(Con{P.FR{i, False{}, tl}, c}), SC.append(Nat, ST.ids(tr), P.after(c)), ST.fst0(SC.append(Nat, ST.ids(tr), P.after(c))), CU.fst0_ok(SC.append(Nat, ST.ids(tr), P.after(c)))))
      +hnl0 = CX.idok_pre(SC.append(Nat, P.before(c), ST.ids(tl)), P.after(Con{P.FR{i, True{}, tr}, c}), ST.last0(SC.append(Nat, P.before(c), ST.ids(tl))), CU.last0_ok(SC.append(Nat, P.before(c), ST.ids(tl))))
      +hnl1 = L.subst(List<&2, Nat>, z => {CU.idok(z, ST.last0(SC.append(Nat, P.before(c), ST.ids(tl)))) == True{} : Bool}, SC.append(Nat, SC.append(Nat, P.before(c), ST.ids(tl)), P.after(Con{P.FR{i, True{}, tr}, c})), SC.append(Nat, P.before(Con{P.FR{i, True{}, tr}, c}), SC.append(Nat, ST.ids(tl), P.after(Con{P.FR{i, True{}, tr}, c}))), LL.append_assoc(Nat, P.before(c), ST.ids(tl), P.after(Con{P.FR{i, True{}, tr}, c})), hnl0)
      +hnl = L.subst(List<&2, Nat>, z => {CU.idok(z, ST.last0(SC.append(Nat, P.before(c), ST.ids(tl)))) == True{} : Bool}, SC.append(Nat, P.before(Con{P.FR{i, True{}, tr}, c}), SC.append(Nat, ST.ids(tl), P.after(Con{P.FR{i, True{}, tr}, c}))), SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{i, tl, tr}), P.after(c))), el, hnl1)
      pk3_ok(SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{i, tl, tr}), P.after(c))), TR.kc(~K, ~cmp, k, ST.nd(K, nl, i)), NA.gnav(~K, ~cmp, tl, Con{P.FR{i, True{}, tr}, c}, nl, k, h, incl), NA.gnav(~K, ~cmp, tr, Con{P.FR{i, False{}, tl}, c}, nl, k, h, incl), ST.pk(Nat, incl, i, ST.pk(Nat, h, ST.fst0(SC.append(Nat, ST.ids(tr), P.after(c))), ST.last0(SC.append(Nat, P.before(c), ST.ids(tl))))), ihl, ihr, pk_ok(SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{i, tl, tr}), P.after(c))), incl, i, ST.pk(Nat, h, ST.fst0(SC.append(Nat, ST.ids(tr), P.after(c))), ST.last0(SC.append(Nat, P.before(c), ST.ids(tl)))), hi, pk_ok(SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{i, tl, tr}), P.after(c))), h, ST.fst0(SC.append(Nat, ST.ids(tr), P.after(c))), ST.last0(SC.append(Nat, P.before(c), ST.ids(tl))), hnf, hnl)))

# ---- the id a bound starts at ----


def g0_ok(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +hg: {ST.good(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}) == True{} : Bool}, +k: K, +h: Bool, +incl: Bool) -> {CU.ck(~K, nl, NA.gnav(~K, ~cmp, tg, Nil{}, nl, k, h, incl)) == S.key_m(K, V, S.nav(~K, ~V, ~cmp, k, h, incl, ST.ents(~K, ~V, ST.ids(tg), nl, pl))) : Maybe<&2, K>} & {CU.idok(ST.ids(tg), NA.gnav(~K, ~cmp, tg, Nil{}, nl, k, h, incl)) == True{} : Bool}:
  +hk = L.subst(List<&2, Nat>, z => {EN.oks(~K, ~V, z, nl, pl) == True{} : Bool}, ST.ids(tg), SC.append(Nat, ST.ids(tg), Nil{}), Equal.sym(List<&2, Nat>, SC.append(Nat, ST.ids(tg), Nil{}), ST.ids(tg), LL.append_nil(Nat, ST.ids(tg))), EN.oks_tree(~K, ~V, nl, pl, tg, 0n, ST.g_crep(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg), ST.g_cpay(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg)))
  +e1 = Equal.sym(Maybe<&2, K>, S.key_m(K, V, ST.ent(K, V, ST.nd(K, nl, NA.gnav(~K, ~cmp, tg, Nil{}, nl, k, h, incl)), ST.pv(V, pl, NA.gnav(~K, ~cmp, tg, Nil{}, nl, k, h, incl)))), M.node_key(~K, ST.nd(K, nl, NA.gnav(~K, ~cmp, tg, Nil{}, nl, k, h, incl))), NM.gnav_key(~K, ~V, ~cmp, nl, pl, tg, Nil{}, k, h, incl, ST.g_crep(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg), ST.g_cpay(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg), hk))
  +e2 = L.subst(Maybe<&2, M.Entry<K, V>>, z => {S.key_m(K, V, ST.ent(K, V, ST.nd(K, nl, NA.gnav(~K, ~cmp, tg, Nil{}, nl, k, h, incl)), ST.pv(V, pl, NA.gnav(~K, ~cmp, tg, Nil{}, nl, k, h, incl)))) == S.key_m(K, V, z) : Maybe<&2, K>}, ST.ent(K, V, ST.nd(K, nl, NA.gnav(~K, ~cmp, tg, Nil{}, nl, k, h, incl)), ST.pv(V, pl, NA.gnav(~K, ~cmp, tg, Nil{}, nl, k, h, incl))), S.nav(~K, ~V, ~cmp, k, h, incl, ST.ents(~K, ~V, ST.ids(tg), nl, pl)), NM.gnav_ent(~K, ~V, ~cmp, ~o, n, root, lo, hi, free, l, d, nl, pl, tg, fl, k, h, incl, hg), {==})
  +hid = L.subst(List<&2, Nat>, z => {CU.idok(z, NA.gnav(~K, ~cmp, tg, Nil{}, nl, k, h, incl)) == True{} : Bool}, SC.append(Nat, ST.ids(tg), Nil{}), ST.ids(tg), LL.append_nil(Nat, ST.ids(tg)), gnav_ok(~K, ~cmp, tg, Nil{}, nl, k, h, incl))
  (Equal.trans(Maybe<&2, K>, CU.ck(~K, nl, NA.gnav(~K, ~cmp, tg, Nil{}, nl, k, h, incl)), S.key_m(K, V, ST.ent(K, V, ST.nd(K, nl, NA.gnav(~K, ~cmp, tg, Nil{}, nl, k, h, incl)), ST.pv(V, pl, NA.gnav(~K, ~cmp, tg, Nil{}, nl, k, h, incl)))), S.key_m(K, V, S.nav(~K, ~V, ~cmp, k, h, incl, ST.ents(~K, ~V, ST.ids(tg), nl, pl))), e1, e2), hid)

def rs_nav(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +hg: {ST.good(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}) == True{} : Bool}, +k: K, +h: Bool, +incl: Bool, r: {CU.ck(~K, nl, NA.gnav(~K, ~cmp, tg, Nil{}, nl, k, h, incl)) == S.key_m(K, V, S.nav(~K, ~V, ~cmp, k, h, incl, ST.ents(~K, ~V, ST.ids(tg), nl, pl))) : Maybe<&2, K>} & {CU.idok(ST.ids(tg), NA.gnav(~K, ~cmp, tg, Nil{}, nl, k, h, incl)) == True{} : Bool}) -> Sigma<&1, &1, Nat, j => {MI.navigate(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, k, h, incl) == (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, j) : ST.Sh<K, V> & Nat} & ({CU.ck(~K, nl, j) == S.key_m(K, V, S.nav(~K, ~V, ~cmp, k, h, incl, ST.ents(~K, ~V, ST.ids(tg), nl, pl))) : Maybe<&2, K>} & {CU.idok(ST.ids(tg), j) == True{} : Bool})>:
  match r:
    case Tuple{ec, ei}:
      (NA.gnav(~K, ~cmp, tg, Nil{}, nl, k, h, incl), (NM.navigate_m(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, k, h, incl, hg), (ec, ei)))

def rsid(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +hg: {ST.good(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}) == True{} : Bool}, +b: M.Bound<K>, +fw: Bool) -> Sigma<&1, &1, Nat, j => {MI.range_start(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, b, fw) == (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, j) : ST.Sh<K, V> & Nat} & ({CU.ck(~K, nl, j) == S.start(~K, ~V, ~cmp, b, fw, ST.ents(~K, ~V, ST.ids(tg), nl, pl)) : Maybe<&2, K>} & {CU.idok(ST.ids(tg), j) == True{} : Bool})>:
  match b fw:
    case M.Unbounded{} True{}:
      +e = N.eq_from_is_eq(lo, ST.fst0(ST.ids(tg)), ST.g_clo(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg))
      (ST.fst0(ST.ids(tg)), (L.subst(Nat, z => {(ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, lo) == (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, z) : ST.Sh<K, V> & Nat}, lo, ST.fst0(ST.ids(tg)), e, {==}), (Equal.sym(Maybe<&2, K>, S.key_m(K, V, S.head(M.Entry<K, V>, ST.ents(~K, ~V, ST.ids(tg), nl, pl))), CU.ck(~K, nl, ST.fst0(ST.ids(tg))), EN.first_key_eq(~K, ~V, nl, pl, ST.ids(tg), EN.oks_tree(~K, ~V, nl, pl, tg, 0n, ST.g_crep(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg), ST.g_cpay(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg)))), CU.fst0_ok(ST.ids(tg)))))
    case M.Unbounded{} False{}:
      +e = N.eq_from_is_eq(hi, ST.last0(ST.ids(tg)), ST.g_chi(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg))
      (ST.last0(ST.ids(tg)), (L.subst(Nat, z => {(ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, hi) == (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, z) : ST.Sh<K, V> & Nat}, hi, ST.last0(ST.ids(tg)), e, {==}), (Equal.sym(Maybe<&2, K>, S.key_m(K, V, S.last(M.Entry<K, V>, ST.ents(~K, ~V, ST.ids(tg), nl, pl))), CU.ck(~K, nl, ST.last0(ST.ids(tg))), EN.last_key_eq(~K, ~V, nl, pl, ST.ids(tg), EN.oks_tree(~K, ~V, nl, pl, tg, 0n, ST.g_crep(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg), ST.g_cpay(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg)))), CU.last0_ok(ST.ids(tg)))))
    case M.Inclusive{+x} _:
      rs_nav(~K, ~V, ~cmp, ~o, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg, x, fw, True{}, g0_ok(~K, ~V, ~cmp, ~o, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg, x, fw, True{}))
    case M.Exclusive{+x} _:
      rs_nav(~K, ~V, ~cmp, ~o, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg, x, fw, False{}, g0_ok(~K, ~V, ~cmp, ~o, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg, x, fw, False{}))

# ---- the view's cursor ----


def vit_q(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +hg: {ST.good(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}) == True{} : Bool}, +lo2: M.Bound<K>, +hi2: M.Bound<K>, +b: M.Bound<K>, +fw: Bool, +j: Nat, +h1: {MI.range_start(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, b, fw) == (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, j) : ST.Sh<K, V> & Nat}, r: {CU.ck(~K, nl, j) == S.start(~K, ~V, ~cmp, b, fw, ST.ents(~K, ~V, ST.ids(tg), nl, pl)) : Maybe<&2, K>} & {CU.idok(ST.ids(tg), j) == True{} : Bool}) -> Sigma<&1, &1, MI.MCursor<K, V>, c2 => {MI.cursor_started(~K, ~V, ~cmp, lo2, hi2, fw, MI.range_start(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, b, fw)) == c2 : MI.MCursor<K, V>} & ({S.CR{S.TM{l, ST.ents(~K, ~V, ST.ids(tg), nl, pl)}, S.start(~K, ~V, ~cmp, b, fw, ST.ents(~K, ~V, ST.ids(tg), nl, pl)), None{}, lo2, hi2, fw} == CU.cmod(~K, ~V, ~cmp, c2) : S.Cursor<K, V>} & {CU.cgood(~K, ~V, ~cmp, c2) == True{} : Bool})>:
  match r:
    case Tuple{h2, h3}:
      +e1 = L.subst(ST.Sh<K, V> & Nat, z => {MI.cursor_started(~K, ~V, ~cmp, lo2, hi2, fw, MI.range_start(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, b, fw)) == MI.cursor_started(~K, ~V, ~cmp, lo2, hi2, fw, z) : MI.MCursor<K, V>}, MI.range_start(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, b, fw), (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, j), h1, {==})
      +e2 = L.subst(Maybe<&2, K>, z => {S.CR{S.TM{l, ST.ents(~K, ~V, ST.ids(tg), nl, pl)}, z, None{}, lo2, hi2, fw} == S.CR{S.TM{l, ST.ents(~K, ~V, ST.ids(tg), nl, pl)}, CU.ck(~K, nl, j), None{}, lo2, hi2, fw} : S.Cursor<K, V>}, CU.ck(~K, nl, j), S.start(~K, ~V, ~cmp, b, fw, ST.ents(~K, ~V, ST.ids(tg), nl, pl)), h2, {==})
      (MI.MC{ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, j, 0n, lo2, hi2, fw}, (e1, (e2, CU.cg_start(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg, j, h3, fw))))

def vit_r(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +hg: {ST.good(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}) == True{} : Bool}, +lo2: M.Bound<K>, +hi2: M.Bound<K>, +b: M.Bound<K>, +fw: Bool, r: Sigma<&1, &1, Nat, j => {MI.range_start(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, b, fw) == (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, j) : ST.Sh<K, V> & Nat} & ({CU.ck(~K, nl, j) == S.start(~K, ~V, ~cmp, b, fw, ST.ents(~K, ~V, ST.ids(tg), nl, pl)) : Maybe<&2, K>} & {CU.idok(ST.ids(tg), j) == True{} : Bool})>) -> Sigma<&1, &1, MI.MCursor<K, V>, c2 => {MI.cursor_started(~K, ~V, ~cmp, lo2, hi2, fw, MI.range_start(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, b, fw)) == c2 : MI.MCursor<K, V>} & ({S.CR{S.TM{l, ST.ents(~K, ~V, ST.ids(tg), nl, pl)}, S.start(~K, ~V, ~cmp, b, fw, ST.ents(~K, ~V, ST.ids(tg), nl, pl)), None{}, lo2, hi2, fw} == CU.cmod(~K, ~V, ~cmp, c2) : S.Cursor<K, V>} & {CU.cgood(~K, ~V, ~cmp, c2) == True{} : Bool})>:
  match r:
    case Tuple{+j, Tuple{+h1, r2}}:
      vit_q(~K, ~V, ~cmp, ~o, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg, lo2, hi2, b, fw, j, h1, r2)

def vit_m(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +hg: {ST.good(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}) == True{} : Bool}, +lo2: M.Bound<K>, +hi2: M.Bound<K>, +d2: Bool) -> Sigma<&1, &1, MI.MCursor<K, V>, c2 => {MI.view_iterator(~K, ~V, ~cmp, MI.MV{ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, lo2, hi2, d2}) == c2 : MI.MCursor<K, V>} & ({S.view_iterator(~K, ~V, ~cmp, VD.vmod(~K, ~V, ~cmp, MI.MV{ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, lo2, hi2, d2})) == CU.cmod(~K, ~V, ~cmp, c2) : S.Cursor<K, V>} & {CU.cgood(~K, ~V, ~cmp, c2) == True{} : Bool})>:
  match d2:
    case True{}:
      vit_r(~K, ~V, ~cmp, ~o, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg, lo2, hi2, hi2, False{}, rsid(~K, ~V, ~cmp, ~o, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg, hi2, False{}))
    case False{}:
      vit_r(~K, ~V, ~cmp, ~o, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg, lo2, hi2, lo2, True{}, rsid(~K, ~V, ~cmp, ~o, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg, lo2, True{}))

