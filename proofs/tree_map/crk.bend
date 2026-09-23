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
import ./ends.bend as EN
import ./path.bend as P
import ./plug.bend as PG
import ./dj.bend as DJ
import ./ord.bend as OR
import ./navl.bend as NV
import ./cur.bend as CU
import ./reads.bend as RD
import ./spath.bend as SP
import ./agree.bend as AG
import ./find.bend as FI
import ./slot.bend as SL

# Keys present are found: a list split at a member, the entry of a member
# found by its key in sorted entries, and the search for a present key ending
# at a node holding it. (source: tools/generators/tm_hand/crk.src)


def sp_up(+x: Nat, +t: List<&2, Nat>, +j: Nat, r: Sigma<&1, &1, List<&2, Nat>, sa_ => Sigma<&1, &1, List<&2, Nat>, sb_ => {t == SC.append(Nat, sa_, Con{j, sb_}) : List<&2, Nat>}>>) -> Sigma<&1, &1, List<&2, Nat>, sa_ => Sigma<&1, &1, List<&2, Nat>, sb_ => {Con{x, t} == SC.append(Nat, sa_, Con{j, sb_}) : List<&2, Nat>}>>:
  match r:
    case Tuple{+sa, Tuple{+sb, h}}:
      (Con{x, sa}, (sb, L.subst(List<&2, Nat>, z => {Con{x, t} == Con{x, z} : List<&2, Nat>}, t, SC.append(Nat, sa, Con{j, sb}), h, {==})))

# a list at a member
def split_c(+x: Nat, +t: List<&2, Nat>, +j: Nat, +e: Bool, +he: {Nat.is_eq(x, j) == e : Bool}, +hm: {Bool.or(e, HT.memn(j, t)) == True{} : Bool}, ih: @+hmt: {HT.memn(j, t) == True{} : Bool} -> Sigma<&1, &1, List<&2, Nat>, sa_ => Sigma<&1, &1, List<&2, Nat>, sb_ => {t == SC.append(Nat, sa_, Con{j, sb_}) : List<&2, Nat>}>>) -> Sigma<&1, &1, List<&2, Nat>, sa_ => Sigma<&1, &1, List<&2, Nat>, sb_ => {Con{x, t} == SC.append(Nat, sa_, Con{j, sb_}) : List<&2, Nat>}>>:
  match e:
    case True{}:
      L.subst(Nat, z => Sigma<&1, &1, List<&2, Nat>, sa_ => Sigma<&1, &1, List<&2, Nat>, sb_ => {Con{z, t} == SC.append(Nat, sa_, Con{j, sb_}) : List<&2, Nat>}>>, j, x, Equal.sym(Nat, x, j, N.eq_from_is_eq(x, j, he)), (Nil{}, (t, {==})))
    case False{}:
      sp_up(x, t, j, ih(hm))

def split_mem(+xs: List<&2, Nat>, +j: Nat, +hm: {HT.memn(j, xs) == True{} : Bool}) -> Sigma<&1, &1, List<&2, Nat>, sa_ => Sigma<&1, &1, List<&2, Nat>, sb_ => {xs == SC.append(Nat, sa_, Con{j, sb_}) : List<&2, Nat>}>>:
  match xs:
    case Nil{}:
      Empty.absurd(Sigma<&1, &1, List<&2, Nat>, sa_ => Sigma<&1, &1, List<&2, Nat>, sb_ => {Nil{} == SC.append(Nat, sa_, Con{j, sb_}) : List<&2, Nat>}>>, L.false_true(hm))
    case Con{+x, +t}:
      split_c(x, t, j, Nat.is_eq(x, j), {==}, hm, hmt => split_mem(t, j, hmt))


def fi_s(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +xs: List<&2, Nat>, +j: Nat, +hord: {ST.ordered(~K, ~V, ~cmp, ST.ents(~K, ~V, xs, nl, pl)) == True{} : Bool}, +c0: Bool, +x1: Nat, +x2: Nat, +x3: Nat, +k: K, +hx: {ST.nd(K, nl, j) == M.N{c0, x1, x2, x3, k} : M.Node<K>}, +v: V, +hv: {ST.pv(V, pl, j) == Some{v} : Maybe<&2, V>}, r: Sigma<&1, &1, List<&2, Nat>, sa_ => Sigma<&1, &1, List<&2, Nat>, sb_ => {xs == SC.append(Nat, sa_, Con{j, sb_}) : List<&2, Nat>}>>) -> {S.find_e(~K, ~V, ~cmp, k, ST.ents(~K, ~V, xs, nl, pl)) == Some{M.Entry{k, v}} : Maybe<&2, M.Entry<K, V>>}:
  match r:
    case Tuple{+sa, Tuple{+sb, h}}:
      +eent = L.subst(Maybe<&2, V>, z => {ST.ent(K, V, ST.nd(K, nl, j), ST.pv(V, pl, j)) == ST.ent(K, V, M.N{c0, x1, x2, x3, k}, z) : Maybe<&2, M.Entry<K, V>>}, ST.pv(V, pl, j), Some{v}, hv, L.subst(M.Node<K>, z => {ST.ent(K, V, ST.nd(K, nl, j), ST.pv(V, pl, j)) == ST.ent(K, V, z, ST.pv(V, pl, j)) : Maybe<&2, M.Entry<K, V>>}, ST.nd(K, nl, j), M.N{c0, x1, x2, x3, k}, hx, {==}))
      +hE = Equal.trans(List<&2, M.Entry<K, V>>, ST.ents(~K, ~V, xs, nl, pl), ST.ents(~K, ~V, SC.append(Nat, sa, Con{j, sb}), nl, pl), SC.append(M.Entry<K, V>, ST.ents(~K, ~V, sa, nl, pl), Con{M.Entry{k, v}, ST.ents(~K, ~V, sb, nl, pl)}), L.subst(List<&2, Nat>, z => {ST.ents(~K, ~V, xs, nl, pl) == ST.ents(~K, ~V, z, nl, pl) : List<&2, M.Entry<K, V>>}, xs, SC.append(Nat, sa, Con{j, sb}), h, {==}), Equal.trans(List<&2, M.Entry<K, V>>, ST.ents(~K, ~V, SC.append(Nat, sa, Con{j, sb}), nl, pl), SC.append(M.Entry<K, V>, ST.ents(~K, ~V, sa, nl, pl), ST.cons_m(M.Entry<K, V>, ST.ent(K, V, ST.nd(K, nl, j), ST.pv(V, pl, j)), ST.ents(~K, ~V, sb, nl, pl))), SC.append(M.Entry<K, V>, ST.ents(~K, ~V, sa, nl, pl), Con{M.Entry{k, v}, ST.ents(~K, ~V, sb, nl, pl)}), FI.ents_app(~K, ~V, sa, Con{j, sb}, nl, pl), L.subst(Maybe<&2, M.Entry<K, V>>, z => {SC.append(M.Entry<K, V>, ST.ents(~K, ~V, sa, nl, pl), ST.cons_m(M.Entry<K, V>, ST.ent(K, V, ST.nd(K, nl, j), ST.pv(V, pl, j)), ST.ents(~K, ~V, sb, nl, pl))) == SC.append(M.Entry<K, V>, ST.ents(~K, ~V, sa, nl, pl), ST.cons_m(M.Entry<K, V>, z, ST.ents(~K, ~V, sb, nl, pl))) : List<&2, M.Entry<K, V>>}, ST.ent(K, V, ST.nd(K, nl, j), ST.pv(V, pl, j)), Some{M.Entry{k, v}}, eent, {==})))
      Equal.trans(Maybe<&2, M.Entry<K, V>>, S.find_e(~K, ~V, ~cmp, k, ST.ents(~K, ~V, xs, nl, pl)), S.find_e(~K, ~V, ~cmp, k, SC.append(M.Entry<K, V>, ST.ents(~K, ~V, sa, nl, pl), Con{M.Entry{k, v}, ST.ents(~K, ~V, sb, nl, pl)})), Some{M.Entry{k, v}}, L.subst(List<&2, M.Entry<K, V>>, z => {S.find_e(~K, ~V, ~cmp, k, ST.ents(~K, ~V, xs, nl, pl)) == S.find_e(~K, ~V, ~cmp, k, z) : Maybe<&2, M.Entry<K, V>>}, ST.ents(~K, ~V, xs, nl, pl), SC.append(M.Entry<K, V>, ST.ents(~K, ~V, sa, nl, pl), Con{M.Entry{k, v}, ST.ents(~K, ~V, sb, nl, pl)}), hE, {==}), OR.find_mid_eq(~K, ~V, ~cmp, ~o, k, ST.ents(~K, ~V, sa, nl, pl), M.Entry{k, v}, ST.ents(~K, ~V, sb, nl, pl), L.subst(List<&2, M.Entry<K, V>>, z => {ST.ordered(~K, ~V, ~cmp, z) == True{} : Bool}, ST.ents(~K, ~V, xs, nl, pl), SC.append(M.Entry<K, V>, ST.ents(~K, ~V, sa, nl, pl), Con{M.Entry{k, v}, ST.ents(~K, ~V, sb, nl, pl)}), hE, hord), O.refl(~K, ~cmp, ~o, k)))

# the entry of a member, found by its key
def find_in(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +xs: List<&2, Nat>, +j: Nat, +hm: {HT.memn(j, xs) == True{} : Bool}, +hord: {ST.ordered(~K, ~V, ~cmp, ST.ents(~K, ~V, xs, nl, pl)) == True{} : Bool}, +c0: Bool, +x1: Nat, +x2: Nat, +x3: Nat, +k: K, +hx: {ST.nd(K, nl, j) == M.N{c0, x1, x2, x3, k} : M.Node<K>}, +v: V, +hv: {ST.pv(V, pl, j) == Some{v} : Maybe<&2, V>}) -> {S.find_e(~K, ~V, ~cmp, k, ST.ents(~K, ~V, xs, nl, pl)) == Some{M.Entry{k, v}} : Maybe<&2, M.Entry<K, V>>}:
  fi_s(~K, ~V, ~cmp, ~o, nl, pl, xs, j, hord, c0, x1, x2, x3, k, hx, v, hv, split_mem(xs, j, hm))

# ---- a present key: the search ends at a node holding it ----


def fk_x(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +i: Nat, +a: ST.Tr, +b: ST.Tr, +k: K, +c: List<&2, P.Fr>, +hwh: {SC.append(Nat, ST.ids(tg), Nil{}) == SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{i, a, b}), P.after(c))) : List<&2, Nat>}, +hr: {ST.rep(~K, ST.TN{i, a, b}, P.top(c), nl) == True{} : Bool}, +x: M.Node<K>, +hx: {ST.nd(K, nl, i) == x : M.Node<K>}, +hq: {S.is_eq(TR.kc(~K, ~cmp, k, x)) == True{} : Bool}) -> {CU.ck(~K, nl, ST.rid(ST.TN{i, a, b})) == Some{k} : Maybe<&2, K>} & {CU.idok(ST.ids(tg), ST.rid(ST.TN{i, a, b})) == True{} : Bool}:
  match x:
    case M.Free{f}:
      Empty.absurd({CU.ck(~K, nl, ST.rid(ST.TN{i, a, b})) == Some{k} : Maybe<&2, K>} & {CU.idok(ST.ids(tg), ST.rid(ST.TN{i, a, b})) == True{} : Bool}, L.false_true(L.subst(M.Node<K>, z => {ST.is_node(K, z, ST.rid(a), ST.rid(b), P.top(c)) == True{} : Bool}, ST.nd(K, nl, i), M.Free{f}, hx, TR.rep_node(~K, i, a, b, P.top(c), nl, hr))))
    case M.N{+c0, +x1, +x2, +x3, +key}:
      +ek = O.antisym(~K, ~cmp, o, k, key, AG.iseq_eq(cmp(k, key), hq))
      +eck = Equal.trans(Maybe<&2, K>, CU.ck(~K, nl, i), Some{key}, Some{k}, L.subst(M.Node<K>, z => {CU.ck(~K, nl, i) == M.node_key(~K, z) : Maybe<&2, K>}, ST.nd(K, nl, i), M.N{c0, x1, x2, x3, key}, hx, {==}), L.subst(K, z => {Some{key} == Some{z} : Maybe<&2, K>}, key, k, Equal.sym(K, k, key, ek), {==}))
      +hm0 = DJ.mem_r(i, P.before(c), SC.append(Nat, ST.ids(ST.TN{i, a, b}), P.after(c)), DJ.mem_l(i, ST.ids(ST.TN{i, a, b}), P.after(c), P.mem_root(i, a, b)))
      +hm = L.subst(List<&2, Nat>, z => {HT.memn(i, z) == True{} : Bool}, SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{i, a, b}), P.after(c))), ST.ids(tg), Equal.trans(List<&2, Nat>, SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{i, a, b}), P.after(c))), SC.append(Nat, ST.ids(tg), Nil{}), ST.ids(tg), Equal.sym(List<&2, Nat>, SC.append(Nat, ST.ids(tg), Nil{}), SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{i, a, b}), P.after(c))), hwh), LL.append_nil(Nat, ST.ids(tg))), hm0)
      (eck, CU.or_r(Nat.is_eq(i, 0n), HT.memn(i, ST.ids(tg)), hm))

def fk_t(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +t: ST.Tr, +k: K, +w: V, +hpv: {ST.pv(V, pl, ST.rid(t)) == Some{w} : Maybe<&2, V>}, +c: List<&2, P.Fr>, +hwh: {SC.append(Nat, ST.ids(tg), Nil{}) == SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(t), P.after(c))) : List<&2, Nat>}, +hr: {ST.rep(~K, t, P.top(c), nl) == True{} : Bool}, +hfin: {SP.fin(~K, ~cmp, k, t, nl) == True{} : Bool}) -> {CU.ck(~K, nl, ST.rid(t)) == Some{k} : Maybe<&2, K>} & {CU.idok(ST.ids(tg), ST.rid(t)) == True{} : Bool}:
  match t:
    case ST.TE{}:
      Empty.absurd({CU.ck(~K, nl, ST.rid(ST.TE{})) == Some{k} : Maybe<&2, K>} & {CU.idok(ST.ids(tg), ST.rid(ST.TE{})) == True{} : Bool}, L.none_some(V, w, hpv))
    case ST.TN{+i, +a, +b}:
      fk_x(~K, ~V, ~cmp, ~o, n, root, lo, hi, free, l, d, nl, pl, tg, fl, i, a, b, k, c, hwh, hr, ST.nd(K, nl, i), {==}, hfin)


def fk_c2(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +k: K, +w: V, +c: List<&2, P.Fr>, +t: ST.Tr, +hts: {TR.tsearch(~K, ~V, ~cmp, tg, nl, k, 0n, False{}) == M.Search{ST.rid(t), P.top(c), SP.dir(c)} : M.Search}, +hpv0: {ST.pv(V, pl, FI.sfound(TR.tsearch(~K, ~V, ~cmp, tg, nl, k, 0n, False{}))) == Some{w} : Maybe<&2, V>}, +hwh: {SC.append(Nat, ST.ids(tg), Nil{}) == SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(t), P.after(c))) : List<&2, Nat>}, +hr: {ST.rep(~K, t, P.top(c), nl) == True{} : Bool}, r2: {OR.gtall(~K, ~V, ~cmp, k, ST.ents(~K, ~V, P.after(c), nl, pl)) == True{} : Bool} & {SP.fin(~K, ~cmp, k, t, nl) == True{} : Bool}) -> {CU.ck(~K, nl, FI.sfound(TR.tsearch(~K, ~V, ~cmp, tg, nl, k, 0n, False{}))) == Some{k} : Maybe<&2, K>} & {CU.idok(ST.ids(tg), FI.sfound(TR.tsearch(~K, ~V, ~cmp, tg, nl, k, 0n, False{}))) == True{} : Bool}:
  match r2:
    case Tuple{ha, hfin}:
      %Equal.sym(M.Search, TR.tsearch(~K, ~V, ~cmp, tg, nl, k, 0n, False{}), M.Search{ST.rid(t), P.top(c), SP.dir(c)}, hts) : {CU.ck(~K, nl, FI.sfound(_)) == Some{k} : Maybe<&2, K>} & {CU.idok(ST.ids(tg), FI.sfound(_)) == True{} : Bool}
      fk_t(~K, ~V, ~cmp, ~o, n, root, lo, hi, free, l, d, nl, pl, tg, fl, t, k, w, L.subst(M.Search, z => {ST.pv(V, pl, FI.sfound(z)) == Some{w} : Maybe<&2, V>}, TR.tsearch(~K, ~V, ~cmp, tg, nl, k, 0n, False{}), M.Search{ST.rid(t), P.top(c), SP.dir(c)}, hts, hpv0), c, hwh, hr, hfin)

def fk_c(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +k: K, +w: V, +hpv0: {ST.pv(V, pl, FI.sfound(TR.tsearch(~K, ~V, ~cmp, tg, nl, k, 0n, False{}))) == Some{w} : Maybe<&2, V>}, +c: List<&2, P.Fr>, +t: ST.Tr, r: {TR.tsearch(~K, ~V, ~cmp, tg, nl, k, 0n, False{}) == M.Search{ST.rid(t), P.top(c), SP.dir(c)} : M.Search} & ({SC.append(Nat, ST.ids(tg), Nil{}) == SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(t), P.after(c))) : List<&2, Nat>} & ({tg == PG.plug(c, t) : ST.Tr} & ({ST.rep(~K, t, P.top(c), nl) == True{} : Bool} & ({P.ctxok(~K, c, ST.rid(t), nl) == True{} : Bool} & ({OR.ltall(~K, ~V, ~cmp, k, ST.ents(~K, ~V, P.before(c), nl, pl)) == True{} : Bool} & ({OR.gtall(~K, ~V, ~cmp, k, ST.ents(~K, ~V, P.after(c), nl, pl)) == True{} : Bool} & {SP.fin(~K, ~cmp, k, t, nl) == True{} : Bool}))))))) -> {CU.ck(~K, nl, FI.sfound(TR.tsearch(~K, ~V, ~cmp, tg, nl, k, 0n, False{}))) == Some{k} : Maybe<&2, K>} & {CU.idok(ST.ids(tg), FI.sfound(TR.tsearch(~K, ~V, ~cmp, tg, nl, k, 0n, False{}))) == True{} : Bool}:
  match r:
    case Tuple{hts, Tuple{hwh, Tuple{hplug, Tuple{hr, Tuple{hokc, Tuple{hb, r2}}}}}}:
      fk_c2(~K, ~V, ~cmp, ~o, n, root, lo, hi, free, l, d, nl, pl, tg, fl, k, w, c, t, hts, hpv0, hwh, hr, r2)

def fk_sp(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +k: K, +w: V, +hpv0: {ST.pv(V, pl, FI.sfound(TR.tsearch(~K, ~V, ~cmp, tg, nl, k, 0n, False{}))) == Some{w} : Maybe<&2, V>}, sp: Sigma<&1, &1, List<&2, P.Fr>, c => Sigma<&1, &1, ST.Tr, t => {TR.tsearch(~K, ~V, ~cmp, tg, nl, k, 0n, False{}) == M.Search{ST.rid(t), P.top(c), SP.dir(c)} : M.Search} & ({SC.append(Nat, ST.ids(tg), Nil{}) == SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(t), P.after(c))) : List<&2, Nat>} & ({tg == PG.plug(c, t) : ST.Tr} & ({ST.rep(~K, t, P.top(c), nl) == True{} : Bool} & ({P.ctxok(~K, c, ST.rid(t), nl) == True{} : Bool} & ({OR.ltall(~K, ~V, ~cmp, k, ST.ents(~K, ~V, P.before(c), nl, pl)) == True{} : Bool} & ({OR.gtall(~K, ~V, ~cmp, k, ST.ents(~K, ~V, P.after(c), nl, pl)) == True{} : Bool} & {SP.fin(~K, ~cmp, k, t, nl) == True{} : Bool}))))))>>) -> {CU.ck(~K, nl, FI.sfound(TR.tsearch(~K, ~V, ~cmp, tg, nl, k, 0n, False{}))) == Some{k} : Maybe<&2, K>} & {CU.idok(ST.ids(tg), FI.sfound(TR.tsearch(~K, ~V, ~cmp, tg, nl, k, 0n, False{}))) == True{} : Bool}:
  match sp:
    case Tuple{+c, Tuple{+t, r}}:
      fk_c(~K, ~V, ~cmp, ~o, n, root, lo, hi, free, l, d, nl, pl, tg, fl, k, w, hpv0, c, t, r)


# a present key: the search's id holds it and is in the tree
def fkey(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +hg: {ST.goodF(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl) == True{} : Bool}, +k: K, +w: V, +hf: {S.find(~K, ~V, ~cmp, k, ST.ents(~K, ~V, ST.ids(tg), nl, pl)) == Some{w} : Maybe<&2, V>}) -> {CU.ck(~K, nl, FI.sfound(TR.tsearch(~K, ~V, ~cmp, tg, nl, k, 0n, False{}))) == Some{k} : Maybe<&2, K>} & {CU.idok(ST.ids(tg), FI.sfound(TR.tsearch(~K, ~V, ~cmp, tg, nl, k, 0n, False{}))) == True{} : Bool}:
  +ean = LL.append_nil(Nat, ST.ids(tg))
  +hk1 = EN.oks_tree(~K, ~V, nl, pl, tg, 0n, ST.g_crep(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg), ST.g_cpay(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg))
  +hk0 = L.subst(List<&2, Nat>, z => {EN.oks(~K, ~V, z, nl, pl) == True{} : Bool}, ST.ids(tg), SC.append(Nat, ST.ids(tg), Nil{}), Equal.sym(List<&2, Nat>, SC.append(Nat, ST.ids(tg), Nil{}), ST.ids(tg), ean), hk1)
  +ho0 = L.subst(List<&2, Nat>, z => {ST.ordered(~K, ~V, ~cmp, ST.ents(~K, ~V, z, nl, pl)) == True{} : Bool}, ST.ids(tg), SC.append(Nat, ST.ids(tg), Nil{}), Equal.sym(List<&2, Nat>, SC.append(Nat, ST.ids(tg), Nil{}), ST.ids(tg), ean), ST.g_cord(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg))
  +hpv0 = Equal.trans(Maybe<&2, V>, ST.pv(V, pl, FI.sfound(TR.tsearch(~K, ~V, ~cmp, tg, nl, k, 0n, False{}))), S.find(~K, ~V, ~cmp, k, ST.ents(~K, ~V, ST.ids(tg), nl, pl)), Some{w}, FI.tfind(~K, ~V, ~cmp, ~o, nl, pl, tg, 0n, False{}, k, ST.g_crep(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg), ST.g_cpay(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg), ST.g_cord(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg)), hf)
  fk_sp(~K, ~V, ~cmp, ~o, n, root, lo, hi, free, l, d, nl, pl, tg, fl, k, w, hpv0, SP.spath(~K, ~V, ~cmp, ~o, nl, pl, tg, Nil{}, k, ST.g_crep(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg), {==}, ST.g_cpay(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg), ho0, hk0, {==}, {==}))
