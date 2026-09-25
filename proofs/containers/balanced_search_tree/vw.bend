import Base
import ../../lib/logic.bend as L
import ../../lib/order.bend as O
import ../../../spec/lib/common.bend as SC
import ../../../spec/containers/balanced_search_tree/main.bend as S
import ../../../src/containers/balanced_search_tree.bend as M
import ./state.bend as ST
import ./mirror.bend as MI
import ./sim.bend as SM
import ./ok.bend as OK
import ./reads.bend as RD
import ./putm.bend as PM
import ./rmv.bend as RV
import ./cur.bend as CU
import ./vdef.bend as VD

# The implementation's views refine the specification's: a view of a good
# shadow is realized by the implementation's view and modelled by the
# specification's over the shadow's model; every view operation gives the
# real view (and answer) of a good view whose model is the specification's
# result. (source: tools/generators/tm_hand/vw.src)


# ---- making views ----

def head_map_ok(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +sh: ST.Sh<K, V>, +hg: {ST.good(~K, ~V, ~cmp, sh) == True{} : Bool}, +up: M.Bound<K>) -> VD.VOK(~K, ~V, ~cmp, S.head_map(K, V, ST.model(~K, ~V, ~cmp, sh), up), M.head_map(~K, ~V, ~cmp, ST.real(~K, ~V, ~cmp, sh), up)):
  (MI.MV{sh, M.Unbounded{}, up, False{}}, (SM.head_map_s(~K, ~V, ~cmp, sh, up, OK.dg_good(~K, ~V, ~cmp, sh, hg)), ({==}, hg)))

def tail_map_ok(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +sh: ST.Sh<K, V>, +hg: {ST.good(~K, ~V, ~cmp, sh) == True{} : Bool}, +lw: M.Bound<K>) -> VD.VOK(~K, ~V, ~cmp, S.tail_map(K, V, ST.model(~K, ~V, ~cmp, sh), lw), M.tail_map(~K, ~V, ~cmp, ST.real(~K, ~V, ~cmp, sh), lw)):
  (MI.MV{sh, lw, M.Unbounded{}, False{}}, (SM.tail_map_s(~K, ~V, ~cmp, sh, lw, OK.dg_good(~K, ~V, ~cmp, sh, hg)), ({==}, hg)))

def descending_map_ok(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +sh: ST.Sh<K, V>, +hg: {ST.good(~K, ~V, ~cmp, sh) == True{} : Bool}) -> VD.VOK(~K, ~V, ~cmp, S.descending_map(K, V, ST.model(~K, ~V, ~cmp, sh)), M.descending_map(~K, ~V, ~cmp, ST.real(~K, ~V, ~cmp, sh))):
  (MI.MV{sh, M.Unbounded{}, M.Unbounded{}, True{}}, (SM.descending_map_s(~K, ~V, ~cmp, sh, OK.dg_good(~K, ~V, ~cmp, sh, hg)), ({==}, hg)))

def view_reverse_ok(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +w: MI.MView<K, V>, +hw: {VD.vgood(~K, ~V, ~cmp, w) == True{} : Bool}) -> VD.VOK(~K, ~V, ~cmp, S.view_reverse(K, V, VD.vmod(~K, ~V, ~cmp, w)), M.view_reverse(~K, ~V, ~cmp, MI.rv(~K, ~V, ~cmp, w))):
  match w:
    case MI.MV{+s, +lo2, +hi2, +d2}:
      (MI.MV{s, lo2, hi2, Bool.not(d2)}, (SM.view_reverse_s(~K, ~V, ~cmp, MI.MV{s, lo2, hi2, d2}, OK.dg_good(~K, ~V, ~cmp, s, hw)), ({==}, hw)))


def view_finish_ok(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +w: MI.MView<K, V>, +hw: {VD.vgood(~K, ~V, ~cmp, w) == True{} : Bool}) -> Sigma<&1, &1, ST.Sh<K, V>, s2 => {M.view_finish(~K, ~V, ~cmp, MI.rv(~K, ~V, ~cmp, w)) == ST.real(~K, ~V, ~cmp, s2) : M.TreeMap<K, V, cmp>} & ({S.view_finish(K, V, VD.vmod(~K, ~V, ~cmp, w)) == ST.model(~K, ~V, ~cmp, s2) : S.Model<K, V>} & {ST.good(~K, ~V, ~cmp, s2) == True{} : Bool})>:
  match w:
    case MI.MV{+s, +lo2, +hi2, +d2}:
      (s, (SM.view_finish_s(~K, ~V, ~cmp, MI.MV{s, lo2, hi2, d2}, OK.dg_good(~K, ~V, ~cmp, s, hw)), ({==}, hw)))

# ---- sub_map: the bounds checked ----

def rmod(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, r: Result<&1, &1, MI.MInvalid<K, V>, MI.MView<K, V>>) -> Result<&1, &1, S.InvalidView<K, V>, S.View<K, V>>:
  match r:
    case Done{w}:
      Done{VD.vmod(~K, ~V, ~cmp, w)}
    case Fail{MI.MI{s, e}}:
      Fail{S.IV{ST.model(~K, ~V, ~cmp, s), e}}

def rgood(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, r: Result<&1, &1, MI.MInvalid<K, V>, MI.MView<K, V>>) -> Bool:
  match r:
    case Done{w}:
      VD.vgood(~K, ~V, ~cmp, w)
    case Fail{MI.MI{s, e}}:
      ST.good(~K, ~V, ~cmp, s)

def ROK(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, sp: Result<&1, &1, S.InvalidView<K, V>, S.View<K, V>>, r: Result<&1, &1, M.InvalidView<K, V, cmp>, M.View<K, V, cmp>>) -> Type:
  Sigma<&1, &1, Result<&1, &1, MI.MInvalid<K, V>, MI.MView<K, V>>, x => {r == MI.rr(~K, ~V, ~cmp, x) : Result<&1, &1, M.InvalidView<K, V, cmp>, M.View<K, V, cmp>>} & ({sp == rmod(~K, ~V, ~cmp, x) : Result<&1, &1, S.InvalidView<K, V>, S.View<K, V>>} & {rgood(~K, ~V, ~cmp, x) == True{} : Bool})>

def bv_eq(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +a: M.Bound<K>, +b: M.Bound<K>) -> {M.bounds_valid(~K, ~V, ~cmp, a, b) == S.bounds_valid(~K, ~cmp, a, b) : Bool}:
  match a b:
    case M.Unbounded{} M.Unbounded{}:
      {==}
    case M.Unbounded{} M.Inclusive{y}:
      {==}
    case M.Unbounded{} M.Exclusive{y}:
      {==}
    case M.Inclusive{x} M.Unbounded{}:
      {==}
    case M.Exclusive{x} M.Unbounded{}:
      {==}
    case M.Inclusive{+x} M.Inclusive{+y}:
      CU.oo_eq(cmp(x, y), True{})
    case M.Inclusive{+x} M.Exclusive{+y}:
      CU.oo_eq(cmp(x, y), True{})
    case M.Exclusive{+x} M.Inclusive{+y}:
      CU.oo_eq(cmp(x, y), True{})
    case M.Exclusive{+x} M.Exclusive{+y}:
      CU.oo_eq(cmp(x, y), True{})

def sub_b(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +sh: ST.Sh<K, V>, +hg: {ST.good(~K, ~V, ~cmp, sh) == True{} : Bool}, +lw: M.Bound<K>, +up: M.Bound<K>, +b: Bool) -> {S.view_checked(K, V, ST.model(~K, ~V, ~cmp, sh), lw, up, b) == rmod(~K, ~V, ~cmp, MI.view_checked(~K, ~V, ~cmp, sh, lw, up, False{}, b)) : Result<&1, &1, S.InvalidView<K, V>, S.View<K, V>>} & {rgood(~K, ~V, ~cmp, MI.view_checked(~K, ~V, ~cmp, sh, lw, up, False{}, b)) == True{} : Bool}:
  match b:
    case True{}:
      ({==}, hg)
    case False{}:
      ({==}, hg)

def sub_map_ok(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +sh: ST.Sh<K, V>, +hg: {ST.good(~K, ~V, ~cmp, sh) == True{} : Bool}, +lw: M.Bound<K>, +up: M.Bound<K>) -> ROK(~K, ~V, ~cmp, S.sub_map(~K, ~V, ~cmp, ST.model(~K, ~V, ~cmp, sh), lw, up), M.sub_map(~K, ~V, ~cmp, ST.real(~K, ~V, ~cmp, sh), lw, up)):
  %bv_eq(~K, ~V, ~cmp, lw, up) : ROK(~K, ~V, ~cmp, S.view_checked(K, V, ST.model(~K, ~V, ~cmp, sh), lw, up, _), M.sub_map(~K, ~V, ~cmp, ST.real(~K, ~V, ~cmp, sh), lw, up))
  (MI.sub_map(~K, ~V, ~cmp, sh, lw, up), (SM.sub_map_s(~K, ~V, ~cmp, sh, lw, up, OK.dg_good(~K, ~V, ~cmp, sh, hg)), sub_b(~K, ~V, ~cmp, sh, hg, lw, up, M.bounds_valid(~K, ~V, ~cmp, lw, up))))

# ---- get and contains_key: the key in range, then the map's ----


def vget_b(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +hg: {ST.good(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}) == True{} : Bool}, +lo2: M.Bound<K>, +hi2: M.Bound<K>, +d2: Bool, +k: K, +b: Bool) -> {MI.view_get_checked(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, k, lo2, hi2, d2, b) == (MI.MV{ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, lo2, hi2, d2}, S.pick(Maybe<&2, V>, b, S.find(~K, ~V, ~cmp, k, ST.ents(~K, ~V, ST.ids(tg), nl, pl)), None{})) : MI.MView<K, V> & Maybe<&2, V>}:
  match b:
    case True{}:
      %Equal.sym(ST.Sh<K, V> & Maybe<&2, V>, MI.get(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, k), (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, S.find(~K, ~V, ~cmp, k, ST.ents(~K, ~V, ST.ids(tg), nl, pl))), RD.get_m(~K, ~V, ~cmp, ~o, n, root, lo, hi, free, l, d, nl, pl, tg, fl, k, hg)) : {MI.view_value(~K, ~V, ~cmp, lo2, hi2, d2, _) == (MI.MV{ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, lo2, hi2, d2}, S.pick(Maybe<&2, V>, True{}, S.find(~K, ~V, ~cmp, k, ST.ents(~K, ~V, ST.ids(tg), nl, pl)), None{})) : MI.MView<K, V> & Maybe<&2, V>}
      {==}
    case False{}:
      {==}

def vget_m(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +hg: {ST.good(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}) == True{} : Bool}, +lo2: M.Bound<K>, +hi2: M.Bound<K>, +d2: Bool, +k: K) -> {MI.view_get(~K, ~V, ~cmp, MI.MV{ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, lo2, hi2, d2}, k) == (MI.MV{ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, lo2, hi2, d2}, S.pick(Maybe<&2, V>, S.in_range(~K, ~cmp, k, lo2, hi2), S.find(~K, ~V, ~cmp, k, ST.ents(~K, ~V, ST.ids(tg), nl, pl)), None{})) : MI.MView<K, V> & Maybe<&2, V>}:
  %Equal.sym(Bool, M.in_range(~K, ~V, ~cmp, k, lo2, hi2), S.in_range(~K, ~cmp, k, lo2, hi2), CU.inr_eq(~K, ~V, ~cmp, k, lo2, hi2)) : {MI.view_get_checked(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, k, lo2, hi2, d2, _) == (MI.MV{ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, lo2, hi2, d2}, S.pick(Maybe<&2, V>, S.in_range(~K, ~cmp, k, lo2, hi2), S.find(~K, ~V, ~cmp, k, ST.ents(~K, ~V, ST.ids(tg), nl, pl)), None{})) : MI.MView<K, V> & Maybe<&2, V>}
  vget_b(~K, ~V, ~cmp, ~o, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg, lo2, hi2, d2, k, S.in_range(~K, ~cmp, k, lo2, hi2))

def view_get_ok(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +w: MI.MView<K, V>, +hw: {VD.vgood(~K, ~V, ~cmp, w) == True{} : Bool}, +k: K) -> VD.VPOK(~K, ~V, ~cmp, Maybe<&2, V>, S.view_get(~K, ~V, ~cmp, VD.vmod(~K, ~V, ~cmp, w), k), M.view_get(~K, ~V, ~cmp, MI.rv(~K, ~V, ~cmp, w), k)):
  match w:
    case MI.MV{ST.SH{+n, +root, +lo, +hi, +free, +l, +d, +nl, +pl, +tg, +fl}, +lo2, +hi2, +d2}:
      VD.vm_pok(~K, ~V, ~cmp, Maybe<&2, V>, S.view_get(~K, ~V, ~cmp, VD.vmod(~K, ~V, ~cmp, MI.MV{ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, lo2, hi2, d2}), k), MI.view_get(~K, ~V, ~cmp, MI.MV{ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, lo2, hi2, d2}, k), M.view_get(~K, ~V, ~cmp, MI.rv(~K, ~V, ~cmp, MI.MV{ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, lo2, hi2, d2}), k), SM.view_get_s(~K, ~V, ~cmp, MI.MV{ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, lo2, hi2, d2}, k, OK.dg_good(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, hw)), VD.vm_exact(~K, ~V, ~cmp, Maybe<&2, V>, S.view_get(~K, ~V, ~cmp, VD.vmod(~K, ~V, ~cmp, MI.MV{ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, lo2, hi2, d2}), k), MI.view_get(~K, ~V, ~cmp, MI.MV{ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, lo2, hi2, d2}, k), MI.MV{ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, lo2, hi2, d2}, S.pick(Maybe<&2, V>, S.in_range(~K, ~cmp, k, lo2, hi2), S.find(~K, ~V, ~cmp, k, ST.ents(~K, ~V, ST.ids(tg), nl, pl)), None{}), vget_m(~K, ~V, ~cmp, ~o, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hw, lo2, hi2, d2, k), {==}, hw))

def vcv_eq(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +w2: MI.MView<K, V>, +o: Maybe<&2, V>) -> {MI.view_contains_value(~K, ~V, ~cmp, (w2, o)) == (w2, S.is_some(V, o)) : MI.MView<K, V> & Bool}:
  match o:
    case None{}:
      {==}
    case Some{x}:
      {==}

def view_contains_key_ok(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +w: MI.MView<K, V>, +hw: {VD.vgood(~K, ~V, ~cmp, w) == True{} : Bool}, +k: K) -> VD.VPOK(~K, ~V, ~cmp, Bool, S.view_contains_key(~K, ~V, ~cmp, VD.vmod(~K, ~V, ~cmp, w), k), M.view_contains_key(~K, ~V, ~cmp, MI.rv(~K, ~V, ~cmp, w), k)):
  match w:
    case MI.MV{ST.SH{+n, +root, +lo, +hi, +free, +l, +d, +nl, +pl, +tg, +fl}, +lo2, +hi2, +d2}:
      +hm = Equal.trans(MI.MView<K, V> & Bool, MI.view_contains_key(~K, ~V, ~cmp, MI.MV{ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, lo2, hi2, d2}, k), MI.view_contains_value(~K, ~V, ~cmp, (MI.MV{ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, lo2, hi2, d2}, S.pick(Maybe<&2, V>, S.in_range(~K, ~cmp, k, lo2, hi2), S.find(~K, ~V, ~cmp, k, ST.ents(~K, ~V, ST.ids(tg), nl, pl)), None{}))), (MI.MV{ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, lo2, hi2, d2}, S.is_some(V, S.pick(Maybe<&2, V>, S.in_range(~K, ~cmp, k, lo2, hi2), S.find(~K, ~V, ~cmp, k, ST.ents(~K, ~V, ST.ids(tg), nl, pl)), None{}))), L.subst(MI.MView<K, V> & Maybe<&2, V>, z => {MI.view_contains_value(~K, ~V, ~cmp, MI.view_get(~K, ~V, ~cmp, MI.MV{ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, lo2, hi2, d2}, k)) == MI.view_contains_value(~K, ~V, ~cmp, z) : MI.MView<K, V> & Bool}, MI.view_get(~K, ~V, ~cmp, MI.MV{ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, lo2, hi2, d2}, k), (MI.MV{ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, lo2, hi2, d2}, S.pick(Maybe<&2, V>, S.in_range(~K, ~cmp, k, lo2, hi2), S.find(~K, ~V, ~cmp, k, ST.ents(~K, ~V, ST.ids(tg), nl, pl)), None{})), vget_m(~K, ~V, ~cmp, ~o, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hw, lo2, hi2, d2, k), {==}), vcv_eq(~K, ~V, ~cmp, MI.MV{ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, lo2, hi2, d2}, S.pick(Maybe<&2, V>, S.in_range(~K, ~cmp, k, lo2, hi2), S.find(~K, ~V, ~cmp, k, ST.ents(~K, ~V, ST.ids(tg), nl, pl)), None{})))
      VD.vm_pok(~K, ~V, ~cmp, Bool, S.view_contains_key(~K, ~V, ~cmp, VD.vmod(~K, ~V, ~cmp, MI.MV{ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, lo2, hi2, d2}), k), MI.view_contains_key(~K, ~V, ~cmp, MI.MV{ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, lo2, hi2, d2}, k), M.view_contains_key(~K, ~V, ~cmp, MI.rv(~K, ~V, ~cmp, MI.MV{ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, lo2, hi2, d2}), k), SM.view_contains_key_s(~K, ~V, ~cmp, MI.MV{ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, lo2, hi2, d2}, k, OK.dg_good(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, hw)), VD.vm_exact(~K, ~V, ~cmp, Bool, S.view_contains_key(~K, ~V, ~cmp, VD.vmod(~K, ~V, ~cmp, MI.MV{ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, lo2, hi2, d2}), k), MI.view_contains_key(~K, ~V, ~cmp, MI.MV{ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, lo2, hi2, d2}, k), MI.MV{ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, lo2, hi2, d2}, S.is_some(V, S.pick(Maybe<&2, V>, S.in_range(~K, ~cmp, k, lo2, hi2), S.find(~K, ~V, ~cmp, k, ST.ents(~K, ~V, ST.ids(tg), nl, pl)), None{})), hm, {==}, hw))

# ---- put and remove: the key in range, then the map's ----

# a map result rewrapped in the view's bounds
def rw_put(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +lo2: M.Bound<K>, +hi2: M.Bound<K>, +d2: Bool, r: ST.Sh<K, V> & Result<&2, &2, M.Rejected<K, V>, Maybe<&2, V>>, -a: M.TreeMap<K, V, cmp>, +o: Result<&2, &2, M.Rejected<K, V>, Maybe<&2, V>>, +h: {MI.rp(~K, ~V, ~cmp, Result<&2, &2, M.Rejected<K, V>, Maybe<&2, V>>, r) == (a, o) : M.TreeMap<K, V, cmp> & Result<&2, &2, M.Rejected<K, V>, Maybe<&2, V>>}) -> {MI.rvp(~K, ~V, ~cmp, Result<&2, &2, M.Rejected<K, V>, Maybe<&2, V>>, MI.view_put_finish(~K, ~V, ~cmp, lo2, hi2, d2, r)) == (M.View{a, lo2, hi2, d2}, o) : M.View<K, V, cmp> & Result<&2, &2, M.Rejected<K, V>, Maybe<&2, V>>}:
  match r:
    case Tuple{+m, +x}:
      L.subst(M.TreeMap<K, V, cmp> & Result<&2, &2, M.Rejected<K, V>, Maybe<&2, V>>, z => {(M.View{ST.real(~K, ~V, ~cmp, m), lo2, hi2, d2}, x) == (M.View{Pair.fst(M.TreeMap<K, V, cmp>, Result<&2, &2, M.Rejected<K, V>, Maybe<&2, V>>, z), lo2, hi2, d2}, Pair.snd(M.TreeMap<K, V, cmp>, Result<&2, &2, M.Rejected<K, V>, Maybe<&2, V>>, z)) : M.View<K, V, cmp> & Result<&2, &2, M.Rejected<K, V>, Maybe<&2, V>>}, (ST.real(~K, ~V, ~cmp, m), x), (a, o), h, {==})

def rw_val(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +lo2: M.Bound<K>, +hi2: M.Bound<K>, +d2: Bool, r: ST.Sh<K, V> & Maybe<&2, V>, -a: M.TreeMap<K, V, cmp>, +o: Maybe<&2, V>, +h: {MI.rp(~K, ~V, ~cmp, Maybe<&2, V>, r) == (a, o) : M.TreeMap<K, V, cmp> & Maybe<&2, V>}) -> {MI.rvp(~K, ~V, ~cmp, Maybe<&2, V>, MI.view_value(~K, ~V, ~cmp, lo2, hi2, d2, r)) == (M.View{a, lo2, hi2, d2}, o) : M.View<K, V, cmp> & Maybe<&2, V>}:
  match r:
    case Tuple{+m, +x}:
      L.subst(M.TreeMap<K, V, cmp> & Maybe<&2, V>, z => {(M.View{ST.real(~K, ~V, ~cmp, m), lo2, hi2, d2}, x) == (M.View{Pair.fst(M.TreeMap<K, V, cmp>, Maybe<&2, V>, z), lo2, hi2, d2}, Pair.snd(M.TreeMap<K, V, cmp>, Maybe<&2, V>, z)) : M.View<K, V, cmp> & Maybe<&2, V>}, (ST.real(~K, ~V, ~cmp, m), x), (a, o), h, {==})


def vput_t(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +lo2: M.Bound<K>, +hi2: M.Bound<K>, +d2: Bool, +k: K, +v: V, p: OK.MOK(~K, ~V, ~cmp, Result<&2, &2, M.Rejected<K, V>, Maybe<&2, V>>, S.put(~K, ~V, ~cmp, ST.model(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}), k, v), MI.put(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, k, v))) -> VD.VM(~K, ~V, ~cmp, Result<&2, &2, M.Rejected<K, V>, Maybe<&2, V>>, S.view_put_at(~K, ~V, ~cmp, ST.model(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}), k, v, lo2, hi2, d2, True{}), MI.view_put_checked(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, k, v, lo2, hi2, d2, True{})):
  match p:
    case Tuple{+s2, Tuple{+o, Tuple{+h1, Tuple{+h2, h3}}}}:
      %Equal.sym(S.Model<K, V> & Result<&2, &2, M.Rejected<K, V>, Maybe<&2, V>>, S.put(~K, ~V, ~cmp, ST.model(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}), k, v), (ST.model(~K, ~V, ~cmp, s2), o), h2) : VD.VM(~K, ~V, ~cmp, Result<&2, &2, M.Rejected<K, V>, Maybe<&2, V>>, S.rewrap_put(K, V, lo2, hi2, d2, _), MI.view_put_checked(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, k, v, lo2, hi2, d2, True{}))
      (MI.MV{s2, lo2, hi2, d2}, (o, (rw_put(~K, ~V, ~cmp, lo2, hi2, d2, MI.put(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, k, v), ST.real(~K, ~V, ~cmp, s2), o, h1), ({==}, h3))))

def vput_b(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +hg: {ST.good(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}) == True{} : Bool}, +lo2: M.Bound<K>, +hi2: M.Bound<K>, +d2: Bool, +k: K, +v: V, +b: Bool) -> VD.VM(~K, ~V, ~cmp, Result<&2, &2, M.Rejected<K, V>, Maybe<&2, V>>, S.view_put_at(~K, ~V, ~cmp, ST.model(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}), k, v, lo2, hi2, d2, b), MI.view_put_checked(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, k, v, lo2, hi2, d2, b)):
  match b:
    case True{}:
      vput_t(~K, ~V, ~cmp, ~o, n, root, lo, hi, free, l, d, nl, pl, tg, fl, lo2, hi2, d2, k, v, PM.put_m(~K, ~V, ~cmp, ~o, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg, k, v))
    case False{}:
      (MI.MV{ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, lo2, hi2, d2}, (Fail{M.Rejected{M.OutOfRange{}, k, v}}, ({==}, ({==}, hg))))

def view_put_ok(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +w: MI.MView<K, V>, +hw: {VD.vgood(~K, ~V, ~cmp, w) == True{} : Bool}, +k: K, +v: V) -> VD.VPOK(~K, ~V, ~cmp, Result<&2, &2, M.Rejected<K, V>, Maybe<&2, V>>, S.view_put(~K, ~V, ~cmp, VD.vmod(~K, ~V, ~cmp, w), k, v), M.view_put(~K, ~V, ~cmp, MI.rv(~K, ~V, ~cmp, w), k, v)):
  match w:
    case MI.MV{ST.SH{+n, +root, +lo, +hi, +free, +l, +d, +nl, +pl, +tg, +fl}, +lo2, +hi2, +d2}:
      %CU.inr_eq(~K, ~V, ~cmp, k, lo2, hi2) : VD.VPOK(~K, ~V, ~cmp, Result<&2, &2, M.Rejected<K, V>, Maybe<&2, V>>, S.view_put_at(~K, ~V, ~cmp, ST.model(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}), k, v, lo2, hi2, d2, _), M.view_put(~K, ~V, ~cmp, MI.rv(~K, ~V, ~cmp, MI.MV{ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, lo2, hi2, d2}), k, v))
      VD.vm_pok(~K, ~V, ~cmp, Result<&2, &2, M.Rejected<K, V>, Maybe<&2, V>>, S.view_put_at(~K, ~V, ~cmp, ST.model(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}), k, v, lo2, hi2, d2, M.in_range(~K, ~V, ~cmp, k, lo2, hi2)), MI.view_put(~K, ~V, ~cmp, MI.MV{ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, lo2, hi2, d2}, k, v), M.view_put(~K, ~V, ~cmp, MI.rv(~K, ~V, ~cmp, MI.MV{ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, lo2, hi2, d2}), k, v), SM.view_put_s(~K, ~V, ~cmp, MI.MV{ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, lo2, hi2, d2}, k, v, OK.dg_good(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, hw)), vput_b(~K, ~V, ~cmp, ~o, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hw, lo2, hi2, d2, k, v, M.in_range(~K, ~V, ~cmp, k, lo2, hi2)))


def vrem_t(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +lo2: M.Bound<K>, +hi2: M.Bound<K>, +d2: Bool, +k: K, p: OK.MOK(~K, ~V, ~cmp, Maybe<&2, V>, S.remove(~K, ~V, ~cmp, ST.model(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}), k), MI.remove(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, k))) -> VD.VM(~K, ~V, ~cmp, Maybe<&2, V>, S.view_remove_at(~K, ~V, ~cmp, ST.model(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}), k, lo2, hi2, d2, True{}), MI.view_remove_checked(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, k, lo2, hi2, d2, True{})):
  match p:
    case Tuple{+s2, Tuple{+o, Tuple{+h1, Tuple{+h2, h3}}}}:
      %Equal.sym(S.Model<K, V> & Maybe<&2, V>, S.remove(~K, ~V, ~cmp, ST.model(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}), k), (ST.model(~K, ~V, ~cmp, s2), o), h2) : VD.VM(~K, ~V, ~cmp, Maybe<&2, V>, S.rewrap_val(K, V, lo2, hi2, d2, _), MI.view_remove_checked(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, k, lo2, hi2, d2, True{}))
      (MI.MV{s2, lo2, hi2, d2}, (o, (rw_val(~K, ~V, ~cmp, lo2, hi2, d2, MI.remove(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, k), ST.real(~K, ~V, ~cmp, s2), o, h1), ({==}, h3))))

def vrem_b(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +hg: {ST.good(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}) == True{} : Bool}, +lo2: M.Bound<K>, +hi2: M.Bound<K>, +d2: Bool, +k: K, +b: Bool) -> VD.VM(~K, ~V, ~cmp, Maybe<&2, V>, S.view_remove_at(~K, ~V, ~cmp, ST.model(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}), k, lo2, hi2, d2, b), MI.view_remove_checked(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, k, lo2, hi2, d2, b)):
  match b:
    case True{}:
      vrem_t(~K, ~V, ~cmp, ~o, n, root, lo, hi, free, l, d, nl, pl, tg, fl, lo2, hi2, d2, k, RV.rm_m(~K, ~V, ~cmp, ~o, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg, k))
    case False{}:
      (MI.MV{ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, lo2, hi2, d2}, (None{}, ({==}, ({==}, hg))))

def view_remove_ok(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +w: MI.MView<K, V>, +hw: {VD.vgood(~K, ~V, ~cmp, w) == True{} : Bool}, +k: K) -> VD.VPOK(~K, ~V, ~cmp, Maybe<&2, V>, S.view_remove(~K, ~V, ~cmp, VD.vmod(~K, ~V, ~cmp, w), k), M.view_remove(~K, ~V, ~cmp, MI.rv(~K, ~V, ~cmp, w), k)):
  match w:
    case MI.MV{ST.SH{+n, +root, +lo, +hi, +free, +l, +d, +nl, +pl, +tg, +fl}, +lo2, +hi2, +d2}:
      %CU.inr_eq(~K, ~V, ~cmp, k, lo2, hi2) : VD.VPOK(~K, ~V, ~cmp, Maybe<&2, V>, S.view_remove_at(~K, ~V, ~cmp, ST.model(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}), k, lo2, hi2, d2, _), M.view_remove(~K, ~V, ~cmp, MI.rv(~K, ~V, ~cmp, MI.MV{ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, lo2, hi2, d2}), k))
      VD.vm_pok(~K, ~V, ~cmp, Maybe<&2, V>, S.view_remove_at(~K, ~V, ~cmp, ST.model(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}), k, lo2, hi2, d2, M.in_range(~K, ~V, ~cmp, k, lo2, hi2)), MI.view_remove(~K, ~V, ~cmp, MI.MV{ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, lo2, hi2, d2}, k), M.view_remove(~K, ~V, ~cmp, MI.rv(~K, ~V, ~cmp, MI.MV{ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, lo2, hi2, d2}), k), SM.view_remove_s(~K, ~V, ~cmp, MI.MV{ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, lo2, hi2, d2}, k, OK.dg_good(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, hw)), vrem_b(~K, ~V, ~cmp, ~o, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hw, lo2, hi2, d2, k, M.in_range(~K, ~V, ~cmp, k, lo2, hi2)))
