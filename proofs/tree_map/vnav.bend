import Base
import ../lib/logic.bend as L
import ../lib/order.bend as O
import ../spec/common.bend as SC
import ../spec/tree_map.bend as S
import ../../src/containers/balanced_search_tree.bend as M
import ./state.bend as ST
import ./mirror.bend as MI
import ./ok.bend as OK
import ./ends.bend as EN
import ./navm.bend as NM
import ./ord.bend as OR
import ./cur.bend as CU
import ./vsp.bend as VS
import ./vdef.bend as VD

# A view's first and last entries and its searches: the mirror starts at the
# bound (or searches from the key, when inside the view) and checks the entry
# found against the range; the specification searches the entries within.
# (source: tools/generators/tm_hand/vnav.src)


# ---- the entry at a bound ----

def rsf_m(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +hg: {ST.good(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}) == True{} : Bool}, +lw: M.Bound<K>) -> {MI.entry_snapshot(~K, ~V, ~cmp, MI.range_start(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, lw, True{})) == (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, VS.fal(~K, ~V, ~cmp, lw, ST.ents(~K, ~V, ST.ids(tg), nl, pl))) : ST.Sh<K, V> & Maybe<&2, M.Entry<K, V>>}:
  match lw:
    case M.Unbounded{}:
      %Equal.sym(Maybe<&2, M.Entry<K, V>>, VS.fal(~K, ~V, ~cmp, M.Unbounded{}, ST.ents(~K, ~V, ST.ids(tg), nl, pl)), S.head(M.Entry<K, V>, ST.ents(~K, ~V, ST.ids(tg), nl, pl)), VS.fal_u(~K, ~V, ~cmp, ST.ents(~K, ~V, ST.ids(tg), nl, pl))) : {MI.entry_snapshot(~K, ~V, ~cmp, MI.range_start(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, M.Unbounded{}, True{})) == (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, _) : ST.Sh<K, V> & Maybe<&2, M.Entry<K, V>>}
      EN.first_entry_m(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg)
    case M.Inclusive{+x}:
      %Equal.sym(Maybe<&2, M.Entry<K, V>>, VS.fal(~K, ~V, ~cmp, M.Inclusive{x}, ST.ents(~K, ~V, ST.ids(tg), nl, pl)), S.first_where(~K, ~V, ~cmp, x, True{}, ST.ents(~K, ~V, ST.ids(tg), nl, pl)), VS.fal_i(~K, ~V, ~cmp, x, ST.ents(~K, ~V, ST.ids(tg), nl, pl))) : {MI.entry_snapshot(~K, ~V, ~cmp, MI.range_start(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, M.Inclusive{x}, True{})) == (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, _) : ST.Sh<K, V> & Maybe<&2, M.Entry<K, V>>}
      NM.nav_entry_m(~K, ~V, ~cmp, ~o, n, root, lo, hi, free, l, d, nl, pl, tg, fl, x, True{}, True{}, hg)
    case M.Exclusive{+x}:
      %Equal.sym(Maybe<&2, M.Entry<K, V>>, VS.fal(~K, ~V, ~cmp, M.Exclusive{x}, ST.ents(~K, ~V, ST.ids(tg), nl, pl)), S.first_where(~K, ~V, ~cmp, x, False{}, ST.ents(~K, ~V, ST.ids(tg), nl, pl)), VS.fal_x(~K, ~V, ~cmp, x, ST.ents(~K, ~V, ST.ids(tg), nl, pl))) : {MI.entry_snapshot(~K, ~V, ~cmp, MI.range_start(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, M.Exclusive{x}, True{})) == (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, _) : ST.Sh<K, V> & Maybe<&2, M.Entry<K, V>>}
      NM.nav_entry_m(~K, ~V, ~cmp, ~o, n, root, lo, hi, free, l, d, nl, pl, tg, fl, x, True{}, False{}, hg)

def rsb_m(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +hg: {ST.good(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}) == True{} : Bool}, +up: M.Bound<K>) -> {MI.entry_snapshot(~K, ~V, ~cmp, MI.range_start(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, up, False{})) == (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, VS.lbu(~K, ~V, ~cmp, up, ST.ents(~K, ~V, ST.ids(tg), nl, pl), None{})) : ST.Sh<K, V> & Maybe<&2, M.Entry<K, V>>}:
  match up:
    case M.Unbounded{}:
      %Equal.sym(Maybe<&2, M.Entry<K, V>>, VS.lbu(~K, ~V, ~cmp, M.Unbounded{}, ST.ents(~K, ~V, ST.ids(tg), nl, pl), None{}), S.last(M.Entry<K, V>, ST.ents(~K, ~V, ST.ids(tg), nl, pl)), Equal.trans(Maybe<&2, M.Entry<K, V>>, VS.lbu(~K, ~V, ~cmp, M.Unbounded{}, ST.ents(~K, ~V, ST.ids(tg), nl, pl), None{}), OR.orm(M.Entry<K, V>, S.last(M.Entry<K, V>, ST.ents(~K, ~V, ST.ids(tg), nl, pl)), None{}), S.last(M.Entry<K, V>, ST.ents(~K, ~V, ST.ids(tg), nl, pl)), VS.lbu_u(~K, ~V, ~cmp, ST.ents(~K, ~V, ST.ids(tg), nl, pl), None{}), OR.orm_none(M.Entry<K, V>, S.last(M.Entry<K, V>, ST.ents(~K, ~V, ST.ids(tg), nl, pl))))) : {MI.entry_snapshot(~K, ~V, ~cmp, MI.range_start(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, M.Unbounded{}, False{})) == (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, _) : ST.Sh<K, V> & Maybe<&2, M.Entry<K, V>>}
      EN.last_entry_m(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg)
    case M.Inclusive{+y}:
      %Equal.sym(Maybe<&2, M.Entry<K, V>>, VS.lbu(~K, ~V, ~cmp, M.Inclusive{y}, ST.ents(~K, ~V, ST.ids(tg), nl, pl), None{}), S.last_where(~K, ~V, ~cmp, y, True{}, ST.ents(~K, ~V, ST.ids(tg), nl, pl), None{}), VS.lbu_i(~K, ~V, ~cmp, y, ST.ents(~K, ~V, ST.ids(tg), nl, pl), None{})) : {MI.entry_snapshot(~K, ~V, ~cmp, MI.range_start(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, M.Inclusive{y}, False{})) == (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, _) : ST.Sh<K, V> & Maybe<&2, M.Entry<K, V>>}
      NM.nav_entry_m(~K, ~V, ~cmp, ~o, n, root, lo, hi, free, l, d, nl, pl, tg, fl, y, False{}, True{}, hg)
    case M.Exclusive{+y}:
      %Equal.sym(Maybe<&2, M.Entry<K, V>>, VS.lbu(~K, ~V, ~cmp, M.Exclusive{y}, ST.ents(~K, ~V, ST.ids(tg), nl, pl), None{}), S.last_where(~K, ~V, ~cmp, y, False{}, ST.ents(~K, ~V, ST.ids(tg), nl, pl), None{}), VS.lbu_x(~K, ~V, ~cmp, y, ST.ents(~K, ~V, ST.ids(tg), nl, pl), None{})) : {MI.entry_snapshot(~K, ~V, ~cmp, MI.range_start(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, M.Exclusive{y}, False{})) == (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, _) : ST.Sh<K, V> & Maybe<&2, M.Entry<K, V>>}
      NM.nav_entry_m(~K, ~V, ~cmp, ~o, n, root, lo, hi, free, l, d, nl, pl, tg, fl, y, False{}, False{}, hg)

# ---- the entry found, checked against the range ----


def ver_b(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +s: ST.Sh<K, V>, +lo2: M.Bound<K>, +hi2: M.Bound<K>, +d2: Bool, +en: M.Entry<K, V>, +b: Bool) -> {MI.view_entry_checked(~K, ~V, ~cmp, s, lo2, hi2, d2, en, b) == (MI.MV{s, lo2, hi2, d2}, S.pick(Maybe<&2, M.Entry<K, V>>, b, Some{en}, None{})) : MI.MView<K, V> & Maybe<&2, M.Entry<K, V>>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def ver_eq(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +s: ST.Sh<K, V>, +lo2: M.Bound<K>, +hi2: M.Bound<K>, +d2: Bool, +m: Maybe<&2, M.Entry<K, V>>) -> {MI.view_entry_result(~K, ~V, ~cmp, lo2, hi2, d2, (s, m)) == (MI.MV{s, lo2, hi2, d2}, VS.chk(~K, ~V, ~cmp, lo2, hi2, m)) : MI.MView<K, V> & Maybe<&2, M.Entry<K, V>>}:
  match m:
    case None{}:
      {==}
    case Some{M.Entry{+k, +v}}:
      %Equal.sym(Bool, M.in_range(~K, ~V, ~cmp, k, lo2, hi2), S.in_range(~K, ~cmp, k, lo2, hi2), CU.inr_eq(~K, ~V, ~cmp, k, lo2, hi2)) : {MI.view_entry_checked(~K, ~V, ~cmp, s, lo2, hi2, d2, M.Entry{k, v}, _) == (MI.MV{s, lo2, hi2, d2}, VS.chk(~K, ~V, ~cmp, lo2, hi2, Some{M.Entry{k, v}})) : MI.MView<K, V> & Maybe<&2, M.Entry<K, V>>}
      ver_b(~K, ~V, ~cmp, s, lo2, hi2, d2, M.Entry{k, v}, S.in_range(~K, ~cmp, k, lo2, hi2))

# a snapshot known, its check the specification's answer
def vres(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +s: ST.Sh<K, V>, +lo2: M.Bound<K>, +hi2: M.Bound<K>, +d2: Bool, -r: ST.Sh<K, V> & Maybe<&2, M.Entry<K, V>>, +m: Maybe<&2, M.Entry<K, V>>, +o: Maybe<&2, M.Entry<K, V>>, +hr: {r == (s, m) : ST.Sh<K, V> & Maybe<&2, M.Entry<K, V>>}, +ho: {o == VS.chk(~K, ~V, ~cmp, lo2, hi2, m) : Maybe<&2, M.Entry<K, V>>}) -> {MI.view_entry_result(~K, ~V, ~cmp, lo2, hi2, d2, r) == (MI.MV{s, lo2, hi2, d2}, o) : MI.MView<K, V> & Maybe<&2, M.Entry<K, V>>}:
  %Equal.sym(ST.Sh<K, V> & Maybe<&2, M.Entry<K, V>>, r, (s, m), hr) : {MI.view_entry_result(~K, ~V, ~cmp, lo2, hi2, d2, _) == (MI.MV{s, lo2, hi2, d2}, o) : MI.MView<K, V> & Maybe<&2, M.Entry<K, V>>}
  %Equal.sym(Maybe<&2, M.Entry<K, V>>, o, VS.chk(~K, ~V, ~cmp, lo2, hi2, m), ho) : {MI.view_entry_result(~K, ~V, ~cmp, lo2, hi2, d2, (s, m)) == (MI.MV{s, lo2, hi2, d2}, _) : MI.MView<K, V> & Maybe<&2, M.Entry<K, V>>}
  ver_eq(~K, ~V, ~cmp, s, lo2, hi2, d2, m)

# ---- first and last ----


def vx_up(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +hg: {ST.good(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}) == True{} : Bool}, +lo2: M.Bound<K>, +hi2: M.Bound<K>, +d2: Bool, +up: Bool) -> {MI.view_entry_result(~K, ~V, ~cmp, lo2, hi2, d2, MI.entry_snapshot(~K, ~V, ~cmp, MI.range_start(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, M.pick(M.Bound<K>, up, lo2, hi2), up))) == (MI.MV{ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, lo2, hi2, d2}, S.pick(Maybe<&2, M.Entry<K, V>>, up, S.head(M.Entry<K, V>, S.within(~K, ~V, ~cmp, lo2, hi2, ST.ents(~K, ~V, ST.ids(tg), nl, pl))), S.last(M.Entry<K, V>, S.within(~K, ~V, ~cmp, lo2, hi2, ST.ents(~K, ~V, ST.ids(tg), nl, pl))))) : MI.MView<K, V> & Maybe<&2, M.Entry<K, V>>}:
  match up:
    case True{}:
      vres(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, lo2, hi2, d2, MI.entry_snapshot(~K, ~V, ~cmp, MI.range_start(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, lo2, True{})), VS.fal(~K, ~V, ~cmp, lo2, ST.ents(~K, ~V, ST.ids(tg), nl, pl)), S.head(M.Entry<K, V>, S.within(~K, ~V, ~cmp, lo2, hi2, ST.ents(~K, ~V, ST.ids(tg), nl, pl))), rsf_m(~K, ~V, ~cmp, ~o, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg, lo2), VS.first_within(~K, ~V, ~cmp, ~o, lo2, hi2, ST.ents(~K, ~V, ST.ids(tg), nl, pl), ST.g_cord(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg)))
    case False{}:
      vres(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, lo2, hi2, d2, MI.entry_snapshot(~K, ~V, ~cmp, MI.range_start(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, hi2, False{})), VS.lbu(~K, ~V, ~cmp, hi2, ST.ents(~K, ~V, ST.ids(tg), nl, pl), None{}), S.last(M.Entry<K, V>, S.within(~K, ~V, ~cmp, lo2, hi2, ST.ents(~K, ~V, ST.ids(tg), nl, pl))), rsb_m(~K, ~V, ~cmp, ~o, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg, hi2), VS.last_within(~K, ~V, ~cmp, ~o, lo2, hi2, ST.ents(~K, ~V, ST.ids(tg), nl, pl), ST.g_cord(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg)))


def vx_m(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +hg: {ST.good(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}) == True{} : Bool}, +lo2: M.Bound<K>, +hi2: M.Bound<K>, +d2: Bool, +first: Bool) -> {MI.view_extreme(~K, ~V, ~cmp, MI.MV{ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, lo2, hi2, d2}, first) == (MI.MV{ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, lo2, hi2, d2}, S.pick(Maybe<&2, M.Entry<K, V>>, S.pick(Bool, d2, Bool.not(first), first), S.head(M.Entry<K, V>, S.within(~K, ~V, ~cmp, lo2, hi2, ST.ents(~K, ~V, ST.ids(tg), nl, pl))), S.last(M.Entry<K, V>, S.within(~K, ~V, ~cmp, lo2, hi2, ST.ents(~K, ~V, ST.ids(tg), nl, pl))))) : MI.MView<K, V> & Maybe<&2, M.Entry<K, V>>}:
  match d2:
    case True{}:
      vx_up(~K, ~V, ~cmp, ~o, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg, lo2, hi2, True{}, Bool.not(first))
    case False{}:
      vx_up(~K, ~V, ~cmp, ~o, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg, lo2, hi2, False{}, first)

# ---- searches ----


def vn_t(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +hg: {ST.good(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}) == True{} : Bool}, +lo2: M.Bound<K>, +hi2: M.Bound<K>, +d2: Bool, +k: K, +incl: Bool, +a: Bool, +ha: {S.above_lower(~K, ~cmp, k, lo2) == a : Bool}) -> {MI.view_entry_result(~K, ~V, ~cmp, lo2, hi2, d2, MI.entry_snapshot(~K, ~V, ~cmp, MI.view_nav_start(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, k, lo2, hi2, True{}, incl, a))) == (MI.MV{ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, lo2, hi2, d2}, S.nav(~K, ~V, ~cmp, k, True{}, incl, S.within(~K, ~V, ~cmp, lo2, hi2, ST.ents(~K, ~V, ST.ids(tg), nl, pl)))) : MI.MView<K, V> & Maybe<&2, M.Entry<K, V>>}:
  match a:
    case True{}:
      vres(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, lo2, hi2, d2, MI.entry_snapshot(~K, ~V, ~cmp, MI.navigate(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, k, True{}, incl)), S.first_where(~K, ~V, ~cmp, k, incl, ST.ents(~K, ~V, ST.ids(tg), nl, pl)), S.first_where(~K, ~V, ~cmp, k, incl, S.within(~K, ~V, ~cmp, lo2, hi2, ST.ents(~K, ~V, ST.ids(tg), nl, pl))), NM.nav_entry_m(~K, ~V, ~cmp, ~o, n, root, lo, hi, free, l, d, nl, pl, tg, fl, k, True{}, incl, hg), VS.fw_within(~K, ~V, ~cmp, ~o, lo2, hi2, k, incl, ST.ents(~K, ~V, ST.ids(tg), nl, pl), ST.g_cord(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg), ha))
    case False{}:
      vres(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, lo2, hi2, d2, MI.entry_snapshot(~K, ~V, ~cmp, MI.range_start(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, lo2, True{})), VS.fal(~K, ~V, ~cmp, lo2, ST.ents(~K, ~V, ST.ids(tg), nl, pl)), S.first_where(~K, ~V, ~cmp, k, incl, S.within(~K, ~V, ~cmp, lo2, hi2, ST.ents(~K, ~V, ST.ids(tg), nl, pl))), rsf_m(~K, ~V, ~cmp, ~o, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg, lo2), Equal.trans(Maybe<&2, M.Entry<K, V>>, S.first_where(~K, ~V, ~cmp, k, incl, S.within(~K, ~V, ~cmp, lo2, hi2, ST.ents(~K, ~V, ST.ids(tg), nl, pl))), S.head(M.Entry<K, V>, S.within(~K, ~V, ~cmp, lo2, hi2, ST.ents(~K, ~V, ST.ids(tg), nl, pl))), VS.chk(~K, ~V, ~cmp, lo2, hi2, VS.fal(~K, ~V, ~cmp, lo2, ST.ents(~K, ~V, ST.ids(tg), nl, pl))), VS.fw_below(~K, ~V, ~cmp, ~o, lo2, hi2, k, incl, ST.ents(~K, ~V, ST.ids(tg), nl, pl), ha), VS.first_within(~K, ~V, ~cmp, ~o, lo2, hi2, ST.ents(~K, ~V, ST.ids(tg), nl, pl), ST.g_cord(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg))))

def vn_f(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +hg: {ST.good(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}) == True{} : Bool}, +lo2: M.Bound<K>, +hi2: M.Bound<K>, +d2: Bool, +k: K, +incl: Bool, +b: Bool, +hb: {S.below_upper(~K, ~cmp, k, hi2) == b : Bool}) -> {MI.view_entry_result(~K, ~V, ~cmp, lo2, hi2, d2, MI.entry_snapshot(~K, ~V, ~cmp, MI.view_nav_start(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, k, lo2, hi2, False{}, incl, b))) == (MI.MV{ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, lo2, hi2, d2}, S.nav(~K, ~V, ~cmp, k, False{}, incl, S.within(~K, ~V, ~cmp, lo2, hi2, ST.ents(~K, ~V, ST.ids(tg), nl, pl)))) : MI.MView<K, V> & Maybe<&2, M.Entry<K, V>>}:
  match b:
    case True{}:
      vres(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, lo2, hi2, d2, MI.entry_snapshot(~K, ~V, ~cmp, MI.navigate(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, k, False{}, incl)), S.last_where(~K, ~V, ~cmp, k, incl, ST.ents(~K, ~V, ST.ids(tg), nl, pl), None{}), S.last_where(~K, ~V, ~cmp, k, incl, S.within(~K, ~V, ~cmp, lo2, hi2, ST.ents(~K, ~V, ST.ids(tg), nl, pl)), None{}), NM.nav_entry_m(~K, ~V, ~cmp, ~o, n, root, lo, hi, free, l, d, nl, pl, tg, fl, k, False{}, incl, hg), VS.lw_within(~K, ~V, ~cmp, ~o, lo2, hi2, k, incl, ST.ents(~K, ~V, ST.ids(tg), nl, pl), ST.g_cord(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg), hb))
    case False{}:
      vres(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, lo2, hi2, d2, MI.entry_snapshot(~K, ~V, ~cmp, MI.range_start(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, hi2, False{})), VS.lbu(~K, ~V, ~cmp, hi2, ST.ents(~K, ~V, ST.ids(tg), nl, pl), None{}), S.last_where(~K, ~V, ~cmp, k, incl, S.within(~K, ~V, ~cmp, lo2, hi2, ST.ents(~K, ~V, ST.ids(tg), nl, pl)), None{}), rsb_m(~K, ~V, ~cmp, ~o, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg, hi2), Equal.trans(Maybe<&2, M.Entry<K, V>>, S.last_where(~K, ~V, ~cmp, k, incl, S.within(~K, ~V, ~cmp, lo2, hi2, ST.ents(~K, ~V, ST.ids(tg), nl, pl)), None{}), S.last(M.Entry<K, V>, S.within(~K, ~V, ~cmp, lo2, hi2, ST.ents(~K, ~V, ST.ids(tg), nl, pl))), VS.chk(~K, ~V, ~cmp, lo2, hi2, VS.lbu(~K, ~V, ~cmp, hi2, ST.ents(~K, ~V, ST.ids(tg), nl, pl), None{})), VS.lw_above(~K, ~V, ~cmp, ~o, lo2, hi2, k, incl, ST.ents(~K, ~V, ST.ids(tg), nl, pl), hb), VS.last_within(~K, ~V, ~cmp, ~o, lo2, hi2, ST.ents(~K, ~V, ST.ids(tg), nl, pl), ST.g_cord(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg))))

def vn_up(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +hg: {ST.good(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}) == True{} : Bool}, +lo2: M.Bound<K>, +hi2: M.Bound<K>, +d2: Bool, +k: K, +incl: Bool, +up: Bool) -> {MI.view_entry_result(~K, ~V, ~cmp, lo2, hi2, d2, MI.entry_snapshot(~K, ~V, ~cmp, MI.view_nav_start(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, k, lo2, hi2, up, incl, M.pick(Bool, up, M.above_lower(~K, ~V, ~cmp, k, lo2), M.below_upper(~K, ~V, ~cmp, k, hi2))))) == (MI.MV{ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, lo2, hi2, d2}, S.nav(~K, ~V, ~cmp, k, up, incl, S.within(~K, ~V, ~cmp, lo2, hi2, ST.ents(~K, ~V, ST.ids(tg), nl, pl)))) : MI.MView<K, V> & Maybe<&2, M.Entry<K, V>>}:
  match up:
    case True{}:
      %Equal.sym(Bool, M.above_lower(~K, ~V, ~cmp, k, lo2), S.above_lower(~K, ~cmp, k, lo2), CU.al_eq(~K, ~V, ~cmp, k, lo2)) : {MI.view_entry_result(~K, ~V, ~cmp, lo2, hi2, d2, MI.entry_snapshot(~K, ~V, ~cmp, MI.view_nav_start(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, k, lo2, hi2, True{}, incl, _))) == (MI.MV{ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, lo2, hi2, d2}, S.nav(~K, ~V, ~cmp, k, True{}, incl, S.within(~K, ~V, ~cmp, lo2, hi2, ST.ents(~K, ~V, ST.ids(tg), nl, pl)))) : MI.MView<K, V> & Maybe<&2, M.Entry<K, V>>}
      vn_t(~K, ~V, ~cmp, ~o, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg, lo2, hi2, d2, k, incl, S.above_lower(~K, ~cmp, k, lo2), {==})
    case False{}:
      %Equal.sym(Bool, M.below_upper(~K, ~V, ~cmp, k, hi2), S.below_upper(~K, ~cmp, k, hi2), CU.bu_eq(~K, ~V, ~cmp, k, hi2)) : {MI.view_entry_result(~K, ~V, ~cmp, lo2, hi2, d2, MI.entry_snapshot(~K, ~V, ~cmp, MI.view_nav_start(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, k, lo2, hi2, False{}, incl, _))) == (MI.MV{ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, lo2, hi2, d2}, S.nav(~K, ~V, ~cmp, k, False{}, incl, S.within(~K, ~V, ~cmp, lo2, hi2, ST.ents(~K, ~V, ST.ids(tg), nl, pl)))) : MI.MView<K, V> & Maybe<&2, M.Entry<K, V>>}
      vn_f(~K, ~V, ~cmp, ~o, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg, lo2, hi2, d2, k, incl, S.below_upper(~K, ~cmp, k, hi2), {==})


def vn_m(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +hg: {ST.good(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}) == True{} : Bool}, +lo2: M.Bound<K>, +hi2: M.Bound<K>, +d2: Bool, +k: K, +higher: Bool, +incl: Bool) -> {MI.view_nav(~K, ~V, ~cmp, MI.MV{ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, lo2, hi2, d2}, k, higher, incl) == (MI.MV{ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, lo2, hi2, d2}, S.nav(~K, ~V, ~cmp, k, S.pick(Bool, d2, Bool.not(higher), higher), incl, S.within(~K, ~V, ~cmp, lo2, hi2, ST.ents(~K, ~V, ST.ids(tg), nl, pl)))) : MI.MView<K, V> & Maybe<&2, M.Entry<K, V>>}:
  match d2:
    case True{}:
      vn_up(~K, ~V, ~cmp, ~o, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg, lo2, hi2, True{}, k, incl, Bool.not(higher))
    case False{}:
      vn_up(~K, ~V, ~cmp, ~o, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg, lo2, hi2, False{}, k, incl, higher)

