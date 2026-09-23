import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../spec/common.bend as SC
import ../../src/containers/balanced_search_tree.bend as M
import ./state.bend as ST
import ./mirror.bend as MI

# The ghost tree: its height is at most its size, and the search loop over
# the node list walks it: from a subtree's root, with fuel above the height,
# the loop returns the ghost search of the subtree.
# (source: tools/generators/tm_hand/tree.src)


# ---- height ----

def nmax(+a: Nat, +b: Nat) -> Nat:
  ST.pk(Nat, Nat.is_lt(a, b), b, a)

def ht(t: ST.Tr) -> Nat:
  match t:
    case ST.TE{}:
      0n
    case ST.TN{i, tl, tr}:
      1n+nmax(ht(tl), ht(tr))

def max_c(+a: Nat, +b: Nat, +c: Nat, +ha: {Nat.is_le(a, c) == True{} : Bool}, +hb: {Nat.is_le(b, c) == True{} : Bool}, +x: Bool) -> {Nat.is_le(ST.pk(Nat, x, b, a), c) == True{} : Bool}:
  match x:
    case True{}:
      hb
    case False{}:
      ha

# max(a, b) <= c when both are
def max_le(+a: Nat, +b: Nat, +c: Nat, +ha: {Nat.is_le(a, c) == True{} : Bool}, +hb: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(nmax(a, b), c) == True{} : Bool}:
  max_c(a, b, c, ha, hb, Nat.is_lt(a, b))

def le_max_c(+a: Nat, +b: Nat, +x: Bool, +hx: {Nat.is_lt(a, b) == x : Bool}) -> {Nat.is_le(a, ST.pk(Nat, x, b, a)) == True{} : Bool} & {Nat.is_le(b, ST.pk(Nat, x, b, a)) == True{} : Bool}:
  match x:
    case True{}:
      (N.lt_le(a, b, hx), N.le_refl(b))
    case False{}:
      (N.le_refl(a), N.not_lt_le(a, b, hx))

def le_max_l(+a: Nat, +b: Nat) -> {Nat.is_le(a, nmax(a, b)) == True{} : Bool}:
  Pair.fst({Nat.is_le(a, nmax(a, b)) == True{} : Bool}, {Nat.is_le(b, nmax(a, b)) == True{} : Bool}, le_max_c(a, b, Nat.is_lt(a, b), {==}))

def le_max_r(+a: Nat, +b: Nat) -> {Nat.is_le(b, nmax(a, b)) == True{} : Bool}:
  Pair.snd({Nat.is_le(a, nmax(a, b)) == True{} : Bool}, {Nat.is_le(b, nmax(a, b)) == True{} : Bool}, le_max_c(a, b, Nat.is_lt(a, b), {==}))


def le_add_l(+a: Nat, +b: Nat) -> {Nat.is_le(b, Nat.add(a, b)) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(a, b), Nat.add(b, a), N.add_comm(a, b)) : {Nat.is_le(b, _) == True{} : Bool}
  N.le_add_right(b, a)

# the height is at most the number of ids
def ht_le(+t: ST.Tr) -> {Nat.is_le(ht(t), SC.length(Nat, ST.ids(t))) == True{} : Bool}:
  match t:
    case ST.TE{}:
      {==}
    case ST.TN{+i, +tl, +tr}:
      %Equal.sym(Nat, SC.length(Nat, ST.ids(ST.TN{i, tl, tr})), Nat.add(SC.length(Nat, ST.ids(tl)), 1n+SC.length(Nat, ST.ids(tr))), LL.length_append(Nat, ST.ids(tl), Con{i, ST.ids(tr)})) : {Nat.is_le(1n+nmax(ht(tl), ht(tr)), _) == True{} : Bool}
      %Equal.sym(Nat, Nat.add(SC.length(Nat, ST.ids(tl)), 1n+SC.length(Nat, ST.ids(tr))), 1n+Nat.add(SC.length(Nat, ST.ids(tl)), SC.length(Nat, ST.ids(tr))), N.add_succ(SC.length(Nat, ST.ids(tl)), SC.length(Nat, ST.ids(tr)))) : {Nat.is_le(1n+nmax(ht(tl), ht(tr)), _) == True{} : Bool}
      max_le(ht(tl), ht(tr), Nat.add(SC.length(Nat, ST.ids(tl)), SC.length(Nat, ST.ids(tr))), N.le_trans(ht(tl), SC.length(Nat, ST.ids(tl)), Nat.add(SC.length(Nat, ST.ids(tl)), SC.length(Nat, ST.ids(tr))), ht_le(tl), N.le_add_right(SC.length(Nat, ST.ids(tl)), SC.length(Nat, ST.ids(tr)))), N.le_trans(ht(tr), SC.length(Nat, ST.ids(tr)), Nat.add(SC.length(Nat, ST.ids(tl)), SC.length(Nat, ST.ids(tr))), ht_le(tr), le_add_l(SC.length(Nat, ST.ids(tl)), SC.length(Nat, ST.ids(tr)))))

def ht_l(+i: Nat, +tl: ST.Tr, +tr: ST.Tr, +f: Nat, +h: {Nat.is_lt(ht(ST.TN{i, tl, tr}), 1n+f) == True{} : Bool}) -> {Nat.is_lt(ht(tl), f) == True{} : Bool}:
  N.le_lt_trans(ht(tl), nmax(ht(tl), ht(tr)), f, le_max_l(ht(tl), ht(tr)), h)

def ht_r(+i: Nat, +tl: ST.Tr, +tr: ST.Tr, +f: Nat, +h: {Nat.is_lt(ht(ST.TN{i, tl, tr}), 1n+f) == True{} : Bool}) -> {Nat.is_lt(ht(tr), f) == True{} : Bool}:
  N.le_lt_trans(ht(tr), nmax(ht(tl), ht(tr)), f, le_max_r(ht(tl), ht(tr)), h)

# ---- the ghost search ----

# the comparison of k with a node's key (a free node: equal, as probe does)
def kc(~K: Data, ~cmp: K -> K -> Cmp, +k: K, x: M.Node<K>) -> Cmp:
  match x:
    case M.Free{f}:
      EQ{}
    case M.N{c, a, b, q, key}:
      cmp(k, key)

def pk3(-T: Data, +c: Cmp, x: T, y: T, z: T) -> T:
  match c:
    case LT{}:
      x
    case GT{}:
      y
    case EQ{}:
      z

def tsearch(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, t: ST.Tr, +nl: List<&2, M.Node<K>>, +k: K, +p: Nat, +left: Bool) -> M.Search:
  match t:
    case ST.TE{}:
      M.Search{0n, p, left}
    case ST.TN{+i, tl, tr}:
      pk3(M.Search, kc(~K, ~cmp, k, ST.nd(K, nl, i)), tsearch(~K, ~V, ~cmp, tl, nl, k, i, True{}), tsearch(~K, ~V, ~cmp, tr, nl, k, i, False{}), M.Search{i, p, left})


def sl_c(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +i: Nat, +tl: ST.Tr, +tr: ST.Tr, +p: Nat, +left: Bool, +k: K, +f: Nat, +c: Bool, +a: Nat, +b: Nat, +q: Nat, +key: K, +ea: {a == ST.rid(tl) : Nat}, +eb: {b == ST.rid(tr) : Nat}, +ihl: {MI.search_loop(~K, ~V, ~cmp, f, k, ST.rid(tl), i, True{}, MI.probe(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, ST.rid(tl), k)) == (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, tsearch(~K, ~V, ~cmp, tl, nl, k, i, True{})) : ST.Sh<K, V> & M.Search}, +ihr: {MI.search_loop(~K, ~V, ~cmp, f, k, ST.rid(tr), i, False{}, MI.probe(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, ST.rid(tr), k)) == (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, tsearch(~K, ~V, ~cmp, tr, nl, k, i, False{})) : ST.Sh<K, V> & M.Search}, +cc: Cmp) -> {MI.search_loop(~K, ~V, ~cmp, 1n+f, k, i, p, left, (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, (M.N{c, a, b, q, key}, cc))) == (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, pk3(M.Search, cc, tsearch(~K, ~V, ~cmp, tl, nl, k, i, True{}), tsearch(~K, ~V, ~cmp, tr, nl, k, i, False{}), M.Search{i, p, left})) : ST.Sh<K, V> & M.Search}:
  match cc:
    case LT{}:
      %Equal.sym(Nat, a, ST.rid(tl), ea) : {MI.search_loop(~K, ~V, ~cmp, f, k, _, i, True{}, MI.probe(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, _, k)) == (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, tsearch(~K, ~V, ~cmp, tl, nl, k, i, True{})) : ST.Sh<K, V> & M.Search}
      ihl
    case GT{}:
      %Equal.sym(Nat, b, ST.rid(tr), eb) : {MI.search_loop(~K, ~V, ~cmp, f, k, _, i, False{}, MI.probe(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, _, k)) == (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, tsearch(~K, ~V, ~cmp, tr, nl, k, i, False{})) : ST.Sh<K, V> & M.Search}
      ihr
    case EQ{}:
      {==}

def sl_node(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +i: Nat, +tl: ST.Tr, +tr: ST.Tr, +p: Nat, +left: Bool, +k: K, +f: Nat, +x: M.Node<K>, +hx: {ST.is_node(K, x, ST.rid(tl), ST.rid(tr), p) == True{} : Bool}, +ihl: {MI.search_loop(~K, ~V, ~cmp, f, k, ST.rid(tl), i, True{}, MI.probe(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, ST.rid(tl), k)) == (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, tsearch(~K, ~V, ~cmp, tl, nl, k, i, True{})) : ST.Sh<K, V> & M.Search}, +ihr: {MI.search_loop(~K, ~V, ~cmp, f, k, ST.rid(tr), i, False{}, MI.probe(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, ST.rid(tr), k)) == (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, tsearch(~K, ~V, ~cmp, tr, nl, k, i, False{})) : ST.Sh<K, V> & M.Search}) -> {MI.search_loop(~K, ~V, ~cmp, 1n+f, k, i, p, left, MI.probe_node(~K, ~V, ~cmp, i, k, (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, x))) == (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, pk3(M.Search, kc(~K, ~cmp, k, x), tsearch(~K, ~V, ~cmp, tl, nl, k, i, True{}), tsearch(~K, ~V, ~cmp, tr, nl, k, i, False{}), M.Search{i, p, left})) : ST.Sh<K, V> & M.Search}:
  match x:
    case M.Free{fx}:
      Empty.absurd({MI.search_loop(~K, ~V, ~cmp, 1n+f, k, i, p, left, MI.probe_node(~K, ~V, ~cmp, i, k, (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, M.Free{fx}))) == (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, pk3(M.Search, EQ{}, tsearch(~K, ~V, ~cmp, tl, nl, k, i, True{}), tsearch(~K, ~V, ~cmp, tr, nl, k, i, False{}), M.Search{i, p, left})) : ST.Sh<K, V> & M.Search}, L.false_true(hx))
    case M.N{+c, +a, +b, +q, +key}:
      +ha = L.and_left(Nat.is_eq(a, ST.rid(tl)), Bool.and(Nat.is_eq(b, ST.rid(tr)), Nat.is_eq(q, p)), hx)
      +hb = L.and_left(Nat.is_eq(b, ST.rid(tr)), Nat.is_eq(q, p), L.and_right(Nat.is_eq(a, ST.rid(tl)), Bool.and(Nat.is_eq(b, ST.rid(tr)), Nat.is_eq(q, p)), hx))
      sl_c(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, i, tl, tr, p, left, k, f, c, a, b, q, key, N.eq_from_is_eq(a, ST.rid(tl), ha), N.eq_from_is_eq(b, ST.rid(tr), hb), ihl, ihr, cmp(k, key))


def rep_parts(~K: Data, +i: Nat, +tl: ST.Tr, +tr: ST.Tr, +p: Nat, +nl: List<&2, M.Node<K>>, +h: {ST.rep(~K, ST.TN{i, tl, tr}, p, nl) == True{} : Bool}) -> {ST.is_node(K, ST.nd(K, nl, i), ST.rid(tl), ST.rid(tr), p) == True{} : Bool} & ({ST.rep(~K, tl, i, nl) == True{} : Bool} & {ST.rep(~K, tr, i, nl) == True{} : Bool}):
  +h2 = L.and_right(Nat.is_lt(0n, i), Bool.and(ST.is_node(K, ST.nd(K, nl, i), ST.rid(tl), ST.rid(tr), p), Bool.and(ST.rep(~K, tl, i, nl), ST.rep(~K, tr, i, nl))), h)
  +h3 = L.and_right(ST.is_node(K, ST.nd(K, nl, i), ST.rid(tl), ST.rid(tr), p), Bool.and(ST.rep(~K, tl, i, nl), ST.rep(~K, tr, i, nl)), h2)
  (L.and_left(ST.is_node(K, ST.nd(K, nl, i), ST.rid(tl), ST.rid(tr), p), Bool.and(ST.rep(~K, tl, i, nl), ST.rep(~K, tr, i, nl)), h2), (L.and_left(ST.rep(~K, tl, i, nl), ST.rep(~K, tr, i, nl), h3), L.and_right(ST.rep(~K, tl, i, nl), ST.rep(~K, tr, i, nl), h3)))

def rep_node(~K: Data, +i: Nat, +tl: ST.Tr, +tr: ST.Tr, +p: Nat, +nl: List<&2, M.Node<K>>, +h: {ST.rep(~K, ST.TN{i, tl, tr}, p, nl) == True{} : Bool}) -> {ST.is_node(K, ST.nd(K, nl, i), ST.rid(tl), ST.rid(tr), p) == True{} : Bool}:
  L.and_left(ST.is_node(K, ST.nd(K, nl, i), ST.rid(tl), ST.rid(tr), p), Bool.and(ST.rep(~K, tl, i, nl), ST.rep(~K, tr, i, nl)), L.and_right(Nat.is_lt(0n, i), Bool.and(ST.is_node(K, ST.nd(K, nl, i), ST.rid(tl), ST.rid(tr), p), Bool.and(ST.rep(~K, tl, i, nl), ST.rep(~K, tr, i, nl))), h))

def rep_l(~K: Data, +i: Nat, +tl: ST.Tr, +tr: ST.Tr, +p: Nat, +nl: List<&2, M.Node<K>>, +h: {ST.rep(~K, ST.TN{i, tl, tr}, p, nl) == True{} : Bool}) -> {ST.rep(~K, tl, i, nl) == True{} : Bool}:
  L.and_left(ST.rep(~K, tl, i, nl), ST.rep(~K, tr, i, nl), L.and_right(ST.is_node(K, ST.nd(K, nl, i), ST.rid(tl), ST.rid(tr), p), Bool.and(ST.rep(~K, tl, i, nl), ST.rep(~K, tr, i, nl)), L.and_right(Nat.is_lt(0n, i), Bool.and(ST.is_node(K, ST.nd(K, nl, i), ST.rid(tl), ST.rid(tr), p), Bool.and(ST.rep(~K, tl, i, nl), ST.rep(~K, tr, i, nl))), h)))

def rep_r(~K: Data, +i: Nat, +tl: ST.Tr, +tr: ST.Tr, +p: Nat, +nl: List<&2, M.Node<K>>, +h: {ST.rep(~K, ST.TN{i, tl, tr}, p, nl) == True{} : Bool}) -> {ST.rep(~K, tr, i, nl) == True{} : Bool}:
  L.and_right(ST.rep(~K, tl, i, nl), ST.rep(~K, tr, i, nl), L.and_right(ST.is_node(K, ST.nd(K, nl, i), ST.rid(tl), ST.rid(tr), p), Bool.and(ST.rep(~K, tl, i, nl), ST.rep(~K, tr, i, nl)), L.and_right(Nat.is_lt(0n, i), Bool.and(ST.is_node(K, ST.nd(K, nl, i), ST.rid(tl), ST.rid(tr), p), Bool.and(ST.rep(~K, tl, i, nl), ST.rep(~K, tr, i, nl))), h)))

# the search loop from a subtree's root is the ghost search of the subtree
def sl(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +f: Nat, +t: ST.Tr, +p: Nat, +left: Bool, +k: K, +hr: {ST.rep(~K, t, p, nl) == True{} : Bool}, +hf: {Nat.is_lt(ht(t), f) == True{} : Bool}) -> {MI.search_loop(~K, ~V, ~cmp, f, k, ST.rid(t), p, left, MI.probe(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, ST.rid(t), k)) == (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, tsearch(~K, ~V, ~cmp, t, nl, k, p, left)) : ST.Sh<K, V> & M.Search}:
  match f t:
    case 0n _:
      Empty.absurd({MI.search_loop(~K, ~V, ~cmp, 0n, k, ST.rid(t), p, left, MI.probe(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, ST.rid(t), k)) == (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, tsearch(~K, ~V, ~cmp, t, nl, k, p, left)) : ST.Sh<K, V> & M.Search}, L.true_not_false(Nat.is_lt(ht(t), 0n), hf, N.not_lt_zero(ht(t))))
    case 1n+g ST.TE{}:
      {==}
    case 1n+g ST.TN{+i, +tl, +tr}:
      +ihl = sl(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, g, tl, i, True{}, k, rep_l(~K, i, tl, tr, p, nl, hr), ht_l(i, tl, tr, g, hf))
      +ihr = sl(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, g, tr, i, False{}, k, rep_r(~K, i, tl, tr, p, nl, hr), ht_r(i, tl, tr, g, hf))
      sl_node(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, i, tl, tr, p, left, k, g, ST.nd(K, nl, i), rep_node(~K, i, tl, tr, p, nl, hr), ihl, ihr)
