import Base
import ../../../src/containers/balanced_search_tree.bend as M
import ./state.bend as ST
import ./mirror.bend as MI
import ./tree.bend as TR
import ./nbr.bend as NB

# The extremes the deletion reads: from an id the mirror's walk is the
# node-list walk, so from a node the path leads to it reaches the first
# (backward) or last (forward) id of its subtree, and refreshing the ends
# puts the tree's first and last ids in the header.
# (source: tools/generators/tm_hand/xtr.src)


def ext_eq(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +fuel: Nat, +fw: Bool, +id: Nat, +next: Nat) -> {MI.extreme_loop(~K, ~V, ~cmp, fuel, fw, id, (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, next)) == (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, MI.ext_loop(~K, fuel, nl, fw, id, next)) : ST.Sh<K, V> & Nat}:
  match fuel next:
    case 0n 0n:
      {==}
    case 0n 1n+j:
      {==}
    case 1n+f 0n:
      {==}
    case 1n+f 1n+j:
      ext_eq(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, f, fw, 1n+j, M.child(~K, ST.nd(K, nl, 1n+j), fw))

def extreme_m(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +id: Nat, +fw: Bool) -> {MI.extreme(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, id, fw) == (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, MI.ext_loop(~K, 1n+n, nl, fw, id, M.child(~K, ST.nd(K, nl, id), fw))) : ST.Sh<K, V> & Nat}:
  ext_eq(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, 1n+n, fw, id, M.child(~K, ST.nd(K, nl, id), fw))


# refreshing the ends of a linked tree
def refresh_m(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +n: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +t: ST.Tr, +hr: {ST.rep(~K, t, 0n, nl) == True{} : Bool}, +hf: {Nat.is_lt(TR.ht(t), 1n+n) == True{} : Bool}) -> {MI.refresh_ends(~K, ~V, ~cmp, ST.SH{n, ST.rid(t), lo, hi, free, l, d, nl, pl, tg, fl}) == ST.SH{n, ST.rid(t), ST.fst0(ST.ids(t)), ST.last0(ST.ids(t)), free, l, d, nl, pl, tg, fl} : ST.Sh<K, V>}:
  match t:
    case ST.TE{}:
      {==}
    case ST.TN{+j, +a, +b}:
      %Equal.sym(ST.Sh<K, V> & Nat, MI.extreme(~K, ~V, ~cmp, ST.SH{n, j, lo, hi, free, l, d, nl, pl, tg, fl}, j, False{}), (ST.SH{n, j, lo, hi, free, l, d, nl, pl, tg, fl}, MI.ext_loop(~K, 1n+n, nl, False{}, j, M.child(~K, ST.nd(K, nl, j), False{}))), extreme_m(~K, ~V, ~cmp, n, j, lo, hi, free, l, d, nl, pl, tg, fl, j, False{})) : {MI.refresh_ends_2(~K, ~V, ~cmp, j, _) == ST.SH{n, j, ST.fst0(ST.ids(ST.TN{j, a, b})), ST.last0(ST.ids(ST.TN{j, a, b})), free, l, d, nl, pl, tg, fl} : ST.Sh<K, V>}
      %Equal.sym(Nat, MI.ext_loop(~K, 1n+n, nl, False{}, j, M.child(~K, ST.nd(K, nl, j), False{})), ST.fst0(ST.ids(ST.TN{j, a, b})), NB.ext_l(~K, nl, 1n+n, j, a, b, 0n, hr, hf)) : {MI.refresh_ends_2(~K, ~V, ~cmp, j, (ST.SH{n, j, lo, hi, free, l, d, nl, pl, tg, fl}, _)) == ST.SH{n, j, ST.fst0(ST.ids(ST.TN{j, a, b})), ST.last0(ST.ids(ST.TN{j, a, b})), free, l, d, nl, pl, tg, fl} : ST.Sh<K, V>}
      %Equal.sym(ST.Sh<K, V> & Nat, MI.extreme(~K, ~V, ~cmp, ST.SH{n, j, lo, hi, free, l, d, nl, pl, tg, fl}, j, True{}), (ST.SH{n, j, lo, hi, free, l, d, nl, pl, tg, fl}, MI.ext_loop(~K, 1n+n, nl, True{}, j, M.child(~K, ST.nd(K, nl, j), True{}))), extreme_m(~K, ~V, ~cmp, n, j, lo, hi, free, l, d, nl, pl, tg, fl, j, True{})) : {MI.refresh_ends_3(~K, ~V, ~cmp, ST.fst0(ST.ids(ST.TN{j, a, b})), _) == ST.SH{n, j, ST.fst0(ST.ids(ST.TN{j, a, b})), ST.last0(ST.ids(ST.TN{j, a, b})), free, l, d, nl, pl, tg, fl} : ST.Sh<K, V>}
      %Equal.sym(Nat, MI.ext_loop(~K, 1n+n, nl, True{}, j, M.child(~K, ST.nd(K, nl, j), True{})), ST.last0(ST.ids(ST.TN{j, a, b})), NB.ext_r(~K, nl, 1n+n, j, a, b, 0n, hr, hf)) : {MI.refresh_ends_3(~K, ~V, ~cmp, ST.fst0(ST.ids(ST.TN{j, a, b})), (ST.SH{n, j, lo, hi, free, l, d, nl, pl, tg, fl}, _)) == ST.SH{n, j, ST.fst0(ST.ids(ST.TN{j, a, b})), ST.last0(ST.ids(ST.TN{j, a, b})), free, l, d, nl, pl, tg, fl} : ST.Sh<K, V>}
      {==}
