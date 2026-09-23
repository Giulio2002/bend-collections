import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/order.bend as O
import ../spec/common.bend as SC
import ../../src/containers/balanced_search_tree.bend as M
import ../hash_table/state.bend as HT
import ./state.bend as ST
import ./prim.bend as PR
import ./mirror.bend as MI
import ./frame.bend as FR
import ./agree.bend as AG
import ../spec/tree_map.bend as S
import ./ends.bend as EN

# The mirror's node setters as functions of the node list: each rewrites one
# field of an id's node (nothing for a free or absent node). The written
# node, the length, and agreement off the id.
# (source: tools/generators/tm_hand/setters.src)


# ---- left ----

def setl_n(-K: Data, +nl: List<&2, M.Node<K>>, +id: Nat, +v: Nat, x: M.Node<K>) -> List<&2, M.Node<K>>:
  match x:
    case M.Free{f}:
      nl
    case M.N{+c, +a, +b, +q, +k}:
      PR.wr_nl(K, nl, id, M.N{c, v, b, q, k})

def setl(-K: Data, +nl: List<&2, M.Node<K>>, +id: Nat, +v: Nat) -> List<&2, M.Node<K>>:
  setl_n(K, nl, id, v, ST.nd(K, nl, id))

def set_left_node_m(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +id: Nat, +v: Nat, +x: M.Node<K>) -> {MI.set_left_node(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, id, v, x) == ST.SH{n, root, lo, hi, free, l, d, setl_n(K, nl, id, v, x), pl, tg, fl} : ST.Sh<K, V>}:
  match x:
    case M.Free{f}:
      {==}
    case M.N{c, a, b, q, k}:
      {==}

def set_left_m(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +id: Nat, +v: Nat) -> {MI.set_left(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, id, v) == ST.SH{n, root, lo, hi, free, l, d, setl(K, nl, id, v), pl, tg, fl} : ST.Sh<K, V>}:
  set_left_node_m(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, id, v, ST.nd(K, nl, id))

def setl_same(-K: Data, +nl: List<&2, M.Node<K>>, +i: Nat, +v: Nat, +c: Bool, +a: Nat, +b: Nat, +q: Nat, +k: K, +hx: {ST.nd(K, nl, 1n+i) == M.N{c, a, b, q, k} : M.Node<K>}, +hi: {Nat.is_lt(i, SC.length(M.Node<K>, nl)) == True{} : Bool}) -> {ST.nd(K, setl(K, nl, 1n+i, v), 1n+i) == M.N{c, v, b, q, k} : M.Node<K>}:
  %Equal.sym(M.Node<K>, ST.nd(K, nl, 1n+i), M.N{c, a, b, q, k}, hx) : {ST.nd(K, setl_n(K, nl, 1n+i, v, _), 1n+i) == M.N{c, v, b, q, k} : M.Node<K>}
  FR.nd_wr_same(K, nl, i, M.N{c, v, b, q, k}, hi)

def setl_n_len(-K: Data, +nl: List<&2, M.Node<K>>, +id: Nat, +v: Nat, +x: M.Node<K>) -> {SC.length(M.Node<K>, setl_n(K, nl, id, v, x)) == SC.length(M.Node<K>, nl) : Nat}:
  match x:
    case M.Free{f}:
      {==}
    case M.N{+c, +a, +b, +q, +k}:
      FR.len_wr(K, nl, id, M.N{c, v, b, q, k})

def setl_len(-K: Data, +nl: List<&2, M.Node<K>>, +id: Nat, +v: Nat) -> {SC.length(M.Node<K>, setl(K, nl, id, v)) == SC.length(M.Node<K>, nl) : Nat}:
  setl_n_len(K, nl, id, v, ST.nd(K, nl, id))

def setl_n_agr(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +xs: List<&2, Nat>, +nl: List<&2, M.Node<K>>, +id: Nat, +v: Nat, +x: M.Node<K>, +hn: {HT.memn(id, xs) == False{} : Bool}) -> {AG.agr(~K, ~cmp, xs, nl, setl_n(K, nl, id, v, x)) == True{} : Bool}:
  match x:
    case M.Free{f}:
      AG.agr_refl(~K, ~cmp, ~o, xs, nl)
    case M.N{+c, +a, +b, +q, +k}:
      AG.agr_wr(~K, ~cmp, ~o, xs, nl, id, M.N{c, v, b, q, k}, hn)

# agreement off the written id
def setl_agr(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +xs: List<&2, Nat>, +nl: List<&2, M.Node<K>>, +id: Nat, +v: Nat, +hn: {HT.memn(id, xs) == False{} : Bool}) -> {AG.agr(~K, ~cmp, xs, nl, setl(K, nl, id, v)) == True{} : Bool}:
  setl_n_agr(~K, ~cmp, ~o, xs, nl, id, v, ST.nd(K, nl, id), hn)

# ---- right ----

def setr_n(-K: Data, +nl: List<&2, M.Node<K>>, +id: Nat, +v: Nat, x: M.Node<K>) -> List<&2, M.Node<K>>:
  match x:
    case M.Free{f}:
      nl
    case M.N{+c, +a, +b, +q, +k}:
      PR.wr_nl(K, nl, id, M.N{c, a, v, q, k})

def setr(-K: Data, +nl: List<&2, M.Node<K>>, +id: Nat, +v: Nat) -> List<&2, M.Node<K>>:
  setr_n(K, nl, id, v, ST.nd(K, nl, id))

def set_right_node_m(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +id: Nat, +v: Nat, +x: M.Node<K>) -> {MI.set_right_node(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, id, v, x) == ST.SH{n, root, lo, hi, free, l, d, setr_n(K, nl, id, v, x), pl, tg, fl} : ST.Sh<K, V>}:
  match x:
    case M.Free{f}:
      {==}
    case M.N{c, a, b, q, k}:
      {==}

def set_right_m(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +id: Nat, +v: Nat) -> {MI.set_right(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, id, v) == ST.SH{n, root, lo, hi, free, l, d, setr(K, nl, id, v), pl, tg, fl} : ST.Sh<K, V>}:
  set_right_node_m(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, id, v, ST.nd(K, nl, id))

def setr_same(-K: Data, +nl: List<&2, M.Node<K>>, +i: Nat, +v: Nat, +c: Bool, +a: Nat, +b: Nat, +q: Nat, +k: K, +hx: {ST.nd(K, nl, 1n+i) == M.N{c, a, b, q, k} : M.Node<K>}, +hi: {Nat.is_lt(i, SC.length(M.Node<K>, nl)) == True{} : Bool}) -> {ST.nd(K, setr(K, nl, 1n+i, v), 1n+i) == M.N{c, a, v, q, k} : M.Node<K>}:
  %Equal.sym(M.Node<K>, ST.nd(K, nl, 1n+i), M.N{c, a, b, q, k}, hx) : {ST.nd(K, setr_n(K, nl, 1n+i, v, _), 1n+i) == M.N{c, a, v, q, k} : M.Node<K>}
  FR.nd_wr_same(K, nl, i, M.N{c, a, v, q, k}, hi)

def setr_n_len(-K: Data, +nl: List<&2, M.Node<K>>, +id: Nat, +v: Nat, +x: M.Node<K>) -> {SC.length(M.Node<K>, setr_n(K, nl, id, v, x)) == SC.length(M.Node<K>, nl) : Nat}:
  match x:
    case M.Free{f}:
      {==}
    case M.N{+c, +a, +b, +q, +k}:
      FR.len_wr(K, nl, id, M.N{c, a, v, q, k})

def setr_len(-K: Data, +nl: List<&2, M.Node<K>>, +id: Nat, +v: Nat) -> {SC.length(M.Node<K>, setr(K, nl, id, v)) == SC.length(M.Node<K>, nl) : Nat}:
  setr_n_len(K, nl, id, v, ST.nd(K, nl, id))

def setr_n_agr(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +xs: List<&2, Nat>, +nl: List<&2, M.Node<K>>, +id: Nat, +v: Nat, +x: M.Node<K>, +hn: {HT.memn(id, xs) == False{} : Bool}) -> {AG.agr(~K, ~cmp, xs, nl, setr_n(K, nl, id, v, x)) == True{} : Bool}:
  match x:
    case M.Free{f}:
      AG.agr_refl(~K, ~cmp, ~o, xs, nl)
    case M.N{+c, +a, +b, +q, +k}:
      AG.agr_wr(~K, ~cmp, ~o, xs, nl, id, M.N{c, a, v, q, k}, hn)

# agreement off the written id
def setr_agr(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +xs: List<&2, Nat>, +nl: List<&2, M.Node<K>>, +id: Nat, +v: Nat, +hn: {HT.memn(id, xs) == False{} : Bool}) -> {AG.agr(~K, ~cmp, xs, nl, setr(K, nl, id, v)) == True{} : Bool}:
  setr_n_agr(~K, ~cmp, ~o, xs, nl, id, v, ST.nd(K, nl, id), hn)

# ---- parent ----

def setp_n(-K: Data, +nl: List<&2, M.Node<K>>, +id: Nat, +v: Nat, x: M.Node<K>) -> List<&2, M.Node<K>>:
  match x:
    case M.Free{f}:
      nl
    case M.N{+c, +a, +b, +q, +k}:
      PR.wr_nl(K, nl, id, M.N{c, a, b, v, k})

def setp(-K: Data, +nl: List<&2, M.Node<K>>, +id: Nat, +v: Nat) -> List<&2, M.Node<K>>:
  setp_n(K, nl, id, v, ST.nd(K, nl, id))

def set_parent_node_m(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +id: Nat, +v: Nat, +x: M.Node<K>) -> {MI.set_parent_node(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, id, v, x) == ST.SH{n, root, lo, hi, free, l, d, setp_n(K, nl, id, v, x), pl, tg, fl} : ST.Sh<K, V>}:
  match x:
    case M.Free{f}:
      {==}
    case M.N{c, a, b, q, k}:
      {==}

def set_parent_m(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +id: Nat, +v: Nat) -> {MI.set_parent(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, id, v) == ST.SH{n, root, lo, hi, free, l, d, setp(K, nl, id, v), pl, tg, fl} : ST.Sh<K, V>}:
  set_parent_node_m(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, id, v, ST.nd(K, nl, id))

def setp_same(-K: Data, +nl: List<&2, M.Node<K>>, +i: Nat, +v: Nat, +c: Bool, +a: Nat, +b: Nat, +q: Nat, +k: K, +hx: {ST.nd(K, nl, 1n+i) == M.N{c, a, b, q, k} : M.Node<K>}, +hi: {Nat.is_lt(i, SC.length(M.Node<K>, nl)) == True{} : Bool}) -> {ST.nd(K, setp(K, nl, 1n+i, v), 1n+i) == M.N{c, a, b, v, k} : M.Node<K>}:
  %Equal.sym(M.Node<K>, ST.nd(K, nl, 1n+i), M.N{c, a, b, q, k}, hx) : {ST.nd(K, setp_n(K, nl, 1n+i, v, _), 1n+i) == M.N{c, a, b, v, k} : M.Node<K>}
  FR.nd_wr_same(K, nl, i, M.N{c, a, b, v, k}, hi)

def setp_n_len(-K: Data, +nl: List<&2, M.Node<K>>, +id: Nat, +v: Nat, +x: M.Node<K>) -> {SC.length(M.Node<K>, setp_n(K, nl, id, v, x)) == SC.length(M.Node<K>, nl) : Nat}:
  match x:
    case M.Free{f}:
      {==}
    case M.N{+c, +a, +b, +q, +k}:
      FR.len_wr(K, nl, id, M.N{c, a, b, v, k})

def setp_len(-K: Data, +nl: List<&2, M.Node<K>>, +id: Nat, +v: Nat) -> {SC.length(M.Node<K>, setp(K, nl, id, v)) == SC.length(M.Node<K>, nl) : Nat}:
  setp_n_len(K, nl, id, v, ST.nd(K, nl, id))

def setp_n_agr(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +xs: List<&2, Nat>, +nl: List<&2, M.Node<K>>, +id: Nat, +v: Nat, +x: M.Node<K>, +hn: {HT.memn(id, xs) == False{} : Bool}) -> {AG.agr(~K, ~cmp, xs, nl, setp_n(K, nl, id, v, x)) == True{} : Bool}:
  match x:
    case M.Free{f}:
      AG.agr_refl(~K, ~cmp, ~o, xs, nl)
    case M.N{+c, +a, +b, +q, +k}:
      AG.agr_wr(~K, ~cmp, ~o, xs, nl, id, M.N{c, a, b, v, k}, hn)

# agreement off the written id
def setp_agr(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +xs: List<&2, Nat>, +nl: List<&2, M.Node<K>>, +id: Nat, +v: Nat, +hn: {HT.memn(id, xs) == False{} : Bool}) -> {AG.agr(~K, ~cmp, xs, nl, setp(K, nl, id, v)) == True{} : Bool}:
  setp_n_agr(~K, ~cmp, ~o, xs, nl, id, v, ST.nd(K, nl, id), hn)

# ---- red ----

def setc_n(-K: Data, +nl: List<&2, M.Node<K>>, +id: Nat, +v: Bool, x: M.Node<K>) -> List<&2, M.Node<K>>:
  match x:
    case M.Free{f}:
      nl
    case M.N{+c, +a, +b, +q, +k}:
      PR.wr_nl(K, nl, id, M.N{v, a, b, q, k})

def setc(-K: Data, +nl: List<&2, M.Node<K>>, +id: Nat, +v: Bool) -> List<&2, M.Node<K>>:
  setc_n(K, nl, id, v, ST.nd(K, nl, id))

def set_red_node_m(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +id: Nat, +v: Bool, +x: M.Node<K>) -> {MI.set_red_node(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, id, v, x) == ST.SH{n, root, lo, hi, free, l, d, setc_n(K, nl, id, v, x), pl, tg, fl} : ST.Sh<K, V>}:
  match x:
    case M.Free{f}:
      {==}
    case M.N{c, a, b, q, k}:
      {==}

def set_red_m(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +id: Nat, +v: Bool) -> {MI.set_red(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, id, v) == ST.SH{n, root, lo, hi, free, l, d, setc(K, nl, id, v), pl, tg, fl} : ST.Sh<K, V>}:
  set_red_node_m(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, id, v, ST.nd(K, nl, id))

def setc_same(-K: Data, +nl: List<&2, M.Node<K>>, +i: Nat, +v: Bool, +c: Bool, +a: Nat, +b: Nat, +q: Nat, +k: K, +hx: {ST.nd(K, nl, 1n+i) == M.N{c, a, b, q, k} : M.Node<K>}, +hi: {Nat.is_lt(i, SC.length(M.Node<K>, nl)) == True{} : Bool}) -> {ST.nd(K, setc(K, nl, 1n+i, v), 1n+i) == M.N{v, a, b, q, k} : M.Node<K>}:
  %Equal.sym(M.Node<K>, ST.nd(K, nl, 1n+i), M.N{c, a, b, q, k}, hx) : {ST.nd(K, setc_n(K, nl, 1n+i, v, _), 1n+i) == M.N{v, a, b, q, k} : M.Node<K>}
  FR.nd_wr_same(K, nl, i, M.N{v, a, b, q, k}, hi)

def setc_n_len(-K: Data, +nl: List<&2, M.Node<K>>, +id: Nat, +v: Bool, +x: M.Node<K>) -> {SC.length(M.Node<K>, setc_n(K, nl, id, v, x)) == SC.length(M.Node<K>, nl) : Nat}:
  match x:
    case M.Free{f}:
      {==}
    case M.N{+c, +a, +b, +q, +k}:
      FR.len_wr(K, nl, id, M.N{v, a, b, q, k})

def setc_len(-K: Data, +nl: List<&2, M.Node<K>>, +id: Nat, +v: Bool) -> {SC.length(M.Node<K>, setc(K, nl, id, v)) == SC.length(M.Node<K>, nl) : Nat}:
  setc_n_len(K, nl, id, v, ST.nd(K, nl, id))

def setc_n_agr(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +xs: List<&2, Nat>, +nl: List<&2, M.Node<K>>, +id: Nat, +v: Bool, +x: M.Node<K>, +hn: {HT.memn(id, xs) == False{} : Bool}) -> {AG.agr(~K, ~cmp, xs, nl, setc_n(K, nl, id, v, x)) == True{} : Bool}:
  match x:
    case M.Free{f}:
      AG.agr_refl(~K, ~cmp, ~o, xs, nl)
    case M.N{+c, +a, +b, +q, +k}:
      AG.agr_wr(~K, ~cmp, ~o, xs, nl, id, M.N{v, a, b, q, k}, hn)

# agreement off the written id
def setc_agr(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +xs: List<&2, Nat>, +nl: List<&2, M.Node<K>>, +id: Nat, +v: Bool, +hn: {HT.memn(id, xs) == False{} : Bool}) -> {AG.agr(~K, ~cmp, xs, nl, setc(K, nl, id, v)) == True{} : Bool}:
  setc_n_agr(~K, ~cmp, ~o, xs, nl, id, v, ST.nd(K, nl, id), hn)

# ---- every id's node after a setter ----

def fn_c(-K: Data, +c: Bool, +a: Nat, +b: Nat, +q: Nat, +k: K, +e: {M.Free{0n} == M.N{c, a, b, q, k} : M.Node<K>}) -> Empty:
  L.true_false(L.subst(M.Node<K>, z => {ST.is_free(K, M.Free{0n}, 0n) == ST.is_free(K, z, 0n) : Bool}, M.Free{0n}, M.N{c, a, b, q, k}, e, {==}))

def nr_c(-K: Data, +nl: List<&2, M.Node<K>>, +i: Nat, +c: Bool, +a: Nat, +b: Nat, +q: Nat, +k: K, +hx: {ST.nd(K, nl, 1n+i) == M.N{c, a, b, q, k} : M.Node<K>}, +t: Bool, +ht: {Nat.is_lt(i, SC.length(M.Node<K>, nl)) == t : Bool}) -> {t == True{} : Bool}:
  match t:
    case True{}:
      {==}
    case False{}:
      +e = Equal.trans(M.Node<K>, M.Free{0n}, ST.nd(K, nl, 1n+i), M.N{c, a, b, q, k}, Equal.sym(M.Node<K>, ST.nd(K, nl, 1n+i), M.Free{0n}, PR.nth_hi(M.Node<K>, nl, i, M.Free{0n}, ht)), hx)
      Empty.absurd({False{} == True{} : Bool}, fn_c(K, c, a, b, q, k, e))

def nd_n_range(-K: Data, +nl: List<&2, M.Node<K>>, +i: Nat, +c: Bool, +a: Nat, +b: Nat, +q: Nat, +k: K, +hx: {ST.nd(K, nl, 1n+i) == M.N{c, a, b, q, k} : M.Node<K>}) -> {Nat.is_lt(i, SC.length(M.Node<K>, nl)) == True{} : Bool}:
  nr_c(K, nl, i, c, a, b, q, k, hx, Nat.is_lt(i, SC.length(M.Node<K>, nl)), {==})

def modl(-K: Data, x: M.Node<K>, +v: Nat) -> M.Node<K>:
  match x:
    case M.Free{+f}:
      M.Free{f}
    case M.N{+c, +a, +b, +q, +k}:
      M.N{c, v, b, q, k}

def wsame_l(-K: Data, +nl: List<&2, M.Node<K>>, +id: Nat, +v: Nat, +c: Bool, +a: Nat, +b: Nat, +q: Nat, +k: K, +hx: {ST.nd(K, nl, id) == M.N{c, a, b, q, k} : M.Node<K>}) -> {ST.nd(K, PR.wr_nl(K, nl, id, M.N{c, v, b, q, k}), id) == M.N{c, v, b, q, k} : M.Node<K>}:
  match id:
    case 0n:
      Empty.absurd({ST.nd(K, PR.wr_nl(K, nl, 0n, M.N{c, v, b, q, k}), 0n) == M.N{c, v, b, q, k} : M.Node<K>}, fn_c(K, c, a, b, q, k, hx))
    case 1n+i:
      FR.nd_wr_same(K, nl, i, M.N{c, v, b, q, k}, nd_n_range(K, nl, i, c, a, b, q, k, hx))

def ndl_c(-K: Data, +nl: List<&2, M.Node<K>>, +id: Nat, +v: Nat, +j: Nat, +x: M.Node<K>, +hx: {ST.nd(K, nl, id) == x : M.Node<K>}, +e: Bool, +he: {Nat.is_eq(id, j) == e : Bool}) -> {ST.nd(K, setl_n(K, nl, id, v, x), j) == ST.pk(M.Node<K>, e, modl(K, ST.nd(K, nl, j), v), ST.nd(K, nl, j)) : M.Node<K>}:
  match x e:
    case M.Free{f} True{}:
      +ej = N.eq_from_is_eq(id, j, he)
      %Equal.sym(Nat, j, id, Equal.sym(Nat, id, j, ej)) : {ST.nd(K, nl, _) == modl(K, ST.nd(K, nl, _), v) : M.Node<K>}
      %Equal.sym(M.Node<K>, ST.nd(K, nl, id), M.Free{f}, hx) : {_ == modl(K, _, v) : M.Node<K>}
      {==}
    case M.Free{f} False{}:
      {==}
    case M.N{+c, +a, +b, +q, +k} True{}:
      +ej = N.eq_from_is_eq(id, j, he)
      %Equal.sym(Nat, j, id, Equal.sym(Nat, id, j, ej)) : {ST.nd(K, PR.wr_nl(K, nl, id, M.N{c, v, b, q, k}), _) == modl(K, ST.nd(K, nl, _), v) : M.Node<K>}
      %Equal.sym(M.Node<K>, ST.nd(K, nl, id), M.N{c, a, b, q, k}, hx) : {ST.nd(K, PR.wr_nl(K, nl, id, M.N{c, v, b, q, k}), id) == modl(K, _, v) : M.Node<K>}
      wsame_l(K, nl, id, v, c, a, b, q, k, hx)
    case M.N{+c, +a, +b, +q, +k} False{}:
      FR.nd_wr_other(K, nl, id, M.N{c, v, b, q, k}, j, he)

# the node at j after setting id: modified when j is id
def ndl(-K: Data, +nl: List<&2, M.Node<K>>, +id: Nat, +v: Nat, +j: Nat) -> {ST.nd(K, setl(K, nl, id, v), j) == ST.pk(M.Node<K>, Nat.is_eq(id, j), modl(K, ST.nd(K, nl, j), v), ST.nd(K, nl, j)) : M.Node<K>}:
  ndl_c(K, nl, id, v, j, ST.nd(K, nl, id), {==}, Nat.is_eq(id, j), {==})

def modr(-K: Data, x: M.Node<K>, +v: Nat) -> M.Node<K>:
  match x:
    case M.Free{+f}:
      M.Free{f}
    case M.N{+c, +a, +b, +q, +k}:
      M.N{c, a, v, q, k}

def wsame_r(-K: Data, +nl: List<&2, M.Node<K>>, +id: Nat, +v: Nat, +c: Bool, +a: Nat, +b: Nat, +q: Nat, +k: K, +hx: {ST.nd(K, nl, id) == M.N{c, a, b, q, k} : M.Node<K>}) -> {ST.nd(K, PR.wr_nl(K, nl, id, M.N{c, a, v, q, k}), id) == M.N{c, a, v, q, k} : M.Node<K>}:
  match id:
    case 0n:
      Empty.absurd({ST.nd(K, PR.wr_nl(K, nl, 0n, M.N{c, a, v, q, k}), 0n) == M.N{c, a, v, q, k} : M.Node<K>}, fn_c(K, c, a, b, q, k, hx))
    case 1n+i:
      FR.nd_wr_same(K, nl, i, M.N{c, a, v, q, k}, nd_n_range(K, nl, i, c, a, b, q, k, hx))

def ndr_c(-K: Data, +nl: List<&2, M.Node<K>>, +id: Nat, +v: Nat, +j: Nat, +x: M.Node<K>, +hx: {ST.nd(K, nl, id) == x : M.Node<K>}, +e: Bool, +he: {Nat.is_eq(id, j) == e : Bool}) -> {ST.nd(K, setr_n(K, nl, id, v, x), j) == ST.pk(M.Node<K>, e, modr(K, ST.nd(K, nl, j), v), ST.nd(K, nl, j)) : M.Node<K>}:
  match x e:
    case M.Free{f} True{}:
      +ej = N.eq_from_is_eq(id, j, he)
      %Equal.sym(Nat, j, id, Equal.sym(Nat, id, j, ej)) : {ST.nd(K, nl, _) == modr(K, ST.nd(K, nl, _), v) : M.Node<K>}
      %Equal.sym(M.Node<K>, ST.nd(K, nl, id), M.Free{f}, hx) : {_ == modr(K, _, v) : M.Node<K>}
      {==}
    case M.Free{f} False{}:
      {==}
    case M.N{+c, +a, +b, +q, +k} True{}:
      +ej = N.eq_from_is_eq(id, j, he)
      %Equal.sym(Nat, j, id, Equal.sym(Nat, id, j, ej)) : {ST.nd(K, PR.wr_nl(K, nl, id, M.N{c, a, v, q, k}), _) == modr(K, ST.nd(K, nl, _), v) : M.Node<K>}
      %Equal.sym(M.Node<K>, ST.nd(K, nl, id), M.N{c, a, b, q, k}, hx) : {ST.nd(K, PR.wr_nl(K, nl, id, M.N{c, a, v, q, k}), id) == modr(K, _, v) : M.Node<K>}
      wsame_r(K, nl, id, v, c, a, b, q, k, hx)
    case M.N{+c, +a, +b, +q, +k} False{}:
      FR.nd_wr_other(K, nl, id, M.N{c, a, v, q, k}, j, he)

# the node at j after setting id: modified when j is id
def ndr(-K: Data, +nl: List<&2, M.Node<K>>, +id: Nat, +v: Nat, +j: Nat) -> {ST.nd(K, setr(K, nl, id, v), j) == ST.pk(M.Node<K>, Nat.is_eq(id, j), modr(K, ST.nd(K, nl, j), v), ST.nd(K, nl, j)) : M.Node<K>}:
  ndr_c(K, nl, id, v, j, ST.nd(K, nl, id), {==}, Nat.is_eq(id, j), {==})

def modp(-K: Data, x: M.Node<K>, +v: Nat) -> M.Node<K>:
  match x:
    case M.Free{+f}:
      M.Free{f}
    case M.N{+c, +a, +b, +q, +k}:
      M.N{c, a, b, v, k}

def wsame_p(-K: Data, +nl: List<&2, M.Node<K>>, +id: Nat, +v: Nat, +c: Bool, +a: Nat, +b: Nat, +q: Nat, +k: K, +hx: {ST.nd(K, nl, id) == M.N{c, a, b, q, k} : M.Node<K>}) -> {ST.nd(K, PR.wr_nl(K, nl, id, M.N{c, a, b, v, k}), id) == M.N{c, a, b, v, k} : M.Node<K>}:
  match id:
    case 0n:
      Empty.absurd({ST.nd(K, PR.wr_nl(K, nl, 0n, M.N{c, a, b, v, k}), 0n) == M.N{c, a, b, v, k} : M.Node<K>}, fn_c(K, c, a, b, q, k, hx))
    case 1n+i:
      FR.nd_wr_same(K, nl, i, M.N{c, a, b, v, k}, nd_n_range(K, nl, i, c, a, b, q, k, hx))

def ndp_c(-K: Data, +nl: List<&2, M.Node<K>>, +id: Nat, +v: Nat, +j: Nat, +x: M.Node<K>, +hx: {ST.nd(K, nl, id) == x : M.Node<K>}, +e: Bool, +he: {Nat.is_eq(id, j) == e : Bool}) -> {ST.nd(K, setp_n(K, nl, id, v, x), j) == ST.pk(M.Node<K>, e, modp(K, ST.nd(K, nl, j), v), ST.nd(K, nl, j)) : M.Node<K>}:
  match x e:
    case M.Free{f} True{}:
      +ej = N.eq_from_is_eq(id, j, he)
      %Equal.sym(Nat, j, id, Equal.sym(Nat, id, j, ej)) : {ST.nd(K, nl, _) == modp(K, ST.nd(K, nl, _), v) : M.Node<K>}
      %Equal.sym(M.Node<K>, ST.nd(K, nl, id), M.Free{f}, hx) : {_ == modp(K, _, v) : M.Node<K>}
      {==}
    case M.Free{f} False{}:
      {==}
    case M.N{+c, +a, +b, +q, +k} True{}:
      +ej = N.eq_from_is_eq(id, j, he)
      %Equal.sym(Nat, j, id, Equal.sym(Nat, id, j, ej)) : {ST.nd(K, PR.wr_nl(K, nl, id, M.N{c, a, b, v, k}), _) == modp(K, ST.nd(K, nl, _), v) : M.Node<K>}
      %Equal.sym(M.Node<K>, ST.nd(K, nl, id), M.N{c, a, b, q, k}, hx) : {ST.nd(K, PR.wr_nl(K, nl, id, M.N{c, a, b, v, k}), id) == modp(K, _, v) : M.Node<K>}
      wsame_p(K, nl, id, v, c, a, b, q, k, hx)
    case M.N{+c, +a, +b, +q, +k} False{}:
      FR.nd_wr_other(K, nl, id, M.N{c, a, b, v, k}, j, he)

# the node at j after setting id: modified when j is id
def ndp(-K: Data, +nl: List<&2, M.Node<K>>, +id: Nat, +v: Nat, +j: Nat) -> {ST.nd(K, setp(K, nl, id, v), j) == ST.pk(M.Node<K>, Nat.is_eq(id, j), modp(K, ST.nd(K, nl, j), v), ST.nd(K, nl, j)) : M.Node<K>}:
  ndp_c(K, nl, id, v, j, ST.nd(K, nl, id), {==}, Nat.is_eq(id, j), {==})

def modc(-K: Data, x: M.Node<K>, +v: Bool) -> M.Node<K>:
  match x:
    case M.Free{+f}:
      M.Free{f}
    case M.N{+c, +a, +b, +q, +k}:
      M.N{v, a, b, q, k}

def wsame_c(-K: Data, +nl: List<&2, M.Node<K>>, +id: Nat, +v: Bool, +c: Bool, +a: Nat, +b: Nat, +q: Nat, +k: K, +hx: {ST.nd(K, nl, id) == M.N{c, a, b, q, k} : M.Node<K>}) -> {ST.nd(K, PR.wr_nl(K, nl, id, M.N{v, a, b, q, k}), id) == M.N{v, a, b, q, k} : M.Node<K>}:
  match id:
    case 0n:
      Empty.absurd({ST.nd(K, PR.wr_nl(K, nl, 0n, M.N{v, a, b, q, k}), 0n) == M.N{v, a, b, q, k} : M.Node<K>}, fn_c(K, c, a, b, q, k, hx))
    case 1n+i:
      FR.nd_wr_same(K, nl, i, M.N{v, a, b, q, k}, nd_n_range(K, nl, i, c, a, b, q, k, hx))

def ndc_c(-K: Data, +nl: List<&2, M.Node<K>>, +id: Nat, +v: Bool, +j: Nat, +x: M.Node<K>, +hx: {ST.nd(K, nl, id) == x : M.Node<K>}, +e: Bool, +he: {Nat.is_eq(id, j) == e : Bool}) -> {ST.nd(K, setc_n(K, nl, id, v, x), j) == ST.pk(M.Node<K>, e, modc(K, ST.nd(K, nl, j), v), ST.nd(K, nl, j)) : M.Node<K>}:
  match x e:
    case M.Free{f} True{}:
      +ej = N.eq_from_is_eq(id, j, he)
      %Equal.sym(Nat, j, id, Equal.sym(Nat, id, j, ej)) : {ST.nd(K, nl, _) == modc(K, ST.nd(K, nl, _), v) : M.Node<K>}
      %Equal.sym(M.Node<K>, ST.nd(K, nl, id), M.Free{f}, hx) : {_ == modc(K, _, v) : M.Node<K>}
      {==}
    case M.Free{f} False{}:
      {==}
    case M.N{+c, +a, +b, +q, +k} True{}:
      +ej = N.eq_from_is_eq(id, j, he)
      %Equal.sym(Nat, j, id, Equal.sym(Nat, id, j, ej)) : {ST.nd(K, PR.wr_nl(K, nl, id, M.N{v, a, b, q, k}), _) == modc(K, ST.nd(K, nl, _), v) : M.Node<K>}
      %Equal.sym(M.Node<K>, ST.nd(K, nl, id), M.N{c, a, b, q, k}, hx) : {ST.nd(K, PR.wr_nl(K, nl, id, M.N{v, a, b, q, k}), id) == modc(K, _, v) : M.Node<K>}
      wsame_c(K, nl, id, v, c, a, b, q, k, hx)
    case M.N{+c, +a, +b, +q, +k} False{}:
      FR.nd_wr_other(K, nl, id, M.N{v, a, b, q, k}, j, he)

# the node at j after setting id: modified when j is id
def ndc(-K: Data, +nl: List<&2, M.Node<K>>, +id: Nat, +v: Bool, +j: Nat) -> {ST.nd(K, setc(K, nl, id, v), j) == ST.pk(M.Node<K>, Nat.is_eq(id, j), modc(K, ST.nd(K, nl, j), v), ST.nd(K, nl, j)) : M.Node<K>}:
  ndc_c(K, nl, id, v, j, ST.nd(K, nl, id), {==}, Nat.is_eq(id, j), {==})

# ---- what setters keep everywhere ----


def ent_modl(-K: Data, -V: Data, +x: M.Node<K>, +v: Nat, +m: Maybe<&2, V>) -> {ST.ent(K, V, modl(K, x, v), m) == ST.ent(K, V, x, m) : Maybe<&2, M.Entry<K, V>>}:
  match x m:
    case M.Free{f} +m:
      {==}
    case M.N{c, a, b, q, k} None{}:
      {==}
    case M.N{c, a, b, q, k} Some{w}:
      {==}

def free_modl(-K: Data, +x: M.Node<K>, +v: Nat, +q: Nat) -> {ST.is_free(K, modl(K, x, v), q) == ST.is_free(K, x, q) : Bool}:
  match x:
    case M.Free{f}:
      {==}
    case M.N{c, a, b, q2, k}:
      {==}

def ent_pkl(-K: Data, -V: Data, +e: Bool, +x: M.Node<K>, +v: Nat, +m: Maybe<&2, V>) -> {ST.ent(K, V, ST.pk(M.Node<K>, e, modl(K, x, v), x), m) == ST.ent(K, V, x, m) : Maybe<&2, M.Entry<K, V>>}:
  match e:
    case True{}:
      ent_modl(K, V, x, v, m)
    case False{}:
      {==}

def free_pkl(-K: Data, +e: Bool, +x: M.Node<K>, +v: Nat, +q: Nat) -> {ST.is_free(K, ST.pk(M.Node<K>, e, modl(K, x, v), x), q) == ST.is_free(K, x, q) : Bool}:
  match e:
    case True{}:
      free_modl(K, x, v, q)
    case False{}:
      {==}

def ent_setl(-K: Data, -V: Data, +nl: List<&2, M.Node<K>>, +id: Nat, +v: Nat, +j: Nat, +m: Maybe<&2, V>) -> {ST.ent(K, V, ST.nd(K, setl(K, nl, id, v), j), m) == ST.ent(K, V, ST.nd(K, nl, j), m) : Maybe<&2, M.Entry<K, V>>}:
  %Equal.sym(M.Node<K>, ST.nd(K, setl(K, nl, id, v), j), ST.pk(M.Node<K>, Nat.is_eq(id, j), modl(K, ST.nd(K, nl, j), v), ST.nd(K, nl, j)), ndl(K, nl, id, v, j)) : {ST.ent(K, V, _, m) == ST.ent(K, V, ST.nd(K, nl, j), m) : Maybe<&2, M.Entry<K, V>>}
  ent_pkl(K, V, Nat.is_eq(id, j), ST.nd(K, nl, j), v, m)

# a setter keeps every entry
def ents_setl(~K: Data, ~V: Data, +xs: List<&2, Nat>, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +id: Nat, +v: Nat) -> {ST.ents(~K, ~V, xs, setl(K, nl, id, v), pl) == ST.ents(~K, ~V, xs, nl, pl) : List<&2, M.Entry<K, V>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+j, +t}:
      %Equal.sym(Maybe<&2, M.Entry<K, V>>, ST.ent(K, V, ST.nd(K, setl(K, nl, id, v), j), ST.pv(V, pl, j)), ST.ent(K, V, ST.nd(K, nl, j), ST.pv(V, pl, j)), ent_setl(K, V, nl, id, v, j, ST.pv(V, pl, j))) : {ST.cons_m(M.Entry<K, V>, _, ST.ents(~K, ~V, t, setl(K, nl, id, v), pl)) == ST.ents(~K, ~V, Con{j, t}, nl, pl) : List<&2, M.Entry<K, V>>}
      %Equal.sym(List<&2, M.Entry<K, V>>, ST.ents(~K, ~V, t, setl(K, nl, id, v), pl), ST.ents(~K, ~V, t, nl, pl), ents_setl(~K, ~V, t, nl, pl, id, v)) : {ST.cons_m(M.Entry<K, V>, ST.ent(K, V, ST.nd(K, nl, j), ST.pv(V, pl, j)), _) == ST.ents(~K, ~V, Con{j, t}, nl, pl) : List<&2, M.Entry<K, V>>}
      {==}

def oks_setl(~K: Data, ~V: Data, +xs: List<&2, Nat>, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +id: Nat, +v: Nat) -> {EN.oks(~K, ~V, xs, setl(K, nl, id, v), pl) == EN.oks(~K, ~V, xs, nl, pl) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+j, +t}:
      %Equal.sym(Maybe<&2, M.Entry<K, V>>, ST.ent(K, V, ST.nd(K, setl(K, nl, id, v), j), ST.pv(V, pl, j)), ST.ent(K, V, ST.nd(K, nl, j), ST.pv(V, pl, j)), ent_setl(K, V, nl, id, v, j, ST.pv(V, pl, j))) : {Bool.and(S.is_some(M.Entry<K, V>, _), EN.oks(~K, ~V, t, setl(K, nl, id, v), pl)) == EN.oks(~K, ~V, Con{j, t}, nl, pl) : Bool}
      %Equal.sym(Bool, EN.oks(~K, ~V, t, setl(K, nl, id, v), pl), EN.oks(~K, ~V, t, nl, pl), oks_setl(~K, ~V, t, nl, pl, id, v)) : {Bool.and(S.is_some(M.Entry<K, V>, ST.ent(K, V, ST.nd(K, nl, j), ST.pv(V, pl, j))), _) == EN.oks(~K, ~V, Con{j, t}, nl, pl) : Bool}
      {==}

# a setter keeps the free chain
def fll_setl(~K: Data, +fl: List<&2, Nat>, +nl: List<&2, M.Node<K>>, +id: Nat, +v: Nat) -> {ST.fll(~K, setl(K, nl, id, v), fl) == ST.fll(~K, nl, fl) : Bool}:
  match fl:
    case Nil{}:
      {==}
    case Con{+f, +t}:
      %Equal.sym(M.Node<K>, ST.nd(K, setl(K, nl, id, v), f), ST.pk(M.Node<K>, Nat.is_eq(id, f), modl(K, ST.nd(K, nl, f), v), ST.nd(K, nl, f)), ndl(K, nl, id, v, f)) : {Bool.and(ST.is_free(K, _, ST.fst0(t)), ST.fll(~K, setl(K, nl, id, v), t)) == ST.fll(~K, nl, Con{f, t}) : Bool}
      %Equal.sym(Bool, ST.is_free(K, ST.pk(M.Node<K>, Nat.is_eq(id, f), modl(K, ST.nd(K, nl, f), v), ST.nd(K, nl, f)), ST.fst0(t)), ST.is_free(K, ST.nd(K, nl, f), ST.fst0(t)), free_pkl(K, Nat.is_eq(id, f), ST.nd(K, nl, f), v, ST.fst0(t))) : {Bool.and(_, ST.fll(~K, setl(K, nl, id, v), t)) == ST.fll(~K, nl, Con{f, t}) : Bool}
      %Equal.sym(Bool, ST.fll(~K, setl(K, nl, id, v), t), ST.fll(~K, nl, t), fll_setl(~K, t, nl, id, v)) : {Bool.and(ST.is_free(K, ST.nd(K, nl, f), ST.fst0(t)), _) == ST.fll(~K, nl, Con{f, t}) : Bool}
      {==}

def ent_modr(-K: Data, -V: Data, +x: M.Node<K>, +v: Nat, +m: Maybe<&2, V>) -> {ST.ent(K, V, modr(K, x, v), m) == ST.ent(K, V, x, m) : Maybe<&2, M.Entry<K, V>>}:
  match x m:
    case M.Free{f} +m:
      {==}
    case M.N{c, a, b, q, k} None{}:
      {==}
    case M.N{c, a, b, q, k} Some{w}:
      {==}

def free_modr(-K: Data, +x: M.Node<K>, +v: Nat, +q: Nat) -> {ST.is_free(K, modr(K, x, v), q) == ST.is_free(K, x, q) : Bool}:
  match x:
    case M.Free{f}:
      {==}
    case M.N{c, a, b, q2, k}:
      {==}

def ent_pkr(-K: Data, -V: Data, +e: Bool, +x: M.Node<K>, +v: Nat, +m: Maybe<&2, V>) -> {ST.ent(K, V, ST.pk(M.Node<K>, e, modr(K, x, v), x), m) == ST.ent(K, V, x, m) : Maybe<&2, M.Entry<K, V>>}:
  match e:
    case True{}:
      ent_modr(K, V, x, v, m)
    case False{}:
      {==}

def free_pkr(-K: Data, +e: Bool, +x: M.Node<K>, +v: Nat, +q: Nat) -> {ST.is_free(K, ST.pk(M.Node<K>, e, modr(K, x, v), x), q) == ST.is_free(K, x, q) : Bool}:
  match e:
    case True{}:
      free_modr(K, x, v, q)
    case False{}:
      {==}

def ent_setr(-K: Data, -V: Data, +nl: List<&2, M.Node<K>>, +id: Nat, +v: Nat, +j: Nat, +m: Maybe<&2, V>) -> {ST.ent(K, V, ST.nd(K, setr(K, nl, id, v), j), m) == ST.ent(K, V, ST.nd(K, nl, j), m) : Maybe<&2, M.Entry<K, V>>}:
  %Equal.sym(M.Node<K>, ST.nd(K, setr(K, nl, id, v), j), ST.pk(M.Node<K>, Nat.is_eq(id, j), modr(K, ST.nd(K, nl, j), v), ST.nd(K, nl, j)), ndr(K, nl, id, v, j)) : {ST.ent(K, V, _, m) == ST.ent(K, V, ST.nd(K, nl, j), m) : Maybe<&2, M.Entry<K, V>>}
  ent_pkr(K, V, Nat.is_eq(id, j), ST.nd(K, nl, j), v, m)

# a setter keeps every entry
def ents_setr(~K: Data, ~V: Data, +xs: List<&2, Nat>, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +id: Nat, +v: Nat) -> {ST.ents(~K, ~V, xs, setr(K, nl, id, v), pl) == ST.ents(~K, ~V, xs, nl, pl) : List<&2, M.Entry<K, V>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+j, +t}:
      %Equal.sym(Maybe<&2, M.Entry<K, V>>, ST.ent(K, V, ST.nd(K, setr(K, nl, id, v), j), ST.pv(V, pl, j)), ST.ent(K, V, ST.nd(K, nl, j), ST.pv(V, pl, j)), ent_setr(K, V, nl, id, v, j, ST.pv(V, pl, j))) : {ST.cons_m(M.Entry<K, V>, _, ST.ents(~K, ~V, t, setr(K, nl, id, v), pl)) == ST.ents(~K, ~V, Con{j, t}, nl, pl) : List<&2, M.Entry<K, V>>}
      %Equal.sym(List<&2, M.Entry<K, V>>, ST.ents(~K, ~V, t, setr(K, nl, id, v), pl), ST.ents(~K, ~V, t, nl, pl), ents_setr(~K, ~V, t, nl, pl, id, v)) : {ST.cons_m(M.Entry<K, V>, ST.ent(K, V, ST.nd(K, nl, j), ST.pv(V, pl, j)), _) == ST.ents(~K, ~V, Con{j, t}, nl, pl) : List<&2, M.Entry<K, V>>}
      {==}

def oks_setr(~K: Data, ~V: Data, +xs: List<&2, Nat>, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +id: Nat, +v: Nat) -> {EN.oks(~K, ~V, xs, setr(K, nl, id, v), pl) == EN.oks(~K, ~V, xs, nl, pl) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+j, +t}:
      %Equal.sym(Maybe<&2, M.Entry<K, V>>, ST.ent(K, V, ST.nd(K, setr(K, nl, id, v), j), ST.pv(V, pl, j)), ST.ent(K, V, ST.nd(K, nl, j), ST.pv(V, pl, j)), ent_setr(K, V, nl, id, v, j, ST.pv(V, pl, j))) : {Bool.and(S.is_some(M.Entry<K, V>, _), EN.oks(~K, ~V, t, setr(K, nl, id, v), pl)) == EN.oks(~K, ~V, Con{j, t}, nl, pl) : Bool}
      %Equal.sym(Bool, EN.oks(~K, ~V, t, setr(K, nl, id, v), pl), EN.oks(~K, ~V, t, nl, pl), oks_setr(~K, ~V, t, nl, pl, id, v)) : {Bool.and(S.is_some(M.Entry<K, V>, ST.ent(K, V, ST.nd(K, nl, j), ST.pv(V, pl, j))), _) == EN.oks(~K, ~V, Con{j, t}, nl, pl) : Bool}
      {==}

# a setter keeps the free chain
def fll_setr(~K: Data, +fl: List<&2, Nat>, +nl: List<&2, M.Node<K>>, +id: Nat, +v: Nat) -> {ST.fll(~K, setr(K, nl, id, v), fl) == ST.fll(~K, nl, fl) : Bool}:
  match fl:
    case Nil{}:
      {==}
    case Con{+f, +t}:
      %Equal.sym(M.Node<K>, ST.nd(K, setr(K, nl, id, v), f), ST.pk(M.Node<K>, Nat.is_eq(id, f), modr(K, ST.nd(K, nl, f), v), ST.nd(K, nl, f)), ndr(K, nl, id, v, f)) : {Bool.and(ST.is_free(K, _, ST.fst0(t)), ST.fll(~K, setr(K, nl, id, v), t)) == ST.fll(~K, nl, Con{f, t}) : Bool}
      %Equal.sym(Bool, ST.is_free(K, ST.pk(M.Node<K>, Nat.is_eq(id, f), modr(K, ST.nd(K, nl, f), v), ST.nd(K, nl, f)), ST.fst0(t)), ST.is_free(K, ST.nd(K, nl, f), ST.fst0(t)), free_pkr(K, Nat.is_eq(id, f), ST.nd(K, nl, f), v, ST.fst0(t))) : {Bool.and(_, ST.fll(~K, setr(K, nl, id, v), t)) == ST.fll(~K, nl, Con{f, t}) : Bool}
      %Equal.sym(Bool, ST.fll(~K, setr(K, nl, id, v), t), ST.fll(~K, nl, t), fll_setr(~K, t, nl, id, v)) : {Bool.and(ST.is_free(K, ST.nd(K, nl, f), ST.fst0(t)), _) == ST.fll(~K, nl, Con{f, t}) : Bool}
      {==}

def ent_modp(-K: Data, -V: Data, +x: M.Node<K>, +v: Nat, +m: Maybe<&2, V>) -> {ST.ent(K, V, modp(K, x, v), m) == ST.ent(K, V, x, m) : Maybe<&2, M.Entry<K, V>>}:
  match x m:
    case M.Free{f} +m:
      {==}
    case M.N{c, a, b, q, k} None{}:
      {==}
    case M.N{c, a, b, q, k} Some{w}:
      {==}

def free_modp(-K: Data, +x: M.Node<K>, +v: Nat, +q: Nat) -> {ST.is_free(K, modp(K, x, v), q) == ST.is_free(K, x, q) : Bool}:
  match x:
    case M.Free{f}:
      {==}
    case M.N{c, a, b, q2, k}:
      {==}

def ent_pkp(-K: Data, -V: Data, +e: Bool, +x: M.Node<K>, +v: Nat, +m: Maybe<&2, V>) -> {ST.ent(K, V, ST.pk(M.Node<K>, e, modp(K, x, v), x), m) == ST.ent(K, V, x, m) : Maybe<&2, M.Entry<K, V>>}:
  match e:
    case True{}:
      ent_modp(K, V, x, v, m)
    case False{}:
      {==}

def free_pkp(-K: Data, +e: Bool, +x: M.Node<K>, +v: Nat, +q: Nat) -> {ST.is_free(K, ST.pk(M.Node<K>, e, modp(K, x, v), x), q) == ST.is_free(K, x, q) : Bool}:
  match e:
    case True{}:
      free_modp(K, x, v, q)
    case False{}:
      {==}

def ent_setp(-K: Data, -V: Data, +nl: List<&2, M.Node<K>>, +id: Nat, +v: Nat, +j: Nat, +m: Maybe<&2, V>) -> {ST.ent(K, V, ST.nd(K, setp(K, nl, id, v), j), m) == ST.ent(K, V, ST.nd(K, nl, j), m) : Maybe<&2, M.Entry<K, V>>}:
  %Equal.sym(M.Node<K>, ST.nd(K, setp(K, nl, id, v), j), ST.pk(M.Node<K>, Nat.is_eq(id, j), modp(K, ST.nd(K, nl, j), v), ST.nd(K, nl, j)), ndp(K, nl, id, v, j)) : {ST.ent(K, V, _, m) == ST.ent(K, V, ST.nd(K, nl, j), m) : Maybe<&2, M.Entry<K, V>>}
  ent_pkp(K, V, Nat.is_eq(id, j), ST.nd(K, nl, j), v, m)

# a setter keeps every entry
def ents_setp(~K: Data, ~V: Data, +xs: List<&2, Nat>, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +id: Nat, +v: Nat) -> {ST.ents(~K, ~V, xs, setp(K, nl, id, v), pl) == ST.ents(~K, ~V, xs, nl, pl) : List<&2, M.Entry<K, V>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+j, +t}:
      %Equal.sym(Maybe<&2, M.Entry<K, V>>, ST.ent(K, V, ST.nd(K, setp(K, nl, id, v), j), ST.pv(V, pl, j)), ST.ent(K, V, ST.nd(K, nl, j), ST.pv(V, pl, j)), ent_setp(K, V, nl, id, v, j, ST.pv(V, pl, j))) : {ST.cons_m(M.Entry<K, V>, _, ST.ents(~K, ~V, t, setp(K, nl, id, v), pl)) == ST.ents(~K, ~V, Con{j, t}, nl, pl) : List<&2, M.Entry<K, V>>}
      %Equal.sym(List<&2, M.Entry<K, V>>, ST.ents(~K, ~V, t, setp(K, nl, id, v), pl), ST.ents(~K, ~V, t, nl, pl), ents_setp(~K, ~V, t, nl, pl, id, v)) : {ST.cons_m(M.Entry<K, V>, ST.ent(K, V, ST.nd(K, nl, j), ST.pv(V, pl, j)), _) == ST.ents(~K, ~V, Con{j, t}, nl, pl) : List<&2, M.Entry<K, V>>}
      {==}

def oks_setp(~K: Data, ~V: Data, +xs: List<&2, Nat>, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +id: Nat, +v: Nat) -> {EN.oks(~K, ~V, xs, setp(K, nl, id, v), pl) == EN.oks(~K, ~V, xs, nl, pl) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+j, +t}:
      %Equal.sym(Maybe<&2, M.Entry<K, V>>, ST.ent(K, V, ST.nd(K, setp(K, nl, id, v), j), ST.pv(V, pl, j)), ST.ent(K, V, ST.nd(K, nl, j), ST.pv(V, pl, j)), ent_setp(K, V, nl, id, v, j, ST.pv(V, pl, j))) : {Bool.and(S.is_some(M.Entry<K, V>, _), EN.oks(~K, ~V, t, setp(K, nl, id, v), pl)) == EN.oks(~K, ~V, Con{j, t}, nl, pl) : Bool}
      %Equal.sym(Bool, EN.oks(~K, ~V, t, setp(K, nl, id, v), pl), EN.oks(~K, ~V, t, nl, pl), oks_setp(~K, ~V, t, nl, pl, id, v)) : {Bool.and(S.is_some(M.Entry<K, V>, ST.ent(K, V, ST.nd(K, nl, j), ST.pv(V, pl, j))), _) == EN.oks(~K, ~V, Con{j, t}, nl, pl) : Bool}
      {==}

# a setter keeps the free chain
def fll_setp(~K: Data, +fl: List<&2, Nat>, +nl: List<&2, M.Node<K>>, +id: Nat, +v: Nat) -> {ST.fll(~K, setp(K, nl, id, v), fl) == ST.fll(~K, nl, fl) : Bool}:
  match fl:
    case Nil{}:
      {==}
    case Con{+f, +t}:
      %Equal.sym(M.Node<K>, ST.nd(K, setp(K, nl, id, v), f), ST.pk(M.Node<K>, Nat.is_eq(id, f), modp(K, ST.nd(K, nl, f), v), ST.nd(K, nl, f)), ndp(K, nl, id, v, f)) : {Bool.and(ST.is_free(K, _, ST.fst0(t)), ST.fll(~K, setp(K, nl, id, v), t)) == ST.fll(~K, nl, Con{f, t}) : Bool}
      %Equal.sym(Bool, ST.is_free(K, ST.pk(M.Node<K>, Nat.is_eq(id, f), modp(K, ST.nd(K, nl, f), v), ST.nd(K, nl, f)), ST.fst0(t)), ST.is_free(K, ST.nd(K, nl, f), ST.fst0(t)), free_pkp(K, Nat.is_eq(id, f), ST.nd(K, nl, f), v, ST.fst0(t))) : {Bool.and(_, ST.fll(~K, setp(K, nl, id, v), t)) == ST.fll(~K, nl, Con{f, t}) : Bool}
      %Equal.sym(Bool, ST.fll(~K, setp(K, nl, id, v), t), ST.fll(~K, nl, t), fll_setp(~K, t, nl, id, v)) : {Bool.and(ST.is_free(K, ST.nd(K, nl, f), ST.fst0(t)), _) == ST.fll(~K, nl, Con{f, t}) : Bool}
      {==}

def ent_modc(-K: Data, -V: Data, +x: M.Node<K>, +v: Bool, +m: Maybe<&2, V>) -> {ST.ent(K, V, modc(K, x, v), m) == ST.ent(K, V, x, m) : Maybe<&2, M.Entry<K, V>>}:
  match x m:
    case M.Free{f} +m:
      {==}
    case M.N{c, a, b, q, k} None{}:
      {==}
    case M.N{c, a, b, q, k} Some{w}:
      {==}

def free_modc(-K: Data, +x: M.Node<K>, +v: Bool, +q: Nat) -> {ST.is_free(K, modc(K, x, v), q) == ST.is_free(K, x, q) : Bool}:
  match x:
    case M.Free{f}:
      {==}
    case M.N{c, a, b, q2, k}:
      {==}

def ent_pkc(-K: Data, -V: Data, +e: Bool, +x: M.Node<K>, +v: Bool, +m: Maybe<&2, V>) -> {ST.ent(K, V, ST.pk(M.Node<K>, e, modc(K, x, v), x), m) == ST.ent(K, V, x, m) : Maybe<&2, M.Entry<K, V>>}:
  match e:
    case True{}:
      ent_modc(K, V, x, v, m)
    case False{}:
      {==}

def free_pkc(-K: Data, +e: Bool, +x: M.Node<K>, +v: Bool, +q: Nat) -> {ST.is_free(K, ST.pk(M.Node<K>, e, modc(K, x, v), x), q) == ST.is_free(K, x, q) : Bool}:
  match e:
    case True{}:
      free_modc(K, x, v, q)
    case False{}:
      {==}

def ent_setc(-K: Data, -V: Data, +nl: List<&2, M.Node<K>>, +id: Nat, +v: Bool, +j: Nat, +m: Maybe<&2, V>) -> {ST.ent(K, V, ST.nd(K, setc(K, nl, id, v), j), m) == ST.ent(K, V, ST.nd(K, nl, j), m) : Maybe<&2, M.Entry<K, V>>}:
  %Equal.sym(M.Node<K>, ST.nd(K, setc(K, nl, id, v), j), ST.pk(M.Node<K>, Nat.is_eq(id, j), modc(K, ST.nd(K, nl, j), v), ST.nd(K, nl, j)), ndc(K, nl, id, v, j)) : {ST.ent(K, V, _, m) == ST.ent(K, V, ST.nd(K, nl, j), m) : Maybe<&2, M.Entry<K, V>>}
  ent_pkc(K, V, Nat.is_eq(id, j), ST.nd(K, nl, j), v, m)

# a setter keeps every entry
def ents_setc(~K: Data, ~V: Data, +xs: List<&2, Nat>, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +id: Nat, +v: Bool) -> {ST.ents(~K, ~V, xs, setc(K, nl, id, v), pl) == ST.ents(~K, ~V, xs, nl, pl) : List<&2, M.Entry<K, V>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+j, +t}:
      %Equal.sym(Maybe<&2, M.Entry<K, V>>, ST.ent(K, V, ST.nd(K, setc(K, nl, id, v), j), ST.pv(V, pl, j)), ST.ent(K, V, ST.nd(K, nl, j), ST.pv(V, pl, j)), ent_setc(K, V, nl, id, v, j, ST.pv(V, pl, j))) : {ST.cons_m(M.Entry<K, V>, _, ST.ents(~K, ~V, t, setc(K, nl, id, v), pl)) == ST.ents(~K, ~V, Con{j, t}, nl, pl) : List<&2, M.Entry<K, V>>}
      %Equal.sym(List<&2, M.Entry<K, V>>, ST.ents(~K, ~V, t, setc(K, nl, id, v), pl), ST.ents(~K, ~V, t, nl, pl), ents_setc(~K, ~V, t, nl, pl, id, v)) : {ST.cons_m(M.Entry<K, V>, ST.ent(K, V, ST.nd(K, nl, j), ST.pv(V, pl, j)), _) == ST.ents(~K, ~V, Con{j, t}, nl, pl) : List<&2, M.Entry<K, V>>}
      {==}

def oks_setc(~K: Data, ~V: Data, +xs: List<&2, Nat>, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +id: Nat, +v: Bool) -> {EN.oks(~K, ~V, xs, setc(K, nl, id, v), pl) == EN.oks(~K, ~V, xs, nl, pl) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+j, +t}:
      %Equal.sym(Maybe<&2, M.Entry<K, V>>, ST.ent(K, V, ST.nd(K, setc(K, nl, id, v), j), ST.pv(V, pl, j)), ST.ent(K, V, ST.nd(K, nl, j), ST.pv(V, pl, j)), ent_setc(K, V, nl, id, v, j, ST.pv(V, pl, j))) : {Bool.and(S.is_some(M.Entry<K, V>, _), EN.oks(~K, ~V, t, setc(K, nl, id, v), pl)) == EN.oks(~K, ~V, Con{j, t}, nl, pl) : Bool}
      %Equal.sym(Bool, EN.oks(~K, ~V, t, setc(K, nl, id, v), pl), EN.oks(~K, ~V, t, nl, pl), oks_setc(~K, ~V, t, nl, pl, id, v)) : {Bool.and(S.is_some(M.Entry<K, V>, ST.ent(K, V, ST.nd(K, nl, j), ST.pv(V, pl, j))), _) == EN.oks(~K, ~V, Con{j, t}, nl, pl) : Bool}
      {==}

# a setter keeps the free chain
def fll_setc(~K: Data, +fl: List<&2, Nat>, +nl: List<&2, M.Node<K>>, +id: Nat, +v: Bool) -> {ST.fll(~K, setc(K, nl, id, v), fl) == ST.fll(~K, nl, fl) : Bool}:
  match fl:
    case Nil{}:
      {==}
    case Con{+f, +t}:
      %Equal.sym(M.Node<K>, ST.nd(K, setc(K, nl, id, v), f), ST.pk(M.Node<K>, Nat.is_eq(id, f), modc(K, ST.nd(K, nl, f), v), ST.nd(K, nl, f)), ndc(K, nl, id, v, f)) : {Bool.and(ST.is_free(K, _, ST.fst0(t)), ST.fll(~K, setc(K, nl, id, v), t)) == ST.fll(~K, nl, Con{f, t}) : Bool}
      %Equal.sym(Bool, ST.is_free(K, ST.pk(M.Node<K>, Nat.is_eq(id, f), modc(K, ST.nd(K, nl, f), v), ST.nd(K, nl, f)), ST.fst0(t)), ST.is_free(K, ST.nd(K, nl, f), ST.fst0(t)), free_pkc(K, Nat.is_eq(id, f), ST.nd(K, nl, f), v, ST.fst0(t))) : {Bool.and(_, ST.fll(~K, setc(K, nl, id, v), t)) == ST.fll(~K, nl, Con{f, t}) : Bool}
      %Equal.sym(Bool, ST.fll(~K, setc(K, nl, id, v), t), ST.fll(~K, nl, t), fll_setc(~K, t, nl, id, v)) : {Bool.and(ST.is_free(K, ST.nd(K, nl, f), ST.fst0(t)), _) == ST.fll(~K, nl, Con{f, t}) : Bool}
      {==}
