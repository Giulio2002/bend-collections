import Base
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../../lib/spec_common.bend as SC
import ../../../src/containers/balanced_search_tree.bend as M
import ../../../src/containers/dynamic_array.bend as D
import ../../../src/containers/types/dynamic_array.bend as DE
import ./state.bend as ST
import ./da.bend as DA
import ./arr.bend as AB
import ./nsl.bend as NSL

# The TreeMap's node and payload accesses over the shadow: a read returns
# the list's node, a write or exchange updates the list in range.


def or_else(-X: Data, m: Maybe<&2, X>, +dv: X) -> X:
  match m:
    case None{}:
      dv
    case Some{x}:
      x

def nth_or_nth(-X: Data, +xs: List<&2, X>, +i: Nat, +dv: X) -> {ST.nth_or(X, xs, i, dv) == or_else(X, SC.nth(X, xs, i), dv) : X}:
  match xs i:
    case Nil{} _:
      {==}
    case Con{x, t} 0n:
      {==}
    case Con{x, +t} 1n+p:
      nth_or_nth(X, t, p, dv)

def pl_cap(~K: Data, ~V: Data, +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +t: ST.Tr, +fl: List<&2, Nat>, +hl: {Nat.is_le(l, 31n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, nl), SC.pow2(d)) == True{} : Bool}, +hp: {Nat.is_eq(SC.length(Maybe<&2, V>, pl), SC.length(M.Node<K>, nl)) == True{} : Bool}) -> {Nat.is_le(SC.length(Maybe<&2, V>, pl), SC.pow2(d)) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_le(z, SC.pow2(d)) == True{} : Bool}, SC.length(M.Node<K>, nl), SC.length(Maybe<&2, V>, pl), Equal.sym(Nat, SC.length(Maybe<&2, V>, pl), SC.length(M.Node<K>, nl), N.eq_from_is_eq(SC.length(Maybe<&2, V>, pl), SC.length(M.Node<K>, nl), hp)), hc)

def nth_hi(-X: Data, +xs: List<&2, X>, +i: Nat, +dv: X, +h: {Nat.is_lt(i, SC.length(X, xs)) == False{} : Bool}) -> {ST.nth_or(X, xs, i, dv) == dv : X}:
  match xs i:
    case Nil{} _:
      {==}
    case Con{x, t} 0n:
      Empty.absurd({x == dv : X}, L.true_false(h))
    case Con{x, +t} 1n+p:
      nth_hi(X, t, p, dv, h)

# ---- read ----

def rf(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +t: ST.Tr, +fl: List<&2, Nat>, +m: Maybe<&2, M.Node<K>>) -> {M.read_finish(~K, ~V, ~cmp, n, root, lo, hi, free, ST.pays(~V, l, d, pl), (ST.nodes(~K, l, d, nl), DA.item(M.Node<K>, m))) == (ST.real(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, t, fl}), or_else(M.Node<K>, m, M.Free{0n})) : M.TreeMap<K, V, cmp> & M.Node<K>}:
  match m:
    case None{}:
      {==}
    case Some{x}:
      {==}


def read_c(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +t: ST.Tr, +fl: List<&2, Nat>, +hl: {Nat.is_le(l, 31n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, nl), SC.pow2(d)) == True{} : Bool}, +hp: {Nat.is_eq(SC.length(Maybe<&2, V>, pl), SC.length(M.Node<K>, nl)) == True{} : Bool}, +id: Nat) -> {M.read(~K, ~V, ~cmp, ST.real(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, t, fl}), id) == (ST.real(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, t, fl}), ST.nd(K, nl, id)) : M.TreeMap<K, V, cmp> & M.Node<K>}:
  match id:
    case 0n:
      {==}
    case 1n+i:
      %Equal.sym(M.NodeStore<K> & Result<&2, &2, DE.Error, M.Node<K>>, M.ns_get(~K, ST.nodes(~K, l, d, nl), i), (ST.nodes(~K, l, d, nl), DA.item(M.Node<K>, SC.nth(M.Node<K>, nl, i))), NSL.ns_get_ok(~K, l, d, nl, hl, hd, hc, i)) : {M.read_finish(~K, ~V, ~cmp, n, root, lo, hi, free, ST.pays(~V, l, d, pl), _) == (ST.real(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, t, fl}), ST.nd(K, nl, 1n+i)) : M.TreeMap<K, V, cmp> & M.Node<K>}
      %Equal.sym(M.Node<K>, ST.nth_or(M.Node<K>, nl, i, M.Free{0n}), or_else(M.Node<K>, SC.nth(M.Node<K>, nl, i), M.Free{0n}), nth_or_nth(M.Node<K>, nl, i, M.Free{0n})) : {M.read_finish(~K, ~V, ~cmp, n, root, lo, hi, free, ST.pays(~V, l, d, pl), (ST.nodes(~K, l, d, nl), DA.item(M.Node<K>, SC.nth(M.Node<K>, nl, i)))) == (ST.real(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, t, fl}), _) : M.TreeMap<K, V, cmp> & M.Node<K>}
      rf(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, t, fl, SC.nth(M.Node<K>, nl, i))

# ---- the payload read ----

def gf2(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +t: ST.Tr, +fl: List<&2, Nat>, +m: Maybe<&2, Maybe<&2, V>>) -> {M.get_id_finish(~K, ~V, ~cmp, n, root, lo, hi, free, ST.nodes(~K, l, d, nl), (ST.pays(~V, l, d, pl), DA.item(Maybe<&2, V>, m))) == (ST.real(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, t, fl}), or_else(Maybe<&2, V>, m, None{})) : M.TreeMap<K, V, cmp> & Maybe<&2, V>}:
  match m:
    case None{}:
      {==}
    case Some{x}:
      {==}

def get_id_c(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +t: ST.Tr, +fl: List<&2, Nat>, +hl: {Nat.is_le(l, 31n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, nl), SC.pow2(d)) == True{} : Bool}, +hp: {Nat.is_eq(SC.length(Maybe<&2, V>, pl), SC.length(M.Node<K>, nl)) == True{} : Bool}, +id: Nat) -> {M.get_id(~K, ~V, ~cmp, ST.real(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, t, fl}), id) == (ST.real(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, t, fl}), ST.pv(V, pl, id)) : M.TreeMap<K, V, cmp> & Maybe<&2, V>}:
  match id:
    case 0n:
      {==}
    case 1n+i:
      %Equal.sym(D.DynArray<&2, Maybe<&2, V>> & Result<&2, &2, DE.Error, Maybe<&2, V>>, D.get_at(~Maybe<&2, V>, ST.pays(~V, l, d, pl), i), (ST.pays(~V, l, d, pl), DA.item(Maybe<&2, V>, SC.nth(Maybe<&2, V>, pl, i))), AB.blk_get(~Maybe<&2, V>, l, d, pl, hl, hd, pl_cap(~K, ~V, n, root, lo, hi, free, l, d, nl, pl, t, fl, hl, hd, hc, hp), i)) : {M.get_id_finish(~K, ~V, ~cmp, n, root, lo, hi, free, ST.nodes(~K, l, d, nl), _) == (ST.real(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, t, fl}), ST.pv(V, pl, 1n+i)) : M.TreeMap<K, V, cmp> & Maybe<&2, V>}
      %Equal.sym(Maybe<&2, V>, ST.nth_or(Maybe<&2, V>, pl, i, None{}), or_else(Maybe<&2, V>, SC.nth(Maybe<&2, V>, pl, i), None{}), nth_or_nth(Maybe<&2, V>, pl, i, None{})) : {M.get_id_finish(~K, ~V, ~cmp, n, root, lo, hi, free, ST.nodes(~K, l, d, nl), (ST.pays(~V, l, d, pl), DA.item(Maybe<&2, V>, SC.nth(Maybe<&2, V>, pl, i)))) == (ST.real(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, t, fl}), _) : M.TreeMap<K, V, cmp> & Maybe<&2, V>}
      gf2(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, t, fl, SC.nth(Maybe<&2, V>, pl, i))

# ---- write ----

# the shadow's write: the node of id replaced when id names a slot
def wr_nl(-K: Data, +nl: List<&2, M.Node<K>>, +id: Nat, +x: M.Node<K>) -> List<&2, M.Node<K>>:
  match id:
    case 0n:
      nl
    case 1n+i:
      ST.pk(List<&2, M.Node<K>>, Nat.is_lt(i, SC.length(M.Node<K>, nl)), SC.update(M.Node<K>, nl, i, x), nl)

def wr_c2(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +t: ST.Tr, +fl: List<&2, Nat>, +hl: {Nat.is_le(l, 31n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, nl), SC.pow2(d)) == True{} : Bool}, +hp: {Nat.is_eq(SC.length(Maybe<&2, V>, pl), SC.length(M.Node<K>, nl)) == True{} : Bool}, +i: Nat, +x: M.Node<K>, +b: Bool, +hb: {Nat.is_lt(i, SC.length(M.Node<K>, nl)) == b : Bool}) -> {M.write(~K, ~V, ~cmp, ST.real(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, t, fl}), 1n+i, x) == ST.real(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, ST.pk(List<&2, M.Node<K>>, b, SC.update(M.Node<K>, nl, i, x), nl), pl, t, fl}) : M.TreeMap<K, V, cmp>}:
  match b:
    case True{}:
      %Equal.sym(M.NodeStore<K> & Result<&2, &2, DE.Error, Unit>, M.ns_set(~K, ST.nodes(~K, l, d, nl), i, x), (ST.nodes(~K, l, d, SC.update(M.Node<K>, nl, i, x)), Done{Unit{}}), NSL.ns_set_in(~K, l, d, nl, hl, hd, hc, i, x, hb)) : {M.write_finish(~K, ~V, ~cmp, n, root, lo, hi, free, ST.pays(~V, l, d, pl), _) == ST.real(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, SC.update(M.Node<K>, nl, i, x), pl, t, fl}) : M.TreeMap<K, V, cmp>}
      {==}
    case False{}:
      %Equal.sym(M.NodeStore<K> & Result<&2, &2, DE.Error, Unit>, M.ns_set(~K, ST.nodes(~K, l, d, nl), i, x), (ST.nodes(~K, l, d, nl), Fail{DE.IndexOutOfRange{}}), NSL.ns_set_out(~K, l, d, nl, hl, hd, hc, i, x, hb)) : {M.write_finish(~K, ~V, ~cmp, n, root, lo, hi, free, ST.pays(~V, l, d, pl), _) == ST.real(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, t, fl}) : M.TreeMap<K, V, cmp>}
      {==}

def write_c(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +t: ST.Tr, +fl: List<&2, Nat>, +hl: {Nat.is_le(l, 31n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, nl), SC.pow2(d)) == True{} : Bool}, +hp: {Nat.is_eq(SC.length(Maybe<&2, V>, pl), SC.length(M.Node<K>, nl)) == True{} : Bool}, +id: Nat, +x: M.Node<K>) -> {M.write(~K, ~V, ~cmp, ST.real(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, t, fl}), id, x) == ST.real(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, wr_nl(K, nl, id, x), pl, t, fl}) : M.TreeMap<K, V, cmp>}:
  match id:
    case 0n:
      {==}
    case 1n+i:
      wr_c2(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, t, fl, hl, hd, hc, hp, i, x, Nat.is_lt(i, SC.length(M.Node<K>, nl)), {==})

# ---- exchange ----

def ex_pl(-V: Data, +pl: List<&2, Maybe<&2, V>>, +id: Nat, +v: Maybe<&2, V>) -> List<&2, Maybe<&2, V>>:
  match id:
    case 0n:
      pl
    case 1n+i:
      ST.pk(List<&2, Maybe<&2, V>>, Nat.is_lt(i, SC.length(Maybe<&2, V>, pl)), SC.update(Maybe<&2, V>, pl, i, v), pl)

def ef(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +t: ST.Tr, +fl: List<&2, Nat>, +pl2: List<&2, Maybe<&2, V>>, +m: Maybe<&2, Maybe<&2, V>>) -> {M.exchange_finish(~K, ~V, ~cmp, n, root, lo, hi, free, ST.nodes(~K, l, d, nl), (ST.pays(~V, l, d, pl2), DA.item(Maybe<&2, V>, m))) == (ST.real(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl2, t, fl}), or_else(Maybe<&2, V>, m, None{})) : M.TreeMap<K, V, cmp> & Maybe<&2, V>}:
  match m:
    case None{}:
      {==}
    case Some{x}:
      {==}

def ex_c2(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +t: ST.Tr, +fl: List<&2, Nat>, +hl: {Nat.is_le(l, 31n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, nl), SC.pow2(d)) == True{} : Bool}, +hp: {Nat.is_eq(SC.length(Maybe<&2, V>, pl), SC.length(M.Node<K>, nl)) == True{} : Bool}, +i: Nat, +v: Maybe<&2, V>, +b: Bool, +hb: {Nat.is_lt(i, SC.length(Maybe<&2, V>, pl)) == b : Bool}) -> {M.exchange(~K, ~V, ~cmp, ST.real(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, t, fl}), 1n+i, v) == (ST.real(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, ST.pk(List<&2, Maybe<&2, V>>, b, SC.update(Maybe<&2, V>, pl, i, v), pl), t, fl}), ST.pv(V, pl, 1n+i)) : M.TreeMap<K, V, cmp> & Maybe<&2, V>}:
  match b:
    case True{}:
      %Equal.sym(D.DynArray<&2, Maybe<&2, V>> & Result<&2, &2, DE.Error, Maybe<&2, V>>, D.swap_at(~Maybe<&2, V>, ST.pays(~V, l, d, pl), i, v), (ST.pays(~V, l, d, SC.update(Maybe<&2, V>, pl, i, v)), DA.item(Maybe<&2, V>, SC.nth(Maybe<&2, V>, pl, i))), AB.blk_swap(~Maybe<&2, V>, l, d, pl, hl, hd, pl_cap(~K, ~V, n, root, lo, hi, free, l, d, nl, pl, t, fl, hl, hd, hc, hp), i, v, hb)) : {M.exchange_finish(~K, ~V, ~cmp, n, root, lo, hi, free, ST.nodes(~K, l, d, nl), _) == (ST.real(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, SC.update(Maybe<&2, V>, pl, i, v), t, fl}), ST.pv(V, pl, 1n+i)) : M.TreeMap<K, V, cmp> & Maybe<&2, V>}
      %Equal.sym(Maybe<&2, V>, ST.nth_or(Maybe<&2, V>, pl, i, None{}), or_else(Maybe<&2, V>, SC.nth(Maybe<&2, V>, pl, i), None{}), nth_or_nth(Maybe<&2, V>, pl, i, None{})) : {M.exchange_finish(~K, ~V, ~cmp, n, root, lo, hi, free, ST.nodes(~K, l, d, nl), (ST.pays(~V, l, d, SC.update(Maybe<&2, V>, pl, i, v)), DA.item(Maybe<&2, V>, SC.nth(Maybe<&2, V>, pl, i)))) == (ST.real(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, SC.update(Maybe<&2, V>, pl, i, v), t, fl}), _) : M.TreeMap<K, V, cmp> & Maybe<&2, V>}
      ef(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, t, fl, SC.update(Maybe<&2, V>, pl, i, v), SC.nth(Maybe<&2, V>, pl, i))
    case False{}:
      %Equal.sym(D.DynArray<&2, Maybe<&2, V>> & Result<&2, &2, DE.Error, Maybe<&2, V>>, D.swap_at(~Maybe<&2, V>, ST.pays(~V, l, d, pl), i, v), (ST.pays(~V, l, d, pl), Fail{DE.IndexOutOfRange{}}), AB.blk_swap_out(~Maybe<&2, V>, l, d, pl, hl, hd, pl_cap(~K, ~V, n, root, lo, hi, free, l, d, nl, pl, t, fl, hl, hd, hc, hp), i, v, hb)) : {M.exchange_finish(~K, ~V, ~cmp, n, root, lo, hi, free, ST.nodes(~K, l, d, nl), _) == (ST.real(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, t, fl}), ST.pv(V, pl, 1n+i)) : M.TreeMap<K, V, cmp> & Maybe<&2, V>}
      %Equal.sym(Maybe<&2, V>, ST.nth_or(Maybe<&2, V>, pl, i, None{}), None{}, nth_hi(Maybe<&2, V>, pl, i, None{}, hb)) : {(ST.real(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, t, fl}), None{}) == (ST.real(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, t, fl}), _) : M.TreeMap<K, V, cmp> & Maybe<&2, V>}
      {==}

def exchange_c(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +t: ST.Tr, +fl: List<&2, Nat>, +hl: {Nat.is_le(l, 31n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(M.Node<K>, nl), SC.pow2(d)) == True{} : Bool}, +hp: {Nat.is_eq(SC.length(Maybe<&2, V>, pl), SC.length(M.Node<K>, nl)) == True{} : Bool}, +id: Nat, +v: Maybe<&2, V>) -> {M.exchange(~K, ~V, ~cmp, ST.real(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, t, fl}), id, v) == (ST.real(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, ex_pl(V, pl, id, v), t, fl}), ST.pv(V, pl, id)) : M.TreeMap<K, V, cmp> & Maybe<&2, V>}:
  match id:
    case 0n:
      {==}
    case 1n+i:
      ex_c2(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, t, fl, hl, hd, hc, hp, i, v, Nat.is_lt(i, SC.length(Maybe<&2, V>, pl)), {==})
