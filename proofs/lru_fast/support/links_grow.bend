# Retained proof dependency: history/retired-doubly-linked-list/proofs/dlist/grow.bend
# Only declarations needed by the LRU refinement are kept; no retired runtime is imported.
# Proof-only dependency extracted from retained LRU support; no retired collection API.
import Base
import ../../lib/logic.bend as L
import ../../lib/list.bend as LL
import ../../../spec/common.bend as SC
import links_state.bend as ST
import links_items.bend as IT

def lat_app(+ps: List<&2, U32>, +zs: List<&2, U32>, +p: Nat, +h: {Nat.is_lt(p, SC.length(U32, ps)) == True{} : Bool}) -> {ST.lat(SC.append(U32, ps, zs), p) == ST.lat(ps, p) : U32}:
  Equal.cong(Maybe<&2, U32>, U32, m => L.some_value(U32, m, 0), SC.nth(U32, SC.append(U32, ps, zs), p), SC.nth(U32, ps, p), LL.nth_append_left(U32, ps, zs, p, h))


def lk_grow(+ord: List<&2, Nat>, +pv: U32, +e: U32, +ps: List<&2, U32>, +zs: List<&2, U32>, +ns: List<&2, U32>, +ws: List<&2, U32>, +hp: {ST.alllt(ord, SC.length(U32, ps)) == True{} : Bool}, +hn: {ST.alllt(ord, SC.length(U32, ns)) == True{} : Bool}) -> {ST.lk(ord, pv, e, SC.append(U32, ps, zs), SC.append(U32, ns, ws)) == ST.lk(ord, pv, e, ps, ns) : Bool}:
  match ord:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +ih = lk_grow(t, ST.ln(x), e, ps, zs, ns, ws, IT.lt_tail(x, t, SC.length(U32, ps), hp), IT.lt_tail(x, t, SC.length(U32, ns), hn))
      %Equal.sym(U32, ST.lat(SC.append(U32, ps, zs), x), ST.lat(ps, x), lat_app(ps, zs, x, IT.lt_head(x, t, SC.length(U32, ps), hp))) : {Bool.and(U32.is_eq(_, pv), Bool.and(U32.is_eq(ST.lat(SC.append(U32, ns, ws), x), ST.hd_or(t, e)), ST.lk(t, ST.ln(x), e, SC.append(U32, ps, zs), SC.append(U32, ns, ws)))) == ST.lk(Con{x, t}, pv, e, ps, ns) : Bool}
      %Equal.sym(U32, ST.lat(SC.append(U32, ns, ws), x), ST.lat(ns, x), lat_app(ns, ws, x, IT.lt_head(x, t, SC.length(U32, ns), hn))) : {Bool.and(U32.is_eq(ST.lat(ps, x), pv), Bool.and(U32.is_eq(_, ST.hd_or(t, e)), ST.lk(t, ST.ln(x), e, SC.append(U32, ps, zs), SC.append(U32, ns, ws)))) == ST.lk(Con{x, t}, pv, e, ps, ns) : Bool}
      %Equal.sym(Bool, ST.lk(t, ST.ln(x), e, SC.append(U32, ps, zs), SC.append(U32, ns, ws)), ST.lk(t, ST.ln(x), e, ps, ns), ih) : {Bool.and(U32.is_eq(ST.lat(ps, x), pv), Bool.and(U32.is_eq(ST.lat(ns, x), ST.hd_or(t, e)), _)) == ST.lk(Con{x, t}, pv, e, ps, ns) : Bool}
      {==}
