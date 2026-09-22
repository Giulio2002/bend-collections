# Retained proof dependency: history/retired-doubly-linked-list/proofs/dlist/insitems.bend
# Only declarations needed by the LRU refinement are kept; no retired runtime is imported.
# Proof-only dependency extracted from retained LRU support; no retired collection API.
import Base
import ../../lib/logic.bend as L
import ../../../spec/common.bend as SC
import link_primitives.bend as D
import links_state.bend as ST
import links_facts.bend as F
import links_links.bend as LK
import links_retarget.bend as RT

def hd_ins(+x: List<&2, Nat>, +f: Nat, +y: List<&2, Nat>, +depth: Nat, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +hl: {ST.alllt(x, SC.pow2(depth)) == True{} : Bool}) -> {D.pick_end(U32.is_eq(LK.lastl(x, D.nil()), D.nil()), ST.ln(f), ST.hd(SC.append(Nat, x, y))) == ST.hd(SC.append(Nat, x, Con{f, y})) : U32}:
  match x:
    case Nil{}:
      {==}
    case Con{+x0, +t}:
      L.subst(Bool, z => {D.pick_end(z, ST.ln(f), ST.ln(x0)) == ST.ln(x0) : U32}, False{}, U32.is_eq(ST.ln(ST.lst_or(t, x0)), D.nil()), Equal.sym(Bool, U32.is_eq(ST.ln(ST.lst_or(t, x0)), D.nil()), False{}, F.ln_ne_nil(ST.lst_or(t, x0), depth, hd, RT.lst_lt(t, x0, SC.pow2(depth), hl))), {==})
