import Base
import ../lib/logic.bend as L
import ../lib/array.bend as AR
import ../spec/lru.bend as SP
import ../../src/math/u64.bend as W
import ../../src/containers/lru.bend as LR
import ../hash_table/table.bend as TB
import ./state.bend as ST
import ./meta.bend as MT

# The entry add stores, from the lifetime words: the specification's mk.


def EntOK(~V: Data, +mT: AR.Tree<U32>, +pm: {AR.perfect(U32, 5n, mT) == True{} : Bool}, +v: V, +now: W.U64, +key: String) -> Type:
  Sigma<&1, &1, U32, t => Sigma<&1, &1, U32, lo => Sigma<&1, &1, U32, hi => {LR.entry_of(&2, V, AR.thaw(U32, mT), v, now) == (AR.thaw(U32, mT), LR.E{v, t, lo, hi}) : Array<U32> & LR.Ent<&2, V>} & {SP.LE{key, v, t, W.U64{lo, hi}} == SP.mk(~V, TB.nth0(AR.slots(U32, mT), 3n), ST.w64(AR.slots(U32, mT), 4n), key, v, now) : SP.Ent<V>}>>>


def ent_d(~V: Data, +mT: AR.Tree<U32>, +pm: {AR.perfect(U32, 5n, mT) == True{} : Bool}, +v: V, +now: W.U64, +key: String, +d: W.U64, +hd: {W.add(now, ST.w64(AR.slots(U32, mT), 4n)) == d : W.U64}, +e0: {LR.entry_of(&2, V, AR.thaw(U32, mT), v, now) == (AR.thaw(U32, mT), LR.ent_dl(&2, V, v, W.add(now, ST.w64(AR.slots(U32, mT), 4n)))) : Array<U32> & LR.Ent<&2, V>}, +hsp: {SP.LE{key, v, 1, W.add(now, ST.w64(AR.slots(U32, mT), 4n))} == SP.mk(~V, TB.nth0(AR.slots(U32, mT), 3n), ST.w64(AR.slots(U32, mT), 4n), key, v, now) : SP.Ent<V>}) -> EntOK(~V, mT, pm, v, now, key):
  match d:
    case W.U64{+lo, +hi}:
      +e1 = Equal.cong(W.U64, Array<U32> & LR.Ent<&2, V>, z => (AR.thaw(U32, mT), LR.ent_dl(&2, V, v, z)), W.add(now, ST.w64(AR.slots(U32, mT), 4n)), W.U64{lo, hi}, hd)
      +s1 = Equal.cong(W.U64, SP.Ent<V>, z => SP.LE{key, v, 1, z}, W.add(now, ST.w64(AR.slots(U32, mT), 4n)), W.U64{lo, hi}, hd)
      (1, (lo, (hi, (Equal.trans(Array<U32> & LR.Ent<&2, V>, LR.entry_of(&2, V, AR.thaw(U32, mT), v, now), (AR.thaw(U32, mT), LR.ent_dl(&2, V, v, W.add(now, ST.w64(AR.slots(U32, mT), 4n)))), (AR.thaw(U32, mT), LR.E{v, 1, lo, hi}), e0, e1), Equal.trans(SP.Ent<V>, SP.LE{key, v, 1, W.U64{lo, hi}}, SP.LE{key, v, 1, W.add(now, ST.w64(AR.slots(U32, mT), 4n))}, SP.mk(~V, TB.nth0(AR.slots(U32, mT), 3n), ST.w64(AR.slots(U32, mT), 4n), key, v, now), Equal.sym(SP.Ent<V>, SP.LE{key, v, 1, W.add(now, ST.w64(AR.slots(U32, mT), 4n))}, SP.LE{key, v, 1, W.U64{lo, hi}}, s1), hsp)))))


def ent_c(~V: Data, +mT: AR.Tree<U32>, +pm: {AR.perfect(U32, 5n, mT) == True{} : Bool}, +v: V, +now: W.U64, +key: String, +c: Bool, +hc: {U32.is_eq(TB.nth0(AR.slots(U32, mT), 3n), 0) == c : Bool}, +e0: {LR.entry_of(&2, V, AR.thaw(U32, mT), v, now) == LR.ent_if(&2, V, v, now, AR.thaw(U32, mT), Bool.not(c)) : Array<U32> & LR.Ent<&2, V>}) -> EntOK(~V, mT, pm, v, now, key):
  match c:
    case True{}:
      +hs = Equal.sym(SP.Ent<V>, SP.mk(~V, TB.nth0(AR.slots(U32, mT), 3n), ST.w64(AR.slots(U32, mT), 4n), key, v, now), SP.LE{key, v, 0, W.zero()}, Equal.cong(Bool, SP.Ent<V>, b => SP.mk_c(~V, ST.w64(AR.slots(U32, mT), 4n), key, v, now, b), U32.is_eq(TB.nth0(AR.slots(U32, mT), 3n), 0), True{}, hc))
      (0, (0, (0, (e0, hs))))
    case False{}:
      +hs = Equal.sym(SP.Ent<V>, SP.mk(~V, TB.nth0(AR.slots(U32, mT), 3n), ST.w64(AR.slots(U32, mT), 4n), key, v, now), SP.LE{key, v, 1, W.add(now, ST.w64(AR.slots(U32, mT), 4n))}, Equal.cong(Bool, SP.Ent<V>, b => SP.mk_c(~V, ST.w64(AR.slots(U32, mT), 4n), key, v, now, b), U32.is_eq(TB.nth0(AR.slots(U32, mT), 3n), 0), False{}, hc))
      +g4 = MT.uget(5n, {==}, mT, pm, 4, {==})
      +g5 = MT.uget(5n, {==}, mT, pm, 5, {==})
      +e1 = Equal.cong(Array<U32> & U32, Array<U32> & LR.Ent<&2, V>, r => LR.life_lo(&2, V, v, now, r), Array.get(U32, AR.thaw(U32, mT), 4), (AR.thaw(U32, mT), TB.nth0(AR.slots(U32, mT), 4n)), g4)
      +e2 = Equal.cong(Array<U32> & U32, Array<U32> & LR.Ent<&2, V>, r => LR.life_hi(&2, V, v, now, TB.nth0(AR.slots(U32, mT), 4n), r), Array.get(U32, AR.thaw(U32, mT), 5), (AR.thaw(U32, mT), TB.nth0(AR.slots(U32, mT), 5n)), g5)
      +e3 = Equal.trans(Array<U32> & LR.Ent<&2, V>, LR.entry_of(&2, V, AR.thaw(U32, mT), v, now), LR.ent_if(&2, V, v, now, AR.thaw(U32, mT), True{}), LR.life_hi(&2, V, v, now, TB.nth0(AR.slots(U32, mT), 4n), Array.get(U32, AR.thaw(U32, mT), 5)), e0, e1)
      ent_d(~V, mT, pm, v, now, key, W.add(now, ST.w64(AR.slots(U32, mT), 4n)), {==}, Equal.trans(Array<U32> & LR.Ent<&2, V>, LR.entry_of(&2, V, AR.thaw(U32, mT), v, now), LR.life_hi(&2, V, v, now, TB.nth0(AR.slots(U32, mT), 4n), Array.get(U32, AR.thaw(U32, mT), 5)), (AR.thaw(U32, mT), LR.ent_dl(&2, V, v, W.add(now, ST.w64(AR.slots(U32, mT), 4n)))), e3, e2), hs)

# THEOREM: entry_of builds an entry whose timing is the specification's mk
def ent_ok(~V: Data, +mT: AR.Tree<U32>, +pm: {AR.perfect(U32, 5n, mT) == True{} : Bool}, +v: V, +now: W.U64, +key: String) -> EntOK(~V, mT, pm, v, now, key):
  +g3 = MT.uget(5n, {==}, mT, pm, 3, {==})
  +e0 = Equal.cong(Array<U32> & U32, Array<U32> & LR.Ent<&2, V>, r => LR.ent_ttl(&2, V, v, now, r), Array.get(U32, AR.thaw(U32, mT), 3), (AR.thaw(U32, mT), TB.nth0(AR.slots(U32, mT), 3n)), g3)
  ent_c(~V, mT, pm, v, now, key, U32.is_eq(TB.nth0(AR.slots(U32, mT), 3n), 0), {==}, e0)
