import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/array.bend as AR
import ../spec/common.bend as SC
import ../spec/lru.bend as SP
import ../math/u32div.bend as UD
import ../../src/math/u64.bend as W
import ../../src/containers/lru.bend as LR
import ../hash_table/table.bend as TB
import ./state.bend as ST
import ./meta.bend as MT
import ./basic.bend as BA
import ./bump.bend as BU
import ../hash_table/insa.bend as IA

import ./bumpsh.bend as BS

# The counts on the shadow, keeping the table's bit count k.


def shk(~V: Data, sh: ST.Sh<V>) -> Nat:
  match sh:
    case ST.LS{+cap, +n, +head, +tail, +free, +mT, +k, +sd, +tabT, +ksT, +eT, +lkT, +sl, +fl}:
      k

def CountOKk(~V: Data, +spec: SP.Lru<V>, r: LR.LRU<&2, V>, +k: Nat) -> Type:
  Sigma<&1, &1, ST.Sh<V>, sh2 => {r == ST.real(~V, sh2) : LR.LRU<&2, V>} & ({ST.model(~V, sh2) == spec : SP.Lru<V>} & ({ST.good(~V, sh2) == True{} : Bool} & {shk(~V, sh2) == k : Nat}))>

def count_evk(~V: Data, +cap: U32, +n: U32, +head: U32, +tail: U32, +free: U32, +mT: AR.Tree<U32>, +k: Nat, +sd: Nat, +tabT: AR.Tree<U32>, +ksT: AR.Tree<String>, +eT: AR.Tree<Maybe<&2, V>>, +lkT: AR.Tree<U32>, +sl: List<&2, Nat>, +fl: List<&2, Nat>, +hg: {ST.good(~V, ST.LS{cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, sl, fl}) == True{} : Bool}, bo: BU.BumpOK(mT, 18n, LR.bump(1, AR.thaw(U32, mT)))) -> CountOKk(~V, SP.L{cap, TB.nth0(AR.slots(U32, mT), 3n), ST.w64(AR.slots(U32, mT), 4n), ST.es(~V, AR.slots(U32, lkT), AR.slots(String, ksT), AR.slots(Maybe<&2, V>, eT), sl), SP.c_ev(ST.ctr(AR.slots(U32, mT)))}, LR.fbump(&2, V, 1, ST.real(~V, ST.LS{cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, sl, fl})), k):
  match bo:
    case Tuple{+m2, Tuple{+ea, Tuple{+pm2, Tuple{+ew, Tuple{+x, Tuple{+y, e}}}}}}:
      +ee = {e : {AR.slots(U32, m2) == SC.update(U32, SC.update(U32, AR.slots(U32, mT), 18n, x), 1n+18n, y) : List<&2, U32>}}
      +er = Equal.cong(Array<U32>, LR.LRU<&2, V>, z => LR.F{cap, n, head, tail, free, z, AR.thaw(U32, tabT), AR.thaw(String, ksT), AR.thaw(Maybe<&2, V>, eT), AR.thaw(U32, lkT)}, LR.bump(1, AR.thaw(U32, mT)), AR.thaw(U32, m2), ea)
      +g = BS.bm_fin(~V, cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, sl, fl, hg, 18n, {==}, m2, pm2, x, y, ee)
      +e3 = BS.keep(AR.slots(U32, mT), m2, 18n, x, y, ee, 3n, {==}, {==})
      +e4 = BA.w64_eq(AR.slots(U32, m2), AR.slots(U32, mT), 4n, BS.keep(AR.slots(U32, mT), m2, 18n, x, y, ee, 4n, {==}, {==}), BS.keep(AR.slots(U32, mT), m2, 18n, x, y, ee, 5n, {==}, {==}))
      +ec = BA.ct5(ST.w64(AR.slots(U32, m2), 16n), ST.w64(AR.slots(U32, m2), 18n), ST.w64(AR.slots(U32, m2), 20n), ST.w64(AR.slots(U32, m2), 22n), ST.w64(AR.slots(U32, m2), 24n), ST.w64(AR.slots(U32, mT), 16n), SP.inc64(ST.w64(AR.slots(U32, mT), 18n)), ST.w64(AR.slots(U32, mT), 20n), ST.w64(AR.slots(U32, mT), 22n), ST.w64(AR.slots(U32, mT), 24n), BA.w64_eq(AR.slots(U32, m2), AR.slots(U32, mT), 16n, BS.keep(AR.slots(U32, mT), m2, 18n, x, y, ee, 16n, {==}, {==}), BS.keep(AR.slots(U32, mT), m2, 18n, x, y, ee, 17n, {==}, {==})), ew, BA.w64_eq(AR.slots(U32, m2), AR.slots(U32, mT), 20n, BS.keep(AR.slots(U32, mT), m2, 18n, x, y, ee, 20n, {==}, {==}), BS.keep(AR.slots(U32, mT), m2, 18n, x, y, ee, 21n, {==}, {==})), BA.w64_eq(AR.slots(U32, m2), AR.slots(U32, mT), 22n, BS.keep(AR.slots(U32, mT), m2, 18n, x, y, ee, 22n, {==}, {==}), BS.keep(AR.slots(U32, mT), m2, 18n, x, y, ee, 23n, {==}, {==})), BA.w64_eq(AR.slots(U32, m2), AR.slots(U32, mT), 24n, BS.keep(AR.slots(U32, mT), m2, 18n, x, y, ee, 24n, {==}, {==}), BS.keep(AR.slots(U32, mT), m2, 18n, x, y, ee, 25n, {==}, {==})))
      (ST.LS{cap, n, head, tail, free, m2, k, sd, tabT, ksT, eT, lkT, sl, fl}, (er, (BA.lru_eq(~V, cap, TB.nth0(AR.slots(U32, m2), 3n), TB.nth0(AR.slots(U32, mT), 3n), ST.w64(AR.slots(U32, m2), 4n), ST.w64(AR.slots(U32, mT), 4n), ST.es(~V, AR.slots(U32, lkT), AR.slots(String, ksT), AR.slots(Maybe<&2, V>, eT), sl), ST.es(~V, AR.slots(U32, lkT), AR.slots(String, ksT), AR.slots(Maybe<&2, V>, eT), sl), ST.ctr(AR.slots(U32, m2)), SP.c_ev(ST.ctr(AR.slots(U32, mT))), e3, e4, {==}, ec), (g, {==}))))
