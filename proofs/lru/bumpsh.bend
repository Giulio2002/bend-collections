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

# Counting on the shadow: fbump(c) increments counter c of the model.


def CountOK(~V: Data, +spec: SP.Lru<V>, r: LR.LRU<&2, V>) -> Type:
  Sigma<&1, &1, ST.Sh<V>, sh2 => {r == ST.real(~V, sh2) : LR.LRU<&2, V>} & ({ST.model(~V, sh2) == spec : SP.Lru<V>} & {ST.good(~V, sh2) == True{} : Bool})>

def lo8(+i: Nat, +h8: {Nat.is_le(8n, i) == True{} : Bool}, +j: Nat, +hj: {Nat.is_lt(j, 8n) == True{} : Bool}) -> {Nat.is_eq(i, j) == False{} : Bool}:
  N.is_eq_sym_false(j, i, N.is_eq_lt(j, i, N.lt_le_trans(j, 8n, i, hj, h8)))

def lo8s(+i: Nat, +h8: {Nat.is_le(8n, i) == True{} : Bool}, +j: Nat, +hj: {Nat.is_lt(j, 8n) == True{} : Bool}) -> {Nat.is_eq(1n+i, j) == False{} : Bool}:
  lo8(1n+i, N.le_trans(8n, i, 1n+i, h8, N.le_succ(i)), j, hj)

def keep(+ml: List<&2, U32>, +m2: AR.Tree<U32>, +i: Nat, +x: U32, +y: U32, +e: {AR.slots(U32, m2) == SC.update(U32, SC.update(U32, ml, i, x), 1n+i, y) : List<&2, U32>}, +j: Nat, +h1: {Nat.is_eq(i, j) == False{} : Bool}, +h2: {Nat.is_eq(1n+i, j) == False{} : Bool}) -> {TB.nth0(AR.slots(U32, m2), j) == TB.nth0(ml, j) : U32}:
  Equal.trans(U32, TB.nth0(AR.slots(U32, m2), j), TB.nth0(SC.update(U32, SC.update(U32, ml, i, x), 1n+i, y), j), TB.nth0(ml, j), Equal.cong(List<&2, U32>, U32, z => TB.nth0(z, j), AR.slots(U32, m2), SC.update(U32, SC.update(U32, ml, i, x), 1n+i, y), e), Equal.trans(U32, TB.nth0(SC.update(U32, SC.update(U32, ml, i, x), 1n+i, y), j), TB.nth0(SC.update(U32, ml, i, x), j), TB.nth0(ml, j), IA.nth0_upd_other(SC.update(U32, ml, i, x), 1n+i, j, y, h2), IA.nth0_upd_other(ml, i, j, x, h1)))


# the meta words of m2: i and i + 1 written, the invariant's words kept
def bm_fin(~V: Data, +cap: U32, +n: U32, +head: U32, +tail: U32, +free: U32, +mT: AR.Tree<U32>, +k: Nat, +sd: Nat, +tabT: AR.Tree<U32>, +ksT: AR.Tree<String>, +eT: AR.Tree<Maybe<&2, V>>, +lkT: AR.Tree<U32>, +sl: List<&2, Nat>, +fl: List<&2, Nat>, +hg: {ST.good(~V, ST.LS{cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, sl, fl}) == True{} : Bool}, +i: Nat, +h8: {Nat.is_le(8n, i) == True{} : Bool}, +m2: AR.Tree<U32>, +pm2: {AR.perfect(U32, 5n, m2) == True{} : Bool}, +x: U32, +y: U32, +e: {AR.slots(U32, m2) == SC.update(U32, SC.update(U32, AR.slots(U32, mT), i, x), 1n+i, y) : List<&2, U32>}) -> {ST.good(~V, ST.LS{cap, n, head, tail, free, m2, k, sd, tabT, ksT, eT, lkT, sl, fl}) == True{} : Bool}:
  MT.good_m(~V, cap, n, head, tail, free, mT, m2, k, sd, tabT, ksT, eT, lkT, sl, fl, hg, keep(AR.slots(U32, mT), m2, i, x, y, e, 0n, lo8(i, h8, 0n, {==}), lo8s(i, h8, 0n, {==})), keep(AR.slots(U32, mT), m2, i, x, y, e, 1n, lo8(i, h8, 1n, {==}), lo8s(i, h8, 1n, {==})), keep(AR.slots(U32, mT), m2, i, x, y, e, 2n, lo8(i, h8, 2n, {==}), lo8s(i, h8, 2n, {==})), keep(AR.slots(U32, mT), m2, i, x, y, e, 6n, lo8(i, h8, 6n, {==}), lo8s(i, h8, 6n, {==})), keep(AR.slots(U32, mT), m2, i, x, y, e, 7n, lo8(i, h8, 7n, {==}), lo8s(i, h8, 7n, {==})), pm2)


def count_ins(~V: Data, +cap: U32, +n: U32, +head: U32, +tail: U32, +free: U32, +mT: AR.Tree<U32>, +k: Nat, +sd: Nat, +tabT: AR.Tree<U32>, +ksT: AR.Tree<String>, +eT: AR.Tree<Maybe<&2, V>>, +lkT: AR.Tree<U32>, +sl: List<&2, Nat>, +fl: List<&2, Nat>, +hg: {ST.good(~V, ST.LS{cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, sl, fl}) == True{} : Bool}, bo: BU.BumpOK(mT, 16n, LR.bump(0, AR.thaw(U32, mT)))) -> CountOK(~V, SP.L{cap, TB.nth0(AR.slots(U32, mT), 3n), ST.w64(AR.slots(U32, mT), 4n), ST.es(~V, AR.slots(U32, lkT), AR.slots(String, ksT), AR.slots(Maybe<&2, V>, eT), sl), SP.c_ins(ST.ctr(AR.slots(U32, mT)))}, LR.fbump(&2, V, 0, ST.real(~V, ST.LS{cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, sl, fl}))):
  match bo:
    case Tuple{+m2, Tuple{+ea, Tuple{+pm2, Tuple{+ew, Tuple{+x, Tuple{+y, e}}}}}}:
      +ee = {e : {AR.slots(U32, m2) == SC.update(U32, SC.update(U32, AR.slots(U32, mT), 16n, x), 1n+16n, y) : List<&2, U32>}}
      +er = Equal.cong(Array<U32>, LR.LRU<&2, V>, z => LR.F{cap, n, head, tail, free, z, AR.thaw(U32, tabT), AR.thaw(String, ksT), AR.thaw(Maybe<&2, V>, eT), AR.thaw(U32, lkT)}, LR.bump(0, AR.thaw(U32, mT)), AR.thaw(U32, m2), ea)
      +g = bm_fin(~V, cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, sl, fl, hg, 16n, {==}, m2, pm2, x, y, ee)
      +e3 = keep(AR.slots(U32, mT), m2, 16n, x, y, ee, 3n, {==}, {==})
      +e4 = BA.w64_eq(AR.slots(U32, m2), AR.slots(U32, mT), 4n, keep(AR.slots(U32, mT), m2, 16n, x, y, ee, 4n, {==}, {==}), keep(AR.slots(U32, mT), m2, 16n, x, y, ee, 5n, {==}, {==}))
      +ec = BA.ct5(ST.w64(AR.slots(U32, m2), 16n), ST.w64(AR.slots(U32, m2), 18n), ST.w64(AR.slots(U32, m2), 20n), ST.w64(AR.slots(U32, m2), 22n), ST.w64(AR.slots(U32, m2), 24n), SP.inc64(ST.w64(AR.slots(U32, mT), 16n)), ST.w64(AR.slots(U32, mT), 18n), ST.w64(AR.slots(U32, mT), 20n), ST.w64(AR.slots(U32, mT), 22n), ST.w64(AR.slots(U32, mT), 24n), ew, BA.w64_eq(AR.slots(U32, m2), AR.slots(U32, mT), 18n, keep(AR.slots(U32, mT), m2, 16n, x, y, ee, 18n, {==}, {==}), keep(AR.slots(U32, mT), m2, 16n, x, y, ee, 19n, {==}, {==})), BA.w64_eq(AR.slots(U32, m2), AR.slots(U32, mT), 20n, keep(AR.slots(U32, mT), m2, 16n, x, y, ee, 20n, {==}, {==}), keep(AR.slots(U32, mT), m2, 16n, x, y, ee, 21n, {==}, {==})), BA.w64_eq(AR.slots(U32, m2), AR.slots(U32, mT), 22n, keep(AR.slots(U32, mT), m2, 16n, x, y, ee, 22n, {==}, {==}), keep(AR.slots(U32, mT), m2, 16n, x, y, ee, 23n, {==}, {==})), BA.w64_eq(AR.slots(U32, m2), AR.slots(U32, mT), 24n, keep(AR.slots(U32, mT), m2, 16n, x, y, ee, 24n, {==}, {==}), keep(AR.slots(U32, mT), m2, 16n, x, y, ee, 25n, {==}, {==})))
      (ST.LS{cap, n, head, tail, free, m2, k, sd, tabT, ksT, eT, lkT, sl, fl}, (er, (BA.lru_eq(~V, cap, TB.nth0(AR.slots(U32, m2), 3n), TB.nth0(AR.slots(U32, mT), 3n), ST.w64(AR.slots(U32, m2), 4n), ST.w64(AR.slots(U32, mT), 4n), ST.es(~V, AR.slots(U32, lkT), AR.slots(String, ksT), AR.slots(Maybe<&2, V>, eT), sl), ST.es(~V, AR.slots(U32, lkT), AR.slots(String, ksT), AR.slots(Maybe<&2, V>, eT), sl), ST.ctr(AR.slots(U32, m2)), SP.c_ins(ST.ctr(AR.slots(U32, mT))), e3, e4, {==}, ec), g)))


def count_ev(~V: Data, +cap: U32, +n: U32, +head: U32, +tail: U32, +free: U32, +mT: AR.Tree<U32>, +k: Nat, +sd: Nat, +tabT: AR.Tree<U32>, +ksT: AR.Tree<String>, +eT: AR.Tree<Maybe<&2, V>>, +lkT: AR.Tree<U32>, +sl: List<&2, Nat>, +fl: List<&2, Nat>, +hg: {ST.good(~V, ST.LS{cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, sl, fl}) == True{} : Bool}, bo: BU.BumpOK(mT, 18n, LR.bump(1, AR.thaw(U32, mT)))) -> CountOK(~V, SP.L{cap, TB.nth0(AR.slots(U32, mT), 3n), ST.w64(AR.slots(U32, mT), 4n), ST.es(~V, AR.slots(U32, lkT), AR.slots(String, ksT), AR.slots(Maybe<&2, V>, eT), sl), SP.c_ev(ST.ctr(AR.slots(U32, mT)))}, LR.fbump(&2, V, 1, ST.real(~V, ST.LS{cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, sl, fl}))):
  match bo:
    case Tuple{+m2, Tuple{+ea, Tuple{+pm2, Tuple{+ew, Tuple{+x, Tuple{+y, e}}}}}}:
      +ee = {e : {AR.slots(U32, m2) == SC.update(U32, SC.update(U32, AR.slots(U32, mT), 18n, x), 1n+18n, y) : List<&2, U32>}}
      +er = Equal.cong(Array<U32>, LR.LRU<&2, V>, z => LR.F{cap, n, head, tail, free, z, AR.thaw(U32, tabT), AR.thaw(String, ksT), AR.thaw(Maybe<&2, V>, eT), AR.thaw(U32, lkT)}, LR.bump(1, AR.thaw(U32, mT)), AR.thaw(U32, m2), ea)
      +g = bm_fin(~V, cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, sl, fl, hg, 18n, {==}, m2, pm2, x, y, ee)
      +e3 = keep(AR.slots(U32, mT), m2, 18n, x, y, ee, 3n, {==}, {==})
      +e4 = BA.w64_eq(AR.slots(U32, m2), AR.slots(U32, mT), 4n, keep(AR.slots(U32, mT), m2, 18n, x, y, ee, 4n, {==}, {==}), keep(AR.slots(U32, mT), m2, 18n, x, y, ee, 5n, {==}, {==}))
      +ec = BA.ct5(ST.w64(AR.slots(U32, m2), 16n), ST.w64(AR.slots(U32, m2), 18n), ST.w64(AR.slots(U32, m2), 20n), ST.w64(AR.slots(U32, m2), 22n), ST.w64(AR.slots(U32, m2), 24n), ST.w64(AR.slots(U32, mT), 16n), SP.inc64(ST.w64(AR.slots(U32, mT), 18n)), ST.w64(AR.slots(U32, mT), 20n), ST.w64(AR.slots(U32, mT), 22n), ST.w64(AR.slots(U32, mT), 24n), BA.w64_eq(AR.slots(U32, m2), AR.slots(U32, mT), 16n, keep(AR.slots(U32, mT), m2, 18n, x, y, ee, 16n, {==}, {==}), keep(AR.slots(U32, mT), m2, 18n, x, y, ee, 17n, {==}, {==})), ew, BA.w64_eq(AR.slots(U32, m2), AR.slots(U32, mT), 20n, keep(AR.slots(U32, mT), m2, 18n, x, y, ee, 20n, {==}, {==}), keep(AR.slots(U32, mT), m2, 18n, x, y, ee, 21n, {==}, {==})), BA.w64_eq(AR.slots(U32, m2), AR.slots(U32, mT), 22n, keep(AR.slots(U32, mT), m2, 18n, x, y, ee, 22n, {==}, {==}), keep(AR.slots(U32, mT), m2, 18n, x, y, ee, 23n, {==}, {==})), BA.w64_eq(AR.slots(U32, m2), AR.slots(U32, mT), 24n, keep(AR.slots(U32, mT), m2, 18n, x, y, ee, 24n, {==}, {==}), keep(AR.slots(U32, mT), m2, 18n, x, y, ee, 25n, {==}, {==})))
      (ST.LS{cap, n, head, tail, free, m2, k, sd, tabT, ksT, eT, lkT, sl, fl}, (er, (BA.lru_eq(~V, cap, TB.nth0(AR.slots(U32, m2), 3n), TB.nth0(AR.slots(U32, mT), 3n), ST.w64(AR.slots(U32, m2), 4n), ST.w64(AR.slots(U32, mT), 4n), ST.es(~V, AR.slots(U32, lkT), AR.slots(String, ksT), AR.slots(Maybe<&2, V>, eT), sl), ST.es(~V, AR.slots(U32, lkT), AR.slots(String, ksT), AR.slots(Maybe<&2, V>, eT), sl), ST.ctr(AR.slots(U32, m2)), SP.c_ev(ST.ctr(AR.slots(U32, mT))), e3, e4, {==}, ec), g)))


def count_rm(~V: Data, +cap: U32, +n: U32, +head: U32, +tail: U32, +free: U32, +mT: AR.Tree<U32>, +k: Nat, +sd: Nat, +tabT: AR.Tree<U32>, +ksT: AR.Tree<String>, +eT: AR.Tree<Maybe<&2, V>>, +lkT: AR.Tree<U32>, +sl: List<&2, Nat>, +fl: List<&2, Nat>, +hg: {ST.good(~V, ST.LS{cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, sl, fl}) == True{} : Bool}, bo: BU.BumpOK(mT, 20n, LR.bump(2, AR.thaw(U32, mT)))) -> CountOK(~V, SP.L{cap, TB.nth0(AR.slots(U32, mT), 3n), ST.w64(AR.slots(U32, mT), 4n), ST.es(~V, AR.slots(U32, lkT), AR.slots(String, ksT), AR.slots(Maybe<&2, V>, eT), sl), SP.c_rm(ST.ctr(AR.slots(U32, mT)))}, LR.fbump(&2, V, 2, ST.real(~V, ST.LS{cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, sl, fl}))):
  match bo:
    case Tuple{+m2, Tuple{+ea, Tuple{+pm2, Tuple{+ew, Tuple{+x, Tuple{+y, e}}}}}}:
      +ee = {e : {AR.slots(U32, m2) == SC.update(U32, SC.update(U32, AR.slots(U32, mT), 20n, x), 1n+20n, y) : List<&2, U32>}}
      +er = Equal.cong(Array<U32>, LR.LRU<&2, V>, z => LR.F{cap, n, head, tail, free, z, AR.thaw(U32, tabT), AR.thaw(String, ksT), AR.thaw(Maybe<&2, V>, eT), AR.thaw(U32, lkT)}, LR.bump(2, AR.thaw(U32, mT)), AR.thaw(U32, m2), ea)
      +g = bm_fin(~V, cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, sl, fl, hg, 20n, {==}, m2, pm2, x, y, ee)
      +e3 = keep(AR.slots(U32, mT), m2, 20n, x, y, ee, 3n, {==}, {==})
      +e4 = BA.w64_eq(AR.slots(U32, m2), AR.slots(U32, mT), 4n, keep(AR.slots(U32, mT), m2, 20n, x, y, ee, 4n, {==}, {==}), keep(AR.slots(U32, mT), m2, 20n, x, y, ee, 5n, {==}, {==}))
      +ec = BA.ct5(ST.w64(AR.slots(U32, m2), 16n), ST.w64(AR.slots(U32, m2), 18n), ST.w64(AR.slots(U32, m2), 20n), ST.w64(AR.slots(U32, m2), 22n), ST.w64(AR.slots(U32, m2), 24n), ST.w64(AR.slots(U32, mT), 16n), ST.w64(AR.slots(U32, mT), 18n), SP.inc64(ST.w64(AR.slots(U32, mT), 20n)), ST.w64(AR.slots(U32, mT), 22n), ST.w64(AR.slots(U32, mT), 24n), BA.w64_eq(AR.slots(U32, m2), AR.slots(U32, mT), 16n, keep(AR.slots(U32, mT), m2, 20n, x, y, ee, 16n, {==}, {==}), keep(AR.slots(U32, mT), m2, 20n, x, y, ee, 17n, {==}, {==})), BA.w64_eq(AR.slots(U32, m2), AR.slots(U32, mT), 18n, keep(AR.slots(U32, mT), m2, 20n, x, y, ee, 18n, {==}, {==}), keep(AR.slots(U32, mT), m2, 20n, x, y, ee, 19n, {==}, {==})), ew, BA.w64_eq(AR.slots(U32, m2), AR.slots(U32, mT), 22n, keep(AR.slots(U32, mT), m2, 20n, x, y, ee, 22n, {==}, {==}), keep(AR.slots(U32, mT), m2, 20n, x, y, ee, 23n, {==}, {==})), BA.w64_eq(AR.slots(U32, m2), AR.slots(U32, mT), 24n, keep(AR.slots(U32, mT), m2, 20n, x, y, ee, 24n, {==}, {==}), keep(AR.slots(U32, mT), m2, 20n, x, y, ee, 25n, {==}, {==})))
      (ST.LS{cap, n, head, tail, free, m2, k, sd, tabT, ksT, eT, lkT, sl, fl}, (er, (BA.lru_eq(~V, cap, TB.nth0(AR.slots(U32, m2), 3n), TB.nth0(AR.slots(U32, mT), 3n), ST.w64(AR.slots(U32, m2), 4n), ST.w64(AR.slots(U32, mT), 4n), ST.es(~V, AR.slots(U32, lkT), AR.slots(String, ksT), AR.slots(Maybe<&2, V>, eT), sl), ST.es(~V, AR.slots(U32, lkT), AR.slots(String, ksT), AR.slots(Maybe<&2, V>, eT), sl), ST.ctr(AR.slots(U32, m2)), SP.c_rm(ST.ctr(AR.slots(U32, mT))), e3, e4, {==}, ec), g)))


def count_hit(~V: Data, +cap: U32, +n: U32, +head: U32, +tail: U32, +free: U32, +mT: AR.Tree<U32>, +k: Nat, +sd: Nat, +tabT: AR.Tree<U32>, +ksT: AR.Tree<String>, +eT: AR.Tree<Maybe<&2, V>>, +lkT: AR.Tree<U32>, +sl: List<&2, Nat>, +fl: List<&2, Nat>, +hg: {ST.good(~V, ST.LS{cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, sl, fl}) == True{} : Bool}, bo: BU.BumpOK(mT, 22n, LR.bump(3, AR.thaw(U32, mT)))) -> CountOK(~V, SP.L{cap, TB.nth0(AR.slots(U32, mT), 3n), ST.w64(AR.slots(U32, mT), 4n), ST.es(~V, AR.slots(U32, lkT), AR.slots(String, ksT), AR.slots(Maybe<&2, V>, eT), sl), SP.c_hit(ST.ctr(AR.slots(U32, mT)))}, LR.fbump(&2, V, 3, ST.real(~V, ST.LS{cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, sl, fl}))):
  match bo:
    case Tuple{+m2, Tuple{+ea, Tuple{+pm2, Tuple{+ew, Tuple{+x, Tuple{+y, e}}}}}}:
      +ee = {e : {AR.slots(U32, m2) == SC.update(U32, SC.update(U32, AR.slots(U32, mT), 22n, x), 1n+22n, y) : List<&2, U32>}}
      +er = Equal.cong(Array<U32>, LR.LRU<&2, V>, z => LR.F{cap, n, head, tail, free, z, AR.thaw(U32, tabT), AR.thaw(String, ksT), AR.thaw(Maybe<&2, V>, eT), AR.thaw(U32, lkT)}, LR.bump(3, AR.thaw(U32, mT)), AR.thaw(U32, m2), ea)
      +g = bm_fin(~V, cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, sl, fl, hg, 22n, {==}, m2, pm2, x, y, ee)
      +e3 = keep(AR.slots(U32, mT), m2, 22n, x, y, ee, 3n, {==}, {==})
      +e4 = BA.w64_eq(AR.slots(U32, m2), AR.slots(U32, mT), 4n, keep(AR.slots(U32, mT), m2, 22n, x, y, ee, 4n, {==}, {==}), keep(AR.slots(U32, mT), m2, 22n, x, y, ee, 5n, {==}, {==}))
      +ec = BA.ct5(ST.w64(AR.slots(U32, m2), 16n), ST.w64(AR.slots(U32, m2), 18n), ST.w64(AR.slots(U32, m2), 20n), ST.w64(AR.slots(U32, m2), 22n), ST.w64(AR.slots(U32, m2), 24n), ST.w64(AR.slots(U32, mT), 16n), ST.w64(AR.slots(U32, mT), 18n), ST.w64(AR.slots(U32, mT), 20n), SP.inc64(ST.w64(AR.slots(U32, mT), 22n)), ST.w64(AR.slots(U32, mT), 24n), BA.w64_eq(AR.slots(U32, m2), AR.slots(U32, mT), 16n, keep(AR.slots(U32, mT), m2, 22n, x, y, ee, 16n, {==}, {==}), keep(AR.slots(U32, mT), m2, 22n, x, y, ee, 17n, {==}, {==})), BA.w64_eq(AR.slots(U32, m2), AR.slots(U32, mT), 18n, keep(AR.slots(U32, mT), m2, 22n, x, y, ee, 18n, {==}, {==}), keep(AR.slots(U32, mT), m2, 22n, x, y, ee, 19n, {==}, {==})), BA.w64_eq(AR.slots(U32, m2), AR.slots(U32, mT), 20n, keep(AR.slots(U32, mT), m2, 22n, x, y, ee, 20n, {==}, {==}), keep(AR.slots(U32, mT), m2, 22n, x, y, ee, 21n, {==}, {==})), ew, BA.w64_eq(AR.slots(U32, m2), AR.slots(U32, mT), 24n, keep(AR.slots(U32, mT), m2, 22n, x, y, ee, 24n, {==}, {==}), keep(AR.slots(U32, mT), m2, 22n, x, y, ee, 25n, {==}, {==})))
      (ST.LS{cap, n, head, tail, free, m2, k, sd, tabT, ksT, eT, lkT, sl, fl}, (er, (BA.lru_eq(~V, cap, TB.nth0(AR.slots(U32, m2), 3n), TB.nth0(AR.slots(U32, mT), 3n), ST.w64(AR.slots(U32, m2), 4n), ST.w64(AR.slots(U32, mT), 4n), ST.es(~V, AR.slots(U32, lkT), AR.slots(String, ksT), AR.slots(Maybe<&2, V>, eT), sl), ST.es(~V, AR.slots(U32, lkT), AR.slots(String, ksT), AR.slots(Maybe<&2, V>, eT), sl), ST.ctr(AR.slots(U32, m2)), SP.c_hit(ST.ctr(AR.slots(U32, mT))), e3, e4, {==}, ec), g)))


def count_miss(~V: Data, +cap: U32, +n: U32, +head: U32, +tail: U32, +free: U32, +mT: AR.Tree<U32>, +k: Nat, +sd: Nat, +tabT: AR.Tree<U32>, +ksT: AR.Tree<String>, +eT: AR.Tree<Maybe<&2, V>>, +lkT: AR.Tree<U32>, +sl: List<&2, Nat>, +fl: List<&2, Nat>, +hg: {ST.good(~V, ST.LS{cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, sl, fl}) == True{} : Bool}, bo: BU.BumpOK(mT, 24n, LR.bump(4, AR.thaw(U32, mT)))) -> CountOK(~V, SP.L{cap, TB.nth0(AR.slots(U32, mT), 3n), ST.w64(AR.slots(U32, mT), 4n), ST.es(~V, AR.slots(U32, lkT), AR.slots(String, ksT), AR.slots(Maybe<&2, V>, eT), sl), SP.c_miss(ST.ctr(AR.slots(U32, mT)))}, LR.fbump(&2, V, 4, ST.real(~V, ST.LS{cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, sl, fl}))):
  match bo:
    case Tuple{+m2, Tuple{+ea, Tuple{+pm2, Tuple{+ew, Tuple{+x, Tuple{+y, e}}}}}}:
      +ee = {e : {AR.slots(U32, m2) == SC.update(U32, SC.update(U32, AR.slots(U32, mT), 24n, x), 1n+24n, y) : List<&2, U32>}}
      +er = Equal.cong(Array<U32>, LR.LRU<&2, V>, z => LR.F{cap, n, head, tail, free, z, AR.thaw(U32, tabT), AR.thaw(String, ksT), AR.thaw(Maybe<&2, V>, eT), AR.thaw(U32, lkT)}, LR.bump(4, AR.thaw(U32, mT)), AR.thaw(U32, m2), ea)
      +g = bm_fin(~V, cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, sl, fl, hg, 24n, {==}, m2, pm2, x, y, ee)
      +e3 = keep(AR.slots(U32, mT), m2, 24n, x, y, ee, 3n, {==}, {==})
      +e4 = BA.w64_eq(AR.slots(U32, m2), AR.slots(U32, mT), 4n, keep(AR.slots(U32, mT), m2, 24n, x, y, ee, 4n, {==}, {==}), keep(AR.slots(U32, mT), m2, 24n, x, y, ee, 5n, {==}, {==}))
      +ec = BA.ct5(ST.w64(AR.slots(U32, m2), 16n), ST.w64(AR.slots(U32, m2), 18n), ST.w64(AR.slots(U32, m2), 20n), ST.w64(AR.slots(U32, m2), 22n), ST.w64(AR.slots(U32, m2), 24n), ST.w64(AR.slots(U32, mT), 16n), ST.w64(AR.slots(U32, mT), 18n), ST.w64(AR.slots(U32, mT), 20n), ST.w64(AR.slots(U32, mT), 22n), SP.inc64(ST.w64(AR.slots(U32, mT), 24n)), BA.w64_eq(AR.slots(U32, m2), AR.slots(U32, mT), 16n, keep(AR.slots(U32, mT), m2, 24n, x, y, ee, 16n, {==}, {==}), keep(AR.slots(U32, mT), m2, 24n, x, y, ee, 17n, {==}, {==})), BA.w64_eq(AR.slots(U32, m2), AR.slots(U32, mT), 18n, keep(AR.slots(U32, mT), m2, 24n, x, y, ee, 18n, {==}, {==}), keep(AR.slots(U32, mT), m2, 24n, x, y, ee, 19n, {==}, {==})), BA.w64_eq(AR.slots(U32, m2), AR.slots(U32, mT), 20n, keep(AR.slots(U32, mT), m2, 24n, x, y, ee, 20n, {==}, {==}), keep(AR.slots(U32, mT), m2, 24n, x, y, ee, 21n, {==}, {==})), BA.w64_eq(AR.slots(U32, m2), AR.slots(U32, mT), 22n, keep(AR.slots(U32, mT), m2, 24n, x, y, ee, 22n, {==}, {==}), keep(AR.slots(U32, mT), m2, 24n, x, y, ee, 23n, {==}, {==})), ew)
      (ST.LS{cap, n, head, tail, free, m2, k, sd, tabT, ksT, eT, lkT, sl, fl}, (er, (BA.lru_eq(~V, cap, TB.nth0(AR.slots(U32, m2), 3n), TB.nth0(AR.slots(U32, mT), 3n), ST.w64(AR.slots(U32, m2), 4n), ST.w64(AR.slots(U32, mT), 4n), ST.es(~V, AR.slots(U32, lkT), AR.slots(String, ksT), AR.slots(Maybe<&2, V>, eT), sl), ST.es(~V, AR.slots(U32, lkT), AR.slots(String, ksT), AR.slots(Maybe<&2, V>, eT), sl), ST.ctr(AR.slots(U32, m2)), SP.c_miss(ST.ctr(AR.slots(U32, mT))), e3, e4, {==}, ec), g)))


# ---- counting with the new meta tree exposed, and on any shadow ----

def CntM(~V: Data, +cap: U32, +n: U32, +head: U32, +tail: U32, +free: U32, +mT: AR.Tree<U32>, +k: Nat, +sd: Nat, +tabT: AR.Tree<U32>, +ksT: AR.Tree<String>, +eT: AR.Tree<Maybe<&2, V>>, +lkT: AR.Tree<U32>, +sl: List<&2, Nat>, +fl: List<&2, Nat>, +spec: SP.Lru<V>, r: LR.LRU<&2, V>) -> Type:
  Sigma<&1, &1, AR.Tree<U32>, m2 => {r == ST.real(~V, ST.LS{cap, n, head, tail, free, m2, k, sd, tabT, ksT, eT, lkT, sl, fl}) : LR.LRU<&2, V>} & ({ST.model(~V, ST.LS{cap, n, head, tail, free, m2, k, sd, tabT, ksT, eT, lkT, sl, fl}) == spec : SP.Lru<V>} & {ST.good(~V, ST.LS{cap, n, head, tail, free, m2, k, sd, tabT, ksT, eT, lkT, sl, fl}) == True{} : Bool})>

def cntm_ins(~V: Data, +cap: U32, +n: U32, +head: U32, +tail: U32, +free: U32, +mT: AR.Tree<U32>, +k: Nat, +sd: Nat, +tabT: AR.Tree<U32>, +ksT: AR.Tree<String>, +eT: AR.Tree<Maybe<&2, V>>, +lkT: AR.Tree<U32>, +sl: List<&2, Nat>, +fl: List<&2, Nat>, +hg: {ST.good(~V, ST.LS{cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, sl, fl}) == True{} : Bool}, bo: BU.BumpOK(mT, 16n, LR.bump(0, AR.thaw(U32, mT)))) -> CntM(~V, cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, sl, fl, SP.L{cap, TB.nth0(AR.slots(U32, mT), 3n), ST.w64(AR.slots(U32, mT), 4n), ST.es(~V, AR.slots(U32, lkT), AR.slots(String, ksT), AR.slots(Maybe<&2, V>, eT), sl), SP.c_ins(ST.ctr(AR.slots(U32, mT)))}, LR.fbump(&2, V, 0, ST.real(~V, ST.LS{cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, sl, fl}))):
  match bo:
    case Tuple{+m2, Tuple{+ea, Tuple{+pm2, Tuple{+ew, Tuple{+x, Tuple{+y, e}}}}}}:
      +ee = {e : {AR.slots(U32, m2) == SC.update(U32, SC.update(U32, AR.slots(U32, mT), 16n, x), 1n+16n, y) : List<&2, U32>}}
      +er = Equal.cong(Array<U32>, LR.LRU<&2, V>, z => LR.F{cap, n, head, tail, free, z, AR.thaw(U32, tabT), AR.thaw(String, ksT), AR.thaw(Maybe<&2, V>, eT), AR.thaw(U32, lkT)}, LR.bump(0, AR.thaw(U32, mT)), AR.thaw(U32, m2), ea)
      +g = bm_fin(~V, cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, sl, fl, hg, 16n, {==}, m2, pm2, x, y, ee)
      +e3 = keep(AR.slots(U32, mT), m2, 16n, x, y, ee, 3n, {==}, {==})
      +e4 = BA.w64_eq(AR.slots(U32, m2), AR.slots(U32, mT), 4n, keep(AR.slots(U32, mT), m2, 16n, x, y, ee, 4n, {==}, {==}), keep(AR.slots(U32, mT), m2, 16n, x, y, ee, 5n, {==}, {==}))
      +ec = BA.ct5(ST.w64(AR.slots(U32, m2), 16n), ST.w64(AR.slots(U32, m2), 18n), ST.w64(AR.slots(U32, m2), 20n), ST.w64(AR.slots(U32, m2), 22n), ST.w64(AR.slots(U32, m2), 24n), SP.inc64(ST.w64(AR.slots(U32, mT), 16n)), ST.w64(AR.slots(U32, mT), 18n), ST.w64(AR.slots(U32, mT), 20n), ST.w64(AR.slots(U32, mT), 22n), ST.w64(AR.slots(U32, mT), 24n), ew, BA.w64_eq(AR.slots(U32, m2), AR.slots(U32, mT), 18n, keep(AR.slots(U32, mT), m2, 16n, x, y, ee, 18n, {==}, {==}), keep(AR.slots(U32, mT), m2, 16n, x, y, ee, 19n, {==}, {==})), BA.w64_eq(AR.slots(U32, m2), AR.slots(U32, mT), 20n, keep(AR.slots(U32, mT), m2, 16n, x, y, ee, 20n, {==}, {==}), keep(AR.slots(U32, mT), m2, 16n, x, y, ee, 21n, {==}, {==})), BA.w64_eq(AR.slots(U32, m2), AR.slots(U32, mT), 22n, keep(AR.slots(U32, mT), m2, 16n, x, y, ee, 22n, {==}, {==}), keep(AR.slots(U32, mT), m2, 16n, x, y, ee, 23n, {==}, {==})), BA.w64_eq(AR.slots(U32, m2), AR.slots(U32, mT), 24n, keep(AR.slots(U32, mT), m2, 16n, x, y, ee, 24n, {==}, {==}), keep(AR.slots(U32, mT), m2, 16n, x, y, ee, 25n, {==}, {==})))
      (m2, (er, (BA.lru_eq(~V, cap, TB.nth0(AR.slots(U32, m2), 3n), TB.nth0(AR.slots(U32, mT), 3n), ST.w64(AR.slots(U32, m2), 4n), ST.w64(AR.slots(U32, mT), 4n), ST.es(~V, AR.slots(U32, lkT), AR.slots(String, ksT), AR.slots(Maybe<&2, V>, eT), sl), ST.es(~V, AR.slots(U32, lkT), AR.slots(String, ksT), AR.slots(Maybe<&2, V>, eT), sl), ST.ctr(AR.slots(U32, m2)), SP.c_ins(ST.ctr(AR.slots(U32, mT))), e3, e4, {==}, ec), g)))

def cg_ins(~V: Data, l: SP.Lru<V>) -> SP.Lru<V>:
  match l:
    case SP.L{cap, on, life, es, c}:
      SP.L{cap, on, life, es, SP.c_ins(c)}

# THEOREM: fbump(0) counts on any shadow
def countg_ins(~V: Data, +sh: ST.Sh<V>, +hg: {ST.good(~V, sh) == True{} : Bool}) -> CountOK(~V, cg_ins(~V, ST.model(~V, sh)), LR.fbump(&2, V, 0, ST.real(~V, sh))):
  match sh:
    case ST.LS{cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, sl, fl}:
      count_ins(~V, cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, sl, fl, hg, BU.bump_ok(mT, ST.g_cpm(~V, cap, n, head, tail, free, TB.nth0(AR.slots(U32, mT), 0n), TB.nth0(AR.slots(U32, mT), 1n), TB.nth0(AR.slots(U32, mT), 2n), TB.nth0(AR.slots(U32, mT), 6n), TB.nth0(AR.slots(U32, mT), 7n), AR.perfect(U32, 5n, mT), k, sd, tabT, AR.slots(String, ksT), AR.perfect(String, sd, ksT), eT, lkT, sl, fl, hg), 0, 16n, {==}, {==}, {==}))

def cntm_ev(~V: Data, +cap: U32, +n: U32, +head: U32, +tail: U32, +free: U32, +mT: AR.Tree<U32>, +k: Nat, +sd: Nat, +tabT: AR.Tree<U32>, +ksT: AR.Tree<String>, +eT: AR.Tree<Maybe<&2, V>>, +lkT: AR.Tree<U32>, +sl: List<&2, Nat>, +fl: List<&2, Nat>, +hg: {ST.good(~V, ST.LS{cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, sl, fl}) == True{} : Bool}, bo: BU.BumpOK(mT, 18n, LR.bump(1, AR.thaw(U32, mT)))) -> CntM(~V, cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, sl, fl, SP.L{cap, TB.nth0(AR.slots(U32, mT), 3n), ST.w64(AR.slots(U32, mT), 4n), ST.es(~V, AR.slots(U32, lkT), AR.slots(String, ksT), AR.slots(Maybe<&2, V>, eT), sl), SP.c_ev(ST.ctr(AR.slots(U32, mT)))}, LR.fbump(&2, V, 1, ST.real(~V, ST.LS{cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, sl, fl}))):
  match bo:
    case Tuple{+m2, Tuple{+ea, Tuple{+pm2, Tuple{+ew, Tuple{+x, Tuple{+y, e}}}}}}:
      +ee = {e : {AR.slots(U32, m2) == SC.update(U32, SC.update(U32, AR.slots(U32, mT), 18n, x), 1n+18n, y) : List<&2, U32>}}
      +er = Equal.cong(Array<U32>, LR.LRU<&2, V>, z => LR.F{cap, n, head, tail, free, z, AR.thaw(U32, tabT), AR.thaw(String, ksT), AR.thaw(Maybe<&2, V>, eT), AR.thaw(U32, lkT)}, LR.bump(1, AR.thaw(U32, mT)), AR.thaw(U32, m2), ea)
      +g = bm_fin(~V, cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, sl, fl, hg, 18n, {==}, m2, pm2, x, y, ee)
      +e3 = keep(AR.slots(U32, mT), m2, 18n, x, y, ee, 3n, {==}, {==})
      +e4 = BA.w64_eq(AR.slots(U32, m2), AR.slots(U32, mT), 4n, keep(AR.slots(U32, mT), m2, 18n, x, y, ee, 4n, {==}, {==}), keep(AR.slots(U32, mT), m2, 18n, x, y, ee, 5n, {==}, {==}))
      +ec = BA.ct5(ST.w64(AR.slots(U32, m2), 16n), ST.w64(AR.slots(U32, m2), 18n), ST.w64(AR.slots(U32, m2), 20n), ST.w64(AR.slots(U32, m2), 22n), ST.w64(AR.slots(U32, m2), 24n), ST.w64(AR.slots(U32, mT), 16n), SP.inc64(ST.w64(AR.slots(U32, mT), 18n)), ST.w64(AR.slots(U32, mT), 20n), ST.w64(AR.slots(U32, mT), 22n), ST.w64(AR.slots(U32, mT), 24n), BA.w64_eq(AR.slots(U32, m2), AR.slots(U32, mT), 16n, keep(AR.slots(U32, mT), m2, 18n, x, y, ee, 16n, {==}, {==}), keep(AR.slots(U32, mT), m2, 18n, x, y, ee, 17n, {==}, {==})), ew, BA.w64_eq(AR.slots(U32, m2), AR.slots(U32, mT), 20n, keep(AR.slots(U32, mT), m2, 18n, x, y, ee, 20n, {==}, {==}), keep(AR.slots(U32, mT), m2, 18n, x, y, ee, 21n, {==}, {==})), BA.w64_eq(AR.slots(U32, m2), AR.slots(U32, mT), 22n, keep(AR.slots(U32, mT), m2, 18n, x, y, ee, 22n, {==}, {==}), keep(AR.slots(U32, mT), m2, 18n, x, y, ee, 23n, {==}, {==})), BA.w64_eq(AR.slots(U32, m2), AR.slots(U32, mT), 24n, keep(AR.slots(U32, mT), m2, 18n, x, y, ee, 24n, {==}, {==}), keep(AR.slots(U32, mT), m2, 18n, x, y, ee, 25n, {==}, {==})))
      (m2, (er, (BA.lru_eq(~V, cap, TB.nth0(AR.slots(U32, m2), 3n), TB.nth0(AR.slots(U32, mT), 3n), ST.w64(AR.slots(U32, m2), 4n), ST.w64(AR.slots(U32, mT), 4n), ST.es(~V, AR.slots(U32, lkT), AR.slots(String, ksT), AR.slots(Maybe<&2, V>, eT), sl), ST.es(~V, AR.slots(U32, lkT), AR.slots(String, ksT), AR.slots(Maybe<&2, V>, eT), sl), ST.ctr(AR.slots(U32, m2)), SP.c_ev(ST.ctr(AR.slots(U32, mT))), e3, e4, {==}, ec), g)))

def cg_ev(~V: Data, l: SP.Lru<V>) -> SP.Lru<V>:
  match l:
    case SP.L{cap, on, life, es, c}:
      SP.L{cap, on, life, es, SP.c_ev(c)}

# THEOREM: fbump(1) counts on any shadow
def countg_ev(~V: Data, +sh: ST.Sh<V>, +hg: {ST.good(~V, sh) == True{} : Bool}) -> CountOK(~V, cg_ev(~V, ST.model(~V, sh)), LR.fbump(&2, V, 1, ST.real(~V, sh))):
  match sh:
    case ST.LS{cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, sl, fl}:
      count_ev(~V, cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, sl, fl, hg, BU.bump_ok(mT, ST.g_cpm(~V, cap, n, head, tail, free, TB.nth0(AR.slots(U32, mT), 0n), TB.nth0(AR.slots(U32, mT), 1n), TB.nth0(AR.slots(U32, mT), 2n), TB.nth0(AR.slots(U32, mT), 6n), TB.nth0(AR.slots(U32, mT), 7n), AR.perfect(U32, 5n, mT), k, sd, tabT, AR.slots(String, ksT), AR.perfect(String, sd, ksT), eT, lkT, sl, fl, hg), 1, 18n, {==}, {==}, {==}))

def cntm_rm(~V: Data, +cap: U32, +n: U32, +head: U32, +tail: U32, +free: U32, +mT: AR.Tree<U32>, +k: Nat, +sd: Nat, +tabT: AR.Tree<U32>, +ksT: AR.Tree<String>, +eT: AR.Tree<Maybe<&2, V>>, +lkT: AR.Tree<U32>, +sl: List<&2, Nat>, +fl: List<&2, Nat>, +hg: {ST.good(~V, ST.LS{cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, sl, fl}) == True{} : Bool}, bo: BU.BumpOK(mT, 20n, LR.bump(2, AR.thaw(U32, mT)))) -> CntM(~V, cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, sl, fl, SP.L{cap, TB.nth0(AR.slots(U32, mT), 3n), ST.w64(AR.slots(U32, mT), 4n), ST.es(~V, AR.slots(U32, lkT), AR.slots(String, ksT), AR.slots(Maybe<&2, V>, eT), sl), SP.c_rm(ST.ctr(AR.slots(U32, mT)))}, LR.fbump(&2, V, 2, ST.real(~V, ST.LS{cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, sl, fl}))):
  match bo:
    case Tuple{+m2, Tuple{+ea, Tuple{+pm2, Tuple{+ew, Tuple{+x, Tuple{+y, e}}}}}}:
      +ee = {e : {AR.slots(U32, m2) == SC.update(U32, SC.update(U32, AR.slots(U32, mT), 20n, x), 1n+20n, y) : List<&2, U32>}}
      +er = Equal.cong(Array<U32>, LR.LRU<&2, V>, z => LR.F{cap, n, head, tail, free, z, AR.thaw(U32, tabT), AR.thaw(String, ksT), AR.thaw(Maybe<&2, V>, eT), AR.thaw(U32, lkT)}, LR.bump(2, AR.thaw(U32, mT)), AR.thaw(U32, m2), ea)
      +g = bm_fin(~V, cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, sl, fl, hg, 20n, {==}, m2, pm2, x, y, ee)
      +e3 = keep(AR.slots(U32, mT), m2, 20n, x, y, ee, 3n, {==}, {==})
      +e4 = BA.w64_eq(AR.slots(U32, m2), AR.slots(U32, mT), 4n, keep(AR.slots(U32, mT), m2, 20n, x, y, ee, 4n, {==}, {==}), keep(AR.slots(U32, mT), m2, 20n, x, y, ee, 5n, {==}, {==}))
      +ec = BA.ct5(ST.w64(AR.slots(U32, m2), 16n), ST.w64(AR.slots(U32, m2), 18n), ST.w64(AR.slots(U32, m2), 20n), ST.w64(AR.slots(U32, m2), 22n), ST.w64(AR.slots(U32, m2), 24n), ST.w64(AR.slots(U32, mT), 16n), ST.w64(AR.slots(U32, mT), 18n), SP.inc64(ST.w64(AR.slots(U32, mT), 20n)), ST.w64(AR.slots(U32, mT), 22n), ST.w64(AR.slots(U32, mT), 24n), BA.w64_eq(AR.slots(U32, m2), AR.slots(U32, mT), 16n, keep(AR.slots(U32, mT), m2, 20n, x, y, ee, 16n, {==}, {==}), keep(AR.slots(U32, mT), m2, 20n, x, y, ee, 17n, {==}, {==})), BA.w64_eq(AR.slots(U32, m2), AR.slots(U32, mT), 18n, keep(AR.slots(U32, mT), m2, 20n, x, y, ee, 18n, {==}, {==}), keep(AR.slots(U32, mT), m2, 20n, x, y, ee, 19n, {==}, {==})), ew, BA.w64_eq(AR.slots(U32, m2), AR.slots(U32, mT), 22n, keep(AR.slots(U32, mT), m2, 20n, x, y, ee, 22n, {==}, {==}), keep(AR.slots(U32, mT), m2, 20n, x, y, ee, 23n, {==}, {==})), BA.w64_eq(AR.slots(U32, m2), AR.slots(U32, mT), 24n, keep(AR.slots(U32, mT), m2, 20n, x, y, ee, 24n, {==}, {==}), keep(AR.slots(U32, mT), m2, 20n, x, y, ee, 25n, {==}, {==})))
      (m2, (er, (BA.lru_eq(~V, cap, TB.nth0(AR.slots(U32, m2), 3n), TB.nth0(AR.slots(U32, mT), 3n), ST.w64(AR.slots(U32, m2), 4n), ST.w64(AR.slots(U32, mT), 4n), ST.es(~V, AR.slots(U32, lkT), AR.slots(String, ksT), AR.slots(Maybe<&2, V>, eT), sl), ST.es(~V, AR.slots(U32, lkT), AR.slots(String, ksT), AR.slots(Maybe<&2, V>, eT), sl), ST.ctr(AR.slots(U32, m2)), SP.c_rm(ST.ctr(AR.slots(U32, mT))), e3, e4, {==}, ec), g)))

def cg_rm(~V: Data, l: SP.Lru<V>) -> SP.Lru<V>:
  match l:
    case SP.L{cap, on, life, es, c}:
      SP.L{cap, on, life, es, SP.c_rm(c)}

# THEOREM: fbump(2) counts on any shadow
def countg_rm(~V: Data, +sh: ST.Sh<V>, +hg: {ST.good(~V, sh) == True{} : Bool}) -> CountOK(~V, cg_rm(~V, ST.model(~V, sh)), LR.fbump(&2, V, 2, ST.real(~V, sh))):
  match sh:
    case ST.LS{cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, sl, fl}:
      count_rm(~V, cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, sl, fl, hg, BU.bump_ok(mT, ST.g_cpm(~V, cap, n, head, tail, free, TB.nth0(AR.slots(U32, mT), 0n), TB.nth0(AR.slots(U32, mT), 1n), TB.nth0(AR.slots(U32, mT), 2n), TB.nth0(AR.slots(U32, mT), 6n), TB.nth0(AR.slots(U32, mT), 7n), AR.perfect(U32, 5n, mT), k, sd, tabT, AR.slots(String, ksT), AR.perfect(String, sd, ksT), eT, lkT, sl, fl, hg), 2, 20n, {==}, {==}, {==}))

def cntm_hit(~V: Data, +cap: U32, +n: U32, +head: U32, +tail: U32, +free: U32, +mT: AR.Tree<U32>, +k: Nat, +sd: Nat, +tabT: AR.Tree<U32>, +ksT: AR.Tree<String>, +eT: AR.Tree<Maybe<&2, V>>, +lkT: AR.Tree<U32>, +sl: List<&2, Nat>, +fl: List<&2, Nat>, +hg: {ST.good(~V, ST.LS{cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, sl, fl}) == True{} : Bool}, bo: BU.BumpOK(mT, 22n, LR.bump(3, AR.thaw(U32, mT)))) -> CntM(~V, cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, sl, fl, SP.L{cap, TB.nth0(AR.slots(U32, mT), 3n), ST.w64(AR.slots(U32, mT), 4n), ST.es(~V, AR.slots(U32, lkT), AR.slots(String, ksT), AR.slots(Maybe<&2, V>, eT), sl), SP.c_hit(ST.ctr(AR.slots(U32, mT)))}, LR.fbump(&2, V, 3, ST.real(~V, ST.LS{cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, sl, fl}))):
  match bo:
    case Tuple{+m2, Tuple{+ea, Tuple{+pm2, Tuple{+ew, Tuple{+x, Tuple{+y, e}}}}}}:
      +ee = {e : {AR.slots(U32, m2) == SC.update(U32, SC.update(U32, AR.slots(U32, mT), 22n, x), 1n+22n, y) : List<&2, U32>}}
      +er = Equal.cong(Array<U32>, LR.LRU<&2, V>, z => LR.F{cap, n, head, tail, free, z, AR.thaw(U32, tabT), AR.thaw(String, ksT), AR.thaw(Maybe<&2, V>, eT), AR.thaw(U32, lkT)}, LR.bump(3, AR.thaw(U32, mT)), AR.thaw(U32, m2), ea)
      +g = bm_fin(~V, cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, sl, fl, hg, 22n, {==}, m2, pm2, x, y, ee)
      +e3 = keep(AR.slots(U32, mT), m2, 22n, x, y, ee, 3n, {==}, {==})
      +e4 = BA.w64_eq(AR.slots(U32, m2), AR.slots(U32, mT), 4n, keep(AR.slots(U32, mT), m2, 22n, x, y, ee, 4n, {==}, {==}), keep(AR.slots(U32, mT), m2, 22n, x, y, ee, 5n, {==}, {==}))
      +ec = BA.ct5(ST.w64(AR.slots(U32, m2), 16n), ST.w64(AR.slots(U32, m2), 18n), ST.w64(AR.slots(U32, m2), 20n), ST.w64(AR.slots(U32, m2), 22n), ST.w64(AR.slots(U32, m2), 24n), ST.w64(AR.slots(U32, mT), 16n), ST.w64(AR.slots(U32, mT), 18n), ST.w64(AR.slots(U32, mT), 20n), SP.inc64(ST.w64(AR.slots(U32, mT), 22n)), ST.w64(AR.slots(U32, mT), 24n), BA.w64_eq(AR.slots(U32, m2), AR.slots(U32, mT), 16n, keep(AR.slots(U32, mT), m2, 22n, x, y, ee, 16n, {==}, {==}), keep(AR.slots(U32, mT), m2, 22n, x, y, ee, 17n, {==}, {==})), BA.w64_eq(AR.slots(U32, m2), AR.slots(U32, mT), 18n, keep(AR.slots(U32, mT), m2, 22n, x, y, ee, 18n, {==}, {==}), keep(AR.slots(U32, mT), m2, 22n, x, y, ee, 19n, {==}, {==})), BA.w64_eq(AR.slots(U32, m2), AR.slots(U32, mT), 20n, keep(AR.slots(U32, mT), m2, 22n, x, y, ee, 20n, {==}, {==}), keep(AR.slots(U32, mT), m2, 22n, x, y, ee, 21n, {==}, {==})), ew, BA.w64_eq(AR.slots(U32, m2), AR.slots(U32, mT), 24n, keep(AR.slots(U32, mT), m2, 22n, x, y, ee, 24n, {==}, {==}), keep(AR.slots(U32, mT), m2, 22n, x, y, ee, 25n, {==}, {==})))
      (m2, (er, (BA.lru_eq(~V, cap, TB.nth0(AR.slots(U32, m2), 3n), TB.nth0(AR.slots(U32, mT), 3n), ST.w64(AR.slots(U32, m2), 4n), ST.w64(AR.slots(U32, mT), 4n), ST.es(~V, AR.slots(U32, lkT), AR.slots(String, ksT), AR.slots(Maybe<&2, V>, eT), sl), ST.es(~V, AR.slots(U32, lkT), AR.slots(String, ksT), AR.slots(Maybe<&2, V>, eT), sl), ST.ctr(AR.slots(U32, m2)), SP.c_hit(ST.ctr(AR.slots(U32, mT))), e3, e4, {==}, ec), g)))

def cg_hit(~V: Data, l: SP.Lru<V>) -> SP.Lru<V>:
  match l:
    case SP.L{cap, on, life, es, c}:
      SP.L{cap, on, life, es, SP.c_hit(c)}

# THEOREM: fbump(3) counts on any shadow
def countg_hit(~V: Data, +sh: ST.Sh<V>, +hg: {ST.good(~V, sh) == True{} : Bool}) -> CountOK(~V, cg_hit(~V, ST.model(~V, sh)), LR.fbump(&2, V, 3, ST.real(~V, sh))):
  match sh:
    case ST.LS{cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, sl, fl}:
      count_hit(~V, cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, sl, fl, hg, BU.bump_ok(mT, ST.g_cpm(~V, cap, n, head, tail, free, TB.nth0(AR.slots(U32, mT), 0n), TB.nth0(AR.slots(U32, mT), 1n), TB.nth0(AR.slots(U32, mT), 2n), TB.nth0(AR.slots(U32, mT), 6n), TB.nth0(AR.slots(U32, mT), 7n), AR.perfect(U32, 5n, mT), k, sd, tabT, AR.slots(String, ksT), AR.perfect(String, sd, ksT), eT, lkT, sl, fl, hg), 3, 22n, {==}, {==}, {==}))

def cntm_miss(~V: Data, +cap: U32, +n: U32, +head: U32, +tail: U32, +free: U32, +mT: AR.Tree<U32>, +k: Nat, +sd: Nat, +tabT: AR.Tree<U32>, +ksT: AR.Tree<String>, +eT: AR.Tree<Maybe<&2, V>>, +lkT: AR.Tree<U32>, +sl: List<&2, Nat>, +fl: List<&2, Nat>, +hg: {ST.good(~V, ST.LS{cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, sl, fl}) == True{} : Bool}, bo: BU.BumpOK(mT, 24n, LR.bump(4, AR.thaw(U32, mT)))) -> CntM(~V, cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, sl, fl, SP.L{cap, TB.nth0(AR.slots(U32, mT), 3n), ST.w64(AR.slots(U32, mT), 4n), ST.es(~V, AR.slots(U32, lkT), AR.slots(String, ksT), AR.slots(Maybe<&2, V>, eT), sl), SP.c_miss(ST.ctr(AR.slots(U32, mT)))}, LR.fbump(&2, V, 4, ST.real(~V, ST.LS{cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, sl, fl}))):
  match bo:
    case Tuple{+m2, Tuple{+ea, Tuple{+pm2, Tuple{+ew, Tuple{+x, Tuple{+y, e}}}}}}:
      +ee = {e : {AR.slots(U32, m2) == SC.update(U32, SC.update(U32, AR.slots(U32, mT), 24n, x), 1n+24n, y) : List<&2, U32>}}
      +er = Equal.cong(Array<U32>, LR.LRU<&2, V>, z => LR.F{cap, n, head, tail, free, z, AR.thaw(U32, tabT), AR.thaw(String, ksT), AR.thaw(Maybe<&2, V>, eT), AR.thaw(U32, lkT)}, LR.bump(4, AR.thaw(U32, mT)), AR.thaw(U32, m2), ea)
      +g = bm_fin(~V, cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, sl, fl, hg, 24n, {==}, m2, pm2, x, y, ee)
      +e3 = keep(AR.slots(U32, mT), m2, 24n, x, y, ee, 3n, {==}, {==})
      +e4 = BA.w64_eq(AR.slots(U32, m2), AR.slots(U32, mT), 4n, keep(AR.slots(U32, mT), m2, 24n, x, y, ee, 4n, {==}, {==}), keep(AR.slots(U32, mT), m2, 24n, x, y, ee, 5n, {==}, {==}))
      +ec = BA.ct5(ST.w64(AR.slots(U32, m2), 16n), ST.w64(AR.slots(U32, m2), 18n), ST.w64(AR.slots(U32, m2), 20n), ST.w64(AR.slots(U32, m2), 22n), ST.w64(AR.slots(U32, m2), 24n), ST.w64(AR.slots(U32, mT), 16n), ST.w64(AR.slots(U32, mT), 18n), ST.w64(AR.slots(U32, mT), 20n), ST.w64(AR.slots(U32, mT), 22n), SP.inc64(ST.w64(AR.slots(U32, mT), 24n)), BA.w64_eq(AR.slots(U32, m2), AR.slots(U32, mT), 16n, keep(AR.slots(U32, mT), m2, 24n, x, y, ee, 16n, {==}, {==}), keep(AR.slots(U32, mT), m2, 24n, x, y, ee, 17n, {==}, {==})), BA.w64_eq(AR.slots(U32, m2), AR.slots(U32, mT), 18n, keep(AR.slots(U32, mT), m2, 24n, x, y, ee, 18n, {==}, {==}), keep(AR.slots(U32, mT), m2, 24n, x, y, ee, 19n, {==}, {==})), BA.w64_eq(AR.slots(U32, m2), AR.slots(U32, mT), 20n, keep(AR.slots(U32, mT), m2, 24n, x, y, ee, 20n, {==}, {==}), keep(AR.slots(U32, mT), m2, 24n, x, y, ee, 21n, {==}, {==})), BA.w64_eq(AR.slots(U32, m2), AR.slots(U32, mT), 22n, keep(AR.slots(U32, mT), m2, 24n, x, y, ee, 22n, {==}, {==}), keep(AR.slots(U32, mT), m2, 24n, x, y, ee, 23n, {==}, {==})), ew)
      (m2, (er, (BA.lru_eq(~V, cap, TB.nth0(AR.slots(U32, m2), 3n), TB.nth0(AR.slots(U32, mT), 3n), ST.w64(AR.slots(U32, m2), 4n), ST.w64(AR.slots(U32, mT), 4n), ST.es(~V, AR.slots(U32, lkT), AR.slots(String, ksT), AR.slots(Maybe<&2, V>, eT), sl), ST.es(~V, AR.slots(U32, lkT), AR.slots(String, ksT), AR.slots(Maybe<&2, V>, eT), sl), ST.ctr(AR.slots(U32, m2)), SP.c_miss(ST.ctr(AR.slots(U32, mT))), e3, e4, {==}, ec), g)))

def cg_miss(~V: Data, l: SP.Lru<V>) -> SP.Lru<V>:
  match l:
    case SP.L{cap, on, life, es, c}:
      SP.L{cap, on, life, es, SP.c_miss(c)}

# THEOREM: fbump(4) counts on any shadow
def countg_miss(~V: Data, +sh: ST.Sh<V>, +hg: {ST.good(~V, sh) == True{} : Bool}) -> CountOK(~V, cg_miss(~V, ST.model(~V, sh)), LR.fbump(&2, V, 4, ST.real(~V, sh))):
  match sh:
    case ST.LS{cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, sl, fl}:
      count_miss(~V, cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, sl, fl, hg, BU.bump_ok(mT, ST.g_cpm(~V, cap, n, head, tail, free, TB.nth0(AR.slots(U32, mT), 0n), TB.nth0(AR.slots(U32, mT), 1n), TB.nth0(AR.slots(U32, mT), 2n), TB.nth0(AR.slots(U32, mT), 6n), TB.nth0(AR.slots(U32, mT), 7n), AR.perfect(U32, 5n, mT), k, sd, tabT, AR.slots(String, ksT), AR.perfect(String, sd, ksT), eT, lkT, sl, fl, hg), 4, 24n, {==}, {==}, {==}))
