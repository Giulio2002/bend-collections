import Base
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../../lib/array.bend as AR
import ../../lib/spec_common.bend as SC
import ./spec.bend as S
import ../../lib/u32div.bend as UD
import ../../../src/math/hash.bend as HS
import ../../../src/containers/hash_table.bend as H
import ./keys.bend as K
import ./table.bend as TB
import ./buckets.bend as B
import ./cyc.bend as CY
import ./inv.bend as IV
import ./probe_impl.bend as PI
import ./probe_all.bend as PA
import ./state.bend as ST
import ./lookup.bend as LK

# get: the implementation's get is the specification's get.

# at most half full: fewer entries than buckets
def load_lt_c(+a: Nat, +m: Nat, +hm: {Nat.is_lt(0n, m) == True{} : Bool}, +h: {Nat.is_le(Nat.double(a), m) == True{} : Bool}, +c: Bool, +hc: {Nat.is_lt(a, m) == c : Bool}) -> {Nat.is_lt(a, m) == True{} : Bool}:
  match c:
    case True{}:
      hc
    case False{}:
      +h1 = N.double_le(m, a, N.not_lt_le(a, m, hc))
      +h2 = N.le_trans(Nat.double(m), Nat.double(a), m, h1, h)
      +h3 = L.subst(Nat, z => {Nat.is_le(z, m) == True{} : Bool}, Nat.double(m), Nat.add(m, m), NA.double_self(m), h2)
      Empty.absurd({Nat.is_lt(a, m) == True{} : Bool}, L.true_false(Equal.trans(Bool, True{}, Nat.is_le(Nat.add(m, m), m), False{}, Equal.sym(Bool, Nat.is_le(Nat.add(m, m), m), True{}, h3), N.lt_not_le(m, Nat.add(m, m), L.subst(Nat, z => {Nat.is_lt(z, Nat.add(m, m)) == True{} : Bool}, Nat.add(0n, m), m, {==}, N.lt_add_r2(0n, m, m, hm))))))

def load_lt(+a: Nat, +m: Nat, +hm: {Nat.is_lt(0n, m) == True{} : Bool}, +h: {Nat.is_le(Nat.double(a), m) == True{} : Bool}) -> {Nat.is_lt(a, m) == True{} : Bool}:
  load_lt_c(a, m, hm, h, Nat.is_lt(a, m), {==})

def res_e0(+bs: List<&2, B.Bk>, +n: Nat, +hn: {Nat.is_lt(0n, n) == True{} : Bool}, +mask: U32, +key: String, +h: Nat, +hh: {Nat.is_lt(h, n) == True{} : Bool}, +cl: {B.cluster(bs, n, mask) == True{} : Bool}, +ho: {B.all_lt(B.PHome{bs, mask, key, h}, n) == True{} : Bool}, e: IV.Empty0(bs, n)) -> B.ResOK(bs, n, h, key, B.pf(key, bs, n, n, B.mstep(key, B.at(bs, h)), h)):
  match e:
    case Tuple{+e0, Tuple{+he0, +hz0}}:
      IV.pf_ok_n(bs, n, hn, mask, key, h, hh, cl, ho, e0, he0, hz0)

# the probe facts for key in a table satisfying the invariant
def res_of(~V: Data, +n: U32, +k: Nat, +td: U32, +fresh: U32, +sz: U32, +sd: Nat, +sdU: U32, +free: U32, +tabT: AR.Tree<U32>, +kl: List<&2, String>, +pk: Bool, +vsT: AR.Tree<Maybe<&2, V>>, +nxT: AR.Tree<U32>, +hg: {ST.goodF(~V, n, k, td, fresh, sz, sd, sdU, free, tabT, kl, pk, vsT, nxT) == True{} : Bool}, +key: String) -> B.ResOK(TB.buckets(AR.slots(U32, tabT), kl, SC.pow2(k)), SC.pow2(k), UD.v(HS.bucket(K.kword(key), CY.msk(k))), key, B.pf(key, TB.buckets(AR.slots(U32, tabT), kl, SC.pow2(k)), SC.pow2(k), SC.pow2(k), B.mstep(key, B.at(TB.buckets(AR.slots(U32, tabT), kl, SC.pow2(k)), UD.v(HS.bucket(K.kword(key), CY.msk(k))))), UD.v(HS.bucket(K.kword(key), CY.msk(k))))):
  +bs = TB.buckets(AR.slots(U32, tabT), kl, SC.pow2(k))
  +nb = SC.pow2(k)
  +hn = N.succ_le_lt(0n, nb, N.pow2_pos(k))
  +cn = N.eq_from_is_eq(UD.v(n), IV.occn(bs, nb), ST.g_cn(~V, n, k, td, fresh, sz, sd, sdU, free, tabT, kl, pk, vsT, nxT, hg))
  +hocc = L.subst(Nat, z => {Nat.is_lt(z, nb) == True{} : Bool}, UD.v(n), IV.occn(bs, nb), cn, load_lt(UD.v(n), nb, hn, ST.g_cload(~V, n, k, td, fresh, sz, sd, sdU, free, tabT, kl, pk, vsT, nxT, hg)))
  res_e0(bs, nb, hn, CY.msk(k), key, UD.v(HS.bucket(K.kword(key), CY.msk(k))), PA.home_lt(K.kword(key), k), ST.g_cclus(~V, n, k, td, fresh, sz, sd, sdU, free, tabT, kl, pk, vsT, nxT, hg), IV.home_all(bs, sd, CY.msk(k), key, nb, ST.g_cwell(~V, n, k, td, fresh, sz, sd, sdU, free, tabT, kl, pk, vsT, nxT, hg), nb, N.le_refl(nb)), IV.find_empty(bs, nb, hocc))

# a full bucket holding key: its link is not 0, its slot is in the arena, and
# the slot holds a value
def bf_ok(+sd: Nat, +lv: List<&2, Bool>, +fr: Nat, +key: String, +b: B.Bk, +hw: {B.wb(sd, b) == True{} : Bool}, +hl: {B.live_b(lv, fr, b) == True{} : Bool}, +hk: {B.hold(key, b) == True{} : Bool}) -> {Bool.not(U32.is_eq(B.lnk(b), 0)) == True{} : Bool} & ({Nat.is_lt(UD.v(H.slot(B.lnk(b))), SC.pow2(sd)) == True{} : Bool} & {B.nthb(lv, UD.v(H.slot(B.lnk(b)))) == True{} : Bool}):
  match b:
    case B.BE{}:
      Empty.absurd({Bool.not(U32.is_eq(B.lnk(B.BE{}), 0)) == True{} : Bool} & ({Nat.is_lt(UD.v(H.slot(B.lnk(B.BE{}))), SC.pow2(sd)) == True{} : Bool} & {B.nthb(lv, UD.v(H.slot(B.lnk(B.BE{})))) == True{} : Bool}), L.false_true(hk))
    case B.BF{+x, +l, +k}:
      +hw2 = L.and_right(Nat.is_lt(UD.v(H.slot(l)), SC.pow2(sd)), Bool.and(U32.is_eq(x, K.kword(k)), Bool.not(U32.is_eq(l, 0))), hw)
      (L.and_right(U32.is_eq(x, K.kword(k)), Bool.not(U32.is_eq(l, 0)), hw2), (L.and_left(Nat.is_lt(UD.v(H.slot(l)), SC.pow2(sd)), Bool.and(U32.is_eq(x, K.kword(k)), Bool.not(U32.is_eq(l, 0))), hw), L.and_left(B.nthb(lv, UD.v(H.slot(l))), Nat.is_lt(UD.v(H.slot(l)), fr), hl)))

def get_end(~V: Data, +n: U32, +k: Nat, +td: U32, +fresh: U32, +sz: U32, +sd: Nat, +sdU: U32, +free: U32, +tabT: AR.Tree<U32>, +kl: List<&2, String>, +pk: Bool, +vsT: AR.Tree<Maybe<&2, V>>, +nxT: AR.Tree<U32>, +hg: {ST.goodF(~V, n, k, td, fresh, sz, sd, sdU, free, tabT, kl, pk, vsT, nxT) == True{} : Bool}, +key: String, +dflt: V, +K2: AR.Tree<String>, +sk: String, +w: U32, +e: Nat, +hno: {B.all_lt(B.PNo{TB.buckets(AR.slots(U32, tabT), kl, SC.pow2(k)), key}, SC.pow2(k)) == True{} : Bool}) -> {H.get_f(V, n, CY.msk(k), td, fresh, sz, sdU, free, AR.thaw(Maybe<&2, V>, vsT), AR.thaw(U32, nxT), dflt, (PI.fd_of(B.REnd{e}, AR.thaw(U32, tabT), AR.thaw(String, K2), sk), w)) == (H.HM{n, CY.msk(k), td, fresh, sz, sdU, free, AR.thaw(U32, tabT), AR.thaw(String, K2), AR.thaw(Maybe<&2, V>, vsT), AR.thaw(U32, nxT)}, S.get(~V, dflt, ST.absm(~V, TB.buckets(AR.slots(U32, tabT), kl, SC.pow2(k)), AR.slots(Maybe<&2, V>, vsT), SC.pow2(k), 0n), key)) : H.HashMap<&2, V> & V}:
  Equal.cong(Maybe<&2, V>, H.HashMap<&2, V> & V, z => (H.HM{n, CY.msk(k), td, fresh, sz, sdU, free, AR.thaw(U32, tabT), AR.thaw(String, K2), AR.thaw(Maybe<&2, V>, vsT), AR.thaw(U32, nxT)}, S.get_m(~V, dflt, z)), None{}, S.lookup(~V, ST.absm(~V, TB.buckets(AR.slots(U32, tabT), kl, SC.pow2(k)), AR.slots(Maybe<&2, V>, vsT), SC.pow2(k), 0n), key), Equal.sym(Maybe<&2, V>, S.lookup(~V, ST.absm(~V, TB.buckets(AR.slots(U32, tabT), kl, SC.pow2(k)), AR.slots(Maybe<&2, V>, vsT), SC.pow2(k), 0n), key), None{}, LK.lookup_none(~V, TB.buckets(AR.slots(U32, tabT), kl, SC.pow2(k)), AR.slots(Maybe<&2, V>, vsT), key, SC.pow2(k), hno)))

def get_val(~V: Data, +n: U32, +k: Nat, +td: U32, +fresh: U32, +sz: U32, +sd: Nat, +sdU: U32, +free: U32, +tabT: AR.Tree<U32>, +kl: List<&2, String>, +pk: Bool, +vsT: AR.Tree<Maybe<&2, V>>, +nxT: AR.Tree<U32>, +key: String, +dflt: V, +K2: AR.Tree<String>, +l: U32, +lhs: Maybe<&2, V>, +mv: Maybe<&2, V>, +hmv: {ST.nthm(~V, AR.slots(Maybe<&2, V>, vsT), UD.v(H.slot(l))) == mv : Maybe<&2, V>}, +hlive: {B.nthb(ST.lvs(~V, AR.slots(Maybe<&2, V>, vsT)), UD.v(H.slot(l))) == True{} : Bool}, +hlk: {S.lookup(~V, ST.absm(~V, TB.buckets(AR.slots(U32, tabT), kl, SC.pow2(k)), AR.slots(Maybe<&2, V>, vsT), SC.pow2(k), 0n), key) == ST.nthm(~V, AR.slots(Maybe<&2, V>, vsT), UD.v(H.slot(l))) : Maybe<&2, V>}) -> {H.get_fin(V, n, CY.msk(k), td, fresh, sz, sdU, free, AR.thaw(U32, tabT), AR.thaw(String, K2), AR.thaw(U32, nxT), H.get_v(V, dflt, (AR.thaw(Maybe<&2, V>, vsT), mv))) == (H.HM{n, CY.msk(k), td, fresh, sz, sdU, free, AR.thaw(U32, tabT), AR.thaw(String, K2), AR.thaw(Maybe<&2, V>, vsT), AR.thaw(U32, nxT)}, S.get(~V, dflt, ST.absm(~V, TB.buckets(AR.slots(U32, tabT), kl, SC.pow2(k)), AR.slots(Maybe<&2, V>, vsT), SC.pow2(k), 0n), key)) : H.HashMap<&2, V> & V}:
  match mv:
    case None{}:
      Empty.absurd({H.get_fin(V, n, CY.msk(k), td, fresh, sz, sdU, free, AR.thaw(U32, tabT), AR.thaw(String, K2), AR.thaw(U32, nxT), H.get_v(V, dflt, (AR.thaw(Maybe<&2, V>, vsT), None{}))) == (H.HM{n, CY.msk(k), td, fresh, sz, sdU, free, AR.thaw(U32, tabT), AR.thaw(String, K2), AR.thaw(Maybe<&2, V>, vsT), AR.thaw(U32, nxT)}, S.get(~V, dflt, ST.absm(~V, TB.buckets(AR.slots(U32, tabT), kl, SC.pow2(k)), AR.slots(Maybe<&2, V>, vsT), SC.pow2(k), 0n), key)) : H.HashMap<&2, V> & V}, L.true_false(Equal.trans(Bool, True{}, B.nthb(ST.lvs(~V, AR.slots(Maybe<&2, V>, vsT)), UD.v(H.slot(l))), False{}, Equal.sym(Bool, B.nthb(ST.lvs(~V, AR.slots(Maybe<&2, V>, vsT)), UD.v(H.slot(l))), True{}, hlive), Equal.trans(Bool, B.nthb(ST.lvs(~V, AR.slots(Maybe<&2, V>, vsT)), UD.v(H.slot(l))), ST.some_b(~V, ST.nthm(~V, AR.slots(Maybe<&2, V>, vsT), UD.v(H.slot(l)))), False{}, ST.lvs_nth(~V, AR.slots(Maybe<&2, V>, vsT), UD.v(H.slot(l))), Equal.cong(Maybe<&2, V>, Bool, z => ST.some_b(~V, z), ST.nthm(~V, AR.slots(Maybe<&2, V>, vsT), UD.v(H.slot(l))), None{}, hmv)))))
    case Some{+v}:
      Equal.cong(Maybe<&2, V>, H.HashMap<&2, V> & V, z => (H.HM{n, CY.msk(k), td, fresh, sz, sdU, free, AR.thaw(U32, tabT), AR.thaw(String, K2), AR.thaw(Maybe<&2, V>, vsT), AR.thaw(U32, nxT)}, S.get_m(~V, dflt, z)), Some{v}, S.lookup(~V, ST.absm(~V, TB.buckets(AR.slots(U32, tabT), kl, SC.pow2(k)), AR.slots(Maybe<&2, V>, vsT), SC.pow2(k), 0n), key), Equal.sym(Maybe<&2, V>, S.lookup(~V, ST.absm(~V, TB.buckets(AR.slots(U32, tabT), kl, SC.pow2(k)), AR.slots(Maybe<&2, V>, vsT), SC.pow2(k), 0n), key), Some{v}, Equal.trans(Maybe<&2, V>, S.lookup(~V, ST.absm(~V, TB.buckets(AR.slots(U32, tabT), kl, SC.pow2(k)), AR.slots(Maybe<&2, V>, vsT), SC.pow2(k), 0n), key), ST.nthm(~V, AR.slots(Maybe<&2, V>, vsT), UD.v(H.slot(l))), Some{v}, hlk, hmv)))

def get_hit3(~V: Data, +n: U32, +k: Nat, +td: U32, +fresh: U32, +sz: U32, +sd: Nat, +sdU: U32, +free: U32, +tabT: AR.Tree<U32>, +kl: List<&2, String>, +pk: Bool, +vsT: AR.Tree<Maybe<&2, V>>, +nxT: AR.Tree<U32>, +key: String, +dflt: V, +K2: AR.Tree<String>, +l: U32, +hsd: {Nat.is_lt(sd, 32n) == True{} : Bool}, +pv: {AR.perfect(Maybe<&2, V>, sd, vsT) == True{} : Bool}, +hr: {Nat.is_lt(UD.v(H.slot(l)), SC.pow2(sd)) == True{} : Bool}, +hlive: {B.nthb(ST.lvs(~V, AR.slots(Maybe<&2, V>, vsT)), UD.v(H.slot(l))) == True{} : Bool}, +hlk: {S.lookup(~V, ST.absm(~V, TB.buckets(AR.slots(U32, tabT), kl, SC.pow2(k)), AR.slots(Maybe<&2, V>, vsT), SC.pow2(k), 0n), key) == ST.nthm(~V, AR.slots(Maybe<&2, V>, vsT), UD.v(H.slot(l))) : Maybe<&2, V>}, +z: Bool, +hz: {U32.is_eq(l, 0) == z : Bool}, +hzf: {z == False{} : Bool}) -> {H.get_hit(V, n, CY.msk(k), td, fresh, sz, sdU, free, AR.thaw(U32, tabT), AR.thaw(String, K2), AR.thaw(Maybe<&2, V>, vsT), AR.thaw(U32, nxT), dflt, l, z) == (H.HM{n, CY.msk(k), td, fresh, sz, sdU, free, AR.thaw(U32, tabT), AR.thaw(String, K2), AR.thaw(Maybe<&2, V>, vsT), AR.thaw(U32, nxT)}, S.get(~V, dflt, ST.absm(~V, TB.buckets(AR.slots(U32, tabT), kl, SC.pow2(k)), AR.slots(Maybe<&2, V>, vsT), SC.pow2(k), 0n), key)) : H.HashMap<&2, V> & V}:
  match z:
    case True{}:
      Empty.absurd({H.get_hit(V, n, CY.msk(k), td, fresh, sz, sdU, free, AR.thaw(U32, tabT), AR.thaw(String, K2), AR.thaw(Maybe<&2, V>, vsT), AR.thaw(U32, nxT), dflt, l, True{}) == (H.HM{n, CY.msk(k), td, fresh, sz, sdU, free, AR.thaw(U32, tabT), AR.thaw(String, K2), AR.thaw(Maybe<&2, V>, vsT), AR.thaw(U32, nxT)}, S.get(~V, dflt, ST.absm(~V, TB.buckets(AR.slots(U32, tabT), kl, SC.pow2(k)), AR.slots(Maybe<&2, V>, vsT), SC.pow2(k), 0n), key)) : H.HashMap<&2, V> & V}, L.true_false(hzf))
    case False{}:
      +mv = ST.nthm(~V, AR.slots(Maybe<&2, V>, vsT), UD.v(H.slot(l)))
      +hlen = L.subst(Nat, zz => {Nat.is_lt(UD.v(H.slot(l)), zz) == True{} : Bool}, SC.pow2(sd), SC.length(Maybe<&2, V>, AR.slots(Maybe<&2, V>, vsT)), Equal.sym(Nat, SC.length(Maybe<&2, V>, AR.slots(Maybe<&2, V>, vsT)), SC.pow2(sd), AR.slots_length(Maybe<&2, V>, sd, vsT, pv)), hr)
      +ga = AR.get(Maybe<&2, V>, sd, vsT, H.slot(l), mv, hsd, hr, ST.nthm_some(~V, AR.slots(Maybe<&2, V>, vsT), UD.v(H.slot(l)), hlen), pv)
      Equal.trans(H.HashMap<&2, V> & V, H.get_fin(V, n, CY.msk(k), td, fresh, sz, sdU, free, AR.thaw(U32, tabT), AR.thaw(String, K2), AR.thaw(U32, nxT), H.get_v(V, dflt, Array.get(Maybe<&2, V>, AR.thaw(Maybe<&2, V>, vsT), H.slot(l)))), H.get_fin(V, n, CY.msk(k), td, fresh, sz, sdU, free, AR.thaw(U32, tabT), AR.thaw(String, K2), AR.thaw(U32, nxT), H.get_v(V, dflt, (AR.thaw(Maybe<&2, V>, vsT), mv))), (H.HM{n, CY.msk(k), td, fresh, sz, sdU, free, AR.thaw(U32, tabT), AR.thaw(String, K2), AR.thaw(Maybe<&2, V>, vsT), AR.thaw(U32, nxT)}, S.get(~V, dflt, ST.absm(~V, TB.buckets(AR.slots(U32, tabT), kl, SC.pow2(k)), AR.slots(Maybe<&2, V>, vsT), SC.pow2(k), 0n), key)),
        Equal.cong(Array<Maybe<&2, V>> & Maybe<&2, V>, H.HashMap<&2, V> & V, rr => H.get_fin(V, n, CY.msk(k), td, fresh, sz, sdU, free, AR.thaw(U32, tabT), AR.thaw(String, K2), AR.thaw(U32, nxT), H.get_v(V, dflt, rr)), Array.get(Maybe<&2, V>, AR.thaw(Maybe<&2, V>, vsT), H.slot(l)), (AR.thaw(Maybe<&2, V>, vsT), mv), ga),
        get_val(~V, n, k, td, fresh, sz, sd, sdU, free, tabT, kl, pk, vsT, nxT, key, dflt, K2, l, mv, mv, {==}, hlive, hlk))

def get_hit2(~V: Data, +n: U32, +k: Nat, +td: U32, +fresh: U32, +sz: U32, +sd: Nat, +sdU: U32, +free: U32, +tabT: AR.Tree<U32>, +kl: List<&2, String>, +pk: Bool, +vsT: AR.Tree<Maybe<&2, V>>, +nxT: AR.Tree<U32>, +hg: {ST.goodF(~V, n, k, td, fresh, sz, sd, sdU, free, tabT, kl, pk, vsT, nxT) == True{} : Bool}, +key: String, +dflt: V, +K2: AR.Tree<String>, +sk: String, +w: U32, +i: Nat, +l: U32, +hi: {Nat.is_lt(i, SC.pow2(k)) == True{} : Bool}, +hk: {B.hold(key, B.at(TB.buckets(AR.slots(U32, tabT), kl, SC.pow2(k)), i)) == True{} : Bool}, +hl: {B.lnk(B.at(TB.buckets(AR.slots(U32, tabT), kl, SC.pow2(k)), i)) == l : U32}, bf: {Bool.not(U32.is_eq(B.lnk(B.at(TB.buckets(AR.slots(U32, tabT), kl, SC.pow2(k)), i)), 0)) == True{} : Bool} & ({Nat.is_lt(UD.v(H.slot(B.lnk(B.at(TB.buckets(AR.slots(U32, tabT), kl, SC.pow2(k)), i)))), SC.pow2(sd)) == True{} : Bool} & {B.nthb(ST.lvs(~V, AR.slots(Maybe<&2, V>, vsT)), UD.v(H.slot(B.lnk(B.at(TB.buckets(AR.slots(U32, tabT), kl, SC.pow2(k)), i))))) == True{} : Bool})) -> {H.get_f(V, n, CY.msk(k), td, fresh, sz, sdU, free, AR.thaw(Maybe<&2, V>, vsT), AR.thaw(U32, nxT), dflt, (PI.fd_of(B.RHit{i, l}, AR.thaw(U32, tabT), AR.thaw(String, K2), sk), w)) == (H.HM{n, CY.msk(k), td, fresh, sz, sdU, free, AR.thaw(U32, tabT), AR.thaw(String, K2), AR.thaw(Maybe<&2, V>, vsT), AR.thaw(U32, nxT)}, S.get(~V, dflt, ST.absm(~V, TB.buckets(AR.slots(U32, tabT), kl, SC.pow2(k)), AR.slots(Maybe<&2, V>, vsT), SC.pow2(k), 0n), key)) : H.HashMap<&2, V> & V}:
  match bf:
    case Tuple{nz, Tuple{hr0, hlv0}}:
      +nz2 = L.subst(U32, zz => {Bool.not(U32.is_eq(zz, 0)) == True{} : Bool}, B.lnk(B.at(TB.buckets(AR.slots(U32, tabT), kl, SC.pow2(k)), i)), l, hl, nz)
      +hr = L.subst(U32, zz => {Nat.is_lt(UD.v(H.slot(zz)), SC.pow2(sd)) == True{} : Bool}, B.lnk(B.at(TB.buckets(AR.slots(U32, tabT), kl, SC.pow2(k)), i)), l, hl, hr0)
      +hlv = L.subst(U32, zz => {B.nthb(ST.lvs(~V, AR.slots(Maybe<&2, V>, vsT)), UD.v(H.slot(zz))) == True{} : Bool}, B.lnk(B.at(TB.buckets(AR.slots(U32, tabT), kl, SC.pow2(k)), i)), l, hl, hlv0)
      +hlk = L.subst(U32, zz => {S.lookup(~V, ST.absm(~V, TB.buckets(AR.slots(U32, tabT), kl, SC.pow2(k)), AR.slots(Maybe<&2, V>, vsT), SC.pow2(k), 0n), key) == ST.nthm(~V, AR.slots(Maybe<&2, V>, vsT), UD.v(H.slot(zz))) : Maybe<&2, V>}, B.lnk(B.at(TB.buckets(AR.slots(U32, tabT), kl, SC.pow2(k)), i)), l, hl, LK.lookup_hit(~V, TB.buckets(AR.slots(U32, tabT), kl, SC.pow2(k)), AR.slots(Maybe<&2, V>, vsT), key, SC.pow2(k), ST.g_cuniq(~V, n, k, td, fresh, sz, sd, sdU, free, tabT, kl, pk, vsT, nxT, hg), i, hi, hk))
      get_hit3(~V, n, k, td, fresh, sz, sd, sdU, free, tabT, kl, pk, vsT, nxT, key, dflt, K2, l, ST.g_csd(~V, n, k, td, fresh, sz, sd, sdU, free, tabT, kl, pk, vsT, nxT, hg), ST.g_cpv(~V, n, k, td, fresh, sz, sd, sdU, free, tabT, kl, pk, vsT, nxT, hg), hr, hlv, hlk, U32.is_eq(l, 0), {==}, K.not_true_eq(U32.is_eq(l, 0), nz2))

def get_r(~V: Data, +n: U32, +k: Nat, +td: U32, +fresh: U32, +sz: U32, +sd: Nat, +sdU: U32, +free: U32, +tabT: AR.Tree<U32>, +kl: List<&2, String>, +pk: Bool, +vsT: AR.Tree<Maybe<&2, V>>, +nxT: AR.Tree<U32>, +hg: {ST.goodF(~V, n, k, td, fresh, sz, sd, sdU, free, tabT, kl, pk, vsT, nxT) == True{} : Bool}, +key: String, +dflt: V, +K2: AR.Tree<String>, +sk: String, +w: U32, +h: Nat, +r: B.Res, hres: B.ResOK(TB.buckets(AR.slots(U32, tabT), kl, SC.pow2(k)), SC.pow2(k), h, key, r)) -> {H.get_f(V, n, CY.msk(k), td, fresh, sz, sdU, free, AR.thaw(Maybe<&2, V>, vsT), AR.thaw(U32, nxT), dflt, (PI.fd_of(r, AR.thaw(U32, tabT), AR.thaw(String, K2), sk), w)) == (H.HM{n, CY.msk(k), td, fresh, sz, sdU, free, AR.thaw(U32, tabT), AR.thaw(String, K2), AR.thaw(Maybe<&2, V>, vsT), AR.thaw(U32, nxT)}, S.get(~V, dflt, ST.absm(~V, TB.buckets(AR.slots(U32, tabT), kl, SC.pow2(k)), AR.slots(Maybe<&2, V>, vsT), SC.pow2(k), 0n), key)) : H.HashMap<&2, V> & V}:
  match r:
    case B.RHit{+i, +l}:
      (+hi, rest) = hres
      (+hk, hl) = rest
      get_hit2(~V, n, k, td, fresh, sz, sd, sdU, free, tabT, kl, pk, vsT, nxT, hg, key, dflt, K2, sk, w, i, l, hi, hk, hl, bf_ok(sd, ST.lvs(~V, AR.slots(Maybe<&2, V>, vsT)), UD.v(fresh), key, B.at(TB.buckets(AR.slots(U32, tabT), kl, SC.pow2(k)), i), B.all_inst(B.PWell{TB.buckets(AR.slots(U32, tabT), kl, SC.pow2(k)), sd}, SC.pow2(k), ST.g_cwell(~V, n, k, td, fresh, sz, sd, sdU, free, tabT, kl, pk, vsT, nxT, hg), i, hi), B.all_inst(B.PLive{TB.buckets(AR.slots(U32, tabT), kl, SC.pow2(k)), ST.lvs(~V, AR.slots(Maybe<&2, V>, vsT)), UD.v(fresh)}, SC.pow2(k), ST.g_clive(~V, n, k, td, fresh, sz, sd, sdU, free, tabT, kl, pk, vsT, nxT, hg), i, hi), hk))
    case B.REnd{+e}:
      (he, rest) = hres
      (hz, rest2) = rest
      (hp, hno) = rest2
      get_end(~V, n, k, td, fresh, sz, sd, sdU, free, tabT, kl, pk, vsT, nxT, hg, key, dflt, K2, sk, w, e, hno)

# ---- the operation ----

def GetOK(~V: Data, +sh: ST.Sh<V>, +dflt: V, +key: String, r: H.HashMap<&2, V> & V) -> Type:
  Sigma<&1, &1, ST.Sh<V>, sh2 => {r == (ST.real(~V, sh2), S.get(~V, dflt, ST.model(~V, sh), key)) : H.HashMap<&2, V> & V} & ({ST.good(~V, sh2) == True{} : Bool} & {ST.model(~V, sh2) == ST.model(~V, sh) : List<&2, S.Entry<V>>})>

def get_po(~V: Data, +n: U32, +k: Nat, +td: U32, +fresh: U32, +sz: U32, +sd: Nat, +sdU: U32, +free: U32, +tabT: AR.Tree<U32>, +ksT: AR.Tree<String>, +vsT: AR.Tree<Maybe<&2, V>>, +nxT: AR.Tree<U32>, +hg: {ST.good(~V, ST.HS{n, k, td, fresh, sz, sd, sdU, free, tabT, ksT, vsT, nxT}) == True{} : Bool}, +dflt: V, +key: String, +r: B.Res, hres: B.ResOK(TB.buckets(AR.slots(U32, tabT), AR.slots(String, ksT), SC.pow2(k)), SC.pow2(k), UD.v(HS.bucket(K.kword(key), CY.msk(k))), key, r), po: PA.ProbeOK(tabT, sd, AR.slots(String, ksT), PA.stored(key), K.kword(key), r, H.probe(AR.thaw(U32, tabT), AR.thaw(String, ksT), CY.msk(k), key))) -> GetOK(~V, ST.HS{n, k, td, fresh, sz, sd, sdU, free, tabT, ksT, vsT, nxT}, dflt, key, H.get(V, dflt, ST.real(~V, ST.HS{n, k, td, fresh, sz, sd, sdU, free, tabT, ksT, vsT, nxT}), key)):
  match po:
    case Tuple{+K2, Tuple{+e, rest}}:
      (+hsl2, pk2) = rest
      +kl = AR.slots(String, ksT)
      +pkT = ST.g_cpk(~V, n, k, td, fresh, sz, sd, sdU, free, tabT, kl, AR.perfect(String, sd, ksT), vsT, nxT, hg)
      +hgT = L.subst(Bool, b => {ST.goodF(~V, n, k, td, fresh, sz, sd, sdU, free, tabT, kl, b, vsT, nxT) == True{} : Bool}, AR.perfect(String, sd, ksT), True{}, pkT, hg)
      +g2 = L.subst(List<&2, String>, z => {ST.goodF(~V, n, k, td, fresh, sz, sd, sdU, free, tabT, z, AR.perfect(String, sd, K2), vsT, nxT) == True{} : Bool}, kl, AR.slots(String, K2), Equal.sym(List<&2, String>, AR.slots(String, K2), kl, hsl2), L.subst(Bool, b => {ST.goodF(~V, n, k, td, fresh, sz, sd, sdU, free, tabT, kl, b, vsT, nxT) == True{} : Bool}, True{}, AR.perfect(String, sd, K2), Equal.sym(Bool, AR.perfect(String, sd, K2), True{}, pk2), hgT))
      +m2 = Equal.cong(List<&2, String>, List<&2, S.Entry<V>>, z => ST.absm(~V, TB.buckets(AR.slots(U32, tabT), z, SC.pow2(k)), AR.slots(Maybe<&2, V>, vsT), SC.pow2(k), 0n), AR.slots(String, K2), kl, hsl2)
      +eq = Equal.trans(H.HashMap<&2, V> & V, H.get_f(V, n, CY.msk(k), td, fresh, sz, sdU, free, AR.thaw(Maybe<&2, V>, vsT), AR.thaw(U32, nxT), dflt, H.probe(AR.thaw(U32, tabT), AR.thaw(String, ksT), CY.msk(k), key)), H.get_f(V, n, CY.msk(k), td, fresh, sz, sdU, free, AR.thaw(Maybe<&2, V>, vsT), AR.thaw(U32, nxT), dflt, (PI.fd_of(r, AR.thaw(U32, tabT), AR.thaw(String, K2), PA.stored(key)), K.kword(key))), (ST.real(~V, ST.HS{n, k, td, fresh, sz, sd, sdU, free, tabT, K2, vsT, nxT}), S.get(~V, dflt, ST.model(~V, ST.HS{n, k, td, fresh, sz, sd, sdU, free, tabT, ksT, vsT, nxT}), key)),
        Equal.cong(H.Found & U32, H.HashMap<&2, V> & V, pr => H.get_f(V, n, CY.msk(k), td, fresh, sz, sdU, free, AR.thaw(Maybe<&2, V>, vsT), AR.thaw(U32, nxT), dflt, pr), H.probe(AR.thaw(U32, tabT), AR.thaw(String, ksT), CY.msk(k), key), (PI.fd_of(r, AR.thaw(U32, tabT), AR.thaw(String, K2), PA.stored(key)), K.kword(key)), e),
        get_r(~V, n, k, td, fresh, sz, sd, sdU, free, tabT, kl, AR.perfect(String, sd, ksT), vsT, nxT, hg, key, dflt, K2, PA.stored(key), K.kword(key), UD.v(HS.bucket(K.kword(key), CY.msk(k))), r, hres))
      (ST.HS{n, k, td, fresh, sz, sd, sdU, free, tabT, K2, vsT, nxT}, (eq, (g2, m2)))

# THEOREM: get is the specification's get; the map and its model are kept.
def get_ok(~V: Data, +sh: ST.Sh<V>, +hg: {ST.good(~V, sh) == True{} : Bool}, +dflt: V, +key: String) -> GetOK(~V, sh, dflt, key, H.get(V, dflt, ST.real(~V, sh), key)):
  match sh:
    case ST.HS{+n, +k, +td, +fresh, +sz, +sd, +sdU, +free, +tabT, +ksT, +vsT, +nxT}:
      +kl = AR.slots(String, ksT)
      +pk = AR.perfect(String, sd, ksT)
      +ck = ST.g_ck(~V, n, k, td, fresh, sz, sd, sdU, free, tabT, kl, pk, vsT, nxT, hg)
      +hk31 = L.and_left(Nat.is_lt(k, 31n), Nat.is_lt(0n, k), ck)
      +r = B.pf(key, TB.buckets(AR.slots(U32, tabT), AR.slots(String, ksT), SC.pow2(k)), SC.pow2(k), SC.pow2(k), B.mstep(key, B.at(TB.buckets(AR.slots(U32, tabT), AR.slots(String, ksT), SC.pow2(k)), UD.v(HS.bucket(K.kword(key), CY.msk(k))))), UD.v(HS.bucket(K.kword(key), CY.msk(k))))
      get_po(~V, n, k, td, fresh, sz, sd, sdU, free, tabT, ksT, vsT, nxT, hg, dflt, key, r, res_of(~V, n, k, td, fresh, sz, sd, sdU, free, tabT, kl, pk, vsT, nxT, hg, key), PA.probe_ok(1n, {==}, k, hk31, tabT, ST.g_cpt(~V, n, k, td, fresh, sz, sd, sdU, free, tabT, kl, pk, vsT, nxT, hg), sd, ST.g_csd(~V, n, k, td, fresh, sz, sd, sdU, free, tabT, kl, pk, vsT, nxT, hg), kl, ksT, {==}, ST.g_cpk(~V, n, k, td, fresh, sz, sd, sdU, free, tabT, kl, pk, vsT, nxT, hg), ST.g_cwell(~V, n, k, td, fresh, sz, sd, sdU, free, tabT, kl, pk, vsT, nxT, hg), key))
