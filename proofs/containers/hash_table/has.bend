import Base
import ../../lib/logic.bend as L
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
import ./probe_impl.bend as PI
import ./probe_all.bend as PA
import ./state.bend as ST
import ./lookup.bend as LK
import ./get.bend as G

# has: the implementation's has is the specification's has.

def some_true(~V: Data, +mv: Maybe<&2, V>, +h: {ST.some_b(~V, mv) == True{} : Bool}) -> {S.is_some(~V, mv) == True{} : Bool}:
  match mv:
    case None{}:
      Empty.absurd({S.is_some(~V, None{}) == True{} : Bool}, L.false_true(h))
    case Some{v}:
      {==}

def has_hit2(~V: Data, +n: U32, +k: Nat, +td: U32, +fresh: U32, +sz: U32, +sd: Nat, +sdU: U32, +free: U32, +tabT: AR.Tree<U32>, +kl: List<&2, String>, +pk: Bool, +vsT: AR.Tree<Maybe<&2, V>>, +nxT: AR.Tree<U32>, +hg: {ST.goodF(~V, n, k, td, fresh, sz, sd, sdU, free, tabT, kl, pk, vsT, nxT) == True{} : Bool}, +key: String, +K2: AR.Tree<String>, +sk: String, +w: U32, +i: Nat, +l: U32, +hi: {Nat.is_lt(i, SC.pow2(k)) == True{} : Bool}, +hk: {B.hold(key, B.at(TB.buckets(AR.slots(U32, tabT), kl, SC.pow2(k)), i)) == True{} : Bool}, +hl: {B.lnk(B.at(TB.buckets(AR.slots(U32, tabT), kl, SC.pow2(k)), i)) == l : U32}, bf: {Bool.not(U32.is_eq(B.lnk(B.at(TB.buckets(AR.slots(U32, tabT), kl, SC.pow2(k)), i)), 0)) == True{} : Bool} & ({Nat.is_lt(UD.v(H.slot(B.lnk(B.at(TB.buckets(AR.slots(U32, tabT), kl, SC.pow2(k)), i)))), SC.pow2(sd)) == True{} : Bool} & {B.nthb(ST.lvs(~V, AR.slots(Maybe<&2, V>, vsT)), UD.v(H.slot(B.lnk(B.at(TB.buckets(AR.slots(U32, tabT), kl, SC.pow2(k)), i))))) == True{} : Bool})) -> {H.has_f(&2, V, n, CY.msk(k), td, fresh, sz, sdU, free, AR.thaw(Maybe<&2, V>, vsT), AR.thaw(U32, nxT), (PI.fd_of(B.RHit{i, l}, AR.thaw(U32, tabT), AR.thaw(String, K2), sk), w)) == (H.HM{n, CY.msk(k), td, fresh, sz, sdU, free, AR.thaw(U32, tabT), AR.thaw(String, K2), AR.thaw(Maybe<&2, V>, vsT), AR.thaw(U32, nxT)}, S.has(~V, ST.absm(~V, TB.buckets(AR.slots(U32, tabT), kl, SC.pow2(k)), AR.slots(Maybe<&2, V>, vsT), SC.pow2(k), 0n), key)) : H.HashMap<&2, V> & Bool}:
  match bf:
    case Tuple{nz, Tuple{hr0, hlv0}}:
      +nz2 = L.subst(U32, zz => {Bool.not(U32.is_eq(zz, 0)) == True{} : Bool}, B.lnk(B.at(TB.buckets(AR.slots(U32, tabT), kl, SC.pow2(k)), i)), l, hl, nz)
      +hlk = LK.lookup_hit(~V, TB.buckets(AR.slots(U32, tabT), kl, SC.pow2(k)), AR.slots(Maybe<&2, V>, vsT), key, SC.pow2(k), ST.g_cuniq(~V, n, k, td, fresh, sz, sd, sdU, free, tabT, kl, pk, vsT, nxT, hg), i, hi, hk)
      +hs = Equal.trans(Bool, ST.some_b(~V, ST.nthm(~V, AR.slots(Maybe<&2, V>, vsT), UD.v(H.slot(B.lnk(B.at(TB.buckets(AR.slots(U32, tabT), kl, SC.pow2(k)), i)))))), B.nthb(ST.lvs(~V, AR.slots(Maybe<&2, V>, vsT)), UD.v(H.slot(B.lnk(B.at(TB.buckets(AR.slots(U32, tabT), kl, SC.pow2(k)), i))))), True{}, Equal.sym(Bool, B.nthb(ST.lvs(~V, AR.slots(Maybe<&2, V>, vsT)), UD.v(H.slot(B.lnk(B.at(TB.buckets(AR.slots(U32, tabT), kl, SC.pow2(k)), i))))), ST.some_b(~V, ST.nthm(~V, AR.slots(Maybe<&2, V>, vsT), UD.v(H.slot(B.lnk(B.at(TB.buckets(AR.slots(U32, tabT), kl, SC.pow2(k)), i)))))), ST.lvs_nth(~V, AR.slots(Maybe<&2, V>, vsT), UD.v(H.slot(B.lnk(B.at(TB.buckets(AR.slots(U32, tabT), kl, SC.pow2(k)), i)))))), hlv0)
      +hspec = Equal.trans(Bool, S.has(~V, ST.absm(~V, TB.buckets(AR.slots(U32, tabT), kl, SC.pow2(k)), AR.slots(Maybe<&2, V>, vsT), SC.pow2(k), 0n), key), S.is_some(~V, ST.nthm(~V, AR.slots(Maybe<&2, V>, vsT), UD.v(H.slot(B.lnk(B.at(TB.buckets(AR.slots(U32, tabT), kl, SC.pow2(k)), i)))))), True{}, Equal.cong(Maybe<&2, V>, Bool, z => S.is_some(~V, z), S.lookup(~V, ST.absm(~V, TB.buckets(AR.slots(U32, tabT), kl, SC.pow2(k)), AR.slots(Maybe<&2, V>, vsT), SC.pow2(k), 0n), key), ST.nthm(~V, AR.slots(Maybe<&2, V>, vsT), UD.v(H.slot(B.lnk(B.at(TB.buckets(AR.slots(U32, tabT), kl, SC.pow2(k)), i))))), hlk), some_true(~V, ST.nthm(~V, AR.slots(Maybe<&2, V>, vsT), UD.v(H.slot(B.lnk(B.at(TB.buckets(AR.slots(U32, tabT), kl, SC.pow2(k)), i))))), hs))
      Equal.cong(Bool, H.HashMap<&2, V> & Bool, z => (H.HM{n, CY.msk(k), td, fresh, sz, sdU, free, AR.thaw(U32, tabT), AR.thaw(String, K2), AR.thaw(Maybe<&2, V>, vsT), AR.thaw(U32, nxT)}, z), U32.is_ne(l, 0), S.has(~V, ST.absm(~V, TB.buckets(AR.slots(U32, tabT), kl, SC.pow2(k)), AR.slots(Maybe<&2, V>, vsT), SC.pow2(k), 0n), key), Equal.trans(Bool, U32.is_ne(l, 0), True{}, S.has(~V, ST.absm(~V, TB.buckets(AR.slots(U32, tabT), kl, SC.pow2(k)), AR.slots(Maybe<&2, V>, vsT), SC.pow2(k), 0n), key), nz2, Equal.sym(Bool, S.has(~V, ST.absm(~V, TB.buckets(AR.slots(U32, tabT), kl, SC.pow2(k)), AR.slots(Maybe<&2, V>, vsT), SC.pow2(k), 0n), key), True{}, hspec)))

def has_r(~V: Data, +n: U32, +k: Nat, +td: U32, +fresh: U32, +sz: U32, +sd: Nat, +sdU: U32, +free: U32, +tabT: AR.Tree<U32>, +kl: List<&2, String>, +pk: Bool, +vsT: AR.Tree<Maybe<&2, V>>, +nxT: AR.Tree<U32>, +hg: {ST.goodF(~V, n, k, td, fresh, sz, sd, sdU, free, tabT, kl, pk, vsT, nxT) == True{} : Bool}, +key: String, +K2: AR.Tree<String>, +sk: String, +w: U32, +h: Nat, +r: B.Res, hres: B.ResOK(TB.buckets(AR.slots(U32, tabT), kl, SC.pow2(k)), SC.pow2(k), h, key, r)) -> {H.has_f(&2, V, n, CY.msk(k), td, fresh, sz, sdU, free, AR.thaw(Maybe<&2, V>, vsT), AR.thaw(U32, nxT), (PI.fd_of(r, AR.thaw(U32, tabT), AR.thaw(String, K2), sk), w)) == (H.HM{n, CY.msk(k), td, fresh, sz, sdU, free, AR.thaw(U32, tabT), AR.thaw(String, K2), AR.thaw(Maybe<&2, V>, vsT), AR.thaw(U32, nxT)}, S.has(~V, ST.absm(~V, TB.buckets(AR.slots(U32, tabT), kl, SC.pow2(k)), AR.slots(Maybe<&2, V>, vsT), SC.pow2(k), 0n), key)) : H.HashMap<&2, V> & Bool}:
  match r:
    case B.RHit{+i, +l}:
      (+hi, rest) = hres
      (+hk, hl) = rest
      has_hit2(~V, n, k, td, fresh, sz, sd, sdU, free, tabT, kl, pk, vsT, nxT, hg, key, K2, sk, w, i, l, hi, hk, hl, G.bf_ok(sd, ST.lvs(~V, AR.slots(Maybe<&2, V>, vsT)), UD.v(fresh), key, B.at(TB.buckets(AR.slots(U32, tabT), kl, SC.pow2(k)), i), B.all_inst(B.PWell{TB.buckets(AR.slots(U32, tabT), kl, SC.pow2(k)), sd}, SC.pow2(k), ST.g_cwell(~V, n, k, td, fresh, sz, sd, sdU, free, tabT, kl, pk, vsT, nxT, hg), i, hi), B.all_inst(B.PLive{TB.buckets(AR.slots(U32, tabT), kl, SC.pow2(k)), ST.lvs(~V, AR.slots(Maybe<&2, V>, vsT)), UD.v(fresh)}, SC.pow2(k), ST.g_clive(~V, n, k, td, fresh, sz, sd, sdU, free, tabT, kl, pk, vsT, nxT, hg), i, hi), hk))
    case B.REnd{+e}:
      (he, rest) = hres
      (hz, rest2) = rest
      (hp, hno) = rest2
      Equal.cong(Maybe<&2, V>, H.HashMap<&2, V> & Bool, z => (H.HM{n, CY.msk(k), td, fresh, sz, sdU, free, AR.thaw(U32, tabT), AR.thaw(String, K2), AR.thaw(Maybe<&2, V>, vsT), AR.thaw(U32, nxT)}, S.is_some(~V, z)), None{}, S.lookup(~V, ST.absm(~V, TB.buckets(AR.slots(U32, tabT), kl, SC.pow2(k)), AR.slots(Maybe<&2, V>, vsT), SC.pow2(k), 0n), key), Equal.sym(Maybe<&2, V>, S.lookup(~V, ST.absm(~V, TB.buckets(AR.slots(U32, tabT), kl, SC.pow2(k)), AR.slots(Maybe<&2, V>, vsT), SC.pow2(k), 0n), key), None{}, LK.lookup_none(~V, TB.buckets(AR.slots(U32, tabT), kl, SC.pow2(k)), AR.slots(Maybe<&2, V>, vsT), key, SC.pow2(k), hno)))

# ---- the operation ----

def HasOK(~V: Data, +sh: ST.Sh<V>, +key: String, r: H.HashMap<&2, V> & Bool) -> Type:
  Sigma<&1, &1, ST.Sh<V>, sh2 => {r == (ST.real(~V, sh2), S.has(~V, ST.model(~V, sh), key)) : H.HashMap<&2, V> & Bool} & ({ST.good(~V, sh2) == True{} : Bool} & {ST.model(~V, sh2) == ST.model(~V, sh) : List<&2, S.Entry<V>>})>

def has_po(~V: Data, +n: U32, +k: Nat, +td: U32, +fresh: U32, +sz: U32, +sd: Nat, +sdU: U32, +free: U32, +tabT: AR.Tree<U32>, +ksT: AR.Tree<String>, +vsT: AR.Tree<Maybe<&2, V>>, +nxT: AR.Tree<U32>, +hg: {ST.good(~V, ST.HS{n, k, td, fresh, sz, sd, sdU, free, tabT, ksT, vsT, nxT}) == True{} : Bool}, +key: String, +r: B.Res, hres: B.ResOK(TB.buckets(AR.slots(U32, tabT), AR.slots(String, ksT), SC.pow2(k)), SC.pow2(k), UD.v(HS.bucket(K.kword(key), CY.msk(k))), key, r), po: PA.ProbeOK(tabT, sd, AR.slots(String, ksT), PA.stored(key), K.kword(key), r, H.probe(AR.thaw(U32, tabT), AR.thaw(String, ksT), CY.msk(k), key))) -> HasOK(~V, ST.HS{n, k, td, fresh, sz, sd, sdU, free, tabT, ksT, vsT, nxT}, key, H.has(&2, V, ST.real(~V, ST.HS{n, k, td, fresh, sz, sd, sdU, free, tabT, ksT, vsT, nxT}), key)):
  match po:
    case Tuple{+K2, Tuple{+e, rest}}:
      (+hsl2, pk2) = rest
      +kl = AR.slots(String, ksT)
      +pkT = ST.g_cpk(~V, n, k, td, fresh, sz, sd, sdU, free, tabT, kl, AR.perfect(String, sd, ksT), vsT, nxT, hg)
      +hgT = L.subst(Bool, b => {ST.goodF(~V, n, k, td, fresh, sz, sd, sdU, free, tabT, kl, b, vsT, nxT) == True{} : Bool}, AR.perfect(String, sd, ksT), True{}, pkT, hg)
      +g2 = L.subst(List<&2, String>, z => {ST.goodF(~V, n, k, td, fresh, sz, sd, sdU, free, tabT, z, AR.perfect(String, sd, K2), vsT, nxT) == True{} : Bool}, kl, AR.slots(String, K2), Equal.sym(List<&2, String>, AR.slots(String, K2), kl, hsl2), L.subst(Bool, b => {ST.goodF(~V, n, k, td, fresh, sz, sd, sdU, free, tabT, kl, b, vsT, nxT) == True{} : Bool}, True{}, AR.perfect(String, sd, K2), Equal.sym(Bool, AR.perfect(String, sd, K2), True{}, pk2), hgT))
      +m2 = Equal.cong(List<&2, String>, List<&2, S.Entry<V>>, z => ST.absm(~V, TB.buckets(AR.slots(U32, tabT), z, SC.pow2(k)), AR.slots(Maybe<&2, V>, vsT), SC.pow2(k), 0n), AR.slots(String, K2), kl, hsl2)
      +eq = Equal.trans(H.HashMap<&2, V> & Bool, H.has_f(&2, V, n, CY.msk(k), td, fresh, sz, sdU, free, AR.thaw(Maybe<&2, V>, vsT), AR.thaw(U32, nxT), H.probe(AR.thaw(U32, tabT), AR.thaw(String, ksT), CY.msk(k), key)), H.has_f(&2, V, n, CY.msk(k), td, fresh, sz, sdU, free, AR.thaw(Maybe<&2, V>, vsT), AR.thaw(U32, nxT), (PI.fd_of(r, AR.thaw(U32, tabT), AR.thaw(String, K2), PA.stored(key)), K.kword(key))), (ST.real(~V, ST.HS{n, k, td, fresh, sz, sd, sdU, free, tabT, K2, vsT, nxT}), S.has(~V, ST.model(~V, ST.HS{n, k, td, fresh, sz, sd, sdU, free, tabT, ksT, vsT, nxT}), key)),
        Equal.cong(H.Found & U32, H.HashMap<&2, V> & Bool, pr => H.has_f(&2, V, n, CY.msk(k), td, fresh, sz, sdU, free, AR.thaw(Maybe<&2, V>, vsT), AR.thaw(U32, nxT), pr), H.probe(AR.thaw(U32, tabT), AR.thaw(String, ksT), CY.msk(k), key), (PI.fd_of(r, AR.thaw(U32, tabT), AR.thaw(String, K2), PA.stored(key)), K.kword(key)), e),
        has_r(~V, n, k, td, fresh, sz, sd, sdU, free, tabT, kl, AR.perfect(String, sd, ksT), vsT, nxT, hg, key, K2, PA.stored(key), K.kword(key), UD.v(HS.bucket(K.kword(key), CY.msk(k))), r, hres))
      (ST.HS{n, k, td, fresh, sz, sd, sdU, free, tabT, K2, vsT, nxT}, (eq, (g2, m2)))

# THEOREM: has is the specification's has; the map and its model are kept.
def has_ok(~V: Data, +sh: ST.Sh<V>, +hg: {ST.good(~V, sh) == True{} : Bool}, +key: String) -> HasOK(~V, sh, key, H.has(&2, V, ST.real(~V, sh), key)):
  match sh:
    case ST.HS{+n, +k, +td, +fresh, +sz, +sd, +sdU, +free, +tabT, +ksT, +vsT, +nxT}:
      +kl = AR.slots(String, ksT)
      +pk = AR.perfect(String, sd, ksT)
      +ck = ST.g_ck(~V, n, k, td, fresh, sz, sd, sdU, free, tabT, kl, pk, vsT, nxT, hg)
      +hk31 = L.and_left(Nat.is_lt(k, 31n), Nat.is_lt(0n, k), ck)
      +r = B.pf(key, TB.buckets(AR.slots(U32, tabT), AR.slots(String, ksT), SC.pow2(k)), SC.pow2(k), SC.pow2(k), B.mstep(key, B.at(TB.buckets(AR.slots(U32, tabT), AR.slots(String, ksT), SC.pow2(k)), UD.v(HS.bucket(K.kword(key), CY.msk(k))))), UD.v(HS.bucket(K.kword(key), CY.msk(k))))
      has_po(~V, n, k, td, fresh, sz, sd, sdU, free, tabT, ksT, vsT, nxT, hg, key, r, G.res_of(~V, n, k, td, fresh, sz, sd, sdU, free, tabT, kl, pk, vsT, nxT, hg, key), PA.probe_ok(1n, {==}, k, hk31, tabT, ST.g_cpt(~V, n, k, td, fresh, sz, sd, sdU, free, tabT, kl, pk, vsT, nxT, hg), sd, ST.g_csd(~V, n, k, td, fresh, sz, sd, sdU, free, tabT, kl, pk, vsT, nxT, hg), kl, ksT, {==}, ST.g_cpk(~V, n, k, td, fresh, sz, sd, sdU, free, tabT, kl, pk, vsT, nxT, hg), ST.g_cwell(~V, n, k, td, fresh, sz, sd, sdU, free, tabT, kl, pk, vsT, nxT, hg), key))
