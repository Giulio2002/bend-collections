import Base
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../../lib/u32.bend as U
import ../../lib/array.bend as AR
import ../../../spec/lib/common.bend as SC
import ../../lib/word.bend as WD
import ../../lib/u32div.bend as UD
import ../../math/hash/hash.bend as PH
import ../../../src/math/hash.bend as HS
import ../../../src/containers/hash_table.bend as H
import ./strings.bend as STR
import ./keys.bend as K
import ./table.bend as TB
import ./buckets.bend as B
import ./cyc.bend as CY
import ./probe_impl.bend as PI
import ./qprobe.bend as QP
import ../../lib/words32.bend as W32

# The whole probe (H.probe): every key, long or one-character, starting at
# its home bucket with fuel n.

def zero_mask(+p: Nat) -> {WD.uw(p, WD.mask(p, 0n)) == 0n : Nat}:
  match p:
    case 0n:
      {==}
    case 1n+q:
      Equal.cong(Nat, Nat, Nat.double, WD.uw(q, WD.mask(q, 0n)), 0n, zero_mask(q))

def dbl_step(+u: Nat) -> {Nat.add(1n+Nat.double(u), 1n) == Nat.double(Nat.add(u, 1n)) : Nat}:
  match u:
    case 0n:
      {==}
    case 1n+v:
      Equal.cong(Nat, Nat, z => 2n+z, Nat.add(1n+Nat.double(v), 1n), Nat.double(Nat.add(v, 1n)), dbl_step(v))

# 2^k - 1 + 1 == 2^k for the mask word
def mask_val(+n: Nat, +k: Nat, +hk: {Nat.is_le(k, n) == True{} : Bool}) -> {Nat.add(WD.uw(n, WD.mask(n, k)), 1n) == SC.pow2(k) : Nat}:
  match n k:
    case 0n 0n:
      {==}
    case 0n 1n+j:
      Empty.absurd({Nat.add(WD.uw(0n, WD.mask(0n, 1n+j)), 1n) == SC.pow2(1n+j) : Nat}, L.false_true(hk))
    case 1n+p 0n:
      Equal.cong(Nat, Nat, z => Nat.add(Nat.double(z), 1n), WD.uw(p, WD.mask(p, 0n)), 0n, zero_mask(p))
    case 1n+p 1n+j:
      +u = WD.uw(p, WD.mask(p, j))
      # 1 + 2u + 1 == 2 (u + 1)
      Equal.trans(Nat, Nat.add(1n+Nat.double(u), 1n), Nat.double(Nat.add(u, 1n)), SC.pow2(1n+j), dbl_step(u), Equal.cong(Nat, Nat, Nat.double, Nat.add(u, 1n), SC.pow2(j), mask_val(p, j, hk)))

# the probe's fuel, mask + 1, is the number of buckets
def fuel_eq(+one: Nat, +h1: {one == 1n : Nat}, +k: Nat, +hk31: {Nat.is_lt(k, 31n) == True{} : Bool}) -> {U32.to_nat(U32.inc(CY.msk(k))) == SC.pow2(k) : Nat}:
  +hk = N.lt_le(k, 32n, N.lt_trans(k, 31n, 32n, hk31, {==}))
  +v = UD.v(CY.msk(k))
  +ea = Equal.trans(Nat, Nat.add(v, 1n), Nat.add(WD.uw(32n, WD.mask(32n, k)), 1n), SC.pow2(k), Equal.cong(Nat, Nat, z => Nat.add(z, 1n), v, WD.uw(32n, WD.mask(32n, k)), UD.vw(WD.mask(32n, k))), mask_val(32n, k, hk))
  +e1 = Equal.trans(Nat, 1n+v, Nat.add(v, 1n), SC.pow2(k), Equal.sym(Nat, Nat.add(v, 1n), 1n+v, N.add_comm(v, 1n)), ea)
  +hb = L.subst(Nat, z => {Nat.is_lt(z, WD.sc(32n, one)) == True{} : Bool}, SC.pow2(k), 1n+v, Equal.sym(Nat, 1n+v, SC.pow2(k), e1), N.lt_le_trans(SC.pow2(k), SC.pow2(1n+k), WD.sc(32n, one), N.pow2_lt_succ(k), W32.pow_le32(one, h1, 1n+k, hk31)))
  Equal.trans(Nat, UD.v(U32.inc(CY.msk(k))), 1n+v, SC.pow2(k), W32.inc_val(one, h1, CY.msk(k), hb), e1)

# a home bucket is a bucket
def home_lt(+w: U32, +k: Nat) -> {Nat.is_lt(UD.v(HS.bucket(w, CY.msk(k))), SC.pow2(k)) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_lt(UD.v(HS.bucket(w, CY.msk(k))), z) == True{} : Bool}, WD.sc(k, 1n), SC.pow2(k), Equal.sym(Nat, SC.pow2(k), WD.sc(k, 1n), U.pow2_scale(k)), PH.bucket_lt(w, k, CY.msk(k), {==}))

# ---- the probe's result ----

# the key as the probe hands it back: "" for a short key
def st_c(+c: U32, +t: String, sh: Bool) -> String:
  match sh:
    case True{}:
      SNil{}
    case False{}:
      SCon{Chr{c}, t}

def stored(key: String) -> String:
  match key:
    case SNil{}:
      SNil{}
    case SCon{Chr{+c}, +t}:
      st_c(c, t, K.short_c(c, t))

def ProbeOK(+tabT: AR.Tree<U32>, +sd: Nat, +kl0: List<&2, String>, +skey: String, +w: U32, r: B.Res, v: H.Found & U32) -> Type:
  Sigma<&1, &1, AR.Tree<String>, K2 => {v == (PI.fd_of(r, AR.thaw(U32, tabT), AR.thaw(String, K2), skey), w) : H.Found & U32} & ({AR.slots(String, K2) == kl0 : List<&2, String>} & {AR.perfect(String, sd, K2) == True{} : Bool})>

def po_of_fo(+tabT: AR.Tree<U32>, +sd: Nat, +kl0: List<&2, String>, +key: String, +w: U32, -r: B.Res, -fd: H.Found, fo: PI.FindOK(tabT, sd, kl0, key, r, fd)) -> ProbeOK(tabT, sd, kl0, key, w, r, (fd, w)):
  match fo:
    case Tuple{K2, Tuple{e, rest}}:
      (K2, (Equal.cong(H.Found, H.Found & U32, z => (z, w), fd, PI.fd_of(r, AR.thaw(U32, tabT), AR.thaw(String, K2), key), e), rest))

def probe_long_ok(+one: Nat, +h1: {one == 1n : Nat}, +k: Nat, +hk31: {Nat.is_lt(k, 31n) == True{} : Bool}, +tabT: AR.Tree<U32>, +pt: {AR.perfect(U32, 1n+k, tabT) == True{} : Bool}, +sd: Nat, +hsd: {Nat.is_lt(sd, 32n) == True{} : Bool}, +kl0: List<&2, String>, +K: AR.Tree<String>, +hsl: {AR.slots(String, K) == kl0 : List<&2, String>}, +pk: {AR.perfect(String, sd, K) == True{} : Bool}, +hwell: {B.all_lt(B.PWell{TB.buckets(AR.slots(U32, tabT), kl0, SC.pow2(k)), sd}, SC.pow2(k)) == True{} : Bool}, +key: String, +hkey: {K.shortk(key) == False{} : Bool}) -> ProbeOK(tabT, sd, kl0, key, STR.lword(key), B.pf(key, TB.buckets(AR.slots(U32, tabT), kl0, SC.pow2(k)), SC.pow2(k), SC.pow2(k), B.mstep(key, B.at(TB.buckets(AR.slots(U32, tabT), kl0, SC.pow2(k)), UD.v(HS.bucket(STR.lword(key), CY.msk(k))))), UD.v(HS.bucket(STR.lword(key), CY.msk(k)))), H.probe_long(AR.thaw(U32, tabT), AR.thaw(String, K), CY.msk(k), key)):
  +bs = TB.buckets(AR.slots(U32, tabT), kl0, SC.pow2(k))
  +n = SC.pow2(k)
  +w = STR.lword(key)
  +i = HS.bucket(w, CY.msk(k))
  +r = B.pf(key, bs, n, n, B.mstep(key, B.at(bs, UD.v(i))), UD.v(i))
  fo = po_of_fo(tabT, sd, kl0, key, w, r, H.find(n, H.step(AR.thaw(U32, tabT), AR.thaw(String, K), i, key, w), CY.msk(k), w, i), PI.find_ok(one, h1, k, hk31, tabT, pt, sd, hsd, kl0, key, hkey, hwell, n, i, home_lt(w, k), K, hsl, pk))
  f1 = L.subst(Nat, f => ProbeOK(tabT, sd, kl0, key, w, r, (H.find(f, H.step(AR.thaw(U32, tabT), AR.thaw(String, K), i, key, w), CY.msk(k), w, i), w)), n, U32.to_nat(U32.inc(CY.msk(k))), Equal.sym(Nat, U32.to_nat(U32.inc(CY.msk(k))), n, fuel_eq(one, h1, k, hk31)), fo)
  L.subst(String & U32, v => ProbeOK(tabT, sd, kl0, key, w, r, H.probe_lw(AR.thaw(U32, tabT), AR.thaw(String, K), CY.msk(k), v)), (key, w), H.key_long(key), Equal.sym(String & U32, H.key_long(key), (key, w), STR.key_long(key)), f1)

def qfin_of(r: B.Res, tab: Array<U32>, ks: Array<String>, +w: U32) -> {H.q_fin(ks, w, QP.qf_of(r, tab)) == (PI.fd_of(r, tab, ks, SNil{}), w) : H.Found & U32}:
  match r:
    case B.RHit{a, l}:
      {==}
    case B.REnd{a}:
      {==}

def probe_short_ok(+one: Nat, +h1: {one == 1n : Nat}, +k: Nat, +hk31: {Nat.is_lt(k, 31n) == True{} : Bool}, +tabT: AR.Tree<U32>, +pt: {AR.perfect(U32, 1n+k, tabT) == True{} : Bool}, +sd: Nat, +hsd: {Nat.is_lt(sd, 32n) == True{} : Bool}, +kl0: List<&2, String>, +K: AR.Tree<String>, +hsl: {AR.slots(String, K) == kl0 : List<&2, String>}, +pk: {AR.perfect(String, sd, K) == True{} : Bool}, +hwell: {B.all_lt(B.PWell{TB.buckets(AR.slots(U32, tabT), kl0, SC.pow2(k)), sd}, SC.pow2(k)) == True{} : Bool}, +c: U32, +hc: {U32.is_lt(c, H.tag()) == True{} : Bool}) -> ProbeOK(tabT, sd, kl0, SNil{}, H.short_word(c), B.pf(SCon{Chr{c}, SNil{}}, TB.buckets(AR.slots(U32, tabT), kl0, SC.pow2(k)), SC.pow2(k), SC.pow2(k), B.mstep(SCon{Chr{c}, SNil{}}, B.at(TB.buckets(AR.slots(U32, tabT), kl0, SC.pow2(k)), UD.v(HS.bucket(H.short_word(c), CY.msk(k))))), UD.v(HS.bucket(H.short_word(c), CY.msk(k)))), H.probe_short(AR.thaw(U32, tabT), AR.thaw(String, K), CY.msk(k), c, True{})):
  +w = H.short_word(c)
  +i = HS.bucket(w, CY.msk(k))
  +n = SC.pow2(k)
  +r = B.pf(SCon{Chr{c}, SNil{}}, TB.buckets(AR.slots(U32, tabT), kl0, SC.pow2(k)), SC.pow2(k), SC.pow2(k), B.mstep(SCon{Chr{c}, SNil{}}, B.at(TB.buckets(AR.slots(U32, tabT), kl0, SC.pow2(k)), UD.v(HS.bucket(H.short_word(c), CY.msk(k))))), UD.v(HS.bucket(H.short_word(c), CY.msk(k))))
  +q = QP.qfind_ok(one, h1, k, hk31, tabT, pt, sd, kl0, c, hc, hwell, n, i, home_lt(w, k))
  +e1 = Equal.trans(H.Found & U32, H.q_fin(AR.thaw(String, K), w, H.qfind(n, H.qstep(AR.thaw(U32, tabT), i, w), CY.msk(k), w, i)), H.q_fin(AR.thaw(String, K), w, QP.qf_of(r, AR.thaw(U32, tabT))), (PI.fd_of(r, AR.thaw(U32, tabT), AR.thaw(String, K), SNil{}), w), Equal.cong(H.QFound, H.Found & U32, z => H.q_fin(AR.thaw(String, K), w, z), H.qfind(n, H.qstep(AR.thaw(U32, tabT), i, w), CY.msk(k), w, i), QP.qf_of(r, AR.thaw(U32, tabT)), q), qfin_of(r, AR.thaw(U32, tabT), AR.thaw(String, K), w))
  +e2 = L.subst(Nat, f => {H.q_fin(AR.thaw(String, K), w, H.qfind(f, H.qstep(AR.thaw(U32, tabT), i, w), CY.msk(k), w, i)) == (PI.fd_of(r, AR.thaw(U32, tabT), AR.thaw(String, K), SNil{}), w) : H.Found & U32}, n, U32.to_nat(U32.inc(CY.msk(k))), Equal.sym(Nat, U32.to_nat(U32.inc(CY.msk(k))), n, fuel_eq(one, h1, k, hk31)), e1)
  (K, (e2, (hsl, pk)))

def pc_short(+one: Nat, +h1: {one == 1n : Nat}, +k: Nat, +hk31: {Nat.is_lt(k, 31n) == True{} : Bool}, +tabT: AR.Tree<U32>, +pt: {AR.perfect(U32, 1n+k, tabT) == True{} : Bool}, +sd: Nat, +hsd: {Nat.is_lt(sd, 32n) == True{} : Bool}, +kl0: List<&2, String>, +K: AR.Tree<String>, +hsl: {AR.slots(String, K) == kl0 : List<&2, String>}, +pk: {AR.perfect(String, sd, K) == True{} : Bool}, +hwell: {B.all_lt(B.PWell{TB.buckets(AR.slots(U32, tabT), kl0, SC.pow2(k)), sd}, SC.pow2(k)) == True{} : Bool}, +c: U32, +b: Bool, +hb: {U32.is_lt(c, H.tag()) == b : Bool}) -> ProbeOK(tabT, sd, kl0, st_c(c, SNil{}, b), K.kw_c(c, SNil{}, b), B.pf(SCon{Chr{c}, SNil{}}, TB.buckets(AR.slots(U32, tabT), kl0, SC.pow2(k)), SC.pow2(k), SC.pow2(k), B.mstep(SCon{Chr{c}, SNil{}}, B.at(TB.buckets(AR.slots(U32, tabT), kl0, SC.pow2(k)), UD.v(HS.bucket(K.kw_c(c, SNil{}, b), CY.msk(k))))), UD.v(HS.bucket(K.kw_c(c, SNil{}, b), CY.msk(k)))), H.probe_short(AR.thaw(U32, tabT), AR.thaw(String, K), CY.msk(k), c, b)):
  match b:
    case True{}:
      probe_short_ok(one, h1, k, hk31, tabT, pt, sd, hsd, kl0, K, hsl, pk, hwell, c, hb)
    case False{}:
      probe_long_ok(one, h1, k, hk31, tabT, pt, sd, hsd, kl0, K, hsl, pk, hwell, SCon{Chr{c}, SNil{}}, hb)

def pc(+one: Nat, +h1: {one == 1n : Nat}, +k: Nat, +hk31: {Nat.is_lt(k, 31n) == True{} : Bool}, +tabT: AR.Tree<U32>, +pt: {AR.perfect(U32, 1n+k, tabT) == True{} : Bool}, +sd: Nat, +hsd: {Nat.is_lt(sd, 32n) == True{} : Bool}, +kl0: List<&2, String>, +K: AR.Tree<String>, +hsl: {AR.slots(String, K) == kl0 : List<&2, String>}, +pk: {AR.perfect(String, sd, K) == True{} : Bool}, +hwell: {B.all_lt(B.PWell{TB.buckets(AR.slots(U32, tabT), kl0, SC.pow2(k)), sd}, SC.pow2(k)) == True{} : Bool}, +c: U32, +t: String) -> ProbeOK(tabT, sd, kl0, st_c(c, t, K.short_c(c, t)), K.kw_c(c, t, K.short_c(c, t)), B.pf(SCon{Chr{c}, t}, TB.buckets(AR.slots(U32, tabT), kl0, SC.pow2(k)), SC.pow2(k), SC.pow2(k), B.mstep(SCon{Chr{c}, t}, B.at(TB.buckets(AR.slots(U32, tabT), kl0, SC.pow2(k)), UD.v(HS.bucket(K.kw_c(c, t, K.short_c(c, t)), CY.msk(k))))), UD.v(HS.bucket(K.kw_c(c, t, K.short_c(c, t)), CY.msk(k)))), H.probe_c(AR.thaw(U32, tabT), AR.thaw(String, K), CY.msk(k), c, t)):
  match t:
    case SNil{}:
      pc_short(one, h1, k, hk31, tabT, pt, sd, hsd, kl0, K, hsl, pk, hwell, c, U32.is_lt(c, H.tag()), {==})
    case SCon{+d, +t2}:
      probe_long_ok(one, h1, k, hk31, tabT, pt, sd, hsd, kl0, K, hsl, pk, hwell, SCon{Chr{c}, SCon{d, t2}}, {==})

# THEOREM: the probe of any key is the model probe from the key's home
# bucket with fuel n; it hands back the key's stored form and its word.
def probe_ok(+one: Nat, +h1: {one == 1n : Nat}, +k: Nat, +hk31: {Nat.is_lt(k, 31n) == True{} : Bool}, +tabT: AR.Tree<U32>, +pt: {AR.perfect(U32, 1n+k, tabT) == True{} : Bool}, +sd: Nat, +hsd: {Nat.is_lt(sd, 32n) == True{} : Bool}, +kl0: List<&2, String>, +K: AR.Tree<String>, +hsl: {AR.slots(String, K) == kl0 : List<&2, String>}, +pk: {AR.perfect(String, sd, K) == True{} : Bool}, +hwell: {B.all_lt(B.PWell{TB.buckets(AR.slots(U32, tabT), kl0, SC.pow2(k)), sd}, SC.pow2(k)) == True{} : Bool}, +key: String) -> ProbeOK(tabT, sd, kl0, stored(key), K.kword(key), B.pf(key, TB.buckets(AR.slots(U32, tabT), kl0, SC.pow2(k)), SC.pow2(k), SC.pow2(k), B.mstep(key, B.at(TB.buckets(AR.slots(U32, tabT), kl0, SC.pow2(k)), UD.v(HS.bucket(K.kword(key), CY.msk(k))))), UD.v(HS.bucket(K.kword(key), CY.msk(k)))), H.probe(AR.thaw(U32, tabT), AR.thaw(String, K), CY.msk(k), key)):
  match key:
    case SNil{}:
      probe_long_ok(one, h1, k, hk31, tabT, pt, sd, hsd, kl0, K, hsl, pk, hwell, SNil{}, {==})
    case SCon{Chr{+c}, +t}:
      pc(one, h1, k, hk31, tabT, pt, sd, hsd, kl0, K, hsl, pk, hwell, c, t)
