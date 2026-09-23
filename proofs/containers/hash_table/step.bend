import Base
import ../../lib/logic.bend as L
import ../../lib/list.bend as LL
import ../../lib/array.bend as AR
import ../../lib/spec_common.bend as SC
import ./spec.bend as S
import ../../lib/u32div.bend as UD
import ../../../src/containers/hash_table.bend as H
import ./strings.bend as STR
import ./table.bend as TB
import ./arr.bend as AX
import ./buckets.bend as B
import ../../lib/words32.bend as W32

# The implementation's probe step for a long key, on arrays built from mirror
# trees: it reads bucket i's word x and link l; on a word match it swaps the
# stored key out, compares and puts it back (the stored keys are unchanged).

def step_of(ms: B.MS, tab: Array<U32>, ks: Array<String>, key: String) -> H.Step:
  match ms:
    case B.MEnd{}:
      H.SEnd{tab, ks, key}
    case B.MHit{l}:
      H.SHit{tab, ks, key, l}
    case B.MNext{}:
      H.SNext{tab, ks, key}

def pick_step(tab: Array<U32>, +l: U32, ks: Array<String>, key: String, +e: Bool) -> {H.sk_pick(tab, l, ks, key, e) == step_of(Bool.pick(B.MS, e, B.MHit{l}, B.MNext{}), tab, ks, key) : H.Step}:
  match e:
    case True{}:
      {==}
    case False{}:
      {==}

# the stored keys after a compare at link l: taken out, put back
def kcmp(+sd: Nat, +ksT: AR.Tree<String>, +l: U32) -> AR.Tree<String>:
  AR.upd(String, sd, AR.upd(String, sd, ksT, UD.v(H.slot(l)), SNil{}), UD.v(H.slot(l)), TB.nths(AR.slots(String, ksT), UD.v(H.slot(l))))

def kcmp_slots(+sd: Nat, +ksT: AR.Tree<String>, +l: U32, +hs: {Nat.is_lt(UD.v(H.slot(l)), SC.pow2(sd)) == True{} : Bool}, +pk: {AR.perfect(String, sd, ksT) == True{} : Bool}) -> {AR.slots(String, kcmp(sd, ksT, l)) == AR.slots(String, ksT) : List<&2, String>}:
  +j = UD.v(H.slot(l))
  +kl = AR.slots(String, ksT)
  +k1 = AR.upd(String, sd, ksT, j, SNil{})
  +p1 = AR.upd_perfect(String, sd, ksT, j, SNil{}, pk)
  +e1 = AR.upd_slots(String, sd, k1, j, TB.nths(kl, j), hs, p1)
  +e2 = Equal.cong(List<&2, String>, List<&2, String>, z => SC.update(String, z, j, TB.nths(kl, j)), AR.slots(String, k1), SC.update(String, kl, j, SNil{}), AR.upd_slots(String, sd, ksT, j, SNil{}, hs, pk))
  Equal.trans(List<&2, String>, AR.slots(String, kcmp(sd, ksT, l)), SC.update(String, AR.slots(String, k1), j, TB.nths(kl, j)), kl, e1,
    Equal.trans(List<&2, String>, SC.update(String, AR.slots(String, k1), j, TB.nths(kl, j)), SC.update(String, SC.update(String, kl, j, SNil{}), j, TB.nths(kl, j)), kl, e2,
      Equal.trans(List<&2, String>, SC.update(String, SC.update(String, kl, j, SNil{}), j, TB.nths(kl, j)), SC.update(String, kl, j, TB.nths(kl, j)), kl, TB.upd_upd(kl, j, SNil{}, TB.nths(kl, j)), TB.upd_self(kl, j))))

def kcmp_perfect(+sd: Nat, +ksT: AR.Tree<String>, +l: U32, +pk: {AR.perfect(String, sd, ksT) == True{} : Bool}) -> {AR.perfect(String, sd, kcmp(sd, ksT, l)) == True{} : Bool}:
  AR.upd_perfect(String, sd, AR.upd(String, sd, ksT, UD.v(H.slot(l)), SNil{}), UD.v(H.slot(l)), TB.nths(AR.slots(String, ksT), UD.v(H.slot(l))), AR.upd_perfect(String, sd, ksT, UD.v(H.slot(l)), SNil{}, pk))

# comparing the probed key with the key stored at link l
def cmp_path(tab: Array<U32>, +sd: Nat, +ksT: AR.Tree<String>, +l: U32, +key: String, +hsd: {Nat.is_lt(sd, 32n) == True{} : Bool}, +hs: {Nat.is_lt(UD.v(H.slot(l)), SC.pow2(sd)) == True{} : Bool}, +pk: {AR.perfect(String, sd, ksT) == True{} : Bool}) -> {H.sk_same(tab, AR.thaw(String, ksT), l, key, True{}) == step_of(Bool.pick(B.MS, S.str_eq(key, TB.nths(AR.slots(String, ksT), UD.v(H.slot(l)))), B.MHit{l}, B.MNext{}), tab, AR.thaw(String, kcmp(sd, ksT, l)), key) : H.Step}:
  +j = UD.v(H.slot(l))
  +kl = AR.slots(String, ksT)
  +k = TB.nths(kl, j)
  +k1 = AR.upd(String, sd, ksT, j, SNil{})
  +e = S.str_eq(key, k)
  +hsw = AR.swap(String, sd, ksT, H.slot(l), SNil{}, k, hsd, hs, AX.nths_of(sd, ksT, j, hs, pk), pk)
  +hk1 = L.subst(List<&2, String>, ys => {SC.nth(String, ys, j) == Some{SNil{}} : Maybe<&2, String>}, SC.update(String, kl, j, SNil{}), AR.slots(String, k1), Equal.sym(List<&2, String>, AR.slots(String, k1), SC.update(String, kl, j, SNil{}), AR.upd_slots(String, sd, ksT, j, SNil{}, hs, pk)), LL.nth_update_same(String, kl, j, SNil{}, LL.nth_lt_length(String, kl, j, k, AX.nths_of(sd, ksT, j, hs, pk))))
  +hset = AR.set(String, sd, k1, H.slot(l), k, SNil{}, hsd, hs, hk1, AR.upd_perfect(String, sd, ksT, j, SNil{}, pk))
  +s1 = Equal.cong(Array<String> & String, H.Step, r => H.sk_cmp(tab, l, key, r), Array.swap(String, AR.thaw(String, ksT), H.slot(l), SNil{}), (AR.thaw(String, k1), k), hsw)
  +s2 = Equal.cong((String & String) & Bool, H.Step, r => H.sk_fin(tab, l, AR.thaw(String, k1), r), H.eq(key, k), ((key, k), e), STR.eq(key, k))
  +s3 = Equal.cong(Array<String>, H.Step, a => H.sk_pick(tab, l, a, key, e), Array.set(String, AR.thaw(String, k1), H.slot(l), k), AR.thaw(String, kcmp(sd, ksT, l)), hset)
  Equal.trans(H.Step, H.sk_cmp(tab, l, key, Array.swap(String, AR.thaw(String, ksT), H.slot(l), SNil{})), H.sk_fin(tab, l, AR.thaw(String, k1), H.eq(key, k)), step_of(Bool.pick(B.MS, e, B.MHit{l}, B.MNext{}), tab, AR.thaw(String, kcmp(sd, ksT, l)), key), s1,
    Equal.trans(H.Step, H.sk_fin(tab, l, AR.thaw(String, k1), H.eq(key, k)), H.sk_pick(tab, l, Array.set(String, AR.thaw(String, k1), H.slot(l), k), key, e), step_of(Bool.pick(B.MS, e, B.MHit{l}, B.MNext{}), tab, AR.thaw(String, kcmp(sd, ksT, l)), key), s2,
      Equal.trans(H.Step, H.sk_pick(tab, l, Array.set(String, AR.thaw(String, k1), H.slot(l), k), key, e), H.sk_pick(tab, l, AR.thaw(String, kcmp(sd, ksT, l)), key, e), step_of(Bool.pick(B.MS, e, B.MHit{l}, B.MNext{}), tab, AR.thaw(String, kcmp(sd, ksT, l)), key), s3, pick_step(tab, l, AR.thaw(String, kcmp(sd, ksT, l)), key, e))))

# the decision of a long-key step on word x, link l, stored key k
def ld_w(+key: String, +l: U32, +k: String, same: Bool) -> B.MS:
  match same:
    case False{}:
      B.MNext{}
    case True{}:
      Bool.pick(B.MS, S.str_eq(key, k), B.MHit{l}, B.MNext{})

def ld_e(+key: String, +w: U32, +x: U32, +l: U32, +k: String, empty: Bool) -> B.MS:
  match empty:
    case True{}:
      B.MEnd{}
    case False{}:
      ld_w(key, l, k, U32.is_eq(x, w))

def ldec(+key: String, +w: U32, +x: U32, +l: U32, +k: String) -> B.MS:
  ld_e(key, w, x, l, k, U32.is_eq(x, 0))

def ka_w(+sd: Nat, +ksT: AR.Tree<String>, +l: U32, same: Bool) -> AR.Tree<String>:
  match same:
    case False{}:
      ksT
    case True{}:
      kcmp(sd, ksT, l)

def ka_e(+sd: Nat, +ksT: AR.Tree<String>, +w: U32, +x: U32, +l: U32, empty: Bool) -> AR.Tree<String>:
  match empty:
    case True{}:
      ksT
    case False{}:
      ka_w(sd, ksT, l, U32.is_eq(x, w))

# the stored keys after a long-key step
def kafter(+sd: Nat, +ksT: AR.Tree<String>, +w: U32, +x: U32, +l: U32) -> AR.Tree<String>:
  ka_e(sd, ksT, w, x, l, U32.is_eq(x, 0))

def st_same(tab: Array<U32>, +sd: Nat, +ksT: AR.Tree<String>, +l: U32, +key: String, +hsd: {Nat.is_lt(sd, 32n) == True{} : Bool}, +hs: {Nat.is_lt(UD.v(H.slot(l)), SC.pow2(sd)) == True{} : Bool}, +pk: {AR.perfect(String, sd, ksT) == True{} : Bool}, +same: Bool) -> {H.sk_same(tab, AR.thaw(String, ksT), l, key, same) == step_of(ld_w(key, l, TB.nths(AR.slots(String, ksT), UD.v(H.slot(l))), same), tab, AR.thaw(String, ka_w(sd, ksT, l, same)), key) : H.Step}:
  match same:
    case False{}:
      {==}
    case True{}:
      cmp_path(tab, sd, ksT, l, key, hsd, hs, pk)

def st_empty(+td: Nat, +tabT: AR.Tree<U32>, +sd: Nat, +ksT: AR.Tree<String>, +i: U32, +key: String, +w: U32, +hd: {Nat.is_lt(td, 32n) == True{} : Bool}, +hsd: {Nat.is_lt(sd, 32n) == True{} : Bool}, +pt: {AR.perfect(U32, td, tabT) == True{} : Bool}, +pk: {AR.perfect(String, sd, ksT) == True{} : Bool}, +hl: {Nat.is_lt(UD.v(U32.inc(U32.shl(i))), SC.pow2(td)) == True{} : Bool}, +x: U32, +hs: {B.implies(Bool.not(U32.is_eq(x, 0)), Nat.is_lt(UD.v(H.slot(W32.nth0(AR.slots(U32, tabT), UD.v(U32.inc(U32.shl(i)))))), SC.pow2(sd))) == True{} : Bool}, +e: Bool, +he: {U32.is_eq(x, 0) == e : Bool}) -> {H.sk_empty(AR.thaw(U32, tabT), AR.thaw(String, ksT), i, key, w, x, e) == step_of(ld_e(key, w, x, W32.nth0(AR.slots(U32, tabT), UD.v(U32.inc(U32.shl(i)))), TB.nths(AR.slots(String, ksT), UD.v(H.slot(W32.nth0(AR.slots(U32, tabT), UD.v(U32.inc(U32.shl(i))))))), e), AR.thaw(U32, tabT), AR.thaw(String, ka_e(sd, ksT, w, x, W32.nth0(AR.slots(U32, tabT), UD.v(U32.inc(U32.shl(i)))), e)), key) : H.Step}:
  match e:
    case True{}:
      {==}
    case False{}:
      +l = W32.nth0(AR.slots(U32, tabT), UD.v(U32.inc(U32.shl(i))))
      +hs2 = B.imp_elim(Bool.not(U32.is_eq(x, 0)), Nat.is_lt(UD.v(H.slot(l)), SC.pow2(sd)), hs, L.subst(Bool, b => {Bool.not(b) == True{} : Bool}, False{}, U32.is_eq(x, 0), Equal.sym(Bool, U32.is_eq(x, 0), False{}, he), {==}))
      +g = AX.getw(td, tabT, U32.inc(U32.shl(i)), hd, hl, pt)
      Equal.trans(H.Step, H.sk_l(AR.thaw(String, ksT), key, x, w, Array.get(U32, AR.thaw(U32, tabT), U32.inc(U32.shl(i)))), H.sk_l(AR.thaw(String, ksT), key, x, w, (AR.thaw(U32, tabT), l)), step_of(ld_w(key, l, TB.nths(AR.slots(String, ksT), UD.v(H.slot(l))), U32.is_eq(x, w)), AR.thaw(U32, tabT), AR.thaw(String, ka_w(sd, ksT, l, U32.is_eq(x, w))), key),
        Equal.cong(Array<U32> & U32, H.Step, r => H.sk_l(AR.thaw(String, ksT), key, x, w, r), Array.get(U32, AR.thaw(U32, tabT), U32.inc(U32.shl(i))), (AR.thaw(U32, tabT), l), g),
        st_same(AR.thaw(U32, tabT), sd, ksT, l, key, hsd, hs2, pk, U32.is_eq(x, w)))

# THEOREM: a long-key probe step reads bucket i and decides as ldec.
def step_long(+td: Nat, +tabT: AR.Tree<U32>, +sd: Nat, +ksT: AR.Tree<String>, +i: U32, +key: String, +w: U32, +hd: {Nat.is_lt(td, 32n) == True{} : Bool}, +hsd: {Nat.is_lt(sd, 32n) == True{} : Bool}, +pt: {AR.perfect(U32, td, tabT) == True{} : Bool}, +pk: {AR.perfect(String, sd, ksT) == True{} : Bool}, +hw: {Nat.is_lt(UD.v(U32.shl(i)), SC.pow2(td)) == True{} : Bool}, +hl: {Nat.is_lt(UD.v(U32.inc(U32.shl(i))), SC.pow2(td)) == True{} : Bool}, +hs: {B.implies(Bool.not(U32.is_eq(W32.nth0(AR.slots(U32, tabT), UD.v(U32.shl(i))), 0)), Nat.is_lt(UD.v(H.slot(W32.nth0(AR.slots(U32, tabT), UD.v(U32.inc(U32.shl(i)))))), SC.pow2(sd))) == True{} : Bool}) -> {H.step(AR.thaw(U32, tabT), AR.thaw(String, ksT), i, key, w) == step_of(ldec(key, w, W32.nth0(AR.slots(U32, tabT), UD.v(U32.shl(i))), W32.nth0(AR.slots(U32, tabT), UD.v(U32.inc(U32.shl(i)))), TB.nths(AR.slots(String, ksT), UD.v(H.slot(W32.nth0(AR.slots(U32, tabT), UD.v(U32.inc(U32.shl(i)))))))), AR.thaw(U32, tabT), AR.thaw(String, kafter(sd, ksT, w, W32.nth0(AR.slots(U32, tabT), UD.v(U32.shl(i))), W32.nth0(AR.slots(U32, tabT), UD.v(U32.inc(U32.shl(i)))))), key) : H.Step}:
  +x = W32.nth0(AR.slots(U32, tabT), UD.v(U32.shl(i)))
  +g = AX.getw(td, tabT, U32.shl(i), hd, hw, pt)
  Equal.trans(H.Step, H.sk_w(AR.thaw(String, ksT), i, key, w, Array.get(U32, AR.thaw(U32, tabT), U32.shl(i))), H.sk_w(AR.thaw(String, ksT), i, key, w, (AR.thaw(U32, tabT), x)), step_of(ldec(key, w, x, W32.nth0(AR.slots(U32, tabT), UD.v(U32.inc(U32.shl(i)))), TB.nths(AR.slots(String, ksT), UD.v(H.slot(W32.nth0(AR.slots(U32, tabT), UD.v(U32.inc(U32.shl(i)))))))), AR.thaw(U32, tabT), AR.thaw(String, kafter(sd, ksT, w, x, W32.nth0(AR.slots(U32, tabT), UD.v(U32.inc(U32.shl(i)))))), key),
    Equal.cong(Array<U32> & U32, H.Step, r => H.sk_w(AR.thaw(String, ksT), i, key, w, r), Array.get(U32, AR.thaw(U32, tabT), U32.shl(i)), (AR.thaw(U32, tabT), x), g),
    st_empty(td, tabT, sd, ksT, i, key, w, hd, hsd, pt, pk, hl, x, hs, U32.is_eq(x, 0), {==}))
