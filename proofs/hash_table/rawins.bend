import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/array.bend as AR
import ../spec/common.bend as SC
import ../math/word.bend as WD
import ../math/u32div.bend as UD
import ../../src/math/hash.bend as HS
import ../../src/containers/hash_table.bend as H
import ./table.bend as TB
import ./buckets.bend as B
import ./modn.bend as M
import ./cyc.bend as CY
import ./arr.bend as AX
import ./inv.bend as IV
import ./probe_impl.bend as PI
import ./probe_all.bend as PA
import ./keys.bend as K2

# ins_raw puts a (word, link) pair into the first empty bucket of the word's
# probe path, without reading any key.


# the walk: the first empty bucket within f steps of i
def ri(+tb: List<&2, U32>, +n: Nat, f: Nat, +i: Nat) -> Maybe<&2, Nat>:
  match f:
    case 0n:
      None{}
    case 1n+p:
      Bool.pick(Maybe<&2, Nat>, U32.is_eq(TB.nth0(tb, Nat.double(i)), 0), Some{i}, ri(tb, n, p, Nat.mod(1n+i, n)))

def rput(tab: Array<U32>, m: Maybe<&2, Nat>, +w: U32, +l: U32) -> Array<U32>:
  match m:
    case None{}:
      tab
    case Some{+e}:
      H.put_bucket(tab, U32.from_nat(e), w, l)

# ---- the implementation follows the walk ----

def go0(+T: AR.Tree<U32>, +mask: U32, +i: U32, +w: U32, +l: U32, +c: Bool) -> {H.ins_go(0n, H.rs_if(AR.thaw(U32, T), c), mask, i, w, l) == AR.thaw(U32, T) : Array<U32>}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def rstep_eq(+one: Nat, +h1: {one == 1n : Nat}, +K: Nat, +hK: {Nat.is_lt(K, 31n) == True{} : Bool}, +T: AR.Tree<U32>, +pt: {AR.perfect(U32, 1n+K, T) == True{} : Bool}, +i: U32, +hi: {Nat.is_lt(UD.v(i), SC.pow2(K)) == True{} : Bool}) -> {H.rstep(AR.thaw(U32, T), i) == H.rs_if(AR.thaw(U32, T), U32.is_eq(TB.nth0(AR.slots(U32, T), Nat.double(UD.v(i))), 0)) : H.RStep}:
  +hh = N.double_lt_bit(True{}, UD.v(i), SC.pow2(K), hi)
  +ew = AX.ix_w(i, 1n+K, hK, hh)
  +hw = L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(1n+K)) == True{} : Bool}, Nat.double(UD.v(i)), UD.v(U32.shl(i)), Equal.sym(Nat, UD.v(U32.shl(i)), Nat.double(UD.v(i)), ew), N.lt_trans(Nat.double(UD.v(i)), 1n+Nat.double(UD.v(i)), SC.pow2(1n+K), N.lt_succ(Nat.double(UD.v(i))), hh))
  +g = AX.getw(1n+K, T, U32.shl(i), hK, hw, pt)
  Equal.trans(H.RStep, H.rstep(AR.thaw(U32, T), i), H.rs_w((AR.thaw(U32, T), TB.nth0(AR.slots(U32, T), UD.v(U32.shl(i))))), H.rs_if(AR.thaw(U32, T), U32.is_eq(TB.nth0(AR.slots(U32, T), Nat.double(UD.v(i))), 0)), Equal.cong(Array<U32> & U32, H.RStep, r => H.rs_w(r), Array.get(U32, AR.thaw(U32, T), U32.shl(i)), (AR.thaw(U32, T), TB.nth0(AR.slots(U32, T), UD.v(U32.shl(i)))), g), Equal.cong(Nat, H.RStep, z => H.rs_if(AR.thaw(U32, T), U32.is_eq(TB.nth0(AR.slots(U32, T), z), 0)), UD.v(U32.shl(i)), Nat.double(UD.v(i)), ew))

def go_c(+K: Nat, +T: AR.Tree<U32>, +p: Nat, +i: U32, +hk: {Nat.is_le(K, 32n) == True{} : Bool}, +hi: {Nat.is_lt(UD.v(i), SC.pow2(K)) == True{} : Bool}, +w: U32, +l: U32, +hnext: {UD.v(H.bnext(i, CY.msk(K))) == Nat.mod(1n+UD.v(i), SC.pow2(K)) : Nat}, +rec: {H.ins_go(p, H.rstep(AR.thaw(U32, T), H.bnext(i, CY.msk(K))), CY.msk(K), H.bnext(i, CY.msk(K)), w, l) == rput(AR.thaw(U32, T), ri(AR.slots(U32, T), SC.pow2(K), p, UD.v(H.bnext(i, CY.msk(K)))), w, l) : Array<U32>}, +c: Bool) -> {H.ins_go(1n+p, H.rs_if(AR.thaw(U32, T), c), CY.msk(K), i, w, l) == rput(AR.thaw(U32, T), Bool.pick(Maybe<&2, Nat>, c, Some{UD.v(i)}, ri(AR.slots(U32, T), SC.pow2(K), p, Nat.mod(1n+UD.v(i), SC.pow2(K)))), w, l) : Array<U32>}:
  match c:
    case True{}:
      Equal.cong(U32, Array<U32>, z => H.put_bucket(AR.thaw(U32, T), z, w, l), i, U32.from_nat(UD.v(i)), Equal.sym(U32, U32.from_nat(UD.v(i)), i, PI.from_v(i, K, hk, hi)))
    case False{}:
      L.subst(Nat, z => {H.ins_go(p, H.rstep(AR.thaw(U32, T), H.bnext(i, CY.msk(K))), CY.msk(K), H.bnext(i, CY.msk(K)), w, l) == rput(AR.thaw(U32, T), ri(AR.slots(U32, T), SC.pow2(K), p, z), w, l) : Array<U32>}, UD.v(H.bnext(i, CY.msk(K))), Nat.mod(1n+UD.v(i), SC.pow2(K)), hnext, rec)

# THEOREM: the implementation's insertion loop places the pair where the walk ends
def raw_impl(+one: Nat, +h1: {one == 1n : Nat}, +K: Nat, +hK: {Nat.is_lt(K, 31n) == True{} : Bool}, +T: AR.Tree<U32>, +pt: {AR.perfect(U32, 1n+K, T) == True{} : Bool}, +f: Nat, +i: U32, +hi: {Nat.is_lt(UD.v(i), SC.pow2(K)) == True{} : Bool}, +w: U32, +l: U32) -> {H.ins_go(f, H.rstep(AR.thaw(U32, T), i), CY.msk(K), i, w, l) == rput(AR.thaw(U32, T), ri(AR.slots(U32, T), SC.pow2(K), f, UD.v(i)), w, l) : Array<U32>}:
  match f:
    case 0n:
      +es = rstep_eq(one, h1, K, hK, T, pt, i, hi)
      L.subst(H.RStep, s => {H.ins_go(0n, s, CY.msk(K), i, w, l) == AR.thaw(U32, T) : Array<U32>}, H.rs_if(AR.thaw(U32, T), U32.is_eq(TB.nth0(AR.slots(U32, T), Nat.double(UD.v(i))), 0)), H.rstep(AR.thaw(U32, T), i), Equal.sym(H.RStep, H.rstep(AR.thaw(U32, T), i), H.rs_if(AR.thaw(U32, T), U32.is_eq(TB.nth0(AR.slots(U32, T), Nat.double(UD.v(i))), 0)), es), go0(T, CY.msk(K), i, w, l, U32.is_eq(TB.nth0(AR.slots(U32, T), Nat.double(UD.v(i))), 0)))
    case 1n+p:
      +es = rstep_eq(one, h1, K, hK, T, pt, i, hi)
      +hk = N.lt_le(K, 32n, N.lt_trans(K, 31n, 32n, hK, {==}))
      +hks = L.subst(Nat, z => {Nat.is_lt(z, WD.sc(32n, one)) == True{} : Bool}, SC.pow2(K), WD.sc(K, one), AX.pow_one(one, h1, K), N.lt_le_trans(SC.pow2(K), SC.pow2(1n+K), WD.sc(32n, one), N.pow2_lt_succ(K), AX.pow_le32(one, h1, 1n+K, hK)))
      +hi1 = L.subst(Nat, z => {Nat.is_lt(UD.v(i), z) == True{} : Bool}, SC.pow2(K), WD.sc(K, one), AX.pow_one(one, h1, K), hi)
      +hnext = Equal.trans(Nat, UD.v(H.bnext(i, CY.msk(K))), Nat.mod(1n+UD.v(i), WD.sc(K, one)), Nat.mod(1n+UD.v(i), SC.pow2(K)), CY.next_val(one, h1, K, i, hks, hi1), Equal.cong(Nat, Nat, z => Nat.mod(1n+UD.v(i), z), WD.sc(K, one), SC.pow2(K), Equal.sym(Nat, SC.pow2(K), WD.sc(K, one), AX.pow_one(one, h1, K))))
      +hj = L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(K)) == True{} : Bool}, Nat.mod(1n+UD.v(i), SC.pow2(K)), UD.v(H.bnext(i, CY.msk(K))), Equal.sym(Nat, UD.v(H.bnext(i, CY.msk(K))), Nat.mod(1n+UD.v(i), SC.pow2(K)), hnext), PI.mod_lt(SC.pow2(K), N.succ_le_lt(0n, SC.pow2(K), N.pow2_pos(K)), 1n+UD.v(i)))
      +rec = raw_impl(one, h1, K, hK, T, pt, p, H.bnext(i, CY.msk(K)), hj, w, l)
      L.subst(H.RStep, s => {H.ins_go(1n+p, s, CY.msk(K), i, w, l) == rput(AR.thaw(U32, T), ri(AR.slots(U32, T), SC.pow2(K), 1n+p, UD.v(i)), w, l) : Array<U32>}, H.rs_if(AR.thaw(U32, T), U32.is_eq(TB.nth0(AR.slots(U32, T), Nat.double(UD.v(i))), 0)), H.rstep(AR.thaw(U32, T), i), Equal.sym(H.RStep, H.rstep(AR.thaw(U32, T), i), H.rs_if(AR.thaw(U32, T), U32.is_eq(TB.nth0(AR.slots(U32, T), Nat.double(UD.v(i))), 0)), es), go_c(K, T, p, i, hk, hi, w, l, hnext, rec, U32.is_eq(TB.nth0(AR.slots(U32, T), Nat.double(UD.v(i))), 0)))

# ---- the walk ends at the first empty bucket of the path ----


def occ_dec(+w: U32, +l: U32, +kl: List<&2, String>, +c: Bool) -> {B.occ(TB.dec_c(w, l, kl, c)) == Bool.not(c) : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def occ_flag(+tb: List<&2, U32>, +kl: List<&2, String>, +n: Nat, +j: Nat, +hj: {Nat.is_lt(j, n) == True{} : Bool}) -> {B.occ(B.at(TB.buckets(tb, kl, n), j)) == Bool.not(U32.is_eq(TB.nth0(tb, Nat.double(j)), 0)) : Bool}:
  Equal.trans(Bool, B.occ(B.at(TB.buckets(tb, kl, n), j)), B.occ(TB.dec(tb, kl, j)), Bool.not(U32.is_eq(TB.nth0(tb, Nat.double(j)), 0)), Equal.cong(B.Bk, Bool, b => B.occ(b), B.at(TB.buckets(tb, kl, n), j), TB.dec(tb, kl, j), TB.at_buckets(tb, kl, n, j, hj)), occ_dec(TB.nth0(tb, Nat.double(j)), TB.nth0(tb, 1n+Nat.double(j)), kl, U32.is_eq(TB.nth0(tb, Nat.double(j)), 0)))

def rp_t(+t: Nat, +d: Nat, +ht: {Nat.is_le(t, d) == True{} : Bool}, +c: Bool, +hc: {Nat.is_lt(t, d) == c : Bool}, +no: {c == False{} : Bool}) -> {t == d : Nat}:
  N.le_antisym(t, d, ht, N.not_lt_le(t, d, Equal.trans(Bool, Nat.is_lt(t, d), c, False{}, hc, no)))

def rp_true(+tb: List<&2, U32>, +kl: List<&2, String>, +bp: Nat, +h: Nat, +hh: {Nat.is_lt(h, 1n+bp) == True{} : Bool}, +e: Nat, +he: {Nat.is_lt(e, 1n+bp) == True{} : Bool}, +hz: {B.at(TB.buckets(tb, kl, 1n+bp), e) == B.BE{} : B.Bk}, +hp: {B.occpath(TB.buckets(tb, kl, 1n+bp), 1n+bp, h, M.dist(1n+bp, h, e)) == True{} : Bool}, +t: Nat, +ht: {Nat.is_le(t, M.dist(1n+bp, h, e)) == True{} : Bool}, +hc: {U32.is_eq(TB.nth0(tb, Nat.double(M.pos(1n+bp, h, t))), 0) == True{} : Bool}, +c2: Bool, +hc2: {Nat.is_lt(t, M.dist(1n+bp, h, e)) == c2 : Bool}) -> {Some{M.pos(1n+bp, h, t)} == Some{e} : Maybe<&2, Nat>}:
  match c2:
    case True{}:
      +o1 = B.occ_inst(TB.buckets(tb, kl, 1n+bp), 1n+bp, h, M.dist(1n+bp, h, e), hp, t, hc2)
      +o2 = Equal.trans(Bool, True{}, B.occ(B.at(TB.buckets(tb, kl, 1n+bp), M.pos(1n+bp, h, t))), False{}, Equal.sym(Bool, B.occ(B.at(TB.buckets(tb, kl, 1n+bp), M.pos(1n+bp, h, t))), True{}, o1), Equal.trans(Bool, B.occ(B.at(TB.buckets(tb, kl, 1n+bp), M.pos(1n+bp, h, t))), Bool.not(U32.is_eq(TB.nth0(tb, Nat.double(M.pos(1n+bp, h, t))), 0)), False{}, occ_flag(tb, kl, 1n+bp, M.pos(1n+bp, h, t), M.pos_lt(bp, h, t)), Equal.cong(Bool, Bool, b => Bool.not(b), U32.is_eq(TB.nth0(tb, Nat.double(M.pos(1n+bp, h, t))), 0), True{}, hc)))
      Empty.absurd({Some{M.pos(1n+bp, h, t)} == Some{e} : Maybe<&2, Nat>}, L.true_false(o2))
    case False{}:
      +etd = rp_t(t, M.dist(1n+bp, h, e), ht, False{}, hc2, {==})
      Equal.cong(Nat, Maybe<&2, Nat>, z => Some{z}, M.pos(1n+bp, h, t), e, Equal.trans(Nat, M.pos(1n+bp, h, t), M.pos(1n+bp, h, M.dist(1n+bp, h, e)), e, Equal.cong(Nat, Nat, z => M.pos(1n+bp, h, z), t, M.dist(1n+bp, h, e), etd), M.pos_dist(bp, h, e, hh, he)))

def rp_false(+tb: List<&2, U32>, +kl: List<&2, String>, +bp: Nat, +h: Nat, +hh: {Nat.is_lt(h, 1n+bp) == True{} : Bool}, +e: Nat, +he: {Nat.is_lt(e, 1n+bp) == True{} : Bool}, +hz: {B.at(TB.buckets(tb, kl, 1n+bp), e) == B.BE{} : B.Bk}, +hp: {B.occpath(TB.buckets(tb, kl, 1n+bp), 1n+bp, h, M.dist(1n+bp, h, e)) == True{} : Bool}, +t: Nat, +ht: {Nat.is_le(t, M.dist(1n+bp, h, e)) == True{} : Bool}, +hc: {U32.is_eq(TB.nth0(tb, Nat.double(M.pos(1n+bp, h, t))), 0) == False{} : Bool}, +c2: Bool, +hc2: {Nat.is_eq(t, M.dist(1n+bp, h, e)) == c2 : Bool}) -> {Nat.is_le(1n+t, M.dist(1n+bp, h, e)) == True{} : Bool}:
  match c2:
    case False{}:
      N.lt_succ_le_succ(t, M.dist(1n+bp, h, e), N.lt_or_eq(t, M.dist(1n+bp, h, e), ht, hc2))
    case True{}:
      +pe = Equal.trans(Nat, M.pos(1n+bp, h, t), M.pos(1n+bp, h, M.dist(1n+bp, h, e)), e, Equal.cong(Nat, Nat, z => M.pos(1n+bp, h, z), t, M.dist(1n+bp, h, e), N.eq_from_is_eq(t, M.dist(1n+bp, h, e), hc2)), M.pos_dist(bp, h, e, hh, he))
      +o1 = Equal.trans(Bool, B.occ(B.at(TB.buckets(tb, kl, 1n+bp), M.pos(1n+bp, h, t))), Bool.not(U32.is_eq(TB.nth0(tb, Nat.double(M.pos(1n+bp, h, t))), 0)), True{}, occ_flag(tb, kl, 1n+bp, M.pos(1n+bp, h, t), M.pos_lt(bp, h, t)), Equal.cong(Bool, Bool, b => Bool.not(b), U32.is_eq(TB.nth0(tb, Nat.double(M.pos(1n+bp, h, t))), 0), False{}, hc))
      +o2 = L.subst(Nat, z => {B.occ(B.at(TB.buckets(tb, kl, 1n+bp), z)) == True{} : Bool}, M.pos(1n+bp, h, t), e, pe, o1)
      Empty.absurd({Nat.is_le(1n+t, M.dist(1n+bp, h, e)) == True{} : Bool}, B.occ_at_be(TB.buckets(tb, kl, 1n+bp), e, hz, o2))

def rp_c(+tb: List<&2, U32>, +kl: List<&2, String>, +bp: Nat, +h: Nat, +hh: {Nat.is_lt(h, 1n+bp) == True{} : Bool}, +e: Nat, +he: {Nat.is_lt(e, 1n+bp) == True{} : Bool}, +hz: {B.at(TB.buckets(tb, kl, 1n+bp), e) == B.BE{} : B.Bk}, +hp: {B.occpath(TB.buckets(tb, kl, 1n+bp), 1n+bp, h, M.dist(1n+bp, h, e)) == True{} : Bool}, +p: Nat, +t: Nat, +ht: {Nat.is_le(t, M.dist(1n+bp, h, e)) == True{} : Bool}, +c: Bool, +hc: {U32.is_eq(TB.nth0(tb, Nat.double(M.pos(1n+bp, h, t))), 0) == c : Bool}, rec: @ht2: {Nat.is_le(1n+t, M.dist(1n+bp, h, e)) == True{} : Bool} -> {ri(tb, 1n+bp, p, M.pos(1n+bp, h, 1n+t)) == Some{e} : Maybe<&2, Nat>}) -> {Bool.pick(Maybe<&2, Nat>, c, Some{M.pos(1n+bp, h, t)}, ri(tb, 1n+bp, p, Nat.mod(1n+M.pos(1n+bp, h, t), 1n+bp))) == Some{e} : Maybe<&2, Nat>}:
  match c:
    case True{}:
      rp_true(tb, kl, bp, h, hh, e, he, hz, hp, t, ht, hc, Nat.is_lt(t, M.dist(1n+bp, h, e)), {==})
    case False{}:
      L.subst(Nat, z => {ri(tb, 1n+bp, p, z) == Some{e} : Maybe<&2, Nat>}, M.pos(1n+bp, h, 1n+t), Nat.mod(1n+M.pos(1n+bp, h, t), 1n+bp), Equal.sym(Nat, Nat.mod(1n+M.pos(1n+bp, h, t), 1n+bp), M.pos(1n+bp, h, 1n+t), M.pos_next(bp, h, t)), rec(rp_false(tb, kl, bp, h, hh, e, he, hz, hp, t, ht, hc, Nat.is_eq(t, M.dist(1n+bp, h, e)), {==})))

def ri_path(+tb: List<&2, U32>, +kl: List<&2, String>, +bp: Nat, +h: Nat, +hh: {Nat.is_lt(h, 1n+bp) == True{} : Bool}, +e: Nat, +he: {Nat.is_lt(e, 1n+bp) == True{} : Bool}, +hz: {B.at(TB.buckets(tb, kl, 1n+bp), e) == B.BE{} : B.Bk}, +hp: {B.occpath(TB.buckets(tb, kl, 1n+bp), 1n+bp, h, M.dist(1n+bp, h, e)) == True{} : Bool}, +f: Nat, +t: Nat, +ht: {Nat.is_le(t, M.dist(1n+bp, h, e)) == True{} : Bool}, +hft: {Nat.add(t, f) == 1n+bp : Nat}) -> {ri(tb, 1n+bp, f, M.pos(1n+bp, h, t)) == Some{e} : Maybe<&2, Nat>}:
  match f:
    case 0n:
      +et = Equal.trans(Nat, t, Nat.add(t, 0n), 1n+bp, Equal.sym(Nat, Nat.add(t, 0n), t, N.add_zero(t)), hft)
      Empty.absurd({ri(tb, 1n+bp, 0n, M.pos(1n+bp, h, t)) == Some{e} : Maybe<&2, Nat>}, N.lt_ne(t, 1n+bp, N.le_lt_trans(t, M.dist(1n+bp, h, e), 1n+bp, ht, M.dist_lt(bp, h, e)), et))
    case 1n+p:
      +hft2 = Equal.trans(Nat, Nat.add(1n+t, p), Nat.add(t, 1n+p), 1n+bp, Equal.sym(Nat, Nat.add(t, 1n+p), 1n+Nat.add(t, p), N.add_succ(t, p)), hft)
      rp_c(tb, kl, bp, h, hh, e, he, hz, hp, p, t, ht, U32.is_eq(TB.nth0(tb, Nat.double(M.pos(1n+bp, h, t))), 0), {==}, ht2 => ri_path(tb, kl, bp, h, hh, e, he, hz, hp, p, 1n+t, ht2, hft2))

def ri_n(+tb: List<&2, U32>, +kl: List<&2, String>, +n: Nat, +hn: {Nat.is_lt(0n, n) == True{} : Bool}, +h: Nat, +hh: {Nat.is_lt(h, n) == True{} : Bool}, +e: Nat, +he: {Nat.is_lt(e, n) == True{} : Bool}, +hz: {B.at(TB.buckets(tb, kl, n), e) == B.BE{} : B.Bk}, +hp: {B.occpath(TB.buckets(tb, kl, n), n, h, M.dist(n, h, e)) == True{} : Bool}) -> {ri(tb, n, n, h) == Some{e} : Maybe<&2, Nat>}:
  match n:
    case 0n:
      Empty.absurd({ri(tb, 0n, 0n, h) == Some{e} : Maybe<&2, Nat>}, L.false_true(hn))
    case 1n+bp:
      L.subst(Nat, z => {ri(tb, 1n+bp, 1n+bp, z) == Some{e} : Maybe<&2, Nat>}, M.pos(1n+bp, h, 0n), h, IV.pos0(bp, h, hh), ri_path(tb, kl, bp, h, hh, e, he, hz, hp, 1n+bp, 0n, N.zero_le(M.dist(1n+bp, h, e)), {==}))


# THEOREM: ins_raw writes the pair into the first empty bucket of its path
def raw_ok(+one: Nat, +h1: {one == 1n : Nat}, +K: Nat, +hK: {Nat.is_lt(K, 31n) == True{} : Bool}, +T: AR.Tree<U32>, +pt: {AR.perfect(U32, 1n+K, T) == True{} : Bool}, +kl: List<&2, String>, +w: U32, +l: U32, +e: Nat, +he: {Nat.is_lt(e, SC.pow2(K)) == True{} : Bool}, +hz: {B.at(TB.buckets(AR.slots(U32, T), kl, SC.pow2(K)), e) == B.BE{} : B.Bk}, +hp: {B.occpath(TB.buckets(AR.slots(U32, T), kl, SC.pow2(K)), SC.pow2(K), UD.v(HS.bucket(w, CY.msk(K))), M.dist(SC.pow2(K), UD.v(HS.bucket(w, CY.msk(K))), e)) == True{} : Bool}) -> {H.ins_raw(AR.thaw(U32, T), CY.msk(K), w, l) == H.put_bucket(AR.thaw(U32, T), U32.from_nat(e), w, l) : Array<U32>}:
  +i = HS.bucket(w, CY.msk(K))
  +e1 = Equal.cong(Nat, Array<U32>, f => H.ins_go(f, H.rstep(AR.thaw(U32, T), i), CY.msk(K), i, w, l), U32.to_nat(U32.inc(CY.msk(K))), SC.pow2(K), PA.fuel_eq(one, h1, K, hK))
  +e2 = raw_impl(one, h1, K, hK, T, pt, SC.pow2(K), i, PA.home_lt(w, K), w, l)
  +e3 = Equal.cong(Maybe<&2, Nat>, Array<U32>, m => rput(AR.thaw(U32, T), m, w, l), ri(AR.slots(U32, T), SC.pow2(K), SC.pow2(K), UD.v(HS.bucket(w, CY.msk(K)))), Some{e}, ri_n(AR.slots(U32, T), kl, SC.pow2(K), N.succ_le_lt(0n, SC.pow2(K), N.pow2_pos(K)), UD.v(HS.bucket(w, CY.msk(K))), PA.home_lt(w, K), e, he, hz, hp))
  Equal.trans(Array<U32>, H.ins_raw(AR.thaw(U32, T), CY.msk(K), w, l), H.ins_go(SC.pow2(K), H.rstep(AR.thaw(U32, T), i), CY.msk(K), i, w, l), H.put_bucket(AR.thaw(U32, T), U32.from_nat(e), w, l), e1, Equal.trans(Array<U32>, H.ins_go(SC.pow2(K), H.rstep(AR.thaw(U32, T), i), CY.msk(K), i, w, l), rput(AR.thaw(U32, T), ri(AR.slots(U32, T), SC.pow2(K), SC.pow2(K), UD.v(HS.bucket(w, CY.msk(K)))), w, l), H.put_bucket(AR.thaw(U32, T), U32.from_nat(e), w, l), e2, e3))

# ---- an empty bucket on the path exists ----

def pno_home(+bs: List<&2, B.Bk>, +mask: U32, +key: String, +h: Nat, +n: Nat, +hno: {B.all_lt(B.PNo{bs, key}, n) == True{} : Bool}, +m: Nat, +hm: {Nat.is_le(m, n) == True{} : Bool}) -> {B.all_lt(B.PHome{bs, mask, key, h}, m) == True{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+q:
      +hq = N.succ_le_lt(q, n, hm)
      +nh = K2.not_true_eq(B.hold(key, B.at(bs, q)), B.all_inst(B.PNo{bs, key}, n, hno, q, hq))
      L.and_intro(B.eval(B.PHome{bs, mask, key, h}, q), B.all_lt(B.PHome{bs, mask, key, h}, q), L.subst(Bool, b => {B.implies(b, Nat.is_eq(B.hb(mask, B.at(bs, q)), h)) == True{} : Bool}, False{}, B.hold(key, B.at(bs, q)), Equal.sym(Bool, B.hold(key, B.at(bs, q)), False{}, nh), {==}), pno_home(bs, mask, key, h, n, hno, q, N.lt_le(q, n, hq)))

def FirstE(+bs: List<&2, B.Bk>, +n: Nat, +h: Nat) -> Type:
  Sigma<&1, &1, Nat, e => {Nat.is_lt(e, n) == True{} : Bool} & ({B.at(bs, e) == B.BE{} : B.Bk} & {B.occpath(bs, n, h, M.dist(n, h, e)) == True{} : Bool})>

def fe_r(+bs: List<&2, B.Bk>, +n: Nat, +h: Nat, +key: String, +hno: {B.all_lt(B.PNo{bs, key}, n) == True{} : Bool}, +r: B.Res, ok: B.ResOK(bs, n, h, key, r)) -> FirstE(bs, n, h):
  match r:
    case B.RHit{+i, +l}:
      (+hi, rest) = ok
      (+hk, hl) = rest
      Empty.absurd(FirstE(bs, n, h), L.false_true(L.subst(Bool, b => {Bool.not(b) == True{} : Bool}, B.hold(key, B.at(bs, i)), True{}, hk, B.all_inst(B.PNo{bs, key}, n, hno, i, hi))))
    case B.REnd{+e}:
      (he, rest) = ok
      (hz, rest2) = rest
      (hp, hn2) = rest2
      (e, (he, (hz, hp)))

def fe_0(+bs: List<&2, B.Bk>, +n: Nat, +hn: {Nat.is_lt(0n, n) == True{} : Bool}, +mask: U32, +key: String, +h: Nat, +hh: {Nat.is_lt(h, n) == True{} : Bool}, +cl: {B.cluster(bs, n, mask) == True{} : Bool}, +hno: {B.all_lt(B.PNo{bs, key}, n) == True{} : Bool}, e0: IV.Empty0(bs, n)) -> FirstE(bs, n, h):
  match e0:
    case Tuple{+j, Tuple{+hj, +hzj}}:
      fe_r(bs, n, h, key, hno, B.pf(key, bs, n, n, B.mstep(key, B.at(bs, h)), h), IV.pf_ok_n(bs, n, hn, mask, key, h, hh, cl, pno_home(bs, mask, key, h, n, hno, n, N.le_refl(n)), j, hj, hzj))

# THEOREM: in a table with a free bucket, a key held nowhere has an empty
# bucket on its path, every bucket before it on the path full
def find_e(+bs: List<&2, B.Bk>, +n: Nat, +hn: {Nat.is_lt(0n, n) == True{} : Bool}, +mask: U32, +key: String, +h: Nat, +hh: {Nat.is_lt(h, n) == True{} : Bool}, +cl: {B.cluster(bs, n, mask) == True{} : Bool}, +hno: {B.all_lt(B.PNo{bs, key}, n) == True{} : Bool}, +hem: {Nat.is_lt(IV.occn(bs, n), n) == True{} : Bool}) -> FirstE(bs, n, h):
  fe_0(bs, n, hn, mask, key, h, hh, cl, hno, IV.find_empty(bs, n, hem))
