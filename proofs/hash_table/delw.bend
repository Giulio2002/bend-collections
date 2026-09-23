import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/array.bend as AR
import ../spec/common.bend as SC
import ../math/u32div.bend as UD
import ../../src/containers/hash_table.bend as H
import ./table.bend as TB
import ./buckets.bend as B
import ./cyc.bend as CY
import ./inv.bend as IV
import ./insm.bend as IM
import ./grow.bend as GR
import ./shift.bend as SH

# del_at, stated over the table's 2^k buckets.


def dfin2(+kl: List<&2, String>, +k: Nat, +V0: List<&2, B.Bk>, +Tf: AR.Tree<U32>) -> Bool:
  Bool.and(AR.perfect(U32, 1n+k, Tf), Bool.and(B.cluster(TB.buckets(AR.slots(U32, Tf), kl, SC.pow2(k)), SC.pow2(k), CY.msk(k)), Bool.and(B.all_lt(B.PUniq{TB.buckets(AR.slots(U32, Tf), kl, SC.pow2(k))}, SC.pow2(k)), Bool.and(B.all_lt(B.PFrom{TB.buckets(AR.slots(U32, Tf), kl, SC.pow2(k)), V0, SC.pow2(k)}, SC.pow2(k)), Bool.and(B.all_lt(B.PTo{V0, TB.buckets(AR.slots(U32, Tf), kl, SC.pow2(k)), SC.pow2(k)}, SC.pow2(k)), Nat.is_eq(IV.occn(TB.buckets(AR.slots(U32, Tf), kl, SC.pow2(k)), SC.pow2(k)), IV.occn(V0, SC.pow2(k))))))))

def DelAt2(+kl: List<&2, String>, +k: Nat, +OT: AR.Tree<U32>, +i: Nat) -> Type:
  Sigma<&1, &1, AR.Tree<U32>, Tf => {H.del_at(AR.thaw(U32, OT), CY.msk(k), U32.from_nat(i)) == AR.thaw(U32, Tf) : Array<U32>} & {dfin2(kl, k, IM.bupd(TB.buckets(AR.slots(U32, OT), kl, SC.pow2(k)), i, B.BE{}), Tf) == True{} : Bool}>

def hN(+k: Nat, +hk: {Nat.is_lt(k, 31n) == True{} : Bool}) -> {1n+UD.v(CY.msk(k)) == SC.pow2(k) : Nat}:
  Equal.trans(Nat, 1n+UD.v(CY.msk(k)), Nat.add(UD.v(CY.msk(k)), 1n), SC.pow2(k), N.add_comm(1n, UD.v(CY.msk(k))), GR.mskv(k, N.lt_le(k, 32n, N.lt_trans(k, 31n, 32n, hk, {==}))))


def d2_fin(+kl: List<&2, String>, +k: Nat, +hk31: {Nat.is_lt(k, 31n) == True{} : Bool}, +OT: AR.Tree<U32>, +i: Nat, d: SH.DelAt(kl, k, UD.v(CY.msk(k)), OT, i)) -> DelAt2(kl, k, OT, i):
  match d:
    case Tuple{+Tf, Tuple{+e1, +hd}}:
      +g1 = SH.f1(kl, k, UD.v(CY.msk(k)), IM.bupd(TB.buckets(AR.slots(U32, OT), kl, 1n+UD.v(CY.msk(k))), i, B.BE{}), Tf, hd)
      +g2 = L.subst(Nat, z => {B.cluster(TB.buckets(AR.slots(U32, Tf), kl, z), z, CY.msk(k)) == True{} : Bool} , 1n+UD.v(CY.msk(k)), SC.pow2(k), hN(k, hk31), SH.f2(kl, k, UD.v(CY.msk(k)), IM.bupd(TB.buckets(AR.slots(U32, OT), kl, 1n+UD.v(CY.msk(k))), i, B.BE{}), Tf, hd))
      +g3 = L.subst(Nat, z => {B.all_lt(B.PUniq{TB.buckets(AR.slots(U32, Tf), kl, z)}, z) == True{} : Bool} , 1n+UD.v(CY.msk(k)), SC.pow2(k), hN(k, hk31), SH.f3(kl, k, UD.v(CY.msk(k)), IM.bupd(TB.buckets(AR.slots(U32, OT), kl, 1n+UD.v(CY.msk(k))), i, B.BE{}), Tf, hd))
      +g4 = L.subst(Nat, z => {B.all_lt(B.PFrom{TB.buckets(AR.slots(U32, Tf), kl, z), IM.bupd(TB.buckets(AR.slots(U32, OT), kl, z), i, B.BE{}), z}, z) == True{} : Bool} , 1n+UD.v(CY.msk(k)), SC.pow2(k), hN(k, hk31), SH.f4(kl, k, UD.v(CY.msk(k)), IM.bupd(TB.buckets(AR.slots(U32, OT), kl, 1n+UD.v(CY.msk(k))), i, B.BE{}), Tf, hd))
      +g5 = L.subst(Nat, z => {B.all_lt(B.PTo{IM.bupd(TB.buckets(AR.slots(U32, OT), kl, z), i, B.BE{}), TB.buckets(AR.slots(U32, Tf), kl, z), z}, z) == True{} : Bool} , 1n+UD.v(CY.msk(k)), SC.pow2(k), hN(k, hk31), SH.f5(kl, k, UD.v(CY.msk(k)), IM.bupd(TB.buckets(AR.slots(U32, OT), kl, 1n+UD.v(CY.msk(k))), i, B.BE{}), Tf, hd))
      +g6 = L.subst(Nat, z => {Nat.is_eq(IV.occn(TB.buckets(AR.slots(U32, Tf), kl, z), z), IV.occn(IM.bupd(TB.buckets(AR.slots(U32, OT), kl, z), i, B.BE{}), z)) == True{} : Bool} , 1n+UD.v(CY.msk(k)), SC.pow2(k), hN(k, hk31), SH.f6(kl, k, UD.v(CY.msk(k)), IM.bupd(TB.buckets(AR.slots(U32, OT), kl, 1n+UD.v(CY.msk(k))), i, B.BE{}), Tf, hd))
      (Tf, (e1, L.and_intro(AR.perfect(U32, 1n+k, Tf), Bool.and(B.cluster(TB.buckets(AR.slots(U32, Tf), kl, SC.pow2(k)), SC.pow2(k), CY.msk(k)), Bool.and(B.all_lt(B.PUniq{TB.buckets(AR.slots(U32, Tf), kl, SC.pow2(k))}, SC.pow2(k)), Bool.and(B.all_lt(B.PFrom{TB.buckets(AR.slots(U32, Tf), kl, SC.pow2(k)), IM.bupd(TB.buckets(AR.slots(U32, OT), kl, SC.pow2(k)), i, B.BE{}), SC.pow2(k)}, SC.pow2(k)), Bool.and(B.all_lt(B.PTo{IM.bupd(TB.buckets(AR.slots(U32, OT), kl, SC.pow2(k)), i, B.BE{}), TB.buckets(AR.slots(U32, Tf), kl, SC.pow2(k)), SC.pow2(k)}, SC.pow2(k)), Nat.is_eq(IV.occn(TB.buckets(AR.slots(U32, Tf), kl, SC.pow2(k)), SC.pow2(k)), IV.occn(IM.bupd(TB.buckets(AR.slots(U32, OT), kl, SC.pow2(k)), i, B.BE{}), SC.pow2(k))))))), g1, L.and_intro(B.cluster(TB.buckets(AR.slots(U32, Tf), kl, SC.pow2(k)), SC.pow2(k), CY.msk(k)), Bool.and(B.all_lt(B.PUniq{TB.buckets(AR.slots(U32, Tf), kl, SC.pow2(k))}, SC.pow2(k)), Bool.and(B.all_lt(B.PFrom{TB.buckets(AR.slots(U32, Tf), kl, SC.pow2(k)), IM.bupd(TB.buckets(AR.slots(U32, OT), kl, SC.pow2(k)), i, B.BE{}), SC.pow2(k)}, SC.pow2(k)), Bool.and(B.all_lt(B.PTo{IM.bupd(TB.buckets(AR.slots(U32, OT), kl, SC.pow2(k)), i, B.BE{}), TB.buckets(AR.slots(U32, Tf), kl, SC.pow2(k)), SC.pow2(k)}, SC.pow2(k)), Nat.is_eq(IV.occn(TB.buckets(AR.slots(U32, Tf), kl, SC.pow2(k)), SC.pow2(k)), IV.occn(IM.bupd(TB.buckets(AR.slots(U32, OT), kl, SC.pow2(k)), i, B.BE{}), SC.pow2(k)))))), g2, L.and_intro(B.all_lt(B.PUniq{TB.buckets(AR.slots(U32, Tf), kl, SC.pow2(k))}, SC.pow2(k)), Bool.and(B.all_lt(B.PFrom{TB.buckets(AR.slots(U32, Tf), kl, SC.pow2(k)), IM.bupd(TB.buckets(AR.slots(U32, OT), kl, SC.pow2(k)), i, B.BE{}), SC.pow2(k)}, SC.pow2(k)), Bool.and(B.all_lt(B.PTo{IM.bupd(TB.buckets(AR.slots(U32, OT), kl, SC.pow2(k)), i, B.BE{}), TB.buckets(AR.slots(U32, Tf), kl, SC.pow2(k)), SC.pow2(k)}, SC.pow2(k)), Nat.is_eq(IV.occn(TB.buckets(AR.slots(U32, Tf), kl, SC.pow2(k)), SC.pow2(k)), IV.occn(IM.bupd(TB.buckets(AR.slots(U32, OT), kl, SC.pow2(k)), i, B.BE{}), SC.pow2(k))))), g3, L.and_intro(B.all_lt(B.PFrom{TB.buckets(AR.slots(U32, Tf), kl, SC.pow2(k)), IM.bupd(TB.buckets(AR.slots(U32, OT), kl, SC.pow2(k)), i, B.BE{}), SC.pow2(k)}, SC.pow2(k)), Bool.and(B.all_lt(B.PTo{IM.bupd(TB.buckets(AR.slots(U32, OT), kl, SC.pow2(k)), i, B.BE{}), TB.buckets(AR.slots(U32, Tf), kl, SC.pow2(k)), SC.pow2(k)}, SC.pow2(k)), Nat.is_eq(IV.occn(TB.buckets(AR.slots(U32, Tf), kl, SC.pow2(k)), SC.pow2(k)), IV.occn(IM.bupd(TB.buckets(AR.slots(U32, OT), kl, SC.pow2(k)), i, B.BE{}), SC.pow2(k)))), g4, L.and_intro(B.all_lt(B.PTo{IM.bupd(TB.buckets(AR.slots(U32, OT), kl, SC.pow2(k)), i, B.BE{}), TB.buckets(AR.slots(U32, Tf), kl, SC.pow2(k)), SC.pow2(k)}, SC.pow2(k)), Nat.is_eq(IV.occn(TB.buckets(AR.slots(U32, Tf), kl, SC.pow2(k)), SC.pow2(k)), IV.occn(IM.bupd(TB.buckets(AR.slots(U32, OT), kl, SC.pow2(k)), i, B.BE{}), SC.pow2(k))), g5, g6)))))))


# THEOREM: deleting a full bucket of a good table (2^k buckets, a free one)
def del_ok2(+k: Nat, +hk31: {Nat.is_lt(k, 31n) == True{} : Bool}, +kl: List<&2, String>, +OT: AR.Tree<U32>, +pot: {AR.perfect(U32, 1n+k, OT) == True{} : Bool}, +i: Nat, +hi: {Nat.is_lt(i, SC.pow2(k)) == True{} : Bool}, +cl: {B.cluster(TB.buckets(AR.slots(U32, OT), kl, SC.pow2(k)), SC.pow2(k), CY.msk(k)) == True{} : Bool}, +huo: {B.all_lt(B.PUniq{TB.buckets(AR.slots(U32, OT), kl, SC.pow2(k))}, SC.pow2(k)) == True{} : Bool}, +hoi: {B.occ(B.at(TB.buckets(AR.slots(U32, OT), kl, SC.pow2(k)), i)) == True{} : Bool}, +hem: {Nat.is_lt(IV.occn(TB.buckets(AR.slots(U32, OT), kl, SC.pow2(k)), SC.pow2(k)), SC.pow2(k)) == True{} : Bool}) -> DelAt2(kl, k, OT, i):
  +hi2 = L.subst(Nat, z => {Nat.is_lt(i, z) == True{} : Bool} , SC.pow2(k), 1n+UD.v(CY.msk(k)), Equal.sym(Nat, 1n+UD.v(CY.msk(k)), SC.pow2(k), hN(k, hk31)), hi)
  +cl2 = L.subst(Nat, z => {B.cluster(TB.buckets(AR.slots(U32, OT), kl, z), z, CY.msk(k)) == True{} : Bool} , SC.pow2(k), 1n+UD.v(CY.msk(k)), Equal.sym(Nat, 1n+UD.v(CY.msk(k)), SC.pow2(k), hN(k, hk31)), cl)
  +hu2 = L.subst(Nat, z => {B.all_lt(B.PUniq{TB.buckets(AR.slots(U32, OT), kl, z)}, z) == True{} : Bool} , SC.pow2(k), 1n+UD.v(CY.msk(k)), Equal.sym(Nat, 1n+UD.v(CY.msk(k)), SC.pow2(k), hN(k, hk31)), huo)
  +ho2 = L.subst(Nat, z => {B.occ(B.at(TB.buckets(AR.slots(U32, OT), kl, z), i)) == True{} : Bool} , SC.pow2(k), 1n+UD.v(CY.msk(k)), Equal.sym(Nat, 1n+UD.v(CY.msk(k)), SC.pow2(k), hN(k, hk31)), hoi)
  +he2 = L.subst(Nat, z => {Nat.is_lt(IV.occn(TB.buckets(AR.slots(U32, OT), kl, z), z), z) == True{} : Bool} , SC.pow2(k), 1n+UD.v(CY.msk(k)), Equal.sym(Nat, 1n+UD.v(CY.msk(k)), SC.pow2(k), hN(k, hk31)), hem)
  d2_fin(kl, k, hk31, OT, i, SH.del_ok(1n, {==}, k, hk31, UD.v(CY.msk(k)), hN(k, hk31), kl, OT, pot, i, hi2, cl2, hu2, ho2, he2))
