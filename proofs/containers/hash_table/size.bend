import Base
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../../lib/list.bend as LL
import ../../lib/array.bend as AR
import ../../../spec/lib/common.bend as SC
import ../../../spec/containers/hash_table.bend as S
import ../../lib/u32div.bend as UD
import ../../../src/containers/hash_table.bend as H
import ./table.bend as TB
import ./buckets.bend as B
import ./inv.bend as IV
import ./state.bend as ST

# size: the stored count is the number of entries of the model.

def size_app(~V: Data, +a: List<&2, S.Entry<V>>, +b: List<&2, S.Entry<V>>) -> {S.size(~V, SC.append(S.Entry<V>, a, b)) == Nat.add(S.size(~V, a), S.size(~V, b)) : Nat}:
  match a:
    case Nil{}:
      {==}
    case Con{e, t}:
      N.succ_cong(S.size(~V, SC.append(S.Entry<V>, t, b)), Nat.add(S.size(~V, t), S.size(~V, b)), size_app(~V, t, b))

def absm_snoc(~V: Data, +bs: List<&2, B.Bk>, +vsl: List<&2, Maybe<&2, V>>, +q: Nat, +j: Nat) -> {ST.absm(~V, bs, vsl, 1n+q, j) == SC.append(S.Entry<V>, ST.absm(~V, bs, vsl, q, j), ST.ent(~V, B.at(bs, Nat.add(j, q)), vsl)) : List<&2, S.Entry<V>>}:
  match q:
    case 0n:
      +e = ST.ent(~V, B.at(bs, j), vsl)
      Equal.trans(List<&2, S.Entry<V>>, SC.append(S.Entry<V>, e, Nil{}), e, ST.ent(~V, B.at(bs, Nat.add(j, 0n)), vsl), LL.append_nil(S.Entry<V>, e), Equal.cong(Nat, List<&2, S.Entry<V>>, z => ST.ent(~V, B.at(bs, z), vsl), j, Nat.add(j, 0n), Equal.sym(Nat, Nat.add(j, 0n), j, N.add_zero(j))))
    case 1n+p:
      +e = ST.ent(~V, B.at(bs, j), vsl)
      +last = ST.ent(~V, B.at(bs, Nat.add(1n+j, p)), vsl)
      Equal.trans(List<&2, S.Entry<V>>, SC.append(S.Entry<V>, e, ST.absm(~V, bs, vsl, 1n+p, 1n+j)), SC.append(S.Entry<V>, e, SC.append(S.Entry<V>, ST.absm(~V, bs, vsl, p, 1n+j), last)), SC.append(S.Entry<V>, ST.absm(~V, bs, vsl, 1n+p, j), ST.ent(~V, B.at(bs, Nat.add(j, 1n+p)), vsl)),
        Equal.cong(List<&2, S.Entry<V>>, List<&2, S.Entry<V>>, z => SC.append(S.Entry<V>, e, z), ST.absm(~V, bs, vsl, 1n+p, 1n+j), SC.append(S.Entry<V>, ST.absm(~V, bs, vsl, p, 1n+j), last), absm_snoc(~V, bs, vsl, p, 1n+j)),
        Equal.trans(List<&2, S.Entry<V>>, SC.append(S.Entry<V>, e, SC.append(S.Entry<V>, ST.absm(~V, bs, vsl, p, 1n+j), last)), SC.append(S.Entry<V>, SC.append(S.Entry<V>, e, ST.absm(~V, bs, vsl, p, 1n+j)), last), SC.append(S.Entry<V>, ST.absm(~V, bs, vsl, 1n+p, j), ST.ent(~V, B.at(bs, Nat.add(j, 1n+p)), vsl)),
          Equal.sym(List<&2, S.Entry<V>>, SC.append(S.Entry<V>, SC.append(S.Entry<V>, e, ST.absm(~V, bs, vsl, p, 1n+j)), last), SC.append(S.Entry<V>, e, SC.append(S.Entry<V>, ST.absm(~V, bs, vsl, p, 1n+j), last)), LL.append_assoc(S.Entry<V>, e, ST.absm(~V, bs, vsl, p, 1n+j), last)),
          Equal.cong(Nat, List<&2, S.Entry<V>>, z => SC.append(S.Entry<V>, ST.absm(~V, bs, vsl, 1n+p, j), ST.ent(~V, B.at(bs, z), vsl)), Nat.add(1n+j, p), Nat.add(j, 1n+p), Equal.sym(Nat, Nat.add(j, 1n+p), 1n+Nat.add(j, p), N.add_succ(j, p)))))

def size_m(~V: Data, +k: String, +m: Maybe<&2, V>, +h: {ST.some_b(~V, m) == True{} : Bool}) -> {S.size(~V, ST.ent_m(~V, k, m)) == 1n : Nat}:
  match m:
    case None{}:
      Empty.absurd({S.size(~V, ST.ent_m(~V, k, None{})) == 1n : Nat}, L.false_true(h))
    case Some{v}:
      {==}

# a live bucket has one entry, an empty bucket none
def size_ent(~V: Data, +b: B.Bk, +vsl: List<&2, Maybe<&2, V>>, +fr: Nat, +hl: {B.live_b(ST.lvs(~V, vsl), fr, b) == True{} : Bool}) -> {S.size(~V, ST.ent(~V, b, vsl)) == IV.bitv(B.occ(b)) : Nat}:
  match b:
    case B.BE{}:
      {==}
    case B.BF{w, +l, +k}:
      +hn = L.and_left(B.nthb(ST.lvs(~V, vsl), UD.v(H.slot(l))), Nat.is_lt(UD.v(H.slot(l)), fr), hl)
      size_m(~V, k, ST.nthm(~V, vsl, UD.v(H.slot(l))), Equal.trans(Bool, ST.some_b(~V, ST.nthm(~V, vsl, UD.v(H.slot(l)))), B.nthb(ST.lvs(~V, vsl), UD.v(H.slot(l))), True{}, Equal.sym(Bool, B.nthb(ST.lvs(~V, vsl), UD.v(H.slot(l))), ST.some_b(~V, ST.nthm(~V, vsl, UD.v(H.slot(l)))), ST.lvs_nth(~V, vsl, UD.v(H.slot(l)))), hn))

# the number of entries is the number of full buckets
def size_absm(~V: Data, +bs: List<&2, B.Bk>, +vsl: List<&2, Maybe<&2, V>>, +fr: Nat, +n: Nat, +hl: {B.all_lt(B.PLive{bs, ST.lvs(~V, vsl), fr}, n) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, n) == True{} : Bool}) -> {S.size(~V, ST.absm(~V, bs, vsl, q, 0n)) == IV.occn(bs, q) : Nat}:
  match q:
    case 0n:
      {==}
    case 1n+p:
      +hp = N.succ_le_lt(p, n, hq)
      +e1 = Equal.cong(List<&2, S.Entry<V>>, Nat, z => S.size(~V, z), ST.absm(~V, bs, vsl, 1n+p, 0n), SC.append(S.Entry<V>, ST.absm(~V, bs, vsl, p, 0n), ST.ent(~V, B.at(bs, p), vsl)), absm_snoc(~V, bs, vsl, p, 0n))
      +e2 = size_app(~V, ST.absm(~V, bs, vsl, p, 0n), ST.ent(~V, B.at(bs, p), vsl))
      +e3 = Equal.cong(Nat, Nat, z => Nat.add(z, S.size(~V, ST.ent(~V, B.at(bs, p), vsl))), S.size(~V, ST.absm(~V, bs, vsl, p, 0n)), IV.occn(bs, p), size_absm(~V, bs, vsl, fr, n, hl, p, N.lt_le(p, n, hp)))
      +e4 = Equal.cong(Nat, Nat, z => Nat.add(IV.occn(bs, p), z), S.size(~V, ST.ent(~V, B.at(bs, p), vsl)), IV.bitv(B.occ(B.at(bs, p))), size_ent(~V, B.at(bs, p), vsl, fr, B.all_inst(B.PLive{bs, ST.lvs(~V, vsl), fr}, n, hl, p, hp)))
      Equal.trans(Nat, S.size(~V, ST.absm(~V, bs, vsl, 1n+p, 0n)), Nat.add(IV.occn(bs, p), IV.bitv(B.occ(B.at(bs, p)))), IV.occn(bs, 1n+p), Equal.trans(Nat, S.size(~V, ST.absm(~V, bs, vsl, 1n+p, 0n)), Nat.add(S.size(~V, ST.absm(~V, bs, vsl, p, 0n)), S.size(~V, ST.ent(~V, B.at(bs, p), vsl))), Nat.add(IV.occn(bs, p), IV.bitv(B.occ(B.at(bs, p)))), Equal.trans(Nat, S.size(~V, ST.absm(~V, bs, vsl, 1n+p, 0n)), S.size(~V, SC.append(S.Entry<V>, ST.absm(~V, bs, vsl, p, 0n), ST.ent(~V, B.at(bs, p), vsl))), Nat.add(S.size(~V, ST.absm(~V, bs, vsl, p, 0n)), S.size(~V, ST.ent(~V, B.at(bs, p), vsl))), e1, e2), Equal.trans(Nat, Nat.add(S.size(~V, ST.absm(~V, bs, vsl, p, 0n)), S.size(~V, ST.ent(~V, B.at(bs, p), vsl))), Nat.add(IV.occn(bs, p), S.size(~V, ST.ent(~V, B.at(bs, p), vsl))), Nat.add(IV.occn(bs, p), IV.bitv(B.occ(B.at(bs, p)))), e3, e4)), N.add_comm(IV.occn(bs, p), IV.bitv(B.occ(B.at(bs, p)))))

# THEOREM: size hands back the map unchanged and the model's size.
def size_ok(~V: Data, +sh: ST.Sh<V>, +hg: {ST.good(~V, sh) == True{} : Bool}) -> {H.size(&2, V, ST.real(~V, sh)) == (ST.real(~V, sh), Pair.snd(H.HashMap<&2, V>, U32, H.size(&2, V, ST.real(~V, sh)))) : H.HashMap<&2, V> & U32} & {UD.v(Pair.snd(H.HashMap<&2, V>, U32, H.size(&2, V, ST.real(~V, sh)))) == S.size(~V, ST.model(~V, sh)) : Nat}:
  match sh:
    case ST.HS{+n, +k, +td, +fresh, +sz, +sd, +sdU, +free, +tabT, +ksT, +vsT, +nxT}:
      +kl = AR.slots(String, ksT)
      +pk = AR.perfect(String, sd, ksT)
      +bs = TB.buckets(AR.slots(U32, tabT), kl, SC.pow2(k))
      +vsl = AR.slots(Maybe<&2, V>, vsT)
      +cn = N.eq_from_is_eq(UD.v(n), IV.occn(bs, SC.pow2(k)), ST.g_cn(~V, n, k, td, fresh, sz, sd, sdU, free, tabT, kl, pk, vsT, nxT, hg))
      +sa = size_absm(~V, bs, vsl, UD.v(fresh), SC.pow2(k), ST.g_clive(~V, n, k, td, fresh, sz, sd, sdU, free, tabT, kl, pk, vsT, nxT, hg), SC.pow2(k), N.le_refl(SC.pow2(k)))
      ({==}, Equal.trans(Nat, UD.v(n), IV.occn(bs, SC.pow2(k)), S.size(~V, ST.absm(~V, bs, vsl, SC.pow2(k), 0n)), cn, Equal.sym(Nat, S.size(~V, ST.absm(~V, bs, vsl, SC.pow2(k), 0n)), IV.occn(bs, SC.pow2(k)), sa)))
