import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/array.bend as AR
import ../lib/u32.bend as U
import ../../spec/common.bend as SC
import ../../spec/lru_fast.bend as S
import ../../spec/lru_numeric.bend as NS
import ../../src/lru/fast.bend as F
import ../../src/lru/time.bend as Time
import ../../src/doubly_linked_list.bend as D
import ../../types/lru_model.bend as T
import ../../types/lru_fast.bend as E
import ../dlist/state.bend as DST
import ../dlist/split.bend as SP
import ../dlist/tolist.bend as TL
import ../dlist/core.bend as K
import ../dlist/alive.bend as AL
import ../dlist/facts.bend as DF
import ../dlist/links.bend as LK
import ../dlist/tset.bend as TS
import ../dlist/items.bend as IT
import ./state.bend as ST
import ./table.bend as TB
import ./ents.bend as EN
import ./rs.bend as RS
import ./remove.bend as RM
import ./read.bend as RD
import ./readfacts.bend as RF
import ./addop.bend as AO
import ./resize.bend as RZ
import ./kwalk.bend as KW

# keys(now): the expired oldest prefix is removed (each a removal; at most
# len(order) rounds), then the keys are walked from the tail, oldest first.

# ---- the ghost expiry loop ----

def ev2(-V: Data, sh: ST.Shadow<V>) -> ST.Shadow<V>:
  match sh:
    case ST.Sh{+cap, +fresh, +depth, +life, +tc, +table, +tk, +te, +tp, +tn, +ord, +fl}:
      RM.rs_sh_at(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, AO.hd_nat(ord), fl, 2n)

def st_exp(-V: Data, sh: ST.Shadow<V>, r: ST.Shadow<V>, expired: Bool) -> ST.Shadow<V>:
  match expired:
    case False{}:
      sh
    case True{}:
      r

def st_slot(-V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +now: T.Int64, r: ST.Shadow<V>, e: F.Slot<V>) -> ST.Shadow<V>:
  match e:
    case F.Vacant{}:
      ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}
    case F.Live{v}:
      ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}
    case F.Timed{v, d}:
      st_exp(V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}, r, NS.expired(F.stamp_int(d), now))

def st_ord(-V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, ord: List<&2, Nat>, +fl: List<&2, Nat>, +now: T.Int64, r: ST.Shadow<V>) -> ST.Shadow<V>:
  match ord:
    case Nil{}:
      ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, Nil{}, fl}
    case Con{+s0, +rest}:
      st_slot(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl, now, r, ST.sat(V, AR.slots(F.Slot<V>, te), s0))

def st_dec(-V: Data, sh: ST.Shadow<V>, +now: T.Int64, r: ST.Shadow<V>) -> ST.Shadow<V>:
  match sh:
    case ST.Sh{+cap, +fresh, +depth, +life, +tc, +table, +tk, +te, +tp, +tn, ord, +fl}:
      st_ord(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, now, r)

def st_g(-V: Data, fuel: Nat, +sh: ST.Shadow<V>, +now: T.Int64) -> ST.Shadow<V>:
  match fuel:
    case 0n:
      sh
    case 1n+p:
      st_dec(V, sh, now, st_g(V, p, ev2(V, sh), now))

# ---- the runtime ----

def exp_false(~V: Data, p: Nat, +now: F.Stamp, f: F.Fast<V>) -> {F.exp_go(~V, p, now, (f, False{})) == f : F.Fast<V>}:
  match p:
    case 0n:
      {==}
    case 1n+q:
      {==}

def ex_con(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +s0: Nat, +rest: List<&2, Nat>, +fl: List<&2, Nat>, +now: F.Stamp, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl) == True{} : Bool}) -> {F.ex_head(~V, ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl}), now) == F.ex_slot(~V, ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl}), U32.from_nat(s0), now, ST.sat(V, AR.slots(F.Slot<V>, te), s0)) : F.Fast<V> & Bool}:
  +es = AR.slots(F.Slot<V>, te)
  +hd = ST.g_depth(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl, h)
  +hs0 = N.lt_le_trans(s0, fresh, SC.pow2(depth), L.and_left(Nat.is_lt(s0, fresh), DST.alllt(rest, fresh), ST.g_ordlt(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl, h)), ST.g_fresh(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl, h))
  +sv = L.some_value(F.Slot<V>, SC.nth(F.Slot<V>, es, s0), F.Vacant{})
  +r3 = Equal.trans(F.Fast<V> & Bool, F.ex_got(~V, cap, U32.from_nat(SC.length(Nat, Con{s0, rest})), U32.from_nat(fresh), U.pow2u(depth), depth, Bool.not(Time.is_zero(life)), F.int_stamp(life), AR.thaw(U32, tc), table, AR.thaw(String, tk), F.CH{DST.ln(s0), DST.lst(Con{s0, rest}), DST.hd(fl), AR.thaw(U32, tp), AR.thaw(U32, tn)}, U32.from_nat(s0), now, Array.get(F.Slot<V>, AR.thaw(F.Slot<V>, te), U32.from_nat(s0))), F.ex_slot(~V, ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl}), U32.from_nat(s0), now, sv), F.ex_slot(~V, ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl}), U32.from_nat(s0), now, ST.sat(V, es, s0)),
    Equal.cong(Array<F.Slot<V>> & F.Slot<V>, F.Fast<V> & Bool, r => F.ex_got(~V, cap, U32.from_nat(SC.length(Nat, Con{s0, rest})), U32.from_nat(fresh), U.pow2u(depth), depth, Bool.not(Time.is_zero(life)), F.int_stamp(life), AR.thaw(U32, tc), table, AR.thaw(String, tk), F.CH{DST.ln(s0), DST.lst(Con{s0, rest}), DST.hd(fl), AR.thaw(U32, tp), AR.thaw(U32, tn)}, U32.from_nat(s0), now, r), Array.get(F.Slot<V>, AR.thaw(F.Slot<V>, te), U32.from_nat(s0)), (AR.thaw(F.Slot<V>, te), sv), TL.get_at(F.Slot<V>, depth, te, s0, F.Vacant{}, hd, ST.g_te(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl, h), hs0)),
    Equal.cong(F.Slot<V>, F.Fast<V> & Bool, e => F.ex_slot(~V, ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl}), U32.from_nat(s0), now, e), sv, ST.sat(V, es, s0), RS.sat_sv(V, SC.nth(F.Slot<V>, es, s0))))
  +r2 = L.subst(U32, z => {F.ex_got(~V, cap, U32.from_nat(SC.length(Nat, Con{s0, rest})), U32.from_nat(fresh), U.pow2u(depth), depth, Bool.not(Time.is_zero(life)), F.int_stamp(life), AR.thaw(U32, tc), table, AR.thaw(String, tk), F.CH{DST.ln(s0), DST.lst(Con{s0, rest}), DST.hd(fl), AR.thaw(U32, tp), AR.thaw(U32, tn)}, z, now, Array.get(F.Slot<V>, AR.thaw(F.Slot<V>, te), z)) == F.ex_slot(~V, ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl}), U32.from_nat(s0), now, ST.sat(V, es, s0)) : F.Fast<V> & Bool}, U32.from_nat(s0), F.slot(DST.ln(s0)), Equal.sym(U32, F.slot(DST.ln(s0)), U32.from_nat(s0), DF.slot_ln(s0, depth, hd, hs0)), r3)
  L.subst(Bool, z => {F.ex_pick(~V, cap, U32.from_nat(SC.length(Nat, Con{s0, rest})), U32.from_nat(fresh), U.pow2u(depth), depth, Bool.not(Time.is_zero(life)), F.int_stamp(life), AR.thaw(U32, tc), table, AR.thaw(String, tk), AR.thaw(F.Slot<V>, te), F.CH{DST.ln(s0), DST.lst(Con{s0, rest}), DST.hd(fl), AR.thaw(U32, tp), AR.thaw(U32, tn)}, DST.ln(s0), now, z) == F.ex_slot(~V, ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl}), U32.from_nat(s0), now, ST.sat(V, es, s0)) : F.Fast<V> & Bool}, False{}, U32.is_eq(DST.ln(s0), F.nil()), Equal.sym(Bool, U32.is_eq(DST.ln(s0), F.nil()), False{}, DF.ln_ne_nil(s0, depth, hd, hs0)), r2)

def StIH(~V: Data, +p: Nat, +now: T.Int64) -> Type:
  @cap: U32 -> @fresh: Nat -> @depth: Nat -> @life: T.Int64 -> @tc: AR.Tree<U32> -> @table: Map<&2, Maybe<&2, U32>> -> @tk: AR.Tree<String> -> @te: AR.Tree<F.Slot<V>> -> @tp: AR.Tree<U32> -> @tn: AR.Tree<U32> -> @ord: List<&2, Nat> -> @fl: List<&2, Nat> -> @hl: {Nat.is_le(SC.length(Nat, ord), p) == True{} : Bool} -> @h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool} -> {F.exp_go(~V, p, F.int_stamp(now), (ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), True{})) == ST.real(~V, st_g(V, p, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}, now)) : F.Fast<V>}

def st_x(~V: Data, +p: Nat, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +s0: Nat, +rest: List<&2, Nat>, +fl: List<&2, Nat>, +now: T.Int64, expired: Bool, +hl: {Nat.is_le(SC.length(Nat, Con{s0, rest}), 1n+p) == True{} : Bool}, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl) == True{} : Bool}, ih: StIH(~V, p, now)) -> {F.exp_go(~V, p, F.int_stamp(now), F.ex_drop(~V, ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl}), U32.from_nat(s0), expired)) == ST.real(~V, st_exp(V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl}, st_g(V, p, ev2(V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl}), now), expired)) : F.Fast<V>}:
  match expired:
    case False{}:
      exp_false(~V, p, F.int_stamp(now), ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl}))
    case True{}:
      +hm = TB.or_true_l(Nat.is_eq(s0, s0), DST.lmem(s0, rest), AL.lmem_self(s0))
      +h2 = RM.rm_at_inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl, s0, 2n, hm, h)
      +hl2 = L.subst(Nat, z => {Nat.is_le(z, p) == True{} : Bool}, SC.length(Nat, rest), SC.length(Nat, SC.append(Nat, SP.spre(Con{s0, rest}, s0), SP.spost(Con{s0, rest}, s0))), Equal.sym(Nat, SC.length(Nat, SC.append(Nat, SP.spre(Con{s0, rest}, s0), SP.spost(Con{s0, rest}, s0))), SC.length(Nat, rest), RZ.hrm_len(s0, rest, hm)), hl)
      +e1 = Equal.cong(F.Fast<V> & Maybe<&2, V>, F.Fast<V>, q => F.exp_go(~V, p, F.int_stamp(now), (F.drop_val(~V, q), True{})), F.remove_slot(~V, ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl}), U32.from_nat(s0), 2n), (ST.real(~V, RM.rs_sh_at(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, s0, fl, 2n)), F.slot_val(~V, ST.sat(V, AR.slots(F.Slot<V>, te), s0))), RM.rm_at_real(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl, s0, 2n, hm, h))
      Equal.trans(F.Fast<V>, F.exp_go(~V, p, F.int_stamp(now), (F.drop_val(~V, F.remove_slot(~V, ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl}), U32.from_nat(s0), 2n)), True{})), F.exp_go(~V, p, F.int_stamp(now), (ST.real(~V, RM.rs_sh_at(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, s0, fl, 2n)), True{})), ST.real(~V, st_g(V, p, ev2(V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl}), now)),
        e1, ih(cap, fresh, depth, life, RS.sbd(tc, 2n), Map.del(&2, Maybe<&2, U32>, table, ST.kat(AR.slots(String, tk), s0)), tk, AR.upd(F.Slot<V>, depth, te, s0, F.Vacant{}), TS.tpup(depth, tp, SP.spost(Con{s0, rest}, s0), LK.lastl(SP.spre(Con{s0, rest}, s0), D.nil())), AR.upd(U32, depth, TS.tnup(depth, tn, SP.spre(Con{s0, rest}, s0), DST.hd_or(SP.spost(Con{s0, rest}, s0), D.nil())), s0, DST.hd(fl)), SC.append(Nat, SP.spre(Con{s0, rest}, s0), SP.spost(Con{s0, rest}, s0)), Con{s0, fl}, hl2, h2))

def st_e(~V: Data, +p: Nat, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +s0: Nat, +rest: List<&2, Nat>, +fl: List<&2, Nat>, +now: T.Int64, e: F.Slot<V>, +hl: {Nat.is_le(SC.length(Nat, Con{s0, rest}), 1n+p) == True{} : Bool}, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl) == True{} : Bool}, ih: StIH(~V, p, now)) -> {F.exp_go(~V, p, F.int_stamp(now), F.ex_slot(~V, ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl}), U32.from_nat(s0), F.int_stamp(now), e)) == ST.real(~V, st_slot(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl, now, st_g(V, p, ev2(V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl}), now), e)) : F.Fast<V>}:
  match e:
    case F.Vacant{}:
      exp_false(~V, p, F.int_stamp(now), ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl}))
    case F.Live{v}:
      exp_false(~V, p, F.int_stamp(now), ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl}))
    case F.Timed{v, +d}:
      L.subst(Bool, z => {F.exp_go(~V, p, F.int_stamp(now), F.ex_drop(~V, ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl}), U32.from_nat(s0), z)) == ST.real(~V, st_exp(V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl}, st_g(V, p, ev2(V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl}), now), NS.expired(F.stamp_int(d), now))) : F.Fast<V>}, NS.expired(F.stamp_int(d), now), Time.expired(F.stamp_int(d), F.stamp_int(F.int_stamp(now))), Equal.sym(Bool, Time.expired(F.stamp_int(d), F.stamp_int(F.int_stamp(now))), NS.expired(F.stamp_int(d), now), RD.exp_eq(d, now)),
        st_x(~V, p, cap, fresh, depth, life, tc, table, tk, te, tp, tn, s0, rest, fl, now, NS.expired(F.stamp_int(d), now), hl, h, ih))

def st_c(~V: Data, +p: Nat, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, ord: List<&2, Nat>, +fl: List<&2, Nat>, +now: T.Int64, +hl: {Nat.is_le(SC.length(Nat, ord), 1n+p) == True{} : Bool}, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}, ih: StIH(~V, p, now)) -> {F.exp_go(~V, p, F.int_stamp(now), F.ex_head(~V, ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), F.int_stamp(now))) == ST.real(~V, st_ord(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, now, st_g(V, p, ev2(V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), now))) : F.Fast<V>}:
  match ord:
    case Nil{}:
      exp_false(~V, p, F.int_stamp(now), ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, Nil{}, fl}))
    case Con{+s0, +rest}:
      Equal.trans(F.Fast<V>, F.exp_go(~V, p, F.int_stamp(now), F.ex_head(~V, ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl}), F.int_stamp(now))), F.exp_go(~V, p, F.int_stamp(now), F.ex_slot(~V, ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl}), U32.from_nat(s0), F.int_stamp(now), ST.sat(V, AR.slots(F.Slot<V>, te), s0))), ST.real(~V, st_ord(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl, now, st_g(V, p, ev2(V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl}), now))),
        Equal.cong(F.Fast<V> & Bool, F.Fast<V>, r => F.exp_go(~V, p, F.int_stamp(now), r), F.ex_head(~V, ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl}), F.int_stamp(now)), F.ex_slot(~V, ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl}), U32.from_nat(s0), F.int_stamp(now), ST.sat(V, AR.slots(F.Slot<V>, te), s0)), ex_con(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, s0, rest, fl, F.int_stamp(now), h)),
        st_e(~V, p, cap, fresh, depth, life, tc, table, tk, te, tp, tn, s0, rest, fl, now, ST.sat(V, AR.slots(F.Slot<V>, te), s0), hl, h, ih))

def st_real(~V: Data, fuel: Nat, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +now: T.Int64, +hl: {Nat.is_le(SC.length(Nat, ord), fuel) == True{} : Bool}, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}) -> {F.exp_go(~V, fuel, F.int_stamp(now), (ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), True{})) == ST.real(~V, st_g(V, fuel, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}, now)) : F.Fast<V>}:
  match fuel:
    case 0n:
      {==}
    case 1n+ +p:
      st_c(~V, p, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, now, hl, h, a1 => a2 => a3 => a4 => a5 => a6 => a7 => a8 => a9 => a10 => a11 => a12 => a13 => a14 => st_real(~V, p, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, now, a13, a14))

# ---- the model of the expiry loop ----

def ents_of(-V: Data, sh: ST.Shadow<V>) -> List<&2, S.Ent<V>>:
  match sh:
    case ST.Sh{+cap, +fresh, +depth, +life, +tc, +table, +tk, +te, +tp, +tn, +ord, +fl}:
      ST.ents(V, AR.slots(String, tk), AR.slots(F.Slot<V>, te), ord)

def kobs(~V: Data, +sh: ST.Shadow<V>) -> S.Model<V> & E.Obs<V>:
  (ST.model(~V, sh), E.OKeys{S.keys(V, ents_of(V, sh))})

def StmIH(~V: Data, +p: Nat, +now: T.Int64) -> Type:
  @cap: U32 -> @fresh: Nat -> @depth: Nat -> @life: T.Int64 -> @tc: AR.Tree<U32> -> @table: Map<&2, Maybe<&2, U32>> -> @tk: AR.Tree<String> -> @te: AR.Tree<F.Slot<V>> -> @tp: AR.Tree<U32> -> @tn: AR.Tree<U32> -> @ord: List<&2, Nat> -> @fl: List<&2, Nat> -> @hl: {Nat.is_le(SC.length(Nat, ord), p) == True{} : Bool} -> @h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool} -> {S.keys_fin(V, cap, life, S.strip(V, ST.ents(V, AR.slots(String, tk), AR.slots(F.Slot<V>, te), ord), ST.mets(AR.slots(U32, tc)), now)) == kobs(~V, st_g(V, p, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}, now)) : S.Model<V> & E.Obs<V>}

# strip of an entry list headed by a live entry keeps everything
def keep_head(~V: Data, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +s0: Nat, +rest: List<&2, Nat>, +fl: List<&2, Nat>, +now: T.Int64, +x: S.Ent<V>, +hx: {ST.ents(V, AR.slots(String, tk), AR.slots(F.Slot<V>, te), Con{s0, rest}) == Con{x, ST.ents(V, AR.slots(String, tk), AR.slots(F.Slot<V>, te), rest)} : List<&2, S.Ent<V>>}) -> {S.keys_fin(V, cap, life, (Con{x, ST.ents(V, AR.slots(String, tk), AR.slots(F.Slot<V>, te), rest)}, ST.mets(AR.slots(U32, tc)))) == kobs(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl}) : S.Model<V> & E.Obs<V>}:
  +xs = ST.ents(V, AR.slots(String, tk), AR.slots(F.Slot<V>, te), Con{s0, rest})
  Equal.cong(List<&2, S.Ent<V>>, S.Model<V> & E.Obs<V>, z => (S.LM{cap, life, z, ST.mets(AR.slots(U32, tc))}, E.OKeys{S.keys(V, z)}), Con{x, ST.ents(V, AR.slots(String, tk), AR.slots(F.Slot<V>, te), rest)}, xs, Equal.sym(List<&2, S.Ent<V>>, xs, Con{x, ST.ents(V, AR.slots(String, tk), AR.slots(F.Slot<V>, te), rest)}, hx))

def stm_x(~V: Data, +p: Nat, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +s0: Nat, +rest: List<&2, Nat>, +fl: List<&2, Nat>, +now: T.Int64, +v: V, +d: T.Int64, +hx: {ST.ents(V, AR.slots(String, tk), AR.slots(F.Slot<V>, te), Con{s0, rest}) == Con{S.En{ST.kat(AR.slots(String, tk), s0), v, d}, ST.ents(V, AR.slots(String, tk), AR.slots(F.Slot<V>, te), rest)} : List<&2, S.Ent<V>>}, expired: Bool, +hl: {Nat.is_le(SC.length(Nat, Con{s0, rest}), 1n+p) == True{} : Bool}, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl) == True{} : Bool}, ih: StmIH(~V, p, now)) -> {S.keys_fin(V, cap, life, S.strip_at(V, S.En{ST.kat(AR.slots(String, tk), s0), v, d}, ST.ents(V, AR.slots(String, tk), AR.slots(F.Slot<V>, te), rest), ST.mets(AR.slots(U32, tc)), expired, S.strip(V, ST.ents(V, AR.slots(String, tk), AR.slots(F.Slot<V>, te), rest), T.bump(2n, ST.mets(AR.slots(U32, tc))), now))) == kobs(~V, st_exp(V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl}, st_g(V, p, ev2(V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl}), now), expired)) : S.Model<V> & E.Obs<V>}:
  match expired:
    case False{}:
      keep_head(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, s0, rest, fl, now, S.En{ST.kat(AR.slots(String, tk), s0), v, d}, hx)
    case True{}:
      +ks = AR.slots(String, tk)
      +es = AR.slots(F.Slot<V>, te)
      +er = ST.ents(V, ks, es, rest)
      +hm = TB.or_true_l(Nat.is_eq(s0, s0), DST.lmem(s0, rest), AL.lmem_self(s0))
      +h2 = RM.rm_at_inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl, s0, 2n, hm, h)
      +ab = SC.append(Nat, SP.spre(Con{s0, rest}, s0), SP.spost(Con{s0, rest}, s0))
      +hl2 = L.subst(Nat, z => {Nat.is_le(z, p) == True{} : Bool}, SC.length(Nat, rest), SC.length(Nat, ab), Equal.sym(Nat, SC.length(Nat, ab), SC.length(Nat, rest), RZ.hrm_len(s0, rest, hm)), hl)
      +E1 = ST.ents(V, ks, AR.slots(F.Slot<V>, AR.upd(F.Slot<V>, depth, te, s0, F.Vacant{})), ab)
      +M1 = ST.mets(AR.slots(U32, RS.sbd(tc, 2n)))
      +eE = Equal.trans(List<&2, S.Ent<V>>, E1, S.tail(V, ST.ents(V, ks, es, Con{s0, rest})), er, RZ.hrm_ents(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, s0, rest, fl, h), Equal.cong(List<&2, S.Ent<V>>, List<&2, S.Ent<V>>, z => S.tail(V, z), ST.ents(V, ks, es, Con{s0, rest}), Con{S.En{ST.kat(ks, s0), v, d}, er}, hx))
      +eM = RS.mets_drop(tc, 2n, ST.g_tc(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl, h))
      +e0 = Equal.trans(S.Model<V> & E.Obs<V>, S.keys_fin(V, cap, life, S.strip(V, er, T.bump(2n, ST.mets(AR.slots(U32, tc))), now)), S.keys_fin(V, cap, life, S.strip(V, E1, T.bump(2n, ST.mets(AR.slots(U32, tc))), now)), S.keys_fin(V, cap, life, S.strip(V, E1, M1, now)),
        Equal.cong(List<&2, S.Ent<V>>, S.Model<V> & E.Obs<V>, z => S.keys_fin(V, cap, life, S.strip(V, z, T.bump(2n, ST.mets(AR.slots(U32, tc))), now)), er, E1, Equal.sym(List<&2, S.Ent<V>>, E1, er, eE)),
        Equal.cong(T.Metrics, S.Model<V> & E.Obs<V>, z => S.keys_fin(V, cap, life, S.strip(V, E1, z, now)), T.bump(2n, ST.mets(AR.slots(U32, tc))), M1, Equal.sym(T.Metrics, M1, T.bump(2n, ST.mets(AR.slots(U32, tc))), eM)))
      Equal.trans(S.Model<V> & E.Obs<V>, S.keys_fin(V, cap, life, S.strip(V, er, T.bump(2n, ST.mets(AR.slots(U32, tc))), now)), S.keys_fin(V, cap, life, S.strip(V, E1, M1, now)), kobs(~V, st_g(V, p, ev2(V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl}), now)), e0, ih(cap, fresh, depth, life, RS.sbd(tc, 2n), Map.del(&2, Maybe<&2, U32>, table, ST.kat(AR.slots(String, tk), s0)), tk, AR.upd(F.Slot<V>, depth, te, s0, F.Vacant{}), TS.tpup(depth, tp, SP.spost(Con{s0, rest}, s0), LK.lastl(SP.spre(Con{s0, rest}, s0), D.nil())), AR.upd(U32, depth, TS.tnup(depth, tn, SP.spre(Con{s0, rest}, s0), DST.hd_or(SP.spost(Con{s0, rest}, s0), D.nil())), s0, DST.hd(fl)), SC.append(Nat, SP.spre(Con{s0, rest}, s0), SP.spost(Con{s0, rest}, s0)), Con{s0, fl}, hl2, h2))

def stm_e(~V: Data, +p: Nat, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +s0: Nat, +rest: List<&2, Nat>, +fl: List<&2, Nat>, +now: T.Int64, e: F.Slot<V>, +ee: {ST.sat(V, AR.slots(F.Slot<V>, te), s0) == e : F.Slot<V>}, +hl: {Nat.is_le(SC.length(Nat, Con{s0, rest}), 1n+p) == True{} : Bool}, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl) == True{} : Bool}, ih: StmIH(~V, p, now)) -> {S.keys_fin(V, cap, life, S.strip(V, ST.ents(V, AR.slots(String, tk), AR.slots(F.Slot<V>, te), Con{s0, rest}), ST.mets(AR.slots(U32, tc)), now)) == kobs(~V, st_slot(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl, now, st_g(V, p, ev2(V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl}), now), e)) : S.Model<V> & E.Obs<V>}:
  match e:
    case F.Vacant{}:
      +ks = AR.slots(String, tk)
      +es = AR.slots(F.Slot<V>, te)
      +ho = L.and_left(ST.is_occ(V, ST.sat(V, es, s0)), ST.all_occ(V, es, rest), ST.g_occ(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl, h))
      Empty.absurd({S.keys_fin(V, cap, life, S.strip(V, ST.ents(V, ks, es, Con{s0, rest}), ST.mets(AR.slots(U32, tc)), now)) == kobs(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl}) : S.Model<V> & E.Obs<V>}, L.false_true(L.subst(F.Slot<V>, z => {ST.is_occ(V, z) == True{} : Bool}, ST.sat(V, es, s0), F.Vacant{}, ee, ho)))
    case F.Live{+v}:
      +ks = AR.slots(String, tk)
      +es = AR.slots(F.Slot<V>, te)
      +er = ST.ents(V, ks, es, rest)
      +k0 = ST.kat(ks, s0)
      +hx = Equal.cong(F.Slot<V>, List<&2, S.Ent<V>>, z => ST.ent_at(V, k0, z, er), ST.sat(V, es, s0), F.Live{v}, ee)
      +e1 = Equal.cong(List<&2, S.Ent<V>>, S.Model<V> & E.Obs<V>, z => S.keys_fin(V, cap, life, S.strip(V, z, ST.mets(AR.slots(U32, tc)), now)), ST.ents(V, ks, es, Con{s0, rest}), Con{S.En{k0, v, S.zero_time()}, er}, hx)
      +e2 = L.subst(Bool, z => {S.keys_fin(V, cap, life, S.strip_at(V, S.En{k0, v, S.zero_time()}, er, ST.mets(AR.slots(U32, tc)), z, S.strip(V, er, T.bump(2n, ST.mets(AR.slots(U32, tc))), now))) == kobs(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl}) : S.Model<V> & E.Obs<V>}, False{}, NS.expired(S.zero_time(), now), Equal.sym(Bool, NS.expired(S.zero_time(), now), False{}, RF.zero_live(now)), keep_head(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, s0, rest, fl, now, S.En{k0, v, S.zero_time()}, hx))
      Equal.trans(S.Model<V> & E.Obs<V>, S.keys_fin(V, cap, life, S.strip(V, ST.ents(V, ks, es, Con{s0, rest}), ST.mets(AR.slots(U32, tc)), now)), S.keys_fin(V, cap, life, S.strip(V, Con{S.En{k0, v, S.zero_time()}, er}, ST.mets(AR.slots(U32, tc)), now)), kobs(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl}), e1, e2)
    case F.Timed{+v, +d}:
      +ks = AR.slots(String, tk)
      +es = AR.slots(F.Slot<V>, te)
      +er = ST.ents(V, ks, es, rest)
      +k0 = ST.kat(ks, s0)
      +hx = Equal.cong(F.Slot<V>, List<&2, S.Ent<V>>, z => ST.ent_at(V, k0, z, er), ST.sat(V, es, s0), F.Timed{v, d}, ee)
      +e1 = Equal.cong(List<&2, S.Ent<V>>, S.Model<V> & E.Obs<V>, z => S.keys_fin(V, cap, life, S.strip(V, z, ST.mets(AR.slots(U32, tc)), now)), ST.ents(V, ks, es, Con{s0, rest}), Con{S.En{k0, v, F.stamp_int(d)}, er}, hx)
      Equal.trans(S.Model<V> & E.Obs<V>, S.keys_fin(V, cap, life, S.strip(V, ST.ents(V, ks, es, Con{s0, rest}), ST.mets(AR.slots(U32, tc)), now)), S.keys_fin(V, cap, life, S.strip(V, Con{S.En{k0, v, F.stamp_int(d)}, er}, ST.mets(AR.slots(U32, tc)), now)), kobs(~V, st_exp(V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl}, st_g(V, p, ev2(V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl}), now), NS.expired(F.stamp_int(d), now))), e1,
        stm_x(~V, p, cap, fresh, depth, life, tc, table, tk, te, tp, tn, s0, rest, fl, now, v, F.stamp_int(d), hx, NS.expired(F.stamp_int(d), now), hl, h, ih))

def stm_c(~V: Data, +p: Nat, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, ord: List<&2, Nat>, +fl: List<&2, Nat>, +now: T.Int64, +hl: {Nat.is_le(SC.length(Nat, ord), 1n+p) == True{} : Bool}, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}, ih: StmIH(~V, p, now)) -> {S.keys_fin(V, cap, life, S.strip(V, ST.ents(V, AR.slots(String, tk), AR.slots(F.Slot<V>, te), ord), ST.mets(AR.slots(U32, tc)), now)) == kobs(~V, st_ord(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, now, st_g(V, p, ev2(V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), now))) : S.Model<V> & E.Obs<V>}:
  match ord:
    case Nil{}:
      {==}
    case Con{+s0, +rest}:
      stm_e(~V, p, cap, fresh, depth, life, tc, table, tk, te, tp, tn, s0, rest, fl, now, ST.sat(V, AR.slots(F.Slot<V>, te), s0), {==}, hl, h, ih)

def nil_of(ord: List<&2, Nat>, +h: {Nat.is_le(SC.length(Nat, ord), 0n) == True{} : Bool}) -> {ord == Nil{} : List<&2, Nat>}:
  match ord:
    case Nil{}:
      {==}
    case Con{x, t}:
      Empty.absurd({Con{x, t} == Nil{} : List<&2, Nat>}, L.false_true(h))

def st_model(~V: Data, fuel: Nat, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +now: T.Int64, +hl: {Nat.is_le(SC.length(Nat, ord), fuel) == True{} : Bool}, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}) -> {S.keys_fin(V, cap, life, S.strip(V, ST.ents(V, AR.slots(String, tk), AR.slots(F.Slot<V>, te), ord), ST.mets(AR.slots(U32, tc)), now)) == kobs(~V, st_g(V, fuel, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}, now)) : S.Model<V> & E.Obs<V>}:
  match fuel:
    case 0n:
      L.subst(List<&2, Nat>, z => {S.keys_fin(V, cap, life, S.strip(V, ST.ents(V, AR.slots(String, tk), AR.slots(F.Slot<V>, te), z), ST.mets(AR.slots(U32, tc)), now)) == kobs(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, z, fl}) : S.Model<V> & E.Obs<V>}, Nil{}, ord, Equal.sym(List<&2, Nat>, ord, Nil{}, nil_of(ord, hl)), {==})
    case 1n+ +p:
      stm_c(~V, p, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, now, hl, h, a1 => a2 => a3 => a4 => a5 => a6 => a7 => a8 => a9 => a10 => a11 => a12 => a13 => a14 => st_model(~V, p, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, now, a13, a14))

# ---- the invariant after the expiry loop ----

def StiIH(~V: Data, +p: Nat, +now: T.Int64) -> Type:
  @cap: U32 -> @fresh: Nat -> @depth: Nat -> @life: T.Int64 -> @tc: AR.Tree<U32> -> @table: Map<&2, Maybe<&2, U32>> -> @tk: AR.Tree<String> -> @te: AR.Tree<F.Slot<V>> -> @tp: AR.Tree<U32> -> @tn: AR.Tree<U32> -> @ord: List<&2, Nat> -> @fl: List<&2, Nat> -> @hl: {Nat.is_le(SC.length(Nat, ord), p) == True{} : Bool} -> @h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool} -> {ST.good(~V, st_g(V, p, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}, now)) == True{} : Bool}

def sti_x(~V: Data, +p: Nat, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +s0: Nat, +rest: List<&2, Nat>, +fl: List<&2, Nat>, +now: T.Int64, expired: Bool, +hl: {Nat.is_le(SC.length(Nat, Con{s0, rest}), 1n+p) == True{} : Bool}, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl) == True{} : Bool}, ih: StiIH(~V, p, now)) -> {ST.good(~V, st_exp(V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl}, st_g(V, p, ev2(V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl}), now), expired)) == True{} : Bool}:
  match expired:
    case False{}:
      h
    case True{}:
      +hm = TB.or_true_l(Nat.is_eq(s0, s0), DST.lmem(s0, rest), AL.lmem_self(s0))
      +h2 = RM.rm_at_inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl, s0, 2n, hm, h)
      +hl2 = L.subst(Nat, z => {Nat.is_le(z, p) == True{} : Bool}, SC.length(Nat, rest), SC.length(Nat, SC.append(Nat, SP.spre(Con{s0, rest}, s0), SP.spost(Con{s0, rest}, s0))), Equal.sym(Nat, SC.length(Nat, SC.append(Nat, SP.spre(Con{s0, rest}, s0), SP.spost(Con{s0, rest}, s0))), SC.length(Nat, rest), RZ.hrm_len(s0, rest, hm)), hl)
      ih(cap, fresh, depth, life, RS.sbd(tc, 2n), Map.del(&2, Maybe<&2, U32>, table, ST.kat(AR.slots(String, tk), s0)), tk, AR.upd(F.Slot<V>, depth, te, s0, F.Vacant{}), TS.tpup(depth, tp, SP.spost(Con{s0, rest}, s0), LK.lastl(SP.spre(Con{s0, rest}, s0), D.nil())), AR.upd(U32, depth, TS.tnup(depth, tn, SP.spre(Con{s0, rest}, s0), DST.hd_or(SP.spost(Con{s0, rest}, s0), D.nil())), s0, DST.hd(fl)), SC.append(Nat, SP.spre(Con{s0, rest}, s0), SP.spost(Con{s0, rest}, s0)), Con{s0, fl}, hl2, h2)

def sti_e(~V: Data, +p: Nat, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +s0: Nat, +rest: List<&2, Nat>, +fl: List<&2, Nat>, +now: T.Int64, e: F.Slot<V>, +hl: {Nat.is_le(SC.length(Nat, Con{s0, rest}), 1n+p) == True{} : Bool}, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl) == True{} : Bool}, ih: StiIH(~V, p, now)) -> {ST.good(~V, st_slot(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl, now, st_g(V, p, ev2(V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, Con{s0, rest}, fl}), now), e)) == True{} : Bool}:
  match e:
    case F.Vacant{}:
      h
    case F.Live{v}:
      h
    case F.Timed{v, +d}:
      sti_x(~V, p, cap, fresh, depth, life, tc, table, tk, te, tp, tn, s0, rest, fl, now, NS.expired(F.stamp_int(d), now), hl, h, ih)

def sti_c(~V: Data, +p: Nat, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, ord: List<&2, Nat>, +fl: List<&2, Nat>, +now: T.Int64, +hl: {Nat.is_le(SC.length(Nat, ord), 1n+p) == True{} : Bool}, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}, ih: StiIH(~V, p, now)) -> {ST.good(~V, st_ord(V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, now, st_g(V, p, ev2(V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), now))) == True{} : Bool}:
  match ord:
    case Nil{}:
      h
    case Con{+s0, +rest}:
      sti_e(~V, p, cap, fresh, depth, life, tc, table, tk, te, tp, tn, s0, rest, fl, now, ST.sat(V, AR.slots(F.Slot<V>, te), s0), hl, h, ih)

def st_inv(~V: Data, fuel: Nat, +cap: U32, +fresh: Nat, +depth: Nat, +life: T.Int64, +tc: AR.Tree<U32>, +table: Map<&2, Maybe<&2, U32>>, +tk: AR.Tree<String>, +te: AR.Tree<F.Slot<V>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +fl: List<&2, Nat>, +now: T.Int64, +hl: {Nat.is_le(SC.length(Nat, ord), fuel) == True{} : Bool}, +h: {ST.inv(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl) == True{} : Bool}) -> {ST.good(~V, st_g(V, fuel, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}, now)) == True{} : Bool}:
  match fuel:
    case 0n:
      h
    case 1n+ +p:
      sti_c(~V, p, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, now, hl, h, a1 => a2 => a3 => a4 => a5 => a6 => a7 => a8 => a9 => a10 => a11 => a12 => a13 => a14 => st_inv(~V, p, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, now, a13, a14))

# ---- the walk on any good state ----

def klist_ok(~V: Data, sh: ST.Shadow<V>, +h: {ST.good(~V, sh) == True{} : Bool}) -> {F.obs_keys(~V, F.keys_list(~V, ST.real(~V, sh))) == (ST.real(~V, sh), E.OKeys{S.keys(V, ents_of(V, sh))}) : F.Fast<V> & E.Obs<V>}:
  match sh:
    case ST.Sh{+cap, +fresh, +depth, +life, +tc, +table, +tk, +te, +tp, +tn, +ord, +fl}:
      +ks = AR.slots(String, tk)
      +ps = AR.slots(U32, tp)
      +ns = AR.slots(U32, tn)
      +r = SC.reverse(Nat, ord)
      +err = LL.spec_rev_rev(Nat, ord)
      +hl = L.subst(List<&2, Nat>, z => {DST.alllt(z, SC.pow2(depth)) == True{} : Bool}, ord, SC.reverse(Nat, r), Equal.sym(List<&2, Nat>, SC.reverse(Nat, r), ord, err), K.alllt_mono(ord, fresh, SC.pow2(depth), ST.g_fresh(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_ordlt(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h)))
      +hk = L.subst(List<&2, Nat>, z => {DST.lk(z, D.nil(), D.nil(), ps, ns) == True{} : Bool}, ord, SC.reverse(Nat, r), Equal.sym(List<&2, Nat>, SC.reverse(Nat, r), ord, err), ST.g_lk(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h))
      +w0 = KW.kwalk_ok(depth, tk, tp, ns, r, Nil{}, D.nil(), ST.g_depth(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_tk(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), ST.g_tp(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h), hl, hk)
      +w1 = L.subst(List<&2, Nat>, z => {F.wk_loop(SC.length(Nat, r), KW.kcur(tk, tp, Nil{}, LK.lastl(z, D.nil()))) == KW.kcur(tk, tp, SC.append(String, ST.keys_at(ks, z), Nil{}), D.nil()) : F.Walk}, SC.reverse(Nat, r), ord, err, w0)
      +w2 = L.subst(Nat, n => {F.wk_loop(n, KW.kcur(tk, tp, Nil{}, LK.lastl(ord, D.nil()))) == KW.kcur(tk, tp, SC.append(String, ST.keys_at(ks, ord), Nil{}), D.nil()) : F.Walk}, SC.length(Nat, r), SC.length(Nat, ord), LL.length_rev(Nat, ord), w1)
      +w3 = L.subst(U32, z => {F.wk_loop(SC.length(Nat, ord), KW.kcur(tk, tp, Nil{}, z)) == KW.kcur(tk, tp, SC.append(String, ST.keys_at(ks, ord), Nil{}), D.nil()) : F.Walk}, LK.lastl(ord, D.nil()), DST.lst(ord), Equal.sym(U32, DST.lst(ord), LK.lastl(ord, D.nil()), TL.lst_lastl(ord)), w2)
      +w4 = L.subst(Nat, n => {F.wk_loop(n, KW.kcur(tk, tp, Nil{}, DST.lst(ord))) == KW.kcur(tk, tp, SC.append(String, ST.keys_at(ks, ord), Nil{}), D.nil()) : F.Walk}, SC.length(Nat, ord), U32.to_nat(U32.from_nat(SC.length(Nat, ord))), Equal.sym(Nat, U32.to_nat(U32.from_nat(SC.length(Nat, ord))), SC.length(Nat, ord), AO.len_nat(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h)), w3)
      +ekeys = Equal.trans(List<&2, String>, SC.append(String, ST.keys_at(ks, ord), Nil{}), ST.keys_at(ks, ord), S.keys(V, ST.ents(V, ks, AR.slots(F.Slot<V>, te), ord)), LL.append_nil(String, ST.keys_at(ks, ord)), Equal.sym(List<&2, String>, S.keys(V, ST.ents(V, ks, AR.slots(F.Slot<V>, te), ord)), ST.keys_at(ks, ord), EN.keys_ents(V, ks, AR.slots(F.Slot<V>, te), ord, ST.g_occ(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h))))
      Equal.trans(F.Fast<V> & E.Obs<V>, F.obs_keys(~V, F.keys_fin(~V, cap, U32.from_nat(SC.length(Nat, ord)), U32.from_nat(fresh), U.pow2u(depth), depth, Bool.not(Time.is_zero(life)), F.int_stamp(life), AR.thaw(U32, tc), table, AR.thaw(F.Slot<V>, te), DST.hd(ord), DST.lst(ord), DST.hd(fl), AR.thaw(U32, tn), F.wk_loop(U32.to_nat(U32.from_nat(SC.length(Nat, ord))), KW.kcur(tk, tp, Nil{}, DST.lst(ord))))), (ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), E.OKeys{SC.append(String, ST.keys_at(ks, ord), Nil{})}), (ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), E.OKeys{S.keys(V, ST.ents(V, ks, AR.slots(F.Slot<V>, te), ord))}),
        Equal.cong(F.Walk, F.Fast<V> & E.Obs<V>, w => F.obs_keys(~V, F.keys_fin(~V, cap, U32.from_nat(SC.length(Nat, ord)), U32.from_nat(fresh), U.pow2u(depth), depth, Bool.not(Time.is_zero(life)), F.int_stamp(life), AR.thaw(U32, tc), table, AR.thaw(F.Slot<V>, te), DST.hd(ord), DST.lst(ord), DST.hd(fl), AR.thaw(U32, tn), w)), F.wk_loop(U32.to_nat(U32.from_nat(SC.length(Nat, ord))), KW.kcur(tk, tp, Nil{}, DST.lst(ord))), KW.kcur(tk, tp, SC.append(String, ST.keys_at(ks, ord), Nil{}), D.nil()), w4),
        Equal.cong(List<&2, String>, F.Fast<V> & E.Obs<V>, z => (ST.real(~V, ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}), E.OKeys{z}), SC.append(String, ST.keys_at(ks, ord), Nil{}), S.keys(V, ST.ents(V, ks, AR.slots(F.Slot<V>, te), ord)), ekeys))
