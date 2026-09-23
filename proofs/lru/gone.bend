import Base
import ../lib/logic.bend as L
import ../lib/array.bend as AR
import ../spec/common.bend as SC
import ../spec/lru.bend as SP
import ../math/u32div.bend as UD
import ../../src/math/u64.bend as W
import ../../src/containers/lru.bend as LR
import ./state.bend as ST
import ./idx.bend as ID
import ./unlink.bend as UL
import ../lib/words32.bend as W32
import ../lib/u32_tree.bend as UT

# gone: the implementation's expiry test of a slot is the specification's
# test of its entry.


def exp_c(+d: W.U64, +now: W.U64, +z: Bool, +hz: {W.is_zero(d) == z : Bool}) -> {LR.expired_choose(d, now, z) == Bool.pick(Bool, z, False{}, W.le_signed(d, now)) : Bool}:
  match z:
    case True{}:
      {==}
    case False{}:
      {==}

# the two expiry tests agree
def exp_eq(+d: W.U64, +now: W.U64) -> {LR.expired(d, now) == SP.expired(d, now) : Bool}:
  exp_c(d, now, W.is_zero(d), {==})

# a read of word o of slot s
def rd(+one: Nat, +h1: {one == 1n : Nat}, +lkT: AR.Tree<U32>, +sd: Nat, +hsd: {Nat.is_lt(3n+sd, 32n) == True{} : Bool}, +hpl: {AR.perfect(U32, 3n+sd, lkT) == True{} : Bool}, +i: U32, +s: Nat, +o: Nat, +ho: {Nat.is_lt(o, 8n) == True{} : Bool}, +hs0: {Nat.is_lt(s, SC.pow2(sd)) == True{} : Bool}, +hi: {UD.v(i) == ST.off(s, o) : Nat}) -> {Array.get(U32, AR.thaw(U32, lkT), i) == (AR.thaw(U32, lkT), ST.lw(AR.slots(U32, lkT), s, o)) : Array<U32> & U32}:
  +hl = L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(3n+sd)) == True{} : Bool}, ST.off(s, o), UD.v(i), Equal.sym(Nat, UD.v(i), ST.off(s, o), hi), ID.off_lt(s, sd, hs0, o, ho))
  Equal.trans(Array<U32> & U32, Array.get(U32, AR.thaw(U32, lkT), i), (AR.thaw(U32, lkT), W32.nth0(AR.slots(U32, lkT), UD.v(i))), (AR.thaw(U32, lkT), ST.lw(AR.slots(U32, lkT), s, o)), UT.uget(3n+sd, hsd, lkT, hpl, i, hl), Equal.cong(Nat, Array<U32> & U32, z => (AR.thaw(U32, lkT), W32.nth0(AR.slots(U32, lkT), z)), UD.v(i), ST.off(s, o), hi))

def su_lt(+su: U32, +s: Nat, +sd: Nat, +hsv: {UD.v(su) == s : Nat}, +hs0: {Nat.is_lt(s, SC.pow2(sd)) == True{} : Bool}) -> {Nat.is_lt(UD.v(su), SC.pow2(sd)) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(sd)) == True{} : Bool}, s, UD.v(su), Equal.sym(Nat, UD.v(su), s, hsv), hs0)

def gone_c(~V: Data, +one: Nat, +h1: {one == 1n : Nat}, +lkT: AR.Tree<U32>, +sd: Nat, +hsd: {Nat.is_lt(3n+sd, 32n) == True{} : Bool}, +hpl: {AR.perfect(U32, 3n+sd, lkT) == True{} : Bool}, +su: U32, +s: Nat, +hsv: {UD.v(su) == s : Nat}, +hs0: {Nat.is_lt(s, SC.pow2(sd)) == True{} : Bool}, +now: W.U64, +kk: String, +vv: V, +c: Bool, +hc: {U32.is_eq(ST.lw(AR.slots(U32, lkT), s, 3n), 0) == c : Bool}) -> {LR.gone_t(su, now, AR.thaw(U32, lkT), Bool.not(c)) == (AR.thaw(U32, lkT), SP.gone(~V, SP.LE{kk, vv, ST.lw(AR.slots(U32, lkT), s, 3n), W.U64{ST.lw(AR.slots(U32, lkT), s, 4n), ST.lw(AR.slots(U32, lkT), s, 5n)}}, now)) : Array<U32> & Bool}:
  match c:
    case True{}:
      L.subst(Bool, z => {(AR.thaw(U32, lkT), False{}) == (AR.thaw(U32, lkT), Bool.pick(Bool, z, False{}, SP.expired(W.U64{ST.lw(AR.slots(U32, lkT), s, 4n), ST.lw(AR.slots(U32, lkT), s, 5n)}, now))) : Array<U32> & Bool}, True{}, U32.is_eq(ST.lw(AR.slots(U32, lkT), s, 3n), 0), Equal.sym(Bool, U32.is_eq(ST.lw(AR.slots(U32, lkT), s, 3n), 0), True{}, hc), {==})
    case False{}:
      +hsu = su_lt(su, s, sd, hsv, hs0)
      +i4 = Equal.trans(Nat, UD.v(LR.dlo_idx(su)), ST.off(UD.v(su), 4n), ST.off(s, 4n), ID.w4(one, h1, su, sd, UL.sd3(sd, hsd), hsu), Equal.cong(Nat, Nat, z => ST.off(z, 4n), UD.v(su), s, hsv))
      +i5 = Equal.trans(Nat, UD.v(LR.dhi_idx(su)), ST.off(UD.v(su), 5n), ST.off(s, 5n), ID.w5(one, h1, su, sd, UL.sd3(sd, hsd), hsu), Equal.cong(Nat, Nat, z => ST.off(z, 5n), UD.v(su), s, hsv))
      +E1 = Equal.cong(Array<U32> & U32, Array<U32> & Bool, r => LR.gone_lo(su, now, r), Array.get(U32, AR.thaw(U32, lkT), LR.dlo_idx(su)), (AR.thaw(U32, lkT), ST.lw(AR.slots(U32, lkT), s, 4n)), rd(one, h1, lkT, sd, hsd, hpl, LR.dlo_idx(su), s, 4n, {==}, hs0, i4))
      +E2 = Equal.cong(Array<U32> & U32, Array<U32> & Bool, r => LR.gone_hi(ST.lw(AR.slots(U32, lkT), s, 4n), now, r), Array.get(U32, AR.thaw(U32, lkT), LR.dhi_idx(su)), (AR.thaw(U32, lkT), ST.lw(AR.slots(U32, lkT), s, 5n)), rd(one, h1, lkT, sd, hsd, hpl, LR.dhi_idx(su), s, 5n, {==}, hs0, i5))
      +E3 = Equal.cong(Bool, Array<U32> & Bool, z => (AR.thaw(U32, lkT), z), LR.expired(W.U64{ST.lw(AR.slots(U32, lkT), s, 4n), ST.lw(AR.slots(U32, lkT), s, 5n)}, now), SP.expired(W.U64{ST.lw(AR.slots(U32, lkT), s, 4n), ST.lw(AR.slots(U32, lkT), s, 5n)}, now), exp_eq(W.U64{ST.lw(AR.slots(U32, lkT), s, 4n), ST.lw(AR.slots(U32, lkT), s, 5n)}, now))
      +E4 = L.subst(Bool, z => {(AR.thaw(U32, lkT), SP.expired(W.U64{ST.lw(AR.slots(U32, lkT), s, 4n), ST.lw(AR.slots(U32, lkT), s, 5n)}, now)) == (AR.thaw(U32, lkT), Bool.pick(Bool, z, False{}, SP.expired(W.U64{ST.lw(AR.slots(U32, lkT), s, 4n), ST.lw(AR.slots(U32, lkT), s, 5n)}, now))) : Array<U32> & Bool}, False{}, U32.is_eq(ST.lw(AR.slots(U32, lkT), s, 3n), 0), Equal.sym(Bool, U32.is_eq(ST.lw(AR.slots(U32, lkT), s, 3n), 0), False{}, hc), {==})
      Equal.trans(Array<U32> & Bool, LR.gone_lo(su, now, Array.get(U32, AR.thaw(U32, lkT), LR.dlo_idx(su))), LR.gone_lo(su, now, (AR.thaw(U32, lkT), ST.lw(AR.slots(U32, lkT), s, 4n))), (AR.thaw(U32, lkT), SP.gone(~V, SP.LE{kk, vv, ST.lw(AR.slots(U32, lkT), s, 3n), W.U64{ST.lw(AR.slots(U32, lkT), s, 4n), ST.lw(AR.slots(U32, lkT), s, 5n)}}, now)), E1, Equal.trans(Array<U32> & Bool, LR.gone_hi(ST.lw(AR.slots(U32, lkT), s, 4n), now, Array.get(U32, AR.thaw(U32, lkT), LR.dhi_idx(su))), LR.gone_hi(ST.lw(AR.slots(U32, lkT), s, 4n), now, (AR.thaw(U32, lkT), ST.lw(AR.slots(U32, lkT), s, 5n))), (AR.thaw(U32, lkT), SP.gone(~V, SP.LE{kk, vv, ST.lw(AR.slots(U32, lkT), s, 3n), W.U64{ST.lw(AR.slots(U32, lkT), s, 4n), ST.lw(AR.slots(U32, lkT), s, 5n)}}, now)), E2, Equal.trans(Array<U32> & Bool, (AR.thaw(U32, lkT), LR.expired(W.U64{ST.lw(AR.slots(U32, lkT), s, 4n), ST.lw(AR.slots(U32, lkT), s, 5n)}, now)), (AR.thaw(U32, lkT), SP.expired(W.U64{ST.lw(AR.slots(U32, lkT), s, 4n), ST.lw(AR.slots(U32, lkT), s, 5n)}, now)), (AR.thaw(U32, lkT), SP.gone(~V, SP.LE{kk, vv, ST.lw(AR.slots(U32, lkT), s, 3n), W.U64{ST.lw(AR.slots(U32, lkT), s, 4n), ST.lw(AR.slots(U32, lkT), s, 5n)}}, now)), E3, E4)))

# THEOREM (gone): the implementation's test of slot s is the specification's
# test of an entry with s's timing words
def gone_ok(~V: Data, +one: Nat, +h1: {one == 1n : Nat}, +lkT: AR.Tree<U32>, +sd: Nat, +hsd: {Nat.is_lt(3n+sd, 32n) == True{} : Bool}, +hpl: {AR.perfect(U32, 3n+sd, lkT) == True{} : Bool}, +su: U32, +s: Nat, +hsv: {UD.v(su) == s : Nat}, +hs0: {Nat.is_lt(s, SC.pow2(sd)) == True{} : Bool}, +now: W.U64, +kk: String, +vv: V) -> {LR.gone(AR.thaw(U32, lkT), su, now) == (AR.thaw(U32, lkT), SP.gone(~V, SP.LE{kk, vv, ST.lw(AR.slots(U32, lkT), s, 3n), W.U64{ST.lw(AR.slots(U32, lkT), s, 4n), ST.lw(AR.slots(U32, lkT), s, 5n)}}, now)) : Array<U32> & Bool}:
  +hsu = su_lt(su, s, sd, hsv, hs0)
  +i3 = Equal.trans(Nat, UD.v(LR.tidx(su)), ST.off(UD.v(su), 3n), ST.off(s, 3n), ID.w3(one, h1, su, sd, UL.sd3(sd, hsd), hsu), Equal.cong(Nat, Nat, z => ST.off(z, 3n), UD.v(su), s, hsv))
  +E = Equal.cong(Array<U32> & U32, Array<U32> & Bool, r => LR.gone_r(su, now, r), Array.get(U32, AR.thaw(U32, lkT), LR.tidx(su)), (AR.thaw(U32, lkT), ST.lw(AR.slots(U32, lkT), s, 3n)), rd(one, h1, lkT, sd, hsd, hpl, LR.tidx(su), s, 3n, {==}, hs0, i3))
  Equal.trans(Array<U32> & Bool, LR.gone(AR.thaw(U32, lkT), su, now), LR.gone_r(su, now, (AR.thaw(U32, lkT), ST.lw(AR.slots(U32, lkT), s, 3n))), (AR.thaw(U32, lkT), SP.gone(~V, SP.LE{kk, vv, ST.lw(AR.slots(U32, lkT), s, 3n), W.U64{ST.lw(AR.slots(U32, lkT), s, 4n), ST.lw(AR.slots(U32, lkT), s, 5n)}}, now)), E, gone_c(~V, one, h1, lkT, sd, hsd, hpl, su, s, hsv, hs0, now, kk, vv, U32.is_eq(ST.lw(AR.slots(U32, lkT), s, 3n), 0), {==}))
