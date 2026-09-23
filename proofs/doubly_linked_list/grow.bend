import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/u32.bend as U
import ../lib/array.bend as AR
import ../lib/list.bend as LL
import ../spec/common.bend as SC
import ../spec/doubly_linked_list.bend as S
import ../math/u32div.bend as UD
import ../hash_table/table.bend as TB
import ../lru/state.bend as LST
import ./state.bend as ST
import ./rel.bend as RL
import ./vals.bend as VA

# The doubled blocks: the old block is the lower half, so every id keeps its
# links, value and generation.


def nth0_app(+xs: List<&2, U32>, +ys: List<&2, U32>, +i: Nat, +h: {Nat.is_lt(i, SC.length(U32, xs)) == True{} : Bool}) -> {TB.nth0(SC.append(U32, xs, ys), i) == TB.nth0(xs, i) : U32}:
  match xs i:
    case Nil{} _:
      Empty.absurd({TB.nth0(ys, i) == 0 : U32}, N.lt_zero_absurd(i, h))
    case Con{x, t} 0n:
      {==}
    case Con{x, +t} 1n+p:
      nth0_app(t, ys, p, h)

def val_app(-T: Data, +vl: List<&2, Maybe<&2, T>>, +ys: List<&2, Maybe<&2, T>>, +i: Nat, +h: {Nat.is_lt(i, SC.length(Maybe<&2, T>, vl)) == True{} : Bool}) -> {S.val_of(T, SC.append(Maybe<&2, T>, vl, ys), i) == S.val_of(T, vl, i) : Maybe<&2, T>}:
  match vl i:
    case Nil{} _:
      Empty.absurd({S.val_of(T, ys, i) == None{} : Maybe<&2, T>}, N.lt_zero_absurd(i, h))
    case Con{m, t} 0n:
      {==}
    case Con{m, +t} 1n+p:
      val_app(T, t, ys, p, h)


# the links of a live list, after the blocks are extended
def seg_ext(~T: Data, +pl: List<&2, U32>, +pz: List<&2, U32>, +nl: List<&2, U32>, +nz: List<&2, U32>, +sl: List<&2, Nat>, +p: U32, +q: U32, +fr: Nat, +vl: List<&2, Maybe<&2, T>>, +h: {ST.slok(~T, sl, fr, vl) == True{} : Bool}, +hp: {Nat.is_le(fr, SC.length(U32, pl)) == True{} : Bool}, +hn: {Nat.is_le(fr, SC.length(U32, nl)) == True{} : Bool}) -> {ST.seg(SC.append(U32, pl, pz), SC.append(U32, nl, nz), sl, p, q) == ST.seg(pl, nl, sl, p, q) : Bool}:
  match sl:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +hx = L.and_left(Nat.is_lt(x, fr), ST.live(T, vl, x), L.and_left(Bool.and(Nat.is_lt(x, fr), ST.live(T, vl, x)), ST.slok(~T, t, fr, vl), h))
      +ht = L.and_right(Bool.and(Nat.is_lt(x, fr), ST.live(T, vl, x)), ST.slok(~T, t, fr, vl), h)
      +e0 = nth0_app(pl, pz, x, N.lt_le_trans(x, fr, SC.length(U32, pl), hx, hp))
      +e1 = nth0_app(nl, nz, x, N.lt_le_trans(x, fr, SC.length(U32, nl), hx, hn))
      +ih = seg_ext(~T, pl, pz, nl, nz, t, LST.lnk(x), q, fr, vl, ht, hp, hn)
      +r1 = Equal.cong(U32, Bool, z => Bool.and(U32.is_eq(z, p), Bool.and(U32.is_eq(TB.nth0(SC.append(U32, nl, nz), x), LST.fst_or(t, q)), ST.seg(SC.append(U32, pl, pz), SC.append(U32, nl, nz), t, LST.lnk(x), q))), TB.nth0(SC.append(U32, pl, pz), x), TB.nth0(pl, x), e0)
      +r2 = Equal.cong(U32, Bool, z => Bool.and(U32.is_eq(TB.nth0(pl, x), p), Bool.and(U32.is_eq(z, LST.fst_or(t, q)), ST.seg(SC.append(U32, pl, pz), SC.append(U32, nl, nz), t, LST.lnk(x), q))), TB.nth0(SC.append(U32, nl, nz), x), TB.nth0(nl, x), e1)
      +r3 = Equal.cong(Bool, Bool, z => Bool.and(U32.is_eq(TB.nth0(pl, x), p), Bool.and(U32.is_eq(TB.nth0(nl, x), LST.fst_or(t, q)), z)), ST.seg(SC.append(U32, pl, pz), SC.append(U32, nl, nz), t, LST.lnk(x), q), ST.seg(pl, nl, t, LST.lnk(x), q), ih)
      Equal.trans(Bool, ST.seg(SC.append(U32, pl, pz), SC.append(U32, nl, nz), Con{x, t}, p, q), Bool.and(U32.is_eq(TB.nth0(pl, x), p), Bool.and(U32.is_eq(TB.nth0(SC.append(U32, nl, nz), x), LST.fst_or(t, q)), ST.seg(SC.append(U32, pl, pz), SC.append(U32, nl, nz), t, LST.lnk(x), q))), ST.seg(pl, nl, Con{x, t}, p, q), r1, Equal.trans(Bool, Bool.and(U32.is_eq(TB.nth0(pl, x), p), Bool.and(U32.is_eq(TB.nth0(SC.append(U32, nl, nz), x), LST.fst_or(t, q)), ST.seg(SC.append(U32, pl, pz), SC.append(U32, nl, nz), t, LST.lnk(x), q))), Bool.and(U32.is_eq(TB.nth0(pl, x), p), Bool.and(U32.is_eq(TB.nth0(nl, x), LST.fst_or(t, q)), ST.seg(SC.append(U32, pl, pz), SC.append(U32, nl, nz), t, LST.lnk(x), q))), ST.seg(pl, nl, Con{x, t}, p, q), r2, r3))

# live ids stay live when vacant slots are appended
def slok_ext(~T: Data, +xs: List<&2, Nat>, +fr: Nat, +vl: List<&2, Maybe<&2, T>>, +ys: List<&2, Maybe<&2, T>>, +hfr: {Nat.is_le(fr, SC.length(Maybe<&2, T>, vl)) == True{} : Bool}, +h: {ST.slok(~T, xs, fr, vl) == True{} : Bool}) -> {ST.slok(~T, xs, fr, SC.append(Maybe<&2, T>, vl, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +h0 = L.and_left(Bool.and(Nat.is_lt(x, fr), ST.live(T, vl, x)), ST.slok(~T, t, fr, vl), h)
      +h1 = L.and_right(Bool.and(Nat.is_lt(x, fr), ST.live(T, vl, x)), ST.slok(~T, t, fr, vl), h)
      +hx = L.and_left(Nat.is_lt(x, fr), ST.live(T, vl, x), h0)
      +e = Equal.cong(Maybe<&2, T>, Bool, m => ST.some_b(T, m), S.val_of(T, SC.append(Maybe<&2, T>, vl, ys), x), S.val_of(T, vl, x), val_app(T, vl, ys, x, N.lt_le_trans(x, fr, SC.length(Maybe<&2, T>, vl), hx, hfr)))
      +hl = RL.by_eq(ST.live(T, SC.append(Maybe<&2, T>, vl, ys), x), ST.live(T, vl, x), e, L.and_right(Nat.is_lt(x, fr), ST.live(T, vl, x), h0))
      L.and_intro(Bool.and(Nat.is_lt(x, fr), ST.live(T, SC.append(Maybe<&2, T>, vl, ys), x)), ST.slok(~T, t, fr, SC.append(Maybe<&2, T>, vl, ys)), L.and_intro(Nat.is_lt(x, fr), ST.live(T, SC.append(Maybe<&2, T>, vl, ys), x), hx, hl), slok_ext(~T, t, fr, vl, ys, hfr, h1))

# 2^a < 2^b: a < b
def p2_c(+a: Nat, +b: Nat, +h: {Nat.is_lt(SC.pow2(a), SC.pow2(b)) == True{} : Bool}, +c: Bool, +hc: {Nat.is_lt(a, b) == c : Bool}) -> {c == True{} : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      +hba = N.pow2_mono(b, a, N.not_lt_le(a, b, hc))
      Empty.absurd({False{} == True{} : Bool}, L.true_false(Equal.trans(Bool, True{}, Nat.is_lt(SC.pow2(a), SC.pow2(a)), False{}, Equal.sym(Bool, Nat.is_lt(SC.pow2(a), SC.pow2(a)), True{}, N.lt_le_trans(SC.pow2(a), SC.pow2(b), SC.pow2(a), h, hba)), N.lt_irrefl(SC.pow2(a)))))

def p2_inv(+a: Nat, +b: Nat, +h: {Nat.is_lt(SC.pow2(a), SC.pow2(b)) == True{} : Bool}) -> {Nat.is_lt(a, b) == True{} : Bool}:
  p2_c(a, b, h, Nat.is_lt(a, b), {==})

# the doubled capacity
def shl_cap(+cap: U32, +d: Nat, +hd: {Nat.is_lt(d, 29n) == True{} : Bool}, +hcap: {Nat.is_eq(UD.v(cap), SC.pow2(d)) == True{} : Bool}) -> {Nat.is_eq(UD.v(U32.shl(cap)), SC.pow2(1n+d)) == True{} : Bool}:
  +e = N.eq_from_is_eq(UD.v(cap), SC.pow2(d), hcap)
  +hb = L.subst(Nat, z => {Nat.is_lt(Nat.double(z), SC.pow2(2n+d)) == True{} : Bool}, SC.pow2(d), UD.v(cap), Equal.sym(Nat, UD.v(cap), SC.pow2(d), e), N.pow2_lt_succ(1n+d))
  +hk = N.lt_le(2n+d, 32n, N.lt_trans(2n+d, 31n, 32n, hd, {==}))
  +ev = U.shl_value(cap, 2n+d, hk, hb)
  +ev2 = Equal.trans(Nat, UD.v(U32.shl(cap)), Nat.double(UD.v(cap)), SC.pow2(1n+d), ev, Equal.cong(Nat, Nat, z => Nat.double(z), UD.v(cap), SC.pow2(d), e))
  L.subst(Nat, z => {Nat.is_eq(z, SC.pow2(1n+d)) == True{} : Bool}, SC.pow2(1n+d), UD.v(U32.shl(cap)), Equal.sym(Nat, UD.v(U32.shl(cap)), SC.pow2(1n+d), ev2), N.is_eq_refl(SC.pow2(1n+d)))

def gz_ext(+gT: AR.Tree<U32>, +d: Nat, +pg: {AR.perfect(U32, d, gT) == True{} : Bool}, +fr: Nat, +e: {SC.pow2(d) == fr : Nat}) -> {ST.gz(AR.slots(U32, AR.TNode{gT, AR.trep(U32, d, 0)}), fr) == True{} : Bool}:
  +es = AR.trep_slots(U32, d, 0)
  +h0 = L.subst(Nat, z => {ST.gz(SC.append(U32, AR.slots(U32, gT), SC.replicate(U32, SC.pow2(d), 0)), z) == True{} : Bool}, SC.length(U32, AR.slots(U32, gT)), fr, Equal.trans(Nat, SC.length(U32, AR.slots(U32, gT)), SC.pow2(d), fr, AR.slots_length(U32, d, gT, pg), e), VA.gz_grow(AR.slots(U32, gT), SC.pow2(d)))
  L.subst(List<&2, U32>, z => {ST.gz(SC.append(U32, AR.slots(U32, gT), z), fr) == True{} : Bool}, SC.replicate(U32, SC.pow2(d), 0), AR.slots(U32, AR.trep(U32, d, 0)), Equal.sym(List<&2, U32>, AR.slots(U32, AR.trep(U32, d, 0)), SC.replicate(U32, SC.pow2(d), 0), es), h0)

def lvin_ext(~T: Data, +vT: AR.Tree<Maybe<&2, T>>, +d: Nat, +sl: List<&2, Nat>, +h: {ST.lvin(~T, AR.slots(Maybe<&2, T>, vT), 0n, sl) == True{} : Bool}) -> {ST.lvin(~T, AR.slots(Maybe<&2, T>, AR.TNode{vT, AR.trep(Maybe<&2, T>, d, None{})}), 0n, sl) == True{} : Bool}:
  L.subst(List<&2, Maybe<&2, T>>, z => {ST.lvin(~T, SC.append(Maybe<&2, T>, AR.slots(Maybe<&2, T>, vT), z), 0n, sl) == True{} : Bool}, SC.replicate(Maybe<&2, T>, SC.pow2(d), None{}), AR.slots(Maybe<&2, T>, AR.trep(Maybe<&2, T>, d, None{})), Equal.sym(List<&2, Maybe<&2, T>>, AR.slots(Maybe<&2, T>, AR.trep(Maybe<&2, T>, d, None{})), SC.replicate(Maybe<&2, T>, SC.pow2(d), None{}), AR.trep_slots(Maybe<&2, T>, d, None{})), VA.lvin_grow(~T, AR.slots(Maybe<&2, T>, vT), 0n, sl, SC.pow2(d), h))
