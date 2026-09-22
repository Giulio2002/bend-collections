import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/u32.bend as U
import ../lib/array.bend as AR
import ../binary_heap/u32idx.bend as IX
import ../graph/shift.bend as SH
import ../../reference/lru/spec/numeric.bend as NS
import ../../spec/common.bend as SC
import ../../spec/doubly_linked_list.bend as DS
import ../../src/doubly_linked_list.bend as D
import ../../types/doubly_linked_list.bend as E
import ./state.bend as ST

# Basic facts about a good DLL shadow.

# ---- the parts of the invariant ----

def g1(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>) -> Bool:
  AR.perfect(Maybe<&2, T>, depth, tv)

def rest1(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>) -> Bool:
  Bool.and(AR.perfect(Maybe<&2, T>, depth, tv),
    Bool.and(AR.perfect(U32, depth, tp),
      Bool.and(AR.perfect(U32, depth, tn),
        Bool.and(Nat.is_le(fresh, SC.pow2(depth)),
          Bool.and(ST.alllt(ord, fresh),
            Bool.and(ST.nodup(ord),
              Bool.and(ST.lv(T, fresh, AR.slots(Maybe<&2, T>, tv), 0n, ord),
                ST.lk(ord, D.nil(), D.nil(), AR.slots(U32, tp), AR.slots(U32, tn)))))))))

def c2(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>) -> Bool:
  Bool.and(AR.perfect(U32, depth, tp),
    Bool.and(AR.perfect(U32, depth, tn),
      Bool.and(Nat.is_le(fresh, SC.pow2(depth)),
        Bool.and(ST.alllt(ord, fresh),
          Bool.and(ST.nodup(ord),
            Bool.and(ST.lv(T, fresh, AR.slots(Maybe<&2, T>, tv), 0n, ord),
              ST.lk(ord, D.nil(), D.nil(), AR.slots(U32, tp), AR.slots(U32, tn))))))))

def c3(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>) -> Bool:
  Bool.and(AR.perfect(U32, depth, tn),
    Bool.and(Nat.is_le(fresh, SC.pow2(depth)),
      Bool.and(ST.alllt(ord, fresh),
        Bool.and(ST.nodup(ord),
          Bool.and(ST.lv(T, fresh, AR.slots(Maybe<&2, T>, tv), 0n, ord),
            ST.lk(ord, D.nil(), D.nil(), AR.slots(U32, tp), AR.slots(U32, tn)))))))

def c4(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>) -> Bool:
  Bool.and(Nat.is_le(fresh, SC.pow2(depth)),
    Bool.and(ST.alllt(ord, fresh),
      Bool.and(ST.nodup(ord),
        Bool.and(ST.lv(T, fresh, AR.slots(Maybe<&2, T>, tv), 0n, ord),
          ST.lk(ord, D.nil(), D.nil(), AR.slots(U32, tp), AR.slots(U32, tn))))))

def c5(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>) -> Bool:
  Bool.and(ST.alllt(ord, fresh),
    Bool.and(ST.nodup(ord),
      Bool.and(ST.lv(T, fresh, AR.slots(Maybe<&2, T>, tv), 0n, ord),
        ST.lk(ord, D.nil(), D.nil(), AR.slots(U32, tp), AR.slots(U32, tn)))))

def c6(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>) -> Bool:
  Bool.and(ST.nodup(ord),
    Bool.and(ST.lv(T, fresh, AR.slots(Maybe<&2, T>, tv), 0n, ord),
      ST.lk(ord, D.nil(), D.nil(), AR.slots(U32, tp), AR.slots(U32, tn))))

def c7(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>) -> Bool:
  Bool.and(ST.lv(T, fresh, AR.slots(Maybe<&2, T>, tv), 0n, ord),
    ST.lk(ord, D.nil(), D.nil(), AR.slots(U32, tp), AR.slots(U32, tn)))

def g_depth(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +h: {ST.good(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}) == True{} : Bool}) -> {Nat.is_le(depth, 31n) == True{} : Bool}:
  L.and_left(Nat.is_le(depth, 31n), rest1(~T, tag, fresh, depth, tv, tp, tn, ord), h)

def g_tv(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +h: {ST.good(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}) == True{} : Bool}) -> {AR.perfect(Maybe<&2, T>, depth, tv) == True{} : Bool}:
  L.and_left(AR.perfect(Maybe<&2, T>, depth, tv), c2(~T, tag, fresh, depth, tv, tp, tn, ord), L.and_right(Nat.is_le(depth, 31n), rest1(~T, tag, fresh, depth, tv, tp, tn, ord), h))

def r2(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +h: {ST.good(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}) == True{} : Bool}) -> {c2(~T, tag, fresh, depth, tv, tp, tn, ord) == True{} : Bool}:
  L.and_right(AR.perfect(Maybe<&2, T>, depth, tv), c2(~T, tag, fresh, depth, tv, tp, tn, ord), L.and_right(Nat.is_le(depth, 31n), rest1(~T, tag, fresh, depth, tv, tp, tn, ord), h))

def g_tp(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +h: {ST.good(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}) == True{} : Bool}) -> {AR.perfect(U32, depth, tp) == True{} : Bool}:
  L.and_left(AR.perfect(U32, depth, tp), c3(~T, tag, fresh, depth, tv, tp, tn, ord), r2(~T, tag, fresh, depth, tv, tp, tn, ord, h))

def r3(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +h: {ST.good(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}) == True{} : Bool}) -> {c3(~T, tag, fresh, depth, tv, tp, tn, ord) == True{} : Bool}:
  L.and_right(AR.perfect(U32, depth, tp), c3(~T, tag, fresh, depth, tv, tp, tn, ord), r2(~T, tag, fresh, depth, tv, tp, tn, ord, h))

def g_tn(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +h: {ST.good(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}) == True{} : Bool}) -> {AR.perfect(U32, depth, tn) == True{} : Bool}:
  L.and_left(AR.perfect(U32, depth, tn), c4(~T, tag, fresh, depth, tv, tp, tn, ord), r3(~T, tag, fresh, depth, tv, tp, tn, ord, h))

def r4(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +h: {ST.good(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}) == True{} : Bool}) -> {c4(~T, tag, fresh, depth, tv, tp, tn, ord) == True{} : Bool}:
  L.and_right(AR.perfect(U32, depth, tn), c4(~T, tag, fresh, depth, tv, tp, tn, ord), r3(~T, tag, fresh, depth, tv, tp, tn, ord, h))

def g_fresh(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +h: {ST.good(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}) == True{} : Bool}) -> {Nat.is_le(fresh, SC.pow2(depth)) == True{} : Bool}:
  L.and_left(Nat.is_le(fresh, SC.pow2(depth)), c5(~T, tag, fresh, depth, tv, tp, tn, ord), r4(~T, tag, fresh, depth, tv, tp, tn, ord, h))

def r5(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +h: {ST.good(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}) == True{} : Bool}) -> {c5(~T, tag, fresh, depth, tv, tp, tn, ord) == True{} : Bool}:
  L.and_right(Nat.is_le(fresh, SC.pow2(depth)), c5(~T, tag, fresh, depth, tv, tp, tn, ord), r4(~T, tag, fresh, depth, tv, tp, tn, ord, h))

def g_lt(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +h: {ST.good(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}) == True{} : Bool}) -> {ST.alllt(ord, fresh) == True{} : Bool}:
  L.and_left(ST.alllt(ord, fresh), c6(~T, tag, fresh, depth, tv, tp, tn, ord), r5(~T, tag, fresh, depth, tv, tp, tn, ord, h))

def r6(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +h: {ST.good(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}) == True{} : Bool}) -> {c6(~T, tag, fresh, depth, tv, tp, tn, ord) == True{} : Bool}:
  L.and_right(ST.alllt(ord, fresh), c6(~T, tag, fresh, depth, tv, tp, tn, ord), r5(~T, tag, fresh, depth, tv, tp, tn, ord, h))

def g_nd(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +h: {ST.good(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}) == True{} : Bool}) -> {ST.nodup(ord) == True{} : Bool}:
  L.and_left(ST.nodup(ord), c7(~T, tag, fresh, depth, tv, tp, tn, ord), r6(~T, tag, fresh, depth, tv, tp, tn, ord, h))

def r7(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +h: {ST.good(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}) == True{} : Bool}) -> {c7(~T, tag, fresh, depth, tv, tp, tn, ord) == True{} : Bool}:
  L.and_right(ST.nodup(ord), c7(~T, tag, fresh, depth, tv, tp, tn, ord), r6(~T, tag, fresh, depth, tv, tp, tn, ord, h))

def g_lv(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +h: {ST.good(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}) == True{} : Bool}) -> {ST.lv(T, fresh, AR.slots(Maybe<&2, T>, tv), 0n, ord) == True{} : Bool}:
  L.and_left(ST.lv(T, fresh, AR.slots(Maybe<&2, T>, tv), 0n, ord), ST.lk(ord, D.nil(), D.nil(), AR.slots(U32, tp), AR.slots(U32, tn)), r7(~T, tag, fresh, depth, tv, tp, tn, ord, h))

def g_lk(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +h: {ST.good(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}) == True{} : Bool}) -> {ST.lk(ord, D.nil(), D.nil(), AR.slots(U32, tp), AR.slots(U32, tn)) == True{} : Bool}:
  L.and_right(ST.lv(T, fresh, AR.slots(Maybe<&2, T>, tv), 0n, ord), ST.lk(ord, D.nil(), D.nil(), AR.slots(U32, tp), AR.slots(U32, tn)), r7(~T, tag, fresh, depth, tv, tp, tn, ord, h))

def good_mk(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +pv: {AR.perfect(Maybe<&2, T>, depth, tv) == True{} : Bool}, +pp: {AR.perfect(U32, depth, tp) == True{} : Bool}, +pn: {AR.perfect(U32, depth, tn) == True{} : Bool}, +hf: {Nat.is_le(fresh, SC.pow2(depth)) == True{} : Bool}, +hl: {ST.alllt(ord, fresh) == True{} : Bool}, +hn: {ST.nodup(ord) == True{} : Bool}, +hv: {ST.lv(T, fresh, AR.slots(Maybe<&2, T>, tv), 0n, ord) == True{} : Bool}, +hk: {ST.lk(ord, D.nil(), D.nil(), AR.slots(U32, tp), AR.slots(U32, tn)) == True{} : Bool}) -> {ST.good(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}) == True{} : Bool}:
  L.and_intro(Nat.is_le(depth, 31n), rest1(~T, tag, fresh, depth, tv, tp, tn, ord), hd,
    L.and_intro(AR.perfect(Maybe<&2, T>, depth, tv), c2(~T, tag, fresh, depth, tv, tp, tn, ord), pv,
      L.and_intro(AR.perfect(U32, depth, tp), c3(~T, tag, fresh, depth, tv, tp, tn, ord), pp,
        L.and_intro(AR.perfect(U32, depth, tn), c4(~T, tag, fresh, depth, tv, tp, tn, ord), pn,
          L.and_intro(Nat.is_le(fresh, SC.pow2(depth)), c5(~T, tag, fresh, depth, tv, tp, tn, ord), hf,
            L.and_intro(ST.alllt(ord, fresh), c6(~T, tag, fresh, depth, tv, tp, tn, ord), hl,
              L.and_intro(ST.nodup(ord), c7(~T, tag, fresh, depth, tv, tp, tn, ord), hn,
                L.and_intro(ST.lv(T, fresh, AR.slots(Maybe<&2, T>, tv), 0n, ord), ST.lk(ord, D.nil(), D.nil(), AR.slots(U32, tp), AR.slots(U32, tn)), hv, hk))))))))

# ---- ids and links ----

def u32_eq_nat(+a: U32, +b: U32) -> {U32.is_eq(a, b) == Nat.is_eq(U32.to_nat(a), U32.to_nat(b)) : Bool}:
  Equal.cong(Cmp, Bool, c => Cmp.is_eq(c), U32.cmp(a, b), Nat.cmp(U32.to_nat(a), U32.to_nat(b)), U.u32_cmp(a, b))

# p < 2^depth, depth <= 31: the id and its link are exact.
def id_nat(+p: Nat, +depth: Nat, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +hp: {Nat.is_lt(p, SC.pow2(depth)) == True{} : Bool}) -> {U32.to_nat(U32.from_nat(p)) == p : Nat}:
  IX.nat_round(p, depth, N.le_trans(depth, 31n, 32n, hd, N.le_succ(31n)), hp)

def ln_nat(+p: Nat, +depth: Nat, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +hp: {Nat.is_lt(p, SC.pow2(depth)) == True{} : Bool}) -> {U32.to_nat(ST.ln(p)) == 1n+p : Nat}:
  IX.nat_round(1n+p, 1n+depth, hd, N.le_lt_trans(1n+p, SC.pow2(depth), SC.pow2(1n+depth), N.lt_succ_le_succ(p, SC.pow2(depth), hp), N.pow2_lt_succ(depth)))

# A link is never nil.
def ln_ne_nil(+p: Nat, +depth: Nat, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +hp: {Nat.is_lt(p, SC.pow2(depth)) == True{} : Bool}) -> {U32.is_eq(ST.ln(p), D.nil()) == False{} : Bool}:
  Equal.trans(Bool, U32.is_eq(ST.ln(p), D.nil()), Nat.is_eq(U32.to_nat(ST.ln(p)), U32.to_nat(D.nil())), False{},
    u32_eq_nat(ST.ln(p), D.nil()),
    L.subst(Nat, z => {Nat.is_eq(z, U32.to_nat(D.nil())) == False{} : Bool}, 1n+p, U32.to_nat(ST.ln(p)), Equal.sym(Nat, U32.to_nat(ST.ln(p)), 1n+p, ln_nat(p, depth, hd, hp)), {==}))

# Following a link: slot(ln p) is the id p.
def slot_ln(+p: Nat, +depth: Nat, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +hp: {Nat.is_lt(p, SC.pow2(depth)) == True{} : Bool}) -> {D.slot(ST.ln(p)) == U32.from_nat(p) : U32}:
  Equal.trans(U32, U32.sub(U32.from_nat(1n+p), 1), U32.from_nat(Nat.sub(1n+p, 1n)), U32.from_nat(p),
    IX.sub_one(1n+p, 1n+depth, hd, N.le_lt_trans(1n+p, SC.pow2(depth), SC.pow2(1n+depth), N.lt_succ_le_succ(p, SC.pow2(depth), hp), N.pow2_lt_succ(depth)), N.lt_succ_le_succ(0n, 1n+p, {==})),
    Equal.cong(Nat, U32, z => U32.from_nat(z), Nat.sub(1n+p, 1n), p, N.sub_zero(p)))

# The link to a runtime id x that stands for p.
def link_ln(+x: U32, +p: Nat, +ex: {x == U32.from_nat(p) : U32}) -> {D.link(x) == ST.ln(p) : U32}:
  Equal.trans(U32, U32.inc(x), U32.inc(U32.from_nat(p)), ST.ln(p), Equal.cong(U32, U32, z => U32.inc(z), x, U32.from_nat(p), ex), IX.inc_bridge(p))

# A U32 below 2^depth is the id of its value.
def u32_id(+x: U32, +depth: Nat, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +hx: {Nat.is_lt(U32.to_nat(x), SC.pow2(depth)) == True{} : Bool}) -> {x == U32.from_nat(U32.to_nat(x)) : U32}:
  U.injective(x, U32.from_nat(U32.to_nat(x)), Equal.sym(Nat, U32.to_nat(U32.from_nat(U32.to_nat(x))), U32.to_nat(x), id_nat(U32.to_nat(x), depth, hd, hx)))
