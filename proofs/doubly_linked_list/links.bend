import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../spec/common.bend as SC
import ../math/u32div.bend as UD
import ../hash_table/table.bend as TB
import ../hash_table/state.bend as HT
import ../hash_table/insa.bend as IA
import ../lru/state.bend as LST
import ../lru/dll.bend as DL
import ../lru/lists.bend as LS
import ./state.bend as ST

# Segments of the two link lists: writes off a segment leave it, a segment
# splits at an append, and its ends can be re-targeted.


def seg_c(+pl1: List<&2, U32>, +nl1: List<&2, U32>, +pl2: List<&2, U32>, +nl2: List<&2, U32>, +s: Nat, +t: List<&2, Nat>, +p: U32, +q: U32, +e0: {TB.nth0(pl1, s) == TB.nth0(pl2, s) : U32}, +e1: {TB.nth0(nl1, s) == TB.nth0(nl2, s) : U32}, +ec: {ST.seg(pl1, nl1, t, LST.lnk(s), q) == ST.seg(pl2, nl2, t, LST.lnk(s), q) : Bool}) -> {ST.seg(pl1, nl1, Con{s, t}, p, q) == ST.seg(pl2, nl2, Con{s, t}, p, q) : Bool}:
  +r1 = L.subst(U32, z => {Bool.and(U32.is_eq(z, p), Bool.and(U32.is_eq(TB.nth0(nl2, s), LST.fst_or(t, q)), ST.seg(pl2, nl2, t, LST.lnk(s), q))) == ST.seg(pl2, nl2, Con{s, t}, p, q) : Bool}, TB.nth0(pl2, s), TB.nth0(pl1, s), Equal.sym(U32, TB.nth0(pl1, s), TB.nth0(pl2, s), e0), {==})
  +r2 = L.subst(U32, z => {Bool.and(U32.is_eq(TB.nth0(pl1, s), p), Bool.and(U32.is_eq(z, LST.fst_or(t, q)), ST.seg(pl2, nl2, t, LST.lnk(s), q))) == ST.seg(pl2, nl2, Con{s, t}, p, q) : Bool}, TB.nth0(nl2, s), TB.nth0(nl1, s), Equal.sym(U32, TB.nth0(nl1, s), TB.nth0(nl2, s), e1), r1)
  L.subst(Bool, z => {Bool.and(U32.is_eq(TB.nth0(pl1, s), p), Bool.and(U32.is_eq(TB.nth0(nl1, s), LST.fst_or(t, q)), z)) == ST.seg(pl2, nl2, Con{s, t}, p, q) : Bool}, ST.seg(pl2, nl2, t, LST.lnk(s), q), ST.seg(pl1, nl1, t, LST.lnk(s), q), Equal.sym(Bool, ST.seg(pl1, nl1, t, LST.lnk(s), q), ST.seg(pl2, nl2, t, LST.lnk(s), q), ec), r2)


# a write to the prev list off the segment leaves it
def seg_fp(+pl: List<&2, U32>, +nl: List<&2, U32>, +y: Nat, +v: U32, +xs: List<&2, Nat>, +p: U32, +q: U32, +hy: {HT.memn(y, xs) == False{} : Bool}) -> {ST.seg(SC.update(U32, pl, y, v), nl, xs, p, q) == ST.seg(pl, nl, xs, p, q) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+s, +t}:
      seg_c(SC.update(U32, pl, y, v), nl, pl, nl, s, t, p, q, IA.nth0_upd_other(pl, y, s, v, DL.ne_sym(s, y, DL.or_ff_l(Nat.is_eq(s, y), HT.memn(y, t), hy))), {==}, seg_fp(pl, nl, y, v, t, LST.lnk(s), q, DL.or_ff_r(Nat.is_eq(s, y), HT.memn(y, t), hy)))

# a write to the next list off the segment leaves it
def seg_fn(+pl: List<&2, U32>, +nl: List<&2, U32>, +y: Nat, +v: U32, +xs: List<&2, Nat>, +p: U32, +q: U32, +hy: {HT.memn(y, xs) == False{} : Bool}) -> {ST.seg(pl, SC.update(U32, nl, y, v), xs, p, q) == ST.seg(pl, nl, xs, p, q) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+s, +t}:
      seg_c(pl, SC.update(U32, nl, y, v), pl, nl, s, t, p, q, {==}, IA.nth0_upd_other(nl, y, s, v, DL.ne_sym(s, y, DL.or_ff_l(Nat.is_eq(s, y), HT.memn(y, t), hy))), seg_fn(pl, nl, y, v, t, LST.lnk(s), q, DL.or_ff_r(Nat.is_eq(s, y), HT.memn(y, t), hy)))

# a write to the next list off the free stack leaves it
def fll_fn(+nl: List<&2, U32>, +y: Nat, +v: U32, +fl: List<&2, Nat>, +hy: {HT.memn(y, fl) == False{} : Bool}) -> {ST.fll(SC.update(U32, nl, y, v), fl) == ST.fll(nl, fl) : Bool}:
  match fl:
    case Nil{}:
      {==}
    case Con{+s, +t}:
      +e1 = IA.nth0_upd_other(nl, y, s, v, DL.ne_sym(s, y, DL.or_ff_l(Nat.is_eq(s, y), HT.memn(y, t), hy)))
      +ih = fll_fn(nl, y, v, t, DL.or_ff_r(Nat.is_eq(s, y), HT.memn(y, t), hy))
      +r1 = L.subst(U32, z => {Bool.and(U32.is_eq(z, LST.fst_or(t, 0)), ST.fll(nl, t)) == ST.fll(nl, Con{s, t}) : Bool}, TB.nth0(nl, s), TB.nth0(SC.update(U32, nl, y, v), s), Equal.sym(U32, TB.nth0(SC.update(U32, nl, y, v), s), TB.nth0(nl, s), e1), {==})
      L.subst(Bool, z => {Bool.and(U32.is_eq(TB.nth0(SC.update(U32, nl, y, v), s), LST.fst_or(t, 0)), z) == ST.fll(nl, Con{s, t}) : Bool}, ST.fll(nl, t), ST.fll(SC.update(U32, nl, y, v), t), Equal.sym(Bool, ST.fll(SC.update(U32, nl, y, v), t), ST.fll(nl, t), ih), r1)

# a segment splits at an append
def seg_app(+pl: List<&2, U32>, +nl: List<&2, U32>, +a: List<&2, Nat>, +b: List<&2, Nat>, +p: U32, +q: U32) -> {ST.seg(pl, nl, SC.append(Nat, a, b), p, q) == Bool.and(ST.seg(pl, nl, a, p, LST.fst_or(b, q)), ST.seg(pl, nl, b, LST.last_or(a, p), q)) : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      +E0 = U32.is_eq(TB.nth0(pl, h), p)
      +F = LST.fst_or(b, q)
      +Y = ST.seg(pl, nl, t, LST.lnk(h), F)
      +Z = ST.seg(pl, nl, b, LST.last_or(t, LST.lnk(h)), q)
      +e1 = Equal.cong(U32, Bool, z => Bool.and(E0, Bool.and(U32.is_eq(TB.nth0(nl, h), z), ST.seg(pl, nl, SC.append(Nat, t, b), LST.lnk(h), q))), LST.fst_or(SC.append(Nat, t, b), q), LST.fst_or(t, F), DL.fst_app(t, b, q))
      +e2 = Equal.cong(Bool, Bool, z => Bool.and(E0, Bool.and(U32.is_eq(TB.nth0(nl, h), LST.fst_or(t, F)), z)), ST.seg(pl, nl, SC.append(Nat, t, b), LST.lnk(h), q), Bool.and(Y, Z), seg_app(pl, nl, t, b, LST.lnk(h), q))
      Equal.trans(Bool, ST.seg(pl, nl, SC.append(Nat, Con{h, t}, b), p, q), Bool.and(E0, Bool.and(U32.is_eq(TB.nth0(nl, h), LST.fst_or(t, F)), ST.seg(pl, nl, SC.append(Nat, t, b), LST.lnk(h), q))), Bool.and(Bool.and(E0, Bool.and(U32.is_eq(TB.nth0(nl, h), LST.fst_or(t, F)), Y)), Z), e1, Equal.trans(Bool, Bool.and(E0, Bool.and(U32.is_eq(TB.nth0(nl, h), LST.fst_or(t, F)), ST.seg(pl, nl, SC.append(Nat, t, b), LST.lnk(h), q))), Bool.and(E0, Bool.and(U32.is_eq(TB.nth0(nl, h), LST.fst_or(t, F)), Bool.and(Y, Z))), Bool.and(Bool.and(E0, Bool.and(U32.is_eq(TB.nth0(nl, h), LST.fst_or(t, F)), Y)), Z), e2, DL.and3(E0, U32.is_eq(TB.nth0(nl, h), LST.fst_or(t, F)), Y, Z)))

# re-target the last id's next
def segq(+pl: List<&2, U32>, +nl: List<&2, U32>, +t: List<&2, Nat>, +a: Nat, +p: U32, +x: U32, +y: U32, +hs: {ST.seg(pl, nl, Con{a, t}, p, x) == True{} : Bool}, +hn: {LST.nodupn(Con{a, t}) == True{} : Bool}, +hl: {Nat.is_lt(DL.lastn(t, a), SC.length(U32, nl)) == True{} : Bool}) -> {ST.seg(pl, SC.update(U32, nl, DL.lastn(t, a), y), Con{a, t}, p, y) == True{} : Bool}:
  match t:
    case Nil{}:
      +h0 = L.and_left(U32.is_eq(TB.nth0(pl, a), p), Bool.and(U32.is_eq(TB.nth0(nl, a), x), True{}), hs)
      +h1b = L.subst(U32, z => {U32.is_eq(z, y) == True{} : Bool}, y, TB.nth0(SC.update(U32, nl, a, y), a), Equal.sym(U32, TB.nth0(SC.update(U32, nl, a, y), a), y, IA.nth0_upd_same(nl, a, y, hl)), DL.u_refl(y))
      L.and_intro(U32.is_eq(TB.nth0(pl, a), p), Bool.and(U32.is_eq(TB.nth0(SC.update(U32, nl, a, y), a), y), True{}), h0, L.and_intro(U32.is_eq(TB.nth0(SC.update(U32, nl, a, y), a), y), True{}, h1b, {==}))
    case Con{+b, +t2}:
      +z = DL.lastn(t2, b)
      +hna = L.and_left(Bool.not(HT.memn(a, Con{b, t2})), LST.nodupn(Con{b, t2}), hn)
      +hza = DL.ne_mem(a, z, Con{b, t2}, hna, DL.lastn_mem(t2, b))
      +e1 = IA.nth0_upd_other(nl, z, a, y, hza)
      +h0 = L.and_left(U32.is_eq(TB.nth0(pl, a), p), Bool.and(U32.is_eq(TB.nth0(nl, a), LST.lnk(b)), ST.seg(pl, nl, Con{b, t2}, LST.lnk(a), x)), hs)
      +hr = L.and_right(U32.is_eq(TB.nth0(pl, a), p), Bool.and(U32.is_eq(TB.nth0(nl, a), LST.lnk(b)), ST.seg(pl, nl, Con{b, t2}, LST.lnk(a), x)), hs)
      +h1 = L.and_left(U32.is_eq(TB.nth0(nl, a), LST.lnk(b)), ST.seg(pl, nl, Con{b, t2}, LST.lnk(a), x), hr)
      +hst = L.and_right(U32.is_eq(TB.nth0(nl, a), LST.lnk(b)), ST.seg(pl, nl, Con{b, t2}, LST.lnk(a), x), hr)
      +h1b = L.subst(U32, w => {U32.is_eq(w, LST.lnk(b)) == True{} : Bool}, TB.nth0(nl, a), TB.nth0(SC.update(U32, nl, z, y), a), Equal.sym(U32, TB.nth0(SC.update(U32, nl, z, y), a), TB.nth0(nl, a), e1), h1)
      L.and_intro(U32.is_eq(TB.nth0(pl, a), p), Bool.and(U32.is_eq(TB.nth0(SC.update(U32, nl, z, y), a), LST.lnk(b)), ST.seg(pl, SC.update(U32, nl, z, y), Con{b, t2}, LST.lnk(a), y)), h0, L.and_intro(U32.is_eq(TB.nth0(SC.update(U32, nl, z, y), a), LST.lnk(b)), ST.seg(pl, SC.update(U32, nl, z, y), Con{b, t2}, LST.lnk(a), y), h1b, segq(pl, nl, t2, b, LST.lnk(a), x, y, hst, L.and_right(Bool.not(HT.memn(a, Con{b, t2})), LST.nodupn(Con{b, t2}), hn), hl)))

# re-target the first id's prev
def segp(+pl: List<&2, U32>, +nl: List<&2, U32>, +b: Nat, +t: List<&2, Nat>, +x: U32, +q: U32, +y: U32, +hs: {ST.seg(pl, nl, Con{b, t}, x, q) == True{} : Bool}, +hn: {LST.nodupn(Con{b, t}) == True{} : Bool}, +hl: {Nat.is_lt(b, SC.length(U32, pl)) == True{} : Bool}) -> {ST.seg(SC.update(U32, pl, b, y), nl, Con{b, t}, y, q) == True{} : Bool}:
  +p2 = SC.update(U32, pl, b, y)
  +hr = L.and_right(U32.is_eq(TB.nth0(pl, b), x), Bool.and(U32.is_eq(TB.nth0(nl, b), LST.fst_or(t, q)), ST.seg(pl, nl, t, LST.lnk(b), q)), hs)
  +h1 = L.and_left(U32.is_eq(TB.nth0(nl, b), LST.fst_or(t, q)), ST.seg(pl, nl, t, LST.lnk(b), q), hr)
  +hst = L.and_right(U32.is_eq(TB.nth0(nl, b), LST.fst_or(t, q)), ST.seg(pl, nl, t, LST.lnk(b), q), hr)
  +hbt = LS.not_t_f(HT.memn(b, t), L.and_left(Bool.not(HT.memn(b, t)), LST.nodupn(t), hn))
  +h0b = L.subst(U32, w => {U32.is_eq(w, y) == True{} : Bool}, y, TB.nth0(p2, b), Equal.sym(U32, TB.nth0(p2, b), y, IA.nth0_upd_same(pl, b, y, hl)), DL.u_refl(y))
  +hstb = L.subst(Bool, w => {w == True{} : Bool}, ST.seg(pl, nl, t, LST.lnk(b), q), ST.seg(p2, nl, t, LST.lnk(b), q), Equal.sym(Bool, ST.seg(p2, nl, t, LST.lnk(b), q), ST.seg(pl, nl, t, LST.lnk(b), q), seg_fp(pl, nl, b, y, t, LST.lnk(b), q, hbt)), hst)
  L.and_intro(U32.is_eq(TB.nth0(p2, b), y), Bool.and(U32.is_eq(TB.nth0(nl, b), LST.fst_or(t, q)), ST.seg(p2, nl, t, LST.lnk(b), q)), h0b, L.and_intro(U32.is_eq(TB.nth0(nl, b), LST.fst_or(t, q)), ST.seg(p2, nl, t, LST.lnk(b), q), h1, hstb))
