import Base
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../../lib/spec_common.bend as SC
import ./spec.bend as SP
import ../../lib/u32div.bend as UD
import ../../../src/math/u64.bend as W
import ../../../src/containers/hash_table.bend as H
import ../hash_table/table.bend as TB
import ../hash_table/buckets.bend as B
import ../hash_table/state.bend as HT
import ./state.bend as ST
import ./idx.bend as ID
import ../../lib/nat_list.bend as NL
import ../../lib/links.bend as LK
import ../../lib/words32.bend as W32

# The recency and free lists under writes to lk: reads after a write, frame
# lemmas, and re-targeting a segment's ends.


# ---- Bool helpers ----








# ---- reads after a write ----

def lw_same(+ll: List<&2, U32>, +y: Nat, +o: Nat, +v: U32, +ho: {Nat.is_lt(o, 8n) == True{} : Bool}, +h: {Nat.is_lt(ST.off(y, o), SC.length(U32, ll)) == True{} : Bool}) -> {ST.lw(SC.update(U32, ll, ST.off(y, o), v), y, o) == v : U32}:
  W32.nth0_upd_same(ll, ST.off(y, o), v, h)

def lw_other(+ll: List<&2, U32>, +y: Nat, +o: Nat, +v: U32, +ho: {Nat.is_lt(o, 8n) == True{} : Bool}, +x: Nat, +o2: Nat, +ho2: {Nat.is_lt(o2, 8n) == True{} : Bool}, +hne: {Bool.or(Bool.not(Nat.is_eq(y, x)), Bool.not(Nat.is_eq(o, o2))) == True{} : Bool}) -> {ST.lw(SC.update(U32, ll, ST.off(y, o), v), x, o2) == ST.lw(ll, x, o2) : U32}:
  W32.nth0_upd_other(ll, ST.off(y, o), ST.off(x, o2), v, ID.off_ne(y, x, o, o2, ho, ho2, hne))

def ne_slot(+y: Nat, +x: Nat, +o: Nat, +o2: Nat, +h: {Nat.is_eq(y, x) == False{} : Bool}) -> {Bool.or(Bool.not(Nat.is_eq(y, x)), Bool.not(Nat.is_eq(o, o2))) == True{} : Bool}:
  NL.or_tl(Bool.not(Nat.is_eq(y, x)), Bool.not(Nat.is_eq(o, o2)), NL.not_f(Nat.is_eq(y, x), h))

def ne_word(+y: Nat, +x: Nat, +o: Nat, +o2: Nat, +h: {Nat.is_eq(o, o2) == False{} : Bool}) -> {Bool.or(Bool.not(Nat.is_eq(y, x)), Bool.not(Nat.is_eq(o, o2))) == True{} : Bool}:
  NL.or_tr(Bool.not(Nat.is_eq(y, x)), Bool.not(Nat.is_eq(o, o2)), NL.not_f(Nat.is_eq(o, o2), h))

# a link word (o < 2) is not a data word (2 <= o2)
def lo_hi(+o: Nat, +h01: {Nat.is_lt(o, 2n) == True{} : Bool}, +o2: Nat, +h2: {Nat.is_le(2n, o2) == True{} : Bool}) -> {Nat.is_eq(o, o2) == False{} : Bool}:
  N.is_eq_lt(o, o2, N.lt_le_trans(o, 2n, o2, h01, h2))

# y differs from x

# ---- segments ----

def seg_c(+l1: List<&2, U32>, +l2: List<&2, U32>, +s: Nat, +t: List<&2, Nat>, +p: U32, +q: U32, +e0: {ST.lw(l1, s, 0n) == ST.lw(l2, s, 0n) : U32}, +e1: {ST.lw(l1, s, 1n) == ST.lw(l2, s, 1n) : U32}, +ec: {ST.seg(l1, t, LK.lnk(s), q) == ST.seg(l2, t, LK.lnk(s), q) : Bool}) -> {ST.seg(l1, Con{s, t}, p, q) == ST.seg(l2, Con{s, t}, p, q) : Bool}:
  +r1 = L.subst(U32, z => {Bool.and(U32.is_eq(z, p), Bool.and(U32.is_eq(ST.lw(l2, s, 1n), LK.fst_or(t, q)), ST.seg(l2, t, LK.lnk(s), q))) == ST.seg(l2, Con{s, t}, p, q) : Bool}, ST.lw(l2, s, 0n), ST.lw(l1, s, 0n), Equal.sym(U32, ST.lw(l1, s, 0n), ST.lw(l2, s, 0n), e0), {==})
  +r2 = L.subst(U32, z => {Bool.and(U32.is_eq(ST.lw(l1, s, 0n), p), Bool.and(U32.is_eq(z, LK.fst_or(t, q)), ST.seg(l2, t, LK.lnk(s), q))) == ST.seg(l2, Con{s, t}, p, q) : Bool}, ST.lw(l2, s, 1n), ST.lw(l1, s, 1n), Equal.sym(U32, ST.lw(l1, s, 1n), ST.lw(l2, s, 1n), e1), r1)
  L.subst(Bool, z => {Bool.and(U32.is_eq(ST.lw(l1, s, 0n), p), Bool.and(U32.is_eq(ST.lw(l1, s, 1n), LK.fst_or(t, q)), z)) == ST.seg(l2, Con{s, t}, p, q) : Bool}, ST.seg(l2, t, LK.lnk(s), q), ST.seg(l1, t, LK.lnk(s), q), Equal.sym(Bool, ST.seg(l1, t, LK.lnk(s), q), ST.seg(l2, t, LK.lnk(s), q), ec), r2)

# a write to a slot off the segment leaves it
def seg_fs(+ll: List<&2, U32>, +y: Nat, +o: Nat, +v: U32, +ho: {Nat.is_lt(o, 8n) == True{} : Bool}, +sl: List<&2, Nat>, +p: U32, +q: U32, +hy: {NL.memn(y, sl) == False{} : Bool}) -> {ST.seg(SC.update(U32, ll, ST.off(y, o), v), sl, p, q) == ST.seg(ll, sl, p, q) : Bool}:
  match sl:
    case Nil{}:
      {==}
    case Con{+s, +t}:
      +hys = NL.ne_sym(s, y, NL.or_ff_l(Nat.is_eq(s, y), NL.memn(y, t), hy))
      seg_c(SC.update(U32, ll, ST.off(y, o), v), ll, s, t, p, q, lw_other(ll, y, o, v, ho, s, 0n, {==}, ne_slot(y, s, o, 0n, hys)), lw_other(ll, y, o, v, ho, s, 1n, {==}, ne_slot(y, s, o, 1n, hys)), seg_fs(ll, y, o, v, ho, t, LK.lnk(s), q, NL.or_ff_r(Nat.is_eq(s, y), NL.memn(y, t), hy)))



# a segment splits at an append
def seg_app(+ll: List<&2, U32>, +a: List<&2, Nat>, +b: List<&2, Nat>, +p: U32, +q: U32) -> {ST.seg(ll, SC.append(Nat, a, b), p, q) == Bool.and(ST.seg(ll, a, p, LK.fst_or(b, q)), ST.seg(ll, b, LK.last_or(a, p), q)) : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      +E0 = U32.is_eq(ST.lw(ll, h, 0n), p)
      +F = LK.fst_or(b, q)
      +Y = ST.seg(ll, t, LK.lnk(h), F)
      +Z = ST.seg(ll, b, LK.last_or(t, LK.lnk(h)), q)
      +e1 = Equal.cong(U32, Bool, z => Bool.and(E0, Bool.and(U32.is_eq(ST.lw(ll, h, 1n), z), ST.seg(ll, SC.append(Nat, t, b), LK.lnk(h), q))), LK.fst_or(SC.append(Nat, t, b), q), LK.fst_or(t, F), LK.fst_app(t, b, q))
      +e2 = Equal.cong(Bool, Bool, z => Bool.and(E0, Bool.and(U32.is_eq(ST.lw(ll, h, 1n), LK.fst_or(t, F)), z)), ST.seg(ll, SC.append(Nat, t, b), LK.lnk(h), q), Bool.and(Y, Z), seg_app(ll, t, b, LK.lnk(h), q))
      Equal.trans(Bool, ST.seg(ll, SC.append(Nat, Con{h, t}, b), p, q), Bool.and(E0, Bool.and(U32.is_eq(ST.lw(ll, h, 1n), LK.fst_or(t, F)), ST.seg(ll, SC.append(Nat, t, b), LK.lnk(h), q))), Bool.and(Bool.and(E0, Bool.and(U32.is_eq(ST.lw(ll, h, 1n), LK.fst_or(t, F)), Y)), Z), e1, Equal.trans(Bool, Bool.and(E0, Bool.and(U32.is_eq(ST.lw(ll, h, 1n), LK.fst_or(t, F)), ST.seg(ll, SC.append(Nat, t, b), LK.lnk(h), q))), Bool.and(E0, Bool.and(U32.is_eq(ST.lw(ll, h, 1n), LK.fst_or(t, F)), Bool.and(Y, Z))), Bool.and(Bool.and(E0, Bool.and(U32.is_eq(ST.lw(ll, h, 1n), LK.fst_or(t, F)), Y)), Z), e2, NL.and3(E0, U32.is_eq(ST.lw(ll, h, 1n), LK.fst_or(t, F)), Y, Z)))

# the last slot of a, t after a




# a member differs from a non-member

# re-target the last slot's next
def segq(+ll: List<&2, U32>, +t: List<&2, Nat>, +a: Nat, +p: U32, +x: U32, +y: U32, +hs: {ST.seg(ll, Con{a, t}, p, x) == True{} : Bool}, +hn: {NL.nodupn(Con{a, t}) == True{} : Bool}, +hl: {Nat.is_lt(ST.off(NL.lastn(t, a), 1n), SC.length(U32, ll)) == True{} : Bool}) -> {ST.seg(SC.update(U32, ll, ST.off(NL.lastn(t, a), 1n), y), Con{a, t}, p, y) == True{} : Bool}:
  match t:
    case Nil{}:
      +e0 = lw_other(ll, a, 1n, y, {==}, a, 0n, {==}, ne_word(a, a, 1n, 0n, {==}))
      +h0 = L.and_left(U32.is_eq(ST.lw(ll, a, 0n), p), Bool.and(U32.is_eq(ST.lw(ll, a, 1n), x), True{}), hs)
      +h0b = L.subst(U32, z => {U32.is_eq(z, p) == True{} : Bool}, ST.lw(ll, a, 0n), ST.lw(SC.update(U32, ll, ST.off(a, 1n), y), a, 0n), Equal.sym(U32, ST.lw(SC.update(U32, ll, ST.off(a, 1n), y), a, 0n), ST.lw(ll, a, 0n), e0), h0)
      +h1b = L.subst(U32, z => {U32.is_eq(z, y) == True{} : Bool}, y, ST.lw(SC.update(U32, ll, ST.off(a, 1n), y), a, 1n), Equal.sym(U32, ST.lw(SC.update(U32, ll, ST.off(a, 1n), y), a, 1n), y, lw_same(ll, a, 1n, y, {==}, hl)), LK.u_refl(y))
      L.and_intro(U32.is_eq(ST.lw(SC.update(U32, ll, ST.off(a, 1n), y), a, 0n), p), Bool.and(U32.is_eq(ST.lw(SC.update(U32, ll, ST.off(a, 1n), y), a, 1n), y), True{}), h0b, L.and_intro(U32.is_eq(ST.lw(SC.update(U32, ll, ST.off(a, 1n), y), a, 1n), y), True{}, h1b, {==}))
    case Con{+b, +t2}:
      +z = NL.lastn(t2, b)
      +hna = L.and_left(Bool.not(NL.memn(a, Con{b, t2})), NL.nodupn(Con{b, t2}), hn)
      +hza = NL.ne_mem(a, z, Con{b, t2}, hna, NL.lastn_mem(t2, b))
      +e0 = lw_other(ll, z, 1n, y, {==}, a, 0n, {==}, ne_slot(z, a, 1n, 0n, hza))
      +e1 = lw_other(ll, z, 1n, y, {==}, a, 1n, {==}, ne_slot(z, a, 1n, 1n, hza))
      +h0 = L.and_left(U32.is_eq(ST.lw(ll, a, 0n), p), Bool.and(U32.is_eq(ST.lw(ll, a, 1n), LK.lnk(b)), ST.seg(ll, Con{b, t2}, LK.lnk(a), x)), hs)
      +hr = L.and_right(U32.is_eq(ST.lw(ll, a, 0n), p), Bool.and(U32.is_eq(ST.lw(ll, a, 1n), LK.lnk(b)), ST.seg(ll, Con{b, t2}, LK.lnk(a), x)), hs)
      +h1 = L.and_left(U32.is_eq(ST.lw(ll, a, 1n), LK.lnk(b)), ST.seg(ll, Con{b, t2}, LK.lnk(a), x), hr)
      +hst = L.and_right(U32.is_eq(ST.lw(ll, a, 1n), LK.lnk(b)), ST.seg(ll, Con{b, t2}, LK.lnk(a), x), hr)
      +h0b = L.subst(U32, w => {U32.is_eq(w, p) == True{} : Bool}, ST.lw(ll, a, 0n), ST.lw(SC.update(U32, ll, ST.off(z, 1n), y), a, 0n), Equal.sym(U32, ST.lw(SC.update(U32, ll, ST.off(z, 1n), y), a, 0n), ST.lw(ll, a, 0n), e0), h0)
      +h1b = L.subst(U32, w => {U32.is_eq(w, LK.lnk(b)) == True{} : Bool}, ST.lw(ll, a, 1n), ST.lw(SC.update(U32, ll, ST.off(z, 1n), y), a, 1n), Equal.sym(U32, ST.lw(SC.update(U32, ll, ST.off(z, 1n), y), a, 1n), ST.lw(ll, a, 1n), e1), h1)
      L.and_intro(U32.is_eq(ST.lw(SC.update(U32, ll, ST.off(z, 1n), y), a, 0n), p), Bool.and(U32.is_eq(ST.lw(SC.update(U32, ll, ST.off(z, 1n), y), a, 1n), LK.lnk(b)), ST.seg(SC.update(U32, ll, ST.off(z, 1n), y), Con{b, t2}, LK.lnk(a), y)), h0b, L.and_intro(U32.is_eq(ST.lw(SC.update(U32, ll, ST.off(z, 1n), y), a, 1n), LK.lnk(b)), ST.seg(SC.update(U32, ll, ST.off(z, 1n), y), Con{b, t2}, LK.lnk(a), y), h1b, segq(ll, t2, b, LK.lnk(a), x, y, hst, L.and_right(Bool.not(NL.memn(a, Con{b, t2})), NL.nodupn(Con{b, t2}), hn), hl)))

# re-target the first slot's prev
def segp(+ll: List<&2, U32>, +b: Nat, +t: List<&2, Nat>, +x: U32, +q: U32, +y: U32, +hs: {ST.seg(ll, Con{b, t}, x, q) == True{} : Bool}, +hn: {NL.nodupn(Con{b, t}) == True{} : Bool}, +hl: {Nat.is_lt(ST.off(b, 0n), SC.length(U32, ll)) == True{} : Bool}) -> {ST.seg(SC.update(U32, ll, ST.off(b, 0n), y), Con{b, t}, y, q) == True{} : Bool}:
  +l2 = SC.update(U32, ll, ST.off(b, 0n), y)
  +hr = L.and_right(U32.is_eq(ST.lw(ll, b, 0n), x), Bool.and(U32.is_eq(ST.lw(ll, b, 1n), LK.fst_or(t, q)), ST.seg(ll, t, LK.lnk(b), q)), hs)
  +h1 = L.and_left(U32.is_eq(ST.lw(ll, b, 1n), LK.fst_or(t, q)), ST.seg(ll, t, LK.lnk(b), q), hr)
  +hst = L.and_right(U32.is_eq(ST.lw(ll, b, 1n), LK.fst_or(t, q)), ST.seg(ll, t, LK.lnk(b), q), hr)
  +hbt = L.not_true(NL.memn(b, t), L.and_left(Bool.not(NL.memn(b, t)), NL.nodupn(t), hn))
  +h0b = L.subst(U32, w => {U32.is_eq(w, y) == True{} : Bool}, y, ST.lw(l2, b, 0n), Equal.sym(U32, ST.lw(l2, b, 0n), y, lw_same(ll, b, 0n, y, {==}, hl)), LK.u_refl(y))
  +h1b = L.subst(U32, w => {U32.is_eq(w, LK.fst_or(t, q)) == True{} : Bool}, ST.lw(ll, b, 1n), ST.lw(l2, b, 1n), Equal.sym(U32, ST.lw(l2, b, 1n), ST.lw(ll, b, 1n), lw_other(ll, b, 0n, y, {==}, b, 1n, {==}, ne_word(b, b, 0n, 1n, {==}))), h1)
  +hstb = L.subst(Bool, w => {w == True{} : Bool}, ST.seg(ll, t, LK.lnk(b), q), ST.seg(l2, t, LK.lnk(b), q), Equal.sym(Bool, ST.seg(l2, t, LK.lnk(b), q), ST.seg(ll, t, LK.lnk(b), q), seg_fs(ll, b, 0n, y, {==}, t, LK.lnk(b), q, hbt)), hst)
  L.and_intro(U32.is_eq(ST.lw(l2, b, 0n), y), Bool.and(U32.is_eq(ST.lw(l2, b, 1n), LK.fst_or(t, q)), ST.seg(l2, t, LK.lnk(b), q)), h0b, L.and_intro(U32.is_eq(ST.lw(l2, b, 1n), LK.fst_or(t, q)), ST.seg(l2, t, LK.lnk(b), q), h1b, hstb))

# ---- the free list ----

def fll_fs(+ll: List<&2, U32>, +y: Nat, +o: Nat, +v: U32, +ho: {Nat.is_lt(o, 8n) == True{} : Bool}, +fl: List<&2, Nat>, +hy: {NL.memn(y, fl) == False{} : Bool}) -> {ST.fll(SC.update(U32, ll, ST.off(y, o), v), fl) == ST.fll(ll, fl) : Bool}:
  match fl:
    case Nil{}:
      {==}
    case Con{+s, +t}:
      +hys = NL.ne_sym(s, y, NL.or_ff_l(Nat.is_eq(s, y), NL.memn(y, t), hy))
      +e1 = lw_other(ll, y, o, v, ho, s, 1n, {==}, ne_slot(y, s, o, 1n, hys))
      +ih = fll_fs(ll, y, o, v, ho, t, NL.or_ff_r(Nat.is_eq(s, y), NL.memn(y, t), hy))
      +r1 = L.subst(U32, z => {Bool.and(U32.is_eq(z, LK.fst_or(t, 0)), ST.fll(ll, t)) == ST.fll(ll, Con{s, t}) : Bool}, ST.lw(ll, s, 1n), ST.lw(SC.update(U32, ll, ST.off(y, o), v), s, 1n), Equal.sym(U32, ST.lw(SC.update(U32, ll, ST.off(y, o), v), s, 1n), ST.lw(ll, s, 1n), e1), {==})
      L.subst(Bool, z => {Bool.and(U32.is_eq(ST.lw(SC.update(U32, ll, ST.off(y, o), v), s, 1n), LK.fst_or(t, 0)), z) == ST.fll(ll, Con{s, t}) : Bool}, ST.fll(ll, t), ST.fll(SC.update(U32, ll, ST.off(y, o), v), t), Equal.sym(Bool, ST.fll(SC.update(U32, ll, ST.off(y, o), v), t), ST.fll(ll, t), ih), r1)

# ---- data words: writes to link words (o < 2) leave them ----


def lw_hi(+ll: List<&2, U32>, +y: Nat, +o: Nat, +v: U32, +ho: {Nat.is_lt(o, 8n) == True{} : Bool}, +h01: {Nat.is_lt(o, 2n) == True{} : Bool}, +x: Nat, +o2: Nat, +ho2: {Nat.is_lt(o2, 8n) == True{} : Bool}, +h2: {Nat.is_le(2n, o2) == True{} : Bool}) -> {ST.lw(SC.update(U32, ll, ST.off(y, o), v), x, o2) == ST.lw(ll, x, o2) : U32}:
  lw_other(ll, y, o, v, ho, x, o2, ho2, ne_word(y, x, o, o2, lo_hi(o, h01, o2, h2)))

def skey_fr(+ll: List<&2, U32>, +y: Nat, +o: Nat, +v: U32, +ho: {Nat.is_lt(o, 8n) == True{} : Bool}, +h01: {Nat.is_lt(o, 2n) == True{} : Bool}, +kl: List<&2, String>, +x: Nat) -> {ST.skey(SC.update(U32, ll, ST.off(y, o), v), kl, x) == ST.skey(ll, kl, x) : String}:
  Equal.cong(U32, String, z => TB.keyof(z, TB.nths(kl, x)), ST.lw(SC.update(U32, ll, ST.off(y, o), v), x, 2n), ST.lw(ll, x, 2n), lw_hi(ll, y, o, v, ho, h01, x, 2n, {==}, {==}))

def sent_fr(~V: Data, +ll: List<&2, U32>, +y: Nat, +o: Nat, +v: U32, +ho: {Nat.is_lt(o, 8n) == True{} : Bool}, +h01: {Nat.is_lt(o, 2n) == True{} : Bool}, +kl: List<&2, String>, +x: Nat, +m: Maybe<&2, V>) -> {ST.sent_m(~V, SC.update(U32, ll, ST.off(y, o), v), kl, x, m) == ST.sent_m(~V, ll, kl, x, m) : List<&2, SP.Ent<V>>}:
  match m:
    case None{}:
      {==}
    case Some{+w}:
      +r1 = L.subst(String, z => {Con{SP.LE{z, w, ST.lw(SC.update(U32, ll, ST.off(y, o), v), x, 3n), W.U64{ST.lw(SC.update(U32, ll, ST.off(y, o), v), x, 4n), ST.lw(SC.update(U32, ll, ST.off(y, o), v), x, 5n)}}, Nil{}} == ST.sent_m(~V, SC.update(U32, ll, ST.off(y, o), v), kl, x, Some{w}) : List<&2, SP.Ent<V>>}, ST.skey(SC.update(U32, ll, ST.off(y, o), v), kl, x), ST.skey(ll, kl, x), skey_fr(ll, y, o, v, ho, h01, kl, x), {==})
      +r2 = L.subst(U32, z => {Con{SP.LE{ST.skey(ll, kl, x), w, z, W.U64{ST.lw(SC.update(U32, ll, ST.off(y, o), v), x, 4n), ST.lw(SC.update(U32, ll, ST.off(y, o), v), x, 5n)}}, Nil{}} == ST.sent_m(~V, SC.update(U32, ll, ST.off(y, o), v), kl, x, Some{w}) : List<&2, SP.Ent<V>>}, ST.lw(SC.update(U32, ll, ST.off(y, o), v), x, 3n), ST.lw(ll, x, 3n), lw_hi(ll, y, o, v, ho, h01, x, 3n, {==}, {==}), r1)
      +r3 = L.subst(U32, z => {Con{SP.LE{ST.skey(ll, kl, x), w, ST.lw(ll, x, 3n), W.U64{z, ST.lw(SC.update(U32, ll, ST.off(y, o), v), x, 5n)}}, Nil{}} == ST.sent_m(~V, SC.update(U32, ll, ST.off(y, o), v), kl, x, Some{w}) : List<&2, SP.Ent<V>>}, ST.lw(SC.update(U32, ll, ST.off(y, o), v), x, 4n), ST.lw(ll, x, 4n), lw_hi(ll, y, o, v, ho, h01, x, 4n, {==}, {==}), r2)
      +r4 = L.subst(U32, z => {Con{SP.LE{ST.skey(ll, kl, x), w, ST.lw(ll, x, 3n), W.U64{ST.lw(ll, x, 4n), z}}, Nil{}} == ST.sent_m(~V, SC.update(U32, ll, ST.off(y, o), v), kl, x, Some{w}) : List<&2, SP.Ent<V>>}, ST.lw(SC.update(U32, ll, ST.off(y, o), v), x, 5n), ST.lw(ll, x, 5n), lw_hi(ll, y, o, v, ho, h01, x, 5n, {==}, {==}), r3)
      Equal.sym(List<&2, SP.Ent<V>>, ST.sent_m(~V, ll, kl, x, Some{w}), ST.sent_m(~V, SC.update(U32, ll, ST.off(y, o), v), kl, x, Some{w}), r4)

def es_fr(~V: Data, +ll: List<&2, U32>, +y: Nat, +o: Nat, +v: U32, +ho: {Nat.is_lt(o, 8n) == True{} : Bool}, +h01: {Nat.is_lt(o, 2n) == True{} : Bool}, +kl: List<&2, String>, +el: List<&2, Maybe<&2, V>>, +sl: List<&2, Nat>) -> {ST.es(~V, SC.update(U32, ll, ST.off(y, o), v), kl, el, sl) == ST.es(~V, ll, kl, el, sl) : List<&2, SP.Ent<V>>}:
  match sl:
    case Nil{}:
      {==}
    case Con{+s, +t}:
      +m = HT.nthm(~V, el, s)
      +a = Equal.cong(List<&2, SP.Ent<V>>, List<&2, SP.Ent<V>>, z => SC.append(SP.Ent<V>, z, ST.es(~V, SC.update(U32, ll, ST.off(y, o), v), kl, el, t)), ST.sent_m(~V, SC.update(U32, ll, ST.off(y, o), v), kl, s, m), ST.sent_m(~V, ll, kl, s, m), sent_fr(~V, ll, y, o, v, ho, h01, kl, s, m))
      Equal.trans(List<&2, SP.Ent<V>>, SC.append(SP.Ent<V>, ST.sent_m(~V, SC.update(U32, ll, ST.off(y, o), v), kl, s, m), ST.es(~V, SC.update(U32, ll, ST.off(y, o), v), kl, el, t)), SC.append(SP.Ent<V>, ST.sent_m(~V, ll, kl, s, m), ST.es(~V, SC.update(U32, ll, ST.off(y, o), v), kl, el, t)), SC.append(SP.Ent<V>, ST.sent_m(~V, ll, kl, s, m), ST.es(~V, ll, kl, el, t)), a, Equal.cong(List<&2, SP.Ent<V>>, List<&2, SP.Ent<V>>, z => SC.append(SP.Ent<V>, ST.sent_m(~V, ll, kl, s, m), z), ST.es(~V, SC.update(U32, ll, ST.off(y, o), v), kl, el, t), ST.es(~V, ll, kl, el, t), es_fr(~V, ll, y, o, v, ho, h01, kl, el, t)))

def has_fr(~V: Data, +ll: List<&2, U32>, +y: Nat, +o: Nat, +v: U32, +ho: {Nat.is_lt(o, 8n) == True{} : Bool}, +h01: {Nat.is_lt(o, 2n) == True{} : Bool}, +bs: List<&2, B.Bk>, +m: Nat, +sl: List<&2, Nat>) -> {ST.hasall(~V, bs, m, SC.update(U32, ll, ST.off(y, o), v), sl) == ST.hasall(~V, bs, m, ll, sl) : Bool}:
  match sl:
    case Nil{}:
      {==}
    case Con{+s, +t}:
      +e = Equal.cong(U32, Bool, z => ST.anyb(bs, m, LK.lnk(s), z), ST.lw(SC.update(U32, ll, ST.off(y, o), v), s, 2n), ST.lw(ll, s, 2n), lw_hi(ll, y, o, v, ho, h01, s, 2n, {==}, {==}))
      Equal.trans(Bool, Bool.and(ST.anyb(bs, m, LK.lnk(s), ST.lw(SC.update(U32, ll, ST.off(y, o), v), s, 2n)), ST.hasall(~V, bs, m, SC.update(U32, ll, ST.off(y, o), v), t)), Bool.and(ST.anyb(bs, m, LK.lnk(s), ST.lw(ll, s, 2n)), ST.hasall(~V, bs, m, SC.update(U32, ll, ST.off(y, o), v), t)), Bool.and(ST.anyb(bs, m, LK.lnk(s), ST.lw(ll, s, 2n)), ST.hasall(~V, bs, m, ll, t)), Equal.cong(Bool, Bool, z => Bool.and(z, ST.hasall(~V, bs, m, SC.update(U32, ll, ST.off(y, o), v), t)), ST.anyb(bs, m, LK.lnk(s), ST.lw(SC.update(U32, ll, ST.off(y, o), v), s, 2n)), ST.anyb(bs, m, LK.lnk(s), ST.lw(ll, s, 2n)), e), Equal.cong(Bool, Bool, z => Bool.and(ST.anyb(bs, m, LK.lnk(s), ST.lw(ll, s, 2n)), z), ST.hasall(~V, bs, m, SC.update(U32, ll, ST.off(y, o), v), t), ST.hasall(~V, bs, m, ll, t), has_fr(~V, ll, y, o, v, ho, h01, bs, m, t)))

def bslb_fr(+ll: List<&2, U32>, +y: Nat, +o: Nat, +v: U32, +ho: {Nat.is_lt(o, 8n) == True{} : Bool}, +h01: {Nat.is_lt(o, 2n) == True{} : Bool}, +sl: List<&2, Nat>, +b: B.Bk) -> {ST.bslb(sl, SC.update(U32, ll, ST.off(y, o), v), b) == ST.bslb(sl, ll, b) : Bool}:
  match b:
    case B.BE{}:
      {==}
    case B.BF{+w, +l, +k}:
      Equal.cong(U32, Bool, z => Bool.and(NL.memn(UD.v(H.slot(l)), sl), U32.is_eq(z, w)), ST.lw(SC.update(U32, ll, ST.off(y, o), v), UD.v(H.slot(l)), 2n), ST.lw(ll, UD.v(H.slot(l)), 2n), lw_hi(ll, y, o, v, ho, h01, UD.v(H.slot(l)), 2n, {==}, {==}))

def bsl_fr(+ll: List<&2, U32>, +y: Nat, +o: Nat, +v: U32, +ho: {Nat.is_lt(o, 8n) == True{} : Bool}, +h01: {Nat.is_lt(o, 2n) == True{} : Bool}, +bs: List<&2, B.Bk>, +sl: List<&2, Nat>, +m: Nat) -> {ST.bsl(bs, sl, SC.update(U32, ll, ST.off(y, o), v), m) == ST.bsl(bs, sl, ll, m) : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+j:
      Equal.trans(Bool, Bool.and(ST.bslb(sl, SC.update(U32, ll, ST.off(y, o), v), B.at(bs, j)), ST.bsl(bs, sl, SC.update(U32, ll, ST.off(y, o), v), j)), Bool.and(ST.bslb(sl, ll, B.at(bs, j)), ST.bsl(bs, sl, SC.update(U32, ll, ST.off(y, o), v), j)), Bool.and(ST.bslb(sl, ll, B.at(bs, j)), ST.bsl(bs, sl, ll, j)), Equal.cong(Bool, Bool, z => Bool.and(z, ST.bsl(bs, sl, SC.update(U32, ll, ST.off(y, o), v), j)), ST.bslb(sl, SC.update(U32, ll, ST.off(y, o), v), B.at(bs, j)), ST.bslb(sl, ll, B.at(bs, j)), bslb_fr(ll, y, o, v, ho, h01, sl, B.at(bs, j))), Equal.cong(Bool, Bool, z => Bool.and(ST.bslb(sl, ll, B.at(bs, j)), z), ST.bsl(bs, sl, SC.update(U32, ll, ST.off(y, o), v), j), ST.bsl(bs, sl, ll, j), bsl_fr(ll, y, o, v, ho, h01, bs, sl, j)))

