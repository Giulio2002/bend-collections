import Base
import ../lemmas/spec/numeric.bend as S
import ../lib/nat.bend as N
import ../lib/logic.bend as L
import ../lib/u32.bend as U
import ../lib/u32alg.bend as A
import ../lemmas/proofs/nat_algebra.bend as NA
import ../lemmas/proofs/natural_products.bend as PR
import ../lemmas/proofs/division_bounds.bend as DB
import ../lemmas/proofs/division_quotient.bend as DQ
import ../lemmas/proofs/natural_division.bend as ND
import ../lemmas/proofs/word_comparison.bend as WC
import ./word.bend as WD

# Base's U32.div and U32.mod (binary long division, U32.divmod.go) against
# Nat division, for every nonzero divisor, the remainder's shift carry
# included:
#   div_mod:  to_nat(div(a, b)) * to_nat(b) + to_nat(mod(a, b)) == to_nat(a)
#             and to_nat(mod(a, b)) < to_nat(b)
#   div_nat:  to_nat(div(a, b)) == Nat.div(to_nat(a), to_nat(b))
#   mod_nat:  to_nat(mod(a, b)) == Nat.mod(to_nat(a), to_nat(b))

def v(+x: U32) -> Nat:
  U32.to_nat(x)

def dq(-m: Nat, r: Word(m) & U32) -> Word(m):
  (q, s) = r
  q

def dr(-m: Nat, r: Word(m) & U32) -> U32:
  (q, s) = r
  s

# the long-division invariant of a partial result r for the prefix a
def inv(+m: Nat, +a: Word(m), +bn: Nat, r: Word(m) & U32) -> Type:
  {Nat.add(Nat.mul(S.unsigned(m, dq(m, r)), bn), v(dr(m, r))) == S.unsigned(m, a) : Nat} & {Nat.is_lt(v(dr(m, r)), bn) == True{} : Bool}

# ---- digit algebra ----

# a subtracting digit: (1 + 2q) b + d == a + 2 (q b + r) when b + d == a + 2 r
def digit_one(+q: Nat, +bn: Nat, +r: Nat, +a: Nat, +d: Nat, +h: {Nat.add(bn, d) == Nat.add(a, Nat.double(r)) : Nat}) -> {Nat.add(Nat.mul(1n+Nat.double(q), bn), d) == Nat.add(a, Nat.double(Nat.add(Nat.mul(q, bn), r))) : Nat}:
  +x = Nat.double(Nat.mul(q, bn))
  +rhs = Nat.add(a, Nat.double(Nat.add(Nat.mul(q, bn), r)))
  %Equal.sym(Nat, Nat.mul(Nat.double(q), bn), x, PR.double_product(q, bn)) : {Nat.add(Nat.add(bn, _), d) == rhs : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(bn, x), d), Nat.add(Nat.add(bn, d), x), A.add_rot(bn, x, d)) : {_ == rhs : Nat}
  %N.add_comm(x, Nat.add(bn, d)) : {_ == rhs : Nat}
  %Equal.sym(Nat, Nat.add(bn, d), Nat.add(a, Nat.double(r)), h) : {Nat.add(x, _) == rhs : Nat}
  %NA.add_swap(a, x, Nat.double(r)) : {_ == rhs : Nat}
  Equal.cong(Nat, Nat, z => Nat.add(a, z), Nat.add(x, Nat.double(r)), Nat.double(Nat.add(Nat.mul(q, bn), r)), N.add_double(Nat.mul(q, bn), r))

# a zero digit: 2q b + (a + 2 r) == a + 2 (q b + r)
def digit_zero(+q: Nat, +bn: Nat, +r: Nat, +a: Nat) -> {Nat.add(Nat.mul(Nat.double(q), bn), Nat.add(a, Nat.double(r))) == Nat.add(a, Nat.double(Nat.add(Nat.mul(q, bn), r))) : Nat}:
  +x = Nat.double(Nat.mul(q, bn))
  +rhs = Nat.add(a, Nat.double(Nat.add(Nat.mul(q, bn), r)))
  %Equal.sym(Nat, Nat.mul(Nat.double(q), bn), x, PR.double_product(q, bn)) : {Nat.add(_, Nat.add(a, Nat.double(r))) == rhs : Nat}
  %NA.add_swap(a, x, Nat.double(r)) : {_ == rhs : Nat}
  Equal.cong(Nat, Nat, z => Nat.add(a, z), Nat.add(x, Nat.double(r)), Nat.double(Nat.add(Nat.mul(q, bn), r)), N.add_double(Nat.mul(q, bn), r))

# ---- U32 views of the width-generic word facts ----

def vw(+w: Word(32n)) -> {v(U32{w}) == WD.uw(32n, w) : Nat}:
  U.to_nat_word(w)

def vb(+one: Nat, +h1: {one == 1n : Nat}, +x: U32) -> {Nat.is_lt(v(x), WD.sc(32n, one)) == True{} : Bool}:
  match x:
    case U32{+w}:
      %Equal.sym(Nat, v(U32{w}), WD.uw(32n, w), vw(w)) : {Nat.is_lt(_, WD.sc(32n, one)) == True{} : Bool}
      WD.wb(32n, one, h1, w)

def sub32(+one: Nat, +h1: {one == 1n : Nat}, +x: U32, +b: U32, +d: Nat, +e: {Nat.add(v(x), WD.sc(32n, one)) == Nat.add(d, v(b)) : Nat}, +hd: {Nat.is_lt(d, WD.sc(32n, one)) == True{} : Bool}) -> {v(U32.sub(x, b)) == d : Nat}:
  match x b:
    case U32{+xw} U32{+bw}:
      +e2 = Equal.trans(Nat, Nat.add(WD.uw(32n, xw), WD.sc(32n, one)), Nat.add(v(U32{xw}), WD.sc(32n, one)), Nat.add(d, WD.uw(32n, bw)),
        Equal.cong(Nat, Nat, z => Nat.add(z, WD.sc(32n, one)), WD.uw(32n, xw), v(U32{xw}), Equal.sym(Nat, v(U32{xw}), WD.uw(32n, xw), vw(xw))),
        Equal.trans(Nat, Nat.add(v(U32{xw}), WD.sc(32n, one)), Nat.add(d, v(U32{bw})), Nat.add(d, WD.uw(32n, bw)), e, Equal.cong(Nat, Nat, z => Nat.add(d, z), v(U32{bw}), WD.uw(32n, bw), vw(bw))))
      %Equal.sym(Nat, v(U32{Word.sub(32n, xw, bw)}), WD.uw(32n, Word.sub(32n, xw, bw)), vw(Word.sub(32n, xw, bw))) : {_ == d : Nat}
      WD.sub_wrap(32n, one, h1, xw, bw, d, e2, hd)

# ---- one long-division step ----

def fin_true(+p: Nat, +q: Word(p), +s: U32, +b: U32, +a0: Bool, +hi: Word(p), +r: Nat, +one: Nat, +h1: {one == 1n : Nat}, +he: {Nat.add(Nat.mul(S.unsigned(p, q), v(b)), r) == S.unsigned(p, hi) : Nat}, +hr: {Nat.is_lt(r, v(b)) == True{} : Bool}, +hts: {Nat.add(v(s), WD.sc(32n, one)) == Nat.add(S.bit_value(a0), Nat.double(r)) : Nat}) -> inv(1n+p, WCon{a0, hi}, v(b), U32.divmod.go.fin(p, q, s, b, True{})):
  +bn = v(b)
  +k = WD.sc(32n, one)
  +t = Nat.add(S.bit_value(a0), Nat.double(r))
  +hbk = vb(one, h1, b)
  +hkt = L.subst(Nat, z => {Nat.is_le(k, z) == True{} : Bool}, Nat.add(k, v(s)), t, Equal.trans(Nat, Nat.add(k, v(s)), Nat.add(v(s), k), t, N.add_comm(k, v(s)), hts), N.le_add_right(k, v(s)))
  +hbt = N.lt_le(bn, t, N.lt_le_trans(bn, k, t, hbk, hkt))
  +d = Nat.sub(t, bn)
  +hsum = N.sub_add(t, bn, hbt)
  +htb = L.subst(Nat, z => {Nat.is_lt(t, z) == True{} : Bool}, Nat.double(bn), Nat.add(bn, bn), NA.double_self(bn), N.double_lt_bit(a0, r, bn, hr))
  +hdb = N.sub_lt(t, bn, bn, hbt, htb)
  +hdk = N.lt_trans(d, bn, k, hdb, hbk)
  +e = Equal.trans(Nat, Nat.add(v(s), k), t, Nat.add(d, bn), hts, Equal.trans(Nat, t, Nat.add(bn, d), Nat.add(d, bn), Equal.sym(Nat, Nat.add(bn, d), t, hsum), N.add_comm(bn, d)))
  +hsub = sub32(one, h1, s, b, d, e, hdk)
  +eq = Equal.trans(Nat, Nat.add(Nat.mul(1n+Nat.double(S.unsigned(p, q)), bn), v(U32.sub(s, b))), Nat.add(Nat.mul(1n+Nat.double(S.unsigned(p, q)), bn), d), Nat.add(S.bit_value(a0), Nat.double(S.unsigned(p, hi))),
    Equal.cong(Nat, Nat, z => Nat.add(Nat.mul(1n+Nat.double(S.unsigned(p, q)), bn), z), v(U32.sub(s, b)), d, hsub),
    %he : {Nat.add(Nat.mul(1n+Nat.double(S.unsigned(p, q)), bn), d) == Nat.add(S.bit_value(a0), Nat.double(_)) : Nat}
    digit_one(S.unsigned(p, q), bn, r, S.bit_value(a0), d, hsum))
  +lt = L.subst(Nat, z => {Nat.is_lt(z, bn) == True{} : Bool}, d, v(U32.sub(s, b)), Equal.sym(Nat, v(U32.sub(s, b)), d, hsub), hdb)
  (eq, lt)

def fin_ge(+p: Nat, +q: Word(p), +s: U32, +b: U32, +a0: Bool, +hi: Word(p), +r: Nat, +he: {Nat.add(Nat.mul(S.unsigned(p, q), v(b)), r) == S.unsigned(p, hi) : Nat}, +hr: {Nat.is_lt(r, v(b)) == True{} : Bool}, +hs: {v(s) == Nat.add(S.bit_value(a0), Nat.double(r)) : Nat}, +hge: {Nat.is_ge(v(s), v(b)) == True{} : Bool}) -> inv(1n+p, WCon{a0, hi}, v(b), U32.divmod.go.fin(p, q, s, b, True{})):
  +bn = v(b)
  +t = Nat.add(S.bit_value(a0), Nat.double(r))
  +htb = L.subst(Nat, z => {Nat.is_lt(t, z) == True{} : Bool}, Nat.double(bn), Nat.add(bn, bn), NA.double_self(bn), N.double_lt_bit(a0, r, bn, hr))
  +hle = Equal.trans(Bool, Nat.is_le(bn, v(s)), Nat.is_ge(v(s), bn), True{}, Equal.sym(Bool, Nat.is_ge(v(s), bn), Nat.is_le(bn, v(s)), DB.ge_reverse(v(s), bn)), hge)
  +d = Nat.sub(v(s), bn)
  +hsub = U.sub_nat(s, b, hle)
  +hsum = Equal.trans(Nat, Nat.add(bn, d), v(s), t, N.sub_add(v(s), bn, hle), hs)
  +hsb = L.subst(Nat, z => {Nat.is_lt(z, Nat.add(bn, bn)) == True{} : Bool}, t, v(s), Equal.sym(Nat, v(s), t, hs), htb)
  +hdb = N.sub_lt(v(s), bn, bn, hle, hsb)
  +eq = Equal.trans(Nat, Nat.add(Nat.mul(1n+Nat.double(S.unsigned(p, q)), bn), v(U32.sub(s, b))), Nat.add(Nat.mul(1n+Nat.double(S.unsigned(p, q)), bn), d), Nat.add(S.bit_value(a0), Nat.double(S.unsigned(p, hi))),
    Equal.cong(Nat, Nat, z => Nat.add(Nat.mul(1n+Nat.double(S.unsigned(p, q)), bn), z), v(U32.sub(s, b)), d, hsub),
    %he : {Nat.add(Nat.mul(1n+Nat.double(S.unsigned(p, q)), bn), d) == Nat.add(S.bit_value(a0), Nat.double(_)) : Nat}
    digit_one(S.unsigned(p, q), bn, r, S.bit_value(a0), d, hsum))
  +lt = L.subst(Nat, z => {Nat.is_lt(z, bn) == True{} : Bool}, d, v(U32.sub(s, b)), Equal.sym(Nat, v(U32.sub(s, b)), d, hsub), hdb)
  (eq, lt)

def fin_lt(+p: Nat, +q: Word(p), +s: U32, +b: U32, +a0: Bool, +hi: Word(p), +r: Nat, +he: {Nat.add(Nat.mul(S.unsigned(p, q), v(b)), r) == S.unsigned(p, hi) : Nat}, +hs: {v(s) == Nat.add(S.bit_value(a0), Nat.double(r)) : Nat}, +hge: {Nat.is_ge(v(s), v(b)) == False{} : Bool}) -> inv(1n+p, WCon{a0, hi}, v(b), U32.divmod.go.fin(p, q, s, b, False{})):
  +bn = v(b)
  +t = Nat.add(S.bit_value(a0), Nat.double(r))
  +lt = DB.not_ge(v(s), bn, hge)
  +eq = Equal.trans(Nat, Nat.add(Nat.mul(Nat.double(S.unsigned(p, q)), bn), v(s)), Nat.add(Nat.mul(Nat.double(S.unsigned(p, q)), bn), t), Nat.add(S.bit_value(a0), Nat.double(S.unsigned(p, hi))),
    Equal.cong(Nat, Nat, z => Nat.add(Nat.mul(Nat.double(S.unsigned(p, q)), bn), z), v(s), t, hs),
    %he : {Nat.add(Nat.mul(Nat.double(S.unsigned(p, q)), bn), t) == Nat.add(S.bit_value(a0), Nat.double(_)) : Nat}
    digit_zero(S.unsigned(p, q), bn, r, S.bit_value(a0)))
  (eq, lt)

def fin_false(+p: Nat, +q: Word(p), +s: U32, +b: U32, +a0: Bool, +hi: Word(p), +r: Nat, +he: {Nat.add(Nat.mul(S.unsigned(p, q), v(b)), r) == S.unsigned(p, hi) : Nat}, +hr: {Nat.is_lt(r, v(b)) == True{} : Bool}, +hs: {v(s) == Nat.add(S.bit_value(a0), Nat.double(r)) : Nat}, +g: Bool, +hg: {U32.is_ge(s, b) == g : Bool}) -> inv(1n+p, WCon{a0, hi}, v(b), U32.divmod.go.fin(p, q, s, b, g)):
  match g:
    case True{}:
      fin_ge(p, q, s, b, a0, hi, r, he, hr, hs, Equal.trans(Bool, Nat.is_ge(v(s), v(b)), U32.is_ge(s, b), True{}, Equal.sym(Bool, U32.is_ge(s, b), Nat.is_ge(v(s), v(b)), WC.u32_ge(s, b)), hg))
    case False{}:
      fin_lt(p, q, s, b, a0, hi, r, he, hs, Equal.trans(Bool, Nat.is_ge(v(s), v(b)), U32.is_ge(s, b), False{}, Equal.sym(Bool, U32.is_ge(s, b), Nat.is_ge(v(s), v(b)), WC.u32_ge(s, b)), hg))

def shl_ts(+p: Nat, +q: Word(p), +b: U32, +t: Bool, +s: Word(32n), +a0: Bool, +hi: Word(p), +r: Nat, +one: Nat, +h1: {one == 1n : Nat}, +he: {Nat.add(Nat.mul(S.unsigned(p, q), v(b)), r) == S.unsigned(p, hi) : Nat}, +hr: {Nat.is_lt(r, v(b)) == True{} : Bool}, +hts: {Nat.add(WD.uw(32n, s), WD.sc(32n, WD.bo(t, one))) == Nat.add(S.bit_value(a0), Nat.double(r)) : Nat}) -> inv(1n+p, WCon{a0, hi}, v(b), U32.divmod.go.fin(p, q, U32{s}, b, Bool.or(t, U32.is_ge(U32{s}, b)))):
  match t:
    case True{}:
      fin_true(p, q, U32{s}, b, a0, hi, r, one, h1, he, hr, L.subst(Nat, z => {Nat.add(z, WD.sc(32n, one)) == Nat.add(S.bit_value(a0), Nat.double(r)) : Nat}, WD.uw(32n, s), v(U32{s}), Equal.sym(Nat, v(U32{s}), WD.uw(32n, s), vw(s)), hts))
    case False{}:
      +hs = Equal.trans(Nat, v(U32{s}), WD.uw(32n, s), Nat.add(S.bit_value(a0), Nat.double(r)), vw(s), Equal.trans(Nat, WD.uw(32n, s), Nat.add(WD.uw(32n, s), 0n), Nat.add(S.bit_value(a0), Nat.double(r)), Equal.sym(Nat, Nat.add(WD.uw(32n, s), 0n), WD.uw(32n, s), N.add_zero(WD.uw(32n, s))), hts))
      fin_false(p, q, U32{s}, b, a0, hi, r, he, hr, hs, U32.is_ge(U32{s}, b), {==})

def shl_ok(+p: Nat, +q: Word(p), +b: U32, ts: Bool & Word(32n), +a0: Bool, +hi: Word(p), +r: Nat, +one: Nat, +h1: {one == 1n : Nat}, +he: {Nat.add(Nat.mul(S.unsigned(p, q), v(b)), r) == S.unsigned(p, hi) : Nat}, +hr: {Nat.is_lt(r, v(b)) == True{} : Bool}, hts: {Nat.add(WD.uw(32n, WD.ow(32n, ts)), WD.sc(32n, WD.bo(WD.ob(32n, ts), one))) == Nat.add(S.bit_value(a0), Nat.double(r)) : Nat}) -> inv(1n+p, WCon{a0, hi}, v(b), U32.divmod.go.shl(p, q, b, ts)):
  match ts:
    case (+t, +s):
      shl_ts(p, q, b, t, s, a0, hi, r, one, h1, he, hr, hts)

def rec_ok(+p: Nat, +a0: Bool, +b: U32, +hi: Word(p), qr: Word(p) & U32, ih: inv(p, hi, v(b), qr), +one: Nat, +h1: {one == 1n : Nat}) -> inv(1n+p, WCon{a0, hi}, v(b), U32.divmod.go.rec(p, a0, b, qr)):
  match qr:
    case (+q, +r):
      match r:
        case U32{+rw}:
          (he, hr) = ih
          +hts = Equal.trans(Nat, Nat.add(WD.uw(32n, WD.ow(32n, Word.shl.out(32n, a0, rw))), WD.sc(32n, WD.bo(WD.ob(32n, Word.shl.out(32n, a0, rw)), one))), Nat.add(S.bit_value(a0), Nat.double(WD.uw(32n, rw))), Nat.add(S.bit_value(a0), Nat.double(v(U32{rw}))),
            WD.shl_out1(32n, one, h1, a0, rw),
            Equal.cong(Nat, Nat, z => Nat.add(S.bit_value(a0), Nat.double(z)), WD.uw(32n, rw), v(U32{rw}), Equal.sym(Nat, v(U32{rw}), WD.uw(32n, rw), vw(rw))))
          shl_ok(p, q, b, Word.shl.out(32n, a0, rw), a0, hi, v(U32{rw}), one, h1, he, hr, hts)

# the invariant holds for every prefix of the dividend
def go_ok(+m: Nat, +a: Word(m), +b: U32, +hb: {Nat.is_lt(0n, v(b)) == True{} : Bool}, +one: Nat, +h1: {one == 1n : Nat}) -> inv(m, a, v(b), U32.divmod.go(m, a, b)):
  match m a:
    case 0n WNil{}:
      ({==}, hb)
    case 1n+p WCon{a0, hi}:
      rec_ok(p, a0, b, hi, U32.divmod.go(p, hi, b), go_ok(p, hi, b, hb, one, h1), one, h1)

# ---- the division theorems ----

def pos_nat(+x: Nat, +h: {Cmp.is_eq(Nat.cmp(x, 0n)) == False{} : Bool}) -> {Nat.is_lt(0n, x) == True{} : Bool}:
  match x:
    case 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, L.true_false(h))
    case 1n+k:
      {==}

def pos(+b: U32, +hb: {U32.is_zero(b) == False{} : Bool}) -> {Nat.is_lt(0n, v(b)) == True{} : Bool}:
  pos_nat(v(b), L.subst(Cmp, c => {Cmp.is_eq(c) == False{} : Bool}, U32.cmp(b, 0), Nat.cmp(v(b), 0n), U.u32_cmp(b, 0), hb))

def dm_fin(+aw: Word(32n), +b: U32, qr: Word(32n) & U32, h: inv(32n, aw, v(b), qr)) -> {Nat.add(Nat.mul(v(U32.div.fin(qr)), v(b)), v(U32.mod.fin(qr))) == v(U32{aw}) : Nat} & {Nat.is_lt(v(U32.mod.fin(qr)), v(b)) == True{} : Bool}:
  match qr:
    case (+q, +r):
      (he, hr) = h
      +eq = Equal.trans(Nat, Nat.add(Nat.mul(v(U32{q}), v(b)), v(r)), Nat.add(Nat.mul(S.unsigned(32n, q), v(b)), v(r)), v(U32{aw}),
        Equal.cong(Nat, Nat, z => Nat.add(Nat.mul(z, v(b)), v(r)), v(U32{q}), S.unsigned(32n, q), vw(q)),
        Equal.trans(Nat, Nat.add(Nat.mul(S.unsigned(32n, q), v(b)), v(r)), S.unsigned(32n, aw), v(U32{aw}), he, Equal.sym(Nat, v(U32{aw}), S.unsigned(32n, aw), vw(aw))))
      (eq, hr)

def dm_if(+aw: Word(32n), +b: U32, +z: Bool, +hz: {z == False{} : Bool}, +hb: {Nat.is_lt(0n, v(b)) == True{} : Bool}) -> {Nat.add(Nat.mul(v(U32.div.if(aw, b, z)), v(b)), v(U32.mod.if(aw, b, z))) == v(U32{aw}) : Nat} & {Nat.is_lt(v(U32.mod.if(aw, b, z)), v(b)) == True{} : Bool}:
  match z:
    case True{}:
      Empty.absurd({Nat.add(Nat.mul(v(U32.div.if(aw, b, True{})), v(b)), v(U32.mod.if(aw, b, True{}))) == v(U32{aw}) : Nat} & {Nat.is_lt(v(U32.mod.if(aw, b, True{})), v(b)) == True{} : Bool}, L.true_false(hz))
    case False{}:
      dm_fin(aw, b, U32.divmod.go(32n, aw, b), go_ok(32n, aw, b, hb, 1n, {==}))

# THEOREM: div and mod are Euclidean division by any nonzero divisor.
def div_mod(+a: U32, +b: U32, +hb: {U32.is_zero(b) == False{} : Bool}) -> {Nat.add(Nat.mul(v(U32.div(a, b)), v(b)), v(U32.mod(a, b))) == v(a) : Nat} & {Nat.is_lt(v(U32.mod(a, b)), v(b)) == True{} : Bool}:
  match a:
    case U32{+aw}:
      dm_if(aw, b, U32.is_zero(b), hb, pos(b, hb))

def mod_identify(+q: Nat, +d: Nat, +r: Nat, +bound: {Nat.is_lt(r, d) == True{} : Bool}) -> {Nat.mod(Nat.add(Nat.mul(q, d), r), d) == r : Nat}:
  match d:
    case 0n:
      Empty.absurd({Nat.mod(Nat.add(Nat.mul(q, 0n), r), 0n) == r : Nat}, N.lt_zero_absurd(r, bound))
    case 1n+p:
      ND.remainder(q, p, r, N.lt_succ_le(r, p, bound))

def dm_type(+a: U32, +b: U32) -> Type:
  {Nat.add(Nat.mul(v(U32.div(a, b)), v(b)), v(U32.mod(a, b))) == v(a) : Nat} & {Nat.is_lt(v(U32.mod(a, b)), v(b)) == True{} : Bool}

def div_of(+a: U32, +b: U32, h: dm_type(a, b)) -> {v(U32.div(a, b)) == Nat.div(v(a), v(b)) : Nat}:
  (e, lt) = h
  %e : {v(U32.div(a, b)) == Nat.div(_, v(b)) : Nat}
  Equal.sym(Nat, Nat.div(Nat.add(Nat.mul(v(U32.div(a, b)), v(b)), v(U32.mod(a, b))), v(b)), v(U32.div(a, b)), DQ.identify(v(U32.div(a, b)), v(b), v(U32.mod(a, b)), lt))

def mod_of(+a: U32, +b: U32, h: dm_type(a, b)) -> {v(U32.mod(a, b)) == Nat.mod(v(a), v(b)) : Nat}:
  (e, lt) = h
  %e : {v(U32.mod(a, b)) == Nat.mod(_, v(b)) : Nat}
  Equal.sym(Nat, Nat.mod(Nat.add(Nat.mul(v(U32.div(a, b)), v(b)), v(U32.mod(a, b))), v(b)), v(U32.mod(a, b)), mod_identify(v(U32.div(a, b)), v(b), v(U32.mod(a, b)), lt))

# THEOREM: div is Nat division.
def div_nat(+a: U32, +b: U32, +hb: {U32.is_zero(b) == False{} : Bool}) -> {v(U32.div(a, b)) == Nat.div(v(a), v(b)) : Nat}:
  div_of(a, b, div_mod(a, b, hb))

# THEOREM: mod is Nat remainder.
def mod_nat(+a: U32, +b: U32, +hb: {U32.is_zero(b) == False{} : Bool}) -> {v(U32.mod(a, b)) == Nat.mod(v(a), v(b)) : Nat}:
  mod_of(a, b, div_mod(a, b, hb))
