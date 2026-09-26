import Base
import ../../spec/lib/numeric.bend as SNUM
import ./lemmas/spec/numeric.bend as S
import ./nat.bend as N
import ./logic.bend as L
import ./u32.bend as U
import ./u32alg.bend as A
import ./lemmas/proofs/addition_bounds.bend as AB
import ./lemmas/proofs/word_multiplication.bend as WM
import ./lemmas/proofs/word_value.bend as WV
import ./lemmas/proofs/negation_magnitude.bend as NM
import ./lemmas/proofs/nat_algebra.bend as NA
import ./lemmas/proofs/natural_products.bend as PR
import ./lemmas/proofs/division_bounds.bend as DB
import ./lemmas/proofs/word_addition.bend as WA
import ./lemmas/proofs/modular_addition.bend as MA
import ./lemmas/src/wide.bend as W

# Width-generic word facts. The checker evaluates closed Nat terms in unary,
# so a concrete bound such as 2^32 cannot appear in a type. Every bound here
# is S.scale_binary(n, one) for a symbolic `one` with {one == 1n}; the final
# theorems, whose statements carry no bound, instantiate one := 1n.

def sc(+n: Nat, +k: Nat) -> Nat:
  S.scale_binary(n, k)

def uw(+n: Nat, +w: Word(n)) -> Nat:
  S.unsigned(n, w)

# a bit worth `one`
def bo(b: Bool, +one: Nat) -> Nat:
  match b:
    case True{}:
      one
    case False{}:
      0n

def bo_bit(+b: Bool, +one: Nat, +h1: {one == 1n : Nat}) -> {bo(b, one) == S.bit_value(b) : Nat}:
  match b:
    case True{}:
      h1
    case False{}:
      {==}

def lt1(+n: Nat, +one: Nat, +h1: {one == 1n : Nat}, +x: Nat, +h: {Nat.is_lt(x, sc(n, one)) == True{} : Bool}) -> {Nat.is_lt(x, sc(n, 1n)) == True{} : Bool}:
  L.subst(Nat, o => {Nat.is_lt(x, S.scale_binary(n, o)) == True{} : Bool}, one, 1n, h1, h)

def lt1r(+n: Nat, +one: Nat, +h1: {one == 1n : Nat}, +x: Nat, +h: {Nat.is_lt(x, sc(n, 1n)) == True{} : Bool}) -> {Nat.is_lt(x, sc(n, one)) == True{} : Bool}:
  L.subst(Nat, o => {Nat.is_lt(x, S.scale_binary(n, o)) == True{} : Bool}, 1n, one, Equal.sym(Nat, one, 1n, h1), h)

# every n-bit word is below 2^n
def wb(+n: Nat, +one: Nat, +h1: {one == 1n : Nat}, +w: Word(n)) -> {Nat.is_lt(uw(n, w), sc(n, one)) == True{} : Bool}:
  lt1r(n, one, h1, uw(n, w), U.WB_unsigned(n, w))

# r1 + 2^n x == r2 + 2^n y with both r below 2^n forces r1 == r2
def uniq(+n: Nat, +one: Nat, +h1: {one == 1n : Nat}, +r1: Nat, +r2: Nat, +x: Nat, +y: Nat, +h: {Nat.add(r1, sc(n, x)) == Nat.add(r2, sc(n, y)) : Nat}, +b1: {Nat.is_lt(r1, sc(n, one)) == True{} : Bool}, +b2: {Nat.is_lt(r2, sc(n, one)) == True{} : Bool}) -> {r1 == r2 : Nat}:
  A.uniq(n, r1, r2, x, y, h, lt1(n, one, h1, r1, b1), lt1(n, one, h1, r2, b2))

# addition below 2^n is exact
def add_exact(+n: Nat, +one: Nat, +h1: {one == 1n : Nat}, +a: Word(n), +b: Word(n), +h: {Nat.is_lt(Nat.add(uw(n, a), uw(n, b)), sc(n, one)) == True{} : Bool}) -> {uw(n, Word.add(n, a, b)) == Nat.add(uw(n, a), uw(n, b)) : Nat}:
  AB.exact(n, a, b, lt1(n, one, h1, Nat.add(uw(n, a), uw(n, b)), h))

# multiplication below 2^n is exact
def mul_exact(+n: Nat, +one: Nat, +h1: {one == 1n : Nat}, +a: Word(n), +b: Word(n), +h: {Nat.is_lt(Nat.mul(uw(n, a), uw(n, b)), sc(n, one)) == True{} : Bool}) -> {uw(n, Word.mul(n, a, b)) == Nat.mul(uw(n, a), uw(n, b)) : Nat}:
  +p = Nat.mul(uw(n, a), uw(n, b))
  %Equal.sym(Word(n), Word.mul(n, a, b), S.from_nat(n, p), WM.refines(n, a, b)) : {S.unsigned(n, _) == p : Nat}
  WV.from_nat_value(n, p, L.subst(Nat, z => {Nat.is_lt(p, z) == True{} : Bool}, S.scale_binary(n, 1n), Nat.pow(2n, n), NM.scale_power(n), lt1(n, one, h1, p, h)))

# ---- wrapped subtraction ----

# If x + 2^n == d + b with d < 2^n, the machine difference x - b is d.
def sub_wrap(+n: Nat, +one: Nat, +h1: {one == 1n : Nat}, +xw: Word(n), +bw: Word(n), +d: Nat, +e: {Nat.add(uw(n, xw), sc(n, one)) == Nat.add(d, uw(n, bw)) : Nat}, +hd: {Nat.is_lt(d, sc(n, one)) == True{} : Bool}) -> {uw(n, Word.sub(n, xw, bw)) == d : Nat}:
  +us = uw(n, Word.sub(n, xw, bw))
  +ux = uw(n, xw)
  +ub = uw(n, bw)
  +un = uw(n, Word.not(n, bw))
  +c5 = A.cy(n, xw, Word.not(n, bw), True{})
  +e5 = A.cons_sub(n, xw, bw)
  +nv = A.not_value(n, bw)
  +ew = L.subst(Nat, o => {Nat.add(ux, S.scale_binary(n, o)) == Nat.add(d, ub) : Nat}, one, 1n, h1, e)
  # (1 + (ux + un)) + ub == ux + (1 + (un + ub)) == ux + 2^n
  +mid = Equal.trans(Nat, Nat.add(Nat.add(1n, Nat.add(ux, un)), ub), 1n+Nat.add(ux, Nat.add(un, ub)), Nat.add(ux, sc(n, 1n)),
    N.succ_cong(Nat.add(Nat.add(ux, un), ub), Nat.add(ux, Nat.add(un, ub)), N.add_assoc(ux, un, ub)),
    Equal.trans(Nat, 1n+Nat.add(ux, Nat.add(un, ub)), Nat.add(ux, 1n+Nat.add(un, ub)), Nat.add(ux, sc(n, 1n)), Equal.sym(Nat, Nat.add(ux, 1n+Nat.add(un, ub)), 1n+Nat.add(ux, Nat.add(un, ub)), N.add_succ(ux, Nat.add(un, ub))), Equal.cong(Nat, Nat, z => Nat.add(ux, z), Nat.add(1n, Nat.add(un, ub)), sc(n, 1n), nv)))
  +chain = Equal.trans(Nat, Nat.add(Nat.add(us, sc(n, c5)), ub), Nat.add(Nat.add(1n, Nat.add(ux, un)), ub), Nat.add(d, ub),
    Equal.cong(Nat, Nat, z => Nat.add(z, ub), Nat.add(us, sc(n, c5)), Nat.add(1n, Nat.add(ux, un)), e5),
    Equal.trans(Nat, Nat.add(Nat.add(1n, Nat.add(ux, un)), ub), Nat.add(ux, sc(n, 1n)), Nat.add(d, ub), mid, ew))
  +e0 = A.add_cancel_r(Nat.add(us, sc(n, c5)), d, ub, chain)
  +e1 = Equal.trans(Nat, Nat.add(us, sc(n, c5)), d, Nat.add(d, sc(n, 0n)), e0,
    Equal.trans(Nat, d, Nat.add(d, 0n), Nat.add(d, sc(n, 0n)), Equal.sym(Nat, Nat.add(d, 0n), d, N.add_zero(d)), Equal.cong(Nat, Nat, z => Nat.add(d, z), 0n, sc(n, 0n), Equal.sym(Nat, sc(n, 0n), 0n, A.sc_zero(n)))))
  uniq(n, one, h1, us, d, c5, 0n, e1, wb(n, one, h1, Word.sub(n, xw, bw)), hd)

# ---- shifting a bit in ----

def ob(-n: Nat, r: Bool & Word(n)) -> Bool:
  (t, s) = r
  t

def ow(-n: Nat, r: Bool & Word(n)) -> Word(n):
  (t, s) = r
  s

def shl_con(+p: Nat, +c: Bool, +b: Bool, +tl: Word(p), r: Bool & Word(p), ih: {Nat.add(S.unsigned(p, ow(p, r)), S.scale_binary(p, S.bit_value(ob(p, r)))) == Nat.add(S.bit_value(b), Nat.double(S.unsigned(p, tl))) : Nat}) -> {Nat.add(S.unsigned(1n+p, ow(1n+p, Word.shl.out.con(p, c, r))), S.scale_binary(1n+p, S.bit_value(ob(1n+p, Word.shl.out.con(p, c, r))))) == Nat.add(S.bit_value(c), Nat.double(S.unsigned(1n+p, WCon{b, tl}))) : Nat}:
  match r:
    case (+hi, +t2):
      %ih : {Nat.add(Nat.add(S.bit_value(c), Nat.double(S.unsigned(p, t2))), Nat.double(S.scale_binary(p, S.bit_value(hi)))) == Nat.add(S.bit_value(c), Nat.double(_)) : Nat}
      Equal.trans(Nat, Nat.add(Nat.add(S.bit_value(c), Nat.double(S.unsigned(p, t2))), Nat.double(S.scale_binary(p, S.bit_value(hi)))), Nat.add(S.bit_value(c), Nat.add(Nat.double(S.unsigned(p, t2)), Nat.double(S.scale_binary(p, S.bit_value(hi))))), Nat.add(S.bit_value(c), Nat.double(Nat.add(S.unsigned(p, t2), S.scale_binary(p, S.bit_value(hi))))),
        N.add_assoc(S.bit_value(c), Nat.double(S.unsigned(p, t2)), Nat.double(S.scale_binary(p, S.bit_value(hi)))),
        Equal.cong(Nat, Nat, z => Nat.add(S.bit_value(c), z), Nat.add(Nat.double(S.unsigned(p, t2)), Nat.double(S.scale_binary(p, S.bit_value(hi)))), Nat.double(Nat.add(S.unsigned(p, t2), S.scale_binary(p, S.bit_value(hi)))), N.add_double(S.unsigned(p, t2), S.scale_binary(p, S.bit_value(hi)))))

def shl_nil(+c: Bool) -> {Nat.add(S.unsigned(0n, ow(0n, Word.shl.out(0n, c, WNil{}))), S.scale_binary(0n, S.bit_value(ob(0n, Word.shl.out(0n, c, WNil{}))))) == Nat.add(S.bit_value(c), Nat.double(S.unsigned(0n, WNil{}))) : Nat}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

# the out-shifted bit and word together hold c + 2w
def shl_out(+n: Nat, +c: Bool, +w: Word(n)) -> {Nat.add(S.unsigned(n, ow(n, Word.shl.out(n, c, w))), S.scale_binary(n, S.bit_value(ob(n, Word.shl.out(n, c, w))))) == Nat.add(S.bit_value(c), Nat.double(S.unsigned(n, w))) : Nat}:
  match n w:
    case 0n WNil{}:
      shl_nil(c)
    case 1n+p WCon{b, tl}:
      shl_con(p, c, b, tl, Word.shl.out(p, b, tl), shl_out(p, b, tl))

# the same with the out-shifted bit worth `one`
def shl_out1(+n: Nat, +one: Nat, +h1: {one == 1n : Nat}, +c: Bool, +w: Word(n)) -> {Nat.add(uw(n, ow(n, Word.shl.out(n, c, w))), sc(n, bo(ob(n, Word.shl.out(n, c, w)), one))) == Nat.add(S.bit_value(c), Nat.double(uw(n, w))) : Nat}:
  %Equal.sym(Nat, bo(ob(n, Word.shl.out(n, c, w)), one), S.bit_value(ob(n, Word.shl.out(n, c, w))), bo_bit(ob(n, Word.shl.out(n, c, w)), one, h1)) : {Nat.add(uw(n, ow(n, Word.shl.out(n, c, w))), sc(n, _)) == Nat.add(S.bit_value(c), Nat.double(uw(n, w))) : Nat}
  shl_out(n, c, w)

# ---- two-limb carry algebra ----

def add_inner(+n: Nat, +h: Nat, +t: Nat, +c0: Nat, +c1: Nat, +c2: Nat, +ah: Nat, +bh: Nat, +f2: {Nat.add(t, sc(n, c1)) == Nat.add(ah, bh) : Nat}, +f3: {Nat.add(h, sc(n, c2)) == Nat.add(t, c0) : Nat}) -> {Nat.add(h, Nat.add(sc(n, c1), sc(n, c2))) == Nat.add(c0, Nat.add(ah, bh)) : Nat}:
  +rhs = Nat.add(c0, Nat.add(ah, bh))
  %Equal.sym(Nat, Nat.add(h, Nat.add(sc(n, c1), sc(n, c2))), Nat.add(sc(n, c1), Nat.add(h, sc(n, c2))), NA.add_swap(h, sc(n, c1), sc(n, c2))) : {_ == rhs : Nat}
  %Equal.sym(Nat, Nat.add(h, sc(n, c2)), Nat.add(t, c0), f3) : {Nat.add(sc(n, c1), _) == rhs : Nat}
  %N.add_comm(Nat.add(t, c0), sc(n, c1)) : {_ == rhs : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(t, c0), sc(n, c1)), Nat.add(Nat.add(t, sc(n, c1)), c0), A.add_rot(t, c0, sc(n, c1))) : {_ == rhs : Nat}
  %Equal.sym(Nat, Nat.add(t, sc(n, c1)), Nat.add(ah, bh), f2) : {Nat.add(_, c0) == rhs : Nat}
  N.add_comm(Nat.add(ah, bh), c0)

# low limbs l with carry c0, high limbs t = ah + bh (carry c1), then h = t + c0
# (carry c2): the two-limb sum loses exactly 2^(2n) (c1 + c2).
def add_alg(+n: Nat, +l: Nat, +h: Nat, +t: Nat, +c0: Nat, +c1: Nat, +c2: Nat, +al: Nat, +ah: Nat, +bl: Nat, +bh: Nat, +f1: {Nat.add(l, sc(n, c0)) == Nat.add(al, bl) : Nat}, +f2: {Nat.add(t, sc(n, c1)) == Nat.add(ah, bh) : Nat}, +f3: {Nat.add(h, sc(n, c2)) == Nat.add(t, c0) : Nat}) -> {Nat.add(Nat.add(l, sc(n, h)), sc(n, sc(n, Nat.add(c1, c2)))) == Nat.add(Nat.add(al, sc(n, ah)), Nat.add(bl, sc(n, bh))) : Nat}:
  +x = Nat.add(sc(n, c1), sc(n, c2))
  +rhs = Nat.add(Nat.add(al, sc(n, ah)), Nat.add(bl, sc(n, bh)))
  %A.sc_add(n, c1, c2) : {Nat.add(Nat.add(l, sc(n, h)), sc(n, _)) == rhs : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(l, sc(n, h)), sc(n, x)), Nat.add(l, Nat.add(sc(n, h), sc(n, x))), N.add_assoc(l, sc(n, h), sc(n, x))) : {_ == rhs : Nat}
  %Equal.sym(Nat, Nat.add(sc(n, h), sc(n, x)), sc(n, Nat.add(h, x)), A.sc_add(n, h, x)) : {Nat.add(l, _) == rhs : Nat}
  %Equal.sym(Nat, Nat.add(h, x), Nat.add(c0, Nat.add(ah, bh)), add_inner(n, h, t, c0, c1, c2, ah, bh, f2, f3)) : {Nat.add(l, sc(n, _)) == rhs : Nat}
  %A.sc_add(n, c0, Nat.add(ah, bh)) : {Nat.add(l, _) == rhs : Nat}
  %N.add_assoc(l, sc(n, c0), sc(n, Nat.add(ah, bh))) : {_ == rhs : Nat}
  %Equal.sym(Nat, Nat.add(l, sc(n, c0)), Nat.add(al, bl), f1) : {Nat.add(_, sc(n, Nat.add(ah, bh))) == rhs : Nat}
  %A.sc_add(n, ah, bh) : {Nat.add(Nat.add(al, bl), _) == rhs : Nat}
  PR.shuffle(al, bl, sc(n, ah), sc(n, bh))

# the carry out of an addition is the wrap-around test sum < x
def carry_lt(+n: Nat, +one: Nat, +h1: {one == 1n : Nat}, +s: Nat, +x: Nat, +y: Nat, +c: Bool, +e: {Nat.add(s, sc(n, S.bit_value(c))) == Nat.add(x, y) : Nat}, +hy: {Nat.is_lt(y, sc(n, one)) == True{} : Bool}) -> {Nat.is_lt(s, x) == c : Bool}:
  match c:
    case False{}:
      +e0 = Equal.trans(Nat, s, Nat.add(s, 0n), Nat.add(x, y), Equal.sym(Nat, Nat.add(s, 0n), s, N.add_zero(s)), L.subst(Nat, z => {Nat.add(s, z) == Nat.add(x, y) : Nat}, sc(n, 0n), 0n, A.sc_zero(n), e))
      %Equal.sym(Nat, s, Nat.add(y, x), Equal.trans(Nat, s, Nat.add(x, y), Nat.add(y, x), e0, N.add_comm(x, y))) : {Nat.is_lt(_, x) == False{} : Bool}
      AB.offset_not_less(x, y)
    case True{}:
      +k = sc(n, 1n)
      +hy1 = lt1(n, one, h1, y, hy)
      +l1 = N.lt_add_left(y, k, x, hy1)
      +l2 = L.subst(Nat, z => {Nat.is_lt(z, Nat.add(x, k)) == True{} : Bool}, Nat.add(x, y), Nat.add(k, s), Equal.trans(Nat, Nat.add(x, y), Nat.add(s, k), Nat.add(k, s), Equal.sym(Nat, Nat.add(s, k), Nat.add(x, y), e), N.add_comm(s, k)), l1)
      +l3 = L.subst(Nat, z => {Nat.is_lt(Nat.add(k, s), z) == True{} : Bool}, Nat.add(x, k), Nat.add(k, x), N.add_comm(x, k), l2)
      Equal.trans(Bool, Nat.is_lt(s, x), Nat.is_lt(Nat.add(k, s), Nat.add(k, x)), True{}, Equal.sym(Bool, Nat.is_lt(Nat.add(k, s), Nat.add(k, x)), Nat.is_lt(s, x), DB.cancel_less(k, s, x)), l3)

# ---- negation over joined limbs ----

def not_join(+n: Nat, +m: Nat, +a: Word(n), +b: Word(m)) -> {Word.not(Nat.add(n, m), W.join(n, m, a, b)) == W.join(n, m, Word.not(n, a), Word.not(m, b)) : Word(Nat.add(n, m))}:
  match n a:
    case 0n WNil{}:
      {==}
    case 1n+p WCon{x, t}:
      Equal.cong(Word(Nat.add(p, m)), Word(1n+Nat.add(p, m)), w => WCon{Bool.not(x), w}, Word.not(Nat.add(p, m), W.join(p, m, t, b)), W.join(p, m, Word.not(p, t), Word.not(m, b)), not_join(p, m, t, b))

# every bit set
def ones(+n: Nat, w: Word(n)) -> Bool:
  match n w:
    case 0n WNil{}:
      True{}
    case 1n+p WCon{x, t}:
      Bool.and(x, ones(p, t))

def incif(+m: Nat, c: Bool, b: Word(m)) -> Word(m):
  match c:
    case True{}:
      Word.inc(m, b)
    case False{}:
      b

# incrementing a joined word carries into the high part iff the low part is all ones
def inc_join(+n: Nat, +m: Nat, +a: Word(n), +b: Word(m)) -> {Word.inc(Nat.add(n, m), W.join(n, m, a, b)) == W.join(n, m, Word.inc(n, a), incif(m, ones(n, a), b)) : Word(Nat.add(n, m))}:
  match n a:
    case 0n WNil{}:
      {==}
    case 1n+p WCon{False{}, t}:
      {==}
    case 1n+p WCon{True{}, t}:
      Equal.cong(Word(Nat.add(p, m)), Word(1n+Nat.add(p, m)), w => WCon{False{}, w}, Word.inc(Nat.add(p, m), W.join(p, m, t, b)), W.join(p, m, Word.inc(p, t), incif(m, ones(p, t), b)), inc_join(p, m, t, b))

def eq_fin_tf(+c: Cmp) -> {Cmp.is_eq(Word.cmp.fin(True{}, False{}, c)) == False{} : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def eq_fin_ff(+c: Cmp) -> {Cmp.is_eq(Word.cmp.fin(False{}, False{}, c)) == Cmp.is_eq(c) : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

# an increment is zero iff it wrapped from all ones
def inc_zero(+n: Nat, +x: Word(n)) -> {Cmp.is_eq(Word.cmp(n, Word.inc(n, x), Word.zero(n))) == ones(n, x) : Bool}:
  match n x:
    case 0n WNil{}:
      {==}
    case 1n+p WCon{False{}, t}:
      eq_fin_tf(Word.cmp(p, t, Word.zero(p)))
    case 1n+p WCon{True{}, t}:
      Equal.trans(Bool, Cmp.is_eq(Word.cmp.fin(False{}, False{}, Word.cmp(p, Word.inc(p, t), Word.zero(p)))), Cmp.is_eq(Word.cmp(p, Word.inc(p, t), Word.zero(p))), ones(p, t), eq_fin_ff(Word.cmp(p, Word.inc(p, t), Word.zero(p))), inc_zero(p, t))

def one_word(+p: Nat) -> Word(1n+p):
  WCon{True{}, Word.zero(p)}

# adding one is incrementing
def add_one(+p: Nat, +x: Word(1n+p)) -> {Word.add(1n+p, x, one_word(p)) == Word.inc(1n+p, x) : Word(1n+p)}:
  +ux = uw(1n+p, x)
  +u1 = Equal.cong(Nat, Nat, z => Nat.add(1n, Nat.double(z)), uw(p, Word.zero(p)), 0n, A.uw_zero(p))
  Equal.trans(Word(1n+p), Word.add(1n+p, x, one_word(p)), S.from_nat(1n+p, Nat.add(ux, uw(1n+p, one_word(p)))), Word.inc(1n+p, x),
    WA.refines(1n+p, x, one_word(p)),
    Equal.trans(Word(1n+p), S.from_nat(1n+p, Nat.add(ux, uw(1n+p, one_word(p)))), S.from_nat(1n+p, 1n+ux), Word.inc(1n+p, x),
      Equal.cong(Nat, Word(1n+p), z => S.from_nat(1n+p, z), Nat.add(ux, uw(1n+p, one_word(p))), 1n+ux,
        Equal.trans(Nat, Nat.add(ux, uw(1n+p, one_word(p))), Nat.add(ux, 1n), 1n+ux, Equal.cong(Nat, Nat, z => Nat.add(ux, z), uw(1n+p, one_word(p)), 1n, u1), N.add_comm(ux, 1n))),
      Equal.sym(Word(1n+p), Word.inc(1n+p, x), S.from_nat(1n+p, 1n+ux), MA.increment_refines(1n+p, x))))

# ---- masks and powers of two ----

# the low k bits set
def mask(+n: Nat, +k: Nat) -> Word(n):
  SNUM.mask(n, k)

# the bits of x above the low k
def hi_part(+n: Nat, +k: Nat, +x: Word(n)) -> Nat:
  match n k x:
    case 0n _ WNil{}:
      0n
    case 1n+p 0n WCon{b, t}:
      uw(1n+p, WCon{b, t})
    case 1n+p 1n+j WCon{b, t}:
      hi_part(p, j, t)

def and_false_bv(+b: Bool) -> {S.bit_value(Bool.and(b, False{})) == 0n : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def and_zero(+p: Nat, +t: Word(p)) -> {uw(p, Word.and(p, t, mask(p, 0n))) == 0n : Nat}:
  match p t:
    case 0n WNil{}:
      {==}
    case 1n+q WCon{b, s}:
      %Equal.sym(Nat, S.bit_value(Bool.and(b, False{})), 0n, and_false_bv(b)) : {Nat.add(_, Nat.double(uw(q, Word.and(q, s, mask(q, 0n))))) == 0n : Nat}
      Equal.cong(Nat, Nat, z => Nat.double(z), uw(q, Word.and(q, s, mask(q, 0n))), 0n, and_zero(q, s))

def low0(+p: Nat, +b: Bool, +t: Word(p)) -> {uw(1n+p, Word.and(1n+p, WCon{b, t}, mask(1n+p, 0n))) == 0n : Nat}:
  match b:
    case True{}:
      Equal.cong(Nat, Nat, z => Nat.double(z), uw(p, Word.and(p, t, mask(p, 0n))), 0n, and_zero(p, t))
    case False{}:
      Equal.cong(Nat, Nat, z => Nat.double(z), uw(p, Word.and(p, t, mask(p, 0n))), 0n, and_zero(p, t))

# x == (x & mask k) + 2^k (bits above k)
def mask_split(+n: Nat, +k: Nat, +x: Word(n)) -> {uw(n, x) == Nat.add(uw(n, Word.and(n, x, mask(n, k))), sc(k, hi_part(n, k, x))) : Nat}:
  match n k x:
    case 0n _ WNil{}:
      Equal.sym(Nat, sc(k, 0n), 0n, A.sc_zero(k))
    case 1n+p 0n WCon{b, t}:
      %Equal.sym(Nat, uw(1n+p, Word.and(1n+p, WCon{b, t}, mask(1n+p, 0n))), 0n, low0(p, b, t)) : {uw(1n+p, WCon{b, t}) == Nat.add(_, uw(1n+p, WCon{b, t})) : Nat}
      {==}
    case 1n+p 1n+j WCon{b, t}:
      +at = uw(p, Word.and(p, t, mask(p, j)))
      +hs = sc(j, hi_part(p, j, t))
      %Equal.sym(Bool, Bool.and(b, True{}), b, U.and_true(b)) : {Nat.add(S.bit_value(b), Nat.double(uw(p, t))) == Nat.add(Nat.add(S.bit_value(_), Nat.double(at)), Nat.double(hs)) : Nat}
      %Equal.sym(Nat, uw(p, t), Nat.add(at, hs), mask_split(p, j, t)) : {Nat.add(S.bit_value(b), Nat.double(_)) == Nat.add(Nat.add(S.bit_value(b), Nat.double(at)), Nat.double(hs)) : Nat}
      Equal.trans(Nat, Nat.add(S.bit_value(b), Nat.double(Nat.add(at, hs))), Nat.add(S.bit_value(b), Nat.add(Nat.double(at), Nat.double(hs))), Nat.add(Nat.add(S.bit_value(b), Nat.double(at)), Nat.double(hs)),
        Equal.cong(Nat, Nat, z => Nat.add(S.bit_value(b), z), Nat.double(Nat.add(at, hs)), Nat.add(Nat.double(at), Nat.double(hs)), Equal.sym(Nat, Nat.add(Nat.double(at), Nat.double(hs)), Nat.double(Nat.add(at, hs)), N.add_double(at, hs))),
        Equal.sym(Nat, Nat.add(Nat.add(S.bit_value(b), Nat.double(at)), Nat.double(hs)), Nat.add(S.bit_value(b), Nat.add(Nat.double(at), Nat.double(hs))), N.add_assoc(S.bit_value(b), Nat.double(at), Nat.double(hs))))

def sc_pos(+k: Nat) -> {Nat.is_lt(0n, sc(k, 1n)) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      N.double_lt(0n, sc(j, 1n), sc_pos(j))

# x & mask k is below 2^k
def mask_lt(+n: Nat, +k: Nat, +one: Nat, +h1: {one == 1n : Nat}, +x: Word(n)) -> {Nat.is_lt(uw(n, Word.and(n, x, mask(n, k))), sc(k, one)) == True{} : Bool}:
  match n k x:
    case 0n _ WNil{}:
      lt1r(k, one, h1, 0n, sc_pos(k))
    case 1n+p 0n WCon{b, t}:
      +z = uw(1n+p, Word.and(1n+p, WCon{b, t}, mask(1n+p, 0n)))
      L.subst(Nat, o => {Nat.is_lt(z, o) == True{} : Bool}, 1n, one, Equal.sym(Nat, one, 1n, h1), L.subst(Nat, w => {Nat.is_lt(w, 1n) == True{} : Bool}, 0n, z, Equal.sym(Nat, z, 0n, low0(p, b, t)), {==}))
    case 1n+p 1n+j WCon{b, t}:
      N.double_lt_bit(Bool.and(b, True{}), uw(p, Word.and(p, t, mask(p, j))), sc(j, one), mask_lt(p, j, one, h1, t))

# 2^k as an n-bit word
def pw(+n: Nat, +k: Nat) -> Word(n):
  match n k:
    case 0n _:
      WNil{}
    case 1n+p 0n:
      WCon{True{}, Word.zero(p)}
    case 1n+p 1n+j:
      WCon{False{}, pw(p, j)}

def pw_val(+n: Nat, +k: Nat, +hk: {Nat.is_lt(k, n) == True{} : Bool}) -> {uw(n, pw(n, k)) == sc(k, 1n) : Nat}:
  match n k:
    case 0n _:
      Empty.absurd({uw(0n, pw(0n, k)) == sc(k, 1n) : Nat}, N.lt_zero_absurd(k, hk))
    case 1n+p 0n:
      Equal.cong(Nat, Nat, z => Nat.add(1n, Nat.double(z)), uw(p, Word.zero(p)), 0n, A.uw_zero(p))
    case 1n+p 1n+j:
      Equal.cong(Nat, Nat, Nat.double, uw(p, pw(p, j)), sc(j, 1n), pw_val(p, j, hk))

# a word known to be 2^k has value 2^k (the word stays a variable)
def pwv(+n: Nat, +k: Nat, +hk: {Nat.is_lt(k, n) == True{} : Bool}, +one: Nat, +h1: {one == 1n : Nat}, +c: Word(n), +hc: {c == pw(n, k) : Word(n)}) -> {uw(n, c) == sc(k, one) : Nat}:
  +e = L.subst(Word(n), w => {uw(n, w) == sc(k, 1n) : Nat}, pw(n, k), c, Equal.sym(Word(n), c, pw(n, k), hc), pw_val(n, k, hk))
  L.subst(Nat, o => {uw(n, c) == S.scale_binary(k, o) : Nat}, 1n, one, Equal.sym(Nat, one, 1n, h1), e)

# an increment below 2^n is exact
def inc_exact(+n: Nat, +one: Nat, +h1: {one == 1n : Nat}, +w: Word(n), +h: {Nat.is_lt(1n+uw(n, w), sc(n, one)) == True{} : Bool}) -> {uw(n, Word.inc(n, w)) == 1n+uw(n, w) : Nat}:
  %Equal.sym(Word(n), Word.inc(n, w), S.from_nat(n, 1n+uw(n, w)), MA.increment_refines(n, w)) : {S.unsigned(n, _) == 1n+uw(n, w) : Nat}
  WV.from_nat_value(n, 1n+uw(n, w), L.subst(Nat, z => {Nat.is_lt(1n+uw(n, w), z) == True{} : Bool}, S.scale_binary(n, 1n), Nat.pow(2n, n), NM.scale_power(n), lt1(n, one, h1, 1n+uw(n, w), h)))
