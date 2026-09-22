import Base
import ../lemmas/spec/numeric.bend as S
import ../lib/nat.bend as N
import ../lib/logic.bend as L
import ../lib/u32.bend as U
import ../lib/u32alg.bend as A
import ../lemmas/proofs/addition_bounds.bend as AB
import ../lemmas/proofs/word_multiplication.bend as WM
import ../lemmas/proofs/word_value.bend as WV
import ../lemmas/proofs/negation_magnitude.bend as NM

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
