import Base
import ./logic.bend as L
import ./nat.bend as N
import ./u32.bend as U
import ./lemmas/spec/numeric.bend as S
import ./lemmas/proofs/addition.bend as AD
import ./lemmas/proofs/division_quotient.bend as DQ

# Modular (U32) addition algebra, derived from Base's Word adder through
# the retained LRU carry-conservation law
#   unsigned(adc a b c) + 2^n * carry == c + unsigned a + unsigned b
# and uniqueness of the representation r + 2^n * k with r < 2^n.

def sc(+n: Nat, +k: Nat) -> Nat:
  S.scale_binary(n, k)

def uw(+n: Nat, +w: Word(n)) -> Nat:
  S.unsigned(n, w)

def cy(+n: Nat, +a: Word(n), +b: Word(n), +c: Bool) -> Nat:
  S.bit_value(AD.carry_out(n, a, b, c))

# ---- Nat helpers ----

def add_cancel_r(+a: Nat, +b: Nat, +c: Nat, +e: {Nat.add(a, c) == Nat.add(b, c) : Nat}) -> {a == b : Nat}:
  match c:
    case 0n:
      Equal.trans(Nat, a, Nat.add(a, 0n), b, Equal.sym(Nat, Nat.add(a, 0n), a, N.add_zero(a)), Equal.trans(Nat, Nat.add(a, 0n), Nat.add(b, 0n), b, e, N.add_zero(b)))
    case 1n+k:
      add_cancel_r(a, b, k, N.succ_inj(Nat.add(a, k), Nat.add(b, k), Equal.trans(Nat, 1n+Nat.add(a, k), Nat.add(a, 1n+k), 1n+Nat.add(b, k), Equal.sym(Nat, Nat.add(a, 1n+k), 1n+Nat.add(a, k), N.add_succ(a, k)), Equal.trans(Nat, Nat.add(a, 1n+k), Nat.add(b, 1n+k), 1n+Nat.add(b, k), e, N.add_succ(b, k)))))

# (a + b) + c == (a + c) + b
def add_rot(+a: Nat, +b: Nat, +c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(Nat.add(a, c), b) : Nat}:
  %Equal.sym(Nat, Nat.add(Nat.add(a, b), c), Nat.add(a, Nat.add(b, c)), N.add_assoc(a, b, c)) : {_ == Nat.add(Nat.add(a, c), b) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(a, c), b), Nat.add(a, Nat.add(c, b)), N.add_assoc(a, c, b)) : {Nat.add(a, Nat.add(b, c)) == _ : Nat}
  %N.add_comm(c, b) : {Nat.add(a, _) == Nat.add(a, Nat.add(c, b)) : Nat}
  {==}

def sc_zero(+n: Nat) -> {sc(n, 0n) == 0n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, sc(p, 0n), 0n, sc_zero(p)) : {Nat.double(_) == 0n : Nat}
      {==}

def sc_add(+n: Nat, +x: Nat, +y: Nat) -> {Nat.add(sc(n, x), sc(n, y)) == sc(n, Nat.add(x, y)) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.add(Nat.double(sc(p, x)), Nat.double(sc(p, y))), Nat.double(Nat.add(sc(p, x), sc(p, y))), N.add_double(sc(p, x), sc(p, y))) : {_ == Nat.double(sc(p, Nat.add(x, y))) : Nat}
      Equal.cong(Nat, Nat, Nat.double, Nat.add(sc(p, x), sc(p, y)), sc(p, Nat.add(x, y)), sc_add(p, x, y))

# M <= r + (M + s)
def le_shift(+r: Nat, +m: Nat, +s: Nat) -> {Nat.is_le(m, Nat.add(r, Nat.add(m, s))) == True{} : Bool}:
  %N.add_comm(Nat.add(m, s), r) : {Nat.is_le(m, _) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(Nat.add(m, s), r), Nat.add(m, Nat.add(s, r)), N.add_assoc(m, s, r)) : {Nat.is_le(m, _) == True{} : Bool}
  N.le_add_right(m, Nat.add(s, r))

def sc_succ(+n: Nat, +x: Nat) -> {sc(n, 1n+x) == Nat.add(sc(n, 1n), sc(n, x)) : Nat}:
  Equal.sym(Nat, Nat.add(sc(n, 1n), sc(n, x)), sc(n, Nat.add(1n, x)), sc_add(n, 1n, x))

# r1 < 2^n cannot equal r2 + 2^n (1 + q).
def uniq_gap(+n: Nat, +r1: Nat, +r2: Nat, +q: Nat, +h: {Nat.add(r1, sc(n, 0n)) == Nat.add(r2, sc(n, 1n+q)) : Nat}, +b1: {Nat.is_lt(r1, sc(n, 1n)) == True{} : Bool}) -> Empty:
  +e = Equal.trans(Nat, r1, Nat.add(r1, sc(n, 0n)), Nat.add(r2, Nat.add(sc(n, 1n), sc(n, q))),
    %Equal.sym(Nat, sc(n, 0n), 0n, sc_zero(n)) : {r1 == Nat.add(r1, _) : Nat}
    Equal.sym(Nat, Nat.add(r1, 0n), r1, N.add_zero(r1)),
    %sc_succ(n, q) : {Nat.add(r1, sc(n, 0n)) == Nat.add(r2, _) : Nat}
    h)
  L.true_false(Equal.trans(Bool, True{}, Nat.is_le(sc(n, 1n), r1), False{}, Equal.sym(Bool, Nat.is_le(sc(n, 1n), r1), True{}, L.subst(Nat, z => {Nat.is_le(sc(n, 1n), z) == True{} : Bool}, Nat.add(r2, Nat.add(sc(n, 1n), sc(n, q))), r1, Equal.sym(Nat, r1, Nat.add(r2, Nat.add(sc(n, 1n), sc(n, q))), e), le_shift(r2, sc(n, 1n), sc(n, q)))), N.lt_not_le(r1, sc(n, 1n), b1)))

# r1 + 2^n x == r2 + 2^n y with r1, r2 < 2^n forces r1 == r2.
def uniq(+n: Nat, +r1: Nat, +r2: Nat, +x: Nat, +y: Nat, +h: {Nat.add(r1, sc(n, x)) == Nat.add(r2, sc(n, y)) : Nat}, +b1: {Nat.is_lt(r1, sc(n, 1n)) == True{} : Bool}, +b2: {Nat.is_lt(r2, sc(n, 1n)) == True{} : Bool}) -> {r1 == r2 : Nat}:
  match x y:
    case 0n 0n:
      +h0 = L.subst(Nat, q => {Nat.add(r1, q) == Nat.add(r2, q) : Nat}, sc(n, 0n), 0n, sc_zero(n), h)
      add_cancel_r(r1, r2, 0n, h0)
    case 0n 1n+q:
      Empty.absurd({r1 == r2 : Nat}, uniq_gap(n, r1, r2, q, h, b1))
    case 1n+p 0n:
      Empty.absurd({r1 == r2 : Nat}, uniq_gap(n, r2, r1, p, Equal.sym(Nat, Nat.add(r1, sc(n, 1n+p)), Nat.add(r2, sc(n, 0n)), h), b2))
    case 1n+p 1n+q:
      -Mn = sc(n, 1n)
      +h1 = L.subst(Nat, z => {Nat.add(r1, z) == Nat.add(r2, sc(n, 1n+q)) : Nat}, sc(n, 1n+p), Nat.add(sc(n, 1n), sc(n, p)), sc_succ(n, p), h)
      +h2 = L.subst(Nat, z => {Nat.add(r1, Nat.add(sc(n, 1n), sc(n, p))) == Nat.add(r2, z) : Nat}, sc(n, 1n+q), Nat.add(sc(n, 1n), sc(n, q)), sc_succ(n, q), h1)
      +l1 = Equal.trans(Nat, Nat.add(Nat.add(r1, sc(n, p)), sc(n, 1n)), Nat.add(r1, Nat.add(sc(n, p), sc(n, 1n))), Nat.add(r1, Nat.add(sc(n, 1n), sc(n, p))), N.add_assoc(r1, sc(n, p), sc(n, 1n)), Equal.cong(Nat, Nat, z => Nat.add(r1, z), Nat.add(sc(n, p), sc(n, 1n)), Nat.add(sc(n, 1n), sc(n, p)), N.add_comm(sc(n, p), sc(n, 1n))))
      +l2 = Equal.trans(Nat, Nat.add(Nat.add(r2, sc(n, q)), sc(n, 1n)), Nat.add(r2, Nat.add(sc(n, q), sc(n, 1n))), Nat.add(r2, Nat.add(sc(n, 1n), sc(n, q))), N.add_assoc(r2, sc(n, q), sc(n, 1n)), Equal.cong(Nat, Nat, z => Nat.add(r2, z), Nat.add(sc(n, q), sc(n, 1n)), Nat.add(sc(n, 1n), sc(n, q)), N.add_comm(sc(n, q), sc(n, 1n))))
      uniq(n, r1, r2, p, q, add_cancel_r(Nat.add(r1, sc(n, p)), Nat.add(r2, sc(n, q)), sc(n, 1n), Equal.trans(Nat, Nat.add(Nat.add(r1, sc(n, p)), sc(n, 1n)), Nat.add(r1, Nat.add(sc(n, 1n), sc(n, p))), Nat.add(Nat.add(r2, sc(n, q)), sc(n, 1n)), l1, Equal.trans(Nat, Nat.add(r1, Nat.add(sc(n, 1n), sc(n, p))), Nat.add(r2, Nat.add(sc(n, 1n), sc(n, q))), Nat.add(Nat.add(r2, sc(n, q)), sc(n, 1n)), h2, Equal.sym(Nat, Nat.add(Nat.add(r2, sc(n, q)), sc(n, 1n)), Nat.add(r2, Nat.add(sc(n, 1n), sc(n, q))), l2)))), b1, b2)

# ---- words ----

def w_inj(+n: Nat, +a: Word(n), +b: Word(n), +e: {uw(n, a) == uw(n, b) : Nat}) -> {a == b : Word(n)}:
  Equal.trans(Word(n), a, S.from_nat(n, uw(n, a)), b, Equal.sym(Word(n), S.from_nat(n, uw(n, a)), a, DQ.reconstruct(n, a)),
    Equal.trans(Word(n), S.from_nat(n, uw(n, a)), S.from_nat(n, uw(n, b)), b, Equal.cong(Nat, Word(n), v => S.from_nat(n, v), uw(n, a), uw(n, b), e), DQ.reconstruct(n, b)))

def cons(+n: Nat, +a: Word(n), +b: Word(n)) -> {Nat.add(uw(n, Word.add(n, a, b)), sc(n, cy(n, a, b, False{}))) == Nat.add(uw(n, a), uw(n, b)) : Nat}:
  AD.adc_conservation(n, a, b, False{})

def uw_zero(+n: Nat) -> {uw(n, Word.zero(n)) == 0n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, uw(p, Word.zero(p)), 0n, uw_zero(p)) : {Nat.add(0n, Nat.double(_)) == 0n : Nat}
      {==}

def w_zero_add(+n: Nat, +b: Word(n)) -> {Word.add(n, Word.zero(n), b) == b : Word(n)}:
  +e = cons(n, Word.zero(n), b)
  +e2 = Equal.trans(Nat, Nat.add(uw(n, Word.add(n, Word.zero(n), b)), sc(n, cy(n, Word.zero(n), b, False{}))), Nat.add(uw(n, Word.zero(n)), uw(n, b)), Nat.add(uw(n, b), sc(n, 0n)), e,
    %Equal.sym(Nat, uw(n, Word.zero(n)), 0n, uw_zero(n)) : {Nat.add(_, uw(n, b)) == Nat.add(uw(n, b), sc(n, 0n)) : Nat}
    %Equal.sym(Nat, sc(n, 0n), 0n, sc_zero(n)) : {uw(n, b) == Nat.add(uw(n, b), _) : Nat}
    Equal.sym(Nat, Nat.add(uw(n, b), 0n), uw(n, b), N.add_zero(uw(n, b))))
  w_inj(n, Word.add(n, Word.zero(n), b), b, uniq(n, uw(n, Word.add(n, Word.zero(n), b)), uw(n, b), cy(n, Word.zero(n), b, False{}), 0n, e2, U.WB_unsigned(n, Word.add(n, Word.zero(n), b)), U.WB_unsigned(n, b)))

def w_assoc(+n: Nat, +a: Word(n), +b: Word(n), +c: Word(n)) -> {Word.add(n, Word.add(n, a, b), c) == Word.add(n, a, Word.add(n, b, c)) : Word(n)}:
  -s = Word.add(n, a, b)
  -t = Word.add(n, b, c)
  +ua = uw(n, a)
  +ub = uw(n, b)
  +uc = uw(n, c)
  +us = uw(n, Word.add(n, a, b))
  +ut = uw(n, Word.add(n, b, c))
  +uL = uw(n, Word.add(n, Word.add(n, a, b), c))
  +uR = uw(n, Word.add(n, a, Word.add(n, b, c)))
  +c1 = cy(n, a, b, False{})
  +c2 = cy(n, b, c, False{})
  +c3 = cy(n, Word.add(n, a, b), c, False{})
  +c4 = cy(n, a, Word.add(n, b, c), False{})
  +e1 = cons(n, Word.add(n, a, b), c)
  +e2 = cons(n, a, b)
  +e3 = cons(n, a, Word.add(n, b, c))
  +e4 = cons(n, b, c)
  # uL + sc(c3 + c1) == (ua + ub) + uc
  +left = Equal.trans(Nat, Nat.add(uL, sc(n, Nat.add(c3, c1))), Nat.add(Nat.add(uL, sc(n, c3)), sc(n, c1)), Nat.add(Nat.add(ua, ub), uc),
    %sc_add(n, c3, c1) : {Nat.add(uL, _) == Nat.add(Nat.add(uL, sc(n, c3)), sc(n, c1)) : Nat}
    Equal.sym(Nat, Nat.add(Nat.add(uL, sc(n, c3)), sc(n, c1)), Nat.add(uL, Nat.add(sc(n, c3), sc(n, c1))), N.add_assoc(uL, sc(n, c3), sc(n, c1))),
    %Equal.sym(Nat, Nat.add(uL, sc(n, c3)), Nat.add(us, uc), e1) : {Nat.add(_, sc(n, c1)) == Nat.add(Nat.add(ua, ub), uc) : Nat}
    %Equal.sym(Nat, Nat.add(Nat.add(us, uc), sc(n, c1)), Nat.add(Nat.add(us, sc(n, c1)), uc), add_rot(us, uc, sc(n, c1))) : {_ == Nat.add(Nat.add(ua, ub), uc) : Nat}
    %Equal.sym(Nat, Nat.add(us, sc(n, c1)), Nat.add(ua, ub), e2) : {Nat.add(_, uc) == Nat.add(Nat.add(ua, ub), uc) : Nat}
    {==})
  # uR + sc(c4 + c2) == (ua + ub) + uc
  +right = Equal.trans(Nat, Nat.add(uR, sc(n, Nat.add(c4, c2))), Nat.add(Nat.add(uR, sc(n, c4)), sc(n, c2)), Nat.add(Nat.add(ua, ub), uc),
    %sc_add(n, c4, c2) : {Nat.add(uR, _) == Nat.add(Nat.add(uR, sc(n, c4)), sc(n, c2)) : Nat}
    Equal.sym(Nat, Nat.add(Nat.add(uR, sc(n, c4)), sc(n, c2)), Nat.add(uR, Nat.add(sc(n, c4), sc(n, c2))), N.add_assoc(uR, sc(n, c4), sc(n, c2))),
    %Equal.sym(Nat, Nat.add(uR, sc(n, c4)), Nat.add(ua, ut), e3) : {Nat.add(_, sc(n, c2)) == Nat.add(Nat.add(ua, ub), uc) : Nat}
    %Equal.sym(Nat, Nat.add(Nat.add(ua, ut), sc(n, c2)), Nat.add(ua, Nat.add(ut, sc(n, c2))), N.add_assoc(ua, ut, sc(n, c2))) : {_ == Nat.add(Nat.add(ua, ub), uc) : Nat}
    %Equal.sym(Nat, Nat.add(ut, sc(n, c2)), Nat.add(ub, uc), e4) : {Nat.add(ua, _) == Nat.add(Nat.add(ua, ub), uc) : Nat}
    Equal.sym(Nat, Nat.add(Nat.add(ua, ub), uc), Nat.add(ua, Nat.add(ub, uc)), N.add_assoc(ua, ub, uc)))
  w_inj(n, Word.add(n, Word.add(n, a, b), c), Word.add(n, a, Word.add(n, b, c)), uniq(n, uL, uR, Nat.add(c3, c1), Nat.add(c4, c2), Equal.trans(Nat, Nat.add(uL, sc(n, Nat.add(c3, c1))), Nat.add(Nat.add(ua, ub), uc), Nat.add(uR, sc(n, Nat.add(c4, c2))), left, Equal.sym(Nat, Nat.add(uR, sc(n, Nat.add(c4, c2))), Nat.add(Nat.add(ua, ub), uc), right)), U.WB_unsigned(n, Word.add(n, Word.add(n, a, b), c)), U.WB_unsigned(n, Word.add(n, a, Word.add(n, b, c)))))

# ---- subtraction ----

def adc_con_not(+p: Nat, +at: Word(p), +bt: Word(p), sk: Bool & Bool, ih: @+k: Bool -> {Word.adc(p, at, bt, True{}, k) == Word.adc(p, at, Word.not(p, bt), False{}, k) : Word(p)}) -> {Word.adc.con(p, at, bt, True{}, sk) == Word.adc.con(p, at, Word.not(p, bt), False{}, sk) : Word(1n+p)}:
  match sk:
    case Tuple{s, k}:
      Equal.cong(Word(p), Word(1n+p), w => WCon{s, w}, Word.adc(p, at, bt, True{}, k), Word.adc(p, at, Word.not(p, bt), False{}, k), ih(k))

# Subtraction is addition of the complement with an incoming carry.
def adc_not(+n: Nat, +a: Word(n), +b: Word(n), +c: Bool) -> {Word.adc(n, a, b, True{}, c) == Word.adc(n, a, Word.not(n, b), False{}, c) : Word(n)}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match a b:
        case WCon{x, at} WCon{y, bt}:
          adc_con_not(p, at, bt, Bool.full_add(x, Bool.not(y), c), k => adc_not(p, at, bt, k))

# 1 + unsigned(not b) + unsigned(b) == 2^n
def not_value(+n: Nat, +b: Word(n)) -> {Nat.add(1n, Nat.add(uw(n, Word.not(n, b)), uw(n, b))) == sc(n, 1n) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match b:
        case WCon{True{}, bt}:
          +ih = not_value(p, bt)
          -A = uw(p, Word.not(p, bt))
          -B = uw(p, bt)
          # 1 + (0 + 2A) + (1 + 2B) == 2 (1 + (A + B))
          %Equal.sym(Nat, Nat.add(Nat.double(uw(p, Word.not(p, bt))), 1n+Nat.double(uw(p, bt))), 1n+Nat.add(Nat.double(uw(p, Word.not(p, bt))), Nat.double(uw(p, bt))), N.add_succ(Nat.double(uw(p, Word.not(p, bt))), Nat.double(uw(p, bt)))) : {1n+_ == Nat.double(sc(p, 1n)) : Nat}
          %Equal.sym(Nat, sc(p, 1n), Nat.add(1n, Nat.add(uw(p, Word.not(p, bt)), uw(p, bt))), Equal.sym(Nat, Nat.add(1n, Nat.add(uw(p, Word.not(p, bt)), uw(p, bt))), sc(p, 1n), ih)) : {2n+Nat.add(Nat.double(uw(p, Word.not(p, bt))), Nat.double(uw(p, bt))) == Nat.double(_) : Nat}
          Equal.cong(Nat, Nat, z => 2n+z, Nat.add(Nat.double(uw(p, Word.not(p, bt))), Nat.double(uw(p, bt))), Nat.double(Nat.add(uw(p, Word.not(p, bt)), uw(p, bt))), N.add_double(uw(p, Word.not(p, bt)), uw(p, bt)))
        case WCon{False{}, bt}:
          +ih = not_value(p, bt)
          %Equal.sym(Nat, sc(p, 1n), Nat.add(1n, Nat.add(uw(p, Word.not(p, bt)), uw(p, bt))), Equal.sym(Nat, Nat.add(1n, Nat.add(uw(p, Word.not(p, bt)), uw(p, bt))), sc(p, 1n), ih)) : {2n+Nat.add(Nat.double(uw(p, Word.not(p, bt))), Nat.double(uw(p, bt))) == Nat.double(_) : Nat}
          Equal.cong(Nat, Nat, z => 2n+z, Nat.add(Nat.double(uw(p, Word.not(p, bt))), Nat.double(uw(p, bt))), Nat.double(Nat.add(uw(p, Word.not(p, bt)), uw(p, bt))), N.add_double(uw(p, Word.not(p, bt)), uw(p, bt)))

def cons_sub(+n: Nat, +x: Word(n), +a: Word(n)) -> {Nat.add(uw(n, Word.sub(n, x, a)), sc(n, cy(n, x, Word.not(n, a), True{}))) == Nat.add(1n, Nat.add(uw(n, x), uw(n, Word.not(n, a)))) : Nat}:
  %Equal.sym(Word(n), Word.adc(n, x, a, True{}, True{}), Word.adc(n, x, Word.not(n, a), False{}, True{}), adc_not(n, x, a, True{})) : {Nat.add(uw(n, _), sc(n, cy(n, x, Word.not(n, a), True{}))) == Nat.add(1n, Nat.add(uw(n, x), uw(n, Word.not(n, a)))) : Nat}
  AD.adc_conservation(n, x, Word.not(n, a), True{})

# (a + b) - a == b
def arith_sub(+ux: Nat, +un: Nat, +ua: Nat, +ub: Nat, +k: Nat, +e: {Nat.add(ux, k) == Nat.add(ua, ub) : Nat}) -> {Nat.add(Nat.add(1n, Nat.add(ux, un)), k) == Nat.add(ub, Nat.add(1n, Nat.add(un, ua))) : Nat}:
  # both sides are 1 + ((ua + ub) + un)
  +p1 = N.succ_cong(Nat.add(Nat.add(ux, un), k), Nat.add(Nat.add(ua, ub), un), Equal.trans(Nat, Nat.add(Nat.add(ux, un), k), Nat.add(Nat.add(ux, k), un), Nat.add(Nat.add(ua, ub), un), add_rot(ux, un, k), Equal.cong(Nat, Nat, z => Nat.add(z, un), Nat.add(ux, k), Nat.add(ua, ub), e)))
  +q = Equal.trans(Nat, Nat.add(Nat.add(ua, ub), un), Nat.add(ua, Nat.add(ub, un)), Nat.add(ub, Nat.add(un, ua)), N.add_assoc(ua, ub, un), Equal.trans(Nat, Nat.add(ua, Nat.add(ub, un)), Nat.add(Nat.add(ub, un), ua), Nat.add(ub, Nat.add(un, ua)), N.add_comm(ua, Nat.add(ub, un)), N.add_assoc(ub, un, ua)))
  Equal.trans(Nat, Nat.add(Nat.add(1n, Nat.add(ux, un)), k), 1n+Nat.add(Nat.add(ua, ub), un), Nat.add(ub, Nat.add(1n, Nat.add(un, ua))), p1,
    Equal.trans(Nat, 1n+Nat.add(Nat.add(ua, ub), un), 1n+Nat.add(ub, Nat.add(un, ua)), Nat.add(ub, 1n+Nat.add(un, ua)), N.succ_cong(Nat.add(Nat.add(ua, ub), un), Nat.add(ub, Nat.add(un, ua)), q), Equal.sym(Nat, Nat.add(ub, 1n+Nat.add(un, ua)), 1n+Nat.add(ub, Nat.add(un, ua)), N.add_succ(ub, Nat.add(un, ua)))))

# (v - a) + a == v
def w_add_sub(+n: Nat, +a: Word(n), +b: Word(n)) -> {Word.sub(n, Word.add(n, a, b), a) == b : Word(n)}:
  +ux = uw(n, Word.add(n, a, b))
  +ua = uw(n, a)
  +ub = uw(n, b)
  +un = uw(n, Word.not(n, a))
  +r = uw(n, Word.sub(n, Word.add(n, a, b), a))
  +c1 = cy(n, a, b, False{})
  +c5 = cy(n, Word.add(n, a, b), Word.not(n, a), True{})
  +e2 = cons(n, a, b)
  +e5 = cons_sub(n, Word.add(n, a, b), a)
  +nv = not_value(n, a)
  # r + sc(c5 + c1) == ub + sc(1)
  +chain = Equal.trans(Nat, Nat.add(r, sc(n, Nat.add(c5, c1))), Nat.add(Nat.add(r, sc(n, c5)), sc(n, c1)), Nat.add(ub, sc(n, 1n)),
    %sc_add(n, c5, c1) : {Nat.add(r, _) == Nat.add(Nat.add(r, sc(n, c5)), sc(n, c1)) : Nat}
    Equal.sym(Nat, Nat.add(Nat.add(r, sc(n, c5)), sc(n, c1)), Nat.add(r, Nat.add(sc(n, c5), sc(n, c1))), N.add_assoc(r, sc(n, c5), sc(n, c1))),
    %Equal.sym(Nat, Nat.add(r, sc(n, c5)), Nat.add(1n, Nat.add(ux, un)), e5) : {Nat.add(_, sc(n, c1)) == Nat.add(ub, sc(n, 1n)) : Nat}
    %nv : {Nat.add(Nat.add(1n, Nat.add(ux, un)), sc(n, c1)) == Nat.add(ub, _) : Nat}
    arith_sub(ux, un, ua, ub, sc(n, c1), e2))
  w_inj(n, Word.sub(n, Word.add(n, a, b), a), b, uniq(n, r, ub, Nat.add(c5, c1), 1n, chain, U.WB_unsigned(n, Word.sub(n, Word.add(n, a, b), a)), U.WB_unsigned(n, b)))

# (v - a) + a == v
def w_sub_add(+n: Nat, +v: Word(n), +a: Word(n)) -> {Word.add(n, Word.sub(n, v, a), a) == v : Word(n)}:
  +uv = uw(n, v)
  +ua = uw(n, a)
  +un = uw(n, Word.not(n, a))
  +us = uw(n, Word.sub(n, v, a))
  +ut = uw(n, Word.add(n, Word.sub(n, v, a), a))
  +c5 = cy(n, v, Word.not(n, a), True{})
  +c6 = cy(n, Word.sub(n, v, a), a, False{})
  +e5 = cons_sub(n, v, a)
  +e6 = cons(n, Word.sub(n, v, a), a)
  +nv = not_value(n, a)
  +tail = Equal.trans(Nat, Nat.add(Nat.add(1n, Nat.add(uv, un)), ua), 1n+Nat.add(uv, Nat.add(un, ua)), Nat.add(uv, sc(n, 1n)),
    N.succ_cong(Nat.add(Nat.add(uv, un), ua), Nat.add(uv, Nat.add(un, ua)), N.add_assoc(uv, un, ua)),
    Equal.trans(Nat, 1n+Nat.add(uv, Nat.add(un, ua)), Nat.add(uv, 1n+Nat.add(un, ua)), Nat.add(uv, sc(n, 1n)), Equal.sym(Nat, Nat.add(uv, 1n+Nat.add(un, ua)), 1n+Nat.add(uv, Nat.add(un, ua)), N.add_succ(uv, Nat.add(un, ua))), Equal.cong(Nat, Nat, z => Nat.add(uv, z), Nat.add(1n, Nat.add(un, ua)), sc(n, 1n), nv)))
  +chain = Equal.trans(Nat, Nat.add(ut, sc(n, Nat.add(c6, c5))), Nat.add(Nat.add(ut, sc(n, c6)), sc(n, c5)), Nat.add(uv, sc(n, 1n)),
    %sc_add(n, c6, c5) : {Nat.add(ut, _) == Nat.add(Nat.add(ut, sc(n, c6)), sc(n, c5)) : Nat}
    Equal.sym(Nat, Nat.add(Nat.add(ut, sc(n, c6)), sc(n, c5)), Nat.add(ut, Nat.add(sc(n, c6), sc(n, c5))), N.add_assoc(ut, sc(n, c6), sc(n, c5))),
    %Equal.sym(Nat, Nat.add(ut, sc(n, c6)), Nat.add(us, ua), e6) : {Nat.add(_, sc(n, c5)) == Nat.add(uv, sc(n, 1n)) : Nat}
    %Equal.sym(Nat, Nat.add(Nat.add(us, ua), sc(n, c5)), Nat.add(Nat.add(us, sc(n, c5)), ua), add_rot(us, ua, sc(n, c5))) : {_ == Nat.add(uv, sc(n, 1n)) : Nat}
    %Equal.sym(Nat, Nat.add(us, sc(n, c5)), Nat.add(1n, Nat.add(uv, un)), e5) : {Nat.add(_, ua) == Nat.add(uv, sc(n, 1n)) : Nat}
    tail)
  w_inj(n, Word.add(n, Word.sub(n, v, a), a), v, uniq(n, ut, uv, Nat.add(c6, c5), 1n, chain, U.WB_unsigned(n, Word.add(n, Word.sub(n, v, a), a)), U.WB_unsigned(n, v)))

# Doubling by shifting: shl.put n c w == w + w + c.
def shl_adc(+n: Nat, +w: Word(n), +c: Bool) -> {Word.shl.put(n, c, w) == Word.adc(n, w, w, False{}, c) : Word(n)}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{True{}, t}:
          match c:
            case True{}:
              Equal.cong(Word(p), Word(1n+p), x => WCon{True{}, x}, Word.shl.put(p, True{}, t), Word.adc(p, t, t, False{}, True{}), shl_adc(p, t, True{}))
            case False{}:
              Equal.cong(Word(p), Word(1n+p), x => WCon{False{}, x}, Word.shl.put(p, True{}, t), Word.adc(p, t, t, False{}, True{}), shl_adc(p, t, True{}))
        case WCon{False{}, t}:
          match c:
            case True{}:
              Equal.cong(Word(p), Word(1n+p), x => WCon{True{}, x}, Word.shl.put(p, False{}, t), Word.adc(p, t, t, False{}, False{}), shl_adc(p, t, False{}))
            case False{}:
              Equal.cong(Word(p), Word(1n+p), x => WCon{False{}, x}, Word.shl.put(p, False{}, t), Word.adc(p, t, t, False{}, False{}), shl_adc(p, t, False{}))

def w_shl(+n: Nat, +w: Word(n)) -> {Word.shl(n, w) == Word.add(n, w, w) : Word(n)}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{b, t}:
          shl_adc(1n+p, WCon{b, t}, False{})

# ---- U32 ----

def assoc(+a: U32, +b: U32, +c: U32) -> {U32.add(U32.add(a, b), c) == U32.add(a, U32.add(b, c)) : U32}:
  match a b c:
    case U32{x} U32{y} U32{z}:
      Equal.cong(Word(32n), U32, w => U32{w}, Word.add(32n, Word.add(32n, x, y), z), Word.add(32n, x, Word.add(32n, y, z)), w_assoc(32n, x, y, z))

def comm(+a: U32, +b: U32) -> {U32.add(a, b) == U32.add(b, a) : U32}:
  U32.add_comm(a, b)

def zero_add(+b: U32) -> {U32.add(0, b) == b : U32}:
  match b:
    case U32{y}:
      Equal.cong(Word(32n), U32, w => U32{w}, Word.add(32n, Word.zero(32n), y), y, w_zero_add(32n, y))

def add_zero(+b: U32) -> {U32.add(b, 0) == b : U32}:
  Equal.trans(U32, U32.add(b, 0), U32.add(0, b), b, U32.add_comm(b, 0), zero_add(b))

def add_sub(+a: U32, +b: U32) -> {U32.sub(U32.add(a, b), a) == b : U32}:
  match a b:
    case U32{x} U32{y}:
      Equal.cong(Word(32n), U32, w => U32{w}, Word.sub(32n, Word.add(32n, x, y), x), y, w_add_sub(32n, x, y))

def sub_add(+v: U32, +a: U32) -> {U32.add(U32.sub(v, a), a) == v : U32}:
  match v a:
    case U32{x} U32{y}:
      Equal.cong(Word(32n), U32, w => U32{w}, Word.add(32n, Word.sub(32n, x, y), y), x, w_sub_add(32n, x, y))

def shl_add(+x: U32) -> {U32.shl(x) == U32.add(x, x) : U32}:
  match x:
    case U32{w}:
      Equal.cong(Word(32n), U32, v => U32{v}, Word.shl(32n, w), Word.add(32n, w, w), w_shl(32n, w))

# a + (b + c) == b + (a + c)
def swap(+a: U32, +b: U32, +c: U32) -> {U32.add(a, U32.add(b, c)) == U32.add(b, U32.add(a, c)) : U32}:
  %assoc(a, b, c) : {_ == U32.add(b, U32.add(a, c)) : U32}
  %assoc(b, a, c) : {U32.add(U32.add(a, b), c) == _ : U32}
  %U32.add_comm(a, b) : {U32.add(U32.add(a, b), c) == U32.add(_, c) : U32}
  {==}

# ---- U32 equality as a Bool ----

def eq_of(+a: U32, +b: U32, +h: {U32.is_eq(a, b) == True{} : Bool}) -> {a == b : U32}:
  U.injective(a, b, N.eq_from_is_eq(U32.to_nat(a), U32.to_nat(b), L.subst(Cmp, c => {Cmp.is_eq(c) == True{} : Bool}, U32.cmp(a, b), Nat.cmp(U32.to_nat(a), U32.to_nat(b)), U.u32_cmp(a, b), h)))

def eq_refl(+a: U32) -> {U32.is_eq(a, a) == True{} : Bool}:
  %Equal.sym(Cmp, U32.cmp(a, a), Nat.cmp(U32.to_nat(a), U32.to_nat(a)), U.u32_cmp(a, a)) : {Cmp.is_eq(_) == True{} : Bool}
  N.is_eq_refl(U32.to_nat(a))

def eq_true(+a: U32, +b: U32, +e: {a == b : U32}) -> {U32.is_eq(a, b) == True{} : Bool}:
  %e : {U32.is_eq(a, _) == True{} : Bool}
  eq_refl(a)
