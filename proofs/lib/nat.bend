import Base
import ./logic.bend as L
import ../lemmas/proofs/nat_algebra.bend as NA
import ../spec/common.bend as SC
import ../lemmas/spec/numeric.bend as S

# Natural-number order and arithmetic facts on Base Nat (Bool-valued
# comparisons), proved by induction on the installed definitions.

def pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

def succ_inj(+a: Nat, +b: Nat, e: {1n+a == 1n+b : Nat}) -> {a == b : Nat}:
  Equal.cong(Nat, Nat, pred, 1n+a, 1n+b, e)

def succ_cong(+a: Nat, +b: Nat, e: {a == b : Nat}) -> {1n+a == 1n+b : Nat}:
  Equal.cong(Nat, Nat, x => 1n+x, a, b, e)

def is_zero(n: Nat) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      False{}

def zero_succ(+n: Nat, e: {0n == 1n+n : Nat}) -> Empty:
  %e : L.truth(is_zero(_))
  Unit{}

def succ_zero(+n: Nat, e: {1n+n == 0n : Nat}) -> Empty:
  zero_succ(n, Equal.sym(Nat, 1n+n, 0n, e))

def add_zero(+n: Nat) -> {Nat.add(n, 0n) == n : Nat}:
  NA.add_zero(n)

def add_succ(+a: Nat, +b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  NA.add_succ(a, b)

def add_comm(+a: Nat, +b: Nat) -> {Nat.add(a, b) == Nat.add(b, a) : Nat}:
  NA.add_comm(a, b)

def add_assoc(+a: Nat, +b: Nat, +c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}:
  NA.add_assoc(a, b, c)

# ---- order ----

def lt_irrefl(+n: Nat) -> {Nat.is_lt(n, n) == False{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      lt_irrefl(p)

def le_refl(+n: Nat) -> {Nat.is_le(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      le_refl(p)

def lt_succ(+n: Nat) -> {Nat.is_lt(n, 1n+n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      lt_succ(p)

def le_succ(+n: Nat) -> {Nat.is_le(n, 1n+n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      le_succ(p)

def zero_le(+n: Nat) -> {Nat.is_le(0n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def not_lt_zero(+n: Nat) -> {Nat.is_lt(n, 0n) == False{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def lt_zero_absurd(+n: Nat, e: {Nat.is_lt(n, 0n) == True{} : Bool}) -> Empty:
  L.false_true(Equal.trans(Bool, False{}, Nat.is_lt(n, 0n), True{}, Equal.sym(Bool, Nat.is_lt(n, 0n), False{}, not_lt_zero(n)), e))

def lt_le(+a: Nat, +b: Nat, e: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(a, b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.is_le(1n+p, 0n) == True{} : Bool}, L.false_true(e))
    case 1n+p 1n+q:
      lt_le(p, q, e)

def le_lt_succ(+a: Nat, +b: Nat, e: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_lt(a, 1n+b) == True{} : Bool}:
  match a b:
    case 0n _:
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.is_lt(1n+p, 1n) == True{} : Bool}, L.false_true(e))
    case 1n+p 1n+q:
      le_lt_succ(p, q, e)

def lt_succ_le(+a: Nat, +b: Nat, e: {Nat.is_lt(a, 1n+b) == True{} : Bool}) -> {Nat.is_le(a, b) == True{} : Bool}:
  match a b:
    case 0n _:
      zero_le(b)
    case 1n+p 0n:
      Empty.absurd({Nat.is_le(1n+p, 0n) == True{} : Bool}, lt_zero_absurd(p, e))
    case 1n+p 1n+q:
      lt_succ_le(p, q, e)

def succ_le_lt(+a: Nat, +b: Nat, e: {Nat.is_le(1n+a, b) == True{} : Bool}) -> {Nat.is_lt(a, b) == True{} : Bool}:
  match a b:
    case _ 0n:
      Empty.absurd({Nat.is_lt(a, 0n) == True{} : Bool}, L.false_true(e))
    case 0n 1n+q:
      {==}
    case 1n+p 1n+q:
      succ_le_lt(p, q, e)

def lt_succ_le_succ(+a: Nat, +b: Nat, e: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(1n+a, b) == True{} : Bool}:
  match a b:
    case _ 0n:
      Empty.absurd({Nat.is_le(1n+a, 0n) == True{} : Bool}, lt_zero_absurd(a, e))
    case 0n 1n+q:
      zero_le(q)
    case 1n+p 1n+q:
      lt_succ_le_succ(p, q, e)

def le_trans(+a: Nat, +b: Nat, +c: Nat, ab: {Nat.is_le(a, b) == True{} : Bool}, bc: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(a, c) == True{} : Bool}:
  match a b c:
    case 0n _ _:
      zero_le(c)
    case 1n+p 0n _:
      Empty.absurd({Nat.is_le(1n+p, c) == True{} : Bool}, L.false_true(ab))
    case 1n+p 1n+q 0n:
      Empty.absurd({Nat.is_le(1n+p, 0n) == True{} : Bool}, L.false_true(bc))
    case 1n+p 1n+q 1n+r:
      le_trans(p, q, r, ab, bc)

def lt_le_trans(+a: Nat, +b: Nat, +c: Nat, ab: {Nat.is_lt(a, b) == True{} : Bool}, bc: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_lt(a, c) == True{} : Bool}:
  succ_le_lt(a, c, le_trans(1n+a, b, c, lt_succ_le_succ(a, b, ab), bc))

def le_lt_trans(+a: Nat, +b: Nat, +c: Nat, ab: {Nat.is_le(a, b) == True{} : Bool}, bc: {Nat.is_lt(b, c) == True{} : Bool}) -> {Nat.is_lt(a, c) == True{} : Bool}:
  succ_le_lt(a, c, le_trans(1n+a, 1n+b, c, ab, lt_succ_le_succ(b, c, bc)))

def lt_trans(+a: Nat, +b: Nat, +c: Nat, ab: {Nat.is_lt(a, b) == True{} : Bool}, bc: {Nat.is_lt(b, c) == True{} : Bool}) -> {Nat.is_lt(a, c) == True{} : Bool}:
  lt_le_trans(a, b, c, ab, lt_le(b, c, bc))

# is_lt(a, b) == False gives b <= a.
def not_lt_le(+a: Nat, +b: Nat, e: {Nat.is_lt(a, b) == False{} : Bool}) -> {Nat.is_le(b, a) == True{} : Bool}:
  match a b:
    case _ 0n:
      zero_le(a)
    case 0n 1n+q:
      Empty.absurd({Nat.is_le(1n+q, 0n) == True{} : Bool}, L.true_false(e))
    case 1n+p 1n+q:
      not_lt_le(p, q, e)

def le_not_lt(+a: Nat, +b: Nat, e: {Nat.is_le(b, a) == True{} : Bool}) -> {Nat.is_lt(a, b) == False{} : Bool}:
  match a b:
    case _ 0n:
      not_lt_zero(a)
    case 0n 1n+q:
      Empty.absurd({Nat.is_lt(0n, 1n+q) == False{} : Bool}, L.false_true(e))
    case 1n+p 1n+q:
      le_not_lt(p, q, e)

def lt_not_le(+a: Nat, +b: Nat, e: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(b, a) == False{} : Bool}:
  match a b:
    case _ 0n:
      Empty.absurd({Nat.is_le(0n, a) == False{} : Bool}, lt_zero_absurd(a, e))
    case 0n 1n+q:
      {==}
    case 1n+p 1n+q:
      lt_not_le(p, q, e)

def not_le_lt(+a: Nat, +b: Nat, e: {Nat.is_le(a, b) == False{} : Bool}) -> {Nat.is_lt(b, a) == True{} : Bool}:
  match a b:
    case 0n 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, L.true_false(e))
    case 0n 1n+q:
      Empty.absurd({Nat.is_lt(1n+q, 0n) == True{} : Bool}, L.true_false(e))
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      not_le_lt(p, q, e)

def lt_asym(+a: Nat, +b: Nat, ab: {Nat.is_lt(a, b) == True{} : Bool}, ba: {Nat.is_lt(b, a) == True{} : Bool}) -> Empty:
  L.true_not_false(Nat.is_lt(a, a), lt_trans(a, b, a, ab, ba), lt_irrefl(a))

def le_antisym(+a: Nat, +b: Nat, ab: {Nat.is_le(a, b) == True{} : Bool}, ba: {Nat.is_le(b, a) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({0n == 1n+q : Nat}, L.false_true(ba))
    case 1n+p 0n:
      Empty.absurd({1n+p == 0n : Nat}, L.false_true(ab))
    case 1n+p 1n+q:
      succ_cong(p, q, le_antisym(p, q, ab, ba))

def eq_le(+a: Nat, +b: Nat, e: {a == b : Nat}) -> {Nat.is_le(a, b) == True{} : Bool}:
  %e : {Nat.is_le(a, _) == True{} : Bool}
  le_refl(a)

def lt_ne(+a: Nat, +b: Nat, lt: {Nat.is_lt(a, b) == True{} : Bool}, e: {a == b : Nat}) -> Empty:
  L.true_not_false(Nat.is_lt(a, a), Equal.trans(Bool, Nat.is_lt(a, a), Nat.is_lt(a, b), True{}, Equal.cong(Nat, Bool, x => Nat.is_lt(a, x), a, b, e), lt), lt_irrefl(a))

def eq_from_is_eq(+a: Nat, +b: Nat, e: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({0n == 1n+q : Nat}, L.false_true(e))
    case 1n+p 0n:
      Empty.absurd({1n+p == 0n : Nat}, L.false_true(e))
    case 1n+p 1n+q:
      succ_cong(p, q, eq_from_is_eq(p, q, e))

def is_eq_refl(+a: Nat) -> {Nat.is_eq(a, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      is_eq_refl(p)

def is_eq_lt(+a: Nat, +b: Nat, e: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_eq(a, b) == False{} : Bool}:
  match a b:
    case _ 0n:
      Empty.absurd({Nat.is_eq(a, 0n) == False{} : Bool}, lt_zero_absurd(a, e))
    case 0n 1n+q:
      {==}
    case 1n+p 1n+q:
      is_eq_lt(p, q, e)

def lt_or_eq(+a: Nat, +b: Nat, e: {Nat.is_le(a, b) == True{} : Bool}, ne: {Nat.is_eq(a, b) == False{} : Bool}) -> {Nat.is_lt(a, b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, L.true_false(ne))
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.is_lt(1n+p, 0n) == True{} : Bool}, L.false_true(e))
    case 1n+p 1n+q:
      lt_or_eq(p, q, e, ne)

# ---- addition and subtraction ----

def add_sub_cancel(+a: Nat, +b: Nat) -> {Nat.sub(Nat.add(a, b), a) == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p _:
      add_sub_cancel(p, b)

def sub_add(+a: Nat, +b: Nat, e: {Nat.is_le(b, a) == True{} : Bool}) -> {Nat.add(b, Nat.sub(a, b)) == a : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 1n+p 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({Nat.add(1n+q, Nat.sub(0n, 1n+q)) == 0n : Nat}, L.false_true(e))
    case 1n+p 1n+q:
      succ_cong(Nat.add(q, Nat.sub(p, q)), p, sub_add(p, q, e))

def sub_zero(+n: Nat) -> {Nat.sub(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def sub_self(+n: Nat) -> {Nat.sub(n, n) == 0n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      sub_self(p)

def sub_succ_left(+a: Nat, +b: Nat, e: {Nat.is_le(b, a) == True{} : Bool}) -> {Nat.sub(1n+a, b) == 1n+Nat.sub(a, b) : Nat}:
  match a b:
    case _ 0n:
      %Equal.sym(Nat, Nat.sub(a, 0n), a, sub_zero(a)) : {1n+a == 1n+_ : Nat}
      {==}
    case 0n 1n+q:
      Empty.absurd({Nat.sub(1n, 1n+q) == 1n+Nat.sub(0n, 1n+q) : Nat}, L.false_true(e))
    case 1n+p 1n+q:
      sub_succ_left(p, q, e)

def sub_lt(+a: Nat, +b: Nat, +c: Nat, le: {Nat.is_le(b, a) == True{} : Bool}, lt: {Nat.is_lt(a, Nat.add(b, c)) == True{} : Bool}) -> {Nat.is_lt(Nat.sub(a, b), c) == True{} : Bool}:
  match a b:
    case _ 0n:
      %Equal.sym(Nat, Nat.sub(a, 0n), a, sub_zero(a)) : {Nat.is_lt(_, c) == True{} : Bool}
      lt
    case 0n 1n+q:
      Empty.absurd({Nat.is_lt(Nat.sub(0n, 1n+q), c) == True{} : Bool}, L.false_true(le))
    case 1n+p 1n+q:
      sub_lt(p, q, c, le, lt)

def le_add_right(+a: Nat, +b: Nat) -> {Nat.is_le(a, Nat.add(a, b)) == True{} : Bool}:
  match a:
    case 0n:
      zero_le(b)
    case 1n+p:
      le_add_right(p, b)

def lt_add_left(+a: Nat, +b: Nat, +c: Nat, e: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_lt(Nat.add(c, a), Nat.add(c, b)) == True{} : Bool}:
  match c:
    case 0n:
      e
    case 1n+r:
      lt_add_left(a, b, r, e)

def le_add_left(+a: Nat, +b: Nat, +c: Nat, e: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(Nat.add(c, a), Nat.add(c, b)) == True{} : Bool}:
  match c:
    case 0n:
      e
    case 1n+r:
      le_add_left(a, b, r, e)

# ---- doubling and powers of two (spec/common.bend pow2) ----

def double_inj(+a: Nat, +b: Nat, e: {Nat.double(a) == Nat.double(b) : Nat}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({0n == 1n+q : Nat}, zero_succ(1n+Nat.double(q), e))
    case 1n+p 0n:
      Empty.absurd({1n+p == 0n : Nat}, succ_zero(1n+Nat.double(p), e))
    case 1n+p 1n+q:
      succ_cong(p, q, double_inj(p, q, succ_inj(Nat.double(p), Nat.double(q), succ_inj(1n+Nat.double(p), 1n+Nat.double(q), e))))

def even_odd(+a: Nat, +b: Nat, e: {Nat.double(a) == 1n+Nat.double(b) : Nat}) -> Empty:
  match a b:
    case 0n _:
      zero_succ(Nat.double(b), e)
    case 1n+p 0n:
      succ_zero(Nat.double(p), succ_inj(1n+Nat.double(p), 0n, e))
    case 1n+p 1n+q:
      even_odd(p, q, succ_inj(Nat.double(p), 1n+Nat.double(q), succ_inj(1n+Nat.double(p), 2n+Nat.double(q), e)))

# bit + 2u == bit' + 2v determines both parts.
def bit_split_bit(+b: Bool, +c: Bool, +u: Nat, +v: Nat, e: {Nat.add(S.bit_value(b), Nat.double(u)) == Nat.add(S.bit_value(c), Nat.double(v)) : Nat}) -> {b == c : Bool}:
  match b c:
    case False{} False{}:
      {==}
    case True{} True{}:
      {==}
    case False{} True{}:
      Empty.absurd({False{} == True{} : Bool}, even_odd(u, v, e))
    case True{} False{}:
      Empty.absurd({True{} == False{} : Bool}, even_odd(v, u, Equal.sym(Nat, 1n+Nat.double(u), Nat.double(v), e)))

def bit_split_val(+b: Bool, +c: Bool, +u: Nat, +v: Nat, e: {Nat.add(S.bit_value(b), Nat.double(u)) == Nat.add(S.bit_value(c), Nat.double(v)) : Nat}) -> {u == v : Nat}:
  match b c:
    case False{} False{}:
      double_inj(u, v, e)
    case True{} True{}:
      double_inj(u, v, succ_inj(Nat.double(u), Nat.double(v), e))
    case False{} True{}:
      Empty.absurd({u == v : Nat}, even_odd(u, v, e))
    case True{} False{}:
      Empty.absurd({u == v : Nat}, even_odd(v, u, Equal.sym(Nat, 1n+Nat.double(u), Nat.double(v), e)))

def double_lt(+a: Nat, +b: Nat, e: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_lt(Nat.double(a), Nat.double(b)) == True{} : Bool}:
  match a b:
    case _ 0n:
      Empty.absurd({Nat.is_lt(Nat.double(a), 0n) == True{} : Bool}, lt_zero_absurd(a, e))
    case 0n 1n+q:
      {==}
    case 1n+p 1n+q:
      double_lt(p, q, e)

def double_le(+a: Nat, +b: Nat, e: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(Nat.double(a), Nat.double(b)) == True{} : Bool}:
  match a b:
    case 0n _:
      zero_le(Nat.double(b))
    case 1n+p 0n:
      Empty.absurd({Nat.is_le(Nat.double(1n+p), 0n) == True{} : Bool}, L.false_true(e))
    case 1n+p 1n+q:
      double_le(p, q, e)

# bit + 2u < 2v gives u < v.
def bit_double_lt(+b: Bool, +u: Nat, +v: Nat, e: {Nat.is_lt(Nat.add(S.bit_value(b), Nat.double(u)), Nat.double(v)) == True{} : Bool}) -> {Nat.is_lt(u, v) == True{} : Bool}:
  match b u v:
    case _ _ 0n:
      Empty.absurd({Nat.is_lt(u, 0n) == True{} : Bool}, lt_zero_absurd(Nat.add(S.bit_value(b), Nat.double(u)), e))
    case _ 0n 1n+q:
      {==}
    case False{} 1n+p 1n+q:
      bit_double_lt(False{}, p, q, e)
    case True{} 1n+p 1n+q:
      bit_double_lt(True{}, p, q, e)

def double_lt_bit(+b: Bool, +u: Nat, +v: Nat, e: {Nat.is_lt(u, v) == True{} : Bool}) -> {Nat.is_lt(Nat.add(S.bit_value(b), Nat.double(u)), Nat.double(v)) == True{} : Bool}:
  match b u v:
    case _ _ 0n:
      Empty.absurd({Nat.is_lt(Nat.add(S.bit_value(b), Nat.double(u)), 0n) == True{} : Bool}, lt_zero_absurd(u, e))
    case False{} 0n 1n+q:
      {==}
    case True{} 0n 1n+q:
      {==}
    case False{} 1n+p 1n+q:
      double_lt_bit(False{}, p, q, e)
    case True{} 1n+p 1n+q:
      double_lt_bit(True{}, p, q, e)

def double_self_le(+n: Nat) -> {Nat.is_le(n, Nat.double(n)) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      le_trans(p, Nat.double(p), 1n+Nat.double(p), double_self_le(p), le_succ(Nat.double(p)))

def double_succ_le(+n: Nat, e: {Nat.is_le(1n, n) == True{} : Bool}) -> {Nat.is_le(1n+n, Nat.double(n)) == True{} : Bool}:
  match n:
    case 0n:
      Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, L.false_true(e))
    case 1n+p:
      double_self_le(p)

def pow2_pos(+k: Nat) -> {Nat.is_le(1n, SC.pow2(k)) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      le_trans(1n, SC.pow2(p), Nat.double(SC.pow2(p)), pow2_pos(p), double_self_le(SC.pow2(p)))

def pow2_lt_succ(+k: Nat) -> {Nat.is_lt(SC.pow2(k), SC.pow2(1n+k)) == True{} : Bool}:
  succ_le_lt(SC.pow2(k), Nat.double(SC.pow2(k)), double_succ_le(SC.pow2(k), pow2_pos(k)))

# 1 <= n gives 1 + n <= 2n.
def pow2_mono(+a: Nat, +b: Nat, e: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(SC.pow2(a), SC.pow2(b)) == True{} : Bool}:
  match a b:
    case 0n _:
      pow2_pos(b)
    case 1n+p 0n:
      Empty.absurd({Nat.is_le(SC.pow2(1n+p), 1n) == True{} : Bool}, L.false_true(e))
    case 1n+p 1n+q:
      double_le(SC.pow2(p), SC.pow2(q), pow2_mono(p, q, e))

def pow2_strict(+a: Nat, +b: Nat, e: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_lt(SC.pow2(a), SC.pow2(b)) == True{} : Bool}:
  match b:
    case 0n:
      Empty.absurd({Nat.is_lt(SC.pow2(a), 1n) == True{} : Bool}, lt_zero_absurd(a, e))
    case 1n+q:
      lt_le_trans(SC.pow2(a), SC.pow2(1n+a), SC.pow2(1n+q), pow2_lt_succ(a), pow2_mono(1n+a, 1n+q, lt_succ_le_succ(a, 1n+q, e)))

# pred(2v) == 1 + 2 pred(v) for v >= 1.
def pred_double(+v: Nat, e: {Nat.is_le(1n, v) == True{} : Bool}) -> {Nat.sub(Nat.double(v), 1n) == 1n+Nat.double(Nat.sub(v, 1n)) : Nat}:
  match v:
    case 0n:
      Empty.absurd({Nat.sub(0n, 1n) == 1n+Nat.double(Nat.sub(0n, 1n)) : Nat}, L.false_true(e))
    case 1n+p:
      %Equal.sym(Nat, Nat.sub(p, 0n), p, sub_zero(p)) : {1n+Nat.double(p) == 1n+Nat.double(_) : Nat}
      {==}

def add_double(+a: Nat, +b: Nat) -> {Nat.add(Nat.double(a), Nat.double(b)) == Nat.double(Nat.add(a, b)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      succ_cong(1n+Nat.add(Nat.double(p), Nat.double(b)), 1n+Nat.double(Nat.add(p, b)), succ_cong(Nat.add(Nat.double(p), Nat.double(b)), Nat.double(Nat.add(p, b)), add_double(p, b)))

# ---- halving ----
#
# `Nat.div(n, 2n)` is what the flat-array walks use to step from a block's
# half size to the next one (the C references use `h >> 1`). Both facts below
# come from Base's own `Nat.divmod.go`, which recurses structurally on the
# dividend, so two unfoldings of `Nat.add(2n, i)` are a definitional step.

def bump2(p: Nat & Nat) -> Nat & Nat:
  (q, r) = p
  (1n+q, r)

def acc2(i: Nat, m: Nat, +d: Nat, +r: Nat) -> {Nat.divmod.go(i, m, 1n+d, r) == bump2(Nat.divmod.go(i, m, d, r)) : Nat & Nat}:
  match i m:
    case 0n _:
      {==}
    case 1n+np 0n:
      acc2(np, r, 1n+d, 0n)
    case 1n+np 1n+mp:
      acc2(np, mp, d, 1n+r)

def peel2(+i: Nat, +d: Nat) -> {Nat.divmod.go(Nat.add(2n, i), 1n, d, 0n) == Nat.divmod.go(i, 1n, 1n+d, 0n) : Nat & Nat}:
  {==}

def fst_bump2(p: Nat & Nat) -> {Nat.div.fin(bump2(p)) == 1n+Nat.div.fin(p) : Nat}:
  (q, r) = p
  {==}

def div2_step(+i: Nat) -> {Nat.div(Nat.add(2n, i), 2n) == 1n+Nat.div(i, 2n) : Nat}:
  Equal.trans(Nat, Nat.div.fin(Nat.divmod.go(Nat.add(2n, i), 1n, 0n, 0n)), Nat.div.fin(bump2(Nat.divmod.go(i, 1n, 0n, 0n))), 1n+Nat.div.fin(Nat.divmod.go(i, 1n, 0n, 0n)),
    Equal.cong(Nat & Nat, Nat, Nat.div.fin, Nat.divmod.go(Nat.add(2n, i), 1n, 0n, 0n), bump2(Nat.divmod.go(i, 1n, 0n, 0n)),
      Equal.trans(Nat & Nat, Nat.divmod.go(Nat.add(2n, i), 1n, 0n, 0n), Nat.divmod.go(i, 1n, 1n, 0n), bump2(Nat.divmod.go(i, 1n, 0n, 0n)),
        peel2(i, 0n), acc2(i, 1n, 0n, 0n))),
    fst_bump2(Nat.divmod.go(i, 1n, 0n, 0n)))

def double_succ(+y: Nat) -> {Nat.double(1n+y) == Nat.add(2n, Nat.double(y)) : Nat}:
  %Equal.sym(Nat, Nat.double(y), Nat.add(y, y), NA.double_self(y)) : {Nat.double(1n+y) == Nat.add(2n, _) : Nat}
  %Equal.sym(Nat, Nat.double(1n+y), Nat.add(1n+y, 1n+y), NA.double_self(1n+y)) : {_ == Nat.add(2n, Nat.add(y, y)) : Nat}
  succ_cong(Nat.add(y, 1n+y), 1n+Nat.add(y, y), add_succ(y, y))

def div2_double(x: Nat) -> {Nat.div(Nat.double(x), 2n) == x : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+ +y:
      %double_succ(y) : {Nat.div(_, 2n) == 1n+y : Nat}
      %Equal.sym(Nat, Nat.div(Nat.add(2n, Nat.double(y)), 2n), 1n+Nat.div(Nat.double(y), 2n), div2_step(Nat.double(y))) : {_ == 1n+y : Nat}
      succ_cong(Nat.div(Nat.double(y), 2n), y, div2_double(y))

# 2^(1+r) / 2 = 2^r
def div2_pow2(+r: Nat) -> {Nat.div(SC.pow2(1n+r), 2n) == SC.pow2(r) : Nat}:
  div2_double(SC.pow2(r))

def min_left(+a: Nat, +b: Nat, +h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.min(a, b) == a : Nat}:
  match a b:
    case 0n _:
      {==}
    case 1n+ap 0n:
      Empty.absurd({Nat.min(1n+ap, 0n) == 1n+ap : Nat}, lt_zero_absurd(1n+ap, h))
    case 1n+ap 1n+bp:
      succ_cong(Nat.min(ap, bp), ap, min_left(ap, bp, h))

def min_right(+a: Nat, +b: Nat, +h: {Nat.is_lt(a, b) == False{} : Bool}) -> {Nat.min(a, b) == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      Empty.absurd({Nat.min(0n, 1n+bp) == 1n+bp : Nat}, zero_succ(0n, Equal.sym(Nat, 1n, 0n, Equal.cong(Bool, Nat, c => S.bit_value(c), True{}, False{}, h))))
    case 1n+ap 0n:
      {==}
    case 1n+ap 1n+bp:
      succ_cong(Nat.min(ap, bp), bp, min_right(ap, bp, h))

def is_eq_sym_false(+a: Nat, +b: Nat, +h: {Nat.is_eq(a, b) == False{} : Bool}) -> {Nat.is_eq(b, a) == False{} : Bool}:
  match a b:
    case 0n 0n:
      h
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      is_eq_sym_false(p, q, h)

# a < b  ==>  a + c < b + c
def lt_add_r2(+a: Nat, +b: Nat, +c: Nat, +h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_lt(Nat.add(a, c), Nat.add(b, c)) == True{} : Bool}:
  match a b:
    case 0n 0n:
      Empty.absurd({Nat.is_lt(Nat.add(0n, c), Nat.add(0n, c)) == True{} : Bool}, lt_zero_absurd(0n, h))
    case 0n 1n+q:
      le_lt_succ(c, Nat.add(q, c), le_trans(c, Nat.add(c, q), Nat.add(q, c), le_add_right(c, q), eq_le(Nat.add(c, q), Nat.add(q, c), add_comm(c, q))))
    case 1n+p 0n:
      Empty.absurd({Nat.is_lt(Nat.add(1n+p, c), Nat.add(0n, c)) == True{} : Bool}, lt_zero_absurd(1n+p, h))
    case 1n+p 1n+q:
      lt_add_r2(p, q, c, h)
