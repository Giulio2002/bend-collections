import Base
import ./logic.bend as L
import ./nat.bend as N
import ./u32.bend as U
import ../spec/common.bend as SC
import ../lemmas/spec/numeric.bend as S

# U32 halving as a Nat operation, and the midpoint bounds.
#
# proofs/lib/u32.bend deliberately avoids `U32.add` (its comment explains
# why: `inc`/`shl`/`shr`/`sub` have Nat meanings that can be stated with a
# bound `i < 2^k` for a variable k). The graph's binary search needs the
# midpoint `(lo + hi) / 2`, so the two missing bridges are proved here from
# the retained word lemmas: full-width ripple addition conserves the value
# `shr` is exact halving, so the midpoint can be written with sub and shr
# alone.

# ---- halving ----

# The Nat halving the checker can compute structurally (no Nat.div).
def hlf(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      match p:
        case 0n:
          0n
        case 1n+q:
          1n+hlf(q)

def hlf_double(+q: Nat) -> {hlf(Nat.double(q)) == q : Nat}:
  match q:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, n => 1n+n, hlf(Nat.double(p)), p, hlf_double(p))

def hlf_double_succ(+q: Nat) -> {hlf(1n+Nat.double(q)) == q : Nat}:
  match q:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, n => 1n+n, hlf(1n+Nat.double(p)), p, hlf_double_succ(p))

def hlf_bit(+b: Bool, +q: Nat) -> {hlf(Nat.add(S.bit_value(b), Nat.double(q))) == q : Nat}:
  match b:
    case False{}:
      hlf_double(q)
    case True{}:
      hlf_double_succ(q)

def shr_value(+x: U32) -> {U32.to_nat(U32.shr(x)) == hlf(U32.to_nat(x)) : Nat}:
  %Equal.sym(Nat, U32.to_nat(x), Nat.add(S.bit_value(U.low_bit(x)), Nat.double(U32.to_nat(U32.shr(x)))), U.shr_split(x)) : {U32.to_nat(U32.shr(x)) == hlf(_) : Nat}
  Equal.sym(Nat, hlf(Nat.add(S.bit_value(U.low_bit(x)), Nat.double(U32.to_nat(U32.shr(x))))), U32.to_nat(U32.shr(x)),
    hlf_bit(U.low_bit(x), U32.to_nat(U32.shr(x))))

# ---- halving respects the order ----

def hlf_le(+n: Nat) -> {Nat.is_le(hlf(n), n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match p:
        case 0n:
          {==}
        case 1n+q:
          N.le_trans(hlf(q), q, 1n+q, hlf_le(q), N.le_succ(q))

def hlf_succ_le(+q: Nat) -> {Nat.is_le(hlf(1n+q), q) == True{} : Bool}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      hlf_le(r)

# The midpoint of a nonempty range lies inside it: a <= hlf(a+b) < b
# whenever a < b.
def hlf_lower(+a: Nat, +b: Nat, +h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(a, hlf(Nat.add(a, b))) == True{} : Bool}:
  match a b:
    case 0n b0:
      N.zero_le(hlf(Nat.add(0n, b0)))
    case 1n+p 0n:
      Empty.absurd({Nat.is_le(1n+p, hlf(Nat.add(1n+p, 0n))) == True{} : Bool}, L.false_true(h))
    case 1n+ +p 1n+ +q:
      %Equal.sym(Nat, Nat.add(p, 1n+q), 1n+Nat.add(p, q), N.add_succ(p, q)) : {Nat.is_le(1n+p, hlf(1n+_)) == True{} : Bool}
      hlf_lower(p, q, h)

def hlf_upper(+a: Nat, +b: Nat, +h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_lt(hlf(Nat.add(a, b)), b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      Empty.absurd({Nat.is_lt(hlf(Nat.add(0n, 0n)), 0n) == True{} : Bool}, L.false_true(h))
    case 0n 1n+ +q:
      N.le_lt_trans(hlf(1n+q), q, 1n+q, hlf_succ_le(q), N.lt_succ(q))
    case 1n+p 0n:
      Empty.absurd({Nat.is_lt(hlf(Nat.add(1n+p, 0n)), 0n) == True{} : Bool}, L.false_true(h))
    case 1n+ +p 1n+ +q:
      %Equal.sym(Nat, Nat.add(p, 1n+q), 1n+Nat.add(p, q), N.add_succ(p, q)) : {Nat.is_lt(hlf(1n+_), 1n+q) == True{} : Bool}
      hlf_upper(p, q, h)

# ---- from_nat / sub bridges used with the halving one ----

# The graph implementation avoids `U32.add` entirely (its Nat meaning would
# need a 2^32 bound, and the checker cannot expand 2^32 as a unary Nat), so
# only halving and subtraction bridges are needed. Subtraction is
# proofs/lib/u32.bend `sub_nat`; halving is `shr_value` above.

def hlf_bound(+i: Nat, +k: Nat, +h: {Nat.is_lt(i, SC.pow2(k)) == True{} : Bool}) -> {Nat.is_lt(hlf(i), SC.pow2(k)) == True{} : Bool}:
  N.le_lt_trans(hlf(i), i, SC.pow2(k), hlf_le(i), h)

def shr_bridge(+i: Nat, +k: Nat, +hk: {Nat.is_le(k, 32n) == True{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(k)) == True{} : Bool}) -> {U32.shr(U32.from_nat(i)) == U32.from_nat(hlf(i)) : U32}:
  +ri = U.to_nat_from_nat(i, k, hk, hi)
  U.injective(U32.shr(U32.from_nat(i)), U32.from_nat(hlf(i)),
    Equal.trans(Nat, U32.to_nat(U32.shr(U32.from_nat(i))), hlf(i), U32.to_nat(U32.from_nat(hlf(i))),
      Equal.trans(Nat, U32.to_nat(U32.shr(U32.from_nat(i))), hlf(U32.to_nat(U32.from_nat(i))), hlf(i),
        shr_value(U32.from_nat(i)),
        Equal.cong(Nat, Nat, hlf, U32.to_nat(U32.from_nat(i)), i, ri)),
      Equal.sym(Nat, U32.to_nat(U32.from_nat(hlf(i))), hlf(i),
        U.to_nat_from_nat(hlf(i), k, hk, hlf_bound(i, k, hi)))))

# ---- the halving measure used by the binary search ----

# s < 2m gives s/2 < m: one narrowing step of a search range that started
# below 2^f lands below 2^(f-1).
def hlf_lt(+s: Nat, +m: Nat, +h: {Nat.is_lt(s, Nat.double(m)) == True{} : Bool}) -> {Nat.is_lt(hlf(s), m) == True{} : Bool}:
  match s m:
    case s0 0n:
      Empty.absurd({Nat.is_lt(hlf(s0), 0n) == True{} : Bool}, N.lt_zero_absurd(s0, h))
    case 0n 1n+q:
      {==}
    case 1n+0n 1n+q:
      {==}
    case 1n+1n+r 1n+q:
      hlf_lt(r, q, h)

# The size after one step is at most s/2, so it stays below the halved bound.
def step_bound(+s2: Nat, +s: Nat, +m: Nat, +hle: {Nat.is_le(s2, hlf(s)) == True{} : Bool}, +h: {Nat.is_lt(s, Nat.double(m)) == True{} : Bool}) -> {Nat.is_lt(s2, m) == True{} : Bool}:
  N.le_lt_trans(s2, hlf(s), m, hle, hlf_lt(s, m, h))

# ---- subtraction bridge ----

# U32.sub is exact whenever the subtrahend is not larger (no borrow), so it
# is the Nat subtraction of the two indices.
def sub_le(+a: Nat, +b: Nat) -> {Nat.is_le(Nat.sub(a, b), a) == True{} : Bool}:
  match a b:
    case a0 0n:
      L.subst(Nat, z => {Nat.is_le(z, a0) == True{} : Bool}, a0, Nat.sub(a0, 0n), Equal.sym(Nat, Nat.sub(a0, 0n), a0, N.sub_zero(a0)), N.le_refl(a0))
    case 0n 1n+q:
      N.zero_le(Nat.sub(0n, 1n+q))
    case 1n+p 1n+q:
      N.le_trans(Nat.sub(p, q), p, 1n+p, sub_le(p, q), N.le_succ(p))

def sub_bridge(+a: Nat, +b: Nat, +k: Nat, +hk: {Nat.is_le(k, 32n) == True{} : Bool}, +ha: {Nat.is_lt(a, SC.pow2(k)) == True{} : Bool}, +hb: {Nat.is_le(b, a) == True{} : Bool}) -> {U32.sub(U32.from_nat(a), U32.from_nat(b)) == U32.from_nat(Nat.sub(a, b)) : U32}:
  +hb2 = N.le_lt_trans(b, a, SC.pow2(k), hb, ha)
  +ra = U.to_nat_from_nat(a, k, hk, ha)
  +rb = U.to_nat_from_nat(b, k, hk, hb2)
  +le = L.subst(Nat, z => {Nat.is_le(z, U32.to_nat(U32.from_nat(a))) == True{} : Bool}, b, U32.to_nat(U32.from_nat(b)), Equal.sym(Nat, U32.to_nat(U32.from_nat(b)), b, rb),
          L.subst(Nat, z => {Nat.is_le(b, z) == True{} : Bool}, a, U32.to_nat(U32.from_nat(a)), Equal.sym(Nat, U32.to_nat(U32.from_nat(a)), a, ra), hb))
  U.injective(U32.sub(U32.from_nat(a), U32.from_nat(b)), U32.from_nat(Nat.sub(a, b)),
    Equal.trans(Nat, U32.to_nat(U32.sub(U32.from_nat(a), U32.from_nat(b))), Nat.sub(a, b), U32.to_nat(U32.from_nat(Nat.sub(a, b))),
      Equal.trans(Nat, U32.to_nat(U32.sub(U32.from_nat(a), U32.from_nat(b))), Nat.sub(U32.to_nat(U32.from_nat(a)), U32.to_nat(U32.from_nat(b))), Nat.sub(a, b),
        U.sub_nat(U32.from_nat(a), U32.from_nat(b), le),
        Equal.trans(Nat, Nat.sub(U32.to_nat(U32.from_nat(a)), U32.to_nat(U32.from_nat(b))), Nat.sub(a, U32.to_nat(U32.from_nat(b))), Nat.sub(a, b),
          Equal.cong(Nat, Nat, z => Nat.sub(z, U32.to_nat(U32.from_nat(b))), U32.to_nat(U32.from_nat(a)), a, ra),
          Equal.cong(Nat, Nat, z => Nat.sub(a, z), U32.to_nat(U32.from_nat(b)), b, rb))),
      Equal.sym(Nat, U32.to_nat(U32.from_nat(Nat.sub(a, b))), Nat.sub(a, b),
        U.to_nat_from_nat(Nat.sub(a, b), k, hk, N.le_lt_trans(Nat.sub(a, b), a, SC.pow2(k), sub_le(a, b), ha)))))
