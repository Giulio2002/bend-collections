import Base
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../../../src/containers/bitset.bend as B

# The two facts about the word index `B.wordix(i) = i / 32` and the bit
# position `B.bitix(i) = i % 32` that the packed representation needs:
#
#   i <  32  ->  wordix(i) = 0      and  bitix(i) = i
#   wordix(32 + i) = 1 + wordix(i)  and  bitix(32 + i) = bitix(i)
#
# Both are proved from Base's own `Nat.divmod.go`, which is a structural
# recursion on the dividend, so 32 unfoldings of `Nat.add(32n, i)` are a
# definitional step (`peel_go` below is literally `{==}`); only the quotient
# accumulator has to be pushed out by an induction.

def bump(p: Nat & Nat) -> Nat & Nat:
  (q, r) = p
  (1n+q, r)

# The quotient accumulator of Nat.divmod.go is exactly an accumulator.
def acc(i: Nat, m: Nat, +d: Nat, +r: Nat) -> {Nat.divmod.go(i, m, 1n+d, r) == bump(Nat.divmod.go(i, m, d, r)) : Nat & Nat}:
  match i m:
    case 0n _:
      {==}
    case 1n+np 0n:
      acc(np, r, 1n+d, 0n)
    case 1n+np 1n+mp:
      acc(np, mp, d, 1n+r)

# 32 unfoldings: the dividend loses 32, the quotient gains one.
def peel_go(+i: Nat, +d: Nat) -> {Nat.divmod.go(Nat.add(32n, i), 31n, d, 0n) == Nat.divmod.go(i, 31n, 1n+d, 0n) : Nat & Nat}:
  {==}

def peel(+i: Nat) -> {Nat.divmod(Nat.add(32n, i), 32n) == bump(Nat.divmod(i, 32n)) : Nat & Nat}:
  Equal.trans(Nat & Nat, Nat.divmod.go(Nat.add(32n, i), 31n, 0n, 0n), Nat.divmod.go(i, 31n, 1n, 0n), bump(Nat.divmod.go(i, 31n, 0n, 0n)),
    peel_go(i, 0n), acc(i, 31n, 0n, 0n))

def fst_bump(p: Nat & Nat) -> {Nat.div.fin(bump(p)) == 1n+Nat.div.fin(p) : Nat}:
  (q, r) = p
  {==}

def snd_bump(p: Nat & Nat) -> {Nat.mod.fin(bump(p)) == Nat.mod.fin(p) : Nat}:
  (q, r) = p
  {==}

def wordix_peel(+i: Nat) -> {B.wordix(Nat.add(32n, i)) == 1n+B.wordix(i) : Nat}:
  Equal.trans(Nat, Nat.div.fin(Nat.divmod(Nat.add(32n, i), 32n)), Nat.div.fin(bump(Nat.divmod(i, 32n))), 1n+Nat.div.fin(Nat.divmod(i, 32n)),
    Equal.cong(Nat & Nat, Nat, Nat.div.fin, Nat.divmod(Nat.add(32n, i), 32n), bump(Nat.divmod(i, 32n)), peel(i)),
    fst_bump(Nat.divmod(i, 32n)))

def bitix_peel(+i: Nat) -> {B.bitix(Nat.add(32n, i)) == B.bitix(i) : Nat}:
  Equal.trans(Nat, Nat.mod.fin(Nat.divmod(Nat.add(32n, i), 32n)), Nat.mod.fin(bump(Nat.divmod(i, 32n))), Nat.mod.fin(Nat.divmod(i, 32n)),
    Equal.cong(Nat & Nat, Nat, Nat.mod.fin, Nat.divmod(Nat.add(32n, i), 32n), bump(Nat.divmod(i, 32n)), peel(i)),
    snd_bump(Nat.divmod(i, 32n)))

# A dividend that never reaches the divisor never advances the quotient.
def small_go(i: Nat, m: Nat, +r: Nat, +h: {Nat.is_le(i, m) == True{} : Bool}) -> {Nat.divmod.go(i, m, 0n, r) == (0n, Nat.add(r, i)) : Nat & Nat}:
  match i m:
    case 0n _:
      %Equal.sym(Nat, Nat.add(r, 0n), r, N.add_zero(r)) : {(0n, r) == (0n, _) : Nat & Nat}
      {==}
    case 1n+ +np 0n:
      Empty.absurd({Nat.divmod.go(1n+np, 0n, 0n, r) == (0n, Nat.add(r, 1n+np)) : Nat & Nat}, L.false_true(h))
    case 1n+ +np 1n+mp:
      %Equal.sym(Nat, Nat.add(r, 1n+np), 1n+Nat.add(r, np), N.add_succ(r, np)) : {Nat.divmod.go(np, mp, 0n, 1n+r) == (0n, _) : Nat & Nat}
      small_go(np, mp, 1n+r, h)

def small(+i: Nat, +h: {Nat.is_lt(i, 32n) == True{} : Bool}) -> {Nat.divmod(i, 32n) == (0n, i) : Nat & Nat}:
  small_go(i, 31n, 0n, N.lt_succ_le(i, 31n, h))

def wordix_small(+i: Nat, +h: {Nat.is_lt(i, 32n) == True{} : Bool}) -> {B.wordix(i) == 0n : Nat}:
  Equal.cong(Nat & Nat, Nat, Nat.div.fin, Nat.divmod(i, 32n), (0n, i), small(i, h))

def bitix_small(+i: Nat, +h: {Nat.is_lt(i, 32n) == True{} : Bool}) -> {B.bitix(i) == i : Nat}:
  Equal.cong(Nat & Nat, Nat, Nat.mod.fin, Nat.divmod(i, 32n), (0n, i), small(i, h))

# The form the word walk needs: for i >= 32, i = 32 + (i - 32).
def add_sub32(+i: Nat, +h: {Nat.is_lt(i, 32n) == False{} : Bool}) -> {Nat.add(32n, Nat.sub(i, 32n)) == i : Nat}:
  N.sub_add(i, 32n, N.not_lt_le(i, 32n, h))

def wordix_step(+i: Nat, +h: {Nat.is_lt(i, 32n) == False{} : Bool}) -> {B.wordix(i) == 1n+B.wordix(Nat.sub(i, 32n)) : Nat}:
  L.subst(Nat, x => {B.wordix(x) == 1n+B.wordix(Nat.sub(i, 32n)) : Nat},
    Nat.add(32n, Nat.sub(i, 32n)), i, add_sub32(i, h), wordix_peel(Nat.sub(i, 32n)))

def bitix_step(+i: Nat, +h: {Nat.is_lt(i, 32n) == False{} : Bool}) -> {B.bitix(i) == B.bitix(Nat.sub(i, 32n)) : Nat}:
  L.subst(Nat, x => {B.bitix(x) == B.bitix(Nat.sub(i, 32n)) : Nat},
    Nat.add(32n, Nat.sub(i, 32n)), i, add_sub32(i, h), bitix_peel(Nat.sub(i, 32n)))
