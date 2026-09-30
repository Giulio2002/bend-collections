import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/crypto/curve25519/field.bend as FS
import ../../../spec/crypto/curve25519/fe.bend as FV
import ../../../src/crypto/curve25519/limbs.bend as LS
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/word.bend as WD
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../../math/natural/arith.bend as NR
import ../curve25519/num.bend as M
import ./nl.bend as NL
import ./pw.bend as PW
import ./pass.bend as PS

# Appended limb lists (src/crypto/curve25519/limbs.bend app): bounds and
# lengths, for the scalar arithmetic of ed25519.

def tr(+a: Nat, +b: Nat, +c: Nat, +e1: {a == b : Nat}, +e2: {b == c : Nat}) -> {a == c : Nat}:
  Equal.trans(Nat, a, b, c, e1, e2)

def sy(+a: Nat, +b: Nat, +e: {a == b : Nat}) -> {b == a : Nat}:
  Equal.sym(Nat, a, b, e)

def lt_one_zero(+x: Nat, +h: {Nat.is_lt(x, 1n) == True{} : Bool}) -> {x == 0n : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+y:
      Empty.absurd({1n+y == 0n : Nat}, L.false_true(Equal.trans(Bool, False{}, Nat.is_lt(y, 0n), True{}, Equal.sym(Bool, Nat.is_lt(y, 0n), False{}, N.not_lt_zero(y)), h)))

def app_below(+a: List<&2, Nat>, +b: List<&2, Nat>, +k: Nat, +ha: {FV.below(a, k) == True{} : Bool}, +hb: {FV.below(b, k) == True{} : Bool}) -> {FV.below(LS.app(a, b), k) == True{} : Bool}:
  match a:
    case Nil{}:
      hb
    case Con{+x, +xt}:
      NL.below_con(x, LS.app(xt, b), k, NL.below_head(x, xt, k, ha), app_below(xt, b, k, NL.below_tail(x, xt, k, ha), hb))

def app_len(+a: List<&2, Nat>, +b: List<&2, Nat>) -> {PS.ln(LS.app(a, b)) == Nat.add(PS.ln(a), PS.ln(b)) : Nat}:
  match a:
    case Nil{}:
      {==}
    case Con{+x, +xt}:
      Equal.cong(Nat, Nat, t => 1n+t, PS.ln(LS.app(xt, b)), Nat.add(PS.ln(xt), PS.ln(b)), app_len(xt, b))
