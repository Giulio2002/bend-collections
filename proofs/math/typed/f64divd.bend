import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/math/w64.bend as SW
import ../../../src/math/w64.bend as X
import ../../../src/math/u64.bend as WU
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../natural/arith.bend as NR
import ./width.bend as WW
import ./u32laws.bend as LW
import ./w64dm.bend as DM
import ./w64mm.bend as MM

# Long division by 32-bit quotient digits (SoftFloat's f64_div quotient
# loop): one digit of r * 2^32 / b for r < b is its floor and remainder, and
# two digits make the floor and remainder of r * 2^64 / b.

def v(+x: U32) -> Nat:
  U32.to_nat(x)

# the remainder digit
def dig_r(+one: Nat, +h1: {one == 1n : Nat}, +rl: U32, +rh: U32, +ml: U32, +mh: U32, +e: U32, +hx: {Nat.is_lt(SW.value(WU.U64{rl, rh}), SW.value(WU.U64{ml, mh})) == True{} : Bool}, +hz: {U32.is_zero(mh) == False{} : Bool}) -> {SW.value(X.sub(WU.U64{0, rl}, X.fst_q(X.mul_32_64(X.q_start(WU.U64{0, rl}, rh, WU.U64{ml, mh}, e), WU.U64{ml, mh})))) == Nat.mod(C.shift(32n, SW.value(WU.U64{rl, rh})), SW.value(WU.U64{ml, mh})) : Nat}:
  MM.red_ve(one, h1, 0, rl, rh, ml, mh, e, hx, hz)

# the quotient digit
def dig_q(+one: Nat, +h1: {one == 1n : Nat}, +rl: U32, +rh: U32, +ml: U32, +mh: U32, +e: U32, +hx: {Nat.is_lt(SW.value(WU.U64{rl, rh}), SW.value(WU.U64{ml, mh})) == True{} : Bool}, +hz: {U32.is_zero(mh) == False{} : Bool}) -> {v(X.q_start(WU.U64{0, rl}, rh, WU.U64{ml, mh}, e)) == Nat.div(C.shift(32n, SW.value(WU.U64{rl, rh})), SW.value(WU.U64{ml, mh})) : Nat}:
  +PP = C.shift(32n, one)
  +ex = MM.x96_eq(0, rl, rh)
  +h0 = N.lt_add_r2(v(0), PP, C.shift(32n, SW.value(WU.U64{rl, rh})), WW.lt_one(32n, one, h1, v(0), LW.vb(0)))
  +e1 = Equal.sym(Nat, C.shift(32n, Nat.add(one, SW.value(WU.U64{rl, rh}))), Nat.add(PP, C.shift(32n, SW.value(WU.U64{rl, rh}))), WW.shift_add(32n, one, SW.value(WU.U64{rl, rh})))
  +h2 = WW.shift_mono(32n, Nat.add(one, SW.value(WU.U64{rl, rh})), SW.value(WU.U64{ml, mh}), L.subst(Nat, z => {Nat.is_le(Nat.add(z, SW.value(WU.U64{rl, rh})), SW.value(WU.U64{ml, mh})) == True{} : Bool}, 1n, one, Equal.sym(Nat, one, 1n, h1), N.lt_succ_le_succ(SW.value(WU.U64{rl, rh}), SW.value(WU.U64{ml, mh}), hx)))
  +e2 = Equal.trans(Nat, C.shift(32n, SW.value(WU.U64{ml, mh})), Nat.mul(SW.value(WU.U64{ml, mh}), PP), Nat.mul(PP, SW.value(WU.U64{ml, mh})), WW.shift_mul_one(32n, one, h1, SW.value(WU.U64{ml, mh})), NA.mul_comm(SW.value(WU.U64{ml, mh}), PP))
  +hY = N.lt_le_trans(Nat.add(v(0), C.shift(32n, SW.value(WU.U64{rl, rh}))), C.shift(32n, Nat.add(one, SW.value(WU.U64{rl, rh}))), Nat.mul(PP, SW.value(WU.U64{ml, mh})), L.subst(Nat, z => {Nat.is_lt(Nat.add(v(0), C.shift(32n, SW.value(WU.U64{rl, rh}))), z) == True{} : Bool}, Nat.add(PP, C.shift(32n, SW.value(WU.U64{rl, rh}))), C.shift(32n, Nat.add(one, SW.value(WU.U64{rl, rh}))), e1, h0), L.subst(Nat, z => {Nat.is_le(C.shift(32n, Nat.add(one, SW.value(WU.U64{rl, rh}))), z) == True{} : Bool}, C.shift(32n, SW.value(WU.U64{ml, mh})), Nat.mul(PP, SW.value(WU.U64{ml, mh})), e2, h2))
  +hX = L.subst(Nat, z => {Nat.is_lt(z, Nat.mul(PP, SW.value(WU.U64{ml, mh}))) == True{} : Bool}, Nat.add(v(0), C.shift(32n, SW.value(WU.U64{rl, rh}))), DM.X96(WU.U64{0, rl}, rh), Equal.sym(Nat, DM.X96(WU.U64{0, rl}, rh), Nat.add(v(0), C.shift(32n, SW.value(WU.U64{rl, rh}))), ex), hY)
  +bp = Nat.sub(SW.value(WU.U64{ml, mh}), 1n)
  +hB = Equal.sym(Nat, 1n+bp, SW.value(WU.U64{ml, mh}), N.sub_add(SW.value(WU.U64{ml, mh}), 1n, N.le_trans(1n, 1n+SW.value(WU.U64{rl, rh}), SW.value(WU.U64{ml, mh}), N.zero_le(SW.value(WU.U64{rl, rh})), N.lt_succ_le_succ(SW.value(WU.U64{rl, rh}), SW.value(WU.U64{ml, mh}), hx))))
  pr = DM.qs_pair(one, h1, WU.U64{0, rl}, rh, WU.U64{ml, mh}, e, 4294967295, {==}, hX)
  pq = DM.qs_fin2(DM.X96(WU.U64{0, rl}, rh), v(DM.QS(WU.U64{0, rl}, rh, WU.U64{ml, mh}, e, 4294967295)), SW.value(WU.U64{ml, mh}), bp, hB, pr)
  +dq = DM.pr1({Nat.div(DM.X96(WU.U64{0, rl}, rh), 1n+bp) == v(DM.QS(WU.U64{0, rl}, rh, WU.U64{ml, mh}, e, 4294967295)) : Nat}, {Nat.mod(DM.X96(WU.U64{0, rl}, rh), 1n+bp) == Nat.sub(DM.X96(WU.U64{0, rl}, rh), Nat.mul(v(DM.QS(WU.U64{0, rl}, rh, WU.U64{ml, mh}, e, 4294967295)), 1n+bp)) : Nat}, pq)
  +eq = Equal.cong(U32, Nat, w => v(w), X.q_start(WU.U64{0, rl}, rh, WU.U64{ml, mh}, e), DM.QS(WU.U64{0, rl}, rh, WU.U64{ml, mh}, e, 4294967295), DM.impl_qs(WU.U64{0, rl}, rh, WU.U64{ml, mh}, e))
  +ed = Equal.trans(Nat, Nat.div(DM.X96(WU.U64{0, rl}, rh), 1n+bp), Nat.div(C.shift(32n, SW.value(WU.U64{rl, rh})), 1n+bp), Nat.div(C.shift(32n, SW.value(WU.U64{rl, rh})), SW.value(WU.U64{ml, mh})), Equal.cong(Nat, Nat, w => Nat.div(w, 1n+bp), DM.X96(WU.U64{0, rl}, rh), C.shift(32n, SW.value(WU.U64{rl, rh})), ex), Equal.cong(Nat, Nat, w => Nat.div(C.shift(32n, SW.value(WU.U64{rl, rh})), w), 1n+bp, SW.value(WU.U64{ml, mh}), Equal.sym(Nat, SW.value(WU.U64{ml, mh}), 1n+bp, hB)))
  Equal.trans(Nat, v(X.q_start(WU.U64{0, rl}, rh, WU.U64{ml, mh}, e)), v(DM.QS(WU.U64{0, rl}, rh, WU.U64{ml, mh}, e, 4294967295)), Nat.div(C.shift(32n, SW.value(WU.U64{rl, rh})), SW.value(WU.U64{ml, mh})), eq, Equal.trans(Nat, v(DM.QS(WU.U64{0, rl}, rh, WU.U64{ml, mh}, e, 4294967295)), Nat.div(DM.X96(WU.U64{0, rl}, rh), 1n+bp), Nat.div(C.shift(32n, SW.value(WU.U64{rl, rh})), SW.value(WU.U64{ml, mh})), Equal.sym(Nat, Nat.div(DM.X96(WU.U64{0, rl}, rh), 1n+bp), v(DM.QS(WU.U64{0, rl}, rh, WU.U64{ml, mh}, e, 4294967295)), dq), ed))

# shifting a product shifts one factor
def sh_mul(+k: Nat, +q: Nat, +b: Nat) -> {C.shift(k, Nat.mul(q, b)) == Nat.mul(C.shift(k, q), b) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+ +kp:
      +i = sh_mul(kp, q, b)
      +a = Equal.cong(Nat, Nat, w => Nat.double(w), C.shift(kp, Nat.mul(q, b)), Nat.mul(C.shift(kp, q), b), i)
      +d1 = NA.double_mul(Nat.mul(C.shift(kp, q), b))
      +d2 = Equal.sym(Nat, Nat.mul(Nat.mul(2n, C.shift(kp, q)), b), Nat.mul(2n, Nat.mul(C.shift(kp, q), b)), NA.mul_assoc(2n, C.shift(kp, q), b))
      +d3 = Equal.cong(Nat, Nat, w => Nat.mul(w, b), Nat.mul(2n, C.shift(kp, q)), Nat.double(C.shift(kp, q)), Equal.sym(Nat, Nat.double(C.shift(kp, q)), Nat.mul(2n, C.shift(kp, q)), NA.double_mul(C.shift(kp, q))))
      Equal.trans(Nat, Nat.double(C.shift(kp, Nat.mul(q, b))), Nat.double(Nat.mul(C.shift(kp, q), b)), Nat.mul(Nat.double(C.shift(kp, q)), b), a, Equal.trans(Nat, Nat.double(Nat.mul(C.shift(kp, q), b)), Nat.mul(2n, Nat.mul(C.shift(kp, q), b)), Nat.mul(Nat.double(C.shift(kp, q)), b), d1, Equal.trans(Nat, Nat.mul(2n, Nat.mul(C.shift(kp, q), b)), Nat.mul(Nat.mul(2n, C.shift(kp, q)), b), Nat.mul(Nat.double(C.shift(kp, q)), b), d2, d3)))

# two digits: r * 2^64 = (q1 * 2^32 + q2) * b + r2
def two(+bp: Nat, +R: Nat, +q1: Nat, +r1: Nat, +q2: Nat, +r2: Nat, +e1: {q1 == Nat.div(C.shift(32n, R), 1n+bp) : Nat}, +f1: {r1 == Nat.mod(C.shift(32n, R), 1n+bp) : Nat}, +e2: {q2 == Nat.div(C.shift(32n, r1), 1n+bp) : Nat}, +f2: {r2 == Nat.mod(C.shift(32n, r1), 1n+bp) : Nat}) -> {Nat.add(Nat.mul(Nat.add(C.shift(32n, q1), q2), 1n+bp), r2) == C.shift(64n, R) : Nat}:
  +E1 = L.subst(Nat, w => {C.shift(32n, R) == Nat.add(Nat.mul(q1, 1n+bp), w) : Nat}, Nat.mod(C.shift(32n, R), 1n+bp), r1, Equal.sym(Nat, r1, Nat.mod(C.shift(32n, R), 1n+bp), f1), L.subst(Nat, w => {C.shift(32n, R) == Nat.add(Nat.mul(w, 1n+bp), Nat.mod(C.shift(32n, R), 1n+bp)) : Nat}, Nat.div(C.shift(32n, R), 1n+bp), q1, Equal.sym(Nat, q1, Nat.div(C.shift(32n, R), 1n+bp), e1), NR.dm_eq(bp, C.shift(32n, R))))
  +E2 = L.subst(Nat, w => {C.shift(32n, r1) == Nat.add(Nat.mul(q2, 1n+bp), w) : Nat}, Nat.mod(C.shift(32n, r1), 1n+bp), r2, Equal.sym(Nat, r2, Nat.mod(C.shift(32n, r1), 1n+bp), f2), L.subst(Nat, w => {C.shift(32n, r1) == Nat.add(Nat.mul(w, 1n+bp), Nat.mod(C.shift(32n, r1), 1n+bp)) : Nat}, Nat.div(C.shift(32n, r1), 1n+bp), q2, Equal.sym(Nat, q2, Nat.div(C.shift(32n, r1), 1n+bp), e2), NR.dm_eq(bp, C.shift(32n, r1))))
  +s1 = WW.shift_comp(32n, 32n, R)
  +s2 = Equal.cong(Nat, Nat, w => C.shift(32n, w), C.shift(32n, R), Nat.add(Nat.mul(q1, 1n+bp), r1), E1)
  +s3 = WW.shift_add(32n, Nat.mul(q1, 1n+bp), r1)
  +s4 = Equal.cong(Nat, Nat, w => Nat.add(w, C.shift(32n, r1)), C.shift(32n, Nat.mul(q1, 1n+bp)), Nat.mul(C.shift(32n, q1), 1n+bp), sh_mul(32n, q1, 1n+bp))
  +s5 = Equal.cong(Nat, Nat, w => Nat.add(Nat.mul(C.shift(32n, q1), 1n+bp), w), C.shift(32n, r1), Nat.add(Nat.mul(q2, 1n+bp), r2), E2)
  +s6 = Equal.sym(Nat, Nat.add(Nat.add(Nat.mul(C.shift(32n, q1), 1n+bp), Nat.mul(q2, 1n+bp)), r2), Nat.add(Nat.mul(C.shift(32n, q1), 1n+bp), Nat.add(Nat.mul(q2, 1n+bp), r2)), NA.add_assoc(Nat.mul(C.shift(32n, q1), 1n+bp), Nat.mul(q2, 1n+bp), r2))
  +s7 = Equal.cong(Nat, Nat, w => Nat.add(w, r2), Nat.add(Nat.mul(C.shift(32n, q1), 1n+bp), Nat.mul(q2, 1n+bp)), Nat.mul(Nat.add(C.shift(32n, q1), q2), 1n+bp), Equal.sym(Nat, Nat.mul(Nat.add(C.shift(32n, q1), q2), 1n+bp), Nat.add(Nat.mul(C.shift(32n, q1), 1n+bp), Nat.mul(q2, 1n+bp)), NA.mul_add_right(C.shift(32n, q1), q2, 1n+bp)))
  +ch = Equal.trans(Nat, C.shift(64n, R), C.shift(32n, C.shift(32n, R)), Nat.add(Nat.mul(Nat.add(C.shift(32n, q1), q2), 1n+bp), r2), s1, Equal.trans(Nat, C.shift(32n, C.shift(32n, R)), C.shift(32n, Nat.add(Nat.mul(q1, 1n+bp), r1)), Nat.add(Nat.mul(Nat.add(C.shift(32n, q1), q2), 1n+bp), r2), s2, Equal.trans(Nat, C.shift(32n, Nat.add(Nat.mul(q1, 1n+bp), r1)), Nat.add(C.shift(32n, Nat.mul(q1, 1n+bp)), C.shift(32n, r1)), Nat.add(Nat.mul(Nat.add(C.shift(32n, q1), q2), 1n+bp), r2), s3, Equal.trans(Nat, Nat.add(C.shift(32n, Nat.mul(q1, 1n+bp)), C.shift(32n, r1)), Nat.add(Nat.mul(C.shift(32n, q1), 1n+bp), C.shift(32n, r1)), Nat.add(Nat.mul(Nat.add(C.shift(32n, q1), q2), 1n+bp), r2), s4, Equal.trans(Nat, Nat.add(Nat.mul(C.shift(32n, q1), 1n+bp), C.shift(32n, r1)), Nat.add(Nat.mul(C.shift(32n, q1), 1n+bp), Nat.add(Nat.mul(q2, 1n+bp), r2)), Nat.add(Nat.mul(Nat.add(C.shift(32n, q1), q2), 1n+bp), r2), s5, Equal.trans(Nat, Nat.add(Nat.mul(C.shift(32n, q1), 1n+bp), Nat.add(Nat.mul(q2, 1n+bp), r2)), Nat.add(Nat.add(Nat.mul(C.shift(32n, q1), 1n+bp), Nat.mul(q2, 1n+bp)), r2), Nat.add(Nat.mul(Nat.add(C.shift(32n, q1), q2), 1n+bp), r2), s6, s7))))))
  Equal.sym(Nat, C.shift(64n, R), Nat.add(Nat.mul(Nat.add(C.shift(32n, q1), q2), 1n+bp), r2), ch)
