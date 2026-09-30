import Base
import ../../../spec/crypto/curve25519/fe.bend as FV
import ../../../src/crypto/curve25519/fe.bend as FE
import ../../../src/crypto/curve25519/limbs.bend as LS
import ../../../src/crypto/ed25519/pick.bend as PK
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/word.bend as WD
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../fe/nl.bend as NL
import ../fe/pw.bend as PW
import ../fe/pass.bend as PS
import ../fe/prod.bend as PRD
import ../fe/ops.bend as OP
import ./pickb.bend as PB

# The selection by masks of src/crypto/curve25519/limbs.bend (pick) and
# src/crypto/ed25519/pick.bend (sel16): with the masks ohl(n, i) (1 at
# place i, 0 elsewhere), pick returns the list at place i, for lists of w
# limbs below 2^32.

def LN() -> Type:
  List<&2, Nat>

# every list has w limbs, each below 2^32
def okf(+one: Nat, +w: Nat, fs: List<&2, List<&2, Nat>>) -> Bool:
  match fs:
    case Nil{}:
      True{}
    case Con{+f, ft}:
      Bool.and(Bool.and(Nat.is_eq(PS.ln(f), w), FV.below(f, WD.sc(32n, one))), okf(one, w, ft))

def one_lt(+one: Nat, +h1: {one == 1n : Nat}) -> {Nat.is_lt(1n, WD.sc(32n, one)) == True{} : Bool}:
  L.subst(Nat, o => {Nat.is_lt(o, WD.sc(32n, one)) == True{} : Bool}, one, 1n, h1, PW.lt_sc(31n, 0n, one, h1))

def pu0(+one: Nat, +h1: {one == 1n : Nat}, +y: Nat, +hy: {Nat.is_lt(y, WD.sc(32n, one)) == True{} : Bool}) -> {LS.pu(y, 0n) == 0n : Nat}:
  Equal.trans(Nat, LS.pu(y, 0n), Nat.mul(y, 0n), 0n, PRD.pu_eq(one, h1, y, 0n, hy, PW.sc_pos(32n, one, h1), L.subst(Nat, z => {Nat.is_lt(z, WD.sc(32n, one)) == True{} : Bool}, 0n, Nat.mul(y, 0n), Equal.sym(Nat, Nat.mul(y, 0n), 0n, NA.mul_zero(y)), PW.sc_pos(32n, one, h1))), NA.mul_zero(y))

def pu1(+one: Nat, +h1: {one == 1n : Nat}, +y: Nat, +hy: {Nat.is_lt(y, WD.sc(32n, one)) == True{} : Bool}) -> {LS.pu(y, 1n) == y : Nat}:
  Equal.trans(Nat, LS.pu(y, 1n), Nat.mul(y, 1n), y, PRD.pu_eq(one, h1, y, 1n, hy, one_lt(one, h1), L.subst(Nat, z => {Nat.is_lt(z, WD.sc(32n, one)) == True{} : Bool}, y, Nat.mul(y, 1n), Equal.sym(Nat, Nat.mul(y, 1n), y, NA.mul_one(y)), hy)), NA.mul_one(y))

def con2(+x: Nat, +y: Nat, +xt: List<&2, Nat>, +yt: List<&2, Nat>, +e1: {x == y : Nat}, +e2: {xt == yt : List<&2, Nat>}) -> {Con{x, xt} == Con{y, yt} : List<&2, Nat>}:
  Equal.trans(List<&2, Nat>, Con{x, xt}, Con{y, xt}, Con{y, yt}, Equal.cong(Nat, List<&2, Nat>, t => Con{t, xt}, x, y, e1), Equal.cong(List<&2, Nat>, List<&2, Nat>, t => Con{y, t}, xt, yt, e2))

def scalu0(+one: Nat, +h1: {one == 1n : Nat}, +f: List<&2, Nat>, +hf: {FV.below(f, WD.sc(32n, one)) == True{} : Bool}) -> {LS.scalu(f, 0n) == LS.zeros(PS.ln(f)) : List<&2, Nat>}:
  match f:
    case Nil{}:
      {==}
    case Con{+y, +yt}:
      con2(LS.pu(y, 0n), 0n, LS.scalu(yt, 0n), LS.zeros(PS.ln(yt)), pu0(one, h1, y, NL.below_head(y, yt, WD.sc(32n, one), hf)), scalu0(one, h1, yt, NL.below_tail(y, yt, WD.sc(32n, one), hf)))

def scalu1(+one: Nat, +h1: {one == 1n : Nat}, +f: List<&2, Nat>, +hf: {FV.below(f, WD.sc(32n, one)) == True{} : Bool}) -> {LS.scalu(f, 1n) == f : List<&2, Nat>}:
  match f:
    case Nil{}:
      {==}
    case Con{+y, +yt}:
      con2(LS.pu(y, 1n), y, LS.scalu(yt, 1n), yt, pu1(one, h1, y, NL.below_head(y, yt, WD.sc(32n, one), hf)), scalu1(one, h1, yt, NL.below_tail(y, yt, WD.sc(32n, one), hf)))

def zeros_len(+n: Nat) -> {PS.ln(LS.zeros(n)) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+ +k:
      N.succ_cong(PS.ln(LS.zeros(k)), k, zeros_len(k))

# 0 + ys == ys
def addl_zl(+n: Nat, +ys: List<&2, Nat>, +hl: {PS.ln(ys) == n : Nat}) -> {LS.addl(LS.zeros(n), ys) == ys : List<&2, Nat>}:
  match n ys:
    case 0n Nil{}:
      {==}
    case 0n Con{y, yt}:
      {==}
    case 1n+k Nil{}:
      Empty.absurd({LS.addl(LS.zeros(1n+k), Nil{}) == Nil{} : List<&2, Nat>}, N.zero_succ(k, hl))
    case 1n+ +k Con{+y, +yt}:
      Equal.cong(List<&2, Nat>, List<&2, Nat>, t => Con{y, t}, LS.addl(LS.zeros(k), yt), yt, addl_zl(k, yt, N.succ_inj(PS.ln(yt), k, hl)))

# xs + 0 == xs
def addl_zr(+n: Nat, +xs: List<&2, Nat>, +hl: {PS.ln(xs) == n : Nat}) -> {LS.addl(xs, LS.zeros(n)) == xs : List<&2, Nat>}:
  match n xs:
    case 0n Nil{}:
      {==}
    case 0n Con{x, xt}:
      {==}
    case 1n+k Nil{}:
      Empty.absurd({LS.addl(Nil{}, LS.zeros(1n+k)) == Nil{} : List<&2, Nat>}, N.zero_succ(k, hl))
    case 1n+ +k Con{+x, +xt}:
      con2(Nat.add(x, 0n), x, LS.addl(xt, LS.zeros(k)), xt, N.add_zero(x), addl_zr(k, xt, N.succ_inj(PS.ln(xt), k, hl)))

def ok_len(+one: Nat, +w: Nat, +f: List<&2, Nat>, +ft: List<&2, List<&2, Nat>>, +h: {okf(one, w, Con{f, ft}) == True{} : Bool}) -> {PS.ln(f) == w : Nat}:
  N.eq_from_is_eq(PS.ln(f), w, L.and_left(Nat.is_eq(PS.ln(f), w), FV.below(f, WD.sc(32n, one)), L.and_left(Bool.and(Nat.is_eq(PS.ln(f), w), FV.below(f, WD.sc(32n, one))), okf(one, w, ft), h)))

def ok_below(+one: Nat, +w: Nat, +f: List<&2, Nat>, +ft: List<&2, List<&2, Nat>>, +h: {okf(one, w, Con{f, ft}) == True{} : Bool}) -> {FV.below(f, WD.sc(32n, one)) == True{} : Bool}:
  L.and_right(Nat.is_eq(PS.ln(f), w), FV.below(f, WD.sc(32n, one)), L.and_left(Bool.and(Nat.is_eq(PS.ln(f), w), FV.below(f, WD.sc(32n, one))), okf(one, w, ft), h))

def ok_tail(+one: Nat, +w: Nat, +f: List<&2, Nat>, +ft: List<&2, List<&2, Nat>>, +h: {okf(one, w, Con{f, ft}) == True{} : Bool}) -> {okf(one, w, ft) == True{} : Bool}:
  L.and_right(Bool.and(Nat.is_eq(PS.ln(f), w), FV.below(f, WD.sc(32n, one))), okf(one, w, ft), h)

# addl(a, b) == addl(a2, b2)
def addl2(+a: List<&2, Nat>, +a2: List<&2, Nat>, +b: List<&2, Nat>, +b2: List<&2, Nat>, +ea: {a == a2 : List<&2, Nat>}, +eb: {b == b2 : List<&2, Nat>}) -> {LS.addl(a, b) == LS.addl(a2, b2) : List<&2, Nat>}:
  Equal.trans(List<&2, Nat>, LS.addl(a, b), LS.addl(a2, b), LS.addl(a2, b2), Equal.cong(List<&2, Nat>, List<&2, Nat>, t => LS.addl(t, b), a, a2, ea), Equal.cong(List<&2, Nat>, List<&2, Nat>, t => LS.addl(a2, t), b, b2, eb))

# f scaled by 0 is w zeros
def sc0w(+one: Nat, +h1: {one == 1n : Nat}, +w: Nat, +f: List<&2, Nat>, +ft: List<&2, List<&2, Nat>>, +h: {okf(one, w, Con{f, ft}) == True{} : Bool}) -> {LS.scalu(f, 0n) == LS.zeros(w) : List<&2, Nat>}:
  Equal.trans(List<&2, Nat>, LS.scalu(f, 0n), LS.zeros(PS.ln(f)), LS.zeros(w), scalu0(one, h1, f, ok_below(one, w, f, ft, h)), Equal.cong(Nat, List<&2, Nat>, t => LS.zeros(t), PS.ln(f), w, ok_len(one, w, f, ft, h)))

# all masks 0: w zeros
def pick_z(+one: Nat, +h1: {one == 1n : Nat}, +w: Nat, +k: Nat, +fs: List<&2, List<&2, Nat>>, +h: {okf(one, w, fs) == True{} : Bool}) -> {LS.pick(w, LS.zeros(k), fs) == LS.zeros(w) : List<&2, Nat>}:
  match k fs:
    case 0n _:
      {==}
    case 1n+j Nil{}:
      {==}
    case 1n+ +j Con{+f, +ft}:
      Equal.trans(List<&2, Nat>, LS.addl(LS.scalu(f, 0n), LS.pick(w, LS.zeros(j), ft)), LS.addl(LS.zeros(w), LS.zeros(w)), LS.zeros(w), addl2(LS.scalu(f, 0n), LS.zeros(w), LS.pick(w, LS.zeros(j), ft), LS.zeros(w), sc0w(one, h1, w, f, ft, h), pick_z(one, h1, w, j, ft, ok_tail(one, w, f, ft, h))), addl_zl(w, LS.zeros(w), zeros_len(w)))

# the list at place i of the first n (w zeros when there is none)
def nthm(+w: Nat, n: Nat, fs: List<&2, List<&2, Nat>>, i: Nat) -> List<&2, Nat>:
  match n:
    case 0n:
      LS.zeros(w)
    case 1n+k:
      match fs:
        case Nil{}:
          LS.zeros(w)
        case Con{f, ft}:
          match i:
            case 0n:
              f
            case 1n+e:
              nthm(w, k, ft, e)

def nthm_len(+one: Nat, +w: Nat, +n: Nat, +fs: List<&2, List<&2, Nat>>, +i: Nat, +h: {okf(one, w, fs) == True{} : Bool}) -> {PS.ln(nthm(w, n, fs, i)) == w : Nat}:
  match n:
    case 0n:
      zeros_len(w)
    case 1n+ +k:
      match fs:
        case Nil{}:
          zeros_len(w)
        case Con{+f, +ft}:
          match i:
            case 0n:
              ok_len(one, w, f, ft, h)
            case 1n+ +e:
              nthm_len(one, w, k, ft, e, ok_tail(one, w, f, ft, h))

# the masks of place i select the list at place i
def pick_oh(+one: Nat, +h1: {one == 1n : Nat}, +w: Nat, +n: Nat, +fs: List<&2, List<&2, Nat>>, +i: Nat, +h: {okf(one, w, fs) == True{} : Bool}) -> {LS.pick(w, LS.ohl(n, i), fs) == nthm(w, n, fs, i) : List<&2, Nat>}:
  match n:
    case 0n:
      {==}
    case 1n+ +k:
      match fs:
        case Nil{}:
          match i:
            case 0n:
              {==}
            case 1n+e:
              {==}
        case Con{+f, +ft}:
          match i:
            case 0n:
              Equal.trans(List<&2, Nat>, LS.addl(LS.scalu(f, 1n), LS.pick(w, LS.zeros(k), ft)), LS.addl(f, LS.zeros(w)), f, addl2(LS.scalu(f, 1n), f, LS.pick(w, LS.zeros(k), ft), LS.zeros(w), scalu1(one, h1, f, ok_below(one, w, f, ft, h)), pick_z(one, h1, w, k, ft, ok_tail(one, w, f, ft, h))), addl_zr(w, f, ok_len(one, w, f, ft, h)))
            case 1n+ +e:
              Equal.trans(List<&2, Nat>, LS.addl(LS.scalu(f, 0n), LS.pick(w, LS.ohl(k, e), ft)), LS.addl(LS.zeros(w), nthm(w, k, ft, e)), nthm(w, k, ft, e), addl2(LS.scalu(f, 0n), LS.zeros(w), LS.pick(w, LS.ohl(k, e), ft), nthm(w, k, ft, e), sc0w(one, h1, w, f, ft, h), pick_oh(one, h1, w, k, ft, e, ok_tail(one, w, f, ft, h))), addl_zl(w, nthm(w, k, ft, e), nthm_len(one, w, k, ft, e, ok_tail(one, w, f, ft, h))))

# ---- field elements ----

def fe_eta(+x: FE.Fe) -> {x == FE.of_list(FE.to_list(x)) : FE.Fe}:
  match x:
    case FE.Fe{l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14}:
      {==}

# elements with the same limbs are equal
def fe_ext(+x: FE.Fe, +y: FE.Fe, +e: {FE.to_list(x) == FE.to_list(y) : List<&2, Nat>}) -> {x == y : FE.Fe}:
  Equal.trans(FE.Fe, x, FE.of_list(FE.to_list(x)), y, fe_eta(x), Equal.trans(FE.Fe, FE.of_list(FE.to_list(x)), FE.of_list(FE.to_list(y)), y, Equal.cong(List<&2, Nat>, FE.Fe, t => FE.of_list(t), FE.to_list(x), FE.to_list(y), e), Equal.sym(FE.Fe, y, FE.of_list(FE.to_list(y)), fe_eta(y))))

# an ok element: 15 limbs below 2^32
def ok1(+one: Nat, +f: FE.Fe, +o: {FV.ok(one, f) == True{} : Bool}) -> {Bool.and(Nat.is_eq(PS.ln(FE.to_list(f)), 15n), FV.below(FE.to_list(f), WD.sc(32n, one))) == True{} : Bool}:
  L.and_intro(Nat.is_eq(PS.ln(FE.to_list(f)), 15n), FV.below(FE.to_list(f), WD.sc(32n, one)), L.subst(Nat, z => {Nat.is_eq(z, 15n) == True{} : Bool}, 15n, PS.ln(FE.to_list(f)), Equal.sym(Nat, PS.ln(FE.to_list(f)), 15n, OP.L15(f)), {==}), NL.below_mono(FE.to_list(f), WD.sc(19n, one), WD.sc(32n, one), PW.le_sc(13n, 19n, one), o))

def ok_con(+one: Nat, +f: FE.Fe, +ft: List<&2, List<&2, Nat>>, +o: {FV.ok(one, f) == True{} : Bool}, +ht: {okf(one, 15n, ft) == True{} : Bool}) -> {okf(one, 15n, Con{FE.to_list(f), ft}) == True{} : Bool}:
  L.and_intro(Bool.and(Nat.is_eq(PS.ln(FE.to_list(f)), 15n), FV.below(FE.to_list(f), WD.sc(32n, one))), okf(one, 15n, ft), ok1(one, f, o), ht)

# sixteen ok elements
def okf16(+one: Nat, +f0: FE.Fe, +f1: FE.Fe, +f2: FE.Fe, +f3: FE.Fe, +f4: FE.Fe, +f5: FE.Fe, +f6: FE.Fe, +f7: FE.Fe, +f8: FE.Fe, +f9: FE.Fe, +f10: FE.Fe, +f11: FE.Fe, +f12: FE.Fe, +f13: FE.Fe, +f14: FE.Fe, +f15: FE.Fe, +o0: {FV.ok(one, f0) == True{} : Bool}, +o1: {FV.ok(one, f1) == True{} : Bool}, +o2: {FV.ok(one, f2) == True{} : Bool}, +o3: {FV.ok(one, f3) == True{} : Bool}, +o4: {FV.ok(one, f4) == True{} : Bool}, +o5: {FV.ok(one, f5) == True{} : Bool}, +o6: {FV.ok(one, f6) == True{} : Bool}, +o7: {FV.ok(one, f7) == True{} : Bool}, +o8: {FV.ok(one, f8) == True{} : Bool}, +o9: {FV.ok(one, f9) == True{} : Bool}, +o10: {FV.ok(one, f10) == True{} : Bool}, +o11: {FV.ok(one, f11) == True{} : Bool}, +o12: {FV.ok(one, f12) == True{} : Bool}, +o13: {FV.ok(one, f13) == True{} : Bool}, +o14: {FV.ok(one, f14) == True{} : Bool}, +o15: {FV.ok(one, f15) == True{} : Bool}) -> {okf(one, 15n, [FE.to_list(f0), FE.to_list(f1), FE.to_list(f2), FE.to_list(f3), FE.to_list(f4), FE.to_list(f5), FE.to_list(f6), FE.to_list(f7), FE.to_list(f8), FE.to_list(f9), FE.to_list(f10), FE.to_list(f11), FE.to_list(f12), FE.to_list(f13), FE.to_list(f14), FE.to_list(f15)]) == True{} : Bool}:
  ok_con(one, f0, [FE.to_list(f1), FE.to_list(f2), FE.to_list(f3), FE.to_list(f4), FE.to_list(f5), FE.to_list(f6), FE.to_list(f7), FE.to_list(f8), FE.to_list(f9), FE.to_list(f10), FE.to_list(f11), FE.to_list(f12), FE.to_list(f13), FE.to_list(f14), FE.to_list(f15)], o0, ok_con(one, f1, [FE.to_list(f2), FE.to_list(f3), FE.to_list(f4), FE.to_list(f5), FE.to_list(f6), FE.to_list(f7), FE.to_list(f8), FE.to_list(f9), FE.to_list(f10), FE.to_list(f11), FE.to_list(f12), FE.to_list(f13), FE.to_list(f14), FE.to_list(f15)], o1, ok_con(one, f2, [FE.to_list(f3), FE.to_list(f4), FE.to_list(f5), FE.to_list(f6), FE.to_list(f7), FE.to_list(f8), FE.to_list(f9), FE.to_list(f10), FE.to_list(f11), FE.to_list(f12), FE.to_list(f13), FE.to_list(f14), FE.to_list(f15)], o2, ok_con(one, f3, [FE.to_list(f4), FE.to_list(f5), FE.to_list(f6), FE.to_list(f7), FE.to_list(f8), FE.to_list(f9), FE.to_list(f10), FE.to_list(f11), FE.to_list(f12), FE.to_list(f13), FE.to_list(f14), FE.to_list(f15)], o3, ok_con(one, f4, [FE.to_list(f5), FE.to_list(f6), FE.to_list(f7), FE.to_list(f8), FE.to_list(f9), FE.to_list(f10), FE.to_list(f11), FE.to_list(f12), FE.to_list(f13), FE.to_list(f14), FE.to_list(f15)], o4, ok_con(one, f5, [FE.to_list(f6), FE.to_list(f7), FE.to_list(f8), FE.to_list(f9), FE.to_list(f10), FE.to_list(f11), FE.to_list(f12), FE.to_list(f13), FE.to_list(f14), FE.to_list(f15)], o5, ok_con(one, f6, [FE.to_list(f7), FE.to_list(f8), FE.to_list(f9), FE.to_list(f10), FE.to_list(f11), FE.to_list(f12), FE.to_list(f13), FE.to_list(f14), FE.to_list(f15)], o6, ok_con(one, f7, [FE.to_list(f8), FE.to_list(f9), FE.to_list(f10), FE.to_list(f11), FE.to_list(f12), FE.to_list(f13), FE.to_list(f14), FE.to_list(f15)], o7, ok_con(one, f8, [FE.to_list(f9), FE.to_list(f10), FE.to_list(f11), FE.to_list(f12), FE.to_list(f13), FE.to_list(f14), FE.to_list(f15)], o8, ok_con(one, f9, [FE.to_list(f10), FE.to_list(f11), FE.to_list(f12), FE.to_list(f13), FE.to_list(f14), FE.to_list(f15)], o9, ok_con(one, f10, [FE.to_list(f11), FE.to_list(f12), FE.to_list(f13), FE.to_list(f14), FE.to_list(f15)], o10, ok_con(one, f11, [FE.to_list(f12), FE.to_list(f13), FE.to_list(f14), FE.to_list(f15)], o11, ok_con(one, f12, [FE.to_list(f13), FE.to_list(f14), FE.to_list(f15)], o12, ok_con(one, f13, [FE.to_list(f14), FE.to_list(f15)], o13, ok_con(one, f14, [FE.to_list(f15)], o14, ok_con(one, f15, Nil{}, o15, {==}))))))))))))))))

# sel16 with the masks of place i is the element x at place i
def sel_i(+one: Nat, +h1: {one == 1n : Nat}, +m0: Nat, +m1: Nat, +m2: Nat, +m3: Nat, +m4: Nat, +m5: Nat, +m6: Nat, +m7: Nat, +m8: Nat, +m9: Nat, +m10: Nat, +m11: Nat, +m12: Nat, +m13: Nat, +m14: Nat, +m15: Nat, +f0: FE.Fe, +f1: FE.Fe, +f2: FE.Fe, +f3: FE.Fe, +f4: FE.Fe, +f5: FE.Fe, +f6: FE.Fe, +f7: FE.Fe, +f8: FE.Fe, +f9: FE.Fe, +f10: FE.Fe, +f11: FE.Fe, +f12: FE.Fe, +f13: FE.Fe, +f14: FE.Fe, +f15: FE.Fe, +hok: {okf(one, 15n, [FE.to_list(f0), FE.to_list(f1), FE.to_list(f2), FE.to_list(f3), FE.to_list(f4), FE.to_list(f5), FE.to_list(f6), FE.to_list(f7), FE.to_list(f8), FE.to_list(f9), FE.to_list(f10), FE.to_list(f11), FE.to_list(f12), FE.to_list(f13), FE.to_list(f14), FE.to_list(f15)]) == True{} : Bool}, +i: Nat, +em: {LS.ohl(16n, i) == [m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15] : List<&2, Nat>}, +x: FE.Fe, +ex: {nthm(15n, 16n, [FE.to_list(f0), FE.to_list(f1), FE.to_list(f2), FE.to_list(f3), FE.to_list(f4), FE.to_list(f5), FE.to_list(f6), FE.to_list(f7), FE.to_list(f8), FE.to_list(f9), FE.to_list(f10), FE.to_list(f11), FE.to_list(f12), FE.to_list(f13), FE.to_list(f14), FE.to_list(f15)], i) == FE.to_list(x) : List<&2, Nat>}) -> {PK.sel16(PK.M16{m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15}, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15) == x : FE.Fe}:
  +F = {[FE.to_list(f0), FE.to_list(f1), FE.to_list(f2), FE.to_list(f3), FE.to_list(f4), FE.to_list(f5), FE.to_list(f6), FE.to_list(f7), FE.to_list(f8), FE.to_list(f9), FE.to_list(f10), FE.to_list(f11), FE.to_list(f12), FE.to_list(f13), FE.to_list(f14), FE.to_list(f15)] : List<&2, List<&2, Nat>>}
  +S = PK.sel16(PK.M16{m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15}, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15)
  fe_ext(S, x, Equal.trans(List<&2, Nat>, FE.to_list(S), LS.pick(15n, [m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15], F), FE.to_list(x), PB.sel16_b(m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15), Equal.trans(List<&2, Nat>, LS.pick(15n, [m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15], F), LS.pick(15n, LS.ohl(16n, i), F), FE.to_list(x), Equal.cong(List<&2, Nat>, List<&2, Nat>, t => LS.pick(15n, t, F), [m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15], LS.ohl(16n, i), Equal.sym(List<&2, Nat>, LS.ohl(16n, i), [m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15], em)), Equal.trans(List<&2, Nat>, LS.pick(15n, LS.ohl(16n, i), F), nthm(15n, 16n, F, i), FE.to_list(x), pick_oh(one, h1, 15n, 16n, F, i, hok), ex))))
