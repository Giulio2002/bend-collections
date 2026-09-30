import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/crypto/curve25519/field.bend as FS
import ../../lib/logic.bend as L
import ../../lib/arith.bend as AR
import ../curve25519/num.bend as M
import ../curve25519/limbs.bend as LM
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../../lib/nat.bend as N
import ../../lib/word.bend as WD
import ../../../src/crypto/curve25519/field.bend as F
import ../../lib/u32alg.bend as A
import ../../math/natural/arith.bend as NR
import ../../lib/u32.bend as U
import ../curve25519/cong.bend as G

# Lemmas extracted from the curve25519 byte-field library (consts, poly,
# freeze, fieldops, fold, reduce) and ed25519/{scalar,adc}: only the cones the
# Ed25519 scalar and decoding proofs use, so their closure stays small.

def consts_v(+x: U32) -> Nat:
  U32.to_nat(x)

def valo(+one: Nat, xs: List<&2, U32>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{h, t}:
      Nat.add(Nat.mul(one, U32.to_nat(h)), C.shift(8n, valo(one, t)))

def valo_value(+one: Nat, +h1: {one == 1n : Nat}, +xs: List<&2, U32>) -> {valo(one, xs) == FS.value(xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      +e0 = L.subst(Nat, o => {Nat.mul(o, consts_v(h)) == consts_v(h) : Nat}, 1n, one, Equal.sym(Nat, one, 1n, h1), AR.one_mul(consts_v(h)))
      M.cong_add(Nat.mul(one, consts_v(h)), consts_v(h), C.shift(8n, valo(one, t)), C.shift(8n, FS.value(t)), e0, M.cong_sc(8n, valo(one, t), FS.value(t), valo_value(one, h1, t)))

def rep(n: Nat, +k: U32, tl: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      tl
    case 1n+m:
      Con{k, rep(m, k, tl)}

def run0(+one: Nat, +n: Nat, +tl: List<&2, U32>) -> {valo(one, rep(n, 0, tl)) == LM.shn(n, valo(one, tl)) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+ +m:
      +R = valo(one, rep(m, 0, tl))
      +e1 = M.cong_l(Nat.mul(one, 0n), 0n, C.shift(8n, R), NA.mul_zero(one))
      Equal.trans(Nat, Nat.add(Nat.mul(one, 0n), C.shift(8n, R)), C.shift(8n, R), C.shift(8n, LM.shn(m, valo(one, tl))), e1, M.cong_sc(8n, R, LM.shn(m, valo(one, tl)), run0(one, m, tl)))

def one_k(+one: Nat, +h1: {one == 1n : Nat}, +k: Nat) -> {Nat.mul(one, k) == k : Nat}:
  L.subst(Nat, o => {Nat.mul(o, k) == k : Nat}, 1n, one, Equal.sym(Nat, one, 1n, h1), AR.one_mul(k))

def poly_v(+x: U32) -> Nat:
  U32.to_nat(x)

def len_le(n: Nat, xs: List<&2, U32>) -> Bool:
  match n:
    case 0n:
      match xs:
        case Nil{}:
          True{}
        case Con{x, xt}:
          False{}
    case 1n+m:
      match xs:
        case Nil{}:
          True{}
        case Con{x, xt}:
          len_le(m, xt)

def okb_len_le(+n: Nat, +xs: List<&2, U32>, +b: Nat, +e: {LM.okb(n, xs, b) == True{} : Bool}) -> {len_le(n, xs) == True{} : Bool}:
  match n xs:
    case 0n Nil{}:
      {==}
    case 0n Con{y, yt}:
      Empty.absurd({len_le(0n, Con{y, yt}) == True{} : Bool}, L.false_true(e))
    case 1n+m Nil{}:
      {==}
    case 1n+ +m Con{+y, +yt}:
      okb_len_le(m, yt, b, LM.okb_tail(m, y, yt, b, e))

def okb_mono(+n: Nat, +xs: List<&2, U32>, +b: Nat, +c: Nat, +hb: {Nat.is_le(b, c) == True{} : Bool}, +e: {LM.okb(n, xs, b) == True{} : Bool}) -> {LM.okb(n, xs, c) == True{} : Bool}:
  match n xs:
    case 0n Nil{}:
      {==}
    case 0n Con{y, yt}:
      Empty.absurd({LM.okb(0n, Con{y, yt}, c) == True{} : Bool}, L.false_true(e))
    case 1n+m Nil{}:
      Empty.absurd({LM.okb(1n+m, Nil{}, c) == True{} : Bool}, L.false_true(e))
    case 1n+ +m Con{+y, +yt}:
      L.and_intro(Nat.is_le(poly_v(y), c), LM.okb(m, yt, c), N.le_trans(poly_v(y), b, c, LM.okb_head(m, y, yt, b, e), hb), okb_mono(m, yt, b, c, hb, LM.okb_tail(m, y, yt, b, e)))

def le_add_l(+a: Nat, +b: Nat) -> {Nat.is_le(b, Nat.add(a, b)) == True{} : Bool}:
  %NA.add_comm(b, a) : {Nat.is_le(b, _) == True{} : Bool}
  N.le_add_right(b, a)

def addl_v(+one: Nat, +h1: {one == 1n : Nat}, +x: U32, +y: U32, +a: Nat, +b: Nat, +hx: {Nat.is_le(poly_v(x), a) == True{} : Bool}, +hy: {Nat.is_le(poly_v(y), b) == True{} : Bool}, +hab: {Nat.is_lt(Nat.add(a, b), WD.sc(32n, one)) == True{} : Bool}) -> {poly_v(U32.add(x, y)) == Nat.add(poly_v(x), poly_v(y)) : Nat}:
  LM.add_v(one, h1, x, y, N.le_lt_trans(Nat.add(poly_v(x), poly_v(y)), Nat.add(a, b), WD.sc(32n, one), M.le_add2(poly_v(x), poly_v(y), a, b, hx, hy), hab))

def addl_val(+one: Nat, +h1: {one == 1n : Nat}, +xs: List<&2, U32>, +ys: List<&2, U32>, +a: Nat, +b: Nat, +hx: {LM.lea(xs, a) == True{} : Bool}, +hy: {LM.lea(ys, b) == True{} : Bool}, +hab: {Nat.is_lt(Nat.add(a, b), WD.sc(32n, one)) == True{} : Bool}) -> {FS.value(F.addl(xs, ys)) == Nat.add(FS.value(xs), FS.value(ys)) : Nat}:
  match xs ys:
    case Nil{} _:
      {==}
    case Con{+x, +xt} Nil{}:
      Equal.sym(Nat, Nat.add(FS.value(Con{x, xt}), 0n), FS.value(Con{x, xt}), N.add_zero(FS.value(Con{x, xt})))
    case Con{+x, +xt} Con{+y, +yt}:
      +ev = addl_v(one, h1, x, y, a, b, LM.lea_head(x, xt, a, hx), LM.lea_head(y, yt, b, hy), hab)
      +ih = addl_val(one, h1, xt, yt, a, b, LM.lea_tail(x, xt, a, hx), LM.lea_tail(y, yt, b, hy), hab)
      +X = FS.value(xt)
      +Y = FS.value(yt)
      +e1 = M.cong_add(poly_v(U32.add(x, y)), Nat.add(poly_v(x), poly_v(y)), C.shift(8n, FS.value(F.addl(xt, yt))), C.shift(8n, Nat.add(X, Y)), ev, M.cong_sc(8n, FS.value(F.addl(xt, yt)), Nat.add(X, Y), ih))
      +e2 = M.cong_r(Nat.add(poly_v(x), poly_v(y)), C.shift(8n, Nat.add(X, Y)), Nat.add(C.shift(8n, X), C.shift(8n, Y)), Equal.sym(Nat, Nat.add(C.shift(8n, X), C.shift(8n, Y)), C.shift(8n, Nat.add(X, Y)), M.sc_add(8n, X, Y)))
      Equal.trans(Nat, Nat.add(poly_v(U32.add(x, y)), C.shift(8n, FS.value(F.addl(xt, yt)))), Nat.add(Nat.add(poly_v(x), poly_v(y)), C.shift(8n, Nat.add(X, Y))), Nat.add(Nat.add(poly_v(x), C.shift(8n, X)), Nat.add(poly_v(y), C.shift(8n, Y))), e1,
        Equal.trans(Nat, Nat.add(Nat.add(poly_v(x), poly_v(y)), C.shift(8n, Nat.add(X, Y))), Nat.add(Nat.add(poly_v(x), poly_v(y)), Nat.add(C.shift(8n, X), C.shift(8n, Y))), Nat.add(Nat.add(poly_v(x), C.shift(8n, X)), Nat.add(poly_v(y), C.shift(8n, Y))), e2, M.add4(poly_v(x), poly_v(y), C.shift(8n, X), C.shift(8n, Y))))

def poly_addl_okb(+one: Nat, +h1: {one == 1n : Nat}, +n: Nat, +xs: List<&2, U32>, +ys: List<&2, U32>, +a: Nat, +b: Nat, +hx: {LM.okb(n, xs, a) == True{} : Bool}, +hy: {LM.lea(ys, b) == True{} : Bool}, +hl: {len_le(n, ys) == True{} : Bool}, +hab: {Nat.is_lt(Nat.add(a, b), WD.sc(32n, one)) == True{} : Bool}) -> {LM.okb(n, F.addl(xs, ys), Nat.add(a, b)) == True{} : Bool}:
  match n xs ys:
    case 0n Nil{} Nil{}:
      {==}
    case 0n Nil{} Con{y, yt}:
      Empty.absurd({LM.okb(0n, Con{y, yt}, Nat.add(a, b)) == True{} : Bool}, L.false_true(hl))
    case 0n Con{x, xt} _:
      Empty.absurd({LM.okb(0n, F.addl(Con{x, xt}, ys), Nat.add(a, b)) == True{} : Bool}, L.false_true(hx))
    case 1n+m Nil{} _:
      Empty.absurd({LM.okb(1n+m, ys, Nat.add(a, b)) == True{} : Bool}, L.false_true(hx))
    case 1n+ +m Con{+x, +xt} Nil{}:
      okb_mono(1n+m, Con{x, xt}, a, Nat.add(a, b), N.le_add_right(a, b), hx)
    case 1n+ +m Con{+x, +xt} Con{+y, +yt}:
      +hxh = LM.okb_head(m, x, xt, a, hx)
      +hyh = LM.lea_head(y, yt, b, hy)
      +ev = addl_v(one, h1, x, y, a, b, hxh, hyh, hab)
      +hd = L.subst(Nat, z => {Nat.is_le(z, Nat.add(a, b)) == True{} : Bool}, Nat.add(poly_v(x), poly_v(y)), poly_v(U32.add(x, y)), Equal.sym(Nat, poly_v(U32.add(x, y)), Nat.add(poly_v(x), poly_v(y)), ev), M.le_add2(poly_v(x), poly_v(y), a, b, hxh, hyh))
      L.and_intro(Nat.is_le(poly_v(U32.add(x, y)), Nat.add(a, b)), LM.okb(m, F.addl(xt, yt), Nat.add(a, b)), hd, poly_addl_okb(one, h1, m, xt, yt, a, b, LM.okb_tail(m, x, xt, a, hx), LM.lea_tail(y, yt, b, hy), hl, hab))

def sc_mul_l(+k: Nat, +a: Nat, +x: Nat) -> {WD.sc(k, Nat.mul(a, x)) == Nat.mul(a, WD.sc(k, x)) : Nat}:
  +e1 = M.cong_sc(k, Nat.mul(a, x), Nat.mul(x, a), NA.mul_comm(a, x))
  +e2 = AR.sc_mul(k, x, a)
  +e3 = NA.mul_comm(WD.sc(k, x), a)
  Equal.trans(Nat, WD.sc(k, Nat.mul(a, x)), WD.sc(k, Nat.mul(x, a)), Nat.mul(a, WD.sc(k, x)), e1, Equal.trans(Nat, WD.sc(k, Nat.mul(x, a)), Nat.mul(WD.sc(k, x), a), Nat.mul(a, WD.sc(k, x)), e2, e3))

def fold_v(+x: U32) -> Nat:
  U32.to_nat(x)

def cr_okb(+one: Nat, +h1: {one == 1n : Nat}, +xs: List<&2, U32>, +hx: {LM.okb(32n, xs, WD.sc(28n, one)) == True{} : Bool}) -> {LM.okb(32n, LM.cl(F.carry(xs, 0)), 255n) == True{} : Bool}:
  LM.carry_ok(one, h1, 32n, xs, 0, hx, N.zero_le(WD.sc(21n, one)))

def cr_val(+one: Nat, +h1: {one == 1n : Nat}, +xs: List<&2, U32>, +hx: {LM.okb(32n, xs, WD.sc(28n, one)) == True{} : Bool}) -> {Nat.add(FS.value(LM.cl(F.carry(xs, 0))), LM.shn(32n, fold_v(LM.cc(F.carry(xs, 0))))) == FS.value(xs) : Nat}:
  +r = F.carry(xs, 0)
  +e = LM.carry_val(one, h1, xs, 0, LM.okb_lea(32n, xs, WD.sc(28n, one), hx), N.zero_le(WD.sc(21n, one)))
  %LM.sh_okb(32n, xs, WD.sc(28n, one), fold_v(LM.cc(r)), hx) : {Nat.add(FS.value(LM.cl(r)), _) == FS.value(xs) : Nat}
  Equal.trans(Nat, Nat.add(FS.value(LM.cl(r)), LM.sh(xs, fold_v(LM.cc(r)))), Nat.add(FS.value(xs), 0n), FS.value(xs), e, N.add_zero(FS.value(xs)))

def reduce_v(+x: U32) -> Nat:
  U32.to_nat(x)

def val_lt(+one: Nat, +h1: {one == 1n : Nat}, +n: Nat, +xs: List<&2, U32>, +e: {LM.okb(n, xs, 255n) == True{} : Bool}) -> {Nat.is_lt(FS.value(xs), LM.shn(n, one)) == True{} : Bool}:
  match n xs:
    case 0n Nil{}:
      L.subst(Nat, o => {Nat.is_lt(0n, o) == True{} : Bool}, 1n, one, Equal.sym(Nat, one, 1n, h1), {==})
    case 0n Con{y, yt}:
      Empty.absurd({Nat.is_lt(FS.value(Con{y, yt}), one) == True{} : Bool}, L.false_true(e))
    case 1n+m Nil{}:
      Empty.absurd({Nat.is_lt(0n, LM.shn(1n+m, one)) == True{} : Bool}, L.false_true(e))
    case 1n+ +m Con{+y, +yt}:
      +X = FS.value(yt)
      +ih = val_lt(one, h1, m, yt, LM.okb_tail(m, y, yt, 255n, e))
      +a = M.le_sc(8n, 1n+X, LM.shn(m, one), N.lt_succ_le_succ(X, LM.shn(m, one), ih))
      +b = L.subst(Nat, z => {Nat.is_le(z, C.shift(8n, LM.shn(m, one))) == True{} : Bool}, WD.sc(8n, 1n+X), Nat.add(256n, C.shift(8n, X)), A.sc_succ(8n, X), a)
      +c = N.lt_add_r2(reduce_v(y), 256n, C.shift(8n, X), N.le_lt_succ(reduce_v(y), 255n, LM.okb_head(m, y, yt, 255n, e)))
      N.lt_le_trans(Nat.add(reduce_v(y), C.shift(8n, X)), Nat.add(256n, C.shift(8n, X)), C.shift(8n, LM.shn(m, one)), c, b)

def lt_cancel_r(+a: Nat, +b: Nat, +t: Nat, +h: {Nat.is_lt(Nat.add(a, t), Nat.add(b, t)) == True{} : Bool}) -> {Nat.is_lt(a, b) == True{} : Bool}:
  +h1 = N.lt_succ_le_succ(Nat.add(a, t), Nat.add(b, t), h)
  +h2 = L.subst(Nat, z => {Nat.is_le(z, Nat.add(b, t)) == True{} : Bool}, 1n+Nat.add(a, t), Nat.add(1n+a, t), {==}, h1)
  +h3 = L.subst(Nat, z => {Nat.is_le(z, Nat.add(b, t)) == True{} : Bool}, Nat.add(1n+a, t), Nat.add(t, 1n+a), NA.add_comm(1n+a, t), h2)
  +h4 = L.subst(Nat, z => {Nat.is_le(Nat.add(t, 1n+a), z) == True{} : Bool}, Nat.add(b, t), Nat.add(t, b), NA.add_comm(b, t), h3)
  +h5 = L.subst(Bool, z => {z == True{} : Bool}, Nat.is_le(Nat.add(t, 1n+a), Nat.add(t, b)), Nat.is_le(1n+a, b), NR.le_add_cancel(t, 1n+a, b), h4)
  N.succ_le_lt(a, b, h5)

def shn_lt_cancel(+c: Nat, +d: Nat, +h: {Nat.is_lt(LM.shn(32n, c), LM.shn(32n, d)) == True{} : Bool}) -> {Nat.is_lt(c, d) == True{} : Bool}:
  AR.sc_lt_cancel(256n, c, d, h)

def le_small(+one: Nat, +h1: {one == 1n : Nat}, +x: Nat, +hx: {Nat.is_le(x, 4096n) == True{} : Bool}) -> {Nat.is_le(x, WD.sc(28n, one)) == True{} : Bool}:
  +a = L.subst(Nat, o => {Nat.is_le(4096n, WD.sc(12n, o)) == True{} : Bool}, 1n, one, Equal.sym(Nat, one, 1n, h1), {==})
  N.le_trans(x, WD.sc(12n, one), WD.sc(28n, one), N.le_trans(x, 4096n, WD.sc(12n, one), hx, a), M.sc_mono(16n, 12n, one))

def lt32_small(+one: Nat, +h1: {one == 1n : Nat}, +x: Nat, +hx: {Nat.is_le(x, 4096n) == True{} : Bool}) -> {Nat.is_lt(x, WD.sc(32n, one)) == True{} : Bool}:
  N.le_lt_trans(x, WD.sc(28n, one), WD.sc(32n, one), le_small(one, h1, x, hx), LM.sc_lt(3n, 28n, one, h1))

def fieldops_addl_okb(+one: Nat, +h1: {one == 1n : Nat}, +a: List<&2, U32>, +b: List<&2, U32>, +ha: {LM.okb(32n, a, 255n) == True{} : Bool}, +hb: {LM.okb(32n, b, 255n) == True{} : Bool}) -> {LM.okb(32n, F.addl(a, b), WD.sc(28n, one)) == True{} : Bool}:
  +e = poly_addl_okb(one, h1, 32n, a, b, 255n, 255n, ha, LM.okb_lea(32n, b, 255n, hb), okb_len_le(32n, b, 255n, hb), lt32_small(one, h1, Nat.add(255n, 255n), {==}))
  okb_mono(32n, F.addl(a, b), Nat.add(255n, 255n), WD.sc(28n, one), le_small(one, h1, Nat.add(255n, 255n), {==}), e)

def freeze_v(+x: U32) -> Nat:
  U32.to_nat(x)

def comp_p_shape() -> {F.comp_p() == Con{19, rep(30n, 0, Con{128, Nil{}})} : List<&2, U32>}:
  {==}

def comp_p_val(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}) -> {valo(one, F.comp_p()) == Nat.add(1n+pp, 38n) : Nat}:
  +P = {1n+pp : Nat}
  +R = rep(30n, 0, Con{128, Nil{}})
  %Equal.sym(List<&2, U32>, F.comp_p(), Con{19, R}, comp_p_shape()) : {valo(one, _) == Nat.add(P, 38n) : Nat}
  +e1 = run0(one, 30n, Con{128, Nil{}})
  +e2 = L.subst(Nat, o => {valo(o, Con{128, Nil{}}) == WD.sc(7n, o) : Nat}, 1n, one, Equal.sym(Nat, one, 1n, h1), {==})
  +e3 = Equal.trans(Nat, valo(one, R), LM.shn(30n, valo(one, Con{128, Nil{}})), LM.shn(30n, WD.sc(7n, one)), e1, Equal.cong(Nat, Nat, t => LM.shn(30n, t), valo(one, Con{128, Nil{}}), WD.sc(7n, one), e2))
  +e4 = M.cong_add(Nat.mul(one, freeze_v(19)), 19n, C.shift(8n, valo(one, R)), WD.sc(255n, one), one_k(one, h1, freeze_v(19)), M.cong_sc(8n, valo(one, R), LM.shn(30n, WD.sc(7n, one)), e3))
  +e5 = M.cong_r(19n, WD.sc(255n, one), Nat.add(P, 19n), Equal.sym(Nat, Nat.add(P, 19n), WD.sc(255n, one), hP))
  Equal.trans(Nat, Nat.add(Nat.mul(one, freeze_v(19)), C.shift(8n, valo(one, R))), Nat.add(19n, WD.sc(255n, one)), Nat.add(P, 38n), e4, Equal.trans(Nat, Nat.add(19n, WD.sc(255n, one)), Nat.add(19n, Nat.add(P, 19n)), Nat.add(P, 38n), e5, NA.add_swap(19n, P, 19n)))

def t_val(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}) -> {LM.shn(32n, one) == Nat.add(Nat.add(1n+pp, 1n+pp), 38n) : Nat}:
  +P = {1n+pp : Nat}
  +X = WD.sc(255n, one)
  +e1 = Equal.sym(Nat, Nat.add(X, X), WD.sc(256n, one), M.sc_dbl(255n, one))
  +e2 = M.cong_add(X, Nat.add(P, 19n), X, Nat.add(P, 19n), Equal.sym(Nat, Nat.add(P, 19n), X, hP), Equal.sym(Nat, Nat.add(P, 19n), X, hP))
  Equal.trans(Nat, WD.sc(256n, one), Nat.add(X, X), Nat.add(Nat.add(P, P), 38n), e1, Equal.trans(Nat, Nat.add(X, X), Nat.add(Nat.add(P, 19n), Nat.add(P, 19n)), Nat.add(Nat.add(P, P), 38n), e2, M.add4(P, 19n, P, 19n)))

def adc_v(+x: U32) -> Nat:
  U32.to_nat(x)

def adc_ok(xs: List<&2, U32>, ys: List<&2, U32>, zs: List<&2, U32>, +c: Nat, +co: Nat) -> Bool:
  match xs ys zs:
    case Nil{} Nil{} Nil{}:
      Nat.is_eq(c, co)
    case Con{x, xt} Con{y, yt} Con{z, zt}:
      +s = Nat.add(Nat.add(U32.to_nat(x), U32.to_nat(y)), c)
      Bool.and(Nat.is_eq(Nat.mod(s, 256n), U32.to_nat(z)), adc_ok(xt, yt, zt, Nat.div(s, 256n), co))
    case _ _ _:
      False{}

def digit(+one: Nat, +x: Nat, +y: Nat, +c: Nat, +z: Nat, +hz: {Nat.mod(Nat.add(Nat.add(x, y), c), 256n) == z : Nat}) -> {Nat.add(Nat.add(Nat.mul(one, x), Nat.mul(one, y)), Nat.mul(one, c)) == Nat.add(Nat.mul(one, z), C.shift(8n, Nat.mul(one, Nat.div(Nat.add(Nat.add(x, y), c), 256n)))) : Nat}:
  +s = Nat.add(Nat.add(x, y), c)
  +q = Nat.div(s, 256n)
  +e1 = Equal.trans(Nat, Nat.add(Nat.add(Nat.mul(one, x), Nat.mul(one, y)), Nat.mul(one, c)), Nat.add(Nat.mul(one, Nat.add(x, y)), Nat.mul(one, c)), Nat.mul(one, s), M.cong_l(Nat.add(Nat.mul(one, x), Nat.mul(one, y)), Nat.mul(one, Nat.add(x, y)), Nat.mul(one, c), Equal.sym(Nat, Nat.mul(one, Nat.add(x, y)), Nat.add(Nat.mul(one, x), Nat.mul(one, y)), NA.mul_add_left(one, x, y))), Equal.sym(Nat, Nat.mul(one, s), Nat.add(Nat.mul(one, Nat.add(x, y)), Nat.mul(one, c)), NA.mul_add_left(one, Nat.add(x, y), c)))
  +e2 = Equal.trans(Nat, s, Nat.add(Nat.mod(s, 256n), C.shift(8n, q)), Nat.add(z, C.shift(8n, q)), Equal.sym(Nat, Nat.add(Nat.mod(s, 256n), C.shift(8n, q)), s, LM.dm256(s)), M.cong_l(Nat.mod(s, 256n), z, C.shift(8n, q), hz))
  +e3 = Equal.trans(Nat, Nat.mul(one, s), Nat.mul(one, Nat.add(z, C.shift(8n, q))), Nat.add(Nat.mul(one, z), Nat.mul(one, C.shift(8n, q))), Equal.cong(Nat, Nat, t => Nat.mul(one, t), s, Nat.add(z, C.shift(8n, q)), e2), NA.mul_add_left(one, z, C.shift(8n, q)))
  +e4 = M.cong_r(Nat.mul(one, z), Nat.mul(one, C.shift(8n, q)), C.shift(8n, Nat.mul(one, q)), Equal.sym(Nat, WD.sc(8n, Nat.mul(one, q)), Nat.mul(one, WD.sc(8n, q)), sc_mul_l(8n, one, q)))
  Equal.trans(Nat, Nat.add(Nat.add(Nat.mul(one, x), Nat.mul(one, y)), Nat.mul(one, c)), Nat.mul(one, s), Nat.add(Nat.mul(one, z), C.shift(8n, Nat.mul(one, q))), e1, Equal.trans(Nat, Nat.mul(one, s), Nat.add(Nat.mul(one, z), Nat.mul(one, C.shift(8n, q))), Nat.add(Nat.mul(one, z), C.shift(8n, Nat.mul(one, q))), e3, e4))

def swap5(+a: Nat, +b: Nat, +c: Nat, +X: Nat, +Y: Nat) -> {Nat.add(Nat.add(Nat.add(a, X), Nat.add(b, Y)), c) == Nat.add(Nat.add(Nat.add(a, b), c), Nat.add(X, Y)) : Nat}:
  +e1 = M.cong_l(Nat.add(Nat.add(a, X), Nat.add(b, Y)), Nat.add(Nat.add(a, b), Nat.add(X, Y)), c, M.add4(a, X, b, Y))
  +e2 = Equal.trans(Nat, Nat.add(Nat.add(Nat.add(a, b), Nat.add(X, Y)), c), Nat.add(Nat.add(a, b), Nat.add(Nat.add(X, Y), c)), Nat.add(Nat.add(Nat.add(a, b), c), Nat.add(X, Y)), NA.add_assoc(Nat.add(a, b), Nat.add(X, Y), c), Equal.trans(Nat, Nat.add(Nat.add(a, b), Nat.add(Nat.add(X, Y), c)), Nat.add(Nat.add(a, b), Nat.add(c, Nat.add(X, Y))), Nat.add(Nat.add(Nat.add(a, b), c), Nat.add(X, Y)), M.cong_r(Nat.add(a, b), Nat.add(Nat.add(X, Y), c), Nat.add(c, Nat.add(X, Y)), NA.add_comm(Nat.add(X, Y), c)), Equal.sym(Nat, Nat.add(Nat.add(Nat.add(a, b), c), Nat.add(X, Y)), Nat.add(Nat.add(a, b), Nat.add(c, Nat.add(X, Y))), NA.add_assoc(Nat.add(a, b), c, Nat.add(X, Y)))))
  Equal.trans(Nat, Nat.add(Nat.add(Nat.add(a, X), Nat.add(b, Y)), c), Nat.add(Nat.add(Nat.add(a, b), Nat.add(X, Y)), c), Nat.add(Nat.add(Nat.add(a, b), c), Nat.add(X, Y)), e1, e2)

def adc_val(+one: Nat, +xs: List<&2, U32>, +ys: List<&2, U32>, +zs: List<&2, U32>, +c: Nat, +co: Nat, +h: {adc_ok(xs, ys, zs, c, co) == True{} : Bool}) -> {Nat.add(Nat.add(valo(one, xs), valo(one, ys)), Nat.mul(one, c)) == Nat.add(valo(one, zs), LM.sh(xs, Nat.mul(one, co))) : Nat}:
  match xs ys zs:
    case Nil{} Nil{} Nil{}:
      %N.eq_from_is_eq(c, co, h) : {Nat.add(Nat.add(0n, 0n), Nat.mul(one, c)) == Nat.add(0n, Nat.mul(one, _)) : Nat}
      {==}
    case Con{+x, +xt} Con{+y, +yt} Con{+z, +zt}:
      +s = Nat.add(Nat.add(adc_v(x), adc_v(y)), c)
      +q = Nat.div(s, 256n)
      +hz = N.eq_from_is_eq(Nat.mod(s, 256n), adc_v(z), L.and_left(Nat.is_eq(Nat.mod(s, 256n), adc_v(z)), adc_ok(xt, yt, zt, q, co), h))
      +ih = adc_val(one, xt, yt, zt, q, co, L.and_right(Nat.is_eq(Nat.mod(s, 256n), adc_v(z)), adc_ok(xt, yt, zt, q, co), h))
      +X = valo(one, xt)
      +Y = valo(one, yt)
      +Z = valo(one, zt)
      +a = Nat.mul(one, adc_v(x))
      +b = Nat.mul(one, adc_v(y))
      +cc = Nat.mul(one, c)
      +e1 = swap5(a, b, cc, C.shift(8n, X), C.shift(8n, Y))
      +e2 = M.cong_add(Nat.add(Nat.add(a, b), cc), Nat.add(Nat.mul(one, adc_v(z)), C.shift(8n, Nat.mul(one, q))), Nat.add(C.shift(8n, X), C.shift(8n, Y)), C.shift(8n, Nat.add(X, Y)), digit(one, adc_v(x), adc_v(y), c, adc_v(z), hz), M.sc_add(8n, X, Y))
      +e3 = Equal.trans(Nat, Nat.add(Nat.add(Nat.mul(one, adc_v(z)), C.shift(8n, Nat.mul(one, q))), C.shift(8n, Nat.add(X, Y))), Nat.add(Nat.mul(one, adc_v(z)), Nat.add(C.shift(8n, Nat.mul(one, q)), C.shift(8n, Nat.add(X, Y)))), Nat.add(Nat.mul(one, adc_v(z)), C.shift(8n, Nat.add(Nat.add(X, Y), Nat.mul(one, q)))), NA.add_assoc(Nat.mul(one, adc_v(z)), C.shift(8n, Nat.mul(one, q)), C.shift(8n, Nat.add(X, Y))), M.cong_r(Nat.mul(one, adc_v(z)), Nat.add(C.shift(8n, Nat.mul(one, q)), C.shift(8n, Nat.add(X, Y))), C.shift(8n, Nat.add(Nat.add(X, Y), Nat.mul(one, q))), Equal.trans(Nat, Nat.add(C.shift(8n, Nat.mul(one, q)), C.shift(8n, Nat.add(X, Y))), C.shift(8n, Nat.add(Nat.mul(one, q), Nat.add(X, Y))), C.shift(8n, Nat.add(Nat.add(X, Y), Nat.mul(one, q))), M.sc_add(8n, Nat.mul(one, q), Nat.add(X, Y)), M.cong_sc(8n, Nat.add(Nat.mul(one, q), Nat.add(X, Y)), Nat.add(Nat.add(X, Y), Nat.mul(one, q)), NA.add_comm(Nat.mul(one, q), Nat.add(X, Y))))))
      +e4 = M.cong_r(Nat.mul(one, adc_v(z)), C.shift(8n, Nat.add(Nat.add(X, Y), Nat.mul(one, q))), C.shift(8n, Nat.add(Z, LM.sh(xt, Nat.mul(one, co)))), M.cong_sc(8n, Nat.add(Nat.add(X, Y), Nat.mul(one, q)), Nat.add(Z, LM.sh(xt, Nat.mul(one, co))), ih))
      +e5 = Equal.trans(Nat, Nat.add(Nat.mul(one, adc_v(z)), C.shift(8n, Nat.add(Z, LM.sh(xt, Nat.mul(one, co))))), Nat.add(Nat.mul(one, adc_v(z)), Nat.add(C.shift(8n, Z), C.shift(8n, LM.sh(xt, Nat.mul(one, co))))), Nat.add(Nat.add(Nat.mul(one, adc_v(z)), C.shift(8n, Z)), C.shift(8n, LM.sh(xt, Nat.mul(one, co)))), M.cong_r(Nat.mul(one, adc_v(z)), C.shift(8n, Nat.add(Z, LM.sh(xt, Nat.mul(one, co)))), Nat.add(C.shift(8n, Z), C.shift(8n, LM.sh(xt, Nat.mul(one, co)))), Equal.sym(Nat, Nat.add(C.shift(8n, Z), C.shift(8n, LM.sh(xt, Nat.mul(one, co)))), C.shift(8n, Nat.add(Z, LM.sh(xt, Nat.mul(one, co)))), M.sc_add(8n, Z, LM.sh(xt, Nat.mul(one, co))))), Equal.sym(Nat, Nat.add(Nat.add(Nat.mul(one, adc_v(z)), C.shift(8n, Z)), C.shift(8n, LM.sh(xt, Nat.mul(one, co)))), Nat.add(Nat.mul(one, adc_v(z)), Nat.add(C.shift(8n, Z), C.shift(8n, LM.sh(xt, Nat.mul(one, co))))), NA.add_assoc(Nat.mul(one, adc_v(z)), C.shift(8n, Z), C.shift(8n, LM.sh(xt, Nat.mul(one, co))))))
      Equal.trans(Nat, Nat.add(Nat.add(Nat.add(a, C.shift(8n, X)), Nat.add(b, C.shift(8n, Y))), cc), Nat.add(Nat.add(Nat.add(a, b), cc), Nat.add(C.shift(8n, X), C.shift(8n, Y))), Nat.add(Nat.add(Nat.mul(one, adc_v(z)), C.shift(8n, Z)), C.shift(8n, LM.sh(xt, Nat.mul(one, co)))), e1,
        Equal.trans(Nat, Nat.add(Nat.add(Nat.add(a, b), cc), Nat.add(C.shift(8n, X), C.shift(8n, Y))), Nat.add(Nat.add(Nat.mul(one, adc_v(z)), C.shift(8n, Nat.mul(one, q))), C.shift(8n, Nat.add(X, Y))), Nat.add(Nat.add(Nat.mul(one, adc_v(z)), C.shift(8n, Z)), C.shift(8n, LM.sh(xt, Nat.mul(one, co)))), e2,
          Equal.trans(Nat, Nat.add(Nat.add(Nat.mul(one, adc_v(z)), C.shift(8n, Nat.mul(one, q))), C.shift(8n, Nat.add(X, Y))), Nat.add(Nat.mul(one, adc_v(z)), C.shift(8n, Nat.add(Nat.add(X, Y), Nat.mul(one, q)))), Nat.add(Nat.add(Nat.mul(one, adc_v(z)), C.shift(8n, Z)), C.shift(8n, LM.sh(xt, Nat.mul(one, co)))), e3,
            Equal.trans(Nat, Nat.add(Nat.mul(one, adc_v(z)), C.shift(8n, Nat.add(Nat.add(X, Y), Nat.mul(one, q)))), Nat.add(Nat.mul(one, adc_v(z)), C.shift(8n, Nat.add(Z, LM.sh(xt, Nat.mul(one, co))))), Nat.add(Nat.add(Nat.mul(one, adc_v(z)), C.shift(8n, Z)), C.shift(8n, LM.sh(xt, Nat.mul(one, co)))), e4, e5))))
    case Nil{} Nil{} Con{z, zt}:
      Empty.absurd({Nat.add(Nat.add(0n, 0n), Nat.mul(one, c)) == Nat.add(valo(one, Con{z, zt}), Nat.mul(one, co)) : Nat}, L.false_true(h))
    case Nil{} Con{y, yt} _:
      Empty.absurd({Nat.add(Nat.add(0n, valo(one, Con{y, yt})), Nat.mul(one, c)) == Nat.add(valo(one, zs), Nat.mul(one, co)) : Nat}, L.false_true(h))
    case Con{x, xt} Nil{} _:
      Empty.absurd({Nat.add(Nat.add(valo(one, Con{x, xt}), 0n), Nat.mul(one, c)) == Nat.add(valo(one, zs), LM.sh(Con{x, xt}, Nat.mul(one, co))) : Nat}, L.false_true(h))
    case Con{x, xt} Con{y, yt} Nil{}:
      Empty.absurd({Nat.add(Nat.add(valo(one, Con{x, xt}), valo(one, Con{y, yt})), Nat.mul(one, c)) == Nat.add(0n, LM.sh(Con{x, xt}, Nat.mul(one, co))) : Nat}, L.false_true(h))

def valo_u(+one: Nat, +xs: List<&2, U32>) -> {valo(one, xs) == FS.uvalue(one, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +xt}:
      M.cong_r(Nat.mul(one, adc_v(x)), C.shift(8n, valo(one, xt)), C.shift(8n, FS.uvalue(one, xt)), M.cong_sc(8n, valo(one, xt), FS.uvalue(one, xt), valo_u(one, xt)))

def scalar_v(+x: U32) -> Nat:
  U32.to_nat(x)

def T(+one: Nat) -> Nat:
  LM.shn(32n, one)

def ad_okb(+one: Nat, +h1: {one == 1n : Nat}, +x: List<&2, U32>, +cp: List<&2, U32>, +hx: {LM.okb(32n, x, 255n) == True{} : Bool}, +hk: {LM.okb(32n, cp, 255n) == True{} : Bool}) -> {LM.okb(32n, F.addl(x, cp), WD.sc(28n, one)) == True{} : Bool}:
  fieldops_addl_okb(one, h1, x, cp, hx, hk)

def cvx(+one: Nat, +h1: {one == 1n : Nat}, +mm: Nat, +x: List<&2, U32>, +cp: List<&2, U32>, +hx: {LM.okb(32n, x, 255n) == True{} : Bool}, +hk: {LM.okb(32n, cp, 255n) == True{} : Bool}) -> {Nat.add(FS.value(LM.cl(F.carry(F.addl(x, cp), 0))), LM.shn(32n, scalar_v(LM.cc(F.carry(F.addl(x, cp), 0))))) == Nat.add(FS.value(x), FS.value(cp)) : Nat}:
  +ys = F.addl(x, cp)
  Equal.trans(Nat, Nat.add(FS.value(LM.cl(F.carry(ys, 0))), LM.shn(32n, scalar_v(LM.cc(F.carry(ys, 0))))), FS.value(ys), Nat.add(FS.value(x), FS.value(cp)), cr_val(one, h1, ys, ad_okb(one, h1, x, cp, hx, hk)), addl_val(one, h1, x, cp, 255n, 255n, LM.okb_lea(32n, x, 255n, hx), LM.okb_lea(32n, cp, 255n, hk), lt32_small(one, h1, Nat.add(255n, 255n), {==})))

def cp_val(+one: Nat, +h1: {one == 1n : Nat}, +mm: Nat, +cp: List<&2, U32>, +hv: {Nat.add(valo(one, cp), 1n+mm) == T(one) : Nat}) -> {Nat.add(FS.value(cp), 1n+mm) == T(one) : Nat}:
  Equal.trans(Nat, Nat.add(FS.value(cp), 1n+mm), Nat.add(valo(one, cp), 1n+mm), T(one), M.cong_l(FS.value(cp), valo(one, cp), 1n+mm, Equal.sym(Nat, valo(one, cp), FS.value(cp), valo_value(one, h1, cp))), hv)

def mz(+one: Nat, +h1: {one == 1n : Nat}, +mm: Nat, +x: List<&2, U32>, +cp: List<&2, U32>, +hx: {LM.okb(32n, x, 255n) == True{} : Bool}, +hk: {LM.okb(32n, cp, 255n) == True{} : Bool}, +hv: {Nat.add(valo(one, cp), 1n+mm) == T(one) : Nat}, +hc: {Nat.is_lt(scalar_v(LM.cc(F.carry(F.addl(x, cp), 0))), one) == True{} : Bool}) -> {Nat.is_lt(FS.value(x), 1n+mm) == True{} : Bool}:
  +r = F.carry(F.addl(x, cp), 0)
  +c = scalar_v(LM.cc(r))
  +vs = FS.value(LM.cl(r))
  +VC = FS.value(cp)
  +c0 = U.lt_one_zero(c, L.subst(Nat, o => {Nat.is_lt(c, o) == True{} : Bool}, one, 1n, h1, hc))
  +ev = L.subst(Nat, z => {Nat.add(vs, LM.shn(32n, z)) == Nat.add(FS.value(x), VC) : Nat}, c, 0n, c0, cvx(one, h1, mm, x, cp, hx, hk))
  +ev1 = Equal.trans(Nat, vs, Nat.add(vs, 0n), Nat.add(FS.value(x), VC), Equal.sym(Nat, Nat.add(vs, 0n), vs, N.add_zero(vs)), ev)
  +lt = val_lt(one, h1, 32n, LM.cl(r), cr_okb(one, h1, F.addl(x, cp), ad_okb(one, h1, x, cp, hx, hk)))
  +lt2 = L.subst(Nat, z => {Nat.is_lt(vs, z) == True{} : Bool}, T(one), Nat.add(VC, 1n+mm), Equal.sym(Nat, Nat.add(VC, 1n+mm), T(one), cp_val(one, h1, mm, cp, hv)), lt)
  +lt3 = L.subst(Nat, z => {Nat.is_lt(z, Nat.add(VC, 1n+mm)) == True{} : Bool}, vs, Nat.add(FS.value(x), VC), ev1, lt2)
  +lt4 = L.subst(Nat, z => {Nat.is_lt(Nat.add(FS.value(x), VC), z) == True{} : Bool}, Nat.add(VC, 1n+mm), Nat.add(1n+mm, VC), NA.add_comm(VC, 1n+mm), lt3)
  lt_cancel_r(FS.value(x), 1n+mm, VC, lt4)

def mo_c(+one: Nat, +h1: {one == 1n : Nat}, +mm: Nat, +x: List<&2, U32>, +cp: List<&2, U32>, +hx: {LM.okb(32n, x, 255n) == True{} : Bool}, +hk: {LM.okb(32n, cp, 255n) == True{} : Bool}, +hv: {Nat.add(valo(one, cp), 1n+mm) == T(one) : Nat}, +hc: {Nat.is_lt(scalar_v(LM.cc(F.carry(F.addl(x, cp), 0))), one) == False{} : Bool}) -> {scalar_v(LM.cc(F.carry(F.addl(x, cp), 0))) == one : Nat}:
  +r = F.carry(F.addl(x, cp), 0)
  +c = scalar_v(LM.cc(r))
  +vs = FS.value(LM.cl(r))
  +VC = FS.value(cp)
  +TT = T(one)
  +ev = cvx(one, h1, mm, x, cp, hx, hk)
  +a = N.le_trans(LM.shn(32n, c), Nat.add(vs, LM.shn(32n, c)), Nat.add(FS.value(x), VC), le_add_l(vs, LM.shn(32n, c)), N.eq_le(Nat.add(vs, LM.shn(32n, c)), Nat.add(FS.value(x), VC), ev))
  +vct = L.subst(Nat, z => {Nat.is_le(VC, z) == True{} : Bool}, Nat.add(VC, 1n+mm), TT, cp_val(one, h1, mm, cp, hv), N.le_add_right(VC, 1n+mm))
  +b = N.lt_le_trans(Nat.add(FS.value(x), VC), Nat.add(TT, VC), Nat.add(TT, TT), N.lt_add_r2(FS.value(x), TT, VC, val_lt(one, h1, 32n, x, hx)), N.le_add_left(VC, TT, TT, vct))
  +d = N.le_lt_trans(LM.shn(32n, c), Nat.add(FS.value(x), VC), Nat.add(TT, TT), a, b)
  +d2 = L.subst(Nat, z => {Nat.is_lt(LM.shn(32n, c), z) == True{} : Bool}, Nat.add(TT, TT), LM.shn(32n, Nat.add(one, one)), M.sc_add(256n, one, one), d)
  +c2 = shn_lt_cancel(c, Nat.add(one, one), d2)
  +c2b = L.subst(Nat, o => {Nat.is_lt(c, Nat.add(o, o)) == True{} : Bool}, one, 1n, h1, c2)
  +cle = L.subst(Nat, o => {Nat.is_le(c, o) == True{} : Bool}, 1n, one, Equal.sym(Nat, one, 1n, h1), N.lt_succ_le(c, 1n, c2b))
  N.le_antisym(c, one, cle, N.not_lt_le(c, one, hc))

def mo(+one: Nat, +h1: {one == 1n : Nat}, +mm: Nat, +x: List<&2, U32>, +cp: List<&2, U32>, +hx: {LM.okb(32n, x, 255n) == True{} : Bool}, +hk: {LM.okb(32n, cp, 255n) == True{} : Bool}, +hv: {Nat.add(valo(one, cp), 1n+mm) == T(one) : Nat}, +hc: {Nat.is_lt(scalar_v(LM.cc(F.carry(F.addl(x, cp), 0))), one) == False{} : Bool}) -> {Nat.add(FS.value(LM.cl(F.carry(F.addl(x, cp), 0))), 1n+mm) == FS.value(x) : Nat}:
  +r = F.carry(F.addl(x, cp), 0)
  +c = scalar_v(LM.cc(r))
  +vs = FS.value(LM.cl(r))
  +VC = FS.value(cp)
  +ev = L.subst(Nat, z => {Nat.add(vs, LM.shn(32n, z)) == Nat.add(FS.value(x), VC) : Nat}, c, one, mo_c(one, h1, mm, x, cp, hx, hk, hv, hc), cvx(one, h1, mm, x, cp, hx, hk))
  +ev2 = L.subst(Nat, z => {Nat.add(vs, z) == Nat.add(FS.value(x), VC) : Nat}, T(one), Nat.add(VC, 1n+mm), Equal.sym(Nat, Nat.add(VC, 1n+mm), T(one), cp_val(one, h1, mm, cp, hv)), ev)
  +ev3 = Equal.trans(Nat, Nat.add(Nat.add(vs, 1n+mm), VC), Nat.add(vs, Nat.add(VC, 1n+mm)), Nat.add(FS.value(x), VC), Equal.trans(Nat, Nat.add(Nat.add(vs, 1n+mm), VC), Nat.add(vs, Nat.add(1n+mm, VC)), Nat.add(vs, Nat.add(VC, 1n+mm)), NA.add_assoc(vs, 1n+mm, VC), M.cong_r(vs, Nat.add(1n+mm, VC), Nat.add(VC, 1n+mm), NA.add_comm(1n+mm, VC))), ev2)
  G.cancel_r(Nat.add(vs, 1n+mm), FS.value(x), VC, ev3)

def lt_by(+one: Nat, +h1: {one == 1n : Nat}, +mm: Nat, +x: List<&2, U32>, +cp: List<&2, U32>, +hx: {LM.okb(32n, x, 255n) == True{} : Bool}, +hk: {LM.okb(32n, cp, 255n) == True{} : Bool}, +hv: {Nat.add(valo(one, cp), 1n+mm) == T(one) : Nat}, +b: Bool, +hb: {Nat.is_lt(scalar_v(LM.cc(F.carry(F.addl(x, cp), 0))), one) == b : Bool}) -> {U32.is_eq(LM.cc(F.carry(F.addl(x, cp), 0)), 0) == Nat.is_lt(FS.value(x), 1n+mm) : Bool}:
  match b:
    case True{}:
      +r = F.carry(F.addl(x, cp), 0)
      +c0 = U.lt_one_zero(scalar_v(LM.cc(r)), L.subst(Nat, o => {Nat.is_lt(scalar_v(LM.cc(r)), o) == True{} : Bool}, one, 1n, h1, hb))
      +cz = U.injective(LM.cc(r), 0, c0)
      %Equal.sym(U32, LM.cc(r), 0, cz) : {U32.is_eq(_, 0) == Nat.is_lt(FS.value(x), 1n+mm) : Bool}
      Equal.sym(Bool, Nat.is_lt(FS.value(x), 1n+mm), True{}, mz(one, h1, mm, x, cp, hx, hk, hv, hb))
    case False{}:
      +r = F.carry(F.addl(x, cp), 0)
      +co = U.injective(LM.cc(r), 1, Equal.trans(Nat, scalar_v(LM.cc(r)), one, 1n, mo_c(one, h1, mm, x, cp, hx, hk, hv, hb), h1))
      %Equal.sym(U32, LM.cc(r), 1, co) : {U32.is_eq(_, 0) == Nat.is_lt(FS.value(x), 1n+mm) : Bool}
      +e1 = mo(one, h1, mm, x, cp, hx, hk, hv, hb)
      +ge = L.subst(Nat, z => {Nat.is_le(1n+mm, z) == True{} : Bool}, Nat.add(FS.value(LM.cl(r)), 1n+mm), FS.value(x), e1, le_add_l(FS.value(LM.cl(r)), 1n+mm))
      Equal.sym(Bool, Nat.is_lt(FS.value(x), 1n+mm), False{}, N.le_not_lt(FS.value(x), 1n+mm, ge))
