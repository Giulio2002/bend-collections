import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/crypto/curve25519/field.bend as FS
import ../../../src/crypto/curve25519/field.bend as F
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/word.bend as WD
import ../../lib/arith.bend as AR
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ./num.bend as M
import ./limbs.bend as LM

# The limb-list polynomial operations of src/crypto/curve25519/field.bend:
# addl (limbwise sum), scal (times a limb), conv (the schoolbook product),
# take/drop (the split at 2^256) and wide (the fold of the product's high
# half). Each keeps its value exactly (Nat, no wrap) under limb bounds whose
# sums and products stay below 2^32.

def v(+x: U32) -> Nat:
  U32.to_nat(x)

# ---- lengths ----

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

def len_ge(n: Nat, xs: List<&2, U32>) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+m:
      match xs:
        case Nil{}:
          False{}
        case Con{x, xt}:
          len_ge(m, xt)

def len_le_nil(+n: Nat) -> {len_le(n, Nil{}) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      {==}

def len_le_mono(+k: Nat, +d: Nat, +xs: List<&2, U32>, +e: {len_le(k, xs) == True{} : Bool}) -> {len_le(Nat.add(k, d), xs) == True{} : Bool}:
  match k xs:
    case 0n Nil{}:
      len_le_nil(d)
    case 0n Con{y, yt}:
      Empty.absurd({len_le(d, Con{y, yt}) == True{} : Bool}, L.false_true(e))
    case 1n+m Nil{}:
      {==}
    case 1n+ +m Con{y, +yt}:
      len_le_mono(m, d, yt, e)

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

def okb_len_ge(+n: Nat, +xs: List<&2, U32>, +b: Nat, +e: {LM.okb(n, xs, b) == True{} : Bool}) -> {len_ge(n, xs) == True{} : Bool}:
  match n xs:
    case 0n Nil{}:
      {==}
    case 0n Con{y, yt}:
      {==}
    case 1n+m Nil{}:
      Empty.absurd({len_ge(1n+m, Nil{}) == True{} : Bool}, L.false_true(e))
    case 1n+ +m Con{+y, +yt}:
      okb_len_ge(m, yt, b, LM.okb_tail(m, y, yt, b, e))

def okb_mono(+n: Nat, +xs: List<&2, U32>, +b: Nat, +c: Nat, +hb: {Nat.is_le(b, c) == True{} : Bool}, +e: {LM.okb(n, xs, b) == True{} : Bool}) -> {LM.okb(n, xs, c) == True{} : Bool}:
  match n xs:
    case 0n Nil{}:
      {==}
    case 0n Con{y, yt}:
      Empty.absurd({LM.okb(0n, Con{y, yt}, c) == True{} : Bool}, L.false_true(e))
    case 1n+m Nil{}:
      Empty.absurd({LM.okb(1n+m, Nil{}, c) == True{} : Bool}, L.false_true(e))
    case 1n+ +m Con{+y, +yt}:
      L.and_intro(Nat.is_le(v(y), c), LM.okb(m, yt, c), N.le_trans(v(y), b, c, LM.okb_head(m, y, yt, b, e), hb), okb_mono(m, yt, b, c, hb, LM.okb_tail(m, y, yt, b, e)))

def le_add_l(+a: Nat, +b: Nat) -> {Nat.is_le(b, Nat.add(a, b)) == True{} : Bool}:
  %NA.add_comm(b, a) : {Nat.is_le(b, _) == True{} : Bool}
  N.le_add_right(b, a)

# ---- addl ----

def addl_v(+one: Nat, +h1: {one == 1n : Nat}, +x: U32, +y: U32, +a: Nat, +b: Nat, +hx: {Nat.is_le(v(x), a) == True{} : Bool}, +hy: {Nat.is_le(v(y), b) == True{} : Bool}, +hab: {Nat.is_lt(Nat.add(a, b), WD.sc(32n, one)) == True{} : Bool}) -> {v(U32.add(x, y)) == Nat.add(v(x), v(y)) : Nat}:
  LM.add_v(one, h1, x, y, N.le_lt_trans(Nat.add(v(x), v(y)), Nat.add(a, b), WD.sc(32n, one), M.le_add2(v(x), v(y), a, b, hx, hy), hab))

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
      +e1 = M.cong_add(v(U32.add(x, y)), Nat.add(v(x), v(y)), C.shift(8n, FS.value(F.addl(xt, yt))), C.shift(8n, Nat.add(X, Y)), ev, M.cong_sc(8n, FS.value(F.addl(xt, yt)), Nat.add(X, Y), ih))
      +e2 = M.cong_r(Nat.add(v(x), v(y)), C.shift(8n, Nat.add(X, Y)), Nat.add(C.shift(8n, X), C.shift(8n, Y)), Equal.sym(Nat, Nat.add(C.shift(8n, X), C.shift(8n, Y)), C.shift(8n, Nat.add(X, Y)), M.sc_add(8n, X, Y)))
      Equal.trans(Nat, Nat.add(v(U32.add(x, y)), C.shift(8n, FS.value(F.addl(xt, yt)))), Nat.add(Nat.add(v(x), v(y)), C.shift(8n, Nat.add(X, Y))), Nat.add(Nat.add(v(x), C.shift(8n, X)), Nat.add(v(y), C.shift(8n, Y))), e1,
        Equal.trans(Nat, Nat.add(Nat.add(v(x), v(y)), C.shift(8n, Nat.add(X, Y))), Nat.add(Nat.add(v(x), v(y)), Nat.add(C.shift(8n, X), C.shift(8n, Y))), Nat.add(Nat.add(v(x), C.shift(8n, X)), Nat.add(v(y), C.shift(8n, Y))), e2, M.add4(v(x), v(y), C.shift(8n, X), C.shift(8n, Y))))

def addl_lea(+one: Nat, +h1: {one == 1n : Nat}, +xs: List<&2, U32>, +ys: List<&2, U32>, +a: Nat, +b: Nat, +hx: {LM.lea(xs, a) == True{} : Bool}, +hy: {LM.lea(ys, b) == True{} : Bool}, +hab: {Nat.is_lt(Nat.add(a, b), WD.sc(32n, one)) == True{} : Bool}) -> {LM.lea(F.addl(xs, ys), Nat.add(a, b)) == True{} : Bool}:
  match xs ys:
    case Nil{} _:
      LM.lea_mono(ys, b, Nat.add(a, b), le_add_l(a, b), hy)
    case Con{+x, +xt} Nil{}:
      LM.lea_mono(Con{x, xt}, a, Nat.add(a, b), N.le_add_right(a, b), hx)
    case Con{+x, +xt} Con{+y, +yt}:
      +ev = addl_v(one, h1, x, y, a, b, LM.lea_head(x, xt, a, hx), LM.lea_head(y, yt, b, hy), hab)
      +hd = L.subst(Nat, z => {Nat.is_le(z, Nat.add(a, b)) == True{} : Bool}, Nat.add(v(x), v(y)), v(U32.add(x, y)), Equal.sym(Nat, v(U32.add(x, y)), Nat.add(v(x), v(y)), ev), M.le_add2(v(x), v(y), a, b, LM.lea_head(x, xt, a, hx), LM.lea_head(y, yt, b, hy)))
      L.and_intro(Nat.is_le(v(U32.add(x, y)), Nat.add(a, b)), LM.lea(F.addl(xt, yt), Nat.add(a, b)), hd, addl_lea(one, h1, xt, yt, a, b, LM.lea_tail(x, xt, a, hx), LM.lea_tail(y, yt, b, hy), hab))

# n limbs and at most n limbs give n limbs
def addl_okb(+one: Nat, +h1: {one == 1n : Nat}, +n: Nat, +xs: List<&2, U32>, +ys: List<&2, U32>, +a: Nat, +b: Nat, +hx: {LM.okb(n, xs, a) == True{} : Bool}, +hy: {LM.lea(ys, b) == True{} : Bool}, +hl: {len_le(n, ys) == True{} : Bool}, +hab: {Nat.is_lt(Nat.add(a, b), WD.sc(32n, one)) == True{} : Bool}) -> {LM.okb(n, F.addl(xs, ys), Nat.add(a, b)) == True{} : Bool}:
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
      +hd = L.subst(Nat, z => {Nat.is_le(z, Nat.add(a, b)) == True{} : Bool}, Nat.add(v(x), v(y)), v(U32.add(x, y)), Equal.sym(Nat, v(U32.add(x, y)), Nat.add(v(x), v(y)), ev), M.le_add2(v(x), v(y), a, b, hxh, hyh))
      L.and_intro(Nat.is_le(v(U32.add(x, y)), Nat.add(a, b)), LM.okb(m, F.addl(xt, yt), Nat.add(a, b)), hd, addl_okb(one, h1, m, xt, yt, a, b, LM.okb_tail(m, x, xt, a, hx), LM.lea_tail(y, yt, b, hy), hl, hab))

def addl_len_ge(+n: Nat, +xs: List<&2, U32>, +ys: List<&2, U32>, +e: {len_ge(n, xs) == True{} : Bool}) -> {len_ge(n, F.addl(xs, ys)) == True{} : Bool}:
  match n xs ys:
    case 0n _ _:
      {==}
    case 1n+m Nil{} _:
      Empty.absurd({len_ge(1n+m, ys) == True{} : Bool}, L.false_true(e))
    case 1n+m Con{x, xt} Nil{}:
      e
    case 1n+ +m Con{x, +xt} Con{y, +yt}:
      addl_len_ge(m, xt, yt, e)

def addl_len_le(+n: Nat, +xs: List<&2, U32>, +ys: List<&2, U32>, +ex: {len_le(n, xs) == True{} : Bool}, +ey: {len_le(n, ys) == True{} : Bool}) -> {len_le(n, F.addl(xs, ys)) == True{} : Bool}:
  match n xs ys:
    case 0n Nil{} _:
      ey
    case 0n Con{x, xt} _:
      Empty.absurd({len_le(0n, F.addl(Con{x, xt}, ys)) == True{} : Bool}, L.false_true(ex))
    case 1n+m Nil{} _:
      ey
    case 1n+m Con{x, xt} Nil{}:
      ex
    case 1n+ +m Con{x, +xt} Con{y, +yt}:
      addl_len_le(m, xt, yt, ex, ey)

# ---- scal ----

def sc_mul_l(+k: Nat, +a: Nat, +x: Nat) -> {WD.sc(k, Nat.mul(a, x)) == Nat.mul(a, WD.sc(k, x)) : Nat}:
  +e1 = M.cong_sc(k, Nat.mul(a, x), Nat.mul(x, a), NA.mul_comm(a, x))
  +e2 = AR.sc_mul(k, x, a)
  +e3 = NA.mul_comm(WD.sc(k, x), a)
  Equal.trans(Nat, WD.sc(k, Nat.mul(a, x)), WD.sc(k, Nat.mul(x, a)), Nat.mul(a, WD.sc(k, x)), e1, Equal.trans(Nat, WD.sc(k, Nat.mul(x, a)), Nat.mul(WD.sc(k, x), a), Nat.mul(a, WD.sc(k, x)), e2, e3))

def scal_v(+one: Nat, +h1: {one == 1n : Nat}, +x: U32, +y: U32, +a: Nat, +b: Nat, +hx: {Nat.is_le(v(x), a) == True{} : Bool}, +hy: {Nat.is_le(v(y), b) == True{} : Bool}, +hab: {Nat.is_lt(Nat.mul(a, b), WD.sc(32n, one)) == True{} : Bool}) -> {v(U32.mul(x, y)) == Nat.mul(v(x), v(y)) : Nat}:
  LM.mul_v(one, h1, x, y, N.le_lt_trans(Nat.mul(v(x), v(y)), Nat.mul(a, b), WD.sc(32n, one), M.le_mul2(v(x), v(y), a, b, hx, hy), hab))

def scal_val(+one: Nat, +h1: {one == 1n : Nat}, +x: U32, +ys: List<&2, U32>, +a: Nat, +b: Nat, +hx: {Nat.is_le(v(x), a) == True{} : Bool}, +hy: {LM.lea(ys, b) == True{} : Bool}, +hab: {Nat.is_lt(Nat.mul(a, b), WD.sc(32n, one)) == True{} : Bool}) -> {FS.value(F.scal(x, ys)) == Nat.mul(v(x), FS.value(ys)) : Nat}:
  match ys:
    case Nil{}:
      Equal.sym(Nat, Nat.mul(v(x), 0n), 0n, NA.mul_zero(v(x)))
    case Con{+y, +yt}:
      +ev = scal_v(one, h1, x, y, a, b, hx, LM.lea_head(y, yt, b, hy), hab)
      +ih = scal_val(one, h1, x, yt, a, b, hx, LM.lea_tail(y, yt, b, hy), hab)
      +Y = FS.value(yt)
      +e1 = M.cong_add(v(U32.mul(x, y)), Nat.mul(v(x), v(y)), C.shift(8n, FS.value(F.scal(x, yt))), C.shift(8n, Nat.mul(v(x), Y)), ev, M.cong_sc(8n, FS.value(F.scal(x, yt)), Nat.mul(v(x), Y), ih))
      +e2 = M.cong_r(Nat.mul(v(x), v(y)), C.shift(8n, Nat.mul(v(x), Y)), Nat.mul(v(x), C.shift(8n, Y)), sc_mul_l(8n, v(x), Y))
      +e3 = Equal.sym(Nat, Nat.mul(v(x), Nat.add(v(y), C.shift(8n, Y))), Nat.add(Nat.mul(v(x), v(y)), Nat.mul(v(x), C.shift(8n, Y))), NA.mul_add_left(v(x), v(y), C.shift(8n, Y)))
      Equal.trans(Nat, Nat.add(v(U32.mul(x, y)), C.shift(8n, FS.value(F.scal(x, yt)))), Nat.add(Nat.mul(v(x), v(y)), C.shift(8n, Nat.mul(v(x), Y))), Nat.mul(v(x), Nat.add(v(y), C.shift(8n, Y))), e1,
        Equal.trans(Nat, Nat.add(Nat.mul(v(x), v(y)), C.shift(8n, Nat.mul(v(x), Y))), Nat.add(Nat.mul(v(x), v(y)), Nat.mul(v(x), C.shift(8n, Y))), Nat.mul(v(x), Nat.add(v(y), C.shift(8n, Y))), e2, e3))

def scal_lea(+one: Nat, +h1: {one == 1n : Nat}, +x: U32, +ys: List<&2, U32>, +a: Nat, +b: Nat, +hx: {Nat.is_le(v(x), a) == True{} : Bool}, +hy: {LM.lea(ys, b) == True{} : Bool}, +hab: {Nat.is_lt(Nat.mul(a, b), WD.sc(32n, one)) == True{} : Bool}) -> {LM.lea(F.scal(x, ys), Nat.mul(a, b)) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +yt}:
      +hyh = LM.lea_head(y, yt, b, hy)
      +ev = scal_v(one, h1, x, y, a, b, hx, hyh, hab)
      +hd = L.subst(Nat, z => {Nat.is_le(z, Nat.mul(a, b)) == True{} : Bool}, Nat.mul(v(x), v(y)), v(U32.mul(x, y)), Equal.sym(Nat, v(U32.mul(x, y)), Nat.mul(v(x), v(y)), ev), M.le_mul2(v(x), v(y), a, b, hx, hyh))
      L.and_intro(Nat.is_le(v(U32.mul(x, y)), Nat.mul(a, b)), LM.lea(F.scal(x, yt), Nat.mul(a, b)), hd, scal_lea(one, h1, x, yt, a, b, hx, LM.lea_tail(y, yt, b, hy), hab))

def scal_okb(+one: Nat, +h1: {one == 1n : Nat}, +n: Nat, +x: U32, +ys: List<&2, U32>, +a: Nat, +b: Nat, +hx: {Nat.is_le(v(x), a) == True{} : Bool}, +hy: {LM.okb(n, ys, b) == True{} : Bool}, +hab: {Nat.is_lt(Nat.mul(a, b), WD.sc(32n, one)) == True{} : Bool}) -> {LM.okb(n, F.scal(x, ys), Nat.mul(a, b)) == True{} : Bool}:
  match n ys:
    case 0n Nil{}:
      {==}
    case 0n Con{y, yt}:
      Empty.absurd({LM.okb(0n, F.scal(x, Con{y, yt}), Nat.mul(a, b)) == True{} : Bool}, L.false_true(hy))
    case 1n+m Nil{}:
      Empty.absurd({LM.okb(1n+m, Nil{}, Nat.mul(a, b)) == True{} : Bool}, L.false_true(hy))
    case 1n+ +m Con{+y, +yt}:
      +hyh = LM.okb_head(m, y, yt, b, hy)
      +ev = scal_v(one, h1, x, y, a, b, hx, hyh, hab)
      +hd = L.subst(Nat, z => {Nat.is_le(z, Nat.mul(a, b)) == True{} : Bool}, Nat.mul(v(x), v(y)), v(U32.mul(x, y)), Equal.sym(Nat, v(U32.mul(x, y)), Nat.mul(v(x), v(y)), ev), M.le_mul2(v(x), v(y), a, b, hx, hyh))
      L.and_intro(Nat.is_le(v(U32.mul(x, y)), Nat.mul(a, b)), LM.okb(m, F.scal(x, yt), Nat.mul(a, b)), hd, scal_okb(one, h1, m, x, yt, a, b, hx, LM.okb_tail(m, y, yt, b, hy), hab))

def scal_len_ge(+n: Nat, +x: U32, +ys: List<&2, U32>, +e: {len_ge(n, ys) == True{} : Bool}) -> {len_ge(n, F.scal(x, ys)) == True{} : Bool}:
  match n ys:
    case 0n _:
      {==}
    case 1n+m Nil{}:
      Empty.absurd({len_ge(1n+m, Nil{}) == True{} : Bool}, L.false_true(e))
    case 1n+ +m Con{y, +yt}:
      scal_len_ge(m, x, yt, e)

def scal_len_le(+n: Nat, +x: U32, +ys: List<&2, U32>, +e: {len_le(n, ys) == True{} : Bool}) -> {len_le(n, F.scal(x, ys)) == True{} : Bool}:
  match n ys:
    case 0n Nil{}:
      {==}
    case 0n Con{y, yt}:
      Empty.absurd({len_le(0n, F.scal(x, Con{y, yt})) == True{} : Bool}, L.false_true(e))
    case 1n+m Nil{}:
      {==}
    case 1n+ +m Con{y, +yt}:
      scal_len_le(m, x, yt, e)

# ---- conv ----

# len(xs) * k
def cb(xs: List<&2, U32>, +k: Nat) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{x, xt}:
      Nat.add(k, cb(xt, k))

def cbn(n: Nat, +k: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+m:
      Nat.add(k, cbn(m, k))

def conv_lea(+one: Nat, +h1: {one == 1n : Nat}, +xs: List<&2, U32>, +ys: List<&2, U32>, +a: Nat, +b: Nat, +hx: {LM.lea(xs, a) == True{} : Bool}, +hy: {LM.lea(ys, b) == True{} : Bool}, +hc: {Nat.is_lt(cb(xs, Nat.mul(a, b)), WD.sc(32n, one)) == True{} : Bool}) -> {LM.lea(F.conv(xs, ys), cb(xs, Nat.mul(a, b))) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +xt}:
      +ab = Nat.mul(a, b)
      +k = cb(xt, ab)
      +hab = N.le_lt_trans(ab, Nat.add(ab, k), WD.sc(32n, one), N.le_add_right(ab, k), hc)
      +hk = N.le_lt_trans(k, Nat.add(ab, k), WD.sc(32n, one), le_add_l(ab, k), hc)
      +hs = scal_lea(one, h1, x, ys, a, b, LM.lea_head(x, xt, a, hx), hy, hab)
      +hz = L.and_intro(Nat.is_le(0n, k), LM.lea(F.conv(xt, ys), k), N.zero_le(k), conv_lea(one, h1, xt, ys, a, b, LM.lea_tail(x, xt, a, hx), hy, hk))
      addl_lea(one, h1, F.scal(x, ys), Con{0, F.conv(xt, ys)}, ab, k, hs, hz, hc)

def conv_val(+one: Nat, +h1: {one == 1n : Nat}, +xs: List<&2, U32>, +ys: List<&2, U32>, +a: Nat, +b: Nat, +hx: {LM.lea(xs, a) == True{} : Bool}, +hy: {LM.lea(ys, b) == True{} : Bool}, +hc: {Nat.is_lt(cb(xs, Nat.mul(a, b)), WD.sc(32n, one)) == True{} : Bool}) -> {FS.value(F.conv(xs, ys)) == Nat.mul(FS.value(xs), FS.value(ys)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +xt}:
      +ab = Nat.mul(a, b)
      +k = cb(xt, ab)
      +Y = FS.value(ys)
      +X = FS.value(xt)
      +hab = N.le_lt_trans(ab, Nat.add(ab, k), WD.sc(32n, one), N.le_add_right(ab, k), hc)
      +hk = N.le_lt_trans(k, Nat.add(ab, k), WD.sc(32n, one), le_add_l(ab, k), hc)
      +hxh = LM.lea_head(x, xt, a, hx)
      +hxt = LM.lea_tail(x, xt, a, hx)
      +hs = scal_lea(one, h1, x, ys, a, b, hxh, hy, hab)
      +hz = L.and_intro(Nat.is_le(0n, k), LM.lea(F.conv(xt, ys), k), N.zero_le(k), conv_lea(one, h1, xt, ys, a, b, hxt, hy, hk))
      +e1 = addl_val(one, h1, F.scal(x, ys), Con{0, F.conv(xt, ys)}, ab, k, hs, hz, hc)
      +e2 = M.cong_add(FS.value(F.scal(x, ys)), Nat.mul(v(x), Y), FS.value(Con{0, F.conv(xt, ys)}), C.shift(8n, Nat.mul(X, Y)), scal_val(one, h1, x, ys, a, b, hxh, hy, hab), M.cong_sc(8n, FS.value(F.conv(xt, ys)), Nat.mul(X, Y), conv_val(one, h1, xt, ys, a, b, hxt, hy, hk)))
      +e3 = M.cong_r(Nat.mul(v(x), Y), C.shift(8n, Nat.mul(X, Y)), Nat.mul(C.shift(8n, X), Y), AR.sc_mul(8n, X, Y))
      +e4 = Equal.sym(Nat, Nat.mul(Nat.add(v(x), C.shift(8n, X)), Y), Nat.add(Nat.mul(v(x), Y), Nat.mul(C.shift(8n, X), Y)), NA.mul_add_right(v(x), C.shift(8n, X), Y))
      Equal.trans(Nat, FS.value(F.conv(Con{x, xt}, ys)), Nat.add(FS.value(F.scal(x, ys)), FS.value(Con{0, F.conv(xt, ys)})), Nat.mul(Nat.add(v(x), C.shift(8n, X)), Y), e1,
        Equal.trans(Nat, Nat.add(FS.value(F.scal(x, ys)), FS.value(Con{0, F.conv(xt, ys)})), Nat.add(Nat.mul(v(x), Y), C.shift(8n, Nat.mul(X, Y))), Nat.mul(Nat.add(v(x), C.shift(8n, X)), Y), e2,
          Equal.trans(Nat, Nat.add(Nat.mul(v(x), Y), C.shift(8n, Nat.mul(X, Y))), Nat.add(Nat.mul(v(x), Y), Nat.mul(C.shift(8n, X), Y)), Nat.mul(Nat.add(v(x), C.shift(8n, X)), Y), e3, e4)))

def conv_len_ge(+n: Nat, +x: U32, +xt: List<&2, U32>, +ys: List<&2, U32>, +e: {len_ge(n, ys) == True{} : Bool}) -> {len_ge(n, F.conv(Con{x, xt}, ys)) == True{} : Bool}:
  addl_len_ge(n, F.scal(x, ys), Con{0, F.conv(xt, ys)}, scal_len_ge(n, x, ys, e))

# len(conv(xs, ys)) <= j + k when len(xs) <= j and len(ys) <= k
def conv_len_le(+j: Nat, +k: Nat, +xs: List<&2, U32>, +ys: List<&2, U32>, +ex: {len_le(j, xs) == True{} : Bool}, +ey: {len_le(k, ys) == True{} : Bool}) -> {len_le(Nat.add(j, k), F.conv(xs, ys)) == True{} : Bool}:
  match j xs:
    case 0n Nil{}:
      len_le_nil(k)
    case 0n Con{x, xt}:
      Empty.absurd({len_le(k, F.conv(Con{x, xt}, ys)) == True{} : Bool}, L.false_true(ex))
    case 1n+m Nil{}:
      {==}
    case 1n+ +m Con{+x, +xt}:
      +hs0 = len_le_mono(k, 1n+m, F.scal(x, ys), scal_len_le(k, x, ys, ey))
      +hs = L.subst(Nat, z => {len_le(z, F.scal(x, ys)) == True{} : Bool}, Nat.add(k, 1n+m), Nat.add(1n+m, k), NA.add_comm(k, 1n+m), hs0)
      +hz = conv_len_le(m, k, xt, ys, ex, ey)
      addl_len_le(Nat.add(1n+m, k), F.scal(x, ys), Con{0, F.conv(xt, ys)}, hs, hz)

# ---- take and drop ----

def take_drop_val(+n: Nat, +xs: List<&2, U32>) -> {FS.value(xs) == Nat.add(FS.value(F.take(n, xs)), LM.sh(F.take(n, xs), FS.value(F.drop(n, xs)))) : Nat}:
  match n xs:
    case 0n _:
      {==}
    case 1n+m Nil{}:
      {==}
    case 1n+ +m Con{+x, +xt}:
      +T = FS.value(F.take(m, xt))
      +D = LM.sh(F.take(m, xt), FS.value(F.drop(m, xt)))
      +ih = take_drop_val(m, xt)
      +e1 = M.cong_r(v(x), C.shift(8n, FS.value(xt)), C.shift(8n, Nat.add(T, D)), M.cong_sc(8n, FS.value(xt), Nat.add(T, D), ih))
      +e2 = M.cong_r(v(x), C.shift(8n, Nat.add(T, D)), Nat.add(C.shift(8n, T), C.shift(8n, D)), Equal.sym(Nat, Nat.add(C.shift(8n, T), C.shift(8n, D)), C.shift(8n, Nat.add(T, D)), M.sc_add(8n, T, D)))
      +e3 = Equal.sym(Nat, Nat.add(Nat.add(v(x), C.shift(8n, T)), C.shift(8n, D)), Nat.add(v(x), Nat.add(C.shift(8n, T), C.shift(8n, D))), NA.add_assoc(v(x), C.shift(8n, T), C.shift(8n, D)))
      Equal.trans(Nat, Nat.add(v(x), C.shift(8n, FS.value(xt))), Nat.add(v(x), C.shift(8n, Nat.add(T, D))), Nat.add(Nat.add(v(x), C.shift(8n, T)), C.shift(8n, D)), e1,
        Equal.trans(Nat, Nat.add(v(x), C.shift(8n, Nat.add(T, D))), Nat.add(v(x), Nat.add(C.shift(8n, T), C.shift(8n, D))), Nat.add(Nat.add(v(x), C.shift(8n, T)), C.shift(8n, D)), e2, e3))

def take_okb(+n: Nat, +xs: List<&2, U32>, +b: Nat, +hl: {len_ge(n, xs) == True{} : Bool}, +hx: {LM.lea(xs, b) == True{} : Bool}) -> {LM.okb(n, F.take(n, xs), b) == True{} : Bool}:
  match n xs:
    case 0n _:
      {==}
    case 1n+m Nil{}:
      Empty.absurd({LM.okb(1n+m, Nil{}, b) == True{} : Bool}, L.false_true(hl))
    case 1n+ +m Con{+x, +xt}:
      L.and_intro(Nat.is_le(v(x), b), LM.okb(m, F.take(m, xt), b), LM.lea_head(x, xt, b, hx), take_okb(m, xt, b, hl, LM.lea_tail(x, xt, b, hx)))

def drop_lea(+n: Nat, +xs: List<&2, U32>, +b: Nat, +hx: {LM.lea(xs, b) == True{} : Bool}) -> {LM.lea(F.drop(n, xs), b) == True{} : Bool}:
  match n xs:
    case 0n _:
      hx
    case 1n+m Nil{}:
      {==}
    case 1n+ +m Con{+x, +xt}:
      drop_lea(m, xt, b, LM.lea_tail(x, xt, b, hx))

def drop_len_le(+n: Nat, +k: Nat, +xs: List<&2, U32>, +hl: {len_le(Nat.add(n, k), xs) == True{} : Bool}) -> {len_le(k, F.drop(n, xs)) == True{} : Bool}:
  match n xs:
    case 0n _:
      hl
    case 1n+m Nil{}:
      len_le_nil(k)
    case 1n+ +m Con{x, +xt}:
      drop_len_le(m, k, xt, hl)
