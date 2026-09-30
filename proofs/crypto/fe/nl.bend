import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/crypto/curve25519/fe.bend as FV
import ../../../src/crypto/curve25519/limbs.bend as LS
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/word.bend as WD
import ../../lib/arith.bend as AR
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../curve25519/num.bend as M

# Nat limb lists in radix 2^17 (FV.lv): the value of the polynomial
# operations of src/crypto/curve25519/limbs.bend (addl, scal, scal_r, conv,
# take/drop: exact, the limbs being Nat), and entry bounds (FV.below).

# ---- small algebra ----

# 2^k (a x) == a 2^k x
def sc_mul_l(+k: Nat, +a: Nat, +x: Nat) -> {WD.sc(k, Nat.mul(a, x)) == Nat.mul(a, WD.sc(k, x)) : Nat}:
  +e1 = M.cong_sc(k, Nat.mul(a, x), Nat.mul(x, a), NA.mul_comm(a, x))
  +e2 = AR.sc_mul(k, x, a)
  +e3 = NA.mul_comm(WD.sc(k, x), a)
  Equal.trans(Nat, WD.sc(k, Nat.mul(a, x)), WD.sc(k, Nat.mul(x, a)), Nat.mul(a, WD.sc(k, x)), e1, Equal.trans(Nat, WD.sc(k, Nat.mul(x, a)), Nat.mul(WD.sc(k, x), a), Nat.mul(a, WD.sc(k, x)), e2, e3))

def tr(+a: Nat, +b: Nat, +c: Nat, +e1: {a == b : Nat}, +e2: {b == c : Nat}) -> {a == c : Nat}:
  Equal.trans(Nat, a, b, c, e1, e2)

def sy(+a: Nat, +b: Nat, +e: {a == b : Nat}) -> {b == a : Nat}:
  Equal.sym(Nat, a, b, e)

# ---- value ----

def lv_addl(+xs: List<&2, Nat>, +ys: List<&2, Nat>) -> {FV.lv(LS.addl(xs, ys)) == Nat.add(FV.lv(xs), FV.lv(ys)) : Nat}:
  match xs ys:
    case Nil{} _:
      {==}
    case Con{+x, +xt} Nil{}:
      sy(Nat.add(FV.lv(Con{x, xt}), 0n), FV.lv(Con{x, xt}), N.add_zero(FV.lv(Con{x, xt})))
    case Con{+x, +xt} Con{+y, +yt}:
      +X = FV.lv(xt)
      +Y = FV.lv(yt)
      +Z = FV.lv(LS.addl(xt, yt))
      +e1 = M.cong_r(Nat.add(x, y), C.shift(17n, Z), C.shift(17n, Nat.add(X, Y)), M.cong_sc(17n, Z, Nat.add(X, Y), lv_addl(xt, yt)))
      +e2 = M.cong_r(Nat.add(x, y), C.shift(17n, Nat.add(X, Y)), Nat.add(C.shift(17n, X), C.shift(17n, Y)), sy(Nat.add(C.shift(17n, X), C.shift(17n, Y)), C.shift(17n, Nat.add(X, Y)), M.sc_add(17n, X, Y)))
      tr(Nat.add(Nat.add(x, y), C.shift(17n, Z)), Nat.add(Nat.add(x, y), C.shift(17n, Nat.add(X, Y))), Nat.add(Nat.add(x, C.shift(17n, X)), Nat.add(y, C.shift(17n, Y))), e1,
        tr(Nat.add(Nat.add(x, y), C.shift(17n, Nat.add(X, Y))), Nat.add(Nat.add(x, y), Nat.add(C.shift(17n, X), C.shift(17n, Y))), Nat.add(Nat.add(x, C.shift(17n, X)), Nat.add(y, C.shift(17n, Y))), e2, M.add4(x, y, C.shift(17n, X), C.shift(17n, Y))))

def lv_scal(+a: Nat, +ys: List<&2, Nat>) -> {FV.lv(LS.scal(a, ys)) == Nat.mul(a, FV.lv(ys)) : Nat}:
  match ys:
    case Nil{}:
      sy(Nat.mul(a, 0n), 0n, NA.mul_zero(a))
    case Con{+y, +yt}:
      +Y = FV.lv(yt)
      +Z = FV.lv(LS.scal(a, yt))
      +e1 = M.cong_r(Nat.mul(a, y), C.shift(17n, Z), C.shift(17n, Nat.mul(a, Y)), M.cong_sc(17n, Z, Nat.mul(a, Y), lv_scal(a, yt)))
      +e2 = M.cong_r(Nat.mul(a, y), C.shift(17n, Nat.mul(a, Y)), Nat.mul(a, C.shift(17n, Y)), sc_mul_l(17n, a, Y))
      +e3 = sy(Nat.mul(a, Nat.add(y, C.shift(17n, Y))), Nat.add(Nat.mul(a, y), Nat.mul(a, C.shift(17n, Y))), NA.mul_add_left(a, y, C.shift(17n, Y)))
      tr(Nat.add(Nat.mul(a, y), C.shift(17n, Z)), Nat.add(Nat.mul(a, y), C.shift(17n, Nat.mul(a, Y))), Nat.mul(a, Nat.add(y, C.shift(17n, Y))), e1,
        tr(Nat.add(Nat.mul(a, y), C.shift(17n, Nat.mul(a, Y))), Nat.add(Nat.mul(a, y), Nat.mul(a, C.shift(17n, Y))), Nat.mul(a, Nat.add(y, C.shift(17n, Y))), e2, e3))

def lv_scal_r(+ys: List<&2, Nat>, +k: Nat) -> {FV.lv(LS.scal_r(ys, k)) == Nat.mul(FV.lv(ys), k) : Nat}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +yt}:
      +Y = FV.lv(yt)
      +Z = FV.lv(LS.scal_r(yt, k))
      +e1 = M.cong_r(Nat.mul(y, k), C.shift(17n, Z), C.shift(17n, Nat.mul(Y, k)), M.cong_sc(17n, Z, Nat.mul(Y, k), lv_scal_r(yt, k)))
      +e2 = M.cong_r(Nat.mul(y, k), C.shift(17n, Nat.mul(Y, k)), Nat.mul(C.shift(17n, Y), k), AR.sc_mul(17n, Y, k))
      +e3 = sy(Nat.mul(Nat.add(y, C.shift(17n, Y)), k), Nat.add(Nat.mul(y, k), Nat.mul(C.shift(17n, Y), k)), NA.mul_add_right(y, C.shift(17n, Y), k))
      tr(Nat.add(Nat.mul(y, k), C.shift(17n, Z)), Nat.add(Nat.mul(y, k), C.shift(17n, Nat.mul(Y, k))), Nat.mul(Nat.add(y, C.shift(17n, Y)), k), e1,
        tr(Nat.add(Nat.mul(y, k), C.shift(17n, Nat.mul(Y, k))), Nat.add(Nat.mul(y, k), Nat.mul(C.shift(17n, Y), k)), Nat.mul(Nat.add(y, C.shift(17n, Y)), k), e2, e3))

def lv_conv(+xs: List<&2, Nat>, +ys: List<&2, Nat>) -> {FV.lv(LS.conv(xs, ys)) == Nat.mul(FV.lv(xs), FV.lv(ys)) : Nat}:
  match xs ys:
    case Nil{} _:
      {==}
    case Con{+x, +xt} Nil{}:
      sy(Nat.mul(FV.lv(Con{x, xt}), 0n), 0n, NA.mul_zero(FV.lv(Con{x, xt})))
    case Con{+x, +xt} Con{+y, +yt}:
      +ys2 = {Con{y, yt} : List<&2, Nat>}
      +X = FV.lv(xt)
      +Y1 = FV.lv(yt)
      +Y = FV.lv(ys2)
      +A = LS.scal(x, yt)
      +B = LS.conv(xt, ys2)
      +e1 = M.cong_sc(17n, FV.lv(LS.addl(A, B)), Nat.add(Nat.mul(x, Y1), Nat.mul(X, Y)), tr(FV.lv(LS.addl(A, B)), Nat.add(FV.lv(A), FV.lv(B)), Nat.add(Nat.mul(x, Y1), Nat.mul(X, Y)), lv_addl(A, B), M.cong_add(FV.lv(A), Nat.mul(x, Y1), FV.lv(B), Nat.mul(X, Y), lv_scal(x, yt), lv_conv(xt, ys2))))
      +e2 = sy(Nat.add(C.shift(17n, Nat.mul(x, Y1)), C.shift(17n, Nat.mul(X, Y))), C.shift(17n, Nat.add(Nat.mul(x, Y1), Nat.mul(X, Y))), M.sc_add(17n, Nat.mul(x, Y1), Nat.mul(X, Y)))
      +e3 = M.cong_add(C.shift(17n, Nat.mul(x, Y1)), Nat.mul(x, C.shift(17n, Y1)), C.shift(17n, Nat.mul(X, Y)), Nat.mul(C.shift(17n, X), Y), sc_mul_l(17n, x, Y1), AR.sc_mul(17n, X, Y))
      +S1 = Nat.add(C.shift(17n, Nat.mul(x, Y1)), C.shift(17n, Nat.mul(X, Y)))
      +S2 = Nat.add(Nat.mul(x, C.shift(17n, Y1)), Nat.mul(C.shift(17n, X), Y))
      +e4 = sy(Nat.add(Nat.add(Nat.mul(x, y), Nat.mul(x, C.shift(17n, Y1))), Nat.mul(C.shift(17n, X), Y)), Nat.add(Nat.mul(x, y), S2), NA.add_assoc(Nat.mul(x, y), Nat.mul(x, C.shift(17n, Y1)), Nat.mul(C.shift(17n, X), Y)))
      +e5 = M.cong_l(Nat.add(Nat.mul(x, y), Nat.mul(x, C.shift(17n, Y1))), Nat.mul(x, Y), Nat.mul(C.shift(17n, X), Y), sy(Nat.mul(x, Y), Nat.add(Nat.mul(x, y), Nat.mul(x, C.shift(17n, Y1))), NA.mul_add_left(x, y, C.shift(17n, Y1))))
      +e6 = sy(Nat.mul(Nat.add(x, C.shift(17n, X)), Y), Nat.add(Nat.mul(x, Y), Nat.mul(C.shift(17n, X), Y)), NA.mul_add_right(x, C.shift(17n, X), Y))
      +H = Nat.mul(x, y)
      tr(Nat.add(H, C.shift(17n, FV.lv(LS.addl(A, B)))), Nat.add(H, C.shift(17n, Nat.add(Nat.mul(x, Y1), Nat.mul(X, Y)))), Nat.mul(Nat.add(x, C.shift(17n, X)), Y), M.cong_r(H, C.shift(17n, FV.lv(LS.addl(A, B))), C.shift(17n, Nat.add(Nat.mul(x, Y1), Nat.mul(X, Y))), e1),
        tr(Nat.add(H, C.shift(17n, Nat.add(Nat.mul(x, Y1), Nat.mul(X, Y)))), Nat.add(H, S1), Nat.mul(Nat.add(x, C.shift(17n, X)), Y), M.cong_r(H, C.shift(17n, Nat.add(Nat.mul(x, Y1), Nat.mul(X, Y))), S1, e2),
          tr(Nat.add(H, S1), Nat.add(H, S2), Nat.mul(Nat.add(x, C.shift(17n, X)), Y), M.cong_r(H, S1, S2, e3),
            tr(Nat.add(H, S2), Nat.add(Nat.add(H, Nat.mul(x, C.shift(17n, Y1))), Nat.mul(C.shift(17n, X), Y)), Nat.mul(Nat.add(x, C.shift(17n, X)), Y), e4,
              tr(Nat.add(Nat.add(H, Nat.mul(x, C.shift(17n, Y1))), Nat.mul(C.shift(17n, X), Y)), Nat.add(Nat.mul(x, Y), Nat.mul(C.shift(17n, X), Y)), Nat.mul(Nat.add(x, C.shift(17n, X)), Y), e5, e6)))))

# 2^(17 n) x
def sh(n: Nat, +x: Nat) -> Nat:
  match n:
    case 0n:
      x
    case 1n+m:
      C.shift(17n, sh(m, x))

# 17 n
def m17(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+m:
      Nat.add(17n, m17(m))

def sh_sc(+n: Nat, +x: Nat) -> {sh(n, x) == WD.sc(m17(n), x) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+ +m:
      tr(C.shift(17n, sh(m, x)), WD.sc(17n, WD.sc(m17(m), x)), WD.sc(Nat.add(17n, m17(m)), x), M.cong_sc(17n, sh(m, x), WD.sc(m17(m), x), sh_sc(m, x)), M.sc_sc(17n, m17(m), x))

def sh15(+x: Nat) -> {sh(15n, x) == WD.sc(255n, x) : Nat}:
  sh_sc(15n, x)

def sh_add(+n: Nat, +x: Nat, +y: Nat) -> {Nat.add(sh(n, x), sh(n, y)) == sh(n, Nat.add(x, y)) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+ +m:
      tr(Nat.add(C.shift(17n, sh(m, x)), C.shift(17n, sh(m, y))), C.shift(17n, Nat.add(sh(m, x), sh(m, y))), C.shift(17n, sh(m, Nat.add(x, y))), M.sc_add(17n, sh(m, x), sh(m, y)), M.cong_sc(17n, Nat.add(sh(m, x), sh(m, y)), sh(m, Nat.add(x, y)), sh_add(m, x, y)))

def sh_zero(+n: Nat) -> {sh(n, 0n) == 0n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+ +m:
      Equal.cong(Nat, Nat, t => C.shift(17n, t), sh(m, 0n), 0n, sh_zero(m))

# the split at limb n
def lv_split(+n: Nat, +xs: List<&2, Nat>) -> {FV.lv(xs) == Nat.add(FV.lv(LS.take(n, xs)), sh(n, FV.lv(LS.drop(n, xs)))) : Nat}:
  match n xs:
    case 0n _:
      {==}
    case 1n+ +m Nil{}:
      sy(sh(1n+m, 0n), 0n, sh_zero(1n+m))
    case 1n+ +m Con{+x, +xt}:
      +T = FV.lv(LS.take(m, xt))
      +D = sh(m, FV.lv(LS.drop(m, xt)))
      +e1 = M.cong_r(x, C.shift(17n, FV.lv(xt)), C.shift(17n, Nat.add(T, D)), M.cong_sc(17n, FV.lv(xt), Nat.add(T, D), lv_split(m, xt)))
      +e2 = M.cong_r(x, C.shift(17n, Nat.add(T, D)), Nat.add(C.shift(17n, T), C.shift(17n, D)), sy(Nat.add(C.shift(17n, T), C.shift(17n, D)), C.shift(17n, Nat.add(T, D)), M.sc_add(17n, T, D)))
      +e3 = sy(Nat.add(Nat.add(x, C.shift(17n, T)), C.shift(17n, D)), Nat.add(x, Nat.add(C.shift(17n, T), C.shift(17n, D))), NA.add_assoc(x, C.shift(17n, T), C.shift(17n, D)))
      tr(Nat.add(x, C.shift(17n, FV.lv(xt))), Nat.add(x, C.shift(17n, Nat.add(T, D))), Nat.add(Nat.add(x, C.shift(17n, T)), C.shift(17n, D)), e1,
        tr(Nat.add(x, C.shift(17n, Nat.add(T, D))), Nat.add(x, Nat.add(C.shift(17n, T), C.shift(17n, D))), Nat.add(Nat.add(x, C.shift(17n, T)), C.shift(17n, D)), e2, e3))

# ---- bounds ----

def below_head(+x: Nat, +xt: List<&2, Nat>, +b: Nat, +e: {FV.below(Con{x, xt}, b) == True{} : Bool}) -> {Nat.is_lt(x, b) == True{} : Bool}:
  L.and_left(Nat.is_lt(x, b), FV.below(xt, b), e)

def below_tail(+x: Nat, +xt: List<&2, Nat>, +b: Nat, +e: {FV.below(Con{x, xt}, b) == True{} : Bool}) -> {FV.below(xt, b) == True{} : Bool}:
  L.and_right(Nat.is_lt(x, b), FV.below(xt, b), e)

def below_con(+x: Nat, +xt: List<&2, Nat>, +b: Nat, +hx: {Nat.is_lt(x, b) == True{} : Bool}, +ht: {FV.below(xt, b) == True{} : Bool}) -> {FV.below(Con{x, xt}, b) == True{} : Bool}:
  L.and_intro(Nat.is_lt(x, b), FV.below(xt, b), hx, ht)

def below_mono(+xs: List<&2, Nat>, +a: Nat, +b: Nat, +h: {Nat.is_le(a, b) == True{} : Bool}, +e: {FV.below(xs, a) == True{} : Bool}) -> {FV.below(xs, b) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +xt}:
      below_con(x, xt, b, N.lt_le_trans(x, a, b, below_head(x, xt, a, e), h), below_mono(xt, a, b, h, below_tail(x, xt, a, e)))

def le_add_l(+a: Nat, +b: Nat) -> {Nat.is_le(b, Nat.add(a, b)) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_le(b, z) == True{} : Bool}, Nat.add(b, a), Nat.add(a, b), NA.add_comm(b, a), N.le_add_right(b, a))

# x < a, y < b -> x + y < a + b
def lt_add2(+x: Nat, +y: Nat, +a: Nat, +b: Nat, +hx: {Nat.is_lt(x, a) == True{} : Bool}, +hy: {Nat.is_lt(y, b) == True{} : Bool}) -> {Nat.is_lt(Nat.add(x, y), Nat.add(a, b)) == True{} : Bool}:
  N.lt_le_trans(Nat.add(x, y), Nat.add(x, b), Nat.add(a, b), N.lt_add_left(y, b, x, hy), M.le_add_r(x, a, b, N.lt_le(x, a, hx)))

# x < a, y < b -> x y < a b
def lt_mul2(+x: Nat, +y: Nat, +a: Nat, +b: Nat, +hx: {Nat.is_lt(x, a) == True{} : Bool}, +hy: {Nat.is_lt(y, b) == True{} : Bool}) -> {Nat.is_lt(Nat.mul(x, y), Nat.mul(a, b)) == True{} : Bool}:
  +h1 = M.le_mul2(x, y, x, b, N.le_refl(x), N.lt_le(y, b, hy))
  +bpos = N.le_lt_trans(0n, y, b, N.zero_le(y), hy)
  +h2 = M.le_mul2(Nat.add(x, 1n), b, a, b, L.subst(Nat, z => {Nat.is_le(z, a) == True{} : Bool}, 1n+x, Nat.add(x, 1n), Equal.trans(Nat, 1n+x, 1n+Nat.add(x, 0n), Nat.add(x, 1n), Equal.cong(Nat, Nat, t => 1n+t, x, Nat.add(x, 0n), sy(Nat.add(x, 0n), x, N.add_zero(x))), sy(Nat.add(x, 1n), 1n+Nat.add(x, 0n), N.add_succ(x, 0n))), N.lt_succ_le_succ(x, a, hx)), N.le_refl(b))
  +e = tr(Nat.mul(Nat.add(x, 1n), b), Nat.add(Nat.mul(x, b), Nat.mul(1n, b)), Nat.add(Nat.mul(x, b), b), NA.mul_add_right(x, 1n, b), M.cong_r(Nat.mul(x, b), Nat.mul(1n, b), b, AR.one_mul(b)))
  +h3 = L.subst(Nat, z => {Nat.is_le(z, Nat.mul(a, b)) == True{} : Bool}, Nat.mul(Nat.add(x, 1n), b), Nat.add(Nat.mul(x, b), b), e, h2)
  +h4 = N.lt_le_trans(Nat.mul(x, b), Nat.add(Nat.mul(x, b), b), Nat.mul(a, b), L.subst(Nat, z => {Nat.is_lt(z, Nat.add(Nat.mul(x, b), b)) == True{} : Bool}, Nat.add(Nat.mul(x, b), 0n), Nat.mul(x, b), N.add_zero(Nat.mul(x, b)), N.lt_add_left(0n, b, Nat.mul(x, b), bpos)), h3)
  N.le_lt_trans(Nat.mul(x, y), Nat.mul(x, b), Nat.mul(a, b), h1, h4)

def addl_below(+xs: List<&2, Nat>, +ys: List<&2, Nat>, +a: Nat, +b: Nat, +hx: {FV.below(xs, a) == True{} : Bool}, +hy: {FV.below(ys, b) == True{} : Bool}) -> {FV.below(LS.addl(xs, ys), Nat.add(a, b)) == True{} : Bool}:
  match xs ys:
    case Nil{} _:
      below_mono(ys, b, Nat.add(a, b), le_add_l(a, b), hy)
    case Con{+x, +xt} Nil{}:
      below_mono(Con{x, xt}, a, Nat.add(a, b), N.le_add_right(a, b), hx)
    case Con{+x, +xt} Con{+y, +yt}:
      below_con(Nat.add(x, y), LS.addl(xt, yt), Nat.add(a, b), lt_add2(x, y, a, b, below_head(x, xt, a, hx), below_head(y, yt, b, hy)), addl_below(xt, yt, a, b, below_tail(x, xt, a, hx), below_tail(y, yt, b, hy)))

def scal_below(+x: Nat, +ys: List<&2, Nat>, +a: Nat, +b: Nat, +hx: {Nat.is_lt(x, a) == True{} : Bool}, +hy: {FV.below(ys, b) == True{} : Bool}) -> {FV.below(LS.scal(x, ys), Nat.mul(a, b)) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +yt}:
      below_con(Nat.mul(x, y), LS.scal(x, yt), Nat.mul(a, b), lt_mul2(x, y, a, b, hx, below_head(y, yt, b, hy)), scal_below(x, yt, a, b, hx, below_tail(y, yt, b, hy)))

def scal_r_below(+ys: List<&2, Nat>, +k: Nat, +b: Nat, +kb: Nat, +hy: {FV.below(ys, b) == True{} : Bool}, +hk: {Nat.is_lt(k, kb) == True{} : Bool}) -> {FV.below(LS.scal_r(ys, k), Nat.mul(b, kb)) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +yt}:
      below_con(Nat.mul(y, k), LS.scal_r(yt, k), Nat.mul(b, kb), lt_mul2(y, k, b, kb, below_head(y, yt, b, hy), hk), scal_r_below(yt, k, b, kb, below_tail(y, yt, b, hy), hk))

# len(xs) p
def cb(xs: List<&2, Nat>, +p: Nat) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{x, xt}:
      Nat.add(p, cb(xt, p))

def conv_below(+xs: List<&2, Nat>, +ys: List<&2, Nat>, +a: Nat, +b: Nat, +hx: {FV.below(xs, a) == True{} : Bool}, +hy: {FV.below(ys, b) == True{} : Bool}) -> {FV.below(LS.conv(xs, ys), cb(xs, Nat.mul(a, b))) == True{} : Bool}:
  match xs ys:
    case Nil{} _:
      {==}
    case Con{+x, +xt} Nil{}:
      {==}
    case Con{+x, +xt} Con{+y, +yt}:
      +P = Nat.mul(a, b)
      +K = cb(xt, P)
      +hxh = below_head(x, xt, a, hx)
      +hd = N.lt_le_trans(Nat.mul(x, y), P, Nat.add(P, K), lt_mul2(x, y, a, b, hxh, below_head(y, yt, b, hy)), N.le_add_right(P, K))
      +hs = scal_below(x, yt, a, b, hxh, below_tail(y, yt, b, hy))
      +hc = conv_below(xt, Con{y, yt}, a, b, below_tail(x, xt, a, hx), hy)
      below_con(Nat.mul(x, y), LS.addl(LS.scal(x, yt), LS.conv(xt, Con{y, yt})), Nat.add(P, K), hd, addl_below(LS.scal(x, yt), LS.conv(xt, Con{y, yt}), P, K, hs, hc))

def take_below(+n: Nat, +xs: List<&2, Nat>, +b: Nat, +h: {FV.below(xs, b) == True{} : Bool}) -> {FV.below(LS.take(n, xs), b) == True{} : Bool}:
  match n xs:
    case 0n _:
      {==}
    case 1n+m Nil{}:
      {==}
    case 1n+ +m Con{+x, +xt}:
      below_con(x, LS.take(m, xt), b, below_head(x, xt, b, h), take_below(m, xt, b, below_tail(x, xt, b, h)))

def drop_below(+n: Nat, +xs: List<&2, Nat>, +b: Nat, +h: {FV.below(xs, b) == True{} : Bool}) -> {FV.below(LS.drop(n, xs), b) == True{} : Bool}:
  match n xs:
    case 0n _:
      h
    case 1n+m Nil{}:
      {==}
    case 1n+ +m Con{+x, +xt}:
      drop_below(m, xt, b, below_tail(x, xt, b, h))
