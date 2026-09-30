import Base
import ../../../spec/crypto/curve25519/fe.bend as FV
import ../../../src/crypto/curve25519/fe.bend as FE
import ../../../src/crypto/curve25519/limbs.bend as LS
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/word.bend as WD
import ../../lib/arith.bend as AR
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../curve25519/num.bend as M
import ../curve25519/cong.bend as G
import ./nl.bend as NL
import ./pw.bend as PW
import ./pass.bend as PS
import ./bridge.bend as BR
import ./prod.bend as PD
import ./pcar.bend as PC
import ./sqr.bend as SQ

# add, sub, mul, mul_small and select of src/crypto/curve25519/fe.bend: the
# value mod p and the limb bounds (ok: below 2^19), through their reference
# list forms (bridge.bend) and the pass lemmas (pass.bend).

def tr(+a: Nat, +b: Nat, +c: Nat, +e1: {a == b : Nat}, +e2: {b == c : Nat}) -> {a == c : Nat}:
  Equal.trans(Nat, a, b, c, e1, e2)

def sy(+a: Nat, +b: Nat, +e: {a == b : Nat}) -> {b == a : Nat}:
  Equal.sym(Nat, a, b, e)

def L15(+a: FE.Fe) -> {PS.ln(FE.to_list(a)) == 15n : Nat}:
  match a:
    case FE.Fe{a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14}:
      {==}

# the value through a list equation
def lv_eq(+xs: List<&2, Nat>, +ys: List<&2, Nat>, +e: {xs == ys : List<&2, Nat>}) -> {FV.lv(xs) == FV.lv(ys) : Nat}:
  Equal.cong(List<&2, Nat>, Nat, z => FV.lv(z), xs, ys, e)

def below_eq(+xs: List<&2, Nat>, +ys: List<&2, Nat>, +b: Nat, +e: {xs == ys : List<&2, Nat>}, +h: {FV.below(ys, b) == True{} : Bool}) -> {FV.below(xs, b) == True{} : Bool}:
  L.subst(List<&2, Nat>, z => {FV.below(z, b) == True{} : Bool}, ys, xs, Equal.sym(List<&2, Nat>, xs, ys, e), h)

def le_47(+k: Nat, +one: Nat, +d: Nat, +h: {Nat.add(d, k) == 47n : Nat}) -> {Nat.is_le(WD.sc(k, one), WD.sc(47n, one)) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_le(WD.sc(k, one), WD.sc(z, one)) == True{} : Bool}, Nat.add(d, k), 47n, h, PW.le_sc(d, k, one))

# ---- add ----

def addl_len(+a: FE.Fe, +b: FE.Fe) -> {PS.ln(LS.addl(FE.to_list(a), FE.to_list(b))) == 15n : Nat}:
  match a b:
    case FE.Fe{a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14} FE.Fe{b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14}:
      {==}

def add_c(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +a: FE.Fe, +b: FE.Fe) -> G.ceq(pp, FV.value(FE.add(R, a, b)), Nat.add(FV.value(a), FV.value(b))):
  +A = FE.to_list(a)
  +B = FE.to_list(b)
  +e0 = lv_eq(FE.to_list(FE.add(R, a, b)), LS.add_l(R, A, B), BR.add_b(R, a, b))
  G.c_trans(pp, FV.value(FE.add(R, a, b)), FV.lv(LS.pc(R, LS.addl(A, B))), Nat.add(FV.lv(A), FV.lv(B)), G.c_eq(pp, FV.value(FE.add(R, a, b)), FV.lv(LS.pc(R, LS.addl(A, B))), e0),
    G.c_trans(pp, FV.lv(LS.pc(R, LS.addl(A, B))), FV.lv(LS.addl(A, B)), Nat.add(FV.lv(A), FV.lv(B)), PC.pc_c(one, h1, pp, hP, R, hR, LS.addl(A, B), addl_len(a, b)), G.c_eq(pp, FV.lv(LS.addl(A, B)), Nat.add(FV.lv(A), FV.lv(B)), NL.lv_addl(A, B))))

def add_ok(+one: Nat, +h1: {one == 1n : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +a: FE.Fe, +b: FE.Fe, +ha: {FV.ok(one, a) == True{} : Bool}, +hb: {FV.ok(one, b) == True{} : Bool}) -> {FV.ok(one, FE.add(R, a, b)) == True{} : Bool}:
  +A = FE.to_list(a)
  +B = FE.to_list(b)
  +s19 = WD.sc(19n, one)
  +h20 = NL.addl_below(A, B, s19, s19, ha, hb)
  +h20b = L.subst(Nat, z => {FV.below(LS.addl(A, B), z) == True{} : Bool}, Nat.add(s19, s19), WD.sc(20n, one), PW.dbl(19n, one), h20)
  +h21 = NL.below_mono(LS.addl(A, B), WD.sc(20n, one), WD.sc(21n, one), PW.le_sc(1n, 20n, one), h20b)
  below_eq(FE.to_list(FE.add(R, a, b)), LS.pc(R, LS.addl(A, B)), s19, BR.add_b(R, a, b), PC.pc_ok21(one, h1, R, hR, LS.addl(A, B), addl_len(a, b), h21))

# ---- mul_small ----

def scal_len(+a: FE.Fe, +k: Nat) -> {PS.ln(LS.scal_r(FE.to_list(a), k)) == 15n : Nat}:
  match a:
    case FE.Fe{a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14}:
      {==}

def mul_small_c(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +a: FE.Fe, +k: Nat) -> G.ceq(pp, FV.value(FE.mul_small(R, a, k)), Nat.mul(FV.value(a), k)):
  +A = FE.to_list(a)
  +e0 = lv_eq(FE.to_list(FE.mul_small(R, a, k)), LS.mul_small_l(R, A, k), BR.mul_small_b(R, a, k))
  G.c_trans(pp, FV.value(FE.mul_small(R, a, k)), FV.lv(LS.pass(R, LS.scal_r(A, k))), Nat.mul(FV.lv(A), k), G.c_eq(pp, FV.value(FE.mul_small(R, a, k)), FV.lv(LS.pass(R, LS.scal_r(A, k))), e0),
    G.c_trans(pp, FV.lv(LS.pass(R, LS.scal_r(A, k))), FV.lv(LS.scal_r(A, k)), Nat.mul(FV.lv(A), k), PS.pass_c(one, h1, pp, hP, R, hR, LS.scal_r(A, k), scal_len(a, k)), G.c_eq(pp, FV.lv(LS.scal_r(A, k)), Nat.mul(FV.lv(A), k), NL.lv_scal_r(A, k))))

def mul_small_ok(+one: Nat, +h1: {one == 1n : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +a: FE.Fe, +k: Nat, +ha: {FV.ok(one, a) == True{} : Bool}, +hk: {Nat.is_lt(k, WD.sc(17n, one)) == True{} : Bool}) -> {FV.ok(one, FE.mul_small(R, a, k)) == True{} : Bool}:
  +A = FE.to_list(a)
  +h36 = NL.scal_r_below(A, k, WD.sc(19n, one), WD.sc(17n, one), ha, hk)
  +h36b = L.subst(Nat, z => {FV.below(LS.scal_r(A, k), z) == True{} : Bool}, Nat.mul(WD.sc(19n, one), WD.sc(17n, one)), WD.sc(36n, one), PW.scsc(19n, 17n, one, h1), h36)
  +h47 = NL.below_mono(LS.scal_r(A, k), WD.sc(36n, one), WD.sc(47n, one), le_47(36n, one, 11n, {==}), h36b)
  below_eq(FE.to_list(FE.mul_small(R, a, k)), LS.pass(R, LS.scal_r(A, k)), WD.sc(19n, one), BR.mul_small_b(R, a, k), PS.pass_ok(one, h1, R, hR, LS.scal_r(A, k), scal_len(a, k), h47))

# ---- mul ----

def fold_len(+a: FE.Fe, +b: FE.Fe) -> {PS.ln(LS.fold(LS.conv(FE.to_list(a), FE.to_list(b)))) == 15n : Nat}:
  match a b:
    case FE.Fe{a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14} FE.Fe{b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14}:
      {==}

# value(fold(zs)) == value(zs) (mod p)
def fold_c(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +zs: List<&2, Nat>) -> G.ceq(pp, FV.lv(LS.fold(zs)), FV.lv(zs)):
  +T = FV.lv(LS.take(15n, zs))
  +D = FV.lv(LS.drop(15n, zs))
  +e1 = tr(FV.lv(LS.fold(zs)), Nat.add(T, FV.lv(LS.scal_r(LS.drop(15n, zs), 19n))), Nat.add(T, Nat.mul(D, 19n)), NL.lv_addl(LS.take(15n, zs), LS.scal_r(LS.drop(15n, zs), 19n)), M.cong_r(T, FV.lv(LS.scal_r(LS.drop(15n, zs), 19n)), Nat.mul(D, 19n), NL.lv_scal_r(LS.drop(15n, zs), 19n)))
  +e2 = tr(FV.lv(zs), Nat.add(T, NL.sh(15n, D)), Nat.add(T, WD.sc(255n, D)), NL.lv_split(15n, zs), M.cong_r(T, NL.sh(15n, D), WD.sc(255n, D), NL.sh15(D)))
  +e3 = G.c_add(pp, T, T, Nat.mul(D, 19n), WD.sc(255n, D), G.c_refl(pp, T), G.c_sym(pp, WD.sc(255n, D), Nat.mul(D, 19n), PS.c19(one, h1, pp, hP, D)))
  G.c_trans(pp, FV.lv(LS.fold(zs)), Nat.add(T, Nat.mul(D, 19n)), FV.lv(zs), G.c_eq(pp, FV.lv(LS.fold(zs)), Nat.add(T, Nat.mul(D, 19n)), e1), G.c_trans(pp, Nat.add(T, Nat.mul(D, 19n)), Nat.add(T, WD.sc(255n, D)), FV.lv(zs), e3, G.c_eq(pp, Nat.add(T, WD.sc(255n, D)), FV.lv(zs), sy(FV.lv(zs), Nat.add(T, WD.sc(255n, D)), e2))))

# the flat product is pass(fold(conv)) (convp is conv on ok limbs)
def mul_list(+one: Nat, +h1: {one == 1n : Nat}, +R: Nat, +a: FE.Fe, +b: FE.Fe, +ha: {FV.ok(one, a) == True{} : Bool}, +hb: {FV.ok(one, b) == True{} : Bool}) -> {FE.to_list(FE.mul(R, a, b)) == LS.pass(R, LS.fold(LS.conv(FE.to_list(a), FE.to_list(b)))) : List<&2, Nat>}:
  +A = FE.to_list(a)
  +B = FE.to_list(b)
  Equal.trans(List<&2, Nat>, FE.to_list(FE.mul(R, a, b)), LS.mul_l(R, A, B), LS.pass(R, LS.fold(LS.conv(A, B))), BR.mul_b(R, a, b), Equal.cong(List<&2, Nat>, List<&2, Nat>, z => LS.pass(R, LS.fold(z)), LS.convp(A, B), LS.conv(A, B), PD.convp_eq(one, h1, A, B, ha, hb)))

def mul_c(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +a: FE.Fe, +b: FE.Fe, +ha: {FV.ok(one, a) == True{} : Bool}, +hb: {FV.ok(one, b) == True{} : Bool}) -> G.ceq(pp, FV.value(FE.mul(R, a, b)), Nat.mul(FV.value(a), FV.value(b))):
  +A = FE.to_list(a)
  +B = FE.to_list(b)
  +Z = LS.fold(LS.conv(A, B))
  +e0 = lv_eq(FE.to_list(FE.mul(R, a, b)), LS.pass(R, Z), mul_list(one, h1, R, a, b, ha, hb))
  G.c_trans(pp, FV.value(FE.mul(R, a, b)), FV.lv(LS.pass(R, Z)), Nat.mul(FV.lv(A), FV.lv(B)), G.c_eq(pp, FV.value(FE.mul(R, a, b)), FV.lv(LS.pass(R, Z)), e0),
    G.c_trans(pp, FV.lv(LS.pass(R, Z)), FV.lv(Z), Nat.mul(FV.lv(A), FV.lv(B)), PS.pass_c(one, h1, pp, hP, R, hR, Z, fold_len(a, b)),
      G.c_trans(pp, FV.lv(Z), FV.lv(LS.conv(A, B)), Nat.mul(FV.lv(A), FV.lv(B)), fold_c(one, h1, pp, hP, LS.conv(A, B)), G.c_eq(pp, FV.lv(LS.conv(A, B)), Nat.mul(FV.lv(A), FV.lv(B)), NL.lv_conv(A, B)))))

# the flat square is pass(fold(conv(a, a)))
def sq_list(+one: Nat, +h1: {one == 1n : Nat}, +R: Nat, +a: FE.Fe, +ha: {FV.ok(one, a) == True{} : Bool}) -> {FE.to_list(FE.sq(R, a)) == LS.pass(R, LS.fold(LS.conv(FE.to_list(a), FE.to_list(a)))) : List<&2, Nat>}:
  +A = FE.to_list(a)
  Equal.trans(List<&2, Nat>, FE.to_list(FE.sq(R, a)), LS.sq_l(R, A), LS.pass(R, LS.fold(LS.conv(A, A))), BR.sq_b(R, a), Equal.cong(List<&2, Nat>, List<&2, Nat>, z => LS.pass(R, LS.fold(z)), LS.sqp(A), LS.conv(A, A), SQ.sqp_conv(one, h1, A, ha)))

def sq_c(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +a: FE.Fe, +ha: {FV.ok(one, a) == True{} : Bool}) -> G.ceq(pp, FV.value(FE.sq(R, a)), Nat.mul(FV.value(a), FV.value(a))):
  +A = FE.to_list(a)
  +Z = LS.fold(LS.conv(A, A))
  +e0 = lv_eq(FE.to_list(FE.sq(R, a)), LS.pass(R, Z), sq_list(one, h1, R, a, ha))
  G.c_trans(pp, FV.value(FE.sq(R, a)), FV.lv(LS.pass(R, Z)), Nat.mul(FV.lv(A), FV.lv(A)), G.c_eq(pp, FV.value(FE.sq(R, a)), FV.lv(LS.pass(R, Z)), e0),
    G.c_trans(pp, FV.lv(LS.pass(R, Z)), FV.lv(Z), Nat.mul(FV.lv(A), FV.lv(A)), PS.pass_c(one, h1, pp, hP, R, hR, Z, fold_len(a, a)),
      G.c_trans(pp, FV.lv(Z), FV.lv(LS.conv(A, A)), Nat.mul(FV.lv(A), FV.lv(A)), fold_c(one, h1, pp, hP, LS.conv(A, A)), G.c_eq(pp, FV.lv(LS.conv(A, A)), Nat.mul(FV.lv(A), FV.lv(A)), NL.lv_conv(A, A)))))

def cb15(+a: FE.Fe, +P: Nat) -> {NL.cb(FE.to_list(a), P) == Nat.mul(15n, P) : Nat}:
  match a:
    case FE.Fe{a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14}:
      {==}

# the folded columns of the product of two ok elements are below 2^47
def cols_below(+one: Nat, +h1: {one == 1n : Nat}, +a: FE.Fe, +b: FE.Fe, +ha: {FV.ok(one, a) == True{} : Bool}, +hb: {FV.ok(one, b) == True{} : Bool}) -> {FV.below(LS.fold(LS.conv(FE.to_list(a), FE.to_list(b))), WD.sc(47n, one)) == True{} : Bool}:
  +A = FE.to_list(a)
  +B = FE.to_list(b)
  +s19 = WD.sc(19n, one)
  +P = Nat.mul(s19, s19)
  +Q = WD.sc(42n, one)
  +Z = LS.conv(A, B)
  +h0 = NL.conv_below(A, B, s19, s19, ha, hb)
  +eP = PW.scsc(19n, 19n, one, h1)
  +l1 = AR.mul_le(15n, 16n, P, {==})
  +e16 = tr(Nat.mul(16n, P), Nat.mul(P, 16n), WD.sc(4n, P), NA.mul_comm(16n, P), PS.mulp(4n, P))
  +e42 = tr(WD.sc(4n, P), WD.sc(4n, WD.sc(38n, one)), Q, M.cong_sc(4n, P, WD.sc(38n, one), eP), M.sc_sc(4n, 38n, one))
  +l2 = L.subst(Nat, z => {Nat.is_le(Nat.mul(15n, P), z) == True{} : Bool}, Nat.mul(16n, P), Q, tr(Nat.mul(16n, P), WD.sc(4n, P), Q, e16, e42), l1)
  +hZ = NL.below_mono(Z, NL.cb(A, P), Q, L.subst(Nat, z => {Nat.is_le(z, Q) == True{} : Bool}, Nat.mul(15n, P), NL.cb(A, P), sy(NL.cb(A, P), Nat.mul(15n, P), cb15(a, P)), l2), h0)
  +ht = NL.take_below(15n, Z, Q, hZ)
  +hd = NL.scal_r_below(LS.drop(15n, Z), 19n, Q, 20n, NL.drop_below(15n, Z, Q, hZ), {==})
  +hs = NL.addl_below(LS.take(15n, Z), LS.scal_r(LS.drop(15n, Z), 19n), Q, Nat.mul(Q, 20n), ht, hd)
  +l3 = PW.mul_le_r(Q, 21n, 32n, {==})
  +e32 = tr(Nat.mul(Q, 32n), WD.sc(5n, Q), WD.sc(47n, one), PS.mulp(5n, Q), M.sc_sc(5n, 42n, one))
  +l4 = L.subst(Nat, z => {Nat.is_le(z, WD.sc(47n, one)) == True{} : Bool}, Nat.mul(Q, 21n), Nat.add(Q, Nat.mul(Q, 20n)), NA.mul_succ(Q, 20n), L.subst(Nat, z => {Nat.is_le(Nat.mul(Q, 21n), z) == True{} : Bool}, Nat.mul(Q, 32n), WD.sc(47n, one), e32, l3))
  NL.below_mono(LS.fold(Z), Nat.add(Q, Nat.mul(Q, 20n)), WD.sc(47n, one), l4, hs)

def mul_ok(+one: Nat, +h1: {one == 1n : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +a: FE.Fe, +b: FE.Fe, +ha: {FV.ok(one, a) == True{} : Bool}, +hb: {FV.ok(one, b) == True{} : Bool}) -> {FV.ok(one, FE.mul(R, a, b)) == True{} : Bool}:
  +Z = LS.fold(LS.conv(FE.to_list(a), FE.to_list(b)))
  below_eq(FE.to_list(FE.mul(R, a, b)), LS.pass(R, Z), WD.sc(19n, one), mul_list(one, h1, R, a, b, ha, hb), PS.pass_ok(one, h1, R, hR, Z, fold_len(a, b), cols_below(one, h1, a, b, ha, hb)))

# ---- select ----

def sel0(+xs: List<&2, Nat>, +ys: List<&2, Nat>, +hl: {PS.ln(xs) == PS.ln(ys) : Nat}) -> {LS.sel(0n, xs, ys) == xs : List<&2, Nat>}:
  match xs ys:
    case Nil{} _:
      {==}
    case Con{x, xt} Nil{}:
      Empty.absurd({Nil{} == Con{x, xt} : List<&2, Nat>}, N.succ_zero(PS.ln(xt), hl))
    case Con{+x, +xt} Con{+y, +yt}:
      +eh = tr(Nat.add(Nat.mul(x, 1n), Nat.mul(y, 0n)), Nat.add(x, 0n), x, M.cong_add(Nat.mul(x, 1n), x, Nat.mul(y, 0n), 0n, NA.mul_one(x), NA.mul_zero(y)), N.add_zero(x))
      +et = sel0(xt, yt, N.succ_inj(PS.ln(xt), PS.ln(yt), hl))
      +e1 = Equal.cong(Nat, List<&2, Nat>, z => Con{z, LS.sel(0n, xt, yt)}, Nat.add(Nat.mul(x, 1n), Nat.mul(y, 0n)), x, eh)
      +e2 = Equal.cong(List<&2, Nat>, List<&2, Nat>, z => Con{x, z}, LS.sel(0n, xt, yt), xt, et)
      Equal.trans(List<&2, Nat>, Con{Nat.add(Nat.mul(x, 1n), Nat.mul(y, 0n)), LS.sel(0n, xt, yt)}, Con{x, LS.sel(0n, xt, yt)}, Con{x, xt}, e1, e2)

def sel1(+xs: List<&2, Nat>, +ys: List<&2, Nat>, +hl: {PS.ln(xs) == PS.ln(ys) : Nat}) -> {LS.sel(1n, xs, ys) == ys : List<&2, Nat>}:
  match xs ys:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{y, yt}:
      Empty.absurd({Nil{} == Con{y, yt} : List<&2, Nat>}, N.zero_succ(PS.ln(yt), hl))
    case Con{x, xt} Nil{}:
      Empty.absurd({Nil{} == Nil{} : List<&2, Nat>}, N.succ_zero(PS.ln(xt), hl))
    case Con{+x, +xt} Con{+y, +yt}:
      +eh = tr(Nat.add(Nat.mul(x, 0n), Nat.mul(y, 1n)), Nat.add(0n, y), y, M.cong_add(Nat.mul(x, 0n), 0n, Nat.mul(y, 1n), y, NA.mul_zero(x), NA.mul_one(y)), {==})
      +et = sel1(xt, yt, N.succ_inj(PS.ln(xt), PS.ln(yt), hl))
      +e1 = Equal.cong(Nat, List<&2, Nat>, z => Con{z, LS.sel(1n, xt, yt)}, Nat.add(Nat.mul(x, 0n), Nat.mul(y, 1n)), y, eh)
      +e2 = Equal.cong(List<&2, Nat>, List<&2, Nat>, z => Con{y, z}, LS.sel(1n, xt, yt), yt, et)
      Equal.trans(List<&2, Nat>, Con{Nat.add(Nat.mul(x, 0n), Nat.mul(y, 1n)), LS.sel(1n, xt, yt)}, Con{y, LS.sel(1n, xt, yt)}, Con{y, yt}, e1, e2)

def of_to(+x: FE.Fe) -> {FE.of_list(FE.to_list(x)) == x : FE.Fe}:
  match x:
    case FE.Fe{a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14}:
      {==}

# equal limbs, equal elements
def fe_ext(+x: FE.Fe, +y: FE.Fe, +e: {FE.to_list(x) == FE.to_list(y) : List<&2, Nat>}) -> {x == y : FE.Fe}:
  +e1 = Equal.cong(List<&2, Nat>, FE.Fe, z => FE.of_list(z), FE.to_list(x), FE.to_list(y), e)
  Equal.trans(FE.Fe, x, FE.of_list(FE.to_list(x)), y, Equal.sym(FE.Fe, FE.of_list(FE.to_list(x)), x, of_to(x)), Equal.trans(FE.Fe, FE.of_list(FE.to_list(x)), FE.of_list(FE.to_list(y)), y, e1, of_to(y)))

def ln_eq(+a: FE.Fe, +b: FE.Fe) -> {PS.ln(FE.to_list(a)) == PS.ln(FE.to_list(b)) : Nat}:
  Equal.trans(Nat, PS.ln(FE.to_list(a)), 15n, PS.ln(FE.to_list(b)), L15(a), Equal.sym(Nat, PS.ln(FE.to_list(b)), 15n, L15(b)))

def select0(+a: FE.Fe, +b: FE.Fe) -> {FE.select(0, a, b) == a : FE.Fe}:
  fe_ext(FE.select(0, a, b), a, Equal.trans(List<&2, Nat>, FE.to_list(FE.select(0, a, b)), LS.sel(0n, FE.to_list(a), FE.to_list(b)), FE.to_list(a), BR.select_b(0, a, b), sel0(FE.to_list(a), FE.to_list(b), ln_eq(a, b))))

def select1(+a: FE.Fe, +b: FE.Fe) -> {FE.select(1, a, b) == b : FE.Fe}:
  fe_ext(FE.select(1, a, b), b, Equal.trans(List<&2, Nat>, FE.to_list(FE.select(1, a, b)), LS.sel(1n, FE.to_list(a), FE.to_list(b)), FE.to_list(b), BR.select_b(1, a, b), sel1(FE.to_list(a), FE.to_list(b), ln_eq(a, b))))

def sq_ok(+one: Nat, +h1: {one == 1n : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +a: FE.Fe, +ha: {FV.ok(one, a) == True{} : Bool}) -> {FV.ok(one, FE.sq(R, a)) == True{} : Bool}:
  +Z = LS.fold(LS.conv(FE.to_list(a), FE.to_list(a)))
  below_eq(FE.to_list(FE.sq(R, a)), LS.pass(R, Z), WD.sc(19n, one), sq_list(one, h1, R, a, ha), PS.pass_ok(one, h1, R, hR, Z, fold_len(a, a), cols_below(one, h1, a, a, ha, ha)))
