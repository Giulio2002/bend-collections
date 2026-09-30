import Base
import ../../../spec/lib/common.bend as C
import ../../../src/crypto/poly1305/limbs.bend as Li
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../../math/typed/width.bend as WW
import ../../math/typed/w64mul.bend as WM
import ../../math/typed/w64add.bend as WA
import ../../math/typed/w64sh.bend as SH
import ../../math/typed/shrn.bend as SHN
import ../../math/typed/f64bits.bend as FB
import ./arith.bend as A

# The value of a limb list (radix 2^8, least significant limb first) and the
# limb operations of src/crypto/poly1305/limbs.bend against it: sums and
# products are exact (Fiat-Crypto / HACL* Field32xN style: the limb value is
# the number, as long as no U32 operation wraps), under limb bounds
# le_all(xs, B) (every limb <= B) whose sums and products fit 32 bits.

def v(+x: U32) -> Nat:
  U32.to_nat(x)

def ev(xs: List<&2, U32>) -> Nat:
  match xs:
    case Nil{}: 0n
    case x <> t: Nat.add(v(x), C.shift(8n, ev(t)))

def le_all(xs: List<&2, U32>, +b: Nat) -> Bool:
  match xs:
    case Nil{}: True{}
    case x <> t: Bool.and(Nat.is_le(v(x), b), le_all(t, b))

def hd_le(+x: U32, +t: List<&2, U32>, +b: Nat, +h: {le_all(x <> t, b) == True{} : Bool}) -> {Nat.is_le(v(x), b) == True{} : Bool}:
  L.and_left(Nat.is_le(v(x), b), le_all(t, b), h)

def tl_le(+x: U32, +t: List<&2, U32>, +b: Nat, +h: {le_all(x <> t, b) == True{} : Bool}) -> {le_all(t, b) == True{} : Bool}:
  L.and_right(Nat.is_le(v(x), b), le_all(t, b), h)

def cons_le(+x: U32, +t: List<&2, U32>, +b: Nat, +hx: {Nat.is_le(v(x), b) == True{} : Bool}, +ht: {le_all(t, b) == True{} : Bool}) -> {le_all(x <> t, b) == True{} : Bool}:
  L.and_intro(Nat.is_le(v(x), b), le_all(t, b), hx, ht)

law le_mono:
  for +xs: List<&2, U32>
  for +b: Nat
  for +c: Nat
  for +hb: {Nat.is_le(b, c) == True{} : Bool}
  for +h: {le_all(xs, b) == True{} : Bool}
  {le_all(xs, c) == True{} : Bool}

def le_mono(xs, b, c, hb, h):
  match xs:
    case Nil{}: {==}
    case x <> t:
      cons_le(x, t, c, N.le_trans(v(x), b, c, hd_le(x, t, b, h), hb), le_mono(t, b, c, hb, tl_le(x, t, b, h)))

# ---- sums ----

# the exact U32 sum of two limbs whose bounds add up within 32 bits
def add1(+x: U32, +y: U32, +b1: Nat, +b2: Nat, +hx: {Nat.is_le(v(x), b1) == True{} : Bool}, +hy: {Nat.is_le(v(y), b2) == True{} : Bool}, +hf: {C.fits(32n, Nat.add(b1, b2)) == True{} : Bool}) -> {v(U32.add(x, y)) == Nat.add(v(x), v(y)) : Nat}:
  WA.add_exact(1n, {==}, x, y, A.fits_le(32n, Nat.add(v(x), v(y)), Nat.add(b1, b2), A.le_add2(v(x), v(y), b1, b2, hx, hy), hf))

law add_ev:
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  for +b1: Nat
  for +b2: Nat
  for +ha: {le_all(a, b1) == True{} : Bool}
  for +hb: {le_all(b, b2) == True{} : Bool}
  for +hf: {C.fits(32n, Nat.add(b1, b2)) == True{} : Bool}
  {ev(Li.add(a, b)) == Nat.add(ev(a), ev(b)) : Nat}

def add_ev(a, b, b1, b2, ha, hb, hf):
  match a b:
    case Nil{} _: {==}
    case x <> at Nil{}: A.sy(Nat.add(ev(x <> at), 0n), ev(x <> at), N.add_zero(ev(x <> at)))
    case x <> at y <> bt:
      +e1 = add1(x, y, b1, b2, hd_le(x, at, b1, ha), hd_le(y, bt, b2, hb), hf)
      +e2 = add_ev(at, bt, b1, b2, tl_le(x, at, b1, ha), tl_le(y, bt, b2, hb), hf)
      +s1 = C.shift(8n, ev(at))
      +s2 = C.shift(8n, ev(bt))
      A.tr(Nat.add(v(U32.add(x, y)), C.shift(8n, ev(Li.add(at, bt)))), Nat.add(Nat.add(v(x), v(y)), Nat.add(s1, s2)), Nat.add(Nat.add(v(x), s1), Nat.add(v(y), s2)),
        A.cadd(v(U32.add(x, y)), Nat.add(v(x), v(y)), C.shift(8n, ev(Li.add(at, bt))), Nat.add(s1, s2), e1,
          A.tr(C.shift(8n, ev(Li.add(at, bt))), C.shift(8n, Nat.add(ev(at), ev(bt))), Nat.add(s1, s2), A.csh(8n, ev(Li.add(at, bt)), Nat.add(ev(at), ev(bt)), e2), WW.shift_add(8n, ev(at), ev(bt)))),
        WM.add4(v(x), v(y), s1, s2))

law add_le:
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  for +b1: Nat
  for +b2: Nat
  for +ha: {le_all(a, b1) == True{} : Bool}
  for +hb: {le_all(b, b2) == True{} : Bool}
  for +hf: {C.fits(32n, Nat.add(b1, b2)) == True{} : Bool}
  {le_all(Li.add(a, b), Nat.add(b1, b2)) == True{} : Bool}

def add_le(a, b, b1, b2, ha, hb, hf):
  match a b:
    case Nil{} _: le_mono(b, b2, Nat.add(b1, b2), A.le_add_l(b1, b2), hb)
    case x <> at Nil{}: le_mono(x <> at, b1, Nat.add(b1, b2), N.le_add_right(b1, b2), ha)
    case x <> at y <> bt:
      +hx = hd_le(x, at, b1, ha)
      +hy = hd_le(y, bt, b2, hb)
      cons_le(U32.add(x, y), Li.add(at, bt), Nat.add(b1, b2),
        L.subst(Nat, z => {Nat.is_le(z, Nat.add(b1, b2)) == True{} : Bool}, Nat.add(v(x), v(y)), v(U32.add(x, y)), A.sy(v(U32.add(x, y)), Nat.add(v(x), v(y)), add1(x, y, b1, b2, hx, hy, hf)), A.le_add2(v(x), v(y), b1, b2, hx, hy)),
        add_le(at, bt, b1, b2, tl_le(x, at, b1, ha), tl_le(y, bt, b2, hb), hf))

# ---- products by a limb ----

def mul1(+x: U32, +c: U32, +b: Nat, +bc: Nat, +hx: {Nat.is_le(v(x), b) == True{} : Bool}, +hc: {Nat.is_le(v(c), bc) == True{} : Bool}, +hf: {C.fits(32n, Nat.mul(b, bc)) == True{} : Bool}) -> {v(U32.mul(x, c)) == Nat.mul(v(x), v(c)) : Nat}:
  A.tr(v(U32.mul(x, c)), C.low(32n, Nat.mul(v(x), v(c))), Nat.mul(v(x), v(c)), SH.mul_low(x, c),
    WW.low_fit(32n, Nat.mul(v(x), v(c)), A.fits_le(32n, Nat.mul(v(x), v(c)), Nat.mul(b, bc), A.le_mul2(v(x), v(c), b, bc, hx, hc), hf)))

law scale_ev:
  for +c: U32
  for +a: List<&2, U32>
  for +b: Nat
  for +bc: Nat
  for +ha: {le_all(a, b) == True{} : Bool}
  for +hc: {Nat.is_le(v(c), bc) == True{} : Bool}
  for +hf: {C.fits(32n, Nat.mul(b, bc)) == True{} : Bool}
  {ev(Li.scale(c, a)) == Nat.mul(ev(a), v(c)) : Nat}

def scale_ev(c, a, b, bc, ha, hc, hf):
  match a:
    case Nil{}: {==}
    case x <> t:
      +e1 = mul1(x, c, b, bc, hd_le(x, t, b, ha), hc, hf)
      +e2 = scale_ev(c, t, b, bc, tl_le(x, t, b, ha), hc, hf)
      A.tr(Nat.add(v(U32.mul(x, c)), C.shift(8n, ev(Li.scale(c, t)))), Nat.add(Nat.mul(v(x), v(c)), C.shift(8n, Nat.mul(ev(t), v(c)))), Nat.mul(Nat.add(v(x), C.shift(8n, ev(t))), v(c)),
        A.cadd(v(U32.mul(x, c)), Nat.mul(v(x), v(c)), C.shift(8n, ev(Li.scale(c, t))), C.shift(8n, Nat.mul(ev(t), v(c))), e1, A.csh(8n, ev(Li.scale(c, t)), Nat.mul(ev(t), v(c)), e2)),
        A.sy(Nat.mul(Nat.add(v(x), C.shift(8n, ev(t))), v(c)), Nat.add(Nat.mul(v(x), v(c)), C.shift(8n, Nat.mul(ev(t), v(c)))),
          A.tr(Nat.mul(Nat.add(v(x), C.shift(8n, ev(t))), v(c)), Nat.add(Nat.mul(v(x), v(c)), Nat.mul(C.shift(8n, ev(t)), v(c))), Nat.add(Nat.mul(v(x), v(c)), C.shift(8n, Nat.mul(ev(t), v(c)))),
            NA.mul_add_right(v(x), C.shift(8n, ev(t)), v(c)),
            WM.cong_r(Nat.mul(v(x), v(c)), Nat.mul(C.shift(8n, ev(t)), v(c)), C.shift(8n, Nat.mul(ev(t), v(c))), WW.shift_mul_l(8n, ev(t), v(c))))))

law scale_le:
  for +c: U32
  for +a: List<&2, U32>
  for +b: Nat
  for +bc: Nat
  for +ha: {le_all(a, b) == True{} : Bool}
  for +hc: {Nat.is_le(v(c), bc) == True{} : Bool}
  for +hf: {C.fits(32n, Nat.mul(b, bc)) == True{} : Bool}
  {le_all(Li.scale(c, a), Nat.mul(b, bc)) == True{} : Bool}

def scale_le(c, a, b, bc, ha, hc, hf):
  match a:
    case Nil{}: {==}
    case x <> t:
      +hx = hd_le(x, t, b, ha)
      cons_le(U32.mul(x, c), Li.scale(c, t), Nat.mul(b, bc),
        L.subst(Nat, z => {Nat.is_le(z, Nat.mul(b, bc)) == True{} : Bool}, Nat.mul(v(x), v(c)), v(U32.mul(x, c)), A.sy(v(U32.mul(x, c)), Nat.mul(v(x), v(c)), mul1(x, c, b, bc, hx, hc, hf)), A.le_mul2(v(x), v(c), b, bc, hx, hc)),
        scale_le(c, t, b, bc, tl_le(x, t, b, ha), hc, hf))

# ---- schoolbook products ----

law mul_le:
  for +x: List<&2, U32>
  for +r: List<&2, U32>
  for +bx: Nat
  for +br: Nat
  for +hx: {le_all(x, bx) == True{} : Bool}
  for +hr: {le_all(r, br) == True{} : Bool}
  for +hf: {C.fits(32n, Nat.mul(List.length(&2, U32, r), Nat.mul(bx, br))) == True{} : Bool}
  {le_all(Li.mul(x, r), Nat.mul(List.length(&2, U32, r), Nat.mul(bx, br))) == True{} : Bool}

def mul_le(x, r, bx, br, hx, hr, hf):
  match r:
    case Nil{}: {==}
    case r0 <> rs:
      +m = Nat.mul(bx, br)
      +k = Nat.mul(List.length(&2, U32, rs), m)
      +hm = A.fits_add_l(32n, m, k, hf)
      +hk = A.fits_add_r(32n, m, k, hf)
      add_le(Li.scale(r0, x), 0 <> Li.mul(x, rs), m, k,
        scale_le(r0, x, bx, br, hx, hd_le(r0, rs, br, hr), hm),
        cons_le(0, Li.mul(x, rs), k, N.zero_le(k), mul_le(x, rs, bx, br, hx, tl_le(r0, rs, br, hr), hk)),
        hf)

law mul_ev:
  for +x: List<&2, U32>
  for +r: List<&2, U32>
  for +bx: Nat
  for +br: Nat
  for +hx: {le_all(x, bx) == True{} : Bool}
  for +hr: {le_all(r, br) == True{} : Bool}
  for +hf: {C.fits(32n, Nat.mul(List.length(&2, U32, r), Nat.mul(bx, br))) == True{} : Bool}
  {ev(Li.mul(x, r)) == Nat.mul(ev(x), ev(r)) : Nat}

def mul_ev(x, r, bx, br, hx, hr, hf):
  match r:
    case Nil{}: A.sy(Nat.mul(ev(x), 0n), 0n, NA.mul_zero(ev(x)))
    case r0 <> rs:
      +m = Nat.mul(bx, br)
      +k = Nat.mul(List.length(&2, U32, rs), m)
      +hm = A.fits_add_l(32n, m, k, hf)
      +hk = A.fits_add_r(32n, m, k, hf)
      +hr0 = hd_le(r0, rs, br, hr)
      +hrs = tl_le(r0, rs, br, hr)
      +e1 = add_ev(Li.scale(r0, x), 0 <> Li.mul(x, rs), m, k,
        scale_le(r0, x, bx, br, hx, hr0, hm),
        cons_le(0, Li.mul(x, rs), k, N.zero_le(k), mul_le(x, rs, bx, br, hx, hrs, hk)),
        hf)
      +e2 = scale_ev(r0, x, bx, br, hx, hr0, hm)
      +e3 = mul_ev(x, rs, bx, br, hx, hrs, hk)
      +ex = ev(x)
      A.tr(ev(Li.add(Li.scale(r0, x), 0 <> Li.mul(x, rs))), Nat.add(ev(Li.scale(r0, x)), C.shift(8n, ev(Li.mul(x, rs)))), Nat.mul(ex, Nat.add(v(r0), C.shift(8n, ev(rs)))), e1,
        A.tr(Nat.add(ev(Li.scale(r0, x)), C.shift(8n, ev(Li.mul(x, rs)))), Nat.add(Nat.mul(ex, v(r0)), C.shift(8n, Nat.mul(ex, ev(rs)))), Nat.mul(ex, Nat.add(v(r0), C.shift(8n, ev(rs)))),
          A.cadd(ev(Li.scale(r0, x)), Nat.mul(ex, v(r0)), C.shift(8n, ev(Li.mul(x, rs))), C.shift(8n, Nat.mul(ex, ev(rs))), e2, A.csh(8n, ev(Li.mul(x, rs)), Nat.mul(ex, ev(rs)), e3)),
          A.sy(Nat.mul(ex, Nat.add(v(r0), C.shift(8n, ev(rs)))), Nat.add(Nat.mul(ex, v(r0)), C.shift(8n, Nat.mul(ex, ev(rs)))),
            A.tr(Nat.mul(ex, Nat.add(v(r0), C.shift(8n, ev(rs)))), Nat.add(Nat.mul(ex, v(r0)), Nat.mul(ex, C.shift(8n, ev(rs)))), Nat.add(Nat.mul(ex, v(r0)), C.shift(8n, Nat.mul(ex, ev(rs)))),
              NA.mul_add_left(ex, v(r0), C.shift(8n, ev(rs))),
              WM.cong_r(Nat.mul(ex, v(r0)), Nat.mul(ex, C.shift(8n, ev(rs))), C.shift(8n, Nat.mul(ex, ev(rs))), WW.shift_mul_r(8n, ex, ev(rs)))))))

# ---- positions ----

# y at limb position n: y * 2^(8n)
def pos(n: Nat, +y: Nat) -> Nat:
  match n:
    case 0n: y
    case 1n+k: C.shift(8n, pos(k, y))

law pos_zero:
  for +n: Nat
  {pos(n, 0n) == 0n : Nat}

def pos_zero(n):
  match n:
    case 0n: {==}
    case 1n+k: A.tr(C.shift(8n, pos(k, 0n)), C.shift(8n, 0n), 0n, A.csh(8n, pos(k, 0n), 0n, pos_zero(k)), {==})

law pos_add:
  for +n: Nat
  for +x: Nat
  for +y: Nat
  {pos(n, Nat.add(x, y)) == Nat.add(pos(n, x), pos(n, y)) : Nat}

def pos_add(n, x, y):
  match n:
    case 0n: {==}
    case 1n+k: A.tr(C.shift(8n, pos(k, Nat.add(x, y))), C.shift(8n, Nat.add(pos(k, x), pos(k, y))), Nat.add(C.shift(8n, pos(k, x)), C.shift(8n, pos(k, y))), A.csh(8n, pos(k, Nat.add(x, y)), Nat.add(pos(k, x), pos(k, y)), pos_add(k, x, y)), WW.shift_add(8n, pos(k, x), pos(k, y)))

law skip_nil:
  for +n: Nat
  {Li.skip(n, []) == [] : List<&2, U32>}

def skip_nil(n):
  match n:
    case 0n: {==}
    case 1n+k: {==}

# ev(xs) = ev(take n xs) + 2^(8n) ev(skip n xs)
law ts_ev:
  for +n: Nat
  for +xs: List<&2, U32>
  {ev(xs) == Nat.add(ev(Li.take(n, xs)), pos(n, ev(Li.skip(n, xs)))) : Nat}

def ts_ev(n, xs):
  match n xs:
    case 0n _: {==}
    case 1n+k Nil{}: A.sy(C.shift(8n, pos(k, 0n)), 0n, A.tr(C.shift(8n, pos(k, 0n)), C.shift(8n, 0n), 0n, A.csh(8n, pos(k, 0n), 0n, pos_zero(k)), {==}))
    case 1n+k x <> t:
      +a = ev(Li.take(k, t))
      +b = pos(k, ev(Li.skip(k, t)))
      A.tr(Nat.add(v(x), C.shift(8n, ev(t))), Nat.add(v(x), Nat.add(C.shift(8n, a), C.shift(8n, b))), Nat.add(Nat.add(v(x), C.shift(8n, a)), C.shift(8n, b)),
        WM.cong_r(v(x), C.shift(8n, ev(t)), Nat.add(C.shift(8n, a), C.shift(8n, b)), A.tr(C.shift(8n, ev(t)), C.shift(8n, Nat.add(a, b)), Nat.add(C.shift(8n, a), C.shift(8n, b)), A.csh(8n, ev(t), Nat.add(a, b), ts_ev(k, t)), WW.shift_add(8n, a, b))),
        A.sy(Nat.add(Nat.add(v(x), C.shift(8n, a)), C.shift(8n, b)), Nat.add(v(x), Nat.add(C.shift(8n, a), C.shift(8n, b))), N.add_assoc(v(x), C.shift(8n, a), C.shift(8n, b))))

law take_nil_ev:
  for +n: Nat
  {ev(Li.take(n, [])) == 0n : Nat}

def take_nil_ev(n):
  match n:
    case 0n: {==}
    case 1n+k: {==}

law fit_ev:
  for +n: Nat
  for +xs: List<&2, U32>
  {ev(Li.fit(n, xs)) == ev(Li.take(n, xs)) : Nat}

def fit_ev(n, xs):
  match n xs:
    case 0n _: {==}
    case 1n+k Nil{}: A.tr(C.shift(8n, ev(Li.fit(k, []))), C.shift(8n, 0n), 0n, A.csh(8n, ev(Li.fit(k, [])), 0n, A.tr(ev(Li.fit(k, [])), ev(Li.take(k, [])), 0n, fit_ev(k, []), take_nil_ev(k))), {==})
    case 1n+k x <> t: WM.cong_r(v(x), C.shift(8n, ev(Li.fit(k, t))), C.shift(8n, ev(Li.take(k, t))), A.csh(8n, ev(Li.fit(k, t)), ev(Li.take(k, t)), fit_ev(k, t)))

# ---- carry passes ----

def fit_all(xs: List<&2, U32>, +k: Nat) -> Bool:
  match xs:
    case Nil{}: True{}
    case x <> t: Bool.and(C.fits(k, v(x)), fit_all(t, k))

law fits_zero:
  for +k: Nat
  {C.fits(k, 0n) == True{} : Bool}

def fits_zero(k):
  match k:
    case 0n: {==}
    case 1n+p: fits_zero(p)

def hd0_fit(+ds: List<&2, U32>, +k: Nat, +h: {fit_all(ds, k) == True{} : Bool}) -> {C.fits(k, v(Li.hd0(ds))) == True{} : Bool}:
  match ds:
    case Nil{}: fits_zero(k)
    case x <> t: L.and_left(C.fits(k, v(x)), fit_all(t, k), h)

def tl_fit(+ds: List<&2, U32>, +k: Nat, +h: {fit_all(ds, k) == True{} : Bool}) -> {fit_all(Li.tl(ds), k) == True{} : Bool}:
  match ds:
    case Nil{}: {==}
    case x <> t: L.and_right(C.fits(k, v(x)), fit_all(t, k), h)

def hd_tl_ev(+ds: List<&2, U32>) -> {ev(ds) == Nat.add(v(Li.hd0(ds)), C.shift(8n, ev(Li.tl(ds)))) : Nat}:
  match ds:
    case Nil{}: {==}
    case x <> t: {==}

def skip_succ(+k: Nat, +ds: List<&2, U32>) -> {Li.skip(1n+k, ds) == Li.skip(k, Li.tl(ds)) : List<&2, U32>}:
  match ds:
    case Nil{}: Equal.sym(List<&2, U32>, Li.skip(k, []), [], skip_nil(k))
    case x <> t: {==}

# (a + 2^8 b) + 2^8 c == a + 2^8 (b + c)
def sh3(+a: Nat, +b: Nat, +c: Nat) -> {Nat.add(Nat.add(a, C.shift(8n, b)), C.shift(8n, c)) == Nat.add(a, C.shift(8n, Nat.add(b, c))) : Nat}:
  A.tr(Nat.add(Nat.add(a, C.shift(8n, b)), C.shift(8n, c)), Nat.add(a, Nat.add(C.shift(8n, b), C.shift(8n, c))), Nat.add(a, C.shift(8n, Nat.add(b, c))),
    N.add_assoc(a, C.shift(8n, b), C.shift(8n, c)),
    WM.cong_r(a, Nat.add(C.shift(8n, b), C.shift(8n, c)), C.shift(8n, Nat.add(b, c)), A.sy(C.shift(8n, Nat.add(b, c)), Nat.add(C.shift(8n, b), C.shift(8n, c)), WW.shift_add(8n, b, c))))

def sh4(+a: Nat, +b: Nat, +c: Nat, +d: Nat) -> {Nat.add(Nat.add(Nat.add(a, C.shift(8n, b)), C.shift(8n, c)), C.shift(8n, d)) == Nat.add(a, C.shift(8n, Nat.add(Nat.add(b, c), d))) : Nat}:
  A.tr(Nat.add(Nat.add(Nat.add(a, C.shift(8n, b)), C.shift(8n, c)), C.shift(8n, d)), Nat.add(Nat.add(a, C.shift(8n, Nat.add(b, c))), C.shift(8n, d)), Nat.add(a, C.shift(8n, Nat.add(Nat.add(b, c), d))),
    WM.cong_l(Nat.add(Nat.add(a, C.shift(8n, b)), C.shift(8n, c)), Nat.add(a, C.shift(8n, Nat.add(b, c))), C.shift(8n, d), sh3(a, b, c)),
    sh3(a, Nat.add(b, c), d))

# the sum u + ds[0] of one carry step, exact and within 9 + j bits
def step_fit(+ds: List<&2, U32>, +u: U32, +j: Nat, +hd: {fit_all(ds, Nat.add(8n, j)) == True{} : Bool}, +hu: {C.fits(Nat.add(8n, j), v(u)) == True{} : Bool}) -> {C.fits(Nat.add(9n, j), Nat.add(v(u), v(Li.hd0(ds)))) == True{} : Bool}:
  A.fits_add(Nat.add(8n, j), v(u), v(Li.hd0(ds)), hu, hd0_fit(ds, Nat.add(8n, j), hd))

def step_ev(+ds: List<&2, U32>, +u: U32, +j: Nat, +hj: {Nat.is_le(Nat.add(9n, j), 32n) == True{} : Bool}, +hd: {fit_all(ds, Nat.add(8n, j)) == True{} : Bool}, +hu: {C.fits(Nat.add(8n, j), v(u)) == True{} : Bool}) -> {v(U32.add(u, Li.hd0(ds))) == Nat.add(v(u), v(Li.hd0(ds))) : Nat}:
  WA.add_exact(1n, {==}, u, Li.hd0(ds), SH.fits_mono(Nat.add(9n, j), 32n, Nat.add(v(u), v(Li.hd0(ds))), hj, step_fit(ds, u, j, hd, hu)))

# the next carry high(8, s) fits 8 + j bits again
def next_fit(+ds: List<&2, U32>, +u: U32, +j: Nat, +hj: {Nat.is_le(Nat.add(9n, j), 32n) == True{} : Bool}, +hd: {fit_all(ds, Nat.add(8n, j)) == True{} : Bool}, +hu: {C.fits(Nat.add(8n, j), v(u)) == True{} : Bool}) -> {C.fits(Nat.add(8n, j), v(U32.shrn(U32.add(u, Li.hd0(ds)), 8n))) == True{} : Bool}:
  +s = U32.add(u, Li.hd0(ds))
  +h1 = A.fits_subst(Nat.add(9n, j), Nat.add(v(u), v(Li.hd0(ds))), v(s), A.sy(v(s), Nat.add(v(u), v(Li.hd0(ds))), step_ev(ds, u, j, hj, hd, hu)), step_fit(ds, u, j, hd, hu))
  +h2 = SH.fits_high(8n, 1n+j, v(s), h1)
  +h3 = SH.fits_mono(1n+j, Nat.add(8n, j), C.high(8n, v(s)), A.le_add_l(7n, j), h2)
  A.fits_subst(Nat.add(8n, j), C.high(8n, v(s)), v(U32.shrn(s, 8n)), A.sy(v(U32.shrn(s, 8n)), C.high(8n, v(s)), SHN.shrn_high(s, 8n)), h3)

# A carry pass over n limbs keeps the value: carry(n, ds, u) + 2^(8(n+1)) ds[n+1..] == u + ds.
law carry_ev:
  for +n: Nat
  for +ds: List<&2, U32>
  for +u: U32
  for +j: Nat
  for +hj: {Nat.is_le(Nat.add(9n, j), 32n) == True{} : Bool}
  for +hd: {fit_all(ds, Nat.add(8n, j)) == True{} : Bool}
  for +hu: {C.fits(Nat.add(8n, j), v(u)) == True{} : Bool}
  {Nat.add(ev(Li.carry(n, ds, u)), pos(1n+n, ev(Li.skip(1n+n, ds)))) == Nat.add(v(u), ev(ds)) : Nat}

def carry_ev(n, ds, u, j, hj, hd, hu):
  match n:
    case 0n:
      +h = Li.hd0(ds)
      +s = U32.add(u, h)
      +es = step_ev(ds, u, j, hj, hd, hu)
      +et = ev(Li.tl(ds))
      A.tr(Nat.add(Nat.add(v(s), 0n), C.shift(8n, ev(Li.skip(1n, ds)))), Nat.add(v(s), C.shift(8n, et)), Nat.add(v(u), ev(ds)),
        A.cadd(Nat.add(v(s), 0n), v(s), C.shift(8n, ev(Li.skip(1n, ds))), C.shift(8n, et), N.add_zero(v(s)), A.csh(8n, ev(Li.skip(1n, ds)), et, Equal.cong(List<&2, U32>, Nat, l => ev(l), Li.skip(1n, ds), Li.tl(ds), skip_succ(0n, ds)))),
        A.tr(Nat.add(v(s), C.shift(8n, et)), Nat.add(Nat.add(v(u), v(h)), C.shift(8n, et)), Nat.add(v(u), ev(ds)),
          WM.cong_l(v(s), Nat.add(v(u), v(h)), C.shift(8n, et), es),
          A.tr(Nat.add(Nat.add(v(u), v(h)), C.shift(8n, et)), Nat.add(v(u), Nat.add(v(h), C.shift(8n, et))), Nat.add(v(u), ev(ds)), N.add_assoc(v(u), v(h), C.shift(8n, et)),
            WM.cong_r(v(u), Nat.add(v(h), C.shift(8n, et)), ev(ds), A.sy(ev(ds), Nat.add(v(h), C.shift(8n, et)), hd_tl_ev(ds))))))
    case 1n+k:
      +h = Li.hd0(ds)
      +s = U32.add(u, h)
      +es = step_ev(ds, u, j, hj, hd, hu)
      +et = ev(Li.tl(ds))
      +u2 = U32.shrn(s, 8n)
      +lo = v(U32.and(s, 255))
      +c1 = ev(Li.carry(k, Li.tl(ds), u2))
      +p1 = pos(1n+k, ev(Li.skip(1n+k, Li.tl(ds))))
      +ih = carry_ev(k, Li.tl(ds), u2, j, hj, tl_fit(ds, Nat.add(8n, j), hd), next_fit(ds, u, j, hj, hd, hu))
      +e0 = WM.cong_r(Nat.add(lo, C.shift(8n, c1)), C.shift(8n, pos(1n+k, ev(Li.skip(2n+k, ds)))), C.shift(8n, p1),
        A.csh(8n, pos(1n+k, ev(Li.skip(2n+k, ds))), p1, Equal.cong(List<&2, U32>, Nat, l => pos(1n+k, ev(l)), Li.skip(2n+k, ds), Li.skip(1n+k, Li.tl(ds)), skip_succ(1n+k, ds))))
      +e1 = sh3(lo, c1, p1)
      +e2 = WM.cong_r(lo, C.shift(8n, Nat.add(c1, p1)), C.shift(8n, Nat.add(v(u2), et)), A.csh(8n, Nat.add(c1, p1), Nat.add(v(u2), et), ih))
      +e3 = A.sy(Nat.add(Nat.add(lo, C.shift(8n, v(u2))), C.shift(8n, et)), Nat.add(lo, C.shift(8n, Nat.add(v(u2), et))), sh3(lo, v(u2), et))
      +elo = A.tr(lo, C.low(8n, v(s)), C.low(8n, v(s)), FB.andm(s, 8n, 255, {==}), {==})
      +ehi = SHN.shrn_high(s, 8n)
      +e4 = A.tr(Nat.add(lo, C.shift(8n, v(u2))), Nat.add(C.low(8n, v(s)), C.shift(8n, C.high(8n, v(s)))), v(s),
        A.cadd(lo, C.low(8n, v(s)), C.shift(8n, v(u2)), C.shift(8n, C.high(8n, v(s))), elo, A.csh(8n, v(u2), C.high(8n, v(s)), ehi)),
        A.sy(v(s), Nat.add(C.low(8n, v(s)), C.shift(8n, C.high(8n, v(s)))), WW.low_high(8n, v(s))))
      +e5 = WM.cong_l(Nat.add(lo, C.shift(8n, v(u2))), v(s), C.shift(8n, et), e4)
      +e6 = A.tr(Nat.add(v(s), C.shift(8n, et)), Nat.add(Nat.add(v(u), v(h)), C.shift(8n, et)), Nat.add(v(u), ev(ds)),
          WM.cong_l(v(s), Nat.add(v(u), v(h)), C.shift(8n, et), es),
          A.tr(Nat.add(Nat.add(v(u), v(h)), C.shift(8n, et)), Nat.add(v(u), Nat.add(v(h), C.shift(8n, et))), Nat.add(v(u), ev(ds)), N.add_assoc(v(u), v(h), C.shift(8n, et)),
            WM.cong_r(v(u), Nat.add(v(h), C.shift(8n, et)), ev(ds), A.sy(ev(ds), Nat.add(v(h), C.shift(8n, et)), hd_tl_ev(ds)))))
      A.tr(Nat.add(Nat.add(lo, C.shift(8n, c1)), C.shift(8n, pos(1n+k, ev(Li.skip(2n+k, ds))))), Nat.add(Nat.add(lo, C.shift(8n, c1)), C.shift(8n, p1)), Nat.add(v(u), ev(ds)), e0,
        A.tr(Nat.add(Nat.add(lo, C.shift(8n, c1)), C.shift(8n, p1)), Nat.add(lo, C.shift(8n, Nat.add(c1, p1))), Nat.add(v(u), ev(ds)), e1,
          A.tr(Nat.add(lo, C.shift(8n, Nat.add(c1, p1))), Nat.add(lo, C.shift(8n, Nat.add(v(u2), et))), Nat.add(v(u), ev(ds)), e2,
            A.tr(Nat.add(lo, C.shift(8n, Nat.add(v(u2), et))), Nat.add(Nat.add(lo, C.shift(8n, v(u2))), C.shift(8n, et)), Nat.add(v(u), ev(ds)), e3,
              A.tr(Nat.add(Nat.add(lo, C.shift(8n, v(u2))), C.shift(8n, et)), Nat.add(v(s), C.shift(8n, et)), Nat.add(v(u), ev(ds)), e5, e6)))))

# every limb below the top one has 8 bits
law carry_lo:
  for +n: Nat
  for +ds: List<&2, U32>
  for +u: U32
  {fit_all(Li.take(n, Li.carry(n, ds, u)), 8n) == True{} : Bool}

def carry_lo(n, ds, u):
  match n:
    case 0n: {==}
    case 1n+k:
      +s = U32.add(u, Li.hd0(ds))
      L.and_intro(C.fits(8n, v(U32.and(s, 255))), fit_all(Li.take(k, Li.carry(k, Li.tl(ds), U32.shrn(s, 8n))), 8n),
        A.fits_subst(8n, C.low(8n, v(s)), v(U32.and(s, 255)), A.sy(v(U32.and(s, 255)), C.low(8n, v(s)), FB.andm(s, 8n, 255, {==})), WW.low_fits(8n, v(s))),
        carry_lo(k, Li.tl(ds), U32.shrn(s, 8n)))

# the top limb fits 9 + j bits
law carry_top:
  for +n: Nat
  for +ds: List<&2, U32>
  for +u: U32
  for +j: Nat
  for +hj: {Nat.is_le(Nat.add(9n, j), 32n) == True{} : Bool}
  for +hd: {fit_all(ds, Nat.add(8n, j)) == True{} : Bool}
  for +hu: {C.fits(Nat.add(8n, j), v(u)) == True{} : Bool}
  {C.fits(Nat.add(9n, j), v(Li.hd0(Li.skip(n, Li.carry(n, ds, u))))) == True{} : Bool}

def carry_top(n, ds, u, j, hj, hd, hu):
  match n:
    case 0n:
      A.fits_subst(Nat.add(9n, j), Nat.add(v(u), v(Li.hd0(ds))), v(U32.add(u, Li.hd0(ds))), A.sy(v(U32.add(u, Li.hd0(ds))), Nat.add(v(u), v(Li.hd0(ds))), step_ev(ds, u, j, hj, hd, hu)), step_fit(ds, u, j, hd, hu))
    case 1n+k:
      carry_top(k, Li.tl(ds), U32.shrn(U32.add(u, Li.hd0(ds)), 8n), j, hj, tl_fit(ds, Nat.add(8n, j), hd), next_fit(ds, u, j, hj, hd, hu))

law carry_len:
  for +n: Nat
  for +ds: List<&2, U32>
  for +u: U32
  {List.length(&2, U32, Li.carry(n, ds, u)) == 1n+n : Nat}

def carry_len(n, ds, u):
  match n:
    case 0n: {==}
    case 1n+k:
      +s = U32.add(u, Li.hd0(ds))
      Equal.cong(Nat, Nat, t => 1n+t, List.length(&2, U32, Li.carry(k, Li.tl(ds), U32.shrn(s, 8n))), 1n+k, carry_len(k, Li.tl(ds), U32.shrn(s, 8n)))

# ---- the 2^130 split of limb n ----

law sq_ev:
  for +n: Nat
  for +xs: List<&2, U32>
  {Nat.add(Nat.add(ev(Li.split(n, xs)), pos(n, C.shift(2n, v(Li.quot(n, xs))))), pos(1n+n, ev(Li.skip(1n+n, xs)))) == ev(xs) : Nat}

def sq_ev(n, xs):
  match n:
    case 0n:
      +h = Li.hd0(xs)
      +la = v(U32.and(h, 3))
      +vq = v(U32.shrn(h, 2n))
      +et = ev(Li.tl(xs))
      +e0 = A.cadd(Nat.add(Nat.add(la, 0n), C.shift(2n, vq)), Nat.add(la, C.shift(2n, vq)), C.shift(8n, ev(Li.skip(1n, xs))), C.shift(8n, et),
        WM.cong_l(Nat.add(la, 0n), la, C.shift(2n, vq), N.add_zero(la)),
        A.csh(8n, ev(Li.skip(1n, xs)), et, Equal.cong(List<&2, U32>, Nat, l => ev(l), Li.skip(1n, xs), Li.tl(xs), skip_succ(0n, xs))))
      +e1 = A.tr(Nat.add(la, C.shift(2n, vq)), Nat.add(C.low(2n, v(h)), C.shift(2n, C.high(2n, v(h)))), v(h),
        A.cadd(la, C.low(2n, v(h)), C.shift(2n, vq), C.shift(2n, C.high(2n, v(h))), FB.andm(h, 2n, 3, {==}), A.csh(2n, vq, C.high(2n, v(h)), SHN.shrn_high(h, 2n))),
        A.sy(v(h), Nat.add(C.low(2n, v(h)), C.shift(2n, C.high(2n, v(h)))), WW.low_high(2n, v(h))))
      A.tr(Nat.add(Nat.add(Nat.add(la, 0n), C.shift(2n, vq)), C.shift(8n, ev(Li.skip(1n, xs)))), Nat.add(Nat.add(la, C.shift(2n, vq)), C.shift(8n, et)), ev(xs), e0,
        A.tr(Nat.add(Nat.add(la, C.shift(2n, vq)), C.shift(8n, et)), Nat.add(v(h), C.shift(8n, et)), ev(xs), WM.cong_l(Nat.add(la, C.shift(2n, vq)), v(h), C.shift(8n, et), e1),
          A.sy(ev(xs), Nat.add(v(h), C.shift(8n, et)), hd_tl_ev(xs))))
    case 1n+k:
      +h = Li.hd0(xs)
      +sp = ev(Li.split(k, Li.tl(xs)))
      +pq = pos(k, C.shift(2n, v(Li.quot(k, Li.tl(xs)))))
      +pr = pos(1n+k, ev(Li.skip(1n+k, Li.tl(xs))))
      +et = ev(Li.tl(xs))
      +e0 = WM.cong_r(Nat.add(Nat.add(v(h), C.shift(8n, sp)), C.shift(8n, pq)), C.shift(8n, pos(1n+k, ev(Li.skip(2n+k, xs)))), C.shift(8n, pr),
        A.csh(8n, pos(1n+k, ev(Li.skip(2n+k, xs))), pr, Equal.cong(List<&2, U32>, Nat, l => pos(1n+k, ev(l)), Li.skip(2n+k, xs), Li.skip(1n+k, Li.tl(xs)), skip_succ(1n+k, xs))))
      A.tr(Nat.add(Nat.add(Nat.add(v(h), C.shift(8n, sp)), C.shift(8n, pq)), C.shift(8n, pos(1n+k, ev(Li.skip(2n+k, xs))))), Nat.add(Nat.add(Nat.add(v(h), C.shift(8n, sp)), C.shift(8n, pq)), C.shift(8n, pr)), ev(xs), e0,
        A.tr(Nat.add(Nat.add(Nat.add(v(h), C.shift(8n, sp)), C.shift(8n, pq)), C.shift(8n, pr)), Nat.add(v(h), C.shift(8n, Nat.add(Nat.add(sp, pq), pr))), ev(xs), sh4(v(h), sp, pq, pr),
          A.tr(Nat.add(v(h), C.shift(8n, Nat.add(Nat.add(sp, pq), pr))), Nat.add(v(h), C.shift(8n, et)), ev(xs),
            WM.cong_r(v(h), C.shift(8n, Nat.add(Nat.add(sp, pq), pr)), C.shift(8n, et), A.csh(8n, Nat.add(Nat.add(sp, pq), pr), et, sq_ev(k, Li.tl(xs)))),
            A.sy(ev(xs), Nat.add(v(h), C.shift(8n, et)), hd_tl_ev(xs)))))

# ---- lengths ----

def len(xs: List<&2, U32>) -> Nat:
  List.length(&2, U32, xs)

law len_add:
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  for +n: Nat
  for +ha: {Nat.is_le(len(a), n) == True{} : Bool}
  for +hb: {Nat.is_le(len(b), n) == True{} : Bool}
  {Nat.is_le(len(Li.add(a, b)), n) == True{} : Bool}

def len_add(a, b, n, ha, hb):
  match a b:
    case Nil{} _: hb
    case x <> at Nil{}: ha
    case x <> at y <> bt:
      match n:
        case 0n: Empty.absurd({Nat.is_le(len(Li.add(x <> at, y <> bt)), 0n) == True{} : Bool}, L.false_true(ha))
        case 1n+m: len_add(at, bt, m, ha, hb)

law len_scale:
  for +c: U32
  for +a: List<&2, U32>
  {len(Li.scale(c, a)) == len(a) : Nat}

def len_scale(c, a):
  match a:
    case Nil{}: {==}
    case x <> t: Equal.cong(Nat, Nat, z => 1n+z, len(Li.scale(c, t)), len(t), len_scale(c, t))

law len_mul:
  for +x: List<&2, U32>
  for +r: List<&2, U32>
  for +n: Nat
  for +hx: {Nat.is_le(len(x), n) == True{} : Bool}
  {Nat.is_le(len(Li.mul(x, r)), Nat.add(len(r), n)) == True{} : Bool}

def len_mul(x, r, n, hx):
  match r:
    case Nil{}: N.zero_le(n)
    case r0 <> rs:
      len_add(Li.scale(r0, x), 0 <> Li.mul(x, rs), Nat.add(1n+len(rs), n),
        A.le_substl(len(x), len(Li.scale(r0, x)), Nat.add(1n+len(rs), n), A.sy(len(Li.scale(r0, x)), len(x), len_scale(r0, x)), N.le_trans(len(x), n, Nat.add(1n+len(rs), n), hx, A.le_add_l(1n+len(rs), n))),
        len_mul(x, rs, n, hx))

law len_take:
  for +n: Nat
  for +xs: List<&2, U32>
  {Nat.is_le(len(Li.take(n, xs)), n) == True{} : Bool}

def len_take(n, xs):
  match n xs:
    case 0n _: {==}
    case 1n+k Nil{}: {==}
    case 1n+k x <> t: len_take(k, t)

law len_skip:
  for +n: Nat
  for +xs: List<&2, U32>
  for +b: Nat
  for +h: {Nat.is_le(len(xs), Nat.add(n, b)) == True{} : Bool}
  {Nat.is_le(len(Li.skip(n, xs)), b) == True{} : Bool}

def len_skip(n, xs, b, h):
  match n xs:
    case 0n _: h
    case 1n+k Nil{}: N.zero_le(b)
    case 1n+k x <> t: len_skip(k, t, b, h)

law skip_long:
  for +n: Nat
  for +xs: List<&2, U32>
  for +h: {Nat.is_le(len(xs), n) == True{} : Bool}
  {Li.skip(n, xs) == [] : List<&2, U32>}

def skip_long(n, xs, h):
  match n xs:
    case 0n Nil{}: {==}
    case 0n x <> t: Empty.absurd({Li.skip(0n, x <> t) == [] : List<&2, U32>}, L.false_true(h))
    case 1n+k Nil{}: {==}
    case 1n+k x <> t: skip_long(k, t, h)

# ---- bounds ----

law le_take:
  for +n: Nat
  for +xs: List<&2, U32>
  for +b: Nat
  for +h: {le_all(xs, b) == True{} : Bool}
  {le_all(Li.take(n, xs), b) == True{} : Bool}

def le_take(n, xs, b, h):
  match n xs:
    case 0n _: {==}
    case 1n+k Nil{}: {==}
    case 1n+k x <> t: cons_le(x, Li.take(k, t), b, hd_le(x, t, b, h), le_take(k, t, b, tl_le(x, t, b, h)))

law le_skip:
  for +n: Nat
  for +xs: List<&2, U32>
  for +b: Nat
  for +h: {le_all(xs, b) == True{} : Bool}
  {le_all(Li.skip(n, xs), b) == True{} : Bool}

def le_skip(n, xs, b, h):
  match n xs:
    case 0n _: h
    case 1n+k Nil{}: {==}
    case 1n+k x <> t: le_skip(k, t, b, tl_le(x, t, b, h))

law fit_le:
  for +xs: List<&2, U32>
  for +k: Nat
  for +one: Nat
  for +h1: {one == 1n : Nat}
  for +h: {fit_all(xs, k) == True{} : Bool}
  {le_all(xs, C.shift(k, one)) == True{} : Bool}

def fit_le(xs, k, one, h1, h):
  match xs:
    case Nil{}: {==}
    case x <> t: cons_le(x, t, C.shift(k, one), A.le_one(k, one, h1, v(x), L.and_left(C.fits(k, v(x)), fit_all(t, k), h)), fit_le(t, k, one, h1, L.and_right(C.fits(k, v(x)), fit_all(t, k), h)))

law le_fit:
  for +xs: List<&2, U32>
  for +b: Nat
  for +k: Nat
  for +one: Nat
  for +h1: {one == 1n : Nat}
  for +hb: {Nat.is_lt(b, C.shift(k, one)) == True{} : Bool}
  for +h: {le_all(xs, b) == True{} : Bool}
  {fit_all(xs, k) == True{} : Bool}

def le_fit(xs, b, k, one, h1, hb, h):
  match xs:
    case Nil{}: {==}
    case x <> t: L.and_intro(C.fits(k, v(x)), fit_all(t, k), WW.fits_one(k, one, h1, v(x), N.le_lt_trans(v(x), b, C.shift(k, one), hd_le(x, t, b, h), hb)), le_fit(t, b, k, one, h1, hb, tl_le(x, t, b, h)))

law fit_mono:
  for +xs: List<&2, U32>
  for +a: Nat
  for +b: Nat
  for +hab: {Nat.is_le(a, b) == True{} : Bool}
  for +h: {fit_all(xs, a) == True{} : Bool}
  {fit_all(xs, b) == True{} : Bool}

def fit_mono(xs, a, b, hab, h):
  match xs:
    case Nil{}: {==}
    case x <> t: L.and_intro(C.fits(b, v(x)), fit_all(t, b), SH.fits_mono(a, b, v(x), hab, L.and_left(C.fits(a, v(x)), fit_all(t, a), h)), fit_mono(t, a, b, hab, L.and_right(C.fits(a, v(x)), fit_all(t, a), h)))

law fit_take:
  for +n: Nat
  for +xs: List<&2, U32>
  for +k: Nat
  for +h: {fit_all(xs, k) == True{} : Bool}
  {fit_all(Li.take(n, xs), k) == True{} : Bool}

def fit_take(n, xs, k, h):
  match n xs:
    case 0n _: {==}
    case 1n+m Nil{}: {==}
    case 1n+m x <> t: L.and_intro(C.fits(k, v(x)), fit_all(Li.take(m, t), k), L.and_left(C.fits(k, v(x)), fit_all(t, k), h), fit_take(m, t, k, L.and_right(C.fits(k, v(x)), fit_all(t, k), h)))

# limbs of 8 bits: the value is below 2^(8 len)
law ev_lt:
  for +xs: List<&2, U32>
  for +one: Nat
  for +h1: {one == 1n : Nat}
  for +h: {fit_all(xs, 8n) == True{} : Bool}
  {Nat.is_lt(ev(xs), pos(len(xs), one)) == True{} : Bool}

def ev_lt(xs, one, h1, h):
  match xs:
    case Nil{}: A.lt_subst(0n, 1n, one, A.sy(one, 1n, h1), {==})
    case x <> t:
      +ht = ev_lt(t, one, h1, L.and_right(C.fits(8n, v(x)), fit_all(t, 8n), h))
      +hx = WW.lt_of_fits(8n, v(x), L.and_left(C.fits(8n, v(x)), fit_all(t, 8n), h))
      +p = pos(len(t), one)
      # v x + 2^8 ev t < 2^8 + 2^8 ev t = 2^8 (1 + ev t) <= 2^8 p
      +a1 = A.lt_le_add(v(x), C.shift(8n, ev(t)), C.pow2(8n), C.shift(8n, ev(t)), hx, N.le_refl(C.shift(8n, ev(t))))
      +e1 = A.tr(Nat.add(C.pow2(8n), C.shift(8n, ev(t))), Nat.add(C.shift(8n, 1n), C.shift(8n, ev(t))), C.shift(8n, 1n+ev(t)), {==}, A.sy(C.shift(8n, 1n+ev(t)), Nat.add(C.shift(8n, 1n), C.shift(8n, ev(t))), WW.shift_add(8n, 1n, ev(t))))
      N.lt_le_trans(Nat.add(v(x), C.shift(8n, ev(t))), C.shift(8n, 1n+ev(t)), C.shift(8n, p), A.lt_subst(Nat.add(v(x), C.shift(8n, ev(t))), Nat.add(C.pow2(8n), C.shift(8n, ev(t))), C.shift(8n, 1n+ev(t)), e1, a1), WW.shift_mono(8n, 1n+ev(t), p, N.lt_succ_le_succ(ev(t), p, ht)))

law fit_take_nil:
  for +n: Nat
  for +k: Nat
  {fit_all(Li.take(n, []), k) == True{} : Bool}

def fit_take_nil(n, k):
  match n:
    case 0n: {==}
    case 1n+m: {==}

law split_fit:
  for +n: Nat
  for +xs: List<&2, U32>
  for +h: {fit_all(Li.take(n, xs), 8n) == True{} : Bool}
  {fit_all(Li.split(n, xs), 8n) == True{} : Bool}

def split_fit(n, xs, h):
  match n:
    case 0n:
      +x = Li.hd0(xs)
      L.and_intro(C.fits(8n, v(U32.and(x, 3))), True{}, SH.fits_mono(2n, 8n, v(U32.and(x, 3)), {==}, A.fits_subst(2n, C.low(2n, v(x)), v(U32.and(x, 3)), A.sy(v(U32.and(x, 3)), C.low(2n, v(x)), FB.andm(x, 2n, 3, {==})), WW.low_fits(2n, v(x)))), {==})
    case 1n+k:
      match xs:
        case Nil{}: L.and_intro(C.fits(8n, 0n), fit_all(Li.split(k, []), 8n), {==}, split_fit(k, [], fit_take_nil(k, 8n)))
        case x <> t: L.and_intro(C.fits(8n, v(x)), fit_all(Li.split(k, t), 8n), L.and_left(C.fits(8n, v(x)), fit_all(Li.take(k, t), 8n), h), split_fit(k, t, L.and_right(C.fits(8n, v(x)), fit_all(Li.take(k, t), 8n), h)))

law fit_split:
  for +n: Nat
  for +xs: List<&2, U32>
  for +k: Nat
  for +h1: {fit_all(Li.take(n, xs), k) == True{} : Bool}
  for +h2: {fit_all(Li.skip(n, xs), k) == True{} : Bool}
  {fit_all(xs, k) == True{} : Bool}

def fit_split(n, xs, k, h1, h2):
  match n xs:
    case 0n _: h2
    case 1n+m Nil{}: {==}
    case 1n+m x <> t: L.and_intro(C.fits(k, v(x)), fit_all(t, k), L.and_left(C.fits(k, v(x)), fit_all(Li.take(m, t), k), h1), fit_split(m, t, k, L.and_right(C.fits(k, v(x)), fit_all(Li.take(m, t), k), h1), h2))

law quot_top:
  for +n: Nat
  for +xs: List<&2, U32>
  {Li.quot(n, xs) == U32.shrn(Li.hd0(Li.skip(n, xs)), 2n) : U32}

def quot_top(n, xs):
  match n:
    case 0n: {==}
    case 1n+k: Equal.trans(U32, Li.quot(k, Li.tl(xs)), U32.shrn(Li.hd0(Li.skip(k, Li.tl(xs))), 2n), U32.shrn(Li.hd0(Li.skip(1n+k, xs)), 2n), quot_top(k, Li.tl(xs)),
      Equal.cong(List<&2, U32>, U32, l => U32.shrn(Li.hd0(l), 2n), Li.skip(k, Li.tl(xs)), Li.skip(1n+k, xs), Equal.sym(List<&2, U32>, Li.skip(1n+k, xs), Li.skip(k, Li.tl(xs)), skip_succ(k, xs))))

law ev_one:
  for +xs: List<&2, U32>
  for +h: {Nat.is_le(len(xs), 1n) == True{} : Bool}
  {ev(xs) == v(Li.hd0(xs)) : Nat}

def ev_one(xs, h):
  match xs:
    case Nil{}: {==}
    case x <> t:
      match t:
        case Nil{}: N.add_zero(v(x))
        case y <> u: Empty.absurd({ev(x <> y <> u) == v(x) : Nat}, L.false_true(h))
