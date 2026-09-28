import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/crypto/poly1305.bend as R
import ../../../src/crypto/poly1305/limbs.bend as Li
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/arith.bend as AR
import ../../lib/u32.bend as U3
import ../../lib/u32alg.bend as UA
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../../math/typed/width.bend as WW
import ../../math/typed/w64mul.bend as WM
import ../../math/typed/w64sh.bend as SH
import ../../math/typed/shrn.bend as SHN
import ../../math/typed/f64bits.bend as FB
import ../../math/natural/arith.bend as NR
import ./arith.bend as A
import ./value.bend as V
import ./step.bend as ST

# The last steps: freeze (the canonical value mod p, by a masked choice) and
# the 16 tag bytes (h + s mod 2^128, little-endian).

# ---- words ----

def wones(n: Nat) -> Word(n):
  match n:
    case 0n: WNil{}
    case 1n+p: WCon{True{}, wones(p)}

law wand0:
  for +n: Nat
  for +w: Word(n)
  {Word.and(n, Word.zero(n), w) == Word.zero(n) : Word(n)}

def wand0(n, w):
  match n:
    case 0n:
      match w:
        case WNil{}: {==}
    case 1n+p:
      match w:
        case WCon{b, t}: Equal.cong(Word(p), Word(1n+p), x => WCon{False{}, x}, Word.and(p, Word.zero(p), t), Word.zero(p), wand0(p, t))

law wand1:
  for +n: Nat
  for +w: Word(n)
  {Word.and(n, wones(n), w) == w : Word(n)}

def wand1(n, w):
  match n:
    case 0n:
      match w:
        case WNil{}: {==}
    case 1n+p:
      match w:
        case WCon{b, t}: Equal.cong(Word(p), Word(1n+p), x => WCon{b, x}, Word.and(p, wones(p), t), t, wand1(p, t))

law wxor0:
  for +n: Nat
  for +w: Word(n)
  {Word.xor(n, w, Word.zero(n)) == w : Word(n)}

def wxor0(n, w):
  match n:
    case 0n:
      match w:
        case WNil{}: {==}
    case 1n+p:
      match w:
        case WCon{b, t}:
          match b:
            case False{}: Equal.cong(Word(p), Word(1n+p), x => WCon{False{}, x}, Word.xor(p, t, Word.zero(p)), t, wxor0(p, t))
            case True{}: Equal.cong(Word(p), Word(1n+p), x => WCon{True{}, x}, Word.xor(p, t, Word.zero(p)), t, wxor0(p, t))

law wxor2:
  for +n: Nat
  for +x: Word(n)
  for +y: Word(n)
  {Word.xor(n, x, Word.xor(n, x, y)) == y : Word(n)}

def wxor2(n, x, y):
  match n:
    case 0n:
      match x y:
        case WNil{} WNil{}: {==}
    case 1n+p:
      match x y:
        case WCon{False{}, s} WCon{False{}, t}: Equal.cong(Word(p), Word(1n+p), z => WCon{False{}, z}, Word.xor(p, s, Word.xor(p, s, t)), t, wxor2(p, s, t))
        case WCon{False{}, s} WCon{True{}, t}: Equal.cong(Word(p), Word(1n+p), z => WCon{True{}, z}, Word.xor(p, s, Word.xor(p, s, t)), t, wxor2(p, s, t))
        case WCon{True{}, s} WCon{False{}, t}: Equal.cong(Word(p), Word(1n+p), z => WCon{False{}, z}, Word.xor(p, s, Word.xor(p, s, t)), t, wxor2(p, s, t))
        case WCon{True{}, s} WCon{True{}, t}: Equal.cong(Word(p), Word(1n+p), z => WCon{True{}, z}, Word.xor(p, s, Word.xor(p, s, t)), t, wxor2(p, s, t))

def pick0(+x: U32, +y: U32) -> {Li.pick(0, x, y) == x : U32}:
  match x y:
    case U32{a} U32{b}:
      Equal.trans(U32, U32{Word.xor(32n, a, Word.and(32n, Word.zero(32n), Word.xor(32n, a, b)))}, U32{Word.xor(32n, a, Word.zero(32n))}, U32{a},
        Equal.cong(Word(32n), U32, w => U32{Word.xor(32n, a, w)}, Word.and(32n, Word.zero(32n), Word.xor(32n, a, b)), Word.zero(32n), wand0(32n, Word.xor(32n, a, b))),
        Equal.cong(Word(32n), U32, w => U32{w}, Word.xor(32n, a, Word.zero(32n)), a, wxor0(32n, a)))

def pick1(+x: U32, +y: U32) -> {Li.pick(4294967295, x, y) == y : U32}:
  match x y:
    case U32{a} U32{b}:
      Equal.trans(U32, U32{Word.xor(32n, a, Word.and(32n, wones(32n), Word.xor(32n, a, b)))}, U32{Word.xor(32n, a, Word.xor(32n, a, b))}, U32{b},
        Equal.cong(Word(32n), U32, w => U32{Word.xor(32n, a, w)}, Word.and(32n, wones(32n), Word.xor(32n, a, b)), Word.xor(32n, a, b), wand1(32n, Word.xor(32n, a, b))),
        Equal.cong(Word(32n), U32, w => U32{w}, Word.xor(32n, a, Word.xor(32n, a, b)), b, wxor2(32n, a, b)))

law sel0:
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  for +h: {V.len(a) == V.len(b) : Nat}
  {Li.select(0, a, b) == a : List<&2, U32>}

def sel0(a, b, h):
  match a b:
    case Nil{} Nil{}: {==}
    case Nil{} y <> bt: Empty.absurd({Li.select(0, [], y <> bt) == [] : List<&2, U32>}, N.zero_succ(V.len(bt), h))
    case x <> at Nil{}: Empty.absurd({Li.select(0, x <> at, []) == x <> at : List<&2, U32>}, N.succ_zero(V.len(at), h))
    case x <> at y <> bt:
      Equal.trans(List<&2, U32>, Li.pick(0, x, y) <> Li.select(0, at, bt), x <> Li.select(0, at, bt), x <> at,
        Equal.cong(U32, List<&2, U32>, z => z <> Li.select(0, at, bt), Li.pick(0, x, y), x, pick0(x, y)),
        Equal.cong(List<&2, U32>, List<&2, U32>, z => x <> z, Li.select(0, at, bt), at, sel0(at, bt, N.succ_inj(V.len(at), V.len(bt), h))))

law sel1:
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  for +h: {V.len(a) == V.len(b) : Nat}
  {Li.select(4294967295, a, b) == b : List<&2, U32>}

def sel1(a, b, h):
  match a b:
    case Nil{} Nil{}: {==}
    case Nil{} y <> bt: Empty.absurd({Li.select(4294967295, [], y <> bt) == y <> bt : List<&2, U32>}, N.zero_succ(V.len(bt), h))
    case x <> at Nil{}: Empty.absurd({Li.select(4294967295, x <> at, []) == [] : List<&2, U32>}, N.succ_zero(V.len(at), h))
    case x <> at y <> bt:
      Equal.trans(List<&2, U32>, Li.pick(4294967295, x, y) <> Li.select(4294967295, at, bt), y <> Li.select(4294967295, at, bt), y <> bt,
        Equal.cong(U32, List<&2, U32>, z => z <> Li.select(4294967295, at, bt), Li.pick(4294967295, x, y), y, pick1(x, y)),
        Equal.cong(List<&2, U32>, List<&2, U32>, z => y <> z, Li.select(4294967295, at, bt), bt, sel1(at, bt, N.succ_inj(V.len(at), V.len(bt), h))))

law len_take_eq:
  for +n: Nat
  for +xs: List<&2, U32>
  for +h: {Nat.is_le(n, V.len(xs)) == True{} : Bool}
  {V.len(Li.take(n, xs)) == n : Nat}

def len_take_eq(n, xs, h):
  match n xs:
    case 0n _: {==}
    case 1n+k Nil{}: Empty.absurd({V.len(Li.take(1n+k, [])) == 1n+k : Nat}, L.false_true(h))
    case 1n+k x <> t: Equal.cong(Nat, Nat, z => 1n+z, V.len(Li.take(k, t)), k, len_take_eq(k, t, h))

# ---- freeze ----

# x < 2x for x >= 1
def lt_dbl(+x: Nat, +h: {Nat.is_le(1n, x) == True{} : Bool}) -> {Nat.is_lt(x, Nat.double(x)) == True{} : Bool}:
  A.lt_subst(x, Nat.add(x, x), Nat.double(x), A.sy(Nat.double(x), Nat.add(x, x), NA.double_self(x)),
    A.lt_substl(Nat.add(x, 0n), x, Nat.add(x, x), N.add_zero(x), N.lt_add_left(0n, x, x, N.succ_le_lt(0n, x, h))))

# the facts about h, g = carry(h + 5) and the choice bit shared by both cases
def hval(+h: List<&2, U32>) -> Nat:
  V.ev(h)

def gg(+h: List<&2, U32>) -> List<&2, U32>:
  Li.carry(16n, Li.add(h, [5]), 0)

def qq(+h: List<&2, U32>) -> Nat:
  C.high(130n, Nat.add(V.ev(h), 5n))

law g_ev:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  for +h: List<&2, U32>
  for +hh: {ST.inv(h) == True{} : Bool}
  {V.ev(gg(h)) == Nat.add(V.ev(h), 5n) : Nat}

def g_ev(one, h1, h, hh):
  +s8 = C.shift(8n, one)
  +hl = N.eq_from_is_eq(V.len(h), 17n, L.and_left(Nat.is_eq(V.len(h), 17n), Bool.and(V.fit_all(h, 8n), Nat.is_le(V.v(Li.hd0(Li.skip(16n, h))), 4n)), hh))
  +hr2 = L.and_right(Nat.is_eq(V.len(h), 17n), Bool.and(V.fit_all(h, 8n), Nat.is_le(V.v(Li.hd0(Li.skip(16n, h))), 4n)), hh)
  +hf = L.and_left(V.fit_all(h, 8n), Nat.is_le(V.v(Li.hd0(Li.skip(16n, h))), 4n), hr2)
  +a = Li.add(h, [5])
  +h5 = V.cons_le(5, [], s8, L.subst(Nat, z => {Nat.is_le(5n, C.shift(8n, z)) == True{} : Bool}, 1n, one, A.sy(one, 1n, h1), {==}), {==})
  +hf1 = ST.s8fit(one, h1)
  +ea = V.add_ev(h, [5], s8, s8, V.fit_le(h, 8n, one, h1, hf), h5, hf1)
  +s9 = C.shift(9n, one)
  +l10 = A.lt_substl(s9, Nat.add(s8, s8), Nat.double(s9), NA.double_self(s8), lt_dbl(s9, A.one_le_shift(9n, one, h1)))
  +ha = V.le_fit(a, Nat.add(s8, s8), 10n, one, h1, l10, V.add_le(h, [5], s8, s8, V.fit_le(h, 8n, one, h1, hf), h5, hf1))
  +hal = V.len_add(h, [5], 17n, N.eq_le(V.len(h), 17n, hl), {==})
  +ce = V.carry_ev(16n, a, 0, 2n, {==}, ha, {==})
  +sk = V.skip_long(17n, a, hal)
  A.tr(V.ev(gg(h)), Nat.add(V.ev(gg(h)), V.pos(17n, V.ev(Li.skip(17n, a)))), Nat.add(V.ev(h), 5n),
    A.tr(V.ev(gg(h)), Nat.add(V.ev(gg(h)), 0n), Nat.add(V.ev(gg(h)), V.pos(17n, V.ev(Li.skip(17n, a)))), A.sy(Nat.add(V.ev(gg(h)), 0n), V.ev(gg(h)), N.add_zero(V.ev(gg(h)))),
      Equal.cong(List<&2, U32>, Nat, l => Nat.add(V.ev(gg(h)), V.pos(17n, V.ev(l))), [], Li.skip(17n, a), Equal.sym(List<&2, U32>, Li.skip(17n, a), [], sk))),
    A.tr(Nat.add(V.ev(gg(h)), V.pos(17n, V.ev(Li.skip(17n, a)))), V.ev(a), Nat.add(V.ev(h), 5n), ce, ea))

def lenh(+h: List<&2, U32>, +hh: {ST.inv(h) == True{} : Bool}) -> {V.len(h) == 17n : Nat}:
  N.eq_from_is_eq(V.len(h), 17n, L.and_left(Nat.is_eq(V.len(h), 17n), Bool.and(V.fit_all(h, 8n), Nat.is_le(V.v(Li.hd0(Li.skip(16n, h))), 4n)), hh))

def fith(+h: List<&2, U32>, +hh: {ST.inv(h) == True{} : Bool}) -> {V.fit_all(h, 8n) == True{} : Bool}:
  L.and_left(V.fit_all(h, 8n), Nat.is_le(V.v(Li.hd0(Li.skip(16n, h))), 4n), L.and_right(Nat.is_eq(V.len(h), 17n), Bool.and(V.fit_all(h, 8n), Nat.is_le(V.v(Li.hd0(Li.skip(16n, h))), 4n)), hh))

def toph(+h: List<&2, U32>, +hh: {ST.inv(h) == True{} : Bool}) -> {Nat.is_le(V.v(Li.hd0(Li.skip(16n, h))), 4n) == True{} : Bool}:
  L.and_right(V.fit_all(h, 8n), Nat.is_le(V.v(Li.hd0(Li.skip(16n, h))), 4n), L.and_right(Nat.is_eq(V.len(h), 17n), Bool.and(V.fit_all(h, 8n), Nat.is_le(V.v(Li.hd0(Li.skip(16n, h))), 4n)), hh))

def len16(+h: List<&2, U32>, +hh: {ST.inv(h) == True{} : Bool}) -> {V.len(Li.take(16n, h)) == 16n : Nat}:
  len_take_eq(16n, h, A.le_subst(16n, 17n, V.len(h), A.sy(V.len(h), 17n, lenh(h, hh)), {==}))

law hsplit:
  for +h: List<&2, U32>
  for +hh: {ST.inv(h) == True{} : Bool}
  {V.ev(h) == Nat.add(V.ev(Li.take(16n, h)), V.pos(16n, V.v(Li.hd0(Li.skip(16n, h))))) : Nat}

def hsplit(h, hh):
  +sk = Li.skip(16n, h)
  A.tr(V.ev(h), Nat.add(V.ev(Li.take(16n, h)), V.pos(16n, V.ev(sk))), Nat.add(V.ev(Li.take(16n, h)), V.pos(16n, V.v(Li.hd0(sk)))), V.ts_ev(16n, h),
    WM.cong_r(V.ev(Li.take(16n, h)), V.pos(16n, V.ev(sk)), V.pos(16n, V.v(Li.hd0(sk))), Equal.cong(Nat, Nat, z => V.pos(16n, z), V.ev(sk), V.v(Li.hd0(sk)),
      V.ev_one(sk, V.len_skip(16n, h, 1n, N.eq_le(V.len(h), 17n, lenh(h, hh)))))))

# ev(h) < 2^128 + 2^130
law hlt:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  for +h: List<&2, U32>
  for +hh: {ST.inv(h) == True{} : Bool}
  {Nat.is_lt(V.ev(h), Nat.add(V.pos(16n, one), C.shift(130n, one))) == True{} : Bool}

def hlt(one, h1, h, hh):
  +lh = V.ev(Li.take(16n, h))
  +vt = V.v(Li.hd0(Li.skip(16n, h)))
  +u = V.pos(16n, one)
  +l1 = A.lt_subst(lh, V.pos(V.len(Li.take(16n, h)), one), u, Equal.cong(Nat, Nat, z => V.pos(z, one), V.len(Li.take(16n, h)), 16n, len16(h, hh)), V.ev_lt(Li.take(16n, h), one, h1, V.fit_take(16n, h, 8n, fith(h, hh))))
  +e4 = A.sy(C.shift(2n, one), 4n, Equal.cong(Nat, Nat, z => C.shift(2n, z), one, 1n, h1))
  +l2 = WW.shift_mono(128n, vt, C.shift(2n, one), A.le_subst(vt, 4n, C.shift(2n, one), e4, toph(h, hh)))
  A.lt_substl(Nat.add(lh, V.pos(16n, vt)), V.ev(h), Nat.add(u, C.shift(130n, one)), A.sy(V.ev(h), Nat.add(lh, V.pos(16n, vt)), hsplit(h, hh)), A.lt_le_add(lh, V.pos(16n, vt), u, C.shift(130n, one), l1, l2))

def lg(+h: List<&2, U32>) -> Nat:
  V.ev(Li.take(16n, gg(h)))

def tg(+h: List<&2, U32>) -> Nat:
  Nat.add(V.v(Li.hd0(Li.skip(16n, gg(h)))), 0n)

law gsplit:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  for +h: List<&2, U32>
  for +hh: {ST.inv(h) == True{} : Bool}
  {Nat.add(V.ev(h), 5n) == Nat.add(lg(h), C.shift(128n, tg(h))) : Nat}

def gsplit(one, h1, h, hh):
  A.tr(Nat.add(V.ev(h), 5n), V.ev(gg(h)), Nat.add(lg(h), C.shift(128n, tg(h))), A.sy(V.ev(gg(h)), Nat.add(V.ev(h), 5n), g_ev(one, h1, h, hh)), V.ts_ev(16n, gg(h)))

def flg(+one: Nat, +h1: {one == 1n : Nat}, +h: List<&2, U32>) -> {C.fits(128n, lg(h)) == True{} : Bool}:
  WW.fits_one(128n, one, h1, lg(h), V.ev_lt(Li.take(16n, gg(h)), one, h1, V.carry_lo(16n, Li.add(h, [5]), 0)))

def bb(+h: List<&2, U32>) -> U32:
  U32.shrn(Li.hd0(Li.skip(16n, gg(h))), 2n)

law bval:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  for +h: List<&2, U32>
  for +hh: {ST.inv(h) == True{} : Bool}
  {V.v(bb(h)) == qq(h) : Nat}

def bval(one, h1, h, hh):
  +x = Nat.add(V.ev(h), 5n)
  +tp = V.v(Li.hd0(Li.skip(16n, gg(h))))
  +ehi = A.tr(C.high(128n, x), C.high(128n, Nat.add(lg(h), C.shift(128n, tg(h)))), tg(h), Equal.cong(Nat, Nat, z => C.high(128n, z), x, Nat.add(lg(h), C.shift(128n, tg(h))), gsplit(one, h1, h, hh)), WW.high_u(128n, lg(h), tg(h), flg(one, h1, h)))
  A.tr(V.v(bb(h)), C.high(2n, tp), qq(h), SHN.shrn_high(Li.hd0(Li.skip(16n, gg(h))), 2n),
    A.tr(C.high(2n, tp), C.high(2n, C.high(128n, x)), qq(h), Equal.cong(Nat, Nat, z => C.high(2n, z), tp, C.high(128n, x), A.tr(tp, tg(h), C.high(128n, x), A.sy(tg(h), tp, N.add_zero(tp)), A.sy(C.high(128n, x), tg(h), ehi))),
      A.sy(qq(h), C.high(2n, C.high(128n, x)), WW.high_comp(2n, 128n, x))))

# 2^128 + 5 <= 2^130, 16 <= 2^128
def u16(+one: Nat, +h1: {one == 1n : Nat}) -> {Nat.is_le(16n, V.pos(16n, one)) == True{} : Bool}:
  N.le_trans(16n, C.shift(4n, one), V.pos(16n, one), L.subst(Nat, z => {Nat.is_le(16n, C.shift(4n, z)) == True{} : Bool}, 1n, one, A.sy(one, 1n, h1), {==}), WW.shift_ge(124n, C.shift(4n, one)))

def uu(+one: Nat, +h1: {one == 1n : Nat}) -> {Nat.is_le(Nat.add(V.pos(16n, one), V.pos(16n, one)), C.shift(130n, one)) == True{} : Bool}:
  +u = V.pos(16n, one)
  A.le_substl(Nat.double(u), Nat.add(u, u), C.shift(130n, one), NA.double_self(u), WW.shift_ge(1n, Nat.double(u)))

law qlt2:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  for +h: List<&2, U32>
  for +hh: {ST.inv(h) == True{} : Bool}
  {Nat.is_lt(qq(h), 2n) == True{} : Bool}

def qlt2(one, h1, h, hh):
  +u = V.pos(16n, one)
  +s = C.shift(130n, one)
  +x = Nat.add(V.ev(h), 5n)
  +l1 = N.lt_add_r2(V.ev(h), Nat.add(u, s), 5n, hlt(one, h1, h, hh))
  +e1 = A.tr(Nat.add(Nat.add(u, s), 5n), Nat.add(u, Nat.add(s, 5n)), Nat.add(s, Nat.add(u, 5n)), N.add_assoc(u, s, 5n), A.tr(Nat.add(u, Nat.add(s, 5n)), Nat.add(u, Nat.add(5n, s)), Nat.add(s, Nat.add(u, 5n)), WM.cong_r(u, Nat.add(s, 5n), Nat.add(5n, s), N.add_comm(s, 5n)), A.tr(Nat.add(u, Nat.add(5n, s)), Nat.add(Nat.add(u, 5n), s), Nat.add(s, Nat.add(u, 5n)), A.sy(Nat.add(Nat.add(u, 5n), s), Nat.add(u, Nat.add(5n, s)), N.add_assoc(u, 5n, s)), N.add_comm(Nat.add(u, 5n), s))))
  +l2 = N.le_add_left(Nat.add(u, 5n), s, s, N.le_trans(Nat.add(u, 5n), Nat.add(u, u), s, N.le_add_left(5n, u, u, N.le_trans(5n, 16n, u, {==}, u16(one, h1))), uu(one, h1)))
  +l3 = N.lt_le_trans(x, Nat.add(s, Nat.add(u, 5n)), Nat.add(s, s), A.lt_subst(x, Nat.add(Nat.add(u, s), 5n), Nat.add(s, Nat.add(u, 5n)), e1, l1), l2)
  +f131 = WW.fits_one(131n, one, h1, x, A.lt_subst(x, Nat.add(s, s), Nat.double(s), A.sy(Nat.double(s), Nat.add(s, s), NA.double_self(s)), l3))
  WW.lt_of_fits(1n, qq(h), SH.fits_high(130n, 1n, x, f131))

def heqlen(+h: List<&2, U32>, +hh: {ST.inv(h) == True{} : Bool}) -> {V.len(Li.take(16n, h)) == V.len(Li.take(16n, gg(h))) : Nat}:
  A.tr(V.len(Li.take(16n, h)), 16n, V.len(Li.take(16n, gg(h))), len16(h, hh), {==})

def qone(+one: Nat, +h1: {one == 1n : Nat}, +h: List<&2, U32>, +hh: {ST.inv(h) == True{} : Bool}, +hc: {Nat.is_eq(qq(h), 0n) == False{} : Bool}) -> {qq(h) == 1n : Nat}:
  N.le_antisym(qq(h), 1n, N.lt_succ_le(qq(h), 1n, qlt2(one, h1, h, hh)), N.lt_succ_le_succ(0n, qq(h), N.lt_or_eq(0n, qq(h), N.zero_le(qq(h)), N.is_eq_sym_false(qq(h), 0n, hc))))

def which0(+one: Nat, +h1: {one == 1n : Nat}, +h: List<&2, U32>, +hh: {ST.inv(h) == True{} : Bool}, +hc: {Nat.is_eq(qq(h), 0n) == True{} : Bool}) -> {Li.freeze(h) == Li.take(16n, h) : List<&2, U32>}:
  +eb = U3.injective(bb(h), 0, A.tr(V.v(bb(h)), qq(h), 0n, bval(one, h1, h, hh), N.eq_from_is_eq(qq(h), 0n, hc)))
  Equal.trans(List<&2, U32>, Li.freeze(h), Li.select(U32.sub(0, 0), Li.take(16n, h), Li.take(16n, gg(h))), Li.take(16n, h),
    Equal.cong(U32, List<&2, U32>, w => Li.select(U32.sub(0, w), Li.take(16n, h), Li.take(16n, gg(h))), bb(h), 0, eb),
    sel0(Li.take(16n, h), Li.take(16n, gg(h)), heqlen(h, hh)))

def which1(+one: Nat, +h1: {one == 1n : Nat}, +h: List<&2, U32>, +hh: {ST.inv(h) == True{} : Bool}, +hc: {Nat.is_eq(qq(h), 0n) == False{} : Bool}) -> {Li.freeze(h) == Li.take(16n, gg(h)) : List<&2, U32>}:
  +eb = U3.injective(bb(h), 1, A.tr(V.v(bb(h)), qq(h), 1n, bval(one, h1, h, hh), qone(one, h1, h, hh, hc)))
  Equal.trans(List<&2, U32>, Li.freeze(h), Li.select(U32.sub(0, 1), Li.take(16n, h), Li.take(16n, gg(h))), Li.take(16n, gg(h)),
    Equal.cong(U32, List<&2, U32>, w => Li.select(U32.sub(0, w), Li.take(16n, h), Li.take(16n, gg(h))), bb(h), 1, eb),
    sel1(Li.take(16n, h), Li.take(16n, gg(h)), heqlen(h, hh)))

def which_c(+one: Nat, +h1: {one == 1n : Nat}, +h: List<&2, U32>, +hh: {ST.inv(h) == True{} : Bool}, +c: Bool, +hc: {Nat.is_eq(qq(h), 0n) == c : Bool}) -> Or({Li.freeze(h) == Li.take(16n, h) : List<&2, U32>}, {Li.freeze(h) == Li.take(16n, gg(h)) : List<&2, U32>}):
  match c:
    case True{}: Inl{which0(one, h1, h, hh, hc)}
    case False{}: Inr{which1(one, h1, h, hh, hc)}

def fz_fit_o(+h: List<&2, U32>, +hh: {ST.inv(h) == True{} : Bool}, o: Or({Li.freeze(h) == Li.take(16n, h) : List<&2, U32>}, {Li.freeze(h) == Li.take(16n, gg(h)) : List<&2, U32>})) -> {V.fit_all(Li.freeze(h), 8n) == True{} : Bool}:
  match o:
    case Inl{e}: L.subst(List<&2, U32>, l => {V.fit_all(l, 8n) == True{} : Bool}, Li.take(16n, h), Li.freeze(h), Equal.sym(List<&2, U32>, Li.freeze(h), Li.take(16n, h), e), V.fit_take(16n, h, 8n, fith(h, hh)))
    case Inr{e}: L.subst(List<&2, U32>, l => {V.fit_all(l, 8n) == True{} : Bool}, Li.take(16n, gg(h)), Li.freeze(h), Equal.sym(List<&2, U32>, Li.freeze(h), Li.take(16n, gg(h)), e), V.carry_lo(16n, Li.add(h, [5]), 0))

law freeze_fit:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  for +h: List<&2, U32>
  for +hh: {ST.inv(h) == True{} : Bool}
  {V.fit_all(Li.freeze(h), 8n) == True{} : Bool}

def freeze_fit(one, h1, h, hh):
  fz_fit_o(h, hh, which_c(one, h1, h, hh, Nat.is_eq(qq(h), 0n), {==}))

law freeze_len:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  for +h: List<&2, U32>
  for +hh: {ST.inv(h) == True{} : Bool}
  {Nat.is_le(V.len(Li.freeze(h)), 16n) == True{} : Bool}

def fz_len_o(+h: List<&2, U32>, o: Or({Li.freeze(h) == Li.take(16n, h) : List<&2, U32>}, {Li.freeze(h) == Li.take(16n, gg(h)) : List<&2, U32>})) -> {Nat.is_le(V.len(Li.freeze(h)), 16n) == True{} : Bool}:
  match o:
    case Inl{e}: L.subst(List<&2, U32>, l => {Nat.is_le(V.len(l), 16n) == True{} : Bool}, Li.take(16n, h), Li.freeze(h), Equal.sym(List<&2, U32>, Li.freeze(h), Li.take(16n, h), e), V.len_take(16n, h))
    case Inr{e}: L.subst(List<&2, U32>, l => {Nat.is_le(V.len(l), 16n) == True{} : Bool}, Li.take(16n, gg(h)), Li.freeze(h), Equal.sym(List<&2, U32>, Li.freeze(h), Li.take(16n, gg(h)), e), V.len_take(16n, gg(h)))

def freeze_len(one, h1, h, hh):
  fz_len_o(h, which_c(one, h1, h, hh, Nat.is_eq(qq(h), 0n), {==}))

# the value: the low 128 bits of h mod p
def frz_c(+one: Nat, +h1: {one == 1n : Nat}, +bp: Nat, +h5: {Nat.add(1n+bp, 5n) == C.shift(130n, one) : Nat}, +h: List<&2, U32>, +hh: {ST.inv(h) == True{} : Bool}, +c: Bool, +hc: {Nat.is_eq(qq(h), 0n) == c : Bool}) -> {V.ev(Li.freeze(h)) == C.low(128n, Nat.mod(V.ev(h), 1n+bp)) : Nat}:
  match c:
    case True{}:
      +pp = {1n+bp : Nat}
      +x = Nat.add(V.ev(h), 5n)
      +lh = V.ev(Li.take(16n, h))
      +vt = V.v(Li.hd0(Li.skip(16n, h)))
      +ef = Equal.cong(List<&2, U32>, Nat, l => V.ev(l), Li.freeze(h), Li.take(16n, h), which0(one, h1, h, hh, hc))
      +lx = A.lt_subst(x, C.shift(130n, one), Nat.add(pp, 5n), A.sy(Nat.add(pp, 5n), C.shift(130n, one), h5), WW.lt_one(130n, one, h1, x, hc))
      +lp = A.btrue(Nat.is_lt(V.ev(h), pp), Nat.is_lt(x, Nat.add(pp, 5n)), Equal.sym(Bool, Nat.is_lt(x, Nat.add(pp, 5n)), Nat.is_lt(V.ev(h), pp), WW.lt_cancel_r(V.ev(h), pp, 5n)), lx)
      +em = NR.mod_of(0n, bp, V.ev(h), lp)
      +flh = WW.fits_one(128n, one, h1, lh, A.lt_subst(lh, V.pos(V.len(Li.take(16n, h)), one), V.pos(16n, one), Equal.cong(Nat, Nat, z => V.pos(z, one), V.len(Li.take(16n, h)), 16n, len16(h, hh)), V.ev_lt(Li.take(16n, h), one, h1, V.fit_take(16n, h, 8n, fith(h, hh)))))
      +el = A.tr(C.low(128n, V.ev(h)), C.low(128n, Nat.add(lh, V.pos(16n, vt))), lh, Equal.cong(Nat, Nat, z => C.low(128n, z), V.ev(h), Nat.add(lh, V.pos(16n, vt)), hsplit(h, hh)), WW.low_u(128n, lh, vt, flh))
      A.tr(V.ev(Li.freeze(h)), lh, C.low(128n, Nat.mod(V.ev(h), pp)), ef,
        A.sy(C.low(128n, Nat.mod(V.ev(h), pp)), lh, A.tr(C.low(128n, Nat.mod(V.ev(h), pp)), C.low(128n, V.ev(h)), lh, Equal.cong(Nat, Nat, z => C.low(128n, z), Nat.mod(V.ev(h), pp), V.ev(h), em), el)))
    case False{}:
      +pp = {1n+bp : Nat}
      +s = C.shift(130n, one)
      +u = V.pos(16n, one)
      +x = Nat.add(V.ev(h), 5n)
      +d = C.low(130n, x)
      +q = qq(h)
      +ef = Equal.cong(List<&2, U32>, Nat, l => V.ev(l), Li.freeze(h), Li.take(16n, gg(h)), which1(one, h1, h, hh, hc))
      +eq1 = qone(one, h1, h, hh, hc)
      +es = A.tr(C.shift(130n, q), Nat.mul(q, s), s, WW.shift_mul_one(130n, one, h1, q), A.tr(Nat.mul(q, s), Nat.mul(1n, s), s, Equal.cong(Nat, Nat, z => Nat.mul(z, s), q, 1n, eq1), AR.one_mul(s)))
      +ex = A.tr(x, Nat.add(d, C.shift(130n, q)), Nat.add(d, s), WW.low_high(130n, x), WM.cong_r(d, C.shift(130n, q), s, es))
      +ex2 = A.tr(Nat.add(V.ev(h), 5n), Nat.add(d, Nat.add(pp, 5n)), Nat.add(Nat.add(d, pp), 5n), A.tr(x, Nat.add(d, s), Nat.add(d, Nat.add(pp, 5n)), ex, WM.cong_r(d, s, Nat.add(pp, 5n), A.sy(Nat.add(pp, 5n), s, h5))), A.sy(Nat.add(Nat.add(d, pp), 5n), Nat.add(d, Nat.add(pp, 5n)), N.add_assoc(d, pp, 5n)))
      +eh = UA.add_cancel_r(V.ev(h), Nat.add(d, pp), 5n, ex2)
      # d < 2^128 + 5 <= p
      +l1 = N.lt_add_r2(V.ev(h), Nat.add(u, s), 5n, hlt(one, h1, h, hh))
      +e1 = A.tr(Nat.add(Nat.add(u, s), 5n), Nat.add(u, Nat.add(s, 5n)), Nat.add(Nat.add(u, 5n), s), N.add_assoc(u, s, 5n), A.tr(Nat.add(u, Nat.add(s, 5n)), Nat.add(u, Nat.add(5n, s)), Nat.add(Nat.add(u, 5n), s), WM.cong_r(u, Nat.add(s, 5n), Nat.add(5n, s), N.add_comm(s, 5n)), A.sy(Nat.add(Nat.add(u, 5n), s), Nat.add(u, Nat.add(5n, s)), N.add_assoc(u, 5n, s))))
      +l2 = A.lt_substl(x, Nat.add(d, s), Nat.add(Nat.add(u, 5n), s), ex, A.lt_subst(x, Nat.add(Nat.add(u, s), 5n), Nat.add(Nat.add(u, 5n), s), e1, l1))
      +ld = A.btrue(Nat.is_lt(d, Nat.add(u, 5n)), Nat.is_lt(Nat.add(d, s), Nat.add(Nat.add(u, 5n), s)), Equal.sym(Bool, Nat.is_lt(Nat.add(d, s), Nat.add(Nat.add(u, 5n), s)), Nat.is_lt(d, Nat.add(u, 5n)), WW.lt_cancel_r(d, Nat.add(u, 5n), s)), l2)
      +l9 = N.lt_le_trans(Nat.add(u, 9n), Nat.add(u, u), s, N.lt_add_left(9n, u, u, N.lt_le_trans(9n, 16n, u, {==}, u16(one, h1))), uu(one, h1))
      +l9b = A.lt_substl(Nat.add(u, 9n), Nat.add(Nat.add(u, 4n), 5n), Nat.add(pp, 5n), A.sy(Nat.add(Nat.add(u, 4n), 5n), Nat.add(u, 9n), N.add_assoc(u, 4n, 5n)), A.lt_subst(Nat.add(u, 9n), s, Nat.add(pp, 5n), A.sy(Nat.add(pp, 5n), s, h5), l9))
      +l4 = A.btrue(Nat.is_lt(Nat.add(u, 4n), pp), Nat.is_lt(Nat.add(Nat.add(u, 4n), 5n), Nat.add(pp, 5n)), Equal.sym(Bool, Nat.is_lt(Nat.add(Nat.add(u, 4n), 5n), Nat.add(pp, 5n)), Nat.is_lt(Nat.add(u, 4n), pp), WW.lt_cancel_r(Nat.add(u, 4n), pp, 5n)), l9b)
      +l5 = A.le_substl(1n+Nat.add(u, 4n), Nat.add(u, 5n), pp, A.sy(Nat.add(u, 5n), 1n+Nat.add(u, 4n), N.add_succ(u, 4n)), N.lt_succ_le_succ(Nat.add(u, 4n), pp, l4))
      +ldp = N.lt_le_trans(d, Nat.add(u, 5n), pp, ld, l5)
      +em = A.tr(Nat.mod(V.ev(h), pp), Nat.mod(Nat.add(Nat.mul(1n, pp), d), pp), d,
        Equal.cong(Nat, Nat, z => Nat.mod(z, pp), V.ev(h), Nat.add(Nat.mul(1n, pp), d), A.tr(V.ev(h), Nat.add(d, pp), Nat.add(Nat.mul(1n, pp), d), eh, A.tr(Nat.add(d, pp), Nat.add(pp, d), Nat.add(Nat.mul(1n, pp), d), N.add_comm(d, pp), WM.cong_l(pp, Nat.mul(1n, pp), d, A.sy(Nat.mul(1n, pp), pp, AR.one_mul(pp)))))),
        NR.mod_of(1n, bp, d, ldp))
      +elg = A.tr(lg(h), C.low(128n, x), C.low(128n, d),
        A.sy(C.low(128n, x), lg(h), A.tr(C.low(128n, x), C.low(128n, Nat.add(lg(h), C.shift(128n, tg(h)))), lg(h), Equal.cong(Nat, Nat, z => C.low(128n, z), x, Nat.add(lg(h), C.shift(128n, tg(h))), gsplit(one, h1, h, hh)), WW.low_u(128n, lg(h), tg(h), flg(one, h1, h)))),
        A.tr(C.low(128n, x), C.low(128n, Nat.add(d, s)), C.low(128n, d), Equal.cong(Nat, Nat, z => C.low(128n, z), x, Nat.add(d, s), ex), WW.low_add_shift(128n, d, C.shift(2n, one))))
      A.tr(V.ev(Li.freeze(h)), lg(h), C.low(128n, Nat.mod(V.ev(h), pp)), ef,
        A.tr(lg(h), C.low(128n, d), C.low(128n, Nat.mod(V.ev(h), pp)), elg, Equal.cong(Nat, Nat, z => C.low(128n, z), d, Nat.mod(V.ev(h), pp), A.sy(Nat.mod(V.ev(h), pp), d, em))))

law freeze_ev:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  for +bp: Nat
  for +h5: {Nat.add(1n+bp, 5n) == C.shift(130n, one) : Nat}
  for +h: List<&2, U32>
  for +hh: {ST.inv(h) == True{} : Bool}
  {V.ev(Li.freeze(h)) == C.low(128n, Nat.mod(V.ev(h), 1n+bp)) : Nat}

def freeze_ev(one, h1, bp, h5, h, hh):
  frz_c(one, h1, bp, h5, h, hh, Nat.is_eq(qq(h), 0n), {==})

# ---- the tag bytes ----

law bytes_le:
  for +n: Nat
  for +ds: List<&2, U32>
  for +u: U32
  for +k: Nat
  for +j: Nat
  for +hj: {Nat.is_le(Nat.add(9n, j), 32n) == True{} : Bool}
  for +hd: {V.fit_all(ds, Nat.add(8n, j)) == True{} : Bool}
  for +hu: {C.fits(Nat.add(8n, j), V.v(u)) == True{} : Bool}
  {Li.bytes(n, ds, u) == R.le_bytes(n, Nat.add(Nat.add(V.v(u), V.ev(ds)), V.pos(n, k))) : List<&2, U32>}

def bytes_le(n, ds, u, k, j, hj, hd, hu):
  match n:
    case 0n: {==}
    case 1n+m:
      +h = Li.hd0(ds)
      +s = U32.add(u, h)
      +vs = V.v(s)
      +u2 = U32.shrn(s, 8n)
      +et = V.ev(Li.tl(ds))
      +pk = V.pos(m, k)
      +y = Nat.add(Nat.add(V.v(u), V.ev(ds)), C.shift(8n, pk))
      +y2 = Nat.add(vs, C.shift(8n, Nat.add(et, pk)))
      +es = V.step_ev(ds, u, j, hj, hd, hu)
      +ey = A.tr(y, Nat.add(Nat.add(V.v(u), Nat.add(V.v(h), C.shift(8n, et))), C.shift(8n, pk)), y2,
        WM.cong_l(Nat.add(V.v(u), V.ev(ds)), Nat.add(V.v(u), Nat.add(V.v(h), C.shift(8n, et))), C.shift(8n, pk), WM.cong_r(V.v(u), V.ev(ds), Nat.add(V.v(h), C.shift(8n, et)), V.hd_tl_ev(ds))),
        A.tr(Nat.add(Nat.add(V.v(u), Nat.add(V.v(h), C.shift(8n, et))), C.shift(8n, pk)), Nat.add(Nat.add(Nat.add(V.v(u), V.v(h)), C.shift(8n, et)), C.shift(8n, pk)), y2,
          WM.cong_l(Nat.add(V.v(u), Nat.add(V.v(h), C.shift(8n, et))), Nat.add(Nat.add(V.v(u), V.v(h)), C.shift(8n, et)), C.shift(8n, pk), A.sy(Nat.add(Nat.add(V.v(u), V.v(h)), C.shift(8n, et)), Nat.add(V.v(u), Nat.add(V.v(h), C.shift(8n, et))), N.add_assoc(V.v(u), V.v(h), C.shift(8n, et)))),
          A.tr(Nat.add(Nat.add(Nat.add(V.v(u), V.v(h)), C.shift(8n, et)), C.shift(8n, pk)), Nat.add(Nat.add(V.v(u), V.v(h)), C.shift(8n, Nat.add(et, pk))), y2,
            V.sh3(Nat.add(V.v(u), V.v(h)), et, pk),
            WM.cong_l(Nat.add(V.v(u), V.v(h)), vs, C.shift(8n, Nat.add(et, pk)), A.sy(vs, Nat.add(V.v(u), V.v(h)), es)))))
      +elo = WW.low_add_shift(8n, vs, Nat.add(et, pk))
      +ehi = A.tr(C.high(8n, y2), Nat.add(C.high(8n, vs), Nat.add(et, pk)), Nat.add(Nat.add(V.v(u2), et), pk), WW.high_add_shift(8n, vs, Nat.add(et, pk)),
        A.tr(Nat.add(C.high(8n, vs), Nat.add(et, pk)), Nat.add(V.v(u2), Nat.add(et, pk)), Nat.add(Nat.add(V.v(u2), et), pk), WM.cong_l(C.high(8n, vs), V.v(u2), Nat.add(et, pk), A.sy(V.v(u2), C.high(8n, vs), SHN.shrn_high(s, 8n))), A.sy(Nat.add(Nat.add(V.v(u2), et), pk), Nat.add(V.v(u2), Nat.add(et, pk)), N.add_assoc(V.v(u2), et, pk))))
      +lo8 = C.low(8n, vs)
      +eb = U3.injective(U32.and(s, 255), U32.from_nat(lo8), A.tr(V.v(U32.and(s, 255)), lo8, V.v(U32.from_nat(lo8)), FB.andm(s, 8n, 255, {==}), A.sy(V.v(U32.from_nat(lo8)), lo8, U3.to_nat_from_nat(lo8, 8n, {==}, WW.low_lt(8n, vs)))))
      +ih = bytes_le(m, Li.tl(ds), u2, k, j, hj, V.tl_fit(ds, Nat.add(8n, j), hd), V.next_fit(ds, u, j, hj, hd, hu))
      Equal.trans(List<&2, U32>, U32.and(s, 255) <> Li.bytes(m, Li.tl(ds), u2), R.le_bytes(1n+m, y2), R.le_bytes(1n+m, y),
        Equal.trans(List<&2, U32>, U32.and(s, 255) <> Li.bytes(m, Li.tl(ds), u2), U32.from_nat(lo8) <> R.le_bytes(m, Nat.add(Nat.add(V.v(u2), et), pk)), R.le_bytes(1n+m, y2),
          Equal.trans(List<&2, U32>, U32.and(s, 255) <> Li.bytes(m, Li.tl(ds), u2), U32.from_nat(lo8) <> Li.bytes(m, Li.tl(ds), u2), U32.from_nat(lo8) <> R.le_bytes(m, Nat.add(Nat.add(V.v(u2), et), pk)),
            Equal.cong(U32, List<&2, U32>, z => z <> Li.bytes(m, Li.tl(ds), u2), U32.and(s, 255), U32.from_nat(lo8), eb),
            Equal.cong(List<&2, U32>, List<&2, U32>, z => U32.from_nat(lo8) <> z, Li.bytes(m, Li.tl(ds), u2), R.le_bytes(m, Nat.add(Nat.add(V.v(u2), et), pk)), ih)),
          Equal.trans(List<&2, U32>, U32.from_nat(lo8) <> R.le_bytes(m, Nat.add(Nat.add(V.v(u2), et), pk)), U32.from_nat(C.low(8n, y2)) <> R.le_bytes(m, Nat.add(Nat.add(V.v(u2), et), pk)), R.le_bytes(1n+m, y2),
            Equal.cong(Nat, List<&2, U32>, z => U32.from_nat(z) <> R.le_bytes(m, Nat.add(Nat.add(V.v(u2), et), pk)), lo8, C.low(8n, y2), A.sy(C.low(8n, y2), lo8, elo)),
            Equal.cong(Nat, List<&2, U32>, z => U32.from_nat(C.low(8n, y2)) <> R.le_bytes(m, z), Nat.add(Nat.add(V.v(u2), et), pk), C.high(8n, y2), A.sy(C.high(8n, y2), Nat.add(Nat.add(V.v(u2), et), pk), ehi)))),
        Equal.cong(Nat, List<&2, U32>, z => R.le_bytes(1n+m, z), y2, y, A.sy(y, y2, ey)))

# the tag: (h mod p + s) mod 2^128 as 16 bytes
law tag_eq:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  for +bp: Nat
  for +h5: {Nat.add(1n+bp, 5n) == C.shift(130n, one) : Nat}
  for +h: List<&2, U32>
  for +hh: {ST.inv(h) == True{} : Bool}
  for +s: List<&2, U32>
  for +hs: {V.fit_all(s, 8n) == True{} : Bool}
  {Li.bytes(16n, Li.add(Li.freeze(h), s), 0) == R.le_bytes(16n, Nat.add(Nat.mod(V.ev(h), 1n+bp), V.ev(s))) : List<&2, U32>}

def tag_eq(one, h1, bp, h5, h, hh, s, hs):
  +s8 = C.shift(8n, one)
  +s9 = C.shift(9n, one)
  +fz = Li.freeze(h)
  +a = Nat.mod(V.ev(h), 1n+bp)
  +lo = C.low(128n, a)
  +kk = C.high(128n, a)
  +ds = Li.add(fz, s)
  +hf = freeze_fit(one, h1, h, hh)
  +hf1 = ST.s8fit(one, h1)
  +ed = V.add_ev(fz, s, s8, s8, V.fit_le(fz, 8n, one, h1, hf), V.fit_le(s, 8n, one, h1, hs), hf1)
  +l10 = A.lt_substl(s9, Nat.add(s8, s8), Nat.double(s9), NA.double_self(s8), lt_dbl(s9, A.one_le_shift(9n, one, h1)))
  +hd = V.le_fit(ds, Nat.add(s8, s8), 10n, one, h1, l10, V.add_le(fz, s, s8, s8, V.fit_le(fz, 8n, one, h1, hf), V.fit_le(s, 8n, one, h1, hs), hf1))
  +bl = bytes_le(16n, ds, 0, kk, 2n, {==}, hd, {==})
  # ev ds + 2^128 kk == a + ev s
  +e1 = A.tr(Nat.add(V.ev(ds), V.pos(16n, kk)), Nat.add(Nat.add(lo, V.ev(s)), V.pos(16n, kk)), Nat.add(a, V.ev(s)),
    WM.cong_l(V.ev(ds), Nat.add(lo, V.ev(s)), V.pos(16n, kk), A.tr(V.ev(ds), Nat.add(V.ev(fz), V.ev(s)), Nat.add(lo, V.ev(s)), ed, WM.cong_l(V.ev(fz), lo, V.ev(s), freeze_ev(one, h1, bp, h5, h, hh)))),
    A.tr(Nat.add(Nat.add(lo, V.ev(s)), V.pos(16n, kk)), Nat.add(Nat.add(lo, V.pos(16n, kk)), V.ev(s)), Nat.add(a, V.ev(s)),
      A.tr(Nat.add(Nat.add(lo, V.ev(s)), V.pos(16n, kk)), Nat.add(lo, Nat.add(V.ev(s), V.pos(16n, kk))), Nat.add(Nat.add(lo, V.pos(16n, kk)), V.ev(s)), N.add_assoc(lo, V.ev(s), V.pos(16n, kk)), ST.rot(lo, V.ev(s), V.pos(16n, kk))),
      WM.cong_l(Nat.add(lo, V.pos(16n, kk)), a, V.ev(s), A.sy(a, Nat.add(lo, V.pos(16n, kk)), WW.low_high(128n, a)))))
  Equal.trans(List<&2, U32>, Li.bytes(16n, ds, 0), R.le_bytes(16n, Nat.add(V.ev(ds), V.pos(16n, kk))), R.le_bytes(16n, Nat.add(a, V.ev(s))), bl,
    Equal.cong(Nat, List<&2, U32>, z => R.le_bytes(16n, z), Nat.add(V.ev(ds), V.pos(16n, kk)), Nat.add(a, V.ev(s)), e1))
