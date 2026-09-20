import Base
import ../src/host.bend as H
import ../spec/host.bend as S
import ../spec/numeric.bend as N
import ./host_decimal.bend as Dec
import ./host_binary.bend as Bin
import ./word_value.bend as Value
import ./nat_algebra.bend as A
import ./natural_products.bend as Product
import ./addition_bounds.bend as AddBounds
import ./negation_magnitude.bend as Magnitude
import ./counter.bend as Counter
import ./word_bounds.bend as WordBounds
import ./word_comparison.bend as Compare
import ./subtraction_bounds.bend as SubBounds
import ./division_quotient.bend as Quotient
import ./map_routing.bend as Routing

# Host integer text: the adapter's readers (src/host.bend) accept exactly the
# independent specification's in-range numerals with the specified word, and
# reject every other text with the given message. All statements are generic
# in the word width, so no large constant is ever evaluated by the checker.
def lift(-n: Nat, msg: String, m: Maybe<&2, Word(n)>) -> Result<&2, &2, String, Word(n)>:
  match m:
    case None{}: Fail{msg}
    case Some{w}: Done{w}

def clash(b: Bool, yes: {b == True{} : Bool}, no: {b == False{} : Bool}) -> Empty:
  Routing.false_true(Equal.trans(Bool, False{}, b, True{}, Equal.sym(Bool, b, False{}, no), yes))

def eq_refl(a: Nat) -> {Nat.is_eq(a, a) == True{} : Bool}:
  match a:
    case 0n: {==}
    case 1n+p: eq_refl(p)

def eq_sound(a: Nat, b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n: {==}
    case 0n 1n+bp: Empty.absurd({0n == 1n+bp : Nat}, Routing.false_true(h))
    case 1n+ap 0n: Empty.absurd({1n+ap == 0n : Nat}, Routing.false_true(h))
    case 1n+ap 1n+bp: Equal.cong(Nat, Nat, x => 1n+x, ap, bp, eq_sound(ap, bp, h))

# Every n-bit word's value is below 2^n (from word_bounds.unsigned_bound).
def unsigned_below(+n: Nat, +w: Word(n)) -> {Nat.is_lt(N.unsigned(n, w), Nat.pow(2n, n)) == True{} : Bool}:
  %Magnitude.scale_power(n) : {Nat.is_lt(N.unsigned(n, w), _) == True{} : Bool}
  WordBounds.unsigned_bound(n, w)

# Converse of fits_meaning: a value that survives the n-bit round trip is below
# 2^n. Together, fits(n, v) holds exactly when v < 2^n.
def fits_bound(+n: Nat, +v: Nat, h: {S.fits(n, v) == True{} : Bool}) -> {Nat.is_lt(v, Nat.pow(2n, n)) == True{} : Bool}:
  %eq_sound(N.unsigned(n, N.from_nat(n, v)), v, h) : {Nat.is_lt(_, Nat.pow(2n, n)) == True{} : Bool}
  unsigned_below(n, N.from_nat(n, v))

# fits(n, v) is v < 2^n.
def fits_meaning(+n: Nat, +v: Nat, h: {Nat.is_lt(v, Nat.pow(2n, n)) == True{} : Bool}) -> {S.fits(n, v) == True{} : Bool}:
  %Equal.sym(Nat, N.unsigned(n, N.from_nat(n, v)), v, Value.from_nat_value(n, v, h)) : {Nat.is_eq(_, v) == True{} : Bool}
  eq_refl(v)

def fits_self(+n: Nat, +w: Word(n)) -> {S.fits(n, N.unsigned(n, w)) == True{} : Bool}:
  %Equal.sym(Word(n), N.from_nat(n, N.unsigned(n, w)), w, Quotient.reconstruct(n, w)) : {Nat.is_eq(N.unsigned(n, _), N.unsigned(n, w)) == True{} : Bool}
  eq_refl(N.unsigned(n, w))

def double_positive(x: Nat, h: {Nat.is_lt(0n, x) == True{} : Bool}) -> {Nat.is_lt(0n, Nat.double(x)) == True{} : Bool}:
  match x:
    case 0n: h
    case 1n+p: {==}

def scale_positive(n: Nat) -> {Nat.is_lt(0n, N.scale_binary(n, 1n)) == True{} : Bool}:
  match n:
    case 0n: {==}
    case 1n++p: double_positive(N.scale_binary(p, 1n), scale_positive(p))

# u + 2^n * L with L >= 1 is not below 2^n.
def big(+n: Nat, +u: Nat, l: Nat, hl: {Nat.is_lt(0n, l) == True{} : Bool}) -> {Nat.is_lt(Nat.add(u, N.scale_binary(n, l)), N.scale_binary(n, 1n)) == False{} : Bool}:
  match l:
    case 0n: Empty.absurd({Nat.is_lt(Nat.add(u, N.scale_binary(n, 0n)), N.scale_binary(n, 1n)) == False{} : Bool}, Routing.false_true(hl))
    case 1n++lp:
      %Equal.sym(Nat, N.scale_binary(n, Nat.add(1n, lp)), Nat.add(N.scale_binary(n, 1n), N.scale_binary(n, lp)), Product.scale_sum(n, 1n, lp)) : {Nat.is_lt(Nat.add(u, _), N.scale_binary(n, 1n)) == False{} : Bool}
      %Equal.sym(Nat, Nat.add(u, Nat.add(N.scale_binary(n, 1n), N.scale_binary(n, lp))), Nat.add(N.scale_binary(n, 1n), Nat.add(u, N.scale_binary(n, lp))), A.add_swap(u, N.scale_binary(n, 1n), N.scale_binary(n, lp))) : {Nat.is_lt(_, N.scale_binary(n, 1n)) == False{} : Bool}
      %A.add_comm(Nat.add(u, N.scale_binary(n, lp)), N.scale_binary(n, 1n)) : {Nat.is_lt(_, N.scale_binary(n, 1n)) == False{} : Bool}
      AddBounds.offset_not_less(N.scale_binary(n, 1n), Nat.add(u, N.scale_binary(n, lp)))

def vanish(+n: Nat, +u: Nat, +l: Nat, zl: {l == 0n : Nat}) -> {Nat.add(u, N.scale_binary(n, l)) == u : Nat}:
  %Equal.sym(Nat, l, 0n, zl) : {Nat.add(u, N.scale_binary(n, _)) == u : Nat}
  %Equal.sym(Nat, N.scale_binary(n, 0n), 0n, Counter.scale_zero(n)) : {Nat.add(u, _) == u : Nat}
  A.add_zero(u)

def exact_value(+n: Nat, +w: Word(n), +left: List<&2, H.Digit>, +v: Nat, eq: {Nat.add(N.unsigned(n, w), N.scale_binary(n, Bin.hval(left, 0n))) == v : Nat}, z: {H.zeros(left) == True{} : Bool}) -> {N.unsigned(n, w) == v : Nat}:
  Equal.trans(Nat, N.unsigned(n, w), Nat.add(N.unsigned(n, w), N.scale_binary(n, Bin.hval(left, 0n))), v, Equal.sym(Nat, Nat.add(N.unsigned(n, w), N.scale_binary(n, Bin.hval(left, 0n))), N.unsigned(n, w), vanish(n, N.unsigned(n, w), Bin.hval(left, 0n), Bin.zero_value(left, z))), eq)

def large(+n: Nat, +w: Word(n), +left: List<&2, H.Digit>, +v: Nat, eq: {Nat.add(N.unsigned(n, w), N.scale_binary(n, Bin.hval(left, 0n))) == v : Nat}, z: {H.zeros(left) == False{} : Bool}) -> {Nat.is_lt(v, N.scale_binary(n, 1n)) == False{} : Bool}:
  %eq : {Nat.is_lt(_, N.scale_binary(n, 1n)) == False{} : Bool}
  big(n, N.unsigned(n, w), Bin.hval(left, 0n), Bin.positive(left, z))

def distinct(+a: Nat, +v: Nat, +x: Nat, ha: {Nat.is_lt(a, x) == True{} : Bool}, hv: {Nat.is_lt(v, x) == False{} : Bool}, b: Bool, eb: {Nat.is_eq(a, v) == b : Bool}) -> {Nat.is_eq(a, v) == False{} : Bool}:
  match b:
    case True{}: Empty.absurd({Nat.is_eq(a, v) == False{} : Bool}, clash(Nat.is_lt(v, x), Equal.trans(Bool, Nat.is_lt(v, x), Nat.is_lt(a, x), True{}, Equal.cong(Nat, Bool, y => Nat.is_lt(y, x), v, a, Equal.sym(Nat, a, v, eq_sound(a, v, eb))), ha), hv))
    case False{}: eb

# A value at least 2^n does not fit.
def no_fit(+n: Nat, +v: Nat, hv: {Nat.is_lt(v, N.scale_binary(n, 1n)) == False{} : Bool}) -> {S.fits(n, v) == False{} : Bool}:
  distinct(N.unsigned(n, N.from_nat(n, v)), v, N.scale_binary(n, 1n), WordBounds.unsigned_bound(n, N.from_nat(n, v)), hv, Nat.is_eq(N.unsigned(n, N.from_nat(n, v)), v), {==})

def fit_true(+n: Nat, msg: String, +w: Word(n), +v: Nat, same: {N.unsigned(n, w) == v : Nat}) -> {H.fit(n, msg, w, True{}) == lift(n, msg, S.fits_if(n, v, S.fits(n, v))) : Result<&2, &2, String, Word(n)>}:
  %same : {H.fit(n, msg, w, True{}) == lift(n, msg, S.fits_if(n, _, S.fits(n, _))) : Result<&2, &2, String, Word(n)>}
  %Equal.sym(Bool, S.fits(n, N.unsigned(n, w)), True{}, fits_self(n, w)) : {H.fit(n, msg, w, True{}) == lift(n, msg, S.fits_if(n, N.unsigned(n, w), _)) : Result<&2, &2, String, Word(n)>}
  Equal.cong(Word(n), Result<&2, &2, String, Word(n)>, x => Done{x}, w, N.from_nat(n, N.unsigned(n, w)), Equal.sym(Word(n), N.from_nat(n, N.unsigned(n, w)), w, Quotient.reconstruct(n, w)))

def fit_false(+n: Nat, msg: String, +w: Word(n), +left: List<&2, H.Digit>, +v: Nat, eq: {Nat.add(N.unsigned(n, w), N.scale_binary(n, Bin.hval(left, 0n))) == v : Nat}, z: {H.zeros(left) == False{} : Bool}) -> {H.fit(n, msg, w, False{}) == lift(n, msg, S.fits_if(n, v, S.fits(n, v))) : Result<&2, &2, String, Word(n)>}:
  %Equal.sym(Bool, S.fits(n, v), False{}, no_fit(n, v, large(n, w, left, v, eq, z))) : {H.fit(n, msg, w, False{}) == lift(n, msg, S.fits_if(n, v, _)) : Result<&2, &2, String, Word(n)>}
  {==}

def fit_bool(+n: Nat, msg: String, +w: Word(n), +left: List<&2, H.Digit>, +v: Nat, eq: {Nat.add(N.unsigned(n, w), N.scale_binary(n, Bin.hval(left, 0n))) == v : Nat}, b: Bool, +eb: {H.zeros(left) == b : Bool}) -> {H.fit(n, msg, w, H.zeros(left)) == lift(n, msg, S.fits_if(n, v, S.fits(n, v))) : Result<&2, &2, String, Word(n)>}:
  match b:
    case True{}:
      %Equal.sym(Bool, H.zeros(left), True{}, eb) : {H.fit(n, msg, w, _) == lift(n, msg, S.fits_if(n, v, S.fits(n, v))) : Result<&2, &2, String, Word(n)>}
      fit_true(n, msg, w, v, exact_value(n, w, left, v, eq, eb))
    case False{}:
      %Equal.sym(Bool, H.zeros(left), False{}, eb) : {H.fit(n, msg, w, _) == lift(n, msg, S.fits_if(n, v, S.fits(n, v))) : Result<&2, &2, String, Word(n)>}
      fit_false(n, msg, w, left, v, eq, eb)

def fit_pair(+n: Nat, msg: String, r: Word(n) & List<&2, H.Digit>, +v: Nat, eq: {Nat.add(N.unsigned(n, Bin.wd(n, r)), N.scale_binary(n, Bin.hval(Bin.lf(n, r), 0n))) == v : Nat}) -> {H.fit_pair(n, msg, r) == lift(n, msg, S.fits_if(n, v, S.fits(n, v))) : Result<&2, &2, String, Word(n)>}:
  (+w, +left) = r
  fit_bool(n, msg, w, left, v, eq, H.zeros(left), {==})

def fit_digits(+n: Nat, msg: String, m: Maybe<&2, List<&2, H.Digit>>) -> {H.fit_digits(n, msg, m) == lift(n, msg, S.bounded(n, Dec.hopt(0n, m))) : Result<&2, &2, String, Word(n)>}:
  match m:
    case None{}: {==}
    case Some{+ds}: fit_pair(n, msg, H.binary(n, ds), Bin.hval(ds, 0n), Bin.binary_value(n, ds))

# Unsigned readers: exactly the specification's natural numerals below 2^n.
def unsigned_word(+n: Nat, msg: String, +s: String) -> {H.unsigned_word(n, msg, s) == lift(n, msg, S.unsigned_text(n, s)) : Result<&2, &2, String, Word(n)>}:
  %Dec.numeral_value(s) : {H.unsigned_word(n, msg, s) == lift(n, msg, S.bounded(n, _)) : Result<&2, &2, String, Word(n)>}
  fit_digits(n, msg, H.numeral(s))

def threshold_same(n: Nat) -> {H.threshold(n) == N.sign_threshold(n) : Word(1n+n)}:
  match n:
    case 0n: {==}
    case 1n++p: Equal.cong(Word(1n+p), Word(2n+p), t => WCon{False{}, t}, H.threshold(p), N.sign_threshold(p), threshold_same(p))

def threshold_value(n: Nat) -> {N.unsigned(1n+n, H.threshold(n)) == N.scale_binary(n, 1n) : Nat}:
  match n:
    case 0n: {==}
    case 1n++p: Equal.cong(Nat, Nat, x => Nat.double(x), N.unsigned(1n+p, H.threshold(p)), N.scale_binary(p, 1n), threshold_value(p))

# The implementation's sign bit is the specification's.
def sign_same(+n: Nat, x: Word(1n+n)) -> {S.sign_bit(n, x) == H.sign_bit(n, x) : Bool}:
  %threshold_same(n) : {Cmp.is_ge(Word.cmp(1n+n, x, _)) == H.sign_bit(n, x) : Bool}
  {==}

# The sign bit is set exactly when the value is at least 2^n.
def sign_nat(+n: Nat, +x: Word(1n+n)) -> {H.sign_bit(n, x) == Nat.is_ge(N.unsigned(1n+n, x), N.scale_binary(n, 1n)) : Bool}:
  %Equal.sym(Cmp, Word.cmp(1n+n, x, H.threshold(n)), Nat.cmp(N.unsigned(1n+n, x), N.unsigned(1n+n, H.threshold(n))), Compare.refines(1n+n, x, H.threshold(n))) : {Cmp.is_ge(_) == Nat.is_ge(N.unsigned(1n+n, x), N.scale_binary(n, 1n)) : Bool}
  %Equal.sym(Nat, N.unsigned(1n+n, H.threshold(n)), N.scale_binary(n, 1n), threshold_value(n)) : {Cmp.is_ge(Nat.cmp(N.unsigned(1n+n, x), _)) == Nat.is_ge(N.unsigned(1n+n, x), N.scale_binary(n, 1n)) : Bool}
  {==}

def zero_value(n: Nat) -> {N.unsigned(n, Word.zero(n)) == 0n : Nat}:
  match n:
    case 0n: {==}
    case 1n+p: Equal.cong(Nat, Nat, x => Nat.double(x), N.unsigned(p, Word.zero(p)), 0n, zero_value(p))

def unit_value(+n: Nat) -> {N.unsigned(1n+n, H.unit(n)) == 1n : Nat}:
  Equal.cong(Nat, Nat, x => Nat.add(1n, Nat.double(x)), N.unsigned(n, Word.zero(n)), 0n, zero_value(n))

def nat_clash(k: Nat, e: {0n == 1n+k : Nat}) -> Empty:
  Routing.false_true(Equal.sym(Bool, True{}, False{}, Equal.cong(Nat, Bool, x => Nat.is_eq(x, 0n), 0n, 1n+k, e)))

def double_zero(u: Nat, h: {Nat.double(u) == 0n : Nat}) -> {u == 0n : Nat}:
  match u:
    case 0n: {==}
    case 1n+x: Empty.absurd({1n+x == 0n : Nat}, nat_clash(1n+Nat.double(x), Equal.sym(Nat, 2n+Nat.double(x), 0n, h)))

def zero_test_true(n: Nat, w: Word(n), h: {N.unsigned(n, w) == 0n : Nat}) -> {H.is_zero(n, w) == True{} : Bool}:
  match n:
    case 0n: {==}
    case 1n++p:
      match w:
        case WCon{b, +t}:
          match b:
            case True{}: Empty.absurd({H.is_zero(1n+p, WCon{True{}, t}) == True{} : Bool}, nat_clash(Nat.double(N.unsigned(p, t)), Equal.sym(Nat, 1n+Nat.double(N.unsigned(p, t)), 0n, h)))
            case False{}: zero_test_true(p, t, double_zero(N.unsigned(p, t), h))

def zero_step(+p: Nat, t: Word(p), +k: Nat, u: Nat, eu: {N.unsigned(p, t) == u : Nat}, h: {Nat.double(u) == 1n+k : Nat}, ih: @kk: Nat -> @e: {N.unsigned(p, t) == 1n+kk : Nat} -> {H.is_zero(p, t) == False{} : Bool}) -> {H.is_zero(p, t) == False{} : Bool}:
  match u:
    case 0n: Empty.absurd({H.is_zero(p, t) == False{} : Bool}, nat_clash(k, h))
    case 1n+x: ih(x, eu)

def zero_test_false(n: Nat, w: Word(n), +k: Nat, h: {N.unsigned(n, w) == 1n+k : Nat}) -> {H.is_zero(n, w) == False{} : Bool}:
  match n:
    case 0n: Empty.absurd({H.is_zero(0n, w) == False{} : Bool}, nat_clash(k, h))
    case 1n++p:
      match w:
        case WCon{b, +t}:
          match b:
            case True{}: {==}
            case False{}: zero_step(p, t, k, N.unsigned(p, t), {==}, h, kk => e => zero_test_false(p, t, kk, e))

def le_one(k: Nat) -> {Nat.is_le(1n, 1n+k) == True{} : Bool}:
  match k:
    case 0n: {==}
    case 1n+kk: {==}

def enough(+n: Nat, +w: Word(1n+n), +k: Nat, h: {N.unsigned(1n+n, w) == 1n+k : Nat}) -> {Nat.is_le(N.unsigned(1n+n, H.unit(n)), N.unsigned(1n+n, w)) == True{} : Bool}:
  %Equal.sym(Nat, N.unsigned(1n+n, H.unit(n)), 1n, unit_value(n)) : {Nat.is_le(_, N.unsigned(1n+n, w)) == True{} : Bool}
  %Equal.sym(Nat, N.unsigned(1n+n, w), 1n+k, h) : {Nat.is_le(1n, _) == True{} : Bool}
  le_one(k)

def sub_zero(k: Nat) -> {Nat.sub(k, 0n) == k : Nat}:
  match k:
    case 0n: {==}
    case 1n+p: {==}

def sub_unit(+n: Nat, +w: Word(1n+n), +k: Nat, +h: {N.unsigned(1n+n, w) == 1n+k : Nat}) -> {N.unsigned(1n+n, Word.sub(1n+n, w, H.unit(n))) == k : Nat}:
  %Equal.sym(Nat, N.unsigned(1n+n, Word.sub(1n+n, w, H.unit(n))), Nat.sub(N.unsigned(1n+n, w), N.unsigned(1n+n, H.unit(n))), SubBounds.exact(1n+n, w, H.unit(n), enough(n, w, k, h))) : {_ == k : Nat}
  %Equal.sym(Nat, N.unsigned(1n+n, H.unit(n)), 1n, unit_value(n)) : {Nat.sub(N.unsigned(1n+n, w), _) == k : Nat}
  %Equal.sym(Nat, N.unsigned(1n+n, w), 1n+k, h) : {Nat.sub(_, 1n) == k : Nat}
  sub_zero(k)

def lt_of_le(a: Nat, b: Nat, +c: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_lt(a, Nat.add(b, 1n+c)) == True{} : Bool}:
  match a b:
    case 0n 0n: {==}
    case 0n 1n+bp: {==}
    case 1n+ap 0n: Empty.absurd({Nat.is_lt(1n+ap, Nat.add(0n, 1n+c)) == True{} : Bool}, Routing.false_true(h))
    case 1n+ap 1n+bp: lt_of_le(ap, bp, c, h)

def lt_of_not_ge(a: Nat, b: Nat, h: {Nat.is_ge(a, b) == False{} : Bool}) -> {Nat.is_lt(a, b) == True{} : Bool}:
  match a b:
    case 0n 0n: Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, Routing.false_true(Equal.sym(Bool, True{}, False{}, h)))
    case 0n 1n+bp: {==}
    case 1n+ap 0n: Empty.absurd({Nat.is_lt(1n+ap, 0n) == True{} : Bool}, Routing.false_true(Equal.sym(Bool, True{}, False{}, h)))
    case 1n+ap 1n+bp: lt_of_not_ge(ap, bp, h)

def succ_le(a: Nat, b: Nat, h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(1n+a, b) == True{} : Bool}:
  match a b:
    case 0n 0n: Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, Routing.false_true(h))
    case 0n 1n+bp:
      match bp:
        case 0n: {==}
        case 1n+q: {==}
    case 1n+ap 0n: Empty.absurd({Nat.is_le(2n+ap, 0n) == True{} : Bool}, Routing.false_true(h))
    case 1n+ap 1n+bp: succ_le(ap, bp, h)

def below_double(+v: Nat, s: Nat, hs: {Nat.is_lt(0n, s) == True{} : Bool}, h: {Nat.is_le(v, s) == True{} : Bool}) -> {Nat.is_lt(v, Nat.double(s)) == True{} : Bool}:
  match s:
    case 0n: Empty.absurd({Nat.is_lt(v, 0n) == True{} : Bool}, Routing.false_true(hs))
    case 1n++sp:
      %Equal.sym(Nat, Nat.double(1n+sp), Nat.add(1n+sp, 1n+sp), A.double_self(1n+sp)) : {Nat.is_lt(v, _) == True{} : Bool}
      lt_of_le(v, 1n+sp, sp, h)

# 1 + k >= 2S with S >= 1 gives k >= S.
def ge_from_big(+k: Nat, +s: Nat, hs: {Nat.is_lt(0n, s) == True{} : Bool}, h: {Nat.is_lt(1n+k, Nat.double(s)) == False{} : Bool}, b: Bool, eb: {Nat.is_ge(k, s) == b : Bool}) -> {Nat.is_ge(k, s) == True{} : Bool}:
  match b:
    case True{}: eb
    case False{}: Empty.absurd({Nat.is_ge(k, s) == True{} : Bool}, clash(Nat.is_lt(1n+k, Nat.double(s)), below_double(1n+k, s, hs, succ_le(k, s, lt_of_not_ge(k, s, eb))), h))

def nn_bool(+n: Nat, msg: String, +w: Word(1n+n), c: Bool) -> {H.fit(1n+n, msg, w, c) == lift(1n+n, msg, S.nonnegative_if(n, N.unsigned(1n+n, w), c)) : Result<&2, &2, String, Word(1n+n)>}:
  match c:
    case True{}: Equal.cong(Word(1n+n), Result<&2, &2, String, Word(1n+n)>, x => Done{x}, w, N.from_nat(1n+n, N.unsigned(1n+n, w)), Equal.sym(Word(1n+n), N.from_nat(1n+n, N.unsigned(1n+n, w)), w, Quotient.reconstruct(1n+n, w)))
    case False{}: {==}

def cm_bool(+n: Nat, msg: String, +x: Word(1n+n), c: Bool) -> {H.fit(1n+n, msg, Word.not(1n+n, x), c) == lift(1n+n, msg, S.complement_if(n, N.unsigned(1n+n, x), c)) : Result<&2, &2, String, Word(1n+n)>}:
  match c:
    case True{}: Equal.cong(Word(1n+n), Result<&2, &2, String, Word(1n+n)>, y => Done{Word.not(1n+n, y)}, x, N.from_nat(1n+n, N.unsigned(1n+n, x)), Equal.sym(Word(1n+n), N.from_nat(1n+n, N.unsigned(1n+n, x)), x, Quotient.reconstruct(1n+n, x)))
    case False{}: {==}

# For an in-range word, 0 <= value < 2^n is exactly a clear sign bit.
def half_of_word(+n: Nat, +x: Word(1n+n)) -> {S.half(n, N.unsigned(1n+n, x)) == Bool.not(H.sign_bit(n, x)) : Bool}:
  %Equal.sym(Bool, S.fits(1n+n, N.unsigned(1n+n, x)), True{}, fits_self(1n+n, x)) : {Bool.and(_, Bool.not(S.sign_bit(n, N.from_nat(1n+n, N.unsigned(1n+n, x))))) == Bool.not(H.sign_bit(n, x)) : Bool}
  %Equal.sym(Word(1n+n), N.from_nat(1n+n, N.unsigned(1n+n, x)), x, Quotient.reconstruct(1n+n, x)) : {Bool.not(S.sign_bit(n, _)) == Bool.not(H.sign_bit(n, x)) : Bool}
  Equal.cong(Bool, Bool, y => Bool.not(y), S.sign_bit(n, x), H.sign_bit(n, x), sign_same(n, x))

def neg_value(+n: Nat, msg: String, +w: Word(1n+n), u: Nat, +eu: {N.unsigned(1n+n, w) == u : Nat}) -> {H.negative_zero(n, msg, w, H.is_zero(1n+n, w)) == lift(1n+n, msg, S.negative_of(n, u)) : Result<&2, &2, String, Word(1n+n)>}:
  match u:
    case 0n:
      %Equal.sym(Bool, H.is_zero(1n+n, w), True{}, zero_test_true(1n+n, w, eu)) : {H.negative_zero(n, msg, w, _) == lift(1n+n, msg, S.negative_of(n, 0n)) : Result<&2, &2, String, Word(1n+n)>}
      Equal.cong(Word(1n+n), Result<&2, &2, String, Word(1n+n)>, x => Done{x}, w, N.from_nat(1n+n, 0n), Equal.trans(Word(1n+n), w, N.from_nat(1n+n, N.unsigned(1n+n, w)), N.from_nat(1n+n, 0n), Equal.sym(Word(1n+n), N.from_nat(1n+n, N.unsigned(1n+n, w)), w, Quotient.reconstruct(1n+n, w)), Equal.cong(Nat, Word(1n+n), y => N.from_nat(1n+n, y), N.unsigned(1n+n, w), 0n, eu)))
    case 1n++k:
      %Equal.sym(Bool, H.is_zero(1n+n, w), False{}, zero_test_false(1n+n, w, k, eu)) : {H.negative_zero(n, msg, w, _) == lift(1n+n, msg, S.negative_of(n, 1n+k)) : Result<&2, &2, String, Word(1n+n)>}
      %sub_unit(n, w, k, eu) : {H.negative_nonzero(n, msg, Word.sub(1n+n, w, H.unit(n))) == lift(1n+n, msg, S.complement_if(n, _, S.half(n, _))) : Result<&2, &2, String, Word(1n+n)>}
      %Equal.sym(Bool, S.half(n, N.unsigned(1n+n, Word.sub(1n+n, w, H.unit(n)))), Bool.not(H.sign_bit(n, Word.sub(1n+n, w, H.unit(n)))), half_of_word(n, Word.sub(1n+n, w, H.unit(n)))) : {H.negative_nonzero(n, msg, Word.sub(1n+n, w, H.unit(n))) == lift(1n+n, msg, S.complement_if(n, N.unsigned(1n+n, Word.sub(1n+n, w, H.unit(n))), _)) : Result<&2, &2, String, Word(1n+n)>}
      cm_bool(n, msg, Word.sub(1n+n, w, H.unit(n)), Bool.not(H.sign_bit(n, Word.sub(1n+n, w, H.unit(n)))))

def big_half(+n: Nat, +k: Nat, h: {Nat.is_lt(1n+k, N.scale_binary(1n+n, 1n)) == False{} : Bool}, b: Bool, +eb: {S.fits(1n+n, k) == b : Bool}) -> {S.half(n, k) == False{} : Bool}:
  match b:
    case False{}:
      %Equal.sym(Bool, S.fits(1n+n, k), False{}, eb) : {Bool.and(_, Bool.not(S.sign_bit(n, N.from_nat(1n+n, k)))) == False{} : Bool}
      {==}
    case True{}:
      %Equal.sym(Bool, S.fits(1n+n, k), True{}, eb) : {Bool.and(_, Bool.not(S.sign_bit(n, N.from_nat(1n+n, k)))) == False{} : Bool}
      %Equal.sym(Bool, S.sign_bit(n, N.from_nat(1n+n, k)), H.sign_bit(n, N.from_nat(1n+n, k)), sign_same(n, N.from_nat(1n+n, k))) : {Bool.not(_) == False{} : Bool}
      %Equal.sym(Bool, H.sign_bit(n, N.from_nat(1n+n, k)), Nat.is_ge(N.unsigned(1n+n, N.from_nat(1n+n, k)), N.scale_binary(n, 1n)), sign_nat(n, N.from_nat(1n+n, k))) : {Bool.not(_) == False{} : Bool}
      %Equal.sym(Nat, N.unsigned(1n+n, N.from_nat(1n+n, k)), k, eq_sound(N.unsigned(1n+n, N.from_nat(1n+n, k)), k, eb)) : {Bool.not(Nat.is_ge(_, N.scale_binary(n, 1n))) == False{} : Bool}
      %Equal.sym(Bool, Nat.is_ge(k, N.scale_binary(n, 1n)), True{}, ge_from_big(k, N.scale_binary(n, 1n), scale_positive(n), h, Nat.is_ge(k, N.scale_binary(n, 1n)), {==})) : {Bool.not(_) == False{} : Bool}
      {==}

def neg_large(+n: Nat, msg: String, v: Nat, h: {Nat.is_lt(v, N.scale_binary(1n+n, 1n)) == False{} : Bool}) -> {Fail{msg} == lift(1n+n, msg, S.negative_of(n, v)) : Result<&2, &2, String, Word(1n+n)>}:
  match v:
    case 0n: Empty.absurd({Fail{msg} == lift(1n+n, msg, S.negative_of(n, 0n)) : Result<&2, &2, String, Word(1n+n)>}, clash(Nat.is_lt(0n, N.scale_binary(1n+n, 1n)), scale_positive(1n+n), h))
    case 1n++k:
      %Equal.sym(Bool, S.half(n, k), False{}, big_half(n, k, h, S.fits(1n+n, k), {==})) : {Fail{msg} == lift(1n+n, msg, S.complement_if(n, k, _)) : Result<&2, &2, String, Word(1n+n)>}
      {==}

def neg_zero(+n: Nat, msg: String, +w: Word(1n+n), +left: List<&2, H.Digit>, +v: Nat, eq: {Nat.add(N.unsigned(1n+n, w), N.scale_binary(1n+n, Bin.hval(left, 0n))) == v : Nat}, b: Bool, +eb: {H.zeros(left) == b : Bool}) -> {H.negative_word(n, msg, H.fit(1n+n, msg, w, H.zeros(left))) == lift(1n+n, msg, S.negative_of(n, v)) : Result<&2, &2, String, Word(1n+n)>}:
  match b:
    case True{}:
      %Equal.sym(Bool, H.zeros(left), True{}, eb) : {H.negative_word(n, msg, H.fit(1n+n, msg, w, _)) == lift(1n+n, msg, S.negative_of(n, v)) : Result<&2, &2, String, Word(1n+n)>}
      neg_value(n, msg, w, v, exact_value(1n+n, w, left, v, eq, eb))
    case False{}:
      %Equal.sym(Bool, H.zeros(left), False{}, eb) : {H.negative_word(n, msg, H.fit(1n+n, msg, w, _)) == lift(1n+n, msg, S.negative_of(n, v)) : Result<&2, &2, String, Word(1n+n)>}
      neg_large(n, msg, v, large(1n+n, w, left, v, eq, eb))

def pos_zero(+n: Nat, msg: String, +w: Word(1n+n), +left: List<&2, H.Digit>, +v: Nat, eq: {Nat.add(N.unsigned(1n+n, w), N.scale_binary(1n+n, Bin.hval(left, 0n))) == v : Nat}, b: Bool, +eb: {H.zeros(left) == b : Bool}) -> {H.nonnegative_word(n, msg, H.fit(1n+n, msg, w, H.zeros(left))) == lift(1n+n, msg, S.nonnegative_if(n, v, S.half(n, v))) : Result<&2, &2, String, Word(1n+n)>}:
  match b:
    case True{}:
      %Equal.sym(Bool, H.zeros(left), True{}, eb) : {H.nonnegative_word(n, msg, H.fit(1n+n, msg, w, _)) == lift(1n+n, msg, S.nonnegative_if(n, v, S.half(n, v))) : Result<&2, &2, String, Word(1n+n)>}
      %exact_value(1n+n, w, left, v, eq, eb) : {H.fit(1n+n, msg, w, Bool.not(H.sign_bit(n, w))) == lift(1n+n, msg, S.nonnegative_if(n, _, S.half(n, _))) : Result<&2, &2, String, Word(1n+n)>}
      %Equal.sym(Bool, S.half(n, N.unsigned(1n+n, w)), Bool.not(H.sign_bit(n, w)), half_of_word(n, w)) : {H.fit(1n+n, msg, w, Bool.not(H.sign_bit(n, w))) == lift(1n+n, msg, S.nonnegative_if(n, N.unsigned(1n+n, w), _)) : Result<&2, &2, String, Word(1n+n)>}
      nn_bool(n, msg, w, Bool.not(H.sign_bit(n, w)))
    case False{}:
      %Equal.sym(Bool, H.zeros(left), False{}, eb) : {H.nonnegative_word(n, msg, H.fit(1n+n, msg, w, _)) == lift(1n+n, msg, S.nonnegative_if(n, v, S.half(n, v))) : Result<&2, &2, String, Word(1n+n)>}
      %Equal.sym(Bool, S.fits(1n+n, v), False{}, no_fit(1n+n, v, large(1n+n, w, left, v, eq, eb))) : {H.nonnegative_word(n, msg, H.fit(1n+n, msg, w, False{})) == lift(1n+n, msg, S.nonnegative_if(n, v, Bool.and(_, Bool.not(S.sign_bit(n, N.from_nat(1n+n, v)))))) : Result<&2, &2, String, Word(1n+n)>}
      {==}

def neg_pair(+n: Nat, msg: String, r: Word(1n+n) & List<&2, H.Digit>, +v: Nat, eq: {Nat.add(N.unsigned(1n+n, Bin.wd(1n+n, r)), N.scale_binary(1n+n, Bin.hval(Bin.lf(1n+n, r), 0n))) == v : Nat}) -> {H.negative_word(n, msg, H.fit_pair(1n+n, msg, r)) == lift(1n+n, msg, S.negative_of(n, v)) : Result<&2, &2, String, Word(1n+n)>}:
  (+w, +left) = r
  neg_zero(n, msg, w, left, v, eq, H.zeros(left), {==})

def pos_pair(+n: Nat, msg: String, r: Word(1n+n) & List<&2, H.Digit>, +v: Nat, eq: {Nat.add(N.unsigned(1n+n, Bin.wd(1n+n, r)), N.scale_binary(1n+n, Bin.hval(Bin.lf(1n+n, r), 0n))) == v : Nat}) -> {H.nonnegative_word(n, msg, H.fit_pair(1n+n, msg, r)) == lift(1n+n, msg, S.nonnegative_if(n, v, S.half(n, v))) : Result<&2, &2, String, Word(1n+n)>}:
  (+w, +left) = r
  pos_zero(n, msg, w, left, v, eq, H.zeros(left), {==})

def pmap(m: Maybe<&2, H.Parsed>) -> Maybe<&2, S.Signed>:
  match m:
    case None{}: None{}
    case Some{H.Parsed{negative, ds}}: Some{S.Signed{negative, Bin.hval(ds, 0n)}}

def signed_fit(+n: Nat, +msg: String, m: Maybe<&2, H.Parsed>) -> {H.signed_fit(n, msg, m) == lift(1n+n, msg, S.signed_of(n, pmap(m))) : Result<&2, &2, String, Word(1n+n)>}:
  match m:
    case None{}: {==}
    case Some{H.Parsed{True{}, +ds}}: neg_pair(n, msg, H.binary(1n+n, ds), Bin.hval(ds, 0n), Bin.binary_value(1n+n, ds))
    case Some{H.Parsed{False{}, +ds}}: pos_pair(n, msg, H.binary(1n+n, ds), Bin.hval(ds, 0n), Bin.binary_value(1n+n, ds))

def sign_agree(negative: Bool, m: Maybe<&2, List<&2, H.Digit>>) -> {pmap(H.sign(negative, m)) == S.sign(negative, Dec.hopt(0n, m)) : Maybe<&2, S.Signed>}:
  match m:
    case None{}: {==}
    case Some{ds}: {==}

def signed_agree(b: Bool, +c: Char, +t: String) -> {pmap(H.signed(b, c, t)) == S.signed(b, c, t) : Maybe<&2, S.Signed>}:
  match b:
    case True{}:
      %Dec.numeral_value(t) : {pmap(H.sign(True{}, H.numeral(t))) == S.sign(True{}, _) : Maybe<&2, S.Signed>}
      sign_agree(True{}, H.numeral(t))
    case False{}:
      %Dec.numeral_value(SCon{c, t}) : {pmap(H.sign(False{}, H.numeral(SCon{c, t}))) == S.sign(False{}, _) : Maybe<&2, S.Signed>}
      sign_agree(False{}, H.numeral(SCon{c, t}))

def integer_agree(s: String) -> {pmap(H.integer(s)) == S.integer(s) : Maybe<&2, S.Signed>}:
  match s:
    case SNil{}: {==}
    case SCon{+c, +t}: signed_agree(Char.is_eq(c, '-'), c, t)

# Signed readers: exactly the specification's integer numerals in [-2^n, 2^n).
def signed_word(+n: Nat, +msg: String, +s: String) -> {H.signed_word(n, msg, s) == lift(1n+n, msg, S.signed_text(n, s)) : Result<&2, &2, String, Word(1n+n)>}:
  %integer_agree(s) : {H.signed_word(n, msg, s) == lift(1n+n, msg, S.signed_of(n, _)) : Result<&2, &2, String, Word(1n+n)>}
  signed_fit(n, msg, H.integer(s))

