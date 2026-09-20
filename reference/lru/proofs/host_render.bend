import Base
import ../src/host.bend as H
import ../src/wide.bend as W
import ../spec/host.bend as S
import ../spec/numeric.bend as N
import ./host_decimal.bend as Dec
import ./host_numeric.bend as HN
import ./nat_algebra.bend as A
import ./natural_products.bend as Product
import ./numeric.bend as Numeric
import ./division_quotient.bend as Quotient
import ./map_routing.bend as Routing

# Words rendered as decimal text (src/host.bend) read back, under the
# independent specification, as exactly the word's value: unsigned text for
# counters and uint64 keys, signed text for int64 keys.
def lval(ds: List<&2, H.Digit>) -> Nat:
  match ds:
    case Nil{}: 0n
    case Con{d, t}: Nat.add(Dec.dnat(d), Nat.mul(lval(t), 10n))

def bit(b: Bool) -> Nat:
  N.bit_value(b)

def dd_arith(+d2: Nat, +c2: Nat, +c: Nat, +d: Nat, +l: Nat, fact: {Nat.add(d2, Nat.mul(c2, 10n)) == Nat.add(c, Nat.double(d)) : Nat}) -> {Nat.add(d2, Nat.mul(Nat.add(c2, Nat.double(l)), 10n)) == Nat.add(c, Nat.double(Nat.add(d, Nat.mul(l, 10n)))) : Nat}:
  %Equal.sym(Nat, Nat.mul(Nat.add(c2, Nat.double(l)), 10n), Nat.add(Nat.mul(c2, 10n), Nat.mul(Nat.double(l), 10n)), A.mul_add_right(c2, Nat.double(l), 10n)) : {Nat.add(d2, _) == Nat.add(c, Nat.double(Nat.add(d, Nat.mul(l, 10n)))) : Nat}
  %A.add_assoc(d2, Nat.mul(c2, 10n), Nat.mul(Nat.double(l), 10n)) : {_ == Nat.add(c, Nat.double(Nat.add(d, Nat.mul(l, 10n)))) : Nat}
  %Equal.sym(Nat, Nat.add(d2, Nat.mul(c2, 10n)), Nat.add(c, Nat.double(d)), fact) : {Nat.add(_, Nat.mul(Nat.double(l), 10n)) == Nat.add(c, Nat.double(Nat.add(d, Nat.mul(l, 10n)))) : Nat}
  %Equal.sym(Nat, Nat.double(Nat.add(d, Nat.mul(l, 10n))), Nat.add(Nat.double(d), Nat.double(Nat.mul(l, 10n))), A.double_add(d, Nat.mul(l, 10n))) : {Nat.add(Nat.add(c, Nat.double(d)), Nat.mul(Nat.double(l), 10n)) == Nat.add(c, _) : Nat}
  %Product.double_product(l, 10n) : {Nat.add(Nat.add(c, Nat.double(d)), Nat.mul(Nat.double(l), 10n)) == Nat.add(c, Nat.add(Nat.double(d), _)) : Nat}
  A.add_assoc(c, Nat.double(d), Nat.mul(Nat.double(l), 10n))

def dd_step(+d: H.Digit, +c: Bool, +d2: H.Digit, +c2: Bool, +t: List<&2, H.Digit>, fact: {Nat.add(Dec.dnat(d2), Nat.mul(bit(c2), 10n)) == Nat.add(bit(c), Nat.double(Dec.dnat(d))) : Nat}, ih: {lval(H.double_digits(t, c2)) == Nat.add(bit(c2), Nat.double(lval(t))) : Nat}) -> {lval(Con{d2, H.double_digits(t, c2)}) == Nat.add(bit(c), Nat.double(lval(Con{d, t}))) : Nat}:
  %Equal.sym(Nat, lval(H.double_digits(t, c2)), Nat.add(bit(c2), Nat.double(lval(t))), ih) : {Nat.add(Dec.dnat(d2), Nat.mul(_, 10n)) == Nat.add(bit(c), Nat.double(lval(Con{d, t}))) : Nat}
  dd_arith(Dec.dnat(d2), bit(c2), bit(c), Dec.dnat(d), lval(t), fact)

# Doubling the digit list and adding the carry doubles its value.
def dd_value(ds: List<&2, H.Digit>, c: Bool) -> {lval(H.double_digits(ds, c)) == Nat.add(bit(c), Nat.double(lval(ds))) : Nat}:
  match ds c:
    case Nil{} True{}: {==}
    case Nil{} False{}: {==}
    case Con{H.D0{}, +t} True{}: dd_step(H.D0{}, True{}, H.D1{}, False{}, t, {==}, dd_value(t, False{}))
    case Con{H.D1{}, +t} True{}: dd_step(H.D1{}, True{}, H.D3{}, False{}, t, {==}, dd_value(t, False{}))
    case Con{H.D2{}, +t} True{}: dd_step(H.D2{}, True{}, H.D5{}, False{}, t, {==}, dd_value(t, False{}))
    case Con{H.D3{}, +t} True{}: dd_step(H.D3{}, True{}, H.D7{}, False{}, t, {==}, dd_value(t, False{}))
    case Con{H.D4{}, +t} True{}: dd_step(H.D4{}, True{}, H.D9{}, False{}, t, {==}, dd_value(t, False{}))
    case Con{H.D5{}, +t} True{}: dd_step(H.D5{}, True{}, H.D1{}, True{}, t, {==}, dd_value(t, True{}))
    case Con{H.D6{}, +t} True{}: dd_step(H.D6{}, True{}, H.D3{}, True{}, t, {==}, dd_value(t, True{}))
    case Con{H.D7{}, +t} True{}: dd_step(H.D7{}, True{}, H.D5{}, True{}, t, {==}, dd_value(t, True{}))
    case Con{H.D8{}, +t} True{}: dd_step(H.D8{}, True{}, H.D7{}, True{}, t, {==}, dd_value(t, True{}))
    case Con{H.D9{}, +t} True{}: dd_step(H.D9{}, True{}, H.D9{}, True{}, t, {==}, dd_value(t, True{}))
    case Con{H.D0{}, +t} False{}: dd_step(H.D0{}, False{}, H.D0{}, False{}, t, {==}, dd_value(t, False{}))
    case Con{H.D1{}, +t} False{}: dd_step(H.D1{}, False{}, H.D2{}, False{}, t, {==}, dd_value(t, False{}))
    case Con{H.D2{}, +t} False{}: dd_step(H.D2{}, False{}, H.D4{}, False{}, t, {==}, dd_value(t, False{}))
    case Con{H.D3{}, +t} False{}: dd_step(H.D3{}, False{}, H.D6{}, False{}, t, {==}, dd_value(t, False{}))
    case Con{H.D4{}, +t} False{}: dd_step(H.D4{}, False{}, H.D8{}, False{}, t, {==}, dd_value(t, False{}))
    case Con{H.D5{}, +t} False{}: dd_step(H.D5{}, False{}, H.D0{}, True{}, t, {==}, dd_value(t, True{}))
    case Con{H.D6{}, +t} False{}: dd_step(H.D6{}, False{}, H.D2{}, True{}, t, {==}, dd_value(t, True{}))
    case Con{H.D7{}, +t} False{}: dd_step(H.D7{}, False{}, H.D4{}, True{}, t, {==}, dd_value(t, True{}))
    case Con{H.D8{}, +t} False{}: dd_step(H.D8{}, False{}, H.D6{}, True{}, t, {==}, dd_value(t, True{}))
    case Con{H.D9{}, +t} False{}: dd_step(H.D9{}, False{}, H.D8{}, True{}, t, {==}, dd_value(t, True{}))

# The little-endian digits of a word have its unsigned value.
def decimal_value(n: Nat, w: Word(n)) -> {lval(H.decimal(n, w)) == N.unsigned(n, w) : Nat}:
  match n:
    case 0n: {==}
    case 1n++p:
      match w:
        case WCon{+b, +t}: Equal.trans(Nat, lval(H.double_digits(H.decimal(p, t), b)), Nat.add(bit(b), Nat.double(lval(H.decimal(p, t)))), Nat.add(bit(b), Nat.double(N.unsigned(p, t))), dd_value(H.decimal(p, t), b), Equal.cong(Nat, Nat, x => Nat.add(bit(b), Nat.double(x)), lval(H.decimal(p, t)), N.unsigned(p, t), decimal_value(p, t)))

def char_value(d: H.Digit) -> {S.digit_value(H.digit_char(d)) == Some{Dec.dnat(d)} : Maybe<&2, Nat>}:
  match d:
    case H.D0{}: {==}
    case H.D1{}: {==}
    case H.D2{}: {==}
    case H.D3{}: {==}
    case H.D4{}: {==}
    case H.D5{}: {==}
    case H.D6{}: {==}
    case H.D7{}: {==}
    case H.D8{}: {==}
    case H.D9{}: {==}

def place_sum(+v: Nat, +x: Nat, +p: Nat, +a: Nat) -> {Nat.add(Nat.mul(v, Nat.mul(10n, p)), Nat.add(Nat.mul(x, p), a)) == Nat.add(Nat.mul(Nat.add(x, Nat.mul(v, 10n)), p), a) : Nat}:
  %Equal.sym(Nat, Nat.mul(Nat.add(x, Nat.mul(v, 10n)), p), Nat.add(Nat.mul(x, p), Nat.mul(Nat.mul(v, 10n), p)), A.mul_add_right(x, Nat.mul(v, 10n), p)) : {Nat.add(Nat.mul(v, Nat.mul(10n, p)), Nat.add(Nat.mul(x, p), a)) == Nat.add(_, a) : Nat}
  %Equal.sym(Nat, Nat.mul(Nat.mul(v, 10n), p), Nat.mul(v, Nat.mul(10n, p)), A.mul_assoc(v, 10n, p)) : {Nat.add(Nat.mul(v, Nat.mul(10n, p)), Nat.add(Nat.mul(x, p), a)) == Nat.add(Nat.add(Nat.mul(x, p), _), a) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(Nat.mul(x, p), Nat.mul(v, Nat.mul(10n, p))), a), Nat.add(Nat.mul(x, p), Nat.add(Nat.mul(v, Nat.mul(10n, p)), a)), A.add_assoc(Nat.mul(x, p), Nat.mul(v, Nat.mul(10n, p)), a)) : {Nat.add(Nat.mul(v, Nat.mul(10n, p)), Nat.add(Nat.mul(x, p), a)) == _ : Nat}
  A.add_swap(Nat.mul(v, Nat.mul(10n, p)), Nat.mul(x, p), a)

def place_arith(+v: Nat, +x: Nat, +len: Nat, p: Maybe<&2, Nat>) -> {Dec.scaled(v, 1n+len, S.place(Some{x}, len, p)) == Dec.scaled(Nat.add(x, Nat.mul(v, 10n)), len, p) : Maybe<&2, Nat>}:
  match p:
    case None{}: {==}
    case Some{+a}:
      Equal.cong(Nat, Maybe<&2, Nat>, y => Some{y}, Nat.add(Nat.mul(v, Nat.mul(10n, Nat.pow(10n, len))), Nat.add(Nat.mul(x, Nat.pow(10n, len)), a)), Nat.add(Nat.mul(Nat.add(x, Nat.mul(v, 10n)), Nat.pow(10n, len)), a), place_sum(v, x, Nat.pow(10n, len), a))

# Rendering prepends the digits most significant first.
def render_value(ds: List<&2, H.Digit>, +acc: String) -> {S.positional(H.render(ds, acc)) == Dec.scaled(lval(ds), String.length(acc), S.positional(acc)) : Maybe<&2, Nat>}:
  match ds:
    case Nil{}: Equal.sym(Maybe<&2, Nat>, Dec.scaled(0n, String.length(acc), S.positional(acc)), S.positional(acc), Dec.identity_scale(String.length(acc), S.positional(acc)))
    case Con{+d, +t}:
      %place_arith(lval(t), Dec.dnat(d), String.length(acc), S.positional(acc)) : {S.positional(H.render(t, SCon{H.digit_char(d), acc})) == _ : Maybe<&2, Nat>}
      %char_value(d) : {S.positional(H.render(t, SCon{H.digit_char(d), acc})) == Dec.scaled(lval(t), 1n+String.length(acc), S.place(_, String.length(acc), S.positional(acc))) : Maybe<&2, Nat>}
      render_value(t, SCon{H.digit_char(d), acc})

def natural_render(t: List<&2, H.Digit>, +x: Char, +y: String) -> {S.natural(H.render(t, SCon{x, y})) == S.positional(H.render(t, SCon{x, y})) : Maybe<&2, Nat>}:
  match t:
    case Nil{}: {==}
    case Con{d, t2}: natural_render(t2, H.digit_char(d), SCon{x, y})

def render_all_value(ds: List<&2, H.Digit>) -> {S.natural(H.render_all(ds)) == Some{lval(ds)} : Maybe<&2, Nat>}:
  match ds:
    case Nil{}: {==}
    case Con{+d, +t}:
      Equal.trans(Maybe<&2, Nat>, S.natural(H.render(t, SCon{H.digit_char(d), SNil{}})), S.positional(H.render(Con{d, t}, SNil{})), Some{lval(Con{d, t})}, natural_render(t, H.digit_char(d), SNil{}), Equal.trans(Maybe<&2, Nat>, S.positional(H.render(Con{d, t}, SNil{})), Dec.scaled(lval(Con{d, t}), 0n, Some{0n}), Some{lval(Con{d, t})}, render_value(Con{d, t}, SNil{}), Equal.sym(Maybe<&2, Nat>, Some{lval(Con{d, t})}, Some{Nat.add(Nat.mul(lval(Con{d, t}), 1n), 0n)}, Dec.nil_value(lval(Con{d, t})))))

# Unsigned decimal text reads back as the word's unsigned value.
def unsigned_text(+n: Nat, +w: Word(n)) -> {S.natural(H.unsigned_text(n, w)) == Some{N.unsigned(n, w)} : Maybe<&2, Nat>}:
  Equal.trans(Maybe<&2, Nat>, S.natural(H.render_all(H.decimal(n, w))), Some{lval(H.decimal(n, w))}, Some{N.unsigned(n, w)}, render_all_value(H.decimal(n, w)), Equal.cong(Nat, Maybe<&2, Nat>, x => Some{x}, lval(H.decimal(n, w)), N.unsigned(n, w), decimal_value(n, w)))

def not_not(n: Nat, w: Word(n)) -> {Word.not(n, Word.not(n, w)) == w : Word(n)}:
  match n:
    case 0n:
      match w:
        case WNil{}: {==}
    case 1n++p:
      match w:
        case WCon{b, +t}:
          match b:
            case True{}: Equal.cong(Word(p), Word(1n+p), x => WCon{True{}, x}, Word.not(p, Word.not(p, t)), t, not_not(p, t))
            case False{}: Equal.cong(Word(p), Word(1n+p), x => WCon{False{}, x}, Word.not(p, Word.not(p, t)), t, not_not(p, t))

def last_not(n: Nat, w: Word(1n+n)) -> {W.last(1n+n, Word.not(1n+n, w)) == Bool.not(W.last(1n+n, w)) : Bool}:
  match n:
    case 0n:
      match w:
        case WCon{b, WNil{}}: {==}
    case 1n++p:
      match w:
        case WCon{b, t}: last_not(p, t)

# Incrementing a word whose top bit is clear adds one to its value.
def inc_value(n: Nat, x: Word(1n+n), hl: {W.last(1n+n, x) == False{} : Bool}) -> {N.unsigned(1n+n, Word.inc(1n+n, x)) == 1n+N.unsigned(1n+n, x) : Nat}:
  match n:
    case 0n:
      match x:
        case WCon{False{}, WNil{}}: {==}
        case WCon{True{}, WNil{}}: Empty.absurd({N.unsigned(1n, Word.inc(1n, WCon{True{}, WNil{}})) == 1n+N.unsigned(1n, WCon{True{}, WNil{}}) : Nat}, Routing.false_true(Equal.sym(Bool, True{}, False{}, hl)))
    case 1n++p:
      match x:
        case WCon{b, +t}:
          match b:
            case False{}: {==}
            case True{}: Equal.cong(Nat, Nat, y => Nat.double(y), N.unsigned(1n+p, Word.inc(1n+p, t)), 1n+N.unsigned(1n+p, t), inc_value(p, t, hl))

def sign_last(+n: Nat, +w: Word(1n+n)) -> {H.sign_bit(n, w) == W.last(1n+n, w) : Bool}:
  Equal.trans(Bool, H.sign_bit(n, w), S.sign_bit(n, w), W.last(1n+n, w), Equal.sym(Bool, S.sign_bit(n, w), H.sign_bit(n, w), HN.sign_same(n, w)), Numeric.sign_threshold_correspondence(n, w))

def sign_flip(+n: Nat, +w: Word(1n+n)) -> {H.sign_bit(n, Word.not(1n+n, w)) == Bool.not(H.sign_bit(n, w)) : Bool}:
  Equal.trans(Bool, H.sign_bit(n, Word.not(1n+n, w)), W.last(1n+n, Word.not(1n+n, w)), Bool.not(H.sign_bit(n, w)), sign_last(n, Word.not(1n+n, w)), Equal.trans(Bool, W.last(1n+n, Word.not(1n+n, w)), Bool.not(W.last(1n+n, w)), Bool.not(H.sign_bit(n, w)), last_not(n, w), Equal.cong(Bool, Bool, y => Bool.not(y), W.last(1n+n, w), H.sign_bit(n, w), Equal.sym(Bool, H.sign_bit(n, w), W.last(1n+n, w), sign_last(n, w)))))

def integer_render(t: List<&2, H.Digit>, d: H.Digit, +y: String) -> {S.integer(H.render(t, SCon{H.digit_char(d), y})) == S.sign(False{}, S.natural(H.render(t, SCon{H.digit_char(d), y}))) : Maybe<&2, S.Signed>}:
  match t:
    case Nil{}:
      match d:
        case H.D0{}: {==}
        case H.D1{}: {==}
        case H.D2{}: {==}
        case H.D3{}: {==}
        case H.D4{}: {==}
        case H.D5{}: {==}
        case H.D6{}: {==}
        case H.D7{}: {==}
        case H.D8{}: {==}
        case H.D9{}: {==}
    case Con{d2, t2}: integer_render(t2, d2, SCon{H.digit_char(d), y})

# Unsigned text never starts with '-': it reads as a nonnegative integer.
def integer_render_all(ds: List<&2, H.Digit>) -> {S.integer(H.render_all(ds)) == S.sign(False{}, S.natural(H.render_all(ds))) : Maybe<&2, S.Signed>}:
  match ds:
    case Nil{}: {==}
    case Con{d, t}: integer_render(t, d, SNil{})

def nonnegative_text(+n: Nat, +w: Word(1n+n), eb: {H.sign_bit(n, w) == False{} : Bool}) -> {S.signed_text(n, H.unsigned_text(1n+n, w)) == Some{w} : Maybe<&2, Word(1n+n)>}:
  %Equal.sym(Maybe<&2, S.Signed>, S.integer(H.unsigned_text(1n+n, w)), S.sign(False{}, S.natural(H.unsigned_text(1n+n, w))), integer_render_all(H.decimal(1n+n, w))) : {S.signed_of(n, _) == Some{w} : Maybe<&2, Word(1n+n)>}
  %Equal.sym(Maybe<&2, Nat>, S.natural(H.unsigned_text(1n+n, w)), Some{N.unsigned(1n+n, w)}, unsigned_text(1n+n, w)) : {S.signed_of(n, S.sign(False{}, _)) == Some{w} : Maybe<&2, Word(1n+n)>}
  %Equal.sym(Bool, S.half(n, N.unsigned(1n+n, w)), Bool.not(H.sign_bit(n, w)), HN.half_of_word(n, w)) : {S.nonnegative_if(n, N.unsigned(1n+n, w), _) == Some{w} : Maybe<&2, Word(1n+n)>}
  %Equal.sym(Bool, H.sign_bit(n, w), False{}, eb) : {S.nonnegative_if(n, N.unsigned(1n+n, w), Bool.not(_)) == Some{w} : Maybe<&2, Word(1n+n)>}
  Equal.cong(Word(1n+n), Maybe<&2, Word(1n+n)>, x => Some{x}, N.from_nat(1n+n, N.unsigned(1n+n, w)), w, Quotient.reconstruct(1n+n, w))

def top_clear(+n: Nat, +w: Word(1n+n), eb: {H.sign_bit(n, w) == True{} : Bool}) -> {W.last(1n+n, Word.not(1n+n, w)) == False{} : Bool}:
  Equal.trans(Bool, W.last(1n+n, Word.not(1n+n, w)), H.sign_bit(n, Word.not(1n+n, w)), False{}, Equal.sym(Bool, H.sign_bit(n, Word.not(1n+n, w)), W.last(1n+n, Word.not(1n+n, w)), sign_last(n, Word.not(1n+n, w))), Equal.trans(Bool, H.sign_bit(n, Word.not(1n+n, w)), Bool.not(H.sign_bit(n, w)), False{}, sign_flip(n, w), Equal.cong(Bool, Bool, y => Bool.not(y), H.sign_bit(n, w), True{}, eb)))

def negative_text(+n: Nat, +w: Word(1n+n), +eb: {H.sign_bit(n, w) == True{} : Bool}) -> {S.signed_text(n, SCon{'-', H.unsigned_text(1n+n, Word.inc(1n+n, Word.not(1n+n, w)))}) == Some{w} : Maybe<&2, Word(1n+n)>}:
  %Equal.sym(Maybe<&2, Nat>, S.natural(H.unsigned_text(1n+n, Word.inc(1n+n, Word.not(1n+n, w)))), Some{N.unsigned(1n+n, Word.inc(1n+n, Word.not(1n+n, w)))}, unsigned_text(1n+n, Word.inc(1n+n, Word.not(1n+n, w)))) : {S.signed_of(n, S.sign(True{}, _)) == Some{w} : Maybe<&2, Word(1n+n)>}
  %Equal.sym(Nat, N.unsigned(1n+n, Word.inc(1n+n, Word.not(1n+n, w))), 1n+N.unsigned(1n+n, Word.not(1n+n, w)), inc_value(n, Word.not(1n+n, w), top_clear(n, w, eb))) : {S.negative_of(n, _) == Some{w} : Maybe<&2, Word(1n+n)>}
  %Equal.sym(Bool, S.half(n, N.unsigned(1n+n, Word.not(1n+n, w))), Bool.not(H.sign_bit(n, Word.not(1n+n, w))), HN.half_of_word(n, Word.not(1n+n, w))) : {S.complement_if(n, N.unsigned(1n+n, Word.not(1n+n, w)), _) == Some{w} : Maybe<&2, Word(1n+n)>}
  %Equal.sym(Bool, H.sign_bit(n, Word.not(1n+n, w)), Bool.not(H.sign_bit(n, w)), sign_flip(n, w)) : {S.complement_if(n, N.unsigned(1n+n, Word.not(1n+n, w)), Bool.not(_)) == Some{w} : Maybe<&2, Word(1n+n)>}
  %Equal.sym(Bool, H.sign_bit(n, w), True{}, eb) : {S.complement_if(n, N.unsigned(1n+n, Word.not(1n+n, w)), Bool.not(Bool.not(_))) == Some{w} : Maybe<&2, Word(1n+n)>}
  %Equal.sym(Word(1n+n), N.from_nat(1n+n, N.unsigned(1n+n, Word.not(1n+n, w))), Word.not(1n+n, w), Quotient.reconstruct(1n+n, Word.not(1n+n, w))) : {Some{Word.not(1n+n, _)} == Some{w} : Maybe<&2, Word(1n+n)>}
  Equal.cong(Word(1n+n), Maybe<&2, Word(1n+n)>, x => Some{x}, Word.not(1n+n, Word.not(1n+n, w)), w, not_not(1n+n, w))

def signed_by(+n: Nat, +w: Word(1n+n), b: Bool, +eb: {H.sign_bit(n, w) == b : Bool}) -> {S.signed_text(n, H.signed_text(n, w, b)) == Some{w} : Maybe<&2, Word(1n+n)>}:
  match b:
    case False{}: nonnegative_text(n, w, eb)
    case True{}: negative_text(n, w, eb)

# Signed decimal text reads back as exactly the two's-complement word.
def signed_text(+n: Nat, +w: Word(1n+n)) -> {S.signed_text(n, H.signed_text(n, w, H.sign_bit(n, w))) == Some{w} : Maybe<&2, Word(1n+n)>}:
  signed_by(n, w, H.sign_bit(n, w), {==})
