import Base
# Ported from reference/lru/proofs/numeric.bend (unchanged proof text; imports retargeted to
# the natively compilable copies src/lru/{wide,time}.bend, types/lru_model.bend
# and spec/lru_{numeric,unsigned_division}.bend).
import ../../../spec/lru_numeric.bend as N
import ../../../src/lru/wide.bend as W
import ../../../src/lru/time.bend as Time
import ../../../types/lru_model.bend as T

# Arbitrary-width rollover law, not an enumerated 64-bit test.
law increment_maximum_wraps:
  for n: Nat
  {Word.inc(n, Word.not(n, Word.zero(n))) == Word.zero(n) : Word(n)}
def increment_maximum_wraps(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Word(p), Word(1n+p), t => WCon{False{}, t},
        Word.inc(p, Word.not(p, Word.zero(p))), Word.zero(p), increment_maximum_wraps(p))

law zero_detected:
  for n: Nat
  {W.is_zero(n, Word.zero(n)) == True{} : Bool}
def zero_detected(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      zero_detected(p)

law zero_sign:
  for n: Nat
  {W.last(n, Word.zero(n)) == False{} : Bool}
def zero_sign(n):
  match n:
    case 0n:
      {==}
    case 1n+0n:
      {==}
    case 1n+1n+p:
      zero_sign(1n+p)

law divide_zero:
  for +n: Nat
  {W.div_million(n, Word.zero(n)) == W.Div{Word.zero(n), 0} : W.Division<n>}
def divide_zero(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(W.Division<p>, W.div_million(p, Word.zero(p)), W.Div{Word.zero(p), 0}, divide_zero(p)) : {W.digit(p, False{}, _) == W.Div{Word.zero(1n+p), 0} : W.Division<1n+p>}
      {==}

law immortal_duration:
  for now: T.Int64
  {Time.deadline(now, T.I64{Word.zero(64n)}) == T.I64{Word.zero(64n)} : T.Int64}
def immortal_duration(now):
  {==}

law immortal_deadline:
  for now: T.Int64
  {Time.expired(T.I64{Word.zero(64n)}, now) == False{} : Bool}
def immortal_deadline(now):
  {==}

# Checked connection between the public wrapping counter operation and the
# arbitrary-width rollover theorem, independent of capacity or trace length.
law counter_rollover:
  {W.inc(Word.not(64n, Word.zero(64n))) == Word.zero(64n) : Word(64n)}
def counter_rollover():
  increment_maximum_wraps(64n)

law split_join:
  for +n: Nat
  for +m: Nat
  for a: Word(n)
  for b: Word(m)
  {W.split(n, m, W.join(n, m, a, b)) == W.Split{a, b} : W.Parts<n, m>}
def split_join(n, m, a, b):
  match n:
    case 0n:
      match a:
        case WNil{}:
          {==}
    case 1n+p:
      match a:
        case WCon{+h, tail}:
          Equal.cong(W.Parts<p, m>, W.Parts<1n+p, m>, r => W.split_cons(p, m, h, r),
            W.split(p, m, W.join(p, m, tail, b)), W.Split{tail, b}, split_join(p, m, tail, b))

law pack_roundtrip:
  for low: U32
  for high: U32
  {W.unpack(W.pack(low, high)) == (low, high) : U32 & U32}
def pack_roundtrip(low, high):
  match low high:
    case U32{lo} U32{hi}:
      Equal.cong(W.Parts<32n, 32n>, U32 & U32, W.limbs,
        W.split(32n, 32n, W.join(32n, 32n, lo, hi)), W.Split{lo, hi}, split_join(32n, 32n, lo, hi))

def rejoin(+n: Nat, +m: Nat, parts: W.Parts<n, m>) -> Word(Nat.add(n, m)):
  W.Split{lo, hi} = parts
  W.join(n, m, lo, hi)

law rejoin_cons:
  for +n: Nat
  for +m: Nat
  for h: Bool
  for parts: W.Parts<n, m>
  {rejoin(1n+n, m, W.split_cons(n, m, h, parts)) == WCon{h, rejoin(n, m, parts)} : Word(Nat.add(1n+n, m))}
def rejoin_cons(n, m, h, parts):
  match parts:
    case W.Split{lo, hi}:
      {==}

law join_split:
  for +n: Nat
  for +m: Nat
  for w: Word(Nat.add(n, m))
  {rejoin(n, m, W.split(n, m, w)) == w : Word(Nat.add(n, m))}
def join_split(n, m, w):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{+h, +tail}:
          Equal.trans(Word(Nat.add(1n+p, m)), rejoin(1n+p, m, W.split_cons(p, m, h, W.split(p, m, tail))),
            WCon{h, rejoin(p, m, W.split(p, m, tail))}, WCon{h, tail},
            rejoin_cons(p, m, h, W.split(p, m, tail)),
            Equal.cong(Word(Nat.add(p, m)), Word(Nat.add(1n+p, m)), t => WCon{h, t},
              rejoin(p, m, W.split(p, m, tail)), tail, join_split(p, m, tail)))

# Numeric specification defines sign by comparison with the high-bit threshold;
# executable code reads the last bit. This proves that bridge at every width.
law comparison_low_zero_ge:
  for c: Cmp
  for b: Bool
  {Cmp.is_ge(Word.cmp.fin(b, False{}, c)) == Cmp.is_ge(c) : Bool}
def comparison_low_zero_ge(c, b):
  match c b:
    case LT{} False{}:
      {==}
    case LT{} True{}:
      {==}
    case GT{} False{}:
      {==}
    case GT{} True{}:
      {==}
    case EQ{} False{}:
      {==}
    case EQ{} True{}:
      {==}

law sign_threshold_correspondence:
  for n: Nat
  for w: Word(1n+n)
  {Cmp.is_ge(Word.cmp(1n+n, w, N.sign_threshold(n))) == W.last(1n+n, w) : Bool}
def sign_threshold_correspondence(n, w):
  match n:
    case 0n:
      match w:
        case WCon{False{}, WNil{}}:
          {==}
        case WCon{True{}, WNil{}}:
          {==}
    case 1n+ +p:
      match w:
        case WCon{b, +tail}:
          Equal.trans(Bool, Cmp.is_ge(Word.cmp.fin(b, False{}, Word.cmp(1n+p, tail, N.sign_threshold(p)))), Cmp.is_ge(Word.cmp(1n+p, tail, N.sign_threshold(p))), W.last(1n+p, tail), comparison_low_zero_ge(Word.cmp(1n+p, tail, N.sign_threshold(p)), b), sign_threshold_correspondence(p, tail))

law comparison_low_zero_eq:
  for c: Cmp
  for b: Bool
  {Cmp.is_eq(Word.cmp.fin(b, False{}, c)) == Bool.and(Bool.not(b), Cmp.is_eq(c)) : Bool}
def comparison_low_zero_eq(c, b):
  match c b:
    case LT{} False{}:
      {==}
    case LT{} True{}:
      {==}
    case GT{} False{}:
      {==}
    case GT{} True{}:
      {==}
    case EQ{} False{}:
      {==}
    case EQ{} True{}:
      {==}

law zero_comparison_correspondence:
  for +n: Nat
  for w: Word(n)
  {Cmp.is_eq(Word.cmp(n, w, Word.zero(n))) == W.is_zero(n, w) : Bool}
def zero_comparison_correspondence(n, w):
  match n:
    case 0n:
      {==}
    case 1n+ +p:
      match w:
        case WCon{+b, +tail}:
          Equal.trans(Bool, Cmp.is_eq(Word.cmp.fin(b, False{}, Word.cmp(p, tail, Word.zero(p)))), Bool.and(Bool.not(b), Cmp.is_eq(Word.cmp(p, tail, Word.zero(p)))), Bool.and(Bool.not(b), W.is_zero(p, tail)), comparison_low_zero_eq(Word.cmp(p, tail, Word.zero(p)), b), Equal.cong(Bool, Bool, x => Bool.and(Bool.not(b), x), Cmp.is_eq(Word.cmp(p, tail, Word.zero(p))), W.is_zero(p, tail), zero_comparison_correspondence(p, tail)))

law signed_order_branches:
  for a: Word(64n)
  for b: Word(64n)
  for sa: Bool
  for sb: Bool
  {W.signed_order(a, b, sa, sb) == N.order(a, b, sa, sb) : Bool}
def signed_order_branches(a, b, sa, sb):
  match sa sb:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

law signed_order_refines:
  for +a: Word(64n)
  for +b: Word(64n)
  {W.le(a, b) == N.order(a, b, N.negative(a), N.negative(b)) : Bool}
def signed_order_refines(a, b):
  %Equal.sym(Bool, N.negative(a), W.last(64n, a), sign_threshold_correspondence(63n, a)) : {W.le(a, b) == N.order(a, b, _, N.negative(b)) : Bool}
  %Equal.sym(Bool, N.negative(b), W.last(64n, b), sign_threshold_correspondence(63n, b)) : {W.le(a, b) == N.order(a, b, W.last(64n, a), _) : Bool}
  signed_order_branches(a, b, W.last(64n, a), W.last(64n, b))

law expiration_sentinel_branch:
  for d: T.Int64
  for now: T.Int64
  for immortal: Bool
  {Time.expired_choose(d, now, immortal) == Bool.and(Bool.not(immortal), Time.le(d, now)) : Bool}
def expiration_sentinel_branch(d, now, immortal):
  match immortal:
    case False{}:
      {==}
    case True{}:
      {==}

law expiration_refines:
  for deadline: T.Int64
  for now: T.Int64
  {Time.expired(deadline, now) == N.expired(deadline, now) : Bool}
def expiration_refines(deadline, now):
  match deadline now:
    case T.I64{+a} T.I64{+b}:
      %Equal.sym(Bool, N.zero(a), W.is_zero(64n, a), zero_comparison_correspondence(64n, a)) : {Time.expired(T.I64{a}, T.I64{b}) == Bool.and(Bool.not(_), N.order(a, b, N.negative(a), N.negative(b))) : Bool}
      %signed_order_refines(a, b) : {Time.expired(T.I64{a}, T.I64{b}) == Bool.and(Bool.not(W.is_zero(64n, a)), _) : Bool}
      expiration_sentinel_branch(T.I64{a}, T.I64{b}, W.is_zero(64n, a))

law double_add:
  for a: Nat
  for b: Nat
  {Nat.double(Nat.add(a, b)) == Nat.add(Nat.double(a), Nat.double(b)) : Nat}
def double_add(a, b):
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, x => 2n+x, Nat.double(Nat.add(p, b)), Nat.add(Nat.double(p), Nat.double(b)), double_add(p, b))

law primitive_word_interpretation:
  for +n: Nat
  for w: Word(n)
  {Word.to_nat(n, w) == N.unsigned(n, w) : Nat}
def primitive_word_interpretation(n, w):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{False{}, tail}:
          Equal.cong(Nat, Nat, Nat.double, Word.to_nat(p, tail), N.unsigned(p, tail), primitive_word_interpretation(p, tail))
        case WCon{True{}, tail}:
          Equal.cong(Nat, Nat, x => 1n+Nat.double(x), Word.to_nat(p, tail), N.unsigned(p, tail), primitive_word_interpretation(p, tail))

law join_interpretation:
  for +n: Nat
  for +m: Nat
  for a: Word(n)
  for +b: Word(m)
  {N.unsigned(Nat.add(n, m), W.join(n, m, a, b)) == Nat.add(N.unsigned(n, a), N.scale_binary(n, N.unsigned(m, b))) : Nat}
def join_interpretation(n, m, a, b):
  match n:
    case 0n:
      {==}
    case 1n+ +p:
      match a:
        case WCon{False{}, +tail}:
          Equal.trans(Nat, Nat.double(N.unsigned(Nat.add(p, m), W.join(p, m, tail, b))), Nat.double(Nat.add(N.unsigned(p, tail), N.scale_binary(p, N.unsigned(m, b)))), Nat.add(Nat.double(N.unsigned(p, tail)), Nat.double(N.scale_binary(p, N.unsigned(m, b)))), Equal.cong(Nat, Nat, Nat.double, N.unsigned(Nat.add(p, m), W.join(p, m, tail, b)), Nat.add(N.unsigned(p, tail), N.scale_binary(p, N.unsigned(m, b))), join_interpretation(p, m, tail, b)), double_add(N.unsigned(p, tail), N.scale_binary(p, N.unsigned(m, b))))
        case WCon{True{}, +tail}:
          Equal.trans(Nat, 1n+Nat.double(N.unsigned(Nat.add(p, m), W.join(p, m, tail, b))), 1n+Nat.double(Nat.add(N.unsigned(p, tail), N.scale_binary(p, N.unsigned(m, b)))), 1n+Nat.add(Nat.double(N.unsigned(p, tail)), Nat.double(N.scale_binary(p, N.unsigned(m, b)))), Equal.cong(Nat, Nat, x => 1n+Nat.double(x), N.unsigned(Nat.add(p, m), W.join(p, m, tail, b)), Nat.add(N.unsigned(p, tail), N.scale_binary(p, N.unsigned(m, b))), join_interpretation(p, m, tail, b)), Equal.cong(Nat, Nat, x => 1n+x, Nat.double(Nat.add(N.unsigned(p, tail), N.scale_binary(p, N.unsigned(m, b)))), Nat.add(Nat.double(N.unsigned(p, tail)), Nat.double(N.scale_binary(p, N.unsigned(m, b)))), double_add(N.unsigned(p, tail), N.scale_binary(p, N.unsigned(m, b)))))

law pack_interpretation:
  for low: U32
  for high: U32
  {N.unsigned(64n, W.pack(low, high)) == Nat.add(U32.to_nat(low), N.scale_binary(32n, U32.to_nat(high))) : Nat}
def pack_interpretation(low, high):
  match low high:
    case U32{+lo} U32{+hi}:
      %Equal.sym(Nat, Word.to_nat(32n, lo), N.unsigned(32n, lo), primitive_word_interpretation(32n, lo)) : {N.unsigned(64n, W.pack(U32{lo}, U32{hi})) == Nat.add(_, N.scale_binary(32n, Word.to_nat(32n, hi))) : Nat}
      %Equal.sym(Nat, Word.to_nat(32n, hi), N.unsigned(32n, hi), primitive_word_interpretation(32n, hi)) : {N.unsigned(64n, W.pack(U32{lo}, U32{hi})) == Nat.add(N.unsigned(32n, lo), N.scale_binary(32n, _)) : Nat}
      join_interpretation(32n, 32n, lo, hi)
