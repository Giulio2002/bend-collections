import Base

# Proof observation of a word bit, least-significant position zero, false past
# its width. This is not cache lookup/storage or a replacement Map algorithm.
def nth(n: Nat, w: Word(n), index: Nat) -> Bool:
  match n:
    case 0n:
      False{}
    case 1n+p:
      match w:
        case WCon{bit, tail}:
          match index:
            case 0n: bit
            case 1n+k: nth(p, tail, k)

def at(x: U32, index: Nat) -> Bool:
  U32{w} = x
  nth(32n, w, index)

law padded:
  for +n: Nat
  for w: Word(n)
  for index: Nat
  {nth(1n+n, Word.shr.pad(n, w), index) == nth(n, w, index) : Bool}
def padded(n, w, index):
  match n:
    case 0n:
      match index:
        case 0n: {==}
        case 1n+k: {==}
    case 1n+p:
      match w:
        case WCon{bit, tail}:
          match index:
            case 0n: {==}
            case 1n+k: padded(p, tail, k)

law shifted:
  for +n: Nat
  for w: Word(n)
  for index: Nat
  {nth(n, Word.shr(n, w), index) == nth(n, w, 1n+index) : Bool}
def shifted(n, w, index):
  match n:
    case 0n: {==}
    case 1n+p:
      match w:
        case WCon{bit, tail}:
          padded(p, tail, index)

law shifted_u32:
  for x: U32
  for index: Nat
  {at(U32.shr(x), index) == at(x, 1n+index) : Bool}
def shifted_u32(x, index):
  U32{w} = x
  shifted(32n, w, index)

law shift_front:
  for +x: U32
  for n: Nat
  {U32.shrn(x, 1n+n) == U32.shrn(U32.shr(x), n) : U32}
def shift_front(x, n):
  match n:
    case 0n: {==}
    case 1n+ +p:
      Equal.cong(U32, U32, U32.shr, U32.shrn(x, 1n+p), U32.shrn(U32.shr(x), p), shift_front(x, p))

law low_shift:
  for index: Nat
  for +x: U32
  {at(U32.shrn(x, index), 0n) == at(x, index) : Bool}
def low_shift(index, x):
  match index:
    case 0n: {==}
    case 1n+ +p:
      Equal.trans(Bool, at(U32.shrn(x, 1n+p), 0n), at(U32.shrn(U32.shr(x), p), 0n), at(x, 1n+p), Equal.cong(U32, Bool, y => at(y, 0n), U32.shrn(x, 1n+p), U32.shrn(U32.shr(x), p), shift_front(x, p)), Equal.trans(Bool, at(U32.shrn(U32.shr(x), p), 0n), at(U32.shr(x), p), at(x, 1n+p), low_shift(p, U32.shr(x)), shifted_u32(x, p)))

law and_zero:
  for +n: Nat
  for w: Word(n)
  {Word.and(n, w, Word.zero(n)) == Word.zero(n) : Word(n)}
def and_zero(n, w):
  match n:
    case 0n: {==}
    case 1n+p:
      match w:
        case WCon{False{}, tail}:
          Equal.cong(Word(p), Word(1n+p), t => WCon{False{}, t}, Word.and(p, tail, Word.zero(p)), Word.zero(p), and_zero(p, tail))
        case WCon{True{}, tail}:
          Equal.cong(Word(p), Word(1n+p), t => WCon{False{}, t}, Word.and(p, tail, Word.zero(p)), Word.zero(p), and_zero(p, tail))

law low_mask:
  for x: U32
  {U32.is_ne(U32.and(x, 1), 0) == at(x, 0n) : Bool}
def low_mask(x):
  match x:
    case U32{WCon{False{}, +tail}}:
      %Equal.sym(Word(31n), Word.and(31n, tail, Word.zero(31n)), Word.zero(31n), and_zero(31n, tail)) : {U32.is_ne(U32{WCon{False{}, _}}, 0) == False{} : Bool}
      {==}
    case U32{WCon{True{}, +tail}}:
      %Equal.sym(Word(31n), Word.and(31n, tail, Word.zero(31n)), Word.zero(31n), and_zero(31n, tail)) : {U32.is_ne(U32{WCon{True{}, _}}, 0) == True{} : Bool}
      {==}

# General actual Base Map character-bit extraction correspondence, with no
# index bound premise: out-of-width shifts also have their real false result.
law native_bit:
  for +x: U32
  for +index: Nat
  {Map.bit.u(x, index) == at(x, index) : Bool}
def native_bit(x, index):
  Equal.trans(Bool, Map.bit.u(x, index), at(U32.shrn(x, index), 0n), at(x, index), low_mask(U32.shrn(x, index)), low_shift(index, x))

law xor_bit:
  for +n: Nat
  for a: Word(n)
  for b: Word(n)
  for index: Nat
  {nth(n, Word.xor(n, a, b), index) == Bool.xor(nth(n, a, index), nth(n, b, index)) : Bool}
def xor_bit(n, a, b, index):
  match n:
    case 0n: {==}
    case 1n+p:
      match a b:
        case WCon{x, left_tail} WCon{y, right_tail}:
          match index:
            case 0n: {==}
            case 1n+k: xor_bit(p, left_tail, right_tail, k)

law xor_u32:
  for a: U32
  for b: U32
  for index: Nat
  {at(U32.xor(a, b), index) == Bool.xor(at(a, index), at(b, index)) : Bool}
def xor_u32(a, b, index):
  match a b:
    case U32{x} U32{y}:
      xor_bit(32n, x, y, index)

law native_xor:
  for +a: U32
  for +b: U32
  for +index: Nat
  {Map.bit.u(U32.xor(a, b), index) == Bool.xor(Map.bit.u(a, index), Map.bit.u(b, index)) : Bool}
def native_xor(a, b, index):
  %Equal.sym(Bool, Map.bit.u(a, index), at(a, index), native_bit(a, index)) : {Map.bit.u(U32.xor(a, b), index) == Bool.xor(_, Map.bit.u(b, index)) : Bool}
  %Equal.sym(Bool, Map.bit.u(b, index), at(b, index), native_bit(b, index)) : {Map.bit.u(U32.xor(a, b), index) == Bool.xor(at(a, index), _) : Bool}
  Equal.trans(Bool, Map.bit.u(U32.xor(a, b), index), at(U32.xor(a, b), index), Bool.xor(at(a, index), at(b, index)), native_bit(U32.xor(a, b), index), xor_u32(a, b, index))
