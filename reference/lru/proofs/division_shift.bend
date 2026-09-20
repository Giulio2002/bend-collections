import Base
import ../src/wide.bend as W
import ../spec/numeric.bend as S
import ./word_shift.bend as Shift
import ./addition_bounds.bend as Bounds
import ./division_candidate.bend as Candidate

# Adding the incoming bit to an even shifted word changes only its low bit.
def add_zero(+n: Nat, w: Word(n)) -> {Word.add(n, w, Word.zero(n)) == w : Word(n)}:
  match n:
    case 0n:
      match w:
        case WNil{}: {==}
    case 1n+ +p:
      match w:
        case WCon{bit, +tail}:
          match bit:
            case False{}: Equal.cong(Word(p), Word(1n+p), t => WCon{False{}, t}, Word.add(p, tail, Word.zero(p)), tail, add_zero(p, tail))
            case True{}: Equal.cong(Word(p), Word(1n+p), t => WCon{True{}, t}, Word.add(p, tail, Word.zero(p)), tail, add_zero(p, tail))

def bit_word(n: Nat, bit: Bool) -> Word(n):
  match n:
    case 0n: WNil{}
    case 1n+p: WCon{bit, Word.zero(p)}

def add_bit(+n: Nat, +w: Word(n), bit: Bool) -> {Word.add(n, Word.shl(n, w), bit_word(n, bit)) == Word.shl.put(n, bit, w) : Word(n)}:
  match n:
    case 0n: {==}
    case 1n+ +p:
      match w:
        case WCon{+h, +tail}:
          match bit:
            case False{}: Equal.cong(Word(p), Word(1n+p), t => WCon{False{}, t}, Word.add(p, Word.shl.put(p, h, tail), Word.zero(p)), Word.shl.put(p, h, tail), add_zero(p, Word.shl.put(p, h, tail)))
            case True{}: Equal.cong(Word(p), Word(1n+p), t => WCon{True{}, t}, Word.add(p, Word.shl.put(p, h, tail), Word.zero(p)), Word.shl.put(p, h, tail), add_zero(p, Word.shl.put(p, h, tail)))

def primitive_bit(bit: Bool) -> {W.bit_u32(bit) == U32{bit_word(32n, bit)} : U32}:
  match bit:
    case False{}: {==}
    case True{}: {==}

def shifted(r: U32, bit: Bool) -> U32:
  U32{w} = r
  U32{Word.shl.put(32n, bit, w)}

# This is the exact candidate expression executed in wide.digit.
def actual_candidate(+r: U32, +bit: Bool) -> {U32.add(U32.mul(r, 2), W.bit_u32(bit)) == shifted(r, bit) : U32}:
  match r:
    case U32{+w}:
      %Equal.sym(U32, U32.mul(U32{w}, 2), U32.shl(U32{w}), Candidate.multiplication_is_shift(U32{w})) : {U32.add(_, W.bit_u32(bit)) == shifted(U32{w}, bit) : U32}
      %Equal.sym(U32, W.bit_u32(bit), U32{bit_word(32n, bit)}, primitive_bit(bit)) : {U32.add(U32.shl(U32{w}), _) == shifted(U32{w}, bit) : U32}
      Equal.cong(Word(32n), U32, x => U32{x}, Word.add(32n, Word.shl(32n, w), bit_word(32n, bit)), Word.shl.put(32n, bit, w), add_bit(32n, w, bit))

# The range premise concerns the inputs and discharges discarded carry.
def exact(+n: Nat, +w: Word(n), +bit: Bool, bound: {Nat.is_lt(Nat.add(S.bit_value(bit), Nat.double(S.unsigned(n, w))), S.scale_binary(n, 1n)) == True{} : Bool}) -> {S.unsigned(n, Word.shl.put(n, bit, w)) == Nat.add(S.bit_value(bit), Nat.double(S.unsigned(n, w))) : Nat}:
  Bounds.no_wrap(n, S.unsigned(n, Word.shl.put(n, bit, w)), Nat.add(S.bit_value(bit), Nat.double(S.unsigned(n, w))), Shift.carry(n, bit, w), Shift.conservation(n, bit, w), bound)
