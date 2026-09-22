import Base
import ../spec/numeric.bend as S
import ../src/wide.bend as W
import ../src/time.bend as Time
import ../types/model.bend as T
import ./addition.bend as Add
import ./counter.bend as Counter
import ./numeric.bend as N
import ./map_index.bend as Index
import ./native_map.bend as NatLaws

# The binary constructor in the independent specification uses Base Nat.divmod.
# Establish its behavior against that existing algorithm, for arbitrary Nat.
def stride(+value: Nat) -> {Nat.divmod(2n+value, 2n) == Index.next_quotient(Nat.divmod(value, 2n)) : Nat & Nat}:
  Index.quotient_translation(value, 1n, 0n, 0n)

def binary_division(value: Nat, +bit: Bool) -> {Nat.divmod(Nat.add(S.bit_value(bit), Nat.double(value)), 2n) == (value, S.bit_value(bit)) : Nat & Nat}:
  match value:
    case 0n:
      match bit:
        case False{}: {==}
        case True{}: {==}
    case 1n+ +p:
      match bit:
        case False{}:
          Equal.trans(Nat & Nat, Nat.divmod(2n+Nat.double(p), 2n), Index.next_quotient(Nat.divmod(Nat.double(p), 2n)), (1n+p, 0n), stride(Nat.double(p)), Equal.cong(Nat & Nat, Nat & Nat, Index.next_quotient, Nat.divmod(Nat.double(p), 2n), (p, 0n), binary_division(p, False{})))
        case True{}:
          Equal.trans(Nat & Nat, Nat.divmod(3n+Nat.double(p), 2n), Index.next_quotient(Nat.divmod(1n+Nat.double(p), 2n)), (1n+p, 1n), stride(1n+Nat.double(p)), Equal.cong(Nat & Nat, Nat & Nat, Index.next_quotient, Nat.divmod(1n+Nat.double(p), 2n), (p, 1n), binary_division(p, True{})))

def binary_quotient(+value: Nat, +bit: Bool) -> {Nat.div(Nat.add(S.bit_value(bit), Nat.double(value)), 2n) == value : Nat}:
  Equal.cong(Nat & Nat, Nat, Nat.div.fin, Nat.divmod(Nat.add(S.bit_value(bit), Nat.double(value)), 2n), (value, S.bit_value(bit)), binary_division(value, bit))

def binary_remainder(+value: Nat, +bit: Bool) -> {Nat.mod(Nat.add(S.bit_value(bit), Nat.double(value)), 2n) == S.bit_value(bit) : Nat}:
  Equal.cong(Nat & Nat, Nat, Nat.mod.fin, Nat.divmod(Nat.add(S.bit_value(bit), Nat.double(value)), 2n), (value, S.bit_value(bit)), binary_division(value, bit))

def bit_roundtrip(bit: Bool) -> {Nat.is_eq(S.bit_value(bit), 1n) == bit : Bool}:
  match bit:
    case False{}: {==}
    case True{}: {==}

def binary_constructor(+n: Nat, +value: Nat, +bit: Bool) -> {S.from_nat(1n+n, Nat.add(S.bit_value(bit), Nat.double(value))) == WCon{bit, S.from_nat(n, value)} : Word(1n+n)}:
  %Equal.sym(Nat, Nat.div(Nat.add(S.bit_value(bit), Nat.double(value)), 2n), value, binary_quotient(value, bit)) : {WCon{Nat.is_eq(Nat.mod(Nat.add(S.bit_value(bit), Nat.double(value)), 2n), 1n), S.from_nat(n, _)} == WCon{bit, S.from_nat(n, value)} : Word(1n+n)}
  %Equal.sym(Nat, Nat.mod(Nat.add(S.bit_value(bit), Nat.double(value)), 2n), S.bit_value(bit), binary_remainder(value, bit)) : {WCon{Nat.is_eq(_, 1n), S.from_nat(n, value)} == WCon{bit, S.from_nat(n, value)} : Word(1n+n)}
  Equal.cong(Bool, Word(1n+n), b => WCon{b, S.from_nat(n, value)}, Nat.is_eq(S.bit_value(bit), 1n), bit, bit_roundtrip(bit))

# Reconstruct the low n bits after adding ANY multiple of 2^n. This is a
# universally quantified modular law, not bounded test enumeration.
def regroup(+bit: Bool, +value: Nat, +multiple: Nat) -> {Nat.add(Nat.add(S.bit_value(bit), Nat.double(value)), Nat.double(multiple)) == Nat.add(S.bit_value(bit), Nat.double(Nat.add(value, multiple))) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.add(S.bit_value(bit), Nat.double(value)), Nat.double(multiple)), Nat.add(S.bit_value(bit), Nat.add(Nat.double(value), Nat.double(multiple))), Nat.add(S.bit_value(bit), Nat.double(Nat.add(value, multiple))), Equal.sym(Nat, Nat.add(S.bit_value(bit), Nat.add(Nat.double(value), Nat.double(multiple))), Nat.add(Nat.add(S.bit_value(bit), Nat.double(value)), Nat.double(multiple)), NatLaws.natural_add_associative(S.bit_value(bit), Nat.double(value), Nat.double(multiple))), Equal.cong(Nat, Nat, x => Nat.add(S.bit_value(bit), x), Nat.add(Nat.double(value), Nat.double(multiple)), Nat.double(Nat.add(value, multiple)), Equal.sym(Nat, Nat.double(Nat.add(value, multiple)), Nat.add(Nat.double(value), Nat.double(multiple)), N.double_add(value, multiple))))

def reconstruct(+n: Nat, word: Word(n), +multiple: Nat) -> {S.from_nat(n, Nat.add(S.unsigned(n, word), S.scale_binary(n, multiple))) == word : Word(n)}:
  match n:
    case 0n:
      match word:
        case WNil{}: {==}
    case 1n+ +p:
      match word:
        case WCon{+bit, +tail}:
          %Equal.sym(Nat, Nat.add(Nat.add(S.bit_value(bit), Nat.double(S.unsigned(p, tail))), Nat.double(S.scale_binary(p, multiple))), Nat.add(S.bit_value(bit), Nat.double(Nat.add(S.unsigned(p, tail), S.scale_binary(p, multiple)))), regroup(bit, S.unsigned(p, tail), S.scale_binary(p, multiple))) : {S.from_nat(1n+p, _) == WCon{bit, tail} : Word(1n+p)}
          Equal.trans(Word(1n+p), S.from_nat(1n+p, Nat.add(S.bit_value(bit), Nat.double(Nat.add(S.unsigned(p, tail), S.scale_binary(p, multiple))))), WCon{bit, S.from_nat(p, Nat.add(S.unsigned(p, tail), S.scale_binary(p, multiple)))}, WCon{bit, tail}, binary_constructor(p, Nat.add(S.unsigned(p, tail), S.scale_binary(p, multiple)), bit), Equal.cong(Word(p), Word(1n+p), w => WCon{bit, w}, S.from_nat(p, Nat.add(S.unsigned(p, tail), S.scale_binary(p, multiple))), tail, reconstruct(p, tail, multiple)))

# Actual full-width ripple addition equals independent mathematical conversion.
def add_refines(+a: Word(64n), +b: Word(64n)) -> {W.add(a, b) == S.from_nat(64n, Nat.add(S.unsigned(64n, a), S.unsigned(64n, b))) : Word(64n)}:
  %Add.addition_conservation(a, b) : {W.add(a, b) == S.from_nat(64n, _) : Word(64n)}
  Equal.sym(Word(64n), S.from_nat(64n, Nat.add(S.unsigned(64n, W.add(a, b)), S.scale_binary(64n, S.bit_value(Add.carry_out(64n, a, b, False{}))))), W.add(a, b), reconstruct(64n, W.add(a, b), S.bit_value(Add.carry_out(64n, a, b, False{}))))

def time_add_refines(a: T.Int64, b: T.Int64) -> {Time.add(a, b) == S.add(a, b) : T.Int64}:
  match a b:
    case T.I64{+x} T.I64{+y}:
      Equal.cong(Word(64n), T.Int64, w => T.I64{w}, W.add(x, y), S.from_nat(64n, Nat.add(S.unsigned(64n, x), S.unsigned(64n, y))), add_refines(x, y))

# The same reconstruction discharges wraparound for every metric counter.
def increment_refines(+n: Nat, +word: Word(n)) -> {Word.inc(n, word) == S.from_nat(n, 1n+S.unsigned(n, word)) : Word(n)}:
  %Counter.increment_conservation(n, word) : {Word.inc(n, word) == S.from_nat(n, _) : Word(n)}
  Equal.sym(Word(n), S.from_nat(n, Nat.add(S.unsigned(n, Word.inc(n, word)), S.scale_binary(n, S.bit_value(Counter.carry(n, word))))), Word.inc(n, word), reconstruct(n, Word.inc(n, word), S.bit_value(Counter.carry(n, word))))

def counter_refines(+word: Word(64n)) -> {W.inc(word) == S.from_nat(64n, 1n+S.unsigned(64n, word)) : Word(64n)}:
  increment_refines(64n, word)
