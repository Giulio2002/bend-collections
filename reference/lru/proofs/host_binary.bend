import Base
import ../src/host.bend as H
import ../spec/host.bend as S
import ../spec/numeric.bend as N
import ./host_decimal.bend as Dec
import ./nat_algebra.bend as A
import ./natural_products.bend as Product
import ./addition_bounds.bend as AddBounds
import ./negation_magnitude.bend as Magnitude
import ./counter.bend as Counter
import ./word_bounds.bend as WordBounds
import ./division_quotient.bend as Quotient
import ./map_routing.bend as Routing

# Decimal digits to binary words by exact halving (src/host.bend binary):
# the word holds the low n bits of the value and the leftover digits its high
# part; out-of-range input is detected without any runtime natural above 2^48.
def hval(ds: List<&2, H.Digit>, a: Nat) -> Nat:
  Dec.hval(ds, a)

def hq(h: H.Half) -> List<&2, H.Digit>:
  H.Half{q, b} = h
  q

def hb(h: H.Half) -> Bool:
  H.Half{q, b} = h
  b

def prepend_q(+d: H.Digit, h: H.Half) -> {hq(H.prepend(d, h)) == Con{d, hq(h)} : List<&2, H.Digit>}:
  H.Half{q, b} = h
  {==}

def prepend_b(+d: H.Digit, h: H.Half) -> {hb(H.prepend(d, h)) == hb(h) : Bool}:
  H.Half{q, b} = h
  {==}

def bit(b: Bool) -> Nat:
  N.bit_value(b)

# 2*(a*10 + Q) + R' == (2a + R)*10 + K, given the digit fact 2Q + R' == 10R + K.
def halve_arith(+a: Nat, +q: Nat, +r2: Nat, +r: Nat, +k: Nat, fact: {Nat.add(Nat.double(q), r2) == Nat.add(Nat.mul(r, 10n), k) : Nat}) -> {Nat.add(Nat.double(Nat.add(Nat.mul(a, 10n), q)), r2) == Nat.add(Nat.mul(Nat.add(Nat.double(a), r), 10n), k) : Nat}:
  %Equal.sym(Nat, Nat.double(Nat.add(Nat.mul(a, 10n), q)), Nat.add(Nat.double(Nat.mul(a, 10n)), Nat.double(q)), A.double_add(Nat.mul(a, 10n), q)) : {Nat.add(_, r2) == Nat.add(Nat.mul(Nat.add(Nat.double(a), r), 10n), k) : Nat}
  %Equal.sym(Nat, Nat.mul(Nat.add(Nat.double(a), r), 10n), Nat.add(Nat.mul(Nat.double(a), 10n), Nat.mul(r, 10n)), A.mul_add_right(Nat.double(a), r, 10n)) : {Nat.add(Nat.add(Nat.double(Nat.mul(a, 10n)), Nat.double(q)), r2) == Nat.add(_, k) : Nat}
  %Equal.sym(Nat, Nat.mul(Nat.double(a), 10n), Nat.double(Nat.mul(a, 10n)), Product.double_product(a, 10n)) : {Nat.add(Nat.add(Nat.double(Nat.mul(a, 10n)), Nat.double(q)), r2) == Nat.add(Nat.add(_, Nat.mul(r, 10n)), k) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(Nat.double(Nat.mul(a, 10n)), Nat.double(q)), r2), Nat.add(Nat.double(Nat.mul(a, 10n)), Nat.add(Nat.double(q), r2)), A.add_assoc(Nat.double(Nat.mul(a, 10n)), Nat.double(q), r2)) : {_ == Nat.add(Nat.add(Nat.double(Nat.mul(a, 10n)), Nat.mul(r, 10n)), k) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(Nat.double(Nat.mul(a, 10n)), Nat.mul(r, 10n)), k), Nat.add(Nat.double(Nat.mul(a, 10n)), Nat.add(Nat.mul(r, 10n), k)), A.add_assoc(Nat.double(Nat.mul(a, 10n)), Nat.mul(r, 10n), k)) : {Nat.add(Nat.double(Nat.mul(a, 10n)), Nat.add(Nat.double(q), r2)) == _ : Nat}
  Equal.cong(Nat, Nat, x => Nat.add(Nat.double(Nat.mul(a, 10n)), x), Nat.add(Nat.double(q), r2), Nat.add(Nat.mul(r, 10n), k), fact)

def halve_case(+t: List<&2, H.Digit>, +a: Nat, +dk: H.Digit, +dq: H.Digit, +r: Bool, +r2: Bool, fact: {Nat.add(Nat.double(Dec.dnat(dq)), bit(r2)) == Nat.add(Nat.mul(bit(r), 10n), Dec.dnat(dk)) : Nat}, ih: {Nat.add(Nat.double(hval(hq(H.halve(t, r2)), Nat.add(Nat.mul(a, 10n), Dec.dnat(dq)))), bit(hb(H.halve(t, r2)))) == hval(t, Nat.add(Nat.double(Nat.add(Nat.mul(a, 10n), Dec.dnat(dq))), bit(r2))) : Nat}) -> {Nat.add(Nat.double(hval(hq(H.prepend(dq, H.halve(t, r2))), a)), bit(hb(H.prepend(dq, H.halve(t, r2))))) == hval(Con{dk, t}, Nat.add(Nat.double(a), bit(r))) : Nat}:
  %Equal.sym(List<&2, H.Digit>, hq(H.prepend(dq, H.halve(t, r2))), Con{dq, hq(H.halve(t, r2))}, prepend_q(dq, H.halve(t, r2))) : {Nat.add(Nat.double(hval(_, a)), bit(hb(H.prepend(dq, H.halve(t, r2))))) == hval(Con{dk, t}, Nat.add(Nat.double(a), bit(r))) : Nat}
  %Equal.sym(Bool, hb(H.prepend(dq, H.halve(t, r2))), hb(H.halve(t, r2)), prepend_b(dq, H.halve(t, r2))) : {Nat.add(Nat.double(hval(Con{dq, hq(H.halve(t, r2))}, a)), bit(_)) == hval(Con{dk, t}, Nat.add(Nat.double(a), bit(r))) : Nat}
  Equal.trans(Nat, Nat.add(Nat.double(hval(hq(H.halve(t, r2)), Nat.add(Nat.mul(a, 10n), Dec.dnat(dq)))), bit(hb(H.halve(t, r2)))), hval(t, Nat.add(Nat.double(Nat.add(Nat.mul(a, 10n), Dec.dnat(dq))), bit(r2))), hval(t, Nat.add(Nat.mul(Nat.add(Nat.double(a), bit(r)), 10n), Dec.dnat(dk))), ih, Equal.cong(Nat, Nat, x => hval(t, x), Nat.add(Nat.double(Nat.add(Nat.mul(a, 10n), Dec.dnat(dq))), bit(r2)), Nat.add(Nat.mul(Nat.add(Nat.double(a), bit(r)), 10n), Dec.dnat(dk)), halve_arith(a, Dec.dnat(dq), bit(r2), bit(r), Dec.dnat(dk), fact)))

# Halving invariant: 2*quotient + remainder bit == incoming remainder*10^len + value.
def halve_value(ds: List<&2, H.Digit>, r: Bool, +a: Nat) -> {Nat.add(Nat.double(hval(hq(H.halve(ds, r)), a)), bit(hb(H.halve(ds, r)))) == hval(ds, Nat.add(Nat.double(a), bit(r))) : Nat}:
  match ds r:
    case Nil{} r0: {==}
    case Con{H.D0{}, +t} False{}: halve_case(t, a, H.D0{}, H.D0{}, False{}, False{}, {==}, halve_value(t, False{}, Nat.add(Nat.mul(a, 10n), 0n)))
    case Con{H.D1{}, +t} False{}: halve_case(t, a, H.D1{}, H.D0{}, False{}, True{}, {==}, halve_value(t, True{}, Nat.add(Nat.mul(a, 10n), 0n)))
    case Con{H.D2{}, +t} False{}: halve_case(t, a, H.D2{}, H.D1{}, False{}, False{}, {==}, halve_value(t, False{}, Nat.add(Nat.mul(a, 10n), 1n)))
    case Con{H.D3{}, +t} False{}: halve_case(t, a, H.D3{}, H.D1{}, False{}, True{}, {==}, halve_value(t, True{}, Nat.add(Nat.mul(a, 10n), 1n)))
    case Con{H.D4{}, +t} False{}: halve_case(t, a, H.D4{}, H.D2{}, False{}, False{}, {==}, halve_value(t, False{}, Nat.add(Nat.mul(a, 10n), 2n)))
    case Con{H.D5{}, +t} False{}: halve_case(t, a, H.D5{}, H.D2{}, False{}, True{}, {==}, halve_value(t, True{}, Nat.add(Nat.mul(a, 10n), 2n)))
    case Con{H.D6{}, +t} False{}: halve_case(t, a, H.D6{}, H.D3{}, False{}, False{}, {==}, halve_value(t, False{}, Nat.add(Nat.mul(a, 10n), 3n)))
    case Con{H.D7{}, +t} False{}: halve_case(t, a, H.D7{}, H.D3{}, False{}, True{}, {==}, halve_value(t, True{}, Nat.add(Nat.mul(a, 10n), 3n)))
    case Con{H.D8{}, +t} False{}: halve_case(t, a, H.D8{}, H.D4{}, False{}, False{}, {==}, halve_value(t, False{}, Nat.add(Nat.mul(a, 10n), 4n)))
    case Con{H.D9{}, +t} False{}: halve_case(t, a, H.D9{}, H.D4{}, False{}, True{}, {==}, halve_value(t, True{}, Nat.add(Nat.mul(a, 10n), 4n)))
    case Con{H.D0{}, +t} True{}: halve_case(t, a, H.D0{}, H.D5{}, True{}, False{}, {==}, halve_value(t, False{}, Nat.add(Nat.mul(a, 10n), 5n)))
    case Con{H.D1{}, +t} True{}: halve_case(t, a, H.D1{}, H.D5{}, True{}, True{}, {==}, halve_value(t, True{}, Nat.add(Nat.mul(a, 10n), 5n)))
    case Con{H.D2{}, +t} True{}: halve_case(t, a, H.D2{}, H.D6{}, True{}, False{}, {==}, halve_value(t, False{}, Nat.add(Nat.mul(a, 10n), 6n)))
    case Con{H.D3{}, +t} True{}: halve_case(t, a, H.D3{}, H.D6{}, True{}, True{}, {==}, halve_value(t, True{}, Nat.add(Nat.mul(a, 10n), 6n)))
    case Con{H.D4{}, +t} True{}: halve_case(t, a, H.D4{}, H.D7{}, True{}, False{}, {==}, halve_value(t, False{}, Nat.add(Nat.mul(a, 10n), 7n)))
    case Con{H.D5{}, +t} True{}: halve_case(t, a, H.D5{}, H.D7{}, True{}, True{}, {==}, halve_value(t, True{}, Nat.add(Nat.mul(a, 10n), 7n)))
    case Con{H.D6{}, +t} True{}: halve_case(t, a, H.D6{}, H.D8{}, True{}, False{}, {==}, halve_value(t, False{}, Nat.add(Nat.mul(a, 10n), 8n)))
    case Con{H.D7{}, +t} True{}: halve_case(t, a, H.D7{}, H.D8{}, True{}, True{}, {==}, halve_value(t, True{}, Nat.add(Nat.mul(a, 10n), 8n)))
    case Con{H.D8{}, +t} True{}: halve_case(t, a, H.D8{}, H.D9{}, True{}, False{}, {==}, halve_value(t, False{}, Nat.add(Nat.mul(a, 10n), 9n)))
    case Con{H.D9{}, +t} True{}: halve_case(t, a, H.D9{}, H.D9{}, True{}, True{}, {==}, halve_value(t, True{}, Nat.add(Nat.mul(a, 10n), 9n)))

def wd(-n: Nat, r: Word(n) & List<&2, H.Digit>) -> Word(n):
  (w, l) = r
  w

def lf(-n: Nat, r: Word(n) & List<&2, H.Digit>) -> List<&2, H.Digit>:
  (w, l) = r
  l

def split_eq(-p: Nat, h: H.Half, f: List<&2, H.Digit> -> Bool -> Word(1n+p) & List<&2, H.Digit>) -> {H.split(p, h, f) == f(hq(h))(hb(h)) : Word(1n+p) & List<&2, H.Digit>}:
  H.Half{q, b} = h
  {==}

def attach_w(+b: Bool, -p: Nat, r: Word(p) & List<&2, H.Digit>) -> {wd(1n+p, H.attach(b, p, r)) == WCon{b, wd(p, r)} : Word(1n+p)}:
  (w, l) = r
  {==}

def attach_l(+b: Bool, -p: Nat, r: Word(p) & List<&2, H.Digit>) -> {lf(1n+p, H.attach(b, p, r)) == lf(p, r) : List<&2, H.Digit>}:
  (w, l) = r
  {==}

def binary_arith(+b: Bool, +u: Nat, +sc: Nat, +q: Nat, +v: Nat, ih: {Nat.add(u, sc) == q : Nat}, half: {Nat.add(Nat.double(q), bit(b)) == v : Nat}) -> {Nat.add(Nat.add(bit(b), Nat.double(u)), Nat.double(sc)) == v : Nat}:
  %Equal.sym(Nat, Nat.add(Nat.add(bit(b), Nat.double(u)), Nat.double(sc)), Nat.add(bit(b), Nat.add(Nat.double(u), Nat.double(sc))), A.add_assoc(bit(b), Nat.double(u), Nat.double(sc))) : {_ == v : Nat}
  %A.double_add(u, sc) : {Nat.add(bit(b), _) == v : Nat}
  %Equal.sym(Nat, Nat.add(u, sc), q, ih) : {Nat.add(bit(b), Nat.double(_)) == v : Nat}
  Equal.trans(Nat, Nat.add(bit(b), Nat.double(q)), Nat.add(Nat.double(q), bit(b)), v, A.add_comm(bit(b), Nat.double(q)), half)

def binary_step(+p: Nat, +ds: List<&2, H.Digit>, ih: {Nat.add(N.unsigned(p, wd(p, H.binary(p, hq(H.halve(ds, False{}))))), N.scale_binary(p, hval(lf(p, H.binary(p, hq(H.halve(ds, False{})))), 0n))) == hval(hq(H.halve(ds, False{})), 0n) : Nat}) -> {Nat.add(N.unsigned(1n+p, wd(1n+p, H.attach(hb(H.halve(ds, False{})), p, H.binary(p, hq(H.halve(ds, False{})))))), N.scale_binary(1n+p, hval(lf(1n+p, H.attach(hb(H.halve(ds, False{})), p, H.binary(p, hq(H.halve(ds, False{}))))), 0n))) == hval(ds, 0n) : Nat}:
  %Equal.sym(Word(1n+p), wd(1n+p, H.attach(hb(H.halve(ds, False{})), p, H.binary(p, hq(H.halve(ds, False{}))))), WCon{hb(H.halve(ds, False{})), wd(p, H.binary(p, hq(H.halve(ds, False{}))))}, attach_w(hb(H.halve(ds, False{})), p, H.binary(p, hq(H.halve(ds, False{}))))) : {Nat.add(N.unsigned(1n+p, _), N.scale_binary(1n+p, hval(lf(1n+p, H.attach(hb(H.halve(ds, False{})), p, H.binary(p, hq(H.halve(ds, False{}))))), 0n))) == hval(ds, 0n) : Nat}
  %Equal.sym(List<&2, H.Digit>, lf(1n+p, H.attach(hb(H.halve(ds, False{})), p, H.binary(p, hq(H.halve(ds, False{}))))), lf(p, H.binary(p, hq(H.halve(ds, False{})))), attach_l(hb(H.halve(ds, False{})), p, H.binary(p, hq(H.halve(ds, False{}))))) : {Nat.add(N.unsigned(1n+p, WCon{hb(H.halve(ds, False{})), wd(p, H.binary(p, hq(H.halve(ds, False{}))))}), N.scale_binary(1n+p, hval(_, 0n))) == hval(ds, 0n) : Nat}
  binary_arith(hb(H.halve(ds, False{})), N.unsigned(p, wd(p, H.binary(p, hq(H.halve(ds, False{}))))), N.scale_binary(p, hval(lf(p, H.binary(p, hq(H.halve(ds, False{})))), 0n)), hval(hq(H.halve(ds, False{})), 0n), hval(ds, 0n), ih, halve_value(ds, False{}, 0n))

# The word and leftover returned by binary(n, ds) reconstruct the value.
def binary_value(n: Nat, +ds: List<&2, H.Digit>) -> {Nat.add(N.unsigned(n, wd(n, H.binary(n, ds))), N.scale_binary(n, hval(lf(n, H.binary(n, ds)), 0n))) == hval(ds, 0n) : Nat}:
  match n:
    case 0n: {==}
    case 1n++p:
      %Equal.sym(Word(1n+p) & List<&2, H.Digit>, H.split(p, H.halve(ds, False{}), q => b => H.attach(b, p, H.binary(p, q))), H.attach(hb(H.halve(ds, False{})), p, H.binary(p, hq(H.halve(ds, False{})))), split_eq(p, H.halve(ds, False{}), q => b => H.attach(b, p, H.binary(p, q)))) : {Nat.add(N.unsigned(1n+p, wd(1n+p, _)), N.scale_binary(1n+p, hval(lf(1n+p, _), 0n))) == hval(ds, 0n) : Nat}
      binary_step(p, ds, binary_value(p, hq(H.halve(ds, False{}))))

def zero_value(ds: List<&2, H.Digit>, z: {H.zeros(ds) == True{} : Bool}) -> {hval(ds, 0n) == 0n : Nat}:
  match ds:
    case Nil{}: {==}
    case Con{d, t}:
      match d:
        case H.D0{}: zero_value(t, z)
        case H.D1{}: Empty.absurd({hval(Con{H.D1{}, t}, 0n) == 0n : Nat}, Routing.false_true(z))
        case H.D2{}: Empty.absurd({hval(Con{H.D2{}, t}, 0n) == 0n : Nat}, Routing.false_true(z))
        case H.D3{}: Empty.absurd({hval(Con{H.D3{}, t}, 0n) == 0n : Nat}, Routing.false_true(z))
        case H.D4{}: Empty.absurd({hval(Con{H.D4{}, t}, 0n) == 0n : Nat}, Routing.false_true(z))
        case H.D5{}: Empty.absurd({hval(Con{H.D5{}, t}, 0n) == 0n : Nat}, Routing.false_true(z))
        case H.D6{}: Empty.absurd({hval(Con{H.D6{}, t}, 0n) == 0n : Nat}, Routing.false_true(z))
        case H.D7{}: Empty.absurd({hval(Con{H.D7{}, t}, 0n) == 0n : Nat}, Routing.false_true(z))
        case H.D8{}: Empty.absurd({hval(Con{H.D8{}, t}, 0n) == 0n : Nat}, Routing.false_true(z))
        case H.D9{}: Empty.absurd({hval(Con{H.D9{}, t}, 0n) == 0n : Nat}, Routing.false_true(z))

def positive_acc(ds: List<&2, H.Digit>, a: Nat, ha: {Nat.is_lt(0n, a) == True{} : Bool}) -> {Nat.is_lt(0n, hval(ds, a)) == True{} : Bool}:
  match ds:
    case Nil{}: ha
    case Con{d, t}:
      match a:
        case 0n: Empty.absurd({Nat.is_lt(0n, hval(Con{d, t}, 0n)) == True{} : Bool}, Routing.false_true(ha))
        case 1n+ap: positive_acc(t, Nat.add(Nat.mul(1n+ap, 10n), Dec.dnat(d)), {==})

def positive(ds: List<&2, H.Digit>, z: {H.zeros(ds) == False{} : Bool}) -> {Nat.is_lt(0n, hval(ds, 0n)) == True{} : Bool}:
  match ds:
    case Nil{}: Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, Routing.false_true(Equal.sym(Bool, True{}, False{}, z)))
    case Con{d, t}:
      match d:
        case H.D0{}: positive(t, z)
        case H.D1{}: positive_acc(t, 1n, {==})
        case H.D2{}: positive_acc(t, 2n, {==})
        case H.D3{}: positive_acc(t, 3n, {==})
        case H.D4{}: positive_acc(t, 4n, {==})
        case H.D5{}: positive_acc(t, 5n, {==})
        case H.D6{}: positive_acc(t, 6n, {==})
        case H.D7{}: positive_acc(t, 7n, {==})
        case H.D8{}: positive_acc(t, 8n, {==})
        case H.D9{}: positive_acc(t, 9n, {==})
