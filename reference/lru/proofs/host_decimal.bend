import Base
import ../src/host.bend as H
import ../spec/host.bend as S
import ./nat_algebra.bend as A
import ./map_routing.bend as Routing

# Decimal digit strings: the implementation's digit lists (src/host.bend) have
# exactly the positional value of the independent specification (spec/host.bend).
def dnat(d: H.Digit) -> Nat:
  match d:
    case H.D0{}: 0n
    case H.D1{}: 1n
    case H.D2{}: 2n
    case H.D3{}: 3n
    case H.D4{}: 4n
    case H.D5{}: 5n
    case H.D6{}: 6n
    case H.D7{}: 7n
    case H.D8{}: 8n
    case H.D9{}: 9n

# Big-endian value by accumulation (proof-level).
def hval(ds: List<&2, H.Digit>, a: Nat) -> Nat:
  match ds:
    case Nil{}: a
    case Con{d, t}: hval(t, Nat.add(Nat.mul(a, 10n), dnat(d)))

def dmap(m: Maybe<&2, H.Digit>) -> Maybe<&2, Nat>:
  match m:
    case None{}: None{}
    case Some{d}: Some{dnat(d)}

def hopt(+a: Nat, m: Maybe<&2, List<&2, H.Digit>>) -> Maybe<&2, Nat>:
  match m:
    case None{}: None{}
    case Some{ds}: Some{hval(ds, a)}

def scaled(+a: Nat, +len: Nat, m: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match m:
    case None{}: None{}
    case Some{v}: Some{Nat.add(Nat.mul(a, Nat.pow(10n, len)), v)}

def aligned(cs: String, ds: List<&2, H.Digit>, i: Nat) -> Type:
  match cs ds:
    case SNil{} Nil{}: Unit
    case SCon{c, ct} Con{d, dt}: {dnat(d) == i : Nat} & aligned(ct, dt, 1n+i)
    case x y: Empty

def pick_agree(b: Bool, +d: H.Digit, +i: Nat, rest: Maybe<&2, H.Digit>, spec: Maybe<&2, Nat>, same: {dnat(d) == i : Nat}, ih: {dmap(rest) == spec : Maybe<&2, Nat>}) -> {dmap(H.pick(b, d, rest)) == S.digit_pick(b, i, spec) : Maybe<&2, Nat>}:
  match b:
    case True{}: Equal.cong(Nat, Maybe<&2, Nat>, x => Some{x}, dnat(d), i, same)
    case False{}: ih

def search_agree(+c: Char, cs: String, ds: List<&2, H.Digit>, +i: Nat, al: aligned(cs, ds, i)) -> {dmap(H.search(c, cs, ds)) == S.digit_in(c, cs, i) : Maybe<&2, Nat>}:
  match cs ds:
    case SNil{} Nil{}: {==}
    case SCon{+x, +ct} Con{+d, +dt}:
      (same, rest) = al
      pick_agree(Char.is_eq(c, x), d, i, H.search(c, ct, dt), S.digit_in(c, ct, 1n+i), same, search_agree(c, ct, dt, 1n+i, rest))
    case SNil{} Con{d, dt}: Empty.absurd({dmap(H.search(c, SNil{}, Con{d, dt})) == S.digit_in(c, SNil{}, i) : Maybe<&2, Nat>}, al)
    case SCon{x, ct} Nil{}: Empty.absurd({dmap(H.search(c, SCon{x, ct}, Nil{})) == S.digit_in(c, SCon{x, ct}, i) : Maybe<&2, Nat>}, al)

# The implementation's digit recognition equals the specification's.
def digit_agree(+c: Char) -> {dmap(H.digit(c)) == S.digit_value(c) : Maybe<&2, Nat>}:
  search_agree(c, "0123456789", H.all_digits(), 0n, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, Unit{})))))))))))

def some_inj(+x: Nat, +y: Nat, e: {Some{x} == Some{y} : Maybe<&2, Nat>}) -> {x == y : Nat}:
  Equal.cong(Maybe<&2, Nat>, Nat, m => Maybe.default(&2, Nat, m, x), Some{x}, Some{y}, e)

def maybe_shape(a: Maybe<&2, Nat>, b: Maybe<&2, Nat>) -> Type:
  match a b:
    case None{} None{}: Unit
    case Some{x} Some{y}: Unit
    case x y: Empty

def maybe_refl(a: Maybe<&2, Nat>) -> maybe_shape(a, a):
  match a:
    case None{}: Unit{}
    case Some{x}: Unit{}

def maybe_clash(a: Maybe<&2, Nat>, b: Maybe<&2, Nat>, e: {a == b : Maybe<&2, Nat>}) -> maybe_shape(a, b):
  %e : maybe_shape(a, _)
  maybe_refl(a)

# ((a*10 + x) * P) + v == a * (10 * P) + (x * P + v)
def horner_step(+a: Nat, +x: Nat, +p: Nat, +v: Nat) -> {Nat.add(Nat.mul(Nat.add(Nat.mul(a, 10n), x), p), v) == Nat.add(Nat.mul(a, Nat.mul(10n, p)), Nat.add(Nat.mul(x, p), v)) : Nat}:
  %Equal.sym(Nat, Nat.mul(Nat.add(Nat.mul(a, 10n), x), p), Nat.add(Nat.mul(Nat.mul(a, 10n), p), Nat.mul(x, p)), A.mul_add_right(Nat.mul(a, 10n), x, p)) : {Nat.add(_, v) == Nat.add(Nat.mul(a, Nat.mul(10n, p)), Nat.add(Nat.mul(x, p), v)) : Nat}
  %Equal.sym(Nat, Nat.mul(Nat.mul(a, 10n), p), Nat.mul(a, Nat.mul(10n, p)), A.mul_assoc(a, 10n, p)) : {Nat.add(Nat.add(_, Nat.mul(x, p)), v) == Nat.add(Nat.mul(a, Nat.mul(10n, p)), Nat.add(Nat.mul(x, p), v)) : Nat}
  A.add_assoc(Nat.mul(a, Nat.mul(10n, p)), Nat.mul(x, p), v)

def cons_some(+a: Nat, +len: Nat, +x: H.Digit, m: Maybe<&2, List<&2, H.Digit>>, p: Maybe<&2, Nat>, ih: @+b: Nat -> {hopt(b, m) == scaled(b, len, p) : Maybe<&2, Nat>}) -> {hopt(a, H.cons(Some{x}, m)) == scaled(a, 1n+len, S.place(Some{dnat(x)}, len, p)) : Maybe<&2, Nat>}:
  match m p:
    case None{} None{}: {==}
    case None{} Some{v}: Empty.absurd({hopt(a, H.cons(Some{x}, None{})) == scaled(a, 1n+len, S.place(Some{dnat(x)}, len, Some{v})) : Maybe<&2, Nat>}, maybe_clash(None{}, Some{Nat.add(Nat.mul(0n, Nat.pow(10n, len)), v)}, ih(0n)))
    case Some{ds} None{}: Empty.absurd({hopt(a, H.cons(Some{x}, Some{ds})) == scaled(a, 1n+len, S.place(Some{dnat(x)}, len, None{})) : Maybe<&2, Nat>}, maybe_clash(Some{hval(ds, 0n)}, None{}, ih(0n)))
    case Some{+ds} Some{+v}:
      Equal.cong(Nat, Maybe<&2, Nat>, y => Some{y}, hval(ds, Nat.add(Nat.mul(a, 10n), dnat(x))), Nat.add(Nat.mul(a, Nat.mul(10n, Nat.pow(10n, len))), Nat.add(Nat.mul(dnat(x), Nat.pow(10n, len)), v)),
        Equal.trans(Nat, hval(ds, Nat.add(Nat.mul(a, 10n), dnat(x))), Nat.add(Nat.mul(Nat.add(Nat.mul(a, 10n), dnat(x)), Nat.pow(10n, len)), v), Nat.add(Nat.mul(a, Nat.mul(10n, Nat.pow(10n, len))), Nat.add(Nat.mul(dnat(x), Nat.pow(10n, len)), v)),
          some_inj(hval(ds, Nat.add(Nat.mul(a, 10n), dnat(x))), Nat.add(Nat.mul(Nat.add(Nat.mul(a, 10n), dnat(x)), Nat.pow(10n, len)), v), ih(Nat.add(Nat.mul(a, 10n), dnat(x)))),
          horner_step(a, dnat(x), Nat.pow(10n, len), v)))

def cons_value(+a: Nat, +len: Nat, d: Maybe<&2, H.Digit>, m: Maybe<&2, List<&2, H.Digit>>, p: Maybe<&2, Nat>, ih: @+b: Nat -> {hopt(b, m) == scaled(b, len, p) : Maybe<&2, Nat>}) -> {hopt(a, H.cons(d, m)) == scaled(a, 1n+len, S.place(dmap(d), len, p)) : Maybe<&2, Nat>}:
  match d:
    case None{}: {==}
    case Some{+x}: cons_some(a, len, x, m, p, ih)

def nil_value(+a: Nat) -> {Some{a} == Some{Nat.add(Nat.mul(a, 1n), 0n)} : Maybe<&2, Nat>}:
  Equal.cong(Nat, Maybe<&2, Nat>, y => Some{y}, a, Nat.add(Nat.mul(a, 1n), 0n), Equal.sym(Nat, Nat.add(Nat.mul(a, 1n), 0n), a, Equal.trans(Nat, Nat.add(Nat.mul(a, 1n), 0n), Nat.mul(a, 1n), a, A.add_zero(Nat.mul(a, 1n)), A.mul_one(a))))

# Digit lists of a string have its positional value, scaled past an accumulator.
def digits_value(s: String, +a: Nat) -> {hopt(a, H.digits(s)) == scaled(a, String.length(s), S.positional(s)) : Maybe<&2, Nat>}:
  match s:
    case SNil{}: nil_value(a)
    case SCon{+c, +t}:
      %digit_agree(c) : {hopt(a, H.cons(H.digit(c), H.digits(t))) == scaled(a, 1n+String.length(t), S.place(_, String.length(t), S.positional(t))) : Maybe<&2, Nat>}
      cons_value(a, String.length(t), H.digit(c), H.digits(t), S.positional(t), b => digits_value(t, b))

def identity_scale(+len: Nat, p: Maybe<&2, Nat>) -> {scaled(0n, len, p) == p : Maybe<&2, Nat>}:
  match p:
    case None{}: {==}
    case Some{v}: {==}

# A natural numeral's value: the implementation's digits have the spec value.
def numeral_value(s: String) -> {hopt(0n, H.numeral(s)) == S.natural(s) : Maybe<&2, Nat>}:
  match s:
    case SNil{}: {==}
    case SCon{+c, +t}: Equal.trans(Maybe<&2, Nat>, hopt(0n, H.digits(SCon{c, t})), scaled(0n, String.length(SCon{c, t}), S.positional(SCon{c, t})), S.positional(SCon{c, t}), digits_value(SCon{c, t}, 0n), identity_scale(String.length(SCon{c, t}), S.positional(SCon{c, t})))
