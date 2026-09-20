import Base
import ../spec/numeric.bend as S
import ./numeric.bend as N
import ./map_index.bend as Index
import ./native_map.bend as Natural
import ./map_difference_order.bend as Order

# Elementary semiring equations proved over the existing Base Nat definitions.
def interchange(a: Nat, +b: Nat, +c: Nat) -> {Nat.add(a, Nat.add(b, c)) == Nat.add(b, Nat.add(a, c)) : Nat}:
  match a:
    case 0n: {==}
    case 1n+ +p:
      Equal.trans(Nat, 1n+Nat.add(p, Nat.add(b, c)), 1n+Nat.add(b, Nat.add(p, c)), Nat.add(b, 1n+Nat.add(p, c)), Equal.cong(Nat, Nat, x => 1n+x, Nat.add(p, Nat.add(b, c)), Nat.add(b, Nat.add(p, c)), interchange(p, b, c)), Equal.sym(Nat, Nat.add(b, 1n+Nat.add(p, c)), 1n+Nat.add(b, Nat.add(p, c)), Index.add_right_successor(b, Nat.add(p, c))))

def shuffle(a: Nat, +b: Nat, +c: Nat, +d: Nat) -> {Nat.add(Nat.add(a, b), Nat.add(c, d)) == Nat.add(Nat.add(a, c), Nat.add(b, d)) : Nat}:
  match a:
    case 0n: interchange(b, c, d)
    case 1n+ +p:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.add(Nat.add(p, b), Nat.add(c, d)), Nat.add(Nat.add(p, c), Nat.add(b, d)), shuffle(p, b, c, d))

def distribute(a: Nat, +b: Nat, +c: Nat) -> {Nat.mul(a, Nat.add(b, c)) == Nat.add(Nat.mul(a, b), Nat.mul(a, c)) : Nat}:
  match a:
    case 0n: {==}
    case 1n+ +p:
      Equal.trans(Nat, Nat.add(Nat.add(b, c), Nat.mul(p, Nat.add(b, c))), Nat.add(Nat.add(b, c), Nat.add(Nat.mul(p, b), Nat.mul(p, c))), Nat.add(Nat.add(b, Nat.mul(p, b)), Nat.add(c, Nat.mul(p, c))), Equal.cong(Nat, Nat, x => Nat.add(Nat.add(b, c), x), Nat.mul(p, Nat.add(b, c)), Nat.add(Nat.mul(p, b), Nat.mul(p, c)), distribute(p, b, c)), shuffle(b, c, Nat.mul(p, b), Nat.mul(p, c)))

def double_sum(n: Nat) -> {Nat.double(n) == Nat.add(n, n) : Nat}:
  match n:
    case 0n: {==}
    case 1n+ +p:
      Equal.trans(Nat, 2n+Nat.double(p), 2n+Nat.add(p, p), 1n+Nat.add(p, 1n+p), Equal.cong(Nat, Nat, x => 2n+x, Nat.double(p), Nat.add(p, p), double_sum(p)), Equal.cong(Nat, Nat, x => 1n+x, 1n+Nat.add(p, p), Nat.add(p, 1n+p), Equal.sym(Nat, Nat.add(p, 1n+p), 1n+Nat.add(p, p), Index.add_right_successor(p, p))))

def double_product(a: Nat, +b: Nat) -> {Nat.mul(Nat.double(a), b) == Nat.double(Nat.mul(a, b)) : Nat}:
  match a:
    case 0n: {==}
    case 1n+ +p:
      Equal.trans(Nat, Nat.add(b, Nat.add(b, Nat.mul(Nat.double(p), b))), Nat.add(b, Nat.add(b, Nat.double(Nat.mul(p, b)))), Nat.double(Nat.add(b, Nat.mul(p, b))), Equal.cong(Nat, Nat, x => Nat.add(b, Nat.add(b, x)), Nat.mul(Nat.double(p), b), Nat.double(Nat.mul(p, b)), double_product(p, b)), Equal.trans(Nat, Nat.add(b, Nat.add(b, Nat.double(Nat.mul(p, b)))), Nat.add(Nat.double(b), Nat.double(Nat.mul(p, b))), Nat.double(Nat.add(b, Nat.mul(p, b))), Equal.trans(Nat, Nat.add(b, Nat.add(b, Nat.double(Nat.mul(p, b)))), Nat.add(Nat.add(b, b), Nat.double(Nat.mul(p, b))), Nat.add(Nat.double(b), Nat.double(Nat.mul(p, b))), Natural.natural_add_associative(b, b, Nat.double(Nat.mul(p, b))), Equal.cong(Nat, Nat, x => Nat.add(x, Nat.double(Nat.mul(p, b))), Nat.add(b, b), Nat.double(b), Equal.sym(Nat, Nat.double(b), Nat.add(b, b), double_sum(b)))), Equal.sym(Nat, Nat.double(Nat.add(b, Nat.mul(p, b))), Nat.add(Nat.double(b), Nat.double(Nat.mul(p, b))), N.double_add(b, Nat.mul(p, b)))))

def multiply_double(+a: Nat, +b: Nat) -> {Nat.mul(a, Nat.double(b)) == Nat.double(Nat.mul(a, b)) : Nat}:
  %Equal.sym(Nat, Nat.double(b), Nat.add(b, b), double_sum(b)) : {Nat.mul(a, _) == Nat.double(Nat.mul(a, b)) : Nat}
  Equal.trans(Nat, Nat.mul(a, Nat.add(b, b)), Nat.add(Nat.mul(a, b), Nat.mul(a, b)), Nat.double(Nat.mul(a, b)), distribute(a, b, b), Equal.sym(Nat, Nat.double(Nat.mul(a, b)), Nat.add(Nat.mul(a, b), Nat.mul(a, b)), double_sum(Nat.mul(a, b))))

def scale_sum(n: Nat, +a: Nat, +b: Nat) -> {S.scale_binary(n, Nat.add(a, b)) == Nat.add(S.scale_binary(n, a), S.scale_binary(n, b)) : Nat}:
  match n:
    case 0n: {==}
    case 1n+ +p:
      Equal.trans(Nat, Nat.double(S.scale_binary(p, Nat.add(a, b))), Nat.double(Nat.add(S.scale_binary(p, a), S.scale_binary(p, b))), Nat.add(Nat.double(S.scale_binary(p, a)), Nat.double(S.scale_binary(p, b))), Equal.cong(Nat, Nat, Nat.double, S.scale_binary(p, Nat.add(a, b)), Nat.add(S.scale_binary(p, a), S.scale_binary(p, b)), scale_sum(p, a, b)), N.double_add(S.scale_binary(p, a), S.scale_binary(p, b)))

def scale_product(n: Nat, +a: Nat, +b: Nat) -> {S.scale_binary(n, Nat.mul(a, b)) == Nat.mul(a, S.scale_binary(n, b)) : Nat}:
  match n:
    case 0n: {==}
    case 1n+ +p:
      Equal.trans(Nat, Nat.double(S.scale_binary(p, Nat.mul(a, b))), Nat.double(Nat.mul(a, S.scale_binary(p, b))), Nat.mul(a, Nat.double(S.scale_binary(p, b))), Equal.cong(Nat, Nat, Nat.double, S.scale_binary(p, Nat.mul(a, b)), Nat.mul(a, S.scale_binary(p, b)), scale_product(p, a, b)), Equal.sym(Nat, Nat.mul(a, Nat.double(S.scale_binary(p, b))), Nat.double(Nat.mul(a, S.scale_binary(p, b))), multiply_double(a, S.scale_binary(p, b))))
