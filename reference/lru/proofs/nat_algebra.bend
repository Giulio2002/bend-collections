import Base

# Commutative-semiring laws of Base Nat.add/Nat.mul, by induction on the actual
# definitions. Used by the host decimal/word conversion proofs.
def succ_equal(a: Nat, b: Nat, e: {a == b : Nat}) -> {1n+a == 1n+b : Nat}:
  Equal.cong(Nat, Nat, x => 1n+x, a, b, e)

def add_zero(n: Nat) -> {Nat.add(n, 0n) == n : Nat}:
  match n:
    case 0n: {==}
    case 1n++p: succ_equal(Nat.add(p, 0n), p, add_zero(p))

def add_succ(a: Nat, +b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n: {==}
    case 1n++p: succ_equal(Nat.add(p, 1n+b), 1n+Nat.add(p, b), add_succ(p, b))

def add_comm(a: Nat, +b: Nat) -> {Nat.add(a, b) == Nat.add(b, a) : Nat}:
  match a:
    case 0n: Equal.sym(Nat, Nat.add(b, 0n), b, add_zero(b))
    case 1n++p: Equal.trans(Nat, 1n+Nat.add(p, b), 1n+Nat.add(b, p), Nat.add(b, 1n+p), succ_equal(Nat.add(p, b), Nat.add(b, p), add_comm(p, b)), Equal.sym(Nat, Nat.add(b, 1n+p), 1n+Nat.add(b, p), add_succ(b, p)))

def add_assoc(a: Nat, +b: Nat, +c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}:
  match a:
    case 0n: {==}
    case 1n++p: succ_equal(Nat.add(Nat.add(p, b), c), Nat.add(p, Nat.add(b, c)), add_assoc(p, b, c))

# a + (b + c) == b + (a + c)
def add_swap(+a: Nat, +b: Nat, +c: Nat) -> {Nat.add(a, Nat.add(b, c)) == Nat.add(b, Nat.add(a, c)) : Nat}:
  Equal.trans(Nat, Nat.add(a, Nat.add(b, c)), Nat.add(Nat.add(a, b), c), Nat.add(b, Nat.add(a, c)),
    Equal.sym(Nat, Nat.add(Nat.add(a, b), c), Nat.add(a, Nat.add(b, c)), add_assoc(a, b, c)),
    Equal.trans(Nat, Nat.add(Nat.add(a, b), c), Nat.add(Nat.add(b, a), c), Nat.add(b, Nat.add(a, c)),
      Equal.cong(Nat, Nat, x => Nat.add(x, c), Nat.add(a, b), Nat.add(b, a), add_comm(a, b)),
      add_assoc(b, a, c)))

def mul_zero(n: Nat) -> {Nat.mul(n, 0n) == 0n : Nat}:
  match n:
    case 0n: {==}
    case 1n++p: mul_zero(p)

def mul_succ(a: Nat, +b: Nat) -> {Nat.mul(a, 1n+b) == Nat.add(a, Nat.mul(a, b)) : Nat}:
  match a:
    case 0n: {==}
    case 1n++p:
      %Equal.sym(Nat, Nat.mul(p, 1n+b), Nat.add(p, Nat.mul(p, b)), mul_succ(p, b)) : {1n+Nat.add(b, _) == 1n+Nat.add(p, Nat.add(b, Nat.mul(p, b))) : Nat}
      succ_equal(Nat.add(b, Nat.add(p, Nat.mul(p, b))), Nat.add(p, Nat.add(b, Nat.mul(p, b))), add_swap(b, p, Nat.mul(p, b)))

def mul_comm(a: Nat, +b: Nat) -> {Nat.mul(a, b) == Nat.mul(b, a) : Nat}:
  match a:
    case 0n: Equal.sym(Nat, Nat.mul(b, 0n), 0n, mul_zero(b))
    case 1n++p:
      %Equal.sym(Nat, Nat.mul(b, 1n+p), Nat.add(b, Nat.mul(b, p)), mul_succ(b, p)) : {Nat.add(b, Nat.mul(p, b)) == _ : Nat}
      Equal.cong(Nat, Nat, x => Nat.add(b, x), Nat.mul(p, b), Nat.mul(b, p), mul_comm(p, b))

def mul_one(+n: Nat) -> {Nat.mul(n, 1n) == n : Nat}:
  Equal.trans(Nat, Nat.mul(n, 1n), Nat.mul(1n, n), n, mul_comm(n, 1n), add_zero(n))

def mul_add_right(a: Nat, +b: Nat, +c: Nat) -> {Nat.mul(Nat.add(a, b), c) == Nat.add(Nat.mul(a, c), Nat.mul(b, c)) : Nat}:
  match a:
    case 0n: {==}
    case 1n++p:
      %Equal.sym(Nat, Nat.mul(Nat.add(p, b), c), Nat.add(Nat.mul(p, c), Nat.mul(b, c)), mul_add_right(p, b, c)) : {Nat.add(c, _) == Nat.add(Nat.add(c, Nat.mul(p, c)), Nat.mul(b, c)) : Nat}
      Equal.sym(Nat, Nat.add(Nat.add(c, Nat.mul(p, c)), Nat.mul(b, c)), Nat.add(c, Nat.add(Nat.mul(p, c), Nat.mul(b, c))), add_assoc(c, Nat.mul(p, c), Nat.mul(b, c)))

def mul_add_left(+a: Nat, +b: Nat, +c: Nat) -> {Nat.mul(a, Nat.add(b, c)) == Nat.add(Nat.mul(a, b), Nat.mul(a, c)) : Nat}:
  %Equal.sym(Nat, Nat.mul(a, Nat.add(b, c)), Nat.mul(Nat.add(b, c), a), mul_comm(a, Nat.add(b, c))) : {_ == Nat.add(Nat.mul(a, b), Nat.mul(a, c)) : Nat}
  %Equal.sym(Nat, Nat.mul(a, b), Nat.mul(b, a), mul_comm(a, b)) : {Nat.mul(Nat.add(b, c), a) == Nat.add(_, Nat.mul(a, c)) : Nat}
  %Equal.sym(Nat, Nat.mul(a, c), Nat.mul(c, a), mul_comm(a, c)) : {Nat.mul(Nat.add(b, c), a) == Nat.add(Nat.mul(b, a), _) : Nat}
  mul_add_right(b, c, a)

def mul_assoc(a: Nat, +b: Nat, +c: Nat) -> {Nat.mul(Nat.mul(a, b), c) == Nat.mul(a, Nat.mul(b, c)) : Nat}:
  match a:
    case 0n: {==}
    case 1n++p:
      %Equal.sym(Nat, Nat.mul(Nat.add(b, Nat.mul(p, b)), c), Nat.add(Nat.mul(b, c), Nat.mul(Nat.mul(p, b), c)), mul_add_right(b, Nat.mul(p, b), c)) : {_ == Nat.add(Nat.mul(b, c), Nat.mul(p, Nat.mul(b, c))) : Nat}
      Equal.cong(Nat, Nat, x => Nat.add(Nat.mul(b, c), x), Nat.mul(Nat.mul(p, b), c), Nat.mul(p, Nat.mul(b, c)), mul_assoc(p, b, c))

def double_add(a: Nat, +b: Nat) -> {Nat.double(Nat.add(a, b)) == Nat.add(Nat.double(a), Nat.double(b)) : Nat}:
  match a:
    case 0n: {==}
    case 1n++p: Equal.cong(Nat, Nat, x => 2n+x, Nat.double(Nat.add(p, b)), Nat.add(Nat.double(p), Nat.double(b)), double_add(p, b))

def double_self(n: Nat) -> {Nat.double(n) == Nat.add(n, n) : Nat}:
  match n:
    case 0n: {==}
    case 1n++p:
      %Equal.sym(Nat, Nat.double(p), Nat.add(p, p), double_self(p)) : {2n+_ == 1n+Nat.add(p, 1n+p) : Nat}
      succ_equal(1n+Nat.add(p, p), Nat.add(p, 1n+p), Equal.sym(Nat, Nat.add(p, 1n+p), 1n+Nat.add(p, p), add_succ(p, p)))

def double_mul(+n: Nat) -> {Nat.double(n) == Nat.mul(2n, n) : Nat}:
  %Equal.sym(Nat, Nat.double(n), Nat.add(n, n), double_self(n)) : {_ == Nat.add(n, Nat.add(n, 0n)) : Nat}
  Equal.cong(Nat, Nat, x => Nat.add(n, x), n, Nat.add(n, 0n), Equal.sym(Nat, Nat.add(n, 0n), n, add_zero(n)))
