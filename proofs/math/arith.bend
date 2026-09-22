import Base
import ../lemmas/spec/numeric.bend as S
import ../lib/nat.bend as N
import ../lib/logic.bend as L
import ../lib/u32alg.bend as A
import ../lemmas/proofs/nat_algebra.bend as NA
import ../lemmas/proofs/natural_products.bend as PR

# Nat facts about scaling by powers of two (sc(k, x) = x * 2^k), used by the
# 64-bit long division. Bounds that would be large closed Nats are written
# over a symbolic `one` with {one == 1n}, as in word.bend.

def sc(+n: Nat, +k: Nat) -> Nat:
  S.scale_binary(n, k)

def mul_sc(+k: Nat, +x: Nat) -> {Nat.mul(x, sc(k, 1n)) == sc(k, x) : Nat}:
  match k:
    case 0n:
      NA.mul_one(x)
    case 1n+j:
      Equal.trans(Nat, Nat.mul(x, Nat.double(sc(j, 1n))), Nat.double(Nat.mul(x, sc(j, 1n))), Nat.double(sc(j, x)), PR.multiply_double(x, sc(j, 1n)), Equal.cong(Nat, Nat, Nat.double, Nat.mul(x, sc(j, 1n)), sc(j, x), mul_sc(j, x)))

def mul_sc1(+k: Nat, +one: Nat, +h1: {one == 1n : Nat}, +x: Nat) -> {Nat.mul(x, sc(k, one)) == sc(k, x) : Nat}:
  L.subst(Nat, o => {Nat.mul(x, S.scale_binary(k, o)) == S.scale_binary(k, x) : Nat}, 1n, one, Equal.sym(Nat, one, 1n, h1), mul_sc(k, x))

def sc_mul(+k: Nat, +q: Nat, +d: Nat) -> {sc(k, Nat.mul(q, d)) == Nat.mul(sc(k, q), d) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      Equal.trans(Nat, Nat.double(sc(j, Nat.mul(q, d))), Nat.double(Nat.mul(sc(j, q), d)), Nat.mul(Nat.double(sc(j, q)), d), Equal.cong(Nat, Nat, Nat.double, sc(j, Nat.mul(q, d)), Nat.mul(sc(j, q), d), sc_mul(j, q, d)), Equal.sym(Nat, Nat.mul(Nat.double(sc(j, q)), d), Nat.double(Nat.mul(sc(j, q), d)), PR.double_product(sc(j, q), d)))

def sc_le(+k: Nat, +a: Nat, +b: Nat, +h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(sc(k, a), sc(k, b)) == True{} : Bool}:
  match k:
    case 0n:
      h
    case 1n+j:
      N.double_le(sc(j, a), sc(j, b), sc_le(j, a, b, h))

def sc_lt(+k: Nat, +a: Nat, +b: Nat, +h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_lt(sc(k, a), sc(k, b)) == True{} : Bool}:
  match k:
    case 0n:
      h
    case 1n+j:
      N.double_lt(sc(j, a), sc(j, b), sc_lt(j, a, b, h))

def sc_lt_cancel_g(+k: Nat, +a: Nat, +b: Nat, +c: Bool, +hc: {Nat.is_lt(a, b) == c : Bool}, +h: {Nat.is_lt(sc(k, a), sc(k, b)) == True{} : Bool}) -> {Nat.is_lt(a, b) == True{} : Bool}:
  match c:
    case True{}:
      hc
    case False{}:
      Empty.absurd({Nat.is_lt(a, b) == True{} : Bool}, L.true_false(Equal.trans(Bool, True{}, Nat.is_le(sc(k, b), sc(k, a)), False{}, Equal.sym(Bool, Nat.is_le(sc(k, b), sc(k, a)), True{}, sc_le(k, b, a, N.not_lt_le(a, b, hc))), N.lt_not_le(sc(k, a), sc(k, b), h))))

def sc_lt_cancel(+k: Nat, +a: Nat, +b: Nat, +h: {Nat.is_lt(sc(k, a), sc(k, b)) == True{} : Bool}) -> {Nat.is_lt(a, b) == True{} : Bool}:
  sc_lt_cancel_g(k, a, b, Nat.is_lt(a, b), {==}, h)

def le_sc(+k: Nat, +x: Nat) -> {Nat.is_le(x, sc(k, x)) == True{} : Bool}:
  match k:
    case 0n:
      N.le_refl(x)
    case 1n+j:
      N.le_trans(x, sc(j, x), Nat.double(sc(j, x)), le_sc(j, x), N.double_self_le(sc(j, x)))

# a digit x below 2^k after y < b scaled by 2^k stays below b scaled
def digit_lt(+k: Nat, +one: Nat, +h1: {one == 1n : Nat}, +x: Nat, +y: Nat, +b: Nat, +hx: {Nat.is_lt(x, sc(k, one)) == True{} : Bool}, +hy: {Nat.is_lt(y, b) == True{} : Bool}) -> {Nat.is_lt(Nat.add(sc(k, y), x), sc(k, b)) == True{} : Bool}:
  +hx1 = L.subst(Nat, o => {Nat.is_lt(x, S.scale_binary(k, o)) == True{} : Bool}, one, 1n, h1, hx)
  +l1 = N.lt_add_left(x, sc(k, 1n), sc(k, y), hx1)
  +e1 = Equal.trans(Nat, Nat.add(sc(k, y), sc(k, 1n)), sc(k, Nat.add(y, 1n)), sc(k, 1n+y), A.sc_add(k, y, 1n), Equal.cong(Nat, Nat, z => sc(k, z), Nat.add(y, 1n), 1n+y, N.add_comm(y, 1n)))
  +l2 = L.subst(Nat, z => {Nat.is_lt(Nat.add(sc(k, y), x), z) == True{} : Bool}, Nat.add(sc(k, y), sc(k, 1n)), sc(k, 1n+y), e1, l1)
  N.lt_le_trans(Nat.add(sc(k, y), x), sc(k, 1n+y), sc(k, b), l2, sc_le(k, 1n+y, b, N.lt_succ_le_succ(y, b, hy)))

def mul_le(+a: Nat, +b: Nat, +c: Nat, +h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(Nat.mul(a, c), Nat.mul(b, c)) == True{} : Bool}:
  +e = Nat.sub(b, a)
  +hb = N.sub_add(b, a, h)
  +m = Equal.trans(Nat, Nat.add(Nat.mul(a, c), Nat.mul(e, c)), Nat.mul(Nat.add(a, e), c), Nat.mul(b, c), Equal.sym(Nat, Nat.mul(Nat.add(a, e), c), Nat.add(Nat.mul(a, c), Nat.mul(e, c)), NA.mul_add_right(a, e, c)), Equal.cong(Nat, Nat, z => Nat.mul(z, c), Nat.add(a, e), b, hb))
  L.subst(Nat, z => {Nat.is_le(Nat.mul(a, c), z) == True{} : Bool}, Nat.add(Nat.mul(a, c), Nat.mul(e, c)), Nat.mul(b, c), m, N.le_add_right(Nat.mul(a, c), Nat.mul(e, c)))

def one_mul(+d: Nat) -> {Nat.mul(1n, d) == d : Nat}:
  N.add_zero(d)

def quot_lt_g(+k: Nat, +q: Nat, +d: Nat, +r: Nat, +c: Bool, +hc: {Nat.is_lt(q, sc(k, 1n)) == c : Bool}, +h: {Nat.is_lt(Nat.add(Nat.mul(q, d), r), sc(k, d)) == True{} : Bool}) -> {Nat.is_lt(q, sc(k, 1n)) == True{} : Bool}:
  match c:
    case True{}:
      hc
    case False{}:
      +l1 = mul_le(sc(k, 1n), q, d, N.not_lt_le(q, sc(k, 1n), hc))
      +e1 = Equal.trans(Nat, Nat.mul(sc(k, 1n), d), sc(k, Nat.mul(1n, d)), sc(k, d), Equal.sym(Nat, sc(k, Nat.mul(1n, d)), Nat.mul(sc(k, 1n), d), sc_mul(k, 1n, d)), Equal.cong(Nat, Nat, z => sc(k, z), Nat.mul(1n, d), d, one_mul(d)))
      +l2 = L.subst(Nat, z => {Nat.is_le(z, Nat.mul(q, d)) == True{} : Bool}, Nat.mul(sc(k, 1n), d), sc(k, d), e1, l1)
      +l3 = N.le_trans(sc(k, d), Nat.mul(q, d), Nat.add(Nat.mul(q, d), r), l2, N.le_add_right(Nat.mul(q, d), r))
      Empty.absurd({Nat.is_lt(q, sc(k, 1n)) == True{} : Bool}, L.true_false(Equal.trans(Bool, True{}, Nat.is_le(sc(k, d), Nat.add(Nat.mul(q, d), r)), False{}, Equal.sym(Bool, Nat.is_le(sc(k, d), Nat.add(Nat.mul(q, d), r)), True{}, l3), N.lt_not_le(Nat.add(Nat.mul(q, d), r), sc(k, d), h))))

# q d + r < 2^k d forces q < 2^k
def quot_lt(+k: Nat, +one: Nat, +h1: {one == 1n : Nat}, +q: Nat, +d: Nat, +r: Nat, +h: {Nat.is_lt(Nat.add(Nat.mul(q, d), r), sc(k, d)) == True{} : Bool}) -> {Nat.is_lt(q, sc(k, one)) == True{} : Bool}:
  L.subst(Nat, o => {Nat.is_lt(q, S.scale_binary(k, o)) == True{} : Bool}, 1n, one, Equal.sym(Nat, one, 1n, h1), quot_lt_g(k, q, d, r, Nat.is_lt(q, sc(k, 1n)), {==}, h))

# one long-division step: if x == q d + r and 2^k r + y == q2 d + r2 then
# 2^k x + y == (2^k q + q2) d + r2
def step(+k: Nat, +q: Nat, +r: Nat, +d: Nat, +y: Nat, +q2: Nat, +r2: Nat, +x: Nat, +hx: {x == Nat.add(Nat.mul(q, d), r) : Nat}, +h2: {Nat.add(sc(k, r), y) == Nat.add(Nat.mul(q2, d), r2) : Nat}) -> {Nat.add(sc(k, x), y) == Nat.add(Nat.mul(Nat.add(sc(k, q), q2), d), r2) : Nat}:
  +rhs = Nat.add(Nat.mul(Nat.add(sc(k, q), q2), d), r2)
  %Equal.sym(Nat, x, Nat.add(Nat.mul(q, d), r), hx) : {Nat.add(sc(k, _), y) == rhs : Nat}
  %A.sc_add(k, Nat.mul(q, d), r) : {Nat.add(_, y) == rhs : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(sc(k, Nat.mul(q, d)), sc(k, r)), y), Nat.add(sc(k, Nat.mul(q, d)), Nat.add(sc(k, r), y)), N.add_assoc(sc(k, Nat.mul(q, d)), sc(k, r), y)) : {_ == rhs : Nat}
  %Equal.sym(Nat, Nat.add(sc(k, r), y), Nat.add(Nat.mul(q2, d), r2), h2) : {Nat.add(sc(k, Nat.mul(q, d)), _) == rhs : Nat}
  %Equal.sym(Nat, sc(k, Nat.mul(q, d)), Nat.mul(sc(k, q), d), sc_mul(k, q, d)) : {Nat.add(_, Nat.add(Nat.mul(q2, d), r2)) == rhs : Nat}
  %Equal.sym(Nat, Nat.mul(Nat.add(sc(k, q), q2), d), Nat.add(Nat.mul(sc(k, q), d), Nat.mul(q2, d)), NA.mul_add_right(sc(k, q), q2, d)) : {Nat.add(Nat.mul(sc(k, q), d), Nat.add(Nat.mul(q2, d), r2)) == Nat.add(_, r2) : Nat}
  Equal.sym(Nat, Nat.add(Nat.add(Nat.mul(sc(k, q), d), Nat.mul(q2, d)), r2), Nat.add(Nat.mul(sc(k, q), d), Nat.add(Nat.mul(q2, d), r2)), N.add_assoc(Nat.mul(sc(k, q), d), Nat.mul(q2, d), r2))

def go_le(+n: Nat, +m: Nat, +d: Nat, +r: Nat) -> {Nat.is_le(Nat.div.fin(Nat.divmod.go(n, m, d, r)), Nat.add(d, n)) == True{} : Bool}:
  match n:
    case 0n:
      %Equal.sym(Nat, Nat.add(d, 0n), d, N.add_zero(d)) : {Nat.is_le(d, _) == True{} : Bool}
      N.le_refl(d)
    case 1n+np:
      match m:
        case 0n:
          %Equal.sym(Nat, Nat.add(d, 1n+np), 1n+Nat.add(d, np), N.add_succ(d, np)) : {Nat.is_le(Nat.div.fin(Nat.divmod.go(np, r, 1n+d, 0n)), _) == True{} : Bool}
          go_le(np, r, 1n+d, 0n)
        case 1n+mp:
          N.le_trans(Nat.div.fin(Nat.divmod.go(np, mp, d, 1n+r)), Nat.add(d, np), Nat.add(d, 1n+np), go_le(np, mp, d, 1n+r), L.subst(Nat, z => {Nat.is_le(Nat.add(d, np), z) == True{} : Bool}, 1n+Nat.add(d, np), Nat.add(d, 1n+np), Equal.sym(Nat, Nat.add(d, 1n+np), 1n+Nat.add(d, np), N.add_succ(d, np)), N.le_succ(Nat.add(d, np))))

# a quotient never exceeds its dividend
def div_le(+a: Nat, +d: Nat) -> {Nat.is_le(Nat.div(a, d), a) == True{} : Bool}:
  match d:
    case 0n:
      N.zero_le(a)
    case 1n+bp:
      go_le(a, bp, 0n, 0n)

def zsub(+b: Nat) -> {Nat.sub(0n, b) == 0n : Nat}:
  match b:
    case 0n:
      {==}
    case 1n+q:
      {==}

def sub_cancel_l(+c: Nat, +a: Nat, +b: Nat) -> {Nat.sub(Nat.add(c, a), Nat.add(c, b)) == Nat.sub(a, b) : Nat}:
  match c:
    case 0n:
      {==}
    case 1n+p:
      sub_cancel_l(p, a, b)

# 2^(k + j) x == 2^k (2^j x)
def sc_idx(+k: Nat, +j: Nat, +x: Nat) -> {sc(Nat.add(k, j), x) == sc(k, sc(j, x)) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, Nat.double, sc(Nat.add(p, j), x), sc(p, sc(j, x)), sc_idx(p, j, x))

# 2^k (a - b) == 2^k a - 2^k b
def sc_sub(+k: Nat, +a: Nat, +b: Nat) -> {sc(k, Nat.sub(a, b)) == Nat.sub(sc(k, a), sc(k, b)) : Nat}:
  match a b:
    case 0n _:
      %Equal.sym(Nat, Nat.sub(0n, b), 0n, zsub(b)) : {sc(k, _) == Nat.sub(sc(k, 0n), sc(k, b)) : Nat}
      %Equal.sym(Nat, sc(k, 0n), 0n, A.sc_zero(k)) : {_ == Nat.sub(sc(k, 0n), sc(k, b)) : Nat}
      %Equal.sym(Nat, sc(k, 0n), 0n, A.sc_zero(k)) : {0n == Nat.sub(_, sc(k, b)) : Nat}
      Equal.sym(Nat, Nat.sub(0n, sc(k, b)), 0n, zsub(sc(k, b)))
    case 1n+p 0n:
      %Equal.sym(Nat, sc(k, 0n), 0n, A.sc_zero(k)) : {sc(k, 1n+p) == Nat.sub(sc(k, 1n+p), _) : Nat}
      Equal.sym(Nat, Nat.sub(sc(k, 1n+p), 0n), sc(k, 1n+p), N.sub_zero(sc(k, 1n+p)))
    case 1n+p 1n+q:
      %Equal.sym(Nat, sc(k, 1n+p), Nat.add(sc(k, 1n), sc(k, p)), A.sc_succ(k, p)) : {sc(k, Nat.sub(p, q)) == Nat.sub(_, sc(k, 1n+q)) : Nat}
      %Equal.sym(Nat, sc(k, 1n+q), Nat.add(sc(k, 1n), sc(k, q)), A.sc_succ(k, q)) : {sc(k, Nat.sub(p, q)) == Nat.sub(Nat.add(sc(k, 1n), sc(k, p)), _) : Nat}
      %Equal.sym(Nat, Nat.sub(Nat.add(sc(k, 1n), sc(k, p)), Nat.add(sc(k, 1n), sc(k, q))), Nat.sub(sc(k, p), sc(k, q)), sub_cancel_l(sc(k, 1n), sc(k, p), sc(k, q))) : {sc(k, Nat.sub(p, q)) == _ : Nat}
      sc_sub(k, p, q)

# a - b <= a
def sub_le2(+a: Nat, +b: Nat) -> {Nat.is_le(Nat.sub(a, b), a) == True{} : Bool}:
  match a b:
    case 0n _:
      %Equal.sym(Nat, Nat.sub(0n, b), 0n, zsub(b)) : {Nat.is_le(_, 0n) == True{} : Bool}
      {==}
    case 1n+p 0n:
      N.le_refl(1n+p)
    case 1n+p 1n+q:
      N.le_trans(Nat.sub(p, q), p, 1n+p, sub_le2(p, q), N.le_succ(p))
