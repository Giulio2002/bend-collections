import Base
import ./map_routing.bend as Logic
import ./map_index.bend as Index

law add_zero:
  for n: Nat
  {Nat.add(n, 0n) == n : Nat}
def add_zero(n):
  match n:
    case 0n: {==}
    case 1n+p: Equal.cong(Nat, Nat, x => 1n+x, Nat.add(p, 0n), p, add_zero(p))

law add_commute:
  for a: Nat
  for +b: Nat
  {Nat.add(a, b) == Nat.add(b, a) : Nat}
def add_commute(a, b):
  match a:
    case 0n: Equal.sym(Nat, Nat.add(b, 0n), b, add_zero(b))
    case 1n+ +p:
      Equal.trans(Nat, 1n+Nat.add(p, b), 1n+Nat.add(b, p), Nat.add(b, 1n+p), Equal.cong(Nat, Nat, x => 1n+x, Nat.add(p, b), Nat.add(b, p), add_commute(p, b)), Equal.sym(Nat, Nat.add(b, 1n+p), 1n+Nat.add(b, p), Index.add_right_successor(b, p)))

law add_sub_bound:
  for n: Nat
  for m: Nat
  for +k: Nat
  for bound: {Nat.is_le(m, n) == True{} : Bool}
  for inside: {Nat.is_le(k, Nat.sub(n, m)) == True{} : Bool}
  {Nat.is_le(Nat.add(m, k), n) == True{} : Bool}
def add_sub_bound(n, m, k, bound, inside):
  match n m:
    case 0n 0n: inside
    case 0n 1n+p:
      Empty.absurd({Nat.is_le(Nat.add(1n+p, k), 0n) == True{} : Bool}, Logic.false_true(bound))
    case 1n+p 0n: inside
    case 1n+p 1n+q: add_sub_bound(p, q, k, bound, inside)

law sub_from_add:
  for n: Nat
  for k: Nat
  for +m: Nat
  for bound: {Nat.is_le(Nat.add(k, m), n) == True{} : Bool}
  {Nat.is_le(m, Nat.sub(n, k)) == True{} : Bool}
def sub_from_add(n, k, m, bound):
  match n k:
    case 0n 0n: bound
    case 0n 1n+p:
      Empty.absurd({Nat.is_le(m, 0n) == True{} : Bool}, Logic.false_true(bound))
    case 1n+p 0n: bound
    case 1n+p 1n+q: sub_from_add(p, q, m, bound)

law add_complement:
  for n: Nat
  for m: Nat
  for bound: {Nat.is_le(m, n) == True{} : Bool}
  {Nat.add(m, Nat.sub(n, m)) == n : Nat}
def add_complement(n, m, bound):
  match n m:
    case 0n 0n: {==}
    case 0n 1n+p:
      Empty.absurd({Nat.add(1n+p, 0n) == 0n : Nat}, Logic.false_true(bound))
    case 1n+p 0n: {==}
    case 1n+ +p 1n+ +q:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.add(q, Nat.sub(p, q)), p, add_complement(p, q, bound))

law strict_successor:
  for a: Nat
  for b: Nat
  for strict: {Nat.is_lt(a, b) == True{} : Bool}
  {Nat.is_le(1n+a, b) == True{} : Bool}
def strict_successor(a, b, strict):
  match a b:
    case 0n 0n: Empty.absurd({False{} == True{} : Bool}, Logic.false_true(strict))
    case 0n 1n+p:
      match p:
        case 0n: {==}
        case 1n+q: {==}
    case 1n+p 0n: Empty.absurd({False{} == True{} : Bool}, Logic.false_true(strict))
    case 1n+p 1n+q: strict_successor(p, q, strict)

law less_is_le:
  for a: Nat
  for b: Nat
  for e: {Nat.is_lt(a, b) == True{} : Bool}
  {Nat.is_le(a, b) == True{} : Bool}
def less_is_le(a, b, e):
  match a b:
    case 0n 0n: {==}
    case 0n 1n+p: {==}
    case 1n+p 0n: e
    case 1n+p 1n+q: less_is_le(p, q, e)

def Split(+limit: Nat, +offset: Nat) -> Type:
  Either<&1, &1, {Nat.is_le(offset, limit) == True{} : Bool}, Sigma<&2, &1, Nat, rest => {offset == Nat.add(1n+limit, rest) : Nat}>>

law lift_split:
  for +limit: Nat
  for +offset: Nat
  for split: Split(limit, offset)
  Split(1n+limit, 1n+offset)
def lift_split(limit, offset, split):
  match split:
    case Inl{e}: Inl{e}
    case Inr{Tuple{+rest, e}}:
      Inr{(rest, Equal.cong(Nat, Nat, x => 1n+x, offset, Nat.add(1n+limit, rest), e))}

law split_offset:
  for limit: Nat
  for offset: Nat
  Split(limit, offset)
def split_offset(limit, offset):
  match limit offset:
    case 0n 0n: Inl{{==}}
    case 0n 1n+ +p: Inr{(p, {==})}
    case 1n+p 0n: Inl{{==}}
    case 1n+ +p 1n+ +q:
      lift_split(p, q, split_offset(p, q))
