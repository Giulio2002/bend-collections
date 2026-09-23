import Base
import ./invariants.bend as Inv
import ./native_map.bend as N
import ./map_insert.bend as I
import ./map_difference.bend as D
import ./map_difference_char.bend as C
import ./map_character_prefix.bend as P
import ./map_difference_order.bend as O
import ./map_msb.bend as M
import ./map_routing.bend as Logic
import ./recency_bounds.bend as Bounds

def Agree(+a: String, +b: String, +offset: Nat) -> Type:
  {Bool.xor(I.route_bit(Map.bit(a, offset)), I.route_bit(Map.bit(b, offset))) == False{} : Bool}

law xor_self:
  for b: Bool
  {Bool.xor(b, b) == False{} : Bool}
def xor_self(b):
  match b:
    case False{}: {==}
    case True{}: {==}

law common_character:
  for +head: Char
  for +a: String
  for +b: String
  for +offset: Nat
  for +bound: {Nat.is_le(offset, 32n) == True{} : Bool}
  Agree(SCon{head, a}, SCon{head, b}, offset)
def common_character(head, a, b, offset, bound):
  %Equal.sym(Bool, I.route_bit(Map.bit(SCon{head, a}, offset)), C.bit(Map.bit.chr(head, offset)), D.first_route(head, a, offset, bound)) : {Bool.xor(_, I.route_bit(Map.bit(SCon{head, b}, offset))) == False{} : Bool}
  %Equal.sym(Bool, I.route_bit(Map.bit(SCon{head, b}, offset)), C.bit(Map.bit.chr(head, offset)), D.first_route(head, b, offset, bound)) : {Bool.xor(C.bit(Map.bit.chr(head, offset)), _) == False{} : Bool}
  xor_self(C.bit(Map.bit.chr(head, offset)))

law common_tail:
  for +head: Char
  for +a: String
  for +b: String
  for +offset: Nat
  for agree: Agree(a, b, offset)
  Agree(SCon{head, a}, SCon{head, b}, Nat.add(33n, offset))
def common_tail(head, a, b, offset, agree):
  %Equal.sym(Bool, I.route_bit(Map.bit(SCon{head, a}, Nat.add(33n, offset))), I.route_bit(Map.bit(a, offset)), D.common_head_route(head, a, offset)) : {Bool.xor(_, I.route_bit(Map.bit(SCon{head, b}, Nat.add(33n, offset)))) == False{} : Bool}
  %Equal.sym(Bool, I.route_bit(Map.bit(SCon{head, b}, Nat.add(33n, offset))), I.route_bit(Map.bit(b, offset)), D.common_head_route(head, b, offset)) : {Bool.xor(I.route_bit(Map.bit(a, offset)), _) == False{} : Bool}
  agree

law common_split:
  for +head: Char
  for +a: String
  for +b: String
  for +offset: Nat
  for split: O.Split(32n, offset)
  for earlier: {Nat.is_lt(offset, Nat.add(33n, Map.diff(a, b))) == True{} : Bool}
  for recur: @i: Nat -> {Nat.is_lt(i, Map.diff(a, b)) == True{} : Bool} -> Agree(a, b, i)
  Agree(SCon{head, a}, SCon{head, b}, offset)
def common_split(head, a, b, offset, split, earlier, recur):
  match split:
    case Inl{bound}: common_character(head, a, b, offset, bound)
    case Inr{Tuple{+rest, +eq}}:
      %Equal.sym(Nat, offset, Nat.add(33n, rest), eq) : Agree(SCon{head, a}, SCon{head, b}, _)
      common_tail(head, a, b, rest, recur(rest, %eq : {Nat.is_lt(_, Nat.add(33n, Map.diff(a, b))) == True{} : Bool} earlier))

law common_head:
  for +head: Char
  for +a: String
  for +b: String
  for +offset: Nat
  for earlier: {Nat.is_lt(offset, Map.diff(SCon{head, a}, SCon{head, b})) == True{} : Bool}
  for recur: @i: Nat -> {Nat.is_lt(i, Map.diff(a, b)) == True{} : Bool} -> Agree(a, b, i)
  Agree(SCon{head, a}, SCon{head, b}, offset)
def common_head(head, a, b, offset, earlier, recur):
  common_split(head, a, b, offset, O.split_offset(32n, offset), %N.difference_common_character(head, a, b) : {Nat.is_lt(offset, _) == True{} : Bool} earlier, recur)

law different_head:
  for +x: U32
  for +y: U32
  for +a: String
  for +b: String
  for +offset: Nat
  for +unequal: {U32.is_eq(x, y) == False{} : Bool}
  for earlier: {Nat.is_lt(offset, Map.diff(SCon{Chr{x}, a}, SCon{Chr{y}, b})) == True{} : Bool}
  Agree(SCon{Chr{x}, a}, SCon{Chr{y}, b}, offset)
def different_head(x, y, a, b, offset, unequal, earlier):
  +small = {%unequal : {Nat.is_lt(offset, Map.diff.fin(a, b, (Map.diff.chr(U32.xor(x, y)), _))) == True{} : Bool} earlier : {Nat.is_lt(offset, Map.diff.chr(U32.xor(x, y))) == True{} : Bool}}
  +bound = Bounds.le_transitive(offset, Map.diff.chr(U32.xor(x, y)), 32n, O.less_is_le(offset, Map.diff.chr(U32.xor(x, y)), small), C.difference_bound(x, y, M.unequal_character_difference(x, y, unequal)))
  %Equal.sym(Bool, I.route_bit(Map.bit(SCon{Chr{x}, a}, offset)), C.bit(Map.bit.chr(Chr{x}, offset)), D.first_route(Chr{x}, a, offset, bound)) : {Bool.xor(_, I.route_bit(Map.bit(SCon{Chr{y}, b}, offset))) == False{} : Bool}
  %Equal.sym(Bool, I.route_bit(Map.bit(SCon{Chr{y}, b}, offset)), C.bit(Map.bit.chr(Chr{y}, offset)), D.first_route(Chr{y}, b, offset, bound)) : {Bool.xor(C.bit(Map.bit.chr(Chr{x}, offset)), _) == False{} : Bool}
  P.native_character_prefix(x, y, offset, small)

law equal_head:
  for +x: U32
  for +y: U32
  for +a: String
  for +b: String
  for +offset: Nat
  for +eq: {x == y : U32}
  for earlier: {Nat.is_lt(offset, Map.diff(SCon{Chr{x}, a}, SCon{Chr{y}, b})) == True{} : Bool}
  for recur: @i: Nat -> {Nat.is_lt(i, Map.diff(a, b)) == True{} : Bool} -> Agree(a, b, i)
  Agree(SCon{Chr{x}, a}, SCon{Chr{y}, b}, offset)
def equal_head(x, y, a, b, offset, eq, earlier, recur):
  %eq : Agree(SCon{Chr{x}, a}, SCon{Chr{_}, b}, offset)
  common_head(Chr{x}, a, b, offset, %Equal.sym(U32, x, y, eq) : {Nat.is_lt(offset, Map.diff(SCon{Chr{x}, a}, SCon{Chr{_}, b})) == True{} : Bool} earlier, recur)

law head_case:
  for +x: U32
  for +y: U32
  for +a: String
  for +b: String
  for +offset: Nat
  for same: Bool
  for eq: {U32.is_eq(x, y) == same : Bool}
  for earlier: {Nat.is_lt(offset, Map.diff(SCon{Chr{x}, a}, SCon{Chr{y}, b})) == True{} : Bool}
  for recur: @i: Nat -> {Nat.is_lt(i, Map.diff(a, b)) == True{} : Bool} -> Agree(a, b, i)
  Agree(SCon{Chr{x}, a}, SCon{Chr{y}, b}, offset)
def head_case(x, y, a, b, offset, same, eq, earlier, recur):
  match same:
    case False{}: different_head(x, y, a, b, offset, eq, earlier)
    case True{}: equal_head(x, y, a, b, offset, D.u32_equal(x, y, eq), earlier, recur)

law not_before_zero:
  for offset: Nat
  for earlier: {Nat.is_lt(offset, 0n) == True{} : Bool}
  Empty
def not_before_zero(offset, earlier):
  match offset:
    case 0n: Logic.false_true(earlier)
    case 1n+p: Logic.false_true(earlier)

# Actual native Map.diff is a least discriminator: every earlier native routing
# bit agrees. Together with native_difference, this characterizes first difference.
law native_prefix:
  for a: String
  for b: String
  for +offset: Nat
  for earlier: {Nat.is_lt(offset, Map.diff(a, b)) == True{} : Bool}
  Agree(a, b, offset)
def native_prefix(a, b, offset, earlier):
  match a b:
    case SNil{} SNil{}:
      Empty.absurd(Agree(SNil{}, SNil{}, offset), not_before_zero(offset, earlier))
    case SNil{} SCon{Chr{+x}, +tail}:
      Empty.absurd(Agree(SNil{}, SCon{Chr{x}, tail}, offset), not_before_zero(offset, earlier))
    case SCon{Chr{+x}, +tail} SNil{}:
      Empty.absurd(Agree(SCon{Chr{x}, tail}, SNil{}, offset), not_before_zero(offset, earlier))
    case SCon{Chr{+x}, +left_tail} SCon{Chr{+y}, +right_tail}:
      head_case(x, y, left_tail, right_tail, offset, U32.is_eq(x, y), {==}, earlier, i => e => native_prefix(left_tail, right_tail, i, e))


law predecessor_less:
  for p: Nat
  for n: Nat
  for bound: {Nat.is_le(1n+p, n) == True{} : Bool}
  {Nat.is_lt(p, n) == True{} : Bool}
def predecessor_less(p, n, bound):
  match p n:
    case 0n 0n: bound
    case 0n 1n+q: {==}
    case 1n+p 0n: bound
    case 1n+p 1n+q: predecessor_less(p, q, bound)

law invariant_bit:
  for pair: String & Bool
  {Inv.bit_value(pair) == I.route_bit(pair) : Bool}
def invariant_bit(pair):
  match pair:
    case Tuple{key, bit}: {==}

law invariant_agreement:
  for +a: String
  for +b: String
  for +offset: Nat
  for earlier: {Nat.is_lt(offset, Map.diff(a, b)) == True{} : Bool}
  {Bool.xor(Inv.bit_value(Map.bit(a, offset)), Inv.bit_value(Map.bit(b, offset))) == False{} : Bool}
def invariant_agreement(a, b, offset, earlier):
  %Equal.sym(Bool, Inv.bit_value(Map.bit(a, offset)), I.route_bit(Map.bit(a, offset)), invariant_bit(Map.bit(a, offset))) : {Bool.xor(_, Inv.bit_value(Map.bit(b, offset))) == False{} : Bool}
  %Equal.sym(Bool, Inv.bit_value(Map.bit(b, offset)), I.route_bit(Map.bit(b, offset)), invariant_bit(Map.bit(b, offset))) : {Bool.xor(I.route_bit(Map.bit(a, offset)), _) == False{} : Bool}
  native_prefix(a, b, offset, earlier)

law prefix_invariant_bound:
  for +a: String
  for +b: String
  for limit: Nat
  for bound: {Nat.is_le(limit, Map.diff(a, b)) == True{} : Bool}
  {Inv.same_prefix(a, b, limit) == True{} : Bool}
def prefix_invariant_bound(a, b, limit, bound):
  match limit:
    case 0n: {==}
    case 1n+ +p:
      +earlier = predecessor_less(p, Map.diff(a, b), bound)
      %Equal.sym(Bool, Bool.xor(Inv.bit_value(Map.bit(a, p)), Inv.bit_value(Map.bit(b, p))), False{}, invariant_agreement(a, b, p, earlier)) : {Bool.not(_) && Inv.same_prefix(a, b, p) == True{} : Bool}
      prefix_invariant_bound(a, b, p, O.less_is_le(p, Map.diff(a, b), earlier))

law native_prefix_invariant:
  for +a: String
  for +b: String
  {Inv.same_prefix(a, b, Map.diff(a, b)) == True{} : Bool}
def native_prefix_invariant(a, b):
  prefix_invariant_bound(a, b, Map.diff(a, b), C.le_self(Map.diff(a, b)))
