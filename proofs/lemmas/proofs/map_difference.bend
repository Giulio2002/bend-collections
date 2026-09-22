import Base
import ./native_map.bend as N
import ./map_insert.bend as I
import ./map_routing.bend as Logic
import ./map_msb.bend as M
import ./map_difference_char.bend as D
import ./map_index.bend as Index

law comparison_eq:
  for c: Cmp
  for e: {Cmp.is_eq(c) == True{} : Bool}
  {c == EQ{} : Cmp}
def comparison_eq(c, e):
  match c:
    case LT{}: Empty.absurd({LT{} == EQ{} : Cmp}, Logic.false_true(e))
    case EQ{}: {==}
    case GT{}: Empty.absurd({GT{} == EQ{} : Cmp}, Logic.false_true(e))

law u32_equal:
  for a: U32
  for b: U32
  for e: {U32.is_eq(a, b) == True{} : Bool}
  {a == b : U32}
def u32_equal(a, b, e):
  match a b:
    case U32{+x} U32{+y}:
      Equal.cong(Word(32n), U32, w => U32{w}, x, y, %comparison_eq(Word.cmp(32n, x, y), e) : N.comparison_identity(Word(32n), x, y, _) N.word_comparison_identity(32n, x, y))

law recursive_bit:
  for h: Char
  for pair: String & Bool
  {I.route_bit(Map.bit.go.rec(h, pair)) == I.route_bit(pair) : Bool}
def recursive_bit(h, pair):
  match pair:
    case Tuple{tail, bit}: {==}

law character_bit:
  for tail: String
  for pair: Char & Bool
  {I.route_bit(Map.bit.go.chr(tail, pair)) == D.bit(pair) : Bool}
def character_bit(tail, pair):
  match pair:
    case Tuple{head, bit}: {==}

law common_head_route:
  for +head: Char
  for +tail: String
  for +position: Nat
  {I.route_bit(Map.bit(SCon{head, tail}, Nat.add(33n, position))) == I.route_bit(Map.bit(tail, position)) : Bool}
def common_head_route(head, tail, position):
  Equal.trans(Bool, I.route_bit(Map.bit(SCon{head, tail}, Nat.add(33n, position))), I.route_bit(Map.bit.go.rec(head, Map.bit(tail, position))), I.route_bit(Map.bit(tail, position)), Equal.cong(String & Bool, Bool, I.route_bit, Map.bit(SCon{head, tail}, Nat.add(33n, position)), Map.bit.go.rec(head, Map.bit(tail, position)), Index.native_character_stride(head, tail, position)), recursive_bit(head, Map.bit(tail, position)))

law first_route:
  for +head: Char
  for +tail: String
  for +position: Nat
  for bound: {Nat.is_le(position, 32n) == True{} : Bool}
  {I.route_bit(Map.bit(SCon{head, tail}, position)) == D.bit(Map.bit.chr(head, position)) : Bool}
def first_route(head, tail, position, bound):
  Equal.trans(Bool, I.route_bit(Map.bit(SCon{head, tail}, position)), I.route_bit(Map.bit.go.chr(tail, Map.bit.chr(head, position))), D.bit(Map.bit.chr(head, position)), Equal.cong(String & Bool, Bool, I.route_bit, Map.bit(SCon{head, tail}, position), Map.bit.go.chr(tail, Map.bit.chr(head, position)), Index.native_first_character(head, tail, position, bound)), character_bit(tail, Map.bit.chr(head, position)))

def distinguishes(+a: String, +b: String) -> Bool:
  Bool.xor(I.route_bit(Map.bit(a, Map.diff(a, b))), I.route_bit(Map.bit(b, Map.diff(a, b))))

def different(a: String, b: String) -> Type:
  {a == b : String} -> Empty

law same_head:
  for +head: Char
  for +a: String
  for +b: String
  for tail: {distinguishes(a, b) == True{} : Bool}
  {distinguishes(SCon{head, a}, SCon{head, b}) == True{} : Bool}
def same_head(head, a, b, tail):
  %Equal.sym(Nat, Map.diff(SCon{head, a}, SCon{head, b}), Nat.add(33n, Map.diff(a, b)), N.difference_common_character(head, a, b)) : {Bool.xor(I.route_bit(Map.bit(SCon{head, a}, _)), I.route_bit(Map.bit(SCon{head, b}, _))) == True{} : Bool}
  %Equal.sym(Bool, I.route_bit(Map.bit(SCon{head, a}, Nat.add(33n, Map.diff(a, b)))), I.route_bit(Map.bit(a, Map.diff(a, b))), common_head_route(head, a, Map.diff(a, b))) : {Bool.xor(_, I.route_bit(Map.bit(SCon{head, b}, Nat.add(33n, Map.diff(a, b))))) == True{} : Bool}
  %Equal.sym(Bool, I.route_bit(Map.bit(SCon{head, b}, Nat.add(33n, Map.diff(a, b)))), I.route_bit(Map.bit(b, Map.diff(a, b))), common_head_route(head, b, Map.diff(a, b))) : {Bool.xor(I.route_bit(Map.bit(a, Map.diff(a, b))), _) == True{} : Bool}
  tail

law distinct_head:
  for +x: U32
  for +y: U32
  for +a: String
  for +b: String
  for +unequal: {U32.is_eq(x, y) == False{} : Bool}
  {distinguishes(SCon{Chr{x}, a}, SCon{Chr{y}, b}) == True{} : Bool}
def distinct_head(x, y, a, b, unequal):
  +bound = D.difference_bound(x, y, M.unequal_character_difference(x, y, unequal))
  %Equal.sym(Bool, U32.is_eq(x, y), False{}, unequal) : {Bool.xor(I.route_bit(Map.bit(SCon{Chr{x}, a}, Map.diff.fin(a, b, (Map.diff.chr(U32.xor(x, y)), _)))), I.route_bit(Map.bit(SCon{Chr{y}, b}, Map.diff.fin(a, b, (Map.diff.chr(U32.xor(x, y)), _))))) == True{} : Bool}
  %Equal.sym(Bool, I.route_bit(Map.bit(SCon{Chr{x}, a}, Map.diff.chr(U32.xor(x, y)))), D.bit(Map.bit.chr(Chr{x}, Map.diff.chr(U32.xor(x, y)))), first_route(Chr{x}, a, Map.diff.chr(U32.xor(x, y)), bound)) : {Bool.xor(_, I.route_bit(Map.bit(SCon{Chr{y}, b}, Map.diff.chr(U32.xor(x, y))))) == True{} : Bool}
  %Equal.sym(Bool, I.route_bit(Map.bit(SCon{Chr{y}, b}, Map.diff.chr(U32.xor(x, y)))), D.bit(Map.bit.chr(Chr{y}, Map.diff.chr(U32.xor(x, y)))), first_route(Chr{y}, b, Map.diff.chr(U32.xor(x, y)), bound)) : {Bool.xor(D.bit(Map.bit.chr(Chr{x}, Map.diff.chr(U32.xor(x, y)))), _) == True{} : Bool}
  D.native_character_difference(x, y, unequal)

law equal_head_branch:
  for +x: U32
  for +y: U32
  for +a: String
  for +b: String
  for +eq: {x == y : U32}
  for distinct: different(SCon{Chr{x}, a}, SCon{Chr{y}, b})
  for recur: different(a, b) -> {distinguishes(a, b) == True{} : Bool}
  {distinguishes(SCon{Chr{x}, a}, SCon{Chr{y}, b}) == True{} : Bool}
def equal_head_branch(x, y, a, b, eq, distinct, recur):
  %eq : {distinguishes(SCon{Chr{x}, a}, SCon{Chr{_}, b}) == True{} : Bool}
  same_head(Chr{x}, a, b, recur(e => distinct(Equal.trans(String, SCon{Chr{x}, a}, SCon{Chr{x}, b}, SCon{Chr{y}, b}, Equal.cong(String, String, t => SCon{Chr{x}, t}, a, b, e), Equal.cong(U32, String, h => SCon{Chr{h}, b}, x, y, eq)))))

law head_branch:
  for +x: U32
  for +y: U32
  for +a: String
  for +b: String
  for same: Bool
  for eq: {U32.is_eq(x, y) == same : Bool}
  for distinct: different(SCon{Chr{x}, a}, SCon{Chr{y}, b})
  for recur: different(a, b) -> {distinguishes(a, b) == True{} : Bool}
  {distinguishes(SCon{Chr{x}, a}, SCon{Chr{y}, b}) == True{} : Bool}
def head_branch(x, y, a, b, same, eq, distinct, recur):
  match same:
    case False{}: distinct_head(x, y, a, b, eq)
    case True{}: equal_head_branch(x, y, a, b, u32_equal(x, y, eq), distinct, recur)

# Actual native Map.diff selects a differing bit for every pair of distinct
# Base Strings, including arbitrary U32 characters, empty strings and zeros.
# Least-discriminator prefix minimality is not asserted by this theorem.
law native_difference:
  for a: String
  for b: String
  for distinct: different(a, b)
  {distinguishes(a, b) == True{} : Bool}
def native_difference(a, b, distinct):
  match a b:
    case SNil{} SNil{}:
      Empty.absurd({False{} == True{} : Bool}, distinct({==}))
    case SNil{} SCon{Chr{x}, tail}: {==}
    case SCon{Chr{x}, tail} SNil{}: {==}
    case SCon{Chr{+x}, +left_tail} SCon{Chr{+y}, +right_tail}:
      head_branch(x, y, left_tail, right_tail, U32.is_eq(x, y), {==}, distinct, d => native_difference(left_tail, right_tail, d))

law native_difference_on_unequal_comparison:
  for +a: String
  for +b: String
  for unequal: {String.eq(a, b) == False{} : Bool}
  {distinguishes(a, b) == True{} : Bool}
def native_difference_on_unequal_comparison(a, b, unequal):
  native_difference(a, b, e => Logic.false_true(Equal.trans(Bool, False{}, String.eq(a, b), True{}, Equal.sym(Bool, String.eq(a, b), False{}, unequal), Equal.cong((String & String) & Cmp, Bool, String.eq.fin, String.cmp(a, b), ((a, b), EQ{}), N.string_equal_comparison(a, b, e)))))
