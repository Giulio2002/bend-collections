import Base
import ./map_insert.bend as I
import ./map_routing.bend as Logic

# Native insertion descent preserves the branch it does not visit. These laws
# quantify arbitrary trees, values and queries, including absent queries.
law opposite_descent:
  for -V: Data
  for +fallback: V
  for +value: V
  for +lo: Map<&2, V>
  for +hi: Map<&2, V>
  for +position: Nat
  for +discriminator: Nat
  for +key: String
  for +query: String
  for inserted: Bool
  for queried: Bool
  for different: {Bool.xor(inserted, queried) == True{} : Bool}
  for +route: {Map.bit(query, position) == (query, queried) : String & Bool}
  {I.lookup(V, fallback, Map.ins.deep(&2, V, value, lo, hi, discriminator, position, (key, inserted)), query) == I.lookup(V, fallback, MNode{position, lo, hi}, query) : V}
def opposite_descent(V, fallback, value, lo, hi, position, discriminator, key, query, inserted, queried, different, route):
  match inserted queried:
    case False{} False{}:
      Empty.absurd({I.lookup(V, fallback, Map.ins.deep(&2, V, value, lo, hi, discriminator, position, (key, False{})), query) == I.lookup(V, fallback, MNode{position, lo, hi}, query) : V}, Logic.false_true(different))
    case False{} True{}:
      Equal.trans(V, I.lookup(V, fallback, MNode{position, Map.ins(&2, V, lo, key, value, discriminator), hi}, query), I.lookup(V, fallback, hi, query), I.lookup(V, fallback, MNode{position, lo, hi}, query), I.node_right(V, fallback, Map.ins(&2, V, lo, key, value, discriminator), hi, position, query, route), Equal.sym(V, I.lookup(V, fallback, MNode{position, lo, hi}, query), I.lookup(V, fallback, hi, query), I.node_right(V, fallback, lo, hi, position, query, route)))
    case True{} False{}:
      Equal.trans(V, I.lookup(V, fallback, MNode{position, lo, Map.ins(&2, V, hi, key, value, discriminator)}, query), I.lookup(V, fallback, lo, query), I.lookup(V, fallback, MNode{position, lo, hi}, query), I.node_left(V, fallback, lo, Map.ins(&2, V, hi, key, value, discriminator), position, query, route), Equal.sym(V, I.lookup(V, fallback, MNode{position, lo, hi}, query), I.lookup(V, fallback, lo, query), I.node_left(V, fallback, lo, hi, position, query, route)))
    case True{} True{}:
      Empty.absurd({I.lookup(V, fallback, Map.ins.deep(&2, V, value, lo, hi, discriminator, position, (key, True{})), query) == I.lookup(V, fallback, MNode{position, lo, hi}, query) : V}, Logic.false_true(different))

law insertion_opposite_branch:
  for -V: Data
  for +fallback: V
  for +value: V
  for +lo: Map<&2, V>
  for +hi: Map<&2, V>
  for +position: Nat
  for +discriminator: Nat
  for +key: String
  for +query: String
  for below: {Nat.is_lt(position, discriminator) == True{} : Bool}
  for different: {Bool.xor(I.route_bit(Map.bit(key, position)), I.route_bit(Map.bit(query, position))) == True{} : Bool}
  {I.lookup(V, fallback, Map.ins(&2, V, MNode{position, lo, hi}, key, value, discriminator), query) == I.lookup(V, fallback, MNode{position, lo, hi}, query) : V}
def insertion_opposite_branch(V, fallback, value, lo, hi, position, discriminator, key, query, below, different):
  %Equal.sym(Bool, Nat.is_lt(position, discriminator), True{}, below) : {I.lookup(V, fallback, Map.ins.if(&2, V, key, value, lo, hi, position, discriminator, _), query) == I.lookup(V, fallback, MNode{position, lo, hi}, query) : V}
  %Equal.sym(String & Bool, Map.bit(key, position), (key, I.route_bit(Map.bit(key, position))), I.route_shape(key, position)) : {I.lookup(V, fallback, Map.ins.deep(&2, V, value, lo, hi, discriminator, position, _), query) == I.lookup(V, fallback, MNode{position, lo, hi}, query) : V}
  opposite_descent(V, fallback, value, lo, hi, position, discriminator, key, query, I.route_bit(Map.bit(key, position)), I.route_bit(Map.bit(query, position)), different, I.route_shape(query, position))
