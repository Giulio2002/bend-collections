import Base
import ../src/cache.bend as C
import ./invariants.bend as Inv
import ./recency_membership.bend as Filter
import ./recency_update_membership.bend as Move
import ./map_routing.bend as R
import ./map_delete_prefix.bend as And
import ./map_key_membership.bend as Keys

def moved(+xs: List<&2, String>, +key: String) -> List<&2, String>:
  List.append(&2, String, C.without(xs, key), Con{key, Nil{}})

law append_included:
  for xs: List<&2, String>
  for +ys: List<&2, String>
  for +key: String
  for +included: {Inv.included(xs, ys) == True{} : Bool}
  for +present: {Inv.member(ys, key) == True{} : Bool}
  {Inv.included(List.append(&2, String, xs, Con{key, Nil{}}), ys) == True{} : Bool}
def append_included(xs, ys, key, included, present):
  match xs:
    case Nil{}: And.conjunction(Inv.member(ys, key), True{}, present, {==})
    case Con{+head, +tail}:
      And.conjunction(Inv.member(ys, head), Inv.included(List.append(&2, String, tail, Con{key, Nil{}}), ys), R.and_left(Inv.member(ys, head), Inv.included(tail, ys), included), append_included(tail, ys, key, R.and_right(Inv.member(ys, head), Inv.included(tail, ys), included), present))

law forward:
  for +xs: List<&2, String>
  for +ys: List<&2, String>
  for +key: String
  for +included: {Inv.included(xs, ys) == True{} : Bool}
  for present: {Inv.member(ys, key) == True{} : Bool}
  {Inv.included(moved(xs, key), ys) == True{} : Bool}
def forward(xs, ys, key, included, present):
  append_included(C.without(xs, key), ys, key, Filter.filter_included_left(xs, ys, key, included), present)

law retained:
  for +xs: List<&2, String>
  for +key: String
  for +query: String
  for present: {Inv.member(xs, query) == True{} : Bool}
  {Inv.member(moved(xs, key), query) == True{} : Bool}
def retained(xs, key, query, present):
  Equal.trans(Bool, Inv.member(moved(xs, key), query), String.eq(query, key) || Inv.member(xs, query), True{}, Move.move(xs, key, query), %Equal.sym(Bool, Inv.member(xs, query), True{}, present) : {String.eq(query, key) || _ == True{} : Bool} Keys.or_true(String.eq(query, key)))

law backward:
  for xs: List<&2, String>
  for +ys: List<&2, String>
  for +key: String
  for +included: {Inv.included(xs, ys) == True{} : Bool}
  {Inv.included(xs, moved(ys, key)) == True{} : Bool}
def backward(xs, ys, key, included):
  match xs:
    case Nil{}: {==}
    case Con{+head, +tail}:
      And.conjunction(Inv.member(moved(ys, key), head), Inv.included(tail, moved(ys, key)), retained(ys, key, head, R.and_left(Inv.member(ys, head), Inv.included(tail, ys), included)), backward(tail, ys, key, R.and_right(Inv.member(ys, head), Inv.included(tail, ys), included)))
