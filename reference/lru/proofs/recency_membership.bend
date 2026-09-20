import Base
import ../src/cache.bend as C
import ./invariants.bend as Inv
import ./recency_unique.bend as U
import ./map_routing.bend as R
import ./map_delete_prefix.bend as And

# Filtering a removed code retains exactly the membership of every other code.
law filter_branch:
  for +head: String
  for +tail: List<&2, String>
  for +removed: String
  for +query: String
  for drop: Bool
  for decision: {String.eq(head, removed) == drop : Bool}
  for unequal: {String.eq(query, removed) == False{} : Bool}
  for induction: {Inv.member(C.without(tail, removed), query) == Inv.member(tail, query) : Bool}
  {Inv.member(C.without_keep(head, C.without(tail, removed), drop), query) == Inv.member(Con{head, tail}, query) : Bool}
def filter_branch(head, tail, removed, query, drop, decision, unequal, induction):
  match drop:
    case False{}:
      Equal.cong(Bool, Bool, b => String.eq(head, query) || b, Inv.member(C.without(tail, removed), query), Inv.member(tail, query), induction)
    case True{}:
      %Equal.sym(String, head, removed, U.equal_boolean(head, removed, decision)) : {Inv.member(C.without(tail, removed), query) == String.eq(_, query) || Inv.member(tail, query) : Bool}
      %Equal.sym(Bool, String.eq(removed, query), False{}, U.unequal_reverse(query, removed, unequal)) : {Inv.member(C.without(tail, removed), query) == _ || Inv.member(tail, query) : Bool}
      induction

law filter_other:
  for xs: List<&2, String>
  for +removed: String
  for +query: String
  for +unequal: {String.eq(query, removed) == False{} : Bool}
  {Inv.member(C.without(xs, removed), query) == Inv.member(xs, query) : Bool}
def filter_other(xs, removed, query, unequal):
  match xs:
    case Nil{}: {==}
    case Con{+head, +tail}:
      filter_branch(head, tail, removed, query, String.eq(head, removed), {==}, unequal, filter_other(tail, removed, query, unequal))

law keep_included:
  for +head: String
  for +tail: List<&2, String>
  for +ys: List<&2, String>
  for drop: Bool
  for head_in: {Inv.member(ys, head) == True{} : Bool}
  for tail_in: {Inv.included(tail, ys) == True{} : Bool}
  {Inv.included(C.without_keep(head, tail, drop), ys) == True{} : Bool}
def keep_included(head, tail, ys, drop, head_in, tail_in):
  match drop:
    case True{}: tail_in
    case False{}: And.conjunction(Inv.member(ys, head), Inv.included(tail, ys), head_in, tail_in)

law filter_included_left:
  for xs: List<&2, String>
  for +ys: List<&2, String>
  for +removed: String
  for +included: {Inv.included(xs, ys) == True{} : Bool}
  {Inv.included(C.without(xs, removed), ys) == True{} : Bool}
def filter_included_left(xs, ys, removed, included):
  match xs:
    case Nil{}: {==}
    case Con{+head, +tail}:
      keep_included(head, C.without(tail, removed), ys, String.eq(head, removed), R.and_left(Inv.member(ys, head), Inv.included(tail, ys), included), filter_included_left(tail, ys, removed, R.and_right(Inv.member(ys, head), Inv.included(tail, ys), included)))

law filter_both_branch:
  for +head: String
  for +tail: List<&2, String>
  for +ys: List<&2, String>
  for +removed: String
  for drop: Bool
  for decision: {String.eq(head, removed) == drop : Bool}
  for head_in: {Inv.member(ys, head) == True{} : Bool}
  for tail_in: {Inv.included(C.without(tail, removed), C.without(ys, removed)) == True{} : Bool}
  {Inv.included(C.without_keep(head, C.without(tail, removed), drop), C.without(ys, removed)) == True{} : Bool}
def filter_both_branch(head, tail, ys, removed, drop, decision, head_in, tail_in):
  match drop:
    case True{}: tail_in
    case False{}:
      And.conjunction(Inv.member(C.without(ys, removed), head), Inv.included(C.without(tail, removed), C.without(ys, removed)), Equal.trans(Bool, Inv.member(C.without(ys, removed), head), Inv.member(ys, head), True{}, filter_other(ys, removed, head, decision), head_in), tail_in)

# This is the order-side law needed when deleting from both representations.
law filter_included_both:
  for xs: List<&2, String>
  for +ys: List<&2, String>
  for +removed: String
  for +included: {Inv.included(xs, ys) == True{} : Bool}
  {Inv.included(C.without(xs, removed), C.without(ys, removed)) == True{} : Bool}
def filter_included_both(xs, ys, removed, included):
  match xs:
    case Nil{}: {==}
    case Con{+head, +tail}:
      filter_both_branch(head, tail, ys, removed, String.eq(head, removed), {==}, R.and_left(Inv.member(ys, head), Inv.included(tail, ys), included), filter_included_both(tail, ys, removed, R.and_right(Inv.member(ys, head), Inv.included(tail, ys), included)))
