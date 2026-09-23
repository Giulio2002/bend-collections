import Base
import ../src/cache.bend as C
import ./invariants.bend as Inv
import ./recency_unique.bend as U
import ./recency_membership.bend as F
import ./map_key_membership.bend as Keys

law or_false:
  for b: Bool
  {b || False{} == b : Bool}
def or_false(b):
  match b:
    case False{}: {==}
    case True{}: {==}

law append_other:
  for xs: List<&2, String>
  for +key: String
  for +query: String
  for +unequal: {String.eq(query, key) == False{} : Bool}
  {Inv.member(List.append(&2, String, xs, Con{key, Nil{}}), query) == Inv.member(xs, query) : Bool}
def append_other(xs, key, query, unequal):
  match xs:
    case Nil{}:
      %Equal.sym(Bool, String.eq(key, query), False{}, U.unequal_reverse(query, key, unequal)) : {_ || False{} == False{} : Bool}
      {==}
    case Con{+head, +tail}:
      Equal.cong(Bool, Bool, b => String.eq(head, query) || b, Inv.member(List.append(&2, String, tail, Con{key, Nil{}}), query), Inv.member(tail, query), append_other(tail, key, query, unequal))

law append_same:
  for xs: List<&2, String>
  for +key: String
  {Inv.member(List.append(&2, String, xs, Con{key, Nil{}}), key) == True{} : Bool}
def append_same(xs, key):
  match xs:
    case Nil{}:
      %Equal.sym(Bool, String.eq(key, key), True{}, Keys.eq_true(key, key, {==})) : {_ || False{} == True{} : Bool}
      {==}
    case Con{+head, +tail}:
      Equal.trans(Bool, String.eq(head, key) || Inv.member(List.append(&2, String, tail, Con{key, Nil{}}), key), String.eq(head, key) || True{}, True{}, Equal.cong(Bool, Bool, b => String.eq(head, key) || b, Inv.member(List.append(&2, String, tail, Con{key, Nil{}}), key), True{}, append_same(tail, key)), Keys.or_true(String.eq(head, key)))

law move_branch:
  for +xs: List<&2, String>
  for +key: String
  for +query: String
  for equal: Bool
  for +decision: {String.eq(query, key) == equal : Bool}
  {Inv.member(List.append(&2, String, C.without(xs, key), Con{key, Nil{}}), query) == (equal || Inv.member(xs, query)) : Bool}
def move_branch(xs, key, query, equal, decision):
  match equal:
    case False{}:
      Equal.trans(Bool, Inv.member(List.append(&2, String, C.without(xs, key), Con{key, Nil{}}), query), Inv.member(C.without(xs, key), query), Inv.member(xs, query), append_other(C.without(xs, key), key, query, decision), F.filter_other(xs, key, query, decision))
    case True{}:
      %Equal.sym(String, query, key, U.equal_boolean(query, key, decision)) : {Inv.member(List.append(&2, String, C.without(xs, key), Con{key, Nil{}}), _) == True{} : Bool}
      append_same(C.without(xs, key), key)

law move:
  for +xs: List<&2, String>
  for +key: String
  for +query: String
  {Inv.member(List.append(&2, String, C.without(xs, key), Con{key, Nil{}}), query) == (String.eq(query, key) || Inv.member(xs, query)) : Bool}
def move(xs, key, query):
  move_branch(xs, key, query, String.eq(query, key), {==})
