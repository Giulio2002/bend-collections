import Base
import ../../../src/containers/dynamic_array.bend as A
import ../../../src/containers/types/dynamic_array.bend as E
import ./owned.bend as P

# Explicit checked instances: template declarations alone are not proof checks.
def array_new_length() -> {A.length_owned(~Array<U32>, A.new_owned(~Array<U32>)) == (A.new_owned(~Array<U32>), 0n) : A.DynArray<Array<U32>> & Nat}:
  P.new_length(~Array<U32>)

def array_new_capacity() -> {A.capacity_owned(~Array<U32>, A.new_owned(~Array<U32>)) == (A.new_owned(~Array<U32>), 1n) : A.DynArray<Array<U32>> & Nat}:
  P.new_capacity(~Array<U32>)

def array_empty_pop(l: Nat, d: Nat, c: Nat, a: Array<Maybe<Array<U32>>>) -> {A.pop_owned(~Array<U32>, A.DA{l, d, c, 0n, a}) == (A.DA{l, d, c, 0n, a}, Fail{E.EmptyArray{}}) : A.DynArray<Array<U32>> & Result<&2, &1, E.Error, Array<U32>>}:
  P.empty_pop(~Array<U32>, l, d, c, a)

def array_swap_rejected(l: Nat, d: Nat, c: Nat, n: Nat, a: Array<Maybe<Array<U32>>>, i: Nat, v: Array<U32>) -> {A.swap_checked_owned(~Array<U32>, l, d, c, n, a, i, v, False{}) == (A.DA{l, d, c, n, a}, Fail{E.Rejected{E.IndexOutOfRange{}, v}}) : A.DynArray<Array<U32>> & Result<&1, &1, E.Rejected<Array<U32>>, Maybe<Array<U32>>>}:
  P.swap_rejected(~Array<U32>, l, d, c, n, a, i, v)

def array_push_rejected(l: Nat, d: Nat, c: Nat, n: Nat, a: Array<Maybe<Array<U32>>>, v: Array<U32>) -> {A.push_room_owned(~Array<U32>, l, d, c, n, a, v, False{}, False{}) == (A.DA{l, d, c, n, a}, Fail{E.Rejected{E.CapacityExceeded{}, v}}) : A.DynArray<Array<U32>> & Result<&1, &2, E.Rejected<Array<U32>>, Unit>}:
  P.push_rejected(~Array<U32>, l, d, c, n, a, v)

def array_update_rejected(l: Nat, d: Nat, c: Nat, n: Nat, a: Array<Maybe<Array<U32>>>, i: Nat, f: Array<U32> -> Array<U32> & Array<U32>) -> {A.update_checked_owned(~Array<U32>, ~Array<U32>, l, d, c, n, a, i, f, False{}) == (A.DA{l, d, c, n, a}, Fail{E.IndexOutOfRange{}}) : A.DynArray<Array<U32>> & Result<&2, &1, E.Error, Array<U32>>}:
  P.update_rejected(~Array<U32>, ~Array<U32>, l, d, c, n, a, i, f)

def array_first_push_pop(x: Array<U32>) -> {A.pop_owned(~Array<U32>, Pair.fst(A.DynArray<Array<U32>>, Result<&1, &2, E.Rejected<Array<U32>>, Unit>, A.push_owned(~Array<U32>, A.new_owned(~Array<U32>), x))) == (A.new_owned(~Array<U32>), Done{x}) : A.DynArray<Array<U32>> & Result<&2, &1, E.Error, Array<U32>>}:
  P.first_push_pop(~Array<U32>, x)

def array_first_swap(x: Array<U32>, y: Array<U32>) -> {A.swap_owned(~Array<U32>, A.DA{31n, 0n, 1n, 1n, ALeaf{Some{x}}}, 0n, y) == (A.DA{31n, 0n, 1n, 1n, ALeaf{Some{y}}}, Done{Some{x}}) : A.DynArray<Array<U32>> & Result<&1, &1, E.Rejected<Array<U32>>, Maybe<Array<U32>>>}:
  P.first_swap(~Array<U32>, x, y)

def array_first_update(x: Array<U32>, f: Array<U32> -> Array<U32> & Array<U32>) -> {A.update_owned(~Array<U32>, ~Array<U32>, A.DA{31n, 0n, 1n, 1n, ALeaf{Some{x}}}, 0n, f) == A.update_put_owned(~Array<U32>, ~Array<U32>, 31n, 0n, 1n, 1n, ALeaf{None{}}, 0n, f(x)) : A.DynArray<Array<U32>> & Result<&2, &1, E.Error, Array<U32>>}:
  P.first_update(~Array<U32>, ~Array<U32>, x, f)

def array_clear_length(l: Nat, d: Nat, c: Nat, n: Nat, a: Array<Maybe<Array<U32>>>) -> {A.length_owned(~Array<U32>, A.clear_owned(~Array<U32>, A.DA{l, d, c, n, a})) == (A.DA{l, d, c, 0n, A.empty_owned(~Array<U32>, d)}, 0n) : A.DynArray<Array<U32>> & Nat}:
  P.clear_length(~Array<U32>, l, d, c, n, a)

def array_clear_capacity(l: Nat, d: Nat, c: Nat, n: Nat, a: Array<Maybe<Array<U32>>>) -> {A.capacity_owned(~Array<U32>, A.clear_owned(~Array<U32>, A.DA{l, d, c, n, a})) == (A.DA{l, d, c, 0n, A.empty_owned(~Array<U32>, d)}, c) : A.DynArray<Array<U32>> & Nat}:
  P.clear_capacity(~Array<U32>, l, d, c, n, a)

def array_first_drain(x: Array<U32>) -> {A.into_list_owned(~Array<U32>, A.DA{31n, 0n, 1n, 1n, ALeaf{Some{x}}}) == Con{x, Nil{}} : List<Array<U32>>}:
  P.first_drain(~Array<U32>, x)

def nested_new_length() -> {A.length_owned(~A.DynArray<&2, U32>, A.new_owned(~A.DynArray<&2, U32>)) == (A.new_owned(~A.DynArray<&2, U32>), 0n) : A.DynArray<A.DynArray<&2, U32>> & Nat}:
  P.new_length(~A.DynArray<&2, U32>)

def nested_new_capacity() -> {A.capacity_owned(~A.DynArray<&2, U32>, A.new_owned(~A.DynArray<&2, U32>)) == (A.new_owned(~A.DynArray<&2, U32>), 1n) : A.DynArray<A.DynArray<&2, U32>> & Nat}:
  P.new_capacity(~A.DynArray<&2, U32>)

def nested_empty_pop(l: Nat, d: Nat, c: Nat, a: Array<Maybe<A.DynArray<&2, U32>>>) -> {A.pop_owned(~A.DynArray<&2, U32>, A.DA{l, d, c, 0n, a}) == (A.DA{l, d, c, 0n, a}, Fail{E.EmptyArray{}}) : A.DynArray<A.DynArray<&2, U32>> & Result<&2, &1, E.Error, A.DynArray<&2, U32>>}:
  P.empty_pop(~A.DynArray<&2, U32>, l, d, c, a)

def nested_swap_rejected(l: Nat, d: Nat, c: Nat, n: Nat, a: Array<Maybe<A.DynArray<&2, U32>>>, i: Nat, v: A.DynArray<&2, U32>) -> {A.swap_checked_owned(~A.DynArray<&2, U32>, l, d, c, n, a, i, v, False{}) == (A.DA{l, d, c, n, a}, Fail{E.Rejected{E.IndexOutOfRange{}, v}}) : A.DynArray<A.DynArray<&2, U32>> & Result<&1, &1, E.Rejected<A.DynArray<&2, U32>>, Maybe<A.DynArray<&2, U32>>>}:
  P.swap_rejected(~A.DynArray<&2, U32>, l, d, c, n, a, i, v)

def nested_push_rejected(l: Nat, d: Nat, c: Nat, n: Nat, a: Array<Maybe<A.DynArray<&2, U32>>>, v: A.DynArray<&2, U32>) -> {A.push_room_owned(~A.DynArray<&2, U32>, l, d, c, n, a, v, False{}, False{}) == (A.DA{l, d, c, n, a}, Fail{E.Rejected{E.CapacityExceeded{}, v}}) : A.DynArray<A.DynArray<&2, U32>> & Result<&1, &2, E.Rejected<A.DynArray<&2, U32>>, Unit>}:
  P.push_rejected(~A.DynArray<&2, U32>, l, d, c, n, a, v)

def nested_update_rejected(l: Nat, d: Nat, c: Nat, n: Nat, a: Array<Maybe<A.DynArray<&2, U32>>>, i: Nat, f: A.DynArray<&2, U32> -> A.DynArray<&2, U32> & Array<U32>) -> {A.update_checked_owned(~A.DynArray<&2, U32>, ~Array<U32>, l, d, c, n, a, i, f, False{}) == (A.DA{l, d, c, n, a}, Fail{E.IndexOutOfRange{}}) : A.DynArray<A.DynArray<&2, U32>> & Result<&2, &1, E.Error, Array<U32>>}:
  P.update_rejected(~A.DynArray<&2, U32>, ~Array<U32>, l, d, c, n, a, i, f)

def nested_first_push_pop(x: A.DynArray<&2, U32>) -> {A.pop_owned(~A.DynArray<&2, U32>, Pair.fst(A.DynArray<A.DynArray<&2, U32>>, Result<&1, &2, E.Rejected<A.DynArray<&2, U32>>, Unit>, A.push_owned(~A.DynArray<&2, U32>, A.new_owned(~A.DynArray<&2, U32>), x))) == (A.new_owned(~A.DynArray<&2, U32>), Done{x}) : A.DynArray<A.DynArray<&2, U32>> & Result<&2, &1, E.Error, A.DynArray<&2, U32>>}:
  P.first_push_pop(~A.DynArray<&2, U32>, x)

def nested_first_swap(x: A.DynArray<&2, U32>, y: A.DynArray<&2, U32>) -> {A.swap_owned(~A.DynArray<&2, U32>, A.DA{31n, 0n, 1n, 1n, ALeaf{Some{x}}}, 0n, y) == (A.DA{31n, 0n, 1n, 1n, ALeaf{Some{y}}}, Done{Some{x}}) : A.DynArray<A.DynArray<&2, U32>> & Result<&1, &1, E.Rejected<A.DynArray<&2, U32>>, Maybe<A.DynArray<&2, U32>>>}:
  P.first_swap(~A.DynArray<&2, U32>, x, y)

def nested_first_update(x: A.DynArray<&2, U32>, f: A.DynArray<&2, U32> -> A.DynArray<&2, U32> & Array<U32>) -> {A.update_owned(~A.DynArray<&2, U32>, ~Array<U32>, A.DA{31n, 0n, 1n, 1n, ALeaf{Some{x}}}, 0n, f) == A.update_put_owned(~A.DynArray<&2, U32>, ~Array<U32>, 31n, 0n, 1n, 1n, ALeaf{None{}}, 0n, f(x)) : A.DynArray<A.DynArray<&2, U32>> & Result<&2, &1, E.Error, Array<U32>>}:
  P.first_update(~A.DynArray<&2, U32>, ~Array<U32>, x, f)

def nested_clear_length(l: Nat, d: Nat, c: Nat, n: Nat, a: Array<Maybe<A.DynArray<&2, U32>>>) -> {A.length_owned(~A.DynArray<&2, U32>, A.clear_owned(~A.DynArray<&2, U32>, A.DA{l, d, c, n, a})) == (A.DA{l, d, c, 0n, A.empty_owned(~A.DynArray<&2, U32>, d)}, 0n) : A.DynArray<A.DynArray<&2, U32>> & Nat}:
  P.clear_length(~A.DynArray<&2, U32>, l, d, c, n, a)

def nested_clear_capacity(l: Nat, d: Nat, c: Nat, n: Nat, a: Array<Maybe<A.DynArray<&2, U32>>>) -> {A.capacity_owned(~A.DynArray<&2, U32>, A.clear_owned(~A.DynArray<&2, U32>, A.DA{l, d, c, n, a})) == (A.DA{l, d, c, 0n, A.empty_owned(~A.DynArray<&2, U32>, d)}, c) : A.DynArray<A.DynArray<&2, U32>> & Nat}:
  P.clear_capacity(~A.DynArray<&2, U32>, l, d, c, n, a)

def nested_first_drain(x: A.DynArray<&2, U32>) -> {A.into_list_owned(~A.DynArray<&2, U32>, A.DA{31n, 0n, 1n, 1n, ALeaf{Some{x}}}) == Con{x, Nil{}} : List<A.DynArray<&2, U32>>}:
  P.first_drain(~A.DynArray<&2, U32>, x)

def closure_new_length() -> {A.length_owned(~(U32 -> U32), A.new_owned(~(U32 -> U32))) == (A.new_owned(~(U32 -> U32)), 0n) : A.DynArray<(U32 -> U32)> & Nat}:
  P.new_length(~(U32 -> U32))

def closure_new_capacity() -> {A.capacity_owned(~(U32 -> U32), A.new_owned(~(U32 -> U32))) == (A.new_owned(~(U32 -> U32)), 1n) : A.DynArray<(U32 -> U32)> & Nat}:
  P.new_capacity(~(U32 -> U32))

def closure_empty_pop(l: Nat, d: Nat, c: Nat, a: Array<Maybe<(U32 -> U32)>>) -> {A.pop_owned(~(U32 -> U32), A.DA{l, d, c, 0n, a}) == (A.DA{l, d, c, 0n, a}, Fail{E.EmptyArray{}}) : A.DynArray<(U32 -> U32)> & Result<&2, &1, E.Error, (U32 -> U32)>}:
  P.empty_pop(~(U32 -> U32), l, d, c, a)

def closure_swap_rejected(l: Nat, d: Nat, c: Nat, n: Nat, a: Array<Maybe<(U32 -> U32)>>, i: Nat, v: (U32 -> U32)) -> {A.swap_checked_owned(~(U32 -> U32), l, d, c, n, a, i, v, False{}) == (A.DA{l, d, c, n, a}, Fail{E.Rejected{E.IndexOutOfRange{}, v}}) : A.DynArray<(U32 -> U32)> & Result<&1, &1, E.Rejected<(U32 -> U32)>, Maybe<(U32 -> U32)>>}:
  P.swap_rejected(~(U32 -> U32), l, d, c, n, a, i, v)

def closure_push_rejected(l: Nat, d: Nat, c: Nat, n: Nat, a: Array<Maybe<(U32 -> U32)>>, v: (U32 -> U32)) -> {A.push_room_owned(~(U32 -> U32), l, d, c, n, a, v, False{}, False{}) == (A.DA{l, d, c, n, a}, Fail{E.Rejected{E.CapacityExceeded{}, v}}) : A.DynArray<(U32 -> U32)> & Result<&1, &2, E.Rejected<(U32 -> U32)>, Unit>}:
  P.push_rejected(~(U32 -> U32), l, d, c, n, a, v)

def closure_update_rejected(l: Nat, d: Nat, c: Nat, n: Nat, a: Array<Maybe<(U32 -> U32)>>, i: Nat, f: (U32 -> U32) -> (U32 -> U32) & Array<U32>) -> {A.update_checked_owned(~(U32 -> U32), ~Array<U32>, l, d, c, n, a, i, f, False{}) == (A.DA{l, d, c, n, a}, Fail{E.IndexOutOfRange{}}) : A.DynArray<(U32 -> U32)> & Result<&2, &1, E.Error, Array<U32>>}:
  P.update_rejected(~(U32 -> U32), ~Array<U32>, l, d, c, n, a, i, f)

def closure_first_push_pop(x: (U32 -> U32)) -> {A.pop_owned(~(U32 -> U32), Pair.fst(A.DynArray<(U32 -> U32)>, Result<&1, &2, E.Rejected<(U32 -> U32)>, Unit>, A.push_owned(~(U32 -> U32), A.new_owned(~(U32 -> U32)), x))) == (A.new_owned(~(U32 -> U32)), Done{x}) : A.DynArray<(U32 -> U32)> & Result<&2, &1, E.Error, (U32 -> U32)>}:
  P.first_push_pop(~(U32 -> U32), x)

def closure_first_swap(x: (U32 -> U32), y: (U32 -> U32)) -> {A.swap_owned(~(U32 -> U32), A.DA{31n, 0n, 1n, 1n, ALeaf{Some{x}}}, 0n, y) == (A.DA{31n, 0n, 1n, 1n, ALeaf{Some{y}}}, Done{Some{x}}) : A.DynArray<(U32 -> U32)> & Result<&1, &1, E.Rejected<(U32 -> U32)>, Maybe<(U32 -> U32)>>}:
  P.first_swap(~(U32 -> U32), x, y)

def closure_first_update(x: (U32 -> U32), f: (U32 -> U32) -> (U32 -> U32) & Array<U32>) -> {A.update_owned(~(U32 -> U32), ~Array<U32>, A.DA{31n, 0n, 1n, 1n, ALeaf{Some{x}}}, 0n, f) == A.update_put_owned(~(U32 -> U32), ~Array<U32>, 31n, 0n, 1n, 1n, ALeaf{None{}}, 0n, f(x)) : A.DynArray<(U32 -> U32)> & Result<&2, &1, E.Error, Array<U32>>}:
  P.first_update(~(U32 -> U32), ~Array<U32>, x, f)

def closure_clear_length(l: Nat, d: Nat, c: Nat, n: Nat, a: Array<Maybe<(U32 -> U32)>>) -> {A.length_owned(~(U32 -> U32), A.clear_owned(~(U32 -> U32), A.DA{l, d, c, n, a})) == (A.DA{l, d, c, 0n, A.empty_owned(~(U32 -> U32), d)}, 0n) : A.DynArray<(U32 -> U32)> & Nat}:
  P.clear_length(~(U32 -> U32), l, d, c, n, a)

def closure_clear_capacity(l: Nat, d: Nat, c: Nat, n: Nat, a: Array<Maybe<(U32 -> U32)>>) -> {A.capacity_owned(~(U32 -> U32), A.clear_owned(~(U32 -> U32), A.DA{l, d, c, n, a})) == (A.DA{l, d, c, 0n, A.empty_owned(~(U32 -> U32), d)}, c) : A.DynArray<(U32 -> U32)> & Nat}:
  P.clear_capacity(~(U32 -> U32), l, d, c, n, a)

def closure_first_drain(x: (U32 -> U32)) -> {A.into_list_owned(~(U32 -> U32), A.DA{31n, 0n, 1n, 1n, ALeaf{Some{x}}}) == Con{x, Nil{}} : List<(U32 -> U32)>}:
  P.first_drain(~(U32 -> U32), x)
