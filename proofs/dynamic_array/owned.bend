import Base
import ../../src/dynamic_array.bend as A
import ../../types/dynamic_array.bend as E

# Owning storage laws quantify over Type, not just Data. They do not copy
# elements at runtime: repeated terms occur only in erased equality types.

def new_length(~T: Type) -> {A.length_owned(~T, A.new_owned(~T)) == (A.new_owned(~T), 0n) : A.DynArray<T> & Nat}:
  {==}

def new_capacity(~T: Type) -> {A.capacity_owned(~T, A.new_owned(~T)) == (A.new_owned(~T), 1n) : A.DynArray<T> & Nat}:
  {==}

def empty_pop(~T: Type, l: Nat, d: Nat, c: Nat, a: Array<Maybe<T>>) -> {A.pop_owned(~T, A.DA{l, d, c, 0n, a}) == (A.DA{l, d, c, 0n, a}, Fail{E.EmptyArray{}}) : A.DynArray<T> & Result<&2, &1, E.Error, T>}:
  {==}

def swap_rejected(~T: Type, l: Nat, d: Nat, c: Nat, n: Nat, a: Array<Maybe<T>>, i: Nat, v: T) -> {A.swap_checked_owned(~T, l, d, c, n, a, i, v, False{}) == (A.DA{l, d, c, n, a}, Fail{E.Rejected{E.IndexOutOfRange{}, v}}) : A.DynArray<T> & Result<&1, &1, E.Rejected<T>, Maybe<T>>}:
  {==}

def push_rejected(~T: Type, l: Nat, d: Nat, c: Nat, n: Nat, a: Array<Maybe<T>>, v: T) -> {A.push_room_owned(~T, l, d, c, n, a, v, False{}, False{}) == (A.DA{l, d, c, n, a}, Fail{E.Rejected{E.CapacityExceeded{}, v}}) : A.DynArray<T> & Result<&1, &2, E.Rejected<T>, Unit>}:
  {==}

def update_rejected(~T: Type, ~R: Type, l: Nat, d: Nat, c: Nat, n: Nat, a: Array<Maybe<T>>, i: Nat, f: T -> T & R) -> {A.update_checked_owned(~T, ~R, l, d, c, n, a, i, f, False{}) == (A.DA{l, d, c, n, a}, Fail{E.IndexOutOfRange{}}) : A.DynArray<T> & Result<&2, &1, E.Error, R>}:
  {==}

# A real public push/pop roundtrip with an arbitrary owning payload.
def first_push_pop(~T: Type, x: T) -> {A.pop_owned(~T, Pair.fst(A.DynArray<T>, Result<&1, &2, E.Rejected<T>, Unit>, A.push_owned(~T, A.new_owned(~T), x))) == (A.new_owned(~T), Done{x}) : A.DynArray<T> & Result<&2, &1, E.Error, T>}:
  {==}

def first_swap(~T: Type, x: T, y: T) -> {A.swap_owned(~T, A.DA{31n, 0n, 1n, 1n, ALeaf{Some{x}}}, 0n, y) == (A.DA{31n, 0n, 1n, 1n, ALeaf{Some{y}}}, Done{Some{x}}) : A.DynArray<T> & Result<&1, &1, E.Rejected<T>, Maybe<T>>}:
  {==}

def first_update(~T: Type, ~R: Type, x: T, f: T -> T & R) -> {A.update_owned(~T, ~R, A.DA{31n, 0n, 1n, 1n, ALeaf{Some{x}}}, 0n, f) == A.update_put_owned(~T, ~R, 31n, 0n, 1n, 1n, ALeaf{None{}}, 0n, f(x)) : A.DynArray<T> & Result<&2, &1, E.Error, R>}:
  {==}

def clear_length(~T: Type, l: Nat, d: Nat, c: Nat, n: Nat, a: Array<Maybe<T>>) -> {A.length_owned(~T, A.clear_owned(~T, A.DA{l, d, c, n, a})) == (A.DA{l, d, c, 0n, A.empty_owned(~T, d)}, 0n) : A.DynArray<T> & Nat}:
  {==}

def clear_capacity(~T: Type, l: Nat, d: Nat, c: Nat, n: Nat, a: Array<Maybe<T>>) -> {A.capacity_owned(~T, A.clear_owned(~T, A.DA{l, d, c, n, a})) == (A.DA{l, d, c, 0n, A.empty_owned(~T, d)}, c) : A.DynArray<T> & Nat}:
  {==}

def first_drain(~T: Type, x: T) -> {A.into_list_owned(~T, A.DA{31n, 0n, 1n, 1n, ALeaf{Some{x}}}) == Con{x, Nil{}} : List<T>}:
  {==}
