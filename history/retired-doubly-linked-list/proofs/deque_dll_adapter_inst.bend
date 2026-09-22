import Base
import ./dlist/state.bend as ST
import ./dlist/reuse_insert.bend as RI
import ../src/deque.bend as Q
import ../src/doubly_linked_list.bend as D
import ../types/deque.bend as E
import ../types/doubly_linked_list.bend as H
import ./deque_dll_adapter.bend as A

def new_uses_dll_u32() -> {Q.new(~U32) == Q.DQ{D.new(~U32, 0)} : Q.Deque<U32>}:
  A.new_uses_dll(~U32)

def push_front_uses_dll_u32(+sh: ST.Shadow<U32>, +free: U32, +x: U32) -> {Q.push_front(~U32, Q.DQ{RI.real_with_free(~U32, sh, free)}, x) == Q.pushed(~U32, D.push_front_free(~U32, RI.real_with_free(~U32, sh, free), x)) : Q.Deque<U32>}:
  A.push_front_uses_dll(~U32, sh, free, x)

def push_back_uses_dll_u32(+sh: ST.Shadow<U32>, +free: U32, +x: U32) -> {Q.push_back(~U32, Q.DQ{RI.real_with_free(~U32, sh, free)}, x) == Q.pushed(~U32, D.push_back_free(~U32, RI.real_with_free(~U32, sh, free), x)) : Q.Deque<U32>}:
  A.push_back_uses_dll(~U32, sh, free, x)

def pop_front_uses_dll_u32(+sh: ST.Shadow<U32>, +free: U32) -> {Q.pop_front(~U32, Q.DQ{RI.real_with_free(~U32, sh, free)}) == Q.lift(~U32, D.pop_front_free(~U32, RI.real_with_free(~U32, sh, free))) : Q.Deque<U32> & Result<&2, &2, E.Error, U32>}:
  A.pop_front_uses_dll(~U32, sh, free)

def pop_back_uses_dll_u32(+sh: ST.Shadow<U32>, +free: U32) -> {Q.pop_back(~U32, Q.DQ{RI.real_with_free(~U32, sh, free)}) == Q.lift(~U32, D.pop_back_free(~U32, RI.real_with_free(~U32, sh, free))) : Q.Deque<U32> & Result<&2, &2, E.Error, U32>}:
  A.pop_back_uses_dll(~U32, sh, free)

def peek_front_uses_dll_u32(+sh: ST.Shadow<U32>, +free: U32) -> {Q.peek_front(~U32, Q.DQ{RI.real_with_free(~U32, sh, free)}) == Q.lift(~U32, D.peek_front(~U32, RI.real_with_free(~U32, sh, free))) : Q.Deque<U32> & Result<&2, &2, E.Error, U32>}:
  A.peek_front_uses_dll(~U32, sh, free)

def peek_back_uses_dll_u32(+sh: ST.Shadow<U32>, +free: U32) -> {Q.peek_back(~U32, Q.DQ{RI.real_with_free(~U32, sh, free)}) == Q.lift(~U32, D.peek_back(~U32, RI.real_with_free(~U32, sh, free))) : Q.Deque<U32> & Result<&2, &2, E.Error, U32>}:
  A.peek_back_uses_dll(~U32, sh, free)

def length_uses_dll_u32(+sh: ST.Shadow<U32>, +free: U32) -> {Q.length(~U32, Q.DQ{RI.real_with_free(~U32, sh, free)}) == Q.lift_nat(~U32, D.length(~U32, RI.real_with_free(~U32, sh, free))) : Q.Deque<U32> & Nat}:
  A.length_uses_dll(~U32, sh, free)

def list_uses_dll_u32(+sh: ST.Shadow<U32>, +free: U32) -> {Q.to_list(~U32, Q.DQ{RI.real_with_free(~U32, sh, free)}) == Q.lift_list(~U32, D.to_list(~U32, RI.real_with_free(~U32, sh, free))) : Q.Deque<U32> & List<&2, U32>}:
  A.list_uses_dll(~U32, sh, free)

def first_front_u32(+x: U32) -> {Q.push_front(~U32, Q.new(~U32), x) == A.singleton(~U32, x) : Q.Deque<U32>}:
  A.first_front(~U32, x)

def first_back_u32(+x: U32) -> {Q.push_back(~U32, Q.new(~U32), x) == A.singleton(~U32, x) : Q.Deque<U32>}:
  A.first_back(~U32, x)

def reuse_front_u32(+x: U32) -> {Q.push_front(~U32, A.recycled(~U32), x) == A.singleton(~U32, x) : Q.Deque<U32>}:
  A.reuse_front(~U32, x)

def reuse_back_u32(+x: U32) -> {Q.push_back(~U32, A.recycled(~U32), x) == A.singleton(~U32, x) : Q.Deque<U32>}:
  A.reuse_back(~U32, x)

def retire_front_u32(+x: U32) -> {Q.pop_front(~U32, A.singleton(~U32, x)) == (A.recycled(~U32), Done{x}) : Q.Deque<U32> & Result<&2, &2, E.Error, U32>}:
  A.retire_front(~U32, x)

def retire_back_u32(+x: U32) -> {Q.pop_back(~U32, A.singleton(~U32, x)) == (A.recycled(~U32), Done{x}) : Q.Deque<U32> & Result<&2, &2, E.Error, U32>}:
  A.retire_back(~U32, x)

def recycled_empty_front_u32() -> {Q.pop_front(~U32, A.recycled(~U32)) == (A.recycled(~U32), Fail{E.EmptyDeque{}}) : Q.Deque<U32> & Result<&2, &2, E.Error, U32>}:
  A.recycled_empty_front(~U32)

def recycled_empty_back_u32() -> {Q.pop_back(~U32, A.recycled(~U32)) == (A.recycled(~U32), Fail{E.EmptyDeque{}}) : Q.Deque<U32> & Result<&2, &2, E.Error, U32>}:
  A.recycled_empty_back(~U32)

def initial_empty_front_u32() -> {Q.pop_front(~U32, Q.new(~U32)) == (Q.new(~U32), Fail{E.EmptyDeque{}}) : Q.Deque<U32> & Result<&2, &2, E.Error, U32>}:
  A.initial_empty_front(~U32)

def initial_empty_back_u32() -> {Q.pop_back(~U32, Q.new(~U32)) == (Q.new(~U32), Fail{E.EmptyDeque{}}) : Q.Deque<U32> & Result<&2, &2, E.Error, U32>}:
  A.initial_empty_back(~U32)

def unlimited_reuse_u32(+xs: List<&2, U32>, +acc: List<&2, U32>) -> {A.cycles(~U32, xs, (A.recycled(~U32), acc)) == (A.recycled(~U32), List.reverse.go(&2, U32, xs, acc)) : Q.Deque<U32> & List<&2, U32>}:
  A.unlimited_reuse(~U32, xs, acc)

def new_uses_dll_string() -> {Q.new(~String) == Q.DQ{D.new(~String, 0)} : Q.Deque<String>}:
  A.new_uses_dll(~String)

def push_front_uses_dll_string(+sh: ST.Shadow<String>, +free: U32, +x: String) -> {Q.push_front(~String, Q.DQ{RI.real_with_free(~String, sh, free)}, x) == Q.pushed(~String, D.push_front_free(~String, RI.real_with_free(~String, sh, free), x)) : Q.Deque<String>}:
  A.push_front_uses_dll(~String, sh, free, x)

def push_back_uses_dll_string(+sh: ST.Shadow<String>, +free: U32, +x: String) -> {Q.push_back(~String, Q.DQ{RI.real_with_free(~String, sh, free)}, x) == Q.pushed(~String, D.push_back_free(~String, RI.real_with_free(~String, sh, free), x)) : Q.Deque<String>}:
  A.push_back_uses_dll(~String, sh, free, x)

def pop_front_uses_dll_string(+sh: ST.Shadow<String>, +free: U32) -> {Q.pop_front(~String, Q.DQ{RI.real_with_free(~String, sh, free)}) == Q.lift(~String, D.pop_front_free(~String, RI.real_with_free(~String, sh, free))) : Q.Deque<String> & Result<&2, &2, E.Error, String>}:
  A.pop_front_uses_dll(~String, sh, free)

def pop_back_uses_dll_string(+sh: ST.Shadow<String>, +free: U32) -> {Q.pop_back(~String, Q.DQ{RI.real_with_free(~String, sh, free)}) == Q.lift(~String, D.pop_back_free(~String, RI.real_with_free(~String, sh, free))) : Q.Deque<String> & Result<&2, &2, E.Error, String>}:
  A.pop_back_uses_dll(~String, sh, free)

def peek_front_uses_dll_string(+sh: ST.Shadow<String>, +free: U32) -> {Q.peek_front(~String, Q.DQ{RI.real_with_free(~String, sh, free)}) == Q.lift(~String, D.peek_front(~String, RI.real_with_free(~String, sh, free))) : Q.Deque<String> & Result<&2, &2, E.Error, String>}:
  A.peek_front_uses_dll(~String, sh, free)

def peek_back_uses_dll_string(+sh: ST.Shadow<String>, +free: U32) -> {Q.peek_back(~String, Q.DQ{RI.real_with_free(~String, sh, free)}) == Q.lift(~String, D.peek_back(~String, RI.real_with_free(~String, sh, free))) : Q.Deque<String> & Result<&2, &2, E.Error, String>}:
  A.peek_back_uses_dll(~String, sh, free)

def length_uses_dll_string(+sh: ST.Shadow<String>, +free: U32) -> {Q.length(~String, Q.DQ{RI.real_with_free(~String, sh, free)}) == Q.lift_nat(~String, D.length(~String, RI.real_with_free(~String, sh, free))) : Q.Deque<String> & Nat}:
  A.length_uses_dll(~String, sh, free)

def list_uses_dll_string(+sh: ST.Shadow<String>, +free: U32) -> {Q.to_list(~String, Q.DQ{RI.real_with_free(~String, sh, free)}) == Q.lift_list(~String, D.to_list(~String, RI.real_with_free(~String, sh, free))) : Q.Deque<String> & List<&2, String>}:
  A.list_uses_dll(~String, sh, free)

def first_front_string(+x: String) -> {Q.push_front(~String, Q.new(~String), x) == A.singleton(~String, x) : Q.Deque<String>}:
  A.first_front(~String, x)

def first_back_string(+x: String) -> {Q.push_back(~String, Q.new(~String), x) == A.singleton(~String, x) : Q.Deque<String>}:
  A.first_back(~String, x)

def reuse_front_string(+x: String) -> {Q.push_front(~String, A.recycled(~String), x) == A.singleton(~String, x) : Q.Deque<String>}:
  A.reuse_front(~String, x)

def reuse_back_string(+x: String) -> {Q.push_back(~String, A.recycled(~String), x) == A.singleton(~String, x) : Q.Deque<String>}:
  A.reuse_back(~String, x)

def retire_front_string(+x: String) -> {Q.pop_front(~String, A.singleton(~String, x)) == (A.recycled(~String), Done{x}) : Q.Deque<String> & Result<&2, &2, E.Error, String>}:
  A.retire_front(~String, x)

def retire_back_string(+x: String) -> {Q.pop_back(~String, A.singleton(~String, x)) == (A.recycled(~String), Done{x}) : Q.Deque<String> & Result<&2, &2, E.Error, String>}:
  A.retire_back(~String, x)

def recycled_empty_front_string() -> {Q.pop_front(~String, A.recycled(~String)) == (A.recycled(~String), Fail{E.EmptyDeque{}}) : Q.Deque<String> & Result<&2, &2, E.Error, String>}:
  A.recycled_empty_front(~String)

def recycled_empty_back_string() -> {Q.pop_back(~String, A.recycled(~String)) == (A.recycled(~String), Fail{E.EmptyDeque{}}) : Q.Deque<String> & Result<&2, &2, E.Error, String>}:
  A.recycled_empty_back(~String)

def initial_empty_front_string() -> {Q.pop_front(~String, Q.new(~String)) == (Q.new(~String), Fail{E.EmptyDeque{}}) : Q.Deque<String> & Result<&2, &2, E.Error, String>}:
  A.initial_empty_front(~String)

def initial_empty_back_string() -> {Q.pop_back(~String, Q.new(~String)) == (Q.new(~String), Fail{E.EmptyDeque{}}) : Q.Deque<String> & Result<&2, &2, E.Error, String>}:
  A.initial_empty_back(~String)

def unlimited_reuse_string(+xs: List<&2, String>, +acc: List<&2, String>) -> {A.cycles(~String, xs, (A.recycled(~String), acc)) == (A.recycled(~String), List.reverse.go(&2, String, xs, acc)) : Q.Deque<String> & List<&2, String>}:
  A.unlimited_reuse(~String, xs, acc)

