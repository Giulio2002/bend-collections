import Base
import ./core.bend as P
import ../spec/common.bend as S
import ../../src/containers/deque.bend as D
import ../../src/containers/queue.bend as Q
import ../../src/containers/types/deque.bend as DE
import ../../src/containers/types/queue.bend as QE

def reconstruct_cons_u32(+x: U32, r: List<&2, U32> & List<&2, U32>) -> {P.reconstruct(U32, D.split_cons(~U32, x, r)) == Con{x, P.reconstruct(U32, r)} : List<&2, U32>}:
  P.reconstruct_cons(~U32, x, r)

def reconstruct_cons_string(+x: String, r: List<&2, String> & List<&2, String>) -> {P.reconstruct(String, D.split_cons(~String, x, r)) == Con{x, P.reconstruct(String, r)} : List<&2, String>}:
  P.reconstruct_cons(~String, x, r)

def split_preserves_u32(+n: Nat, +xs: List<&2, U32>) -> {P.reconstruct(U32, D.split(~U32, n, xs)) == xs : List<&2, U32>}:
  P.split_preserves(~U32, n, xs)

def split_preserves_string(+n: Nat, +xs: List<&2, String>) -> {P.reconstruct(String, D.split(~String, n, xs)) == xs : List<&2, String>}:
  P.split_preserves(~String, n, xs)

def deque_to_list_u32(+f: List<&2, U32>, +b: List<&2, U32>, +nf: Nat, +nb: Nat) -> {D.to_list(~U32, D.DE{f, b, nf, nb}) == (D.DE{f, b, nf, nb}, P.contents(U32, f, b)) : D.Deque<U32> & List<&2, U32>}:
  P.deque_to_list(~U32, f, b, nf, nb)

def deque_to_list_string(+f: List<&2, String>, +b: List<&2, String>, +nf: Nat, +nb: Nat) -> {D.to_list(~String, D.DE{f, b, nf, nb}) == (D.DE{f, b, nf, nb}, P.contents(String, f, b)) : D.Deque<String> & List<&2, String>}:
  P.deque_to_list(~String, f, b, nf, nb)

def queue_to_list_u32(+f: List<&2, U32>, +b: List<&2, U32>, +n: Nat) -> {Q.to_list(~U32, Q.QU{f, b, n}) == (Q.QU{f, b, n}, P.contents(U32, f, b)) : Q.Queue<U32> & List<&2, U32>}:
  P.queue_to_list(~U32, f, b, n)

def queue_to_list_string(+f: List<&2, String>, +b: List<&2, String>, +n: Nat) -> {Q.to_list(~String, Q.QU{f, b, n}) == (Q.QU{f, b, n}, P.contents(String, f, b)) : Q.Queue<String> & List<&2, String>}:
  P.queue_to_list(~String, f, b, n)

def front_roundtrip_u32(+f: List<&2, U32>, +b: List<&2, U32>, +nf: Nat, +nb: Nat, +x: U32) -> {D.pop_front(~U32, D.push_front(~U32, D.DE{f, b, nf, nb}, x)) == (D.DE{f, b, nf, nb}, Done{x}) : D.Deque<U32> & Result<&2, &2, DE.Error, U32>}:
  P.front_roundtrip(~U32, f, b, nf, nb, x)

def front_roundtrip_string(+f: List<&2, String>, +b: List<&2, String>, +nf: Nat, +nb: Nat, +x: String) -> {D.pop_front(~String, D.push_front(~String, D.DE{f, b, nf, nb}, x)) == (D.DE{f, b, nf, nb}, Done{x}) : D.Deque<String> & Result<&2, &2, DE.Error, String>}:
  P.front_roundtrip(~String, f, b, nf, nb, x)

def back_roundtrip_u32(+f: List<&2, U32>, +b: List<&2, U32>, +nf: Nat, +nb: Nat, +x: U32) -> {D.pop_back(~U32, D.push_back(~U32, D.DE{f, b, nf, nb}, x)) == (D.DE{f, b, nf, nb}, Done{x}) : D.Deque<U32> & Result<&2, &2, DE.Error, U32>}:
  P.back_roundtrip(~U32, f, b, nf, nb, x)

def back_roundtrip_string(+f: List<&2, String>, +b: List<&2, String>, +nf: Nat, +nb: Nat, +x: String) -> {D.pop_back(~String, D.push_back(~String, D.DE{f, b, nf, nb}, x)) == (D.DE{f, b, nf, nb}, Done{x}) : D.Deque<String> & Result<&2, &2, DE.Error, String>}:
  P.back_roundtrip(~String, f, b, nf, nb, x)

def queue_singleton_u32(+x: U32) -> {Q.dequeue(~U32, Q.enqueue(~U32, Q.new(~U32), x)) == (Q.new(~U32), Done{x}) : Q.Queue<U32> & Result<&2, &2, QE.Error, U32>}:
  P.queue_singleton(~U32, x)

def queue_singleton_string(+x: String) -> {Q.dequeue(~String, Q.enqueue(~String, Q.new(~String), x)) == (Q.new(~String), Done{x}) : Q.Queue<String> & Result<&2, &2, QE.Error, String>}:
  P.queue_singleton(~String, x)

def deque_empty_front_u32() -> {D.pop_front(~U32, D.new(~U32)) == (D.new(~U32), Fail{DE.EmptyDeque{}}) : D.Deque<U32> & Result<&2, &2, DE.Error, U32>}:
  P.deque_empty_front(~U32)

def deque_empty_front_string() -> {D.pop_front(~String, D.new(~String)) == (D.new(~String), Fail{DE.EmptyDeque{}}) : D.Deque<String> & Result<&2, &2, DE.Error, String>}:
  P.deque_empty_front(~String)

def deque_empty_back_u32() -> {D.pop_back(~U32, D.new(~U32)) == (D.new(~U32), Fail{DE.EmptyDeque{}}) : D.Deque<U32> & Result<&2, &2, DE.Error, U32>}:
  P.deque_empty_back(~U32)

def deque_empty_back_string() -> {D.pop_back(~String, D.new(~String)) == (D.new(~String), Fail{DE.EmptyDeque{}}) : D.Deque<String> & Result<&2, &2, DE.Error, String>}:
  P.deque_empty_back(~String)

def queue_empty_u32() -> {Q.dequeue(~U32, Q.new(~U32)) == (Q.new(~U32), Fail{QE.EmptyQueue{}}) : Q.Queue<U32> & Result<&2, &2, QE.Error, U32>}:
  P.queue_empty(~U32)

def queue_empty_string() -> {Q.dequeue(~String, Q.new(~String)) == (Q.new(~String), Fail{QE.EmptyQueue{}}) : Q.Queue<String> & Result<&2, &2, QE.Error, String>}:
  P.queue_empty(~String)

def push_front_order_u32(+f: List<&2, U32>, +b: List<&2, U32>, +nf: Nat, +nb: Nat, +x: U32) -> {P.deque_view(~U32, D.push_front(~U32, D.DE{f, b, nf, nb}, x)) == Con{x, P.contents(U32, f, b)} : List<&2, U32>}:
  P.push_front_order(~U32, f, b, nf, nb, x)

def push_front_order_string(+f: List<&2, String>, +b: List<&2, String>, +nf: Nat, +nb: Nat, +x: String) -> {P.deque_view(~String, D.push_front(~String, D.DE{f, b, nf, nb}, x)) == Con{x, P.contents(String, f, b)} : List<&2, String>}:
  P.push_front_order(~String, f, b, nf, nb, x)

def push_back_order_u32(+f: List<&2, U32>, +b: List<&2, U32>, +nf: Nat, +nb: Nat, +x: U32) -> {P.deque_view(~U32, D.push_back(~U32, D.DE{f, b, nf, nb}, x)) == S.snoc(U32, P.contents(U32, f, b), x) : List<&2, U32>}:
  P.push_back_order(~U32, f, b, nf, nb, x)

def push_back_order_string(+f: List<&2, String>, +b: List<&2, String>, +nf: Nat, +nb: Nat, +x: String) -> {P.deque_view(~String, D.push_back(~String, D.DE{f, b, nf, nb}, x)) == S.snoc(String, P.contents(String, f, b), x) : List<&2, String>}:
  P.push_back_order(~String, f, b, nf, nb, x)

def enqueue_order_u32(+f: List<&2, U32>, +b: List<&2, U32>, +n: Nat, +x: U32) -> {P.queue_view(~U32, Q.enqueue(~U32, Q.QU{f, b, n}, x)) == S.snoc(U32, P.contents(U32, f, b), x) : List<&2, U32>}:
  P.enqueue_order(~U32, f, b, n, x)

def enqueue_order_string(+f: List<&2, String>, +b: List<&2, String>, +n: Nat, +x: String) -> {P.queue_view(~String, Q.enqueue(~String, Q.QU{f, b, n}, x)) == S.snoc(String, P.contents(String, f, b), x) : List<&2, String>}:
  P.enqueue_order(~String, f, b, n, x)

def queue_ready_order_u32(+b: List<&2, U32>, +n: Nat) -> {P.queue_view(~U32, Q.ready(~U32, Q.QU{Nil{}, b, n})) == S.reverse(U32, b) : List<&2, U32>}:
  P.queue_ready_order(~U32, b, n)

def queue_ready_order_string(+b: List<&2, String>, +n: Nat) -> {P.queue_view(~String, Q.ready(~String, Q.QU{Nil{}, b, n})) == S.reverse(String, b) : List<&2, String>}:
  P.queue_ready_order(~String, b, n)

