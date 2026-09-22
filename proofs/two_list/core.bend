import Base
import ../lib/list.bend as LL
import ../lib/nat.bend as N
import ../spec/common.bend as S
import ../../src/containers/deque.bend as D
import ../../src/containers/queue.bend as Q
import ../../src/containers/types/deque.bend as DE
import ../../src/containers/types/queue.bend as QE

# Component laws tied to the real two-list implementation. These do not
# replace universal public-operation trace refinement or a cost proof.
def base_append(-T: Data, +xs: List<&2, T>, +ys: List<&2, T>) -> {List.append(&2, T, xs, ys) == S.append(T, xs, ys) : List<&2, T>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +tail}:
      LL.cons_cong(T, x, List.append(&2, T, tail, ys), S.append(T, tail, ys), base_append(T, tail, ys))

def contents(-T: Data, f: List<&2, T>, b: List<&2, T>) -> List<&2, T>:
  S.append(T, f, S.reverse(T, b))

def materialize(-T: Data, +f: List<&2, T>, +b: List<&2, T>) -> {List.append(&2, T, f, List.reverse(&2, T, b)) == contents(T, f, b) : List<&2, T>}:
  Equal.trans(List<&2, T>, List.append(&2, T, f, List.reverse(&2, T, b)), S.append(T, f, List.reverse(&2, T, b)), contents(T, f, b), base_append(T, f, List.reverse(&2, T, b)), Equal.cong(List<&2, T>, List<&2, T>, xs => S.append(T, f, xs), List.reverse(&2, T, b), S.reverse(T, b), LL.base_rev(T, b)))

def reconstruct(-T: Data, r: List<&2, T> & List<&2, T>) -> List<&2, T>:
  (keep, moved) = r
  S.append(T, keep, List.reverse(&2, T, moved))

def reconstruct_cons(~T: Data, +x: T, r: List<&2, T> & List<&2, T>) -> {reconstruct(T, D.split_cons(~T, x, r)) == Con{x, reconstruct(T, r)} : List<&2, T>}:
  match r:
    case Tuple{keep, moved}:
      {==}

# No values lost, duplicated or reordered by the actual split, for EVERY
# split size and list (not merely concrete examples or balanced inputs).
def split_preserves(~T: Data, +n: Nat, +xs: List<&2, T>) -> {reconstruct(T, D.split(~T, n, xs)) == xs : List<&2, T>}:
  match n xs:
    case 0n +ys:
      LL.rev_rev(T, ys)
    case 1n+p Nil{}:
      {==}
    case 1n+p Con{+x, +tail}:
      Equal.trans(List<&2, T>, reconstruct(T, D.split_cons(~T, x, D.split(~T, p, tail))), Con{x, reconstruct(T, D.split(~T, p, tail))}, Con{x, tail}, reconstruct_cons(~T, x, D.split(~T, p, tail)), LL.cons_cong(T, x, reconstruct(T, D.split(~T, p, tail)), tail, split_preserves(~T, p, tail)))

def deque_to_list(~T: Data, +f: List<&2, T>, +b: List<&2, T>, +nf: Nat, +nb: Nat) -> {D.to_list(~T, D.DE{f, b, nf, nb}) == (D.DE{f, b, nf, nb}, contents(T, f, b)) : D.Deque<T> & List<&2, T>}:
  Equal.cong(List<&2, T>, D.Deque<T> & List<&2, T>, xs => (D.DE{f, b, nf, nb}, xs), List.append(&2, T, f, List.reverse(&2, T, b)), contents(T, f, b), materialize(T, f, b))

def queue_to_list(~T: Data, +f: List<&2, T>, +b: List<&2, T>, +n: Nat) -> {Q.to_list(~T, Q.QU{f, b, n}) == (Q.QU{f, b, n}, contents(T, f, b)) : Q.Queue<T> & List<&2, T>}:
  Equal.cong(List<&2, T>, Q.Queue<T> & List<&2, T>, xs => (Q.QU{f, b, n}, xs), List.append(&2, T, f, List.reverse(&2, T, b)), contents(T, f, b), materialize(T, f, b))

def front_roundtrip(~T: Data, +f: List<&2, T>, +b: List<&2, T>, +nf: Nat, +nb: Nat, +x: T) -> {D.pop_front(~T, D.push_front(~T, D.DE{f, b, nf, nb}, x)) == (D.DE{f, b, nf, nb}, Done{x}) : D.Deque<T> & Result<&2, &2, DE.Error, T>}:
  Equal.cong(Nat, D.Deque<T> & Result<&2, &2, DE.Error, T>, n => (D.DE{f, b, n, nb}, Done{x}), Nat.sub(nf, 0n), nf, N.sub_zero(nf))

def back_roundtrip(~T: Data, +f: List<&2, T>, +b: List<&2, T>, +nf: Nat, +nb: Nat, +x: T) -> {D.pop_back(~T, D.push_back(~T, D.DE{f, b, nf, nb}, x)) == (D.DE{f, b, nf, nb}, Done{x}) : D.Deque<T> & Result<&2, &2, DE.Error, T>}:
  Equal.cong(Nat, D.Deque<T> & Result<&2, &2, DE.Error, T>, n => (D.DE{f, b, nf, n}, Done{x}), Nat.sub(nb, 0n), nb, N.sub_zero(nb))

def queue_singleton(~T: Data, +x: T) -> {Q.dequeue(~T, Q.enqueue(~T, Q.new(~T), x)) == (Q.new(~T), Done{x}) : Q.Queue<T> & Result<&2, &2, QE.Error, T>}:
  {==}

def deque_empty_front(~T: Data) -> {D.pop_front(~T, D.new(~T)) == (D.new(~T), Fail{DE.EmptyDeque{}}) : D.Deque<T> & Result<&2, &2, DE.Error, T>}:
  {==}

def deque_empty_back(~T: Data) -> {D.pop_back(~T, D.new(~T)) == (D.new(~T), Fail{DE.EmptyDeque{}}) : D.Deque<T> & Result<&2, &2, DE.Error, T>}:
  {==}

def queue_empty(~T: Data) -> {Q.dequeue(~T, Q.new(~T)) == (Q.new(~T), Fail{QE.EmptyQueue{}}) : Q.Queue<T> & Result<&2, &2, QE.Error, T>}:
  {==}

# Observable sequence abstraction, independent of the operation code.
def deque_view(~T: Data, d: D.Deque<T>) -> List<&2, T>:
  D.DE{f, b, nf, nb} = d
  contents(T, f, b)

def queue_view(~T: Data, q: Q.Queue<T>) -> List<&2, T>:
  Q.QU{f, b, n} = q
  contents(T, f, b)

def push_front_order(~T: Data, +f: List<&2, T>, +b: List<&2, T>, +nf: Nat, +nb: Nat, +x: T) -> {deque_view(~T, D.push_front(~T, D.DE{f, b, nf, nb}, x)) == Con{x, contents(T, f, b)} : List<&2, T>}:
  {==}

def push_back_order(~T: Data, +f: List<&2, T>, +b: List<&2, T>, +nf: Nat, +nb: Nat, +x: T) -> {deque_view(~T, D.push_back(~T, D.DE{f, b, nf, nb}, x)) == S.snoc(T, contents(T, f, b), x) : List<&2, T>}:
  LL.append_snoc(T, f, S.reverse(T, b), x)

def enqueue_order(~T: Data, +f: List<&2, T>, +b: List<&2, T>, +n: Nat, +x: T) -> {queue_view(~T, Q.enqueue(~T, Q.QU{f, b, n}, x)) == S.snoc(T, contents(T, f, b), x) : List<&2, T>}:
  LL.append_snoc(T, f, S.reverse(T, b), x)

def queue_ready_order(~T: Data, +b: List<&2, T>, +n: Nat) -> {queue_view(~T, Q.ready(~T, Q.QU{Nil{}, b, n})) == S.reverse(T, b) : List<&2, T>}:
  Equal.trans(List<&2, T>, S.append(T, List.reverse(&2, T, b), Nil{}), List.reverse(&2, T, b), S.reverse(T, b), LL.append_nil(T, List.reverse(&2, T, b)), LL.base_rev(T, b))
