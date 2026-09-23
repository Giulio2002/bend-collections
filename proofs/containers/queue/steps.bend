import Base
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../../lib/list.bend as LL
import ../../lib/spec_common.bend as SC
import ./spec.bend as S
import ../../../src/containers/queue.bend as Q
import ../../../src/containers/types/queue.bend as E
import ./state.bend as ST

# Every public queue operation, including the errors (dequeue/peek on an
# empty queue: Fail{EmptyQueue}, queue unchanged), refines the spec step.

def StepOK(~T: Data, sh: ST.Shadow<T>, op: E.Op<T>) -> Type:
  Sigma<&1, &1, ST.Shadow<T>, sh2 => Sigma<&1, &1, E.Obs<T>, o => {Q.step(~T, ST.real(T, sh), op) == (ST.real(T, sh2), o) : Q.Queue<T> & E.Obs<T>} & {(ST.model(T, sh2), o) == S.step(T, ST.model(T, sh), op) : List<&2, T> & E.Obs<T>}>>

def mk(~T: Data, -sh: ST.Shadow<T>, -op: E.Op<T>, sh2: ST.Shadow<T>, o: E.Obs<T>, e1: {Q.step(~T, ST.real(T, sh), op) == (ST.real(T, sh2), o) : Q.Queue<T> & E.Obs<T>}, e2: {(ST.model(T, sh2), o) == S.step(T, ST.model(T, sh), op) : List<&2, T> & E.Obs<T>}) -> StepOK(~T, sh, op):
  (sh2, (o, (e1, e2)))

# ---- ready: reverse the back into an empty front ----

def is_nil(-T: Data, xs: List<&2, T>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{h, t}:
      False{}

# the front can be read: nonempty, or the queue is empty
def rdy(-T: Data, sh: ST.Shadow<T>) -> Bool:
  match sh:
    case ST.Sh{Nil{}, b}:
      is_nil(T, b)
    case ST.Sh{Con{x, f}, b}:
      True{}

def rdy_nil_back(-T: Data, +m: List<&2, T>) -> {rdy(T, ST.Sh{m, Nil{}}) == True{} : Bool}:
  match m:
    case Nil{}:
      {==}
    case Con{x, t}:
      {==}

def Ready(~T: Data, sh: ST.Shadow<T>) -> Type:
  Sigma<&1, &1, ST.Shadow<T>, sh1 => {Q.ready(~T, ST.real(T, sh)) == ST.real(T, sh1) : Q.Queue<T>} & ({ST.model(T, sh1) == ST.model(T, sh) : List<&2, T>} & {rdy(T, sh1) == True{} : Bool})>

def ready(~T: Data, +sh: ST.Shadow<T>) -> Ready(~T, sh):
  match sh:
    case ST.Sh{Con{x, f}, b}:
      (ST.Sh{Con{x, f}, b}, ({==}, ({==}, {==})))
    case ST.Sh{Nil{}, +b}:
      +rb = SC.reverse(T, b)
      +en = Equal.sym(Nat, Nat.add(SC.length(T, rb), 0n), SC.length(T, b), Equal.trans(Nat, Nat.add(SC.length(T, rb), 0n), SC.length(T, rb), SC.length(T, b), N.add_zero(SC.length(T, rb)), LL.length_rev(T, b)))
      +e1 = Equal.cong(List<&2, T>, Q.Queue<T>, z => Q.QU{z, Nil{}, SC.length(T, b)}, List.reverse(&2, T, b), rb, LL.base_rev(T, b))
      +e2 = Equal.cong(Nat, Q.Queue<T>, z => Q.QU{rb, Nil{}, z}, SC.length(T, b), Nat.add(SC.length(T, rb), 0n), en)
      (ST.Sh{rb, Nil{}}, (Equal.trans(Q.Queue<T>, Q.QU{List.reverse(&2, T, b), Nil{}, SC.length(T, b)}, Q.QU{rb, Nil{}, SC.length(T, b)}, ST.real(T, ST.Sh{rb, Nil{}}), e1, e2), (LL.append_nil(T, rb), rdy_nil_back(T, rb))))

# ---- reading the front of a readied shadow ----

def Read(~T: Data, sh: ST.Shadow<T>, r: Q.Queue<T> & E.Obs<T>, spec: List<&2, T> & E.Obs<T>) -> Type:
  Sigma<&1, &1, ST.Shadow<T>, sh2 => Sigma<&1, &1, E.Obs<T>, o => {r == (ST.real(T, sh2), o) : Q.Queue<T> & E.Obs<T>} & {(ST.model(T, sh2), o) == spec : List<&2, T> & E.Obs<T>}>>

def dequeue_ready(~T: Data, +sh: ST.Shadow<T>, +hr: {rdy(T, sh) == True{} : Bool}) -> Read(~T, sh, Q.obs_item(~T, Q.dequeue_ready(~T, ST.real(T, sh))), S.dequeue(T, ST.model(T, sh))):
  match sh:
    case ST.Sh{Con{+x, +t}, +b}:
      +e = Equal.cong(Nat, Q.Queue<T>, z => Q.QU{t, b, z}, Nat.sub(Nat.add(SC.length(T, Con{x, t}), SC.length(T, b)), 1n), Nat.add(SC.length(T, t), SC.length(T, b)), N.sub_zero(Nat.add(SC.length(T, t), SC.length(T, b))))
      (ST.Sh{t, b}, (E.OItem{Done{x}}, (Equal.cong(Q.Queue<T>, Q.Queue<T> & E.Obs<T>, q => (q, E.OItem{Done{x}}), Q.QU{t, b, Nat.sub(Nat.add(SC.length(T, Con{x, t}), SC.length(T, b)), 1n)}, ST.real(T, ST.Sh{t, b}), e), {==})))
    case ST.Sh{Nil{}, Nil{}}:
      (ST.Sh{Nil{}, Nil{}}, (E.OItem{Fail{E.EmptyQueue{}}}, ({==}, {==})))
    case ST.Sh{Nil{}, Con{y, t}}:
      Empty.absurd(Read(~T, ST.Sh{Nil{}, Con{y, t}}, Q.obs_item(~T, Q.dequeue_ready(~T, ST.real(T, ST.Sh{Nil{}, Con{y, t}}))), S.dequeue(T, ST.model(T, ST.Sh{Nil{}, Con{y, t}}))), L.false_true(hr))

def peek_ready(~T: Data, +sh: ST.Shadow<T>, +hr: {rdy(T, sh) == True{} : Bool}) -> Read(~T, sh, Q.obs_item(~T, Q.peek_ready(~T, ST.real(T, sh))), (ST.model(T, sh), E.OItem{S.item(T, SC.head(T, ST.model(T, sh)))})):
  match sh:
    case ST.Sh{Con{x, t}, b}:
      (ST.Sh{Con{x, t}, b}, (E.OItem{Done{x}}, ({==}, {==})))
    case ST.Sh{Nil{}, Nil{}}:
      (ST.Sh{Nil{}, Nil{}}, (E.OItem{Fail{E.EmptyQueue{}}}, ({==}, {==})))
    case ST.Sh{Nil{}, Con{y, t}}:
      Empty.absurd(Read(~T, ST.Sh{Nil{}, Con{y, t}}, Q.obs_item(~T, Q.peek_ready(~T, ST.real(T, ST.Sh{Nil{}, Con{y, t}}))), (ST.model(T, ST.Sh{Nil{}, Con{y, t}}), E.OItem{S.item(T, SC.head(T, ST.model(T, ST.Sh{Nil{}, Con{y, t}})))})), L.false_true(hr))

def dq_fin(~T: Data, +sh: ST.Shadow<T>, +sh1: ST.Shadow<T>, +e: {Q.ready(~T, ST.real(T, sh)) == ST.real(T, sh1) : Q.Queue<T>}, +em: {ST.model(T, sh1) == ST.model(T, sh) : List<&2, T>}, rd: Read(~T, sh1, Q.obs_item(~T, Q.dequeue_ready(~T, ST.real(T, sh1))), S.dequeue(T, ST.model(T, sh1)))) -> StepOK(~T, sh, E.Dequeue{}):
  match rd:
    case Tuple{+sh2, Tuple{+o, Tuple{e1, e2}}}:
      mk(~T, sh, E.Dequeue{}, sh2, o,
        Equal.trans(Q.Queue<T> & E.Obs<T>, Q.obs_item(~T, Q.dequeue_ready(~T, Q.ready(~T, ST.real(T, sh)))), Q.obs_item(~T, Q.dequeue_ready(~T, ST.real(T, sh1))), (ST.real(T, sh2), o), Equal.cong(Q.Queue<T>, Q.Queue<T> & E.Obs<T>, d => Q.obs_item(~T, Q.dequeue_ready(~T, d)), Q.ready(~T, ST.real(T, sh)), ST.real(T, sh1), e), e1),
        Equal.trans(List<&2, T> & E.Obs<T>, (ST.model(T, sh2), o), S.dequeue(T, ST.model(T, sh1)), S.dequeue(T, ST.model(T, sh)), e2, Equal.cong(List<&2, T>, List<&2, T> & E.Obs<T>, z => S.dequeue(T, z), ST.model(T, sh1), ST.model(T, sh), em)))

def dq_rd(~T: Data, +sh: ST.Shadow<T>, r: Ready(~T, sh)) -> StepOK(~T, sh, E.Dequeue{}):
  match r:
    case Tuple{+sh1, Tuple{e, Tuple{em, hr}}}:
      dq_fin(~T, sh, sh1, e, em, dequeue_ready(~T, sh1, hr))

def pk_fin(~T: Data, +sh: ST.Shadow<T>, +sh1: ST.Shadow<T>, +e: {Q.ready(~T, ST.real(T, sh)) == ST.real(T, sh1) : Q.Queue<T>}, +em: {ST.model(T, sh1) == ST.model(T, sh) : List<&2, T>}, rd: Read(~T, sh1, Q.obs_item(~T, Q.peek_ready(~T, ST.real(T, sh1))), (ST.model(T, sh1), E.OItem{S.item(T, SC.head(T, ST.model(T, sh1)))}))) -> StepOK(~T, sh, E.Peek{}):
  match rd:
    case Tuple{+sh2, Tuple{+o, Tuple{e1, e2}}}:
      mk(~T, sh, E.Peek{}, sh2, o,
        Equal.trans(Q.Queue<T> & E.Obs<T>, Q.obs_item(~T, Q.peek_ready(~T, Q.ready(~T, ST.real(T, sh)))), Q.obs_item(~T, Q.peek_ready(~T, ST.real(T, sh1))), (ST.real(T, sh2), o), Equal.cong(Q.Queue<T>, Q.Queue<T> & E.Obs<T>, d => Q.obs_item(~T, Q.peek_ready(~T, d)), Q.ready(~T, ST.real(T, sh)), ST.real(T, sh1), e), e1),
        Equal.trans(List<&2, T> & E.Obs<T>, (ST.model(T, sh2), o), (ST.model(T, sh1), E.OItem{S.item(T, SC.head(T, ST.model(T, sh1)))}), (ST.model(T, sh), E.OItem{S.item(T, SC.head(T, ST.model(T, sh)))}), e2, Equal.cong(List<&2, T>, List<&2, T> & E.Obs<T>, z => (z, E.OItem{S.item(T, SC.head(T, z))}), ST.model(T, sh1), ST.model(T, sh), em)))

def pk_rd(~T: Data, +sh: ST.Shadow<T>, r: Ready(~T, sh)) -> StepOK(~T, sh, E.Peek{}):
  match r:
    case Tuple{+sh1, Tuple{e, Tuple{em, hr}}}:
      pk_fin(~T, sh, sh1, e, em, peek_ready(~T, sh1, hr))

# ---- each operation ----

def op_length(~T: Data, +sh: ST.Shadow<T>) -> StepOK(~T, sh, E.Length{}):
  match sh:
    case ST.Sh{+f, +b}:
      +n = Nat.add(SC.length(T, f), SC.length(T, b))
      +el = Equal.trans(Nat, n, Nat.add(SC.length(T, f), SC.length(T, SC.reverse(T, b))), SC.length(T, SC.append(T, f, SC.reverse(T, b))), Equal.cong(Nat, Nat, z => Nat.add(SC.length(T, f), z), SC.length(T, b), SC.length(T, SC.reverse(T, b)), Equal.sym(Nat, SC.length(T, SC.reverse(T, b)), SC.length(T, b), LL.length_rev(T, b))), Equal.sym(Nat, SC.length(T, SC.append(T, f, SC.reverse(T, b))), Nat.add(SC.length(T, f), SC.length(T, SC.reverse(T, b))), LL.length_append(T, f, SC.reverse(T, b))))
      mk(~T, ST.Sh{f, b}, E.Length{}, ST.Sh{f, b}, E.ONat{n}, {==}, Equal.cong(Nat, List<&2, T> & E.Obs<T>, z => (ST.model(T, ST.Sh{f, b}), E.ONat{z}), n, SC.length(T, ST.model(T, ST.Sh{f, b})), el))

def op_enqueue(~T: Data, +sh: ST.Shadow<T>, +x: T) -> StepOK(~T, sh, E.Enqueue{x}):
  match sh:
    case ST.Sh{+f, +b}:
      +en = Equal.sym(Nat, Nat.add(SC.length(T, f), 1n+SC.length(T, b)), 1n+Nat.add(SC.length(T, f), SC.length(T, b)), N.add_succ(SC.length(T, f), SC.length(T, b)))
      +e1 = Equal.cong(Nat, Q.Queue<T> & E.Obs<T>, z => (Q.QU{f, Con{x, b}, z}, E.OUnit{}), 1n+Nat.add(SC.length(T, f), SC.length(T, b)), Nat.add(SC.length(T, f), 1n+SC.length(T, b)), en)
      mk(~T, ST.Sh{f, b}, E.Enqueue{x}, ST.Sh{f, Con{x, b}}, E.OUnit{}, e1, Equal.cong(List<&2, T>, List<&2, T> & E.Obs<T>, z => (z, E.OUnit{}), ST.model(T, ST.Sh{f, Con{x, b}}), SC.snoc(T, ST.model(T, ST.Sh{f, b}), x), LL.append_snoc(T, f, SC.reverse(T, b), x)))

def op_to_list(~T: Data, +sh: ST.Shadow<T>) -> StepOK(~T, sh, E.ToList{}):
  match sh:
    case ST.Sh{+f, +b}:
      +el = Equal.trans(List<&2, T>, List.append(&2, T, f, List.reverse(&2, T, b)), List.append(&2, T, f, SC.reverse(T, b)), SC.append(T, f, SC.reverse(T, b)), Equal.cong(List<&2, T>, List<&2, T>, z => List.append(&2, T, f, z), List.reverse(&2, T, b), SC.reverse(T, b), LL.base_rev(T, b)), LL.base_append(T, f, SC.reverse(T, b)))
      mk(~T, ST.Sh{f, b}, E.ToList{}, ST.Sh{f, b}, E.OList{List.append(&2, T, f, List.reverse(&2, T, b))}, {==}, Equal.cong(List<&2, T>, List<&2, T> & E.Obs<T>, z => (ST.model(T, ST.Sh{f, b}), E.OList{z}), List.append(&2, T, f, List.reverse(&2, T, b)), ST.model(T, ST.Sh{f, b}), el))

# every public operation refines the spec step
def step_ok(~T: Data, +sh: ST.Shadow<T>, +op: E.Op<T>) -> StepOK(~T, sh, op):
  match op:
    case E.Length{}:
      op_length(~T, sh)
    case E.Enqueue{+x}:
      op_enqueue(~T, sh, x)
    case E.Dequeue{}:
      dq_rd(~T, sh, ready(~T, sh))
    case E.Peek{}:
      pk_rd(~T, sh, ready(~T, sh))
    case E.ToList{}:
      op_to_list(~T, sh)
