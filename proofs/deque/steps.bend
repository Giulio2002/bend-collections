import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../spec/common.bend as SC
import ../spec/deque.bend as S
import ../../src/containers/deque.bend as DQ
import ../../src/containers/types/deque.bend as E
import ./state.bend as ST
import ./stepok.bend as K
import ./rebalance.bend as RB

# Every public deque operation, including the errors (pop/peek on an empty
# deque: Fail{EmptyDeque}, deque unchanged), refines the spec step.

# the result of reading one end of a readied shadow
def Read(~T: Data, sh: ST.Shadow<T>, r: DQ.Deque<T> & E.Obs<T>, spec: List<&2, T> & E.Obs<T>) -> Type:
  Sigma<&1, &1, ST.Shadow<T>, sh2 => Sigma<&1, &1, E.Obs<T>, o => {r == (ST.real(T, sh2), o) : DQ.Deque<T> & E.Obs<T>} & {(ST.model(T, sh2), o) == spec : List<&2, T> & E.Obs<T>}>>

def pred1(-T: Data, +x: T, +t: List<&2, T>, +b: List<&2, T>) -> {DQ.DE{t, b, Nat.sub(SC.length(T, Con{x, t}), 1n), SC.length(T, b)} == ST.real(T, ST.Sh{t, b}) : DQ.Deque<T>}:
  Equal.cong(Nat, DQ.Deque<T>, z => DQ.DE{t, b, z, SC.length(T, b)}, Nat.sub(1n+SC.length(T, t), 1n), SC.length(T, t), N.sub_zero(SC.length(T, t)))

def pred1b(-T: Data, +f: List<&2, T>, +x: T, +t: List<&2, T>) -> {DQ.DE{f, t, SC.length(T, f), Nat.sub(SC.length(T, Con{x, t}), 1n)} == ST.real(T, ST.Sh{f, t}) : DQ.Deque<T>}:
  Equal.cong(Nat, DQ.Deque<T>, z => DQ.DE{f, t, SC.length(T, f), z}, Nat.sub(1n+SC.length(T, t), 1n), SC.length(T, t), N.sub_zero(SC.length(T, t)))

# the model with a nonempty back ends in the back's head
def model_back(-T: Data, +f: List<&2, T>, +x: T, +t: List<&2, T>) -> {ST.model(T, ST.Sh{f, Con{x, t}}) == SC.snoc(T, ST.model(T, ST.Sh{f, t}), x) : List<&2, T>}:
  LL.append_snoc(T, f, SC.reverse(T, t), x)

def pop_back_snoc(-T: Data, +ys: List<&2, T>, +x: T) -> {S.pop_back(T, SC.snoc(T, ys, x)) == (ys, E.OItem{Done{x}}) : List<&2, T> & E.Obs<T>}:
  match ys:
    case Nil{}:
      {==}
    case Con{h, t}:
      %LL.init_snoc(T, Con{h, t}, x) : {S.pop_back(T, SC.snoc(T, Con{h, t}, x)) == (_, E.OItem{Done{x}}) : List<&2, T> & E.Obs<T>}
      %LL.last_snoc(T, Con{h, t}, x) : {S.pop_back(T, SC.snoc(T, Con{h, t}, x)) == (SC.init(T, SC.snoc(T, Con{h, t}, x)), E.OItem{S.item(T, _)}) : List<&2, T> & E.Obs<T>}
      {==}

def pop_front_ready(~T: Data, +sh: ST.Shadow<T>, +hr: {RB.rdy_f(T, sh) == True{} : Bool}) -> Read(~T, sh, DQ.obs_item(~T, DQ.pop_front_ready(~T, ST.real(T, sh))), S.pop_front(T, ST.model(T, sh))):
  match sh:
    case ST.Sh{Con{x, t}, b}:
      (ST.Sh{t, b}, (E.OItem{Done{x}}, (Equal.cong(DQ.Deque<T>, DQ.Deque<T> & E.Obs<T>, d => (d, E.OItem{Done{x}}), DQ.DE{t, b, Nat.sub(SC.length(T, Con{x, t}), 1n), SC.length(T, b)}, ST.real(T, ST.Sh{t, b}), pred1(T, x, t, b)), {==})))
    case ST.Sh{Nil{}, Nil{}}:
      (ST.Sh{Nil{}, Nil{}}, (E.OItem{Fail{E.EmptyDeque{}}}, ({==}, {==})))
    case ST.Sh{Nil{}, Con{y, t}}:
      Empty.absurd(Read(~T, ST.Sh{Nil{}, Con{y, t}}, DQ.obs_item(~T, DQ.pop_front_ready(~T, ST.real(T, ST.Sh{Nil{}, Con{y, t}}))), S.pop_front(T, ST.model(T, ST.Sh{Nil{}, Con{y, t}}))), L.false_true(hr))

def peek_front_ready(~T: Data, +sh: ST.Shadow<T>, +hr: {RB.rdy_f(T, sh) == True{} : Bool}) -> Read(~T, sh, DQ.obs_item(~T, DQ.peek_front_ready(~T, ST.real(T, sh))), (ST.model(T, sh), E.OItem{S.item(T, SC.head(T, ST.model(T, sh)))})):
  match sh:
    case ST.Sh{Con{x, t}, b}:
      (ST.Sh{Con{x, t}, b}, (E.OItem{Done{x}}, ({==}, {==})))
    case ST.Sh{Nil{}, Nil{}}:
      (ST.Sh{Nil{}, Nil{}}, (E.OItem{Fail{E.EmptyDeque{}}}, ({==}, {==})))
    case ST.Sh{Nil{}, Con{y, t}}:
      Empty.absurd(Read(~T, ST.Sh{Nil{}, Con{y, t}}, DQ.obs_item(~T, DQ.peek_front_ready(~T, ST.real(T, ST.Sh{Nil{}, Con{y, t}}))), (ST.model(T, ST.Sh{Nil{}, Con{y, t}}), E.OItem{S.item(T, SC.head(T, ST.model(T, ST.Sh{Nil{}, Con{y, t}})))})), L.false_true(hr))

def pop_back_ready(~T: Data, +sh: ST.Shadow<T>, +hr: {RB.rdy_b(T, sh) == True{} : Bool}) -> Read(~T, sh, DQ.obs_item(~T, DQ.pop_back_ready(~T, ST.real(T, sh))), S.pop_back(T, ST.model(T, sh))):
  match sh:
    case ST.Sh{f, Con{x, t}}:
      +sp = Equal.trans(List<&2, T> & E.Obs<T>, (ST.model(T, ST.Sh{f, t}), E.OItem{Done{x}}), S.pop_back(T, SC.snoc(T, ST.model(T, ST.Sh{f, t}), x)), S.pop_back(T, ST.model(T, ST.Sh{f, Con{x, t}})),
        Equal.sym(List<&2, T> & E.Obs<T>, S.pop_back(T, SC.snoc(T, ST.model(T, ST.Sh{f, t}), x)), (ST.model(T, ST.Sh{f, t}), E.OItem{Done{x}}), pop_back_snoc(T, ST.model(T, ST.Sh{f, t}), x)),
        Equal.cong(List<&2, T>, List<&2, T> & E.Obs<T>, z => S.pop_back(T, z), SC.snoc(T, ST.model(T, ST.Sh{f, t}), x), ST.model(T, ST.Sh{f, Con{x, t}}), Equal.sym(List<&2, T>, ST.model(T, ST.Sh{f, Con{x, t}}), SC.snoc(T, ST.model(T, ST.Sh{f, t}), x), model_back(T, f, x, t))))
      (ST.Sh{f, t}, (E.OItem{Done{x}}, (Equal.cong(DQ.Deque<T>, DQ.Deque<T> & E.Obs<T>, d => (d, E.OItem{Done{x}}), DQ.DE{f, t, SC.length(T, f), Nat.sub(SC.length(T, Con{x, t}), 1n)}, ST.real(T, ST.Sh{f, t}), pred1b(T, f, x, t)), sp)))
    case ST.Sh{Nil{}, Nil{}}:
      (ST.Sh{Nil{}, Nil{}}, (E.OItem{Fail{E.EmptyDeque{}}}, ({==}, {==})))
    case ST.Sh{Con{y, t}, Nil{}}:
      Empty.absurd(Read(~T, ST.Sh{Con{y, t}, Nil{}}, DQ.obs_item(~T, DQ.pop_back_ready(~T, ST.real(T, ST.Sh{Con{y, t}, Nil{}}))), S.pop_back(T, ST.model(T, ST.Sh{Con{y, t}, Nil{}}))), L.false_true(hr))

def peek_back_ready(~T: Data, +sh: ST.Shadow<T>, +hr: {RB.rdy_b(T, sh) == True{} : Bool}) -> Read(~T, sh, DQ.obs_item(~T, DQ.peek_back_ready(~T, ST.real(T, sh))), (ST.model(T, sh), E.OItem{S.item(T, SC.last(T, ST.model(T, sh)))})):
  match sh:
    case ST.Sh{f, Con{x, t}}:
      +sp = Equal.cong(List<&2, T>, List<&2, T> & E.Obs<T>, z => (z, E.OItem{S.item(T, SC.last(T, z))}), SC.snoc(T, ST.model(T, ST.Sh{f, t}), x), ST.model(T, ST.Sh{f, Con{x, t}}), Equal.sym(List<&2, T>, ST.model(T, ST.Sh{f, Con{x, t}}), SC.snoc(T, ST.model(T, ST.Sh{f, t}), x), model_back(T, f, x, t)))
      +lx = Equal.cong(Maybe<&2, T>, List<&2, T> & E.Obs<T>, m => (ST.model(T, ST.Sh{f, Con{x, t}}), E.OItem{S.item(T, m)}), Some{x}, SC.last(T, SC.snoc(T, ST.model(T, ST.Sh{f, t}), x)), Equal.sym(Maybe<&2, T>, SC.last(T, SC.snoc(T, ST.model(T, ST.Sh{f, t}), x)), Some{x}, LL.last_snoc(T, ST.model(T, ST.Sh{f, t}), x)))
      (ST.Sh{f, Con{x, t}}, (E.OItem{Done{x}}, ({==}, Equal.trans(List<&2, T> & E.Obs<T>, (ST.model(T, ST.Sh{f, Con{x, t}}), E.OItem{Done{x}}), (ST.model(T, ST.Sh{f, Con{x, t}}), E.OItem{S.item(T, SC.last(T, SC.snoc(T, ST.model(T, ST.Sh{f, t}), x)))}), (ST.model(T, ST.Sh{f, Con{x, t}}), E.OItem{S.item(T, SC.last(T, ST.model(T, ST.Sh{f, Con{x, t}})))}), lx,
        Equal.cong(List<&2, T>, List<&2, T> & E.Obs<T>, z => (ST.model(T, ST.Sh{f, Con{x, t}}), E.OItem{S.item(T, SC.last(T, z))}), SC.snoc(T, ST.model(T, ST.Sh{f, t}), x), ST.model(T, ST.Sh{f, Con{x, t}}), Equal.sym(List<&2, T>, ST.model(T, ST.Sh{f, Con{x, t}}), SC.snoc(T, ST.model(T, ST.Sh{f, t}), x), model_back(T, f, x, t)))))))
    case ST.Sh{Nil{}, Nil{}}:
      (ST.Sh{Nil{}, Nil{}}, (E.OItem{Fail{E.EmptyDeque{}}}, ({==}, {==})))
    case ST.Sh{Con{y, t}, Nil{}}:
      Empty.absurd(Read(~T, ST.Sh{Con{y, t}, Nil{}}, DQ.obs_item(~T, DQ.peek_back_ready(~T, ST.real(T, ST.Sh{Con{y, t}, Nil{}}))), (ST.model(T, ST.Sh{Con{y, t}, Nil{}}), E.OItem{S.item(T, SC.last(T, ST.model(T, ST.Sh{Con{y, t}, Nil{}})))})), L.false_true(hr))

# ---- each operation ----

def op_length(~T: Data, +sh: ST.Shadow<T>) -> K.StepOK(~T, sh, E.Length{}):
  match sh:
    case ST.Sh{+f, +b}:
      +n = Nat.add(SC.length(T, f), SC.length(T, b))
      +el = Equal.trans(Nat, n, Nat.add(SC.length(T, f), SC.length(T, SC.reverse(T, b))), SC.length(T, SC.append(T, f, SC.reverse(T, b))), Equal.cong(Nat, Nat, z => Nat.add(SC.length(T, f), z), SC.length(T, b), SC.length(T, SC.reverse(T, b)), Equal.sym(Nat, SC.length(T, SC.reverse(T, b)), SC.length(T, b), LL.length_rev(T, b))), Equal.sym(Nat, SC.length(T, SC.append(T, f, SC.reverse(T, b))), Nat.add(SC.length(T, f), SC.length(T, SC.reverse(T, b))), LL.length_append(T, f, SC.reverse(T, b))))
      K.mk(~T, ST.Sh{f, b}, E.Length{}, ST.Sh{f, b}, E.ONat{n}, {==}, Equal.cong(Nat, List<&2, T> & E.Obs<T>, z => (ST.model(T, ST.Sh{f, b}), E.ONat{z}), n, SC.length(T, ST.model(T, ST.Sh{f, b})), el))

def op_push_front(~T: Data, +sh: ST.Shadow<T>, +x: T) -> K.StepOK(~T, sh, E.PushFront{x}):
  match sh:
    case ST.Sh{+f, +b}:
      K.mk(~T, ST.Sh{f, b}, E.PushFront{x}, ST.Sh{Con{x, f}, b}, E.OUnit{}, {==}, {==})

def op_push_back(~T: Data, +sh: ST.Shadow<T>, +x: T) -> K.StepOK(~T, sh, E.PushBack{x}):
  match sh:
    case ST.Sh{+f, +b}:
      K.mk(~T, ST.Sh{f, b}, E.PushBack{x}, ST.Sh{f, Con{x, b}}, E.OUnit{}, {==}, Equal.cong(List<&2, T>, List<&2, T> & E.Obs<T>, z => (z, E.OUnit{}), ST.model(T, ST.Sh{f, Con{x, b}}), SC.snoc(T, ST.model(T, ST.Sh{f, b}), x), model_back(T, f, x, b)))

def op_to_list(~T: Data, +sh: ST.Shadow<T>) -> K.StepOK(~T, sh, E.ToList{}):
  match sh:
    case ST.Sh{+f, +b}:
      +el = Equal.trans(List<&2, T>, List.append(&2, T, f, List.reverse(&2, T, b)), List.append(&2, T, f, SC.reverse(T, b)), SC.append(T, f, SC.reverse(T, b)), Equal.cong(List<&2, T>, List<&2, T>, z => List.append(&2, T, f, z), List.reverse(&2, T, b), SC.reverse(T, b), LL.base_rev(T, b)), LL.base_append(T, f, SC.reverse(T, b)))
      K.mk(~T, ST.Sh{f, b}, E.ToList{}, ST.Sh{f, b}, E.OList{List.append(&2, T, f, List.reverse(&2, T, b))}, {==}, Equal.cong(List<&2, T>, List<&2, T> & E.Obs<T>, z => (ST.model(T, ST.Sh{f, b}), E.OList{z}), List.append(&2, T, f, List.reverse(&2, T, b)), ST.model(T, ST.Sh{f, b}), el))

def pf_fin(~T: Data, +sh: ST.Shadow<T>, +sh1: ST.Shadow<T>, +e: {DQ.ready_front(~T, ST.real(T, sh)) == ST.real(T, sh1) : DQ.Deque<T>}, +em: {ST.model(T, sh1) == ST.model(T, sh) : List<&2, T>}, rd: Read(~T, sh1, DQ.obs_item(~T, DQ.pop_front_ready(~T, ST.real(T, sh1))), S.pop_front(T, ST.model(T, sh1)))) -> K.StepOK(~T, sh, E.PopFront{}):
  match rd:
    case Tuple{+sh2, Tuple{+o, Tuple{e1, e2}}}:
      K.mk(~T, sh, E.PopFront{}, sh2, o,
        Equal.trans(DQ.Deque<T> & E.Obs<T>, DQ.obs_item(~T, DQ.pop_front_ready(~T, DQ.ready_front(~T, ST.real(T, sh)))), DQ.obs_item(~T, DQ.pop_front_ready(~T, ST.real(T, sh1))), (ST.real(T, sh2), o), Equal.cong(DQ.Deque<T>, DQ.Deque<T> & E.Obs<T>, d => DQ.obs_item(~T, DQ.pop_front_ready(~T, d)), DQ.ready_front(~T, ST.real(T, sh)), ST.real(T, sh1), e), e1),
        Equal.trans(List<&2, T> & E.Obs<T>, (ST.model(T, sh2), o), S.pop_front(T, ST.model(T, sh1)), S.pop_front(T, ST.model(T, sh)), e2, Equal.cong(List<&2, T>, List<&2, T> & E.Obs<T>, z => S.pop_front(T, z), ST.model(T, sh1), ST.model(T, sh), em)))

def pf_rf(~T: Data, +sh: ST.Shadow<T>, rf: RB.RF(~T, sh)) -> K.StepOK(~T, sh, E.PopFront{}):
  match rf:
    case Tuple{+sh1, Tuple{e, Tuple{em, hr}}}:
      pf_fin(~T, sh, sh1, e, em, pop_front_ready(~T, sh1, hr))

def kf_fin(~T: Data, +sh: ST.Shadow<T>, +sh1: ST.Shadow<T>, +e: {DQ.ready_front(~T, ST.real(T, sh)) == ST.real(T, sh1) : DQ.Deque<T>}, +em: {ST.model(T, sh1) == ST.model(T, sh) : List<&2, T>}, rd: Read(~T, sh1, DQ.obs_item(~T, DQ.peek_front_ready(~T, ST.real(T, sh1))), (ST.model(T, sh1), E.OItem{S.item(T, SC.head(T, ST.model(T, sh1)))}))) -> K.StepOK(~T, sh, E.PeekFront{}):
  match rd:
    case Tuple{+sh2, Tuple{+o, Tuple{e1, e2}}}:
      K.mk(~T, sh, E.PeekFront{}, sh2, o,
        Equal.trans(DQ.Deque<T> & E.Obs<T>, DQ.obs_item(~T, DQ.peek_front_ready(~T, DQ.ready_front(~T, ST.real(T, sh)))), DQ.obs_item(~T, DQ.peek_front_ready(~T, ST.real(T, sh1))), (ST.real(T, sh2), o), Equal.cong(DQ.Deque<T>, DQ.Deque<T> & E.Obs<T>, d => DQ.obs_item(~T, DQ.peek_front_ready(~T, d)), DQ.ready_front(~T, ST.real(T, sh)), ST.real(T, sh1), e), e1),
        Equal.trans(List<&2, T> & E.Obs<T>, (ST.model(T, sh2), o), (ST.model(T, sh1), E.OItem{S.item(T, SC.head(T, ST.model(T, sh1)))}), (ST.model(T, sh), E.OItem{S.item(T, SC.head(T, ST.model(T, sh)))}), e2, Equal.cong(List<&2, T>, List<&2, T> & E.Obs<T>, z => (z, E.OItem{S.item(T, SC.head(T, z))}), ST.model(T, sh1), ST.model(T, sh), em)))

def kf_rf(~T: Data, +sh: ST.Shadow<T>, rf: RB.RF(~T, sh)) -> K.StepOK(~T, sh, E.PeekFront{}):
  match rf:
    case Tuple{+sh1, Tuple{e, Tuple{em, hr}}}:
      kf_fin(~T, sh, sh1, e, em, peek_front_ready(~T, sh1, hr))

def pb_fin(~T: Data, +sh: ST.Shadow<T>, +sh1: ST.Shadow<T>, +e: {DQ.ready_back(~T, ST.real(T, sh)) == ST.real(T, sh1) : DQ.Deque<T>}, +em: {ST.model(T, sh1) == ST.model(T, sh) : List<&2, T>}, rd: Read(~T, sh1, DQ.obs_item(~T, DQ.pop_back_ready(~T, ST.real(T, sh1))), S.pop_back(T, ST.model(T, sh1)))) -> K.StepOK(~T, sh, E.PopBack{}):
  match rd:
    case Tuple{+sh2, Tuple{+o, Tuple{e1, e2}}}:
      K.mk(~T, sh, E.PopBack{}, sh2, o,
        Equal.trans(DQ.Deque<T> & E.Obs<T>, DQ.obs_item(~T, DQ.pop_back_ready(~T, DQ.ready_back(~T, ST.real(T, sh)))), DQ.obs_item(~T, DQ.pop_back_ready(~T, ST.real(T, sh1))), (ST.real(T, sh2), o), Equal.cong(DQ.Deque<T>, DQ.Deque<T> & E.Obs<T>, d => DQ.obs_item(~T, DQ.pop_back_ready(~T, d)), DQ.ready_back(~T, ST.real(T, sh)), ST.real(T, sh1), e), e1),
        Equal.trans(List<&2, T> & E.Obs<T>, (ST.model(T, sh2), o), S.pop_back(T, ST.model(T, sh1)), S.pop_back(T, ST.model(T, sh)), e2, Equal.cong(List<&2, T>, List<&2, T> & E.Obs<T>, z => S.pop_back(T, z), ST.model(T, sh1), ST.model(T, sh), em)))

def pb_rb(~T: Data, +sh: ST.Shadow<T>, rb: RB.RB(~T, sh)) -> K.StepOK(~T, sh, E.PopBack{}):
  match rb:
    case Tuple{+sh1, Tuple{e, Tuple{em, hr}}}:
      pb_fin(~T, sh, sh1, e, em, pop_back_ready(~T, sh1, hr))

def kb_fin(~T: Data, +sh: ST.Shadow<T>, +sh1: ST.Shadow<T>, +e: {DQ.ready_back(~T, ST.real(T, sh)) == ST.real(T, sh1) : DQ.Deque<T>}, +em: {ST.model(T, sh1) == ST.model(T, sh) : List<&2, T>}, rd: Read(~T, sh1, DQ.obs_item(~T, DQ.peek_back_ready(~T, ST.real(T, sh1))), (ST.model(T, sh1), E.OItem{S.item(T, SC.last(T, ST.model(T, sh1)))}))) -> K.StepOK(~T, sh, E.PeekBack{}):
  match rd:
    case Tuple{+sh2, Tuple{+o, Tuple{e1, e2}}}:
      K.mk(~T, sh, E.PeekBack{}, sh2, o,
        Equal.trans(DQ.Deque<T> & E.Obs<T>, DQ.obs_item(~T, DQ.peek_back_ready(~T, DQ.ready_back(~T, ST.real(T, sh)))), DQ.obs_item(~T, DQ.peek_back_ready(~T, ST.real(T, sh1))), (ST.real(T, sh2), o), Equal.cong(DQ.Deque<T>, DQ.Deque<T> & E.Obs<T>, d => DQ.obs_item(~T, DQ.peek_back_ready(~T, d)), DQ.ready_back(~T, ST.real(T, sh)), ST.real(T, sh1), e), e1),
        Equal.trans(List<&2, T> & E.Obs<T>, (ST.model(T, sh2), o), (ST.model(T, sh1), E.OItem{S.item(T, SC.last(T, ST.model(T, sh1)))}), (ST.model(T, sh), E.OItem{S.item(T, SC.last(T, ST.model(T, sh)))}), e2, Equal.cong(List<&2, T>, List<&2, T> & E.Obs<T>, z => (z, E.OItem{S.item(T, SC.last(T, z))}), ST.model(T, sh1), ST.model(T, sh), em)))

def kb_rb(~T: Data, +sh: ST.Shadow<T>, rb: RB.RB(~T, sh)) -> K.StepOK(~T, sh, E.PeekBack{}):
  match rb:
    case Tuple{+sh1, Tuple{e, Tuple{em, hr}}}:
      kb_fin(~T, sh, sh1, e, em, peek_back_ready(~T, sh1, hr))

# every public operation refines the spec step
def step_ok(~T: Data, +sh: ST.Shadow<T>, +op: E.Op<T>) -> K.StepOK(~T, sh, op):
  match op:
    case E.Length{}:
      op_length(~T, sh)
    case E.PushFront{+x}:
      op_push_front(~T, sh, x)
    case E.PushBack{+x}:
      op_push_back(~T, sh, x)
    case E.PopFront{}:
      pf_rf(~T, sh, RB.ready_front(~T, sh))
    case E.PopBack{}:
      pb_rb(~T, sh, RB.ready_back(~T, sh))
    case E.PeekFront{}:
      kf_rf(~T, sh, RB.ready_front(~T, sh))
    case E.PeekBack{}:
      kb_rb(~T, sh, RB.ready_back(~T, sh))
    case E.ToList{}:
      op_to_list(~T, sh)
