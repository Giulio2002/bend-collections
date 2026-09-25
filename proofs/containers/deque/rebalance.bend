import Base
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../../lib/list.bend as LL
import ../../../spec/lib/common.bend as SC
import ../../lib/arith.bend as AR
import ../../lib/two_list.bend as TL
import ../../../src/containers/deque.bend as DQ
import ./state.bend as ST

# Rebalancing: ready_front / ready_back move half of the other list over.
# They keep the model, and leave the requested end nonempty unless the whole
# deque is empty.

def is_nil(-T: Data, xs: List<&2, T>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{h, t}:
      False{}

# the front can be read: nonempty, or the deque is empty
def rdy_f(-T: Data, sh: ST.Shadow<T>) -> Bool:
  match sh:
    case ST.Sh{Nil{}, b}:
      is_nil(T, b)
    case ST.Sh{Con{x, f}, b}:
      True{}

# the back can be read: nonempty, or the deque is empty
def rdy_b(-T: Data, sh: ST.Shadow<T>) -> Bool:
  match sh:
    case ST.Sh{f, Nil{}}:
      is_nil(T, f)
    case ST.Sh{f, Con{x, b}}:
      True{}

def RF(~T: Data, sh: ST.Shadow<T>) -> Type:
  Sigma<&1, &1, ST.Shadow<T>, sh1 => {DQ.ready_front(~T, ST.real(T, sh)) == ST.real(T, sh1) : DQ.Deque<T>} & ({ST.model(T, sh1) == ST.model(T, sh) : List<&2, T>} & {rdy_f(T, sh1) == True{} : Bool})>

def RB(~T: Data, sh: ST.Shadow<T>) -> Type:
  Sigma<&1, &1, ST.Shadow<T>, sh1 => {DQ.ready_back(~T, ST.real(T, sh)) == ST.real(T, sh1) : DQ.Deque<T>} & ({ST.model(T, sh1) == ST.model(T, sh) : List<&2, T>} & {rdy_b(T, sh1) == True{} : Bool})>

def sub_pos(+n: Nat, +h: Nat, +lt: {Nat.is_lt(h, n) == True{} : Bool}) -> {Nat.is_lt(0n, Nat.sub(n, h)) == True{} : Bool}:
  match n h:
    case 0n _:
      Empty.absurd({Nat.is_lt(0n, Nat.sub(0n, h)) == True{} : Bool}, N.lt_zero_absurd(h, lt))
    case 1n+m 0n:
      {==}
    case 1n+m 1n+k:
      sub_pos(m, k, lt)

def rdy_f_len(-T: Data, +m: List<&2, T>, +k: List<&2, T>, +h: {Nat.is_lt(0n, SC.length(T, m)) == True{} : Bool}) -> {rdy_f(T, ST.Sh{m, k}) == True{} : Bool}:
  match m:
    case Nil{}:
      Empty.absurd({rdy_f(T, ST.Sh{Nil{}, k}) == True{} : Bool}, L.false_true(h))
    case Con{x, t}:
      {==}

def rdy_b_len(-T: Data, +k: List<&2, T>, +m: List<&2, T>, +h: {Nat.is_lt(0n, SC.length(T, m)) == True{} : Bool}) -> {rdy_b(T, ST.Sh{k, m}) == True{} : Bool}:
  match m:
    case Nil{}:
      Empty.absurd({rdy_b(T, ST.Sh{k, Nil{}}) == True{} : Bool}, L.false_true(h))
    case Con{x, t}:
      {==}

# the split of a nonempty list at half its length: lengths of the two parts
def half_lt(-T: Data, +y: T, +t: List<&2, T>) -> {Nat.is_lt(Nat.div(SC.length(T, Con{y, t}), 2n), SC.length(T, Con{y, t})) == True{} : Bool}:
  N.le_lt_succ(Nat.div(1n+SC.length(T, t), 2n), SC.length(T, t), TL.half_le(SC.length(T, t)))

def moved_len(-T: Data, +b: List<&2, T>, +h: Nat) -> {SC.length(T, SC.reverse(T, SC.drop(T, b, h))) == Nat.sub(SC.length(T, b), h) : Nat}:
  Equal.trans(Nat, SC.length(T, SC.reverse(T, SC.drop(T, b, h))), SC.length(T, SC.drop(T, b, h)), Nat.sub(SC.length(T, b), h), TL.len_rev(T, SC.drop(T, b, h)), TL.len_drop(T, b, h))

def kept_len(-T: Data, +b: List<&2, T>, +h: Nat, +hl: {Nat.is_le(h, SC.length(T, b)) == True{} : Bool}) -> {SC.length(T, SC.take(T, b, h)) == h : Nat}:
  TL.len_take(T, b, h, hl)

def rf_move(~T: Data, +y: T, +t: List<&2, T>) -> RF(~T, ST.Sh{Nil{}, Con{y, t}}):
  +b = {Con{y, t} : List<&2, T>}
  +n = SC.length(T, b)
  +h = Nat.div(n, 2n)
  +kk = SC.take(T, b, h)
  +mm = SC.reverse(T, SC.drop(T, b, h))
  +hlt = half_lt(T, y, t)
  +e1 = Equal.cong(List<&2, T> & List<&2, T>, DQ.Deque<T>, r => DQ.front_split(~T, n, h, r), DQ.split(~T, h, b), (kk, mm), TL.split_eq(~T, h, b))
  +e2 = Equal.cong(Nat, DQ.Deque<T>, z => DQ.DE{mm, kk, z, h}, Nat.sub(n, h), SC.length(T, mm), Equal.sym(Nat, SC.length(T, mm), Nat.sub(n, h), moved_len(T, b, h)))
  +e3 = Equal.cong(Nat, DQ.Deque<T>, z => DQ.DE{mm, kk, SC.length(T, mm), z}, h, SC.length(T, kk), Equal.sym(Nat, SC.length(T, kk), h, kept_len(T, b, h, N.lt_le(h, n, hlt))))
  +em = Equal.trans(List<&2, T>, SC.append(T, mm, SC.reverse(T, kk)), SC.reverse(T, SC.append(T, kk, SC.drop(T, b, h))), SC.reverse(T, b),
    Equal.sym(List<&2, T>, SC.reverse(T, SC.append(T, kk, SC.drop(T, b, h))), SC.append(T, mm, SC.reverse(T, kk)), LL.rev_append(T, kk, SC.drop(T, b, h))),
    Equal.cong(List<&2, T>, List<&2, T>, z => SC.reverse(T, z), SC.append(T, kk, SC.drop(T, b, h)), b, TL.take_drop(T, b, h)))
  +hr = rdy_f_len(T, mm, kk, L.subst(Nat, z => {Nat.is_lt(0n, z) == True{} : Bool}, Nat.sub(n, h), SC.length(T, mm), Equal.sym(Nat, SC.length(T, mm), Nat.sub(n, h), moved_len(T, b, h)), sub_pos(n, h, hlt)))
  (ST.Sh{mm, kk}, (Equal.trans(DQ.Deque<T>, DQ.front_split(~T, n, h, DQ.split(~T, h, b)), DQ.DE{mm, kk, Nat.sub(n, h), h}, ST.real(T, ST.Sh{mm, kk}), e1, Equal.trans(DQ.Deque<T>, DQ.DE{mm, kk, Nat.sub(n, h), h}, DQ.DE{mm, kk, SC.length(T, mm), h}, ST.real(T, ST.Sh{mm, kk}), e2, e3)), (em, hr)))

def rb_move(~T: Data, +y: T, +t: List<&2, T>) -> RB(~T, ST.Sh{Con{y, t}, Nil{}}):
  +f = {Con{y, t} : List<&2, T>}
  +n = SC.length(T, f)
  +h = Nat.div(n, 2n)
  +kk = SC.take(T, f, h)
  +mm = SC.reverse(T, SC.drop(T, f, h))
  +hlt = half_lt(T, y, t)
  +e1 = Equal.cong(List<&2, T> & List<&2, T>, DQ.Deque<T>, r => DQ.back_split(~T, n, h, r), DQ.split(~T, h, f), (kk, mm), TL.split_eq(~T, h, f))
  +e2 = Equal.cong(Nat, DQ.Deque<T>, z => DQ.DE{kk, mm, z, Nat.sub(n, h)}, h, SC.length(T, kk), Equal.sym(Nat, SC.length(T, kk), h, kept_len(T, f, h, N.lt_le(h, n, hlt))))
  +e3 = Equal.cong(Nat, DQ.Deque<T>, z => DQ.DE{kk, mm, SC.length(T, kk), z}, Nat.sub(n, h), SC.length(T, mm), Equal.sym(Nat, SC.length(T, mm), Nat.sub(n, h), moved_len(T, f, h)))
  +em = Equal.trans(List<&2, T>, SC.append(T, kk, SC.reverse(T, mm)), SC.append(T, kk, SC.drop(T, f, h)), SC.append(T, f, Nil{}),
    Equal.cong(List<&2, T>, List<&2, T>, z => SC.append(T, kk, z), SC.reverse(T, mm), SC.drop(T, f, h), LL.spec_rev_rev(T, SC.drop(T, f, h))),
    Equal.trans(List<&2, T>, SC.append(T, kk, SC.drop(T, f, h)), f, SC.append(T, f, Nil{}), TL.take_drop(T, f, h), Equal.sym(List<&2, T>, SC.append(T, f, Nil{}), f, LL.append_nil(T, f))))
  +hr = rdy_b_len(T, kk, mm, L.subst(Nat, z => {Nat.is_lt(0n, z) == True{} : Bool}, Nat.sub(n, h), SC.length(T, mm), Equal.sym(Nat, SC.length(T, mm), Nat.sub(n, h), moved_len(T, f, h)), sub_pos(n, h, hlt)))
  (ST.Sh{kk, mm}, (Equal.trans(DQ.Deque<T>, DQ.back_split(~T, n, h, DQ.split(~T, h, f)), DQ.DE{kk, mm, h, Nat.sub(n, h)}, ST.real(T, ST.Sh{kk, mm}), e1, Equal.trans(DQ.Deque<T>, DQ.DE{kk, mm, h, Nat.sub(n, h)}, DQ.DE{kk, mm, SC.length(T, kk), Nat.sub(n, h)}, ST.real(T, ST.Sh{kk, mm}), e2, e3)), (em, hr)))

def ready_front(~T: Data, +sh: ST.Shadow<T>) -> RF(~T, sh):
  match sh:
    case ST.Sh{Con{x, f}, b}:
      (ST.Sh{Con{x, f}, b}, ({==}, ({==}, {==})))
    case ST.Sh{Nil{}, Nil{}}:
      (ST.Sh{Nil{}, Nil{}}, ({==}, ({==}, {==})))
    case ST.Sh{Nil{}, Con{y, t}}:
      rf_move(~T, y, t)

def ready_back(~T: Data, +sh: ST.Shadow<T>) -> RB(~T, sh):
  match sh:
    case ST.Sh{f, Con{x, b}}:
      (ST.Sh{f, Con{x, b}}, ({==}, ({==}, {==})))
    case ST.Sh{Nil{}, Nil{}}:
      (ST.Sh{Nil{}, Nil{}}, ({==}, ({==}, {==})))
    case ST.Sh{Con{y, t}, Nil{}}:
      rb_move(~T, y, t)
