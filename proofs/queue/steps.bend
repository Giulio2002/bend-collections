import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/array.bend as AR
import ../../spec/common.bend as SC
import ../../spec/deque.bend as SD
import ../../spec/queue.bend as S
import ../../src/deque.bend as DQ
import ../../src/queue.bend as Q
import ../../types/deque.bend as DE
import ../../types/queue.bend as E
import ../deque/state.bend as DST
import ../deque/steps.bend as DPS

# Queue: the back-in/front-out specialization of the deque. A queue shadow IS
# a deque shadow; every step law below is the deque's law for the
# corresponding deque operation, with the observation and the error renamed.

def real(-T: Data, sh: DST.Shadow<T>) -> Q.Queue<T>:
  Q.QU{DST.real(T, sh)}

def dop(-T: Data, op: E.Op<T>) -> DE.Op<T>:
  match op:
    case E.Length{}:
      DE.Length{}
    case E.Enqueue{x}:
      DE.PushBack{x}
    case E.Dequeue{}:
      DE.PopFront{}
    case E.Peek{}:
      DE.PeekFront{}
    case E.ToList{}:
      DE.ToList{}

def qobs(-T: Data, o: DE.Obs<T>) -> E.Obs<T>:
  match o:
    case DE.ONat{n}:
      E.ONat{n}
    case DE.OItem{r}:
      E.OItem{Q.result_of(T, r)}
    case DE.OUnit{}:
      E.OUnit{}
    case DE.OList{xs}:
      E.OList{xs}

def qmap(-T: Data, p: List<&2, T> & DE.Obs<T>) -> List<&2, T> & E.Obs<T>:
  match p:
    case Tuple{xs, o}:
      (xs, qobs(T, o))

def pushcost(-T: Data, op: E.Op<T>) -> Nat:
  match op:
    case E.Length{}:
      0n
    case E.Enqueue{x}:
      1n
    case E.Dequeue{}:
      0n
    case E.Peek{}:
      0n
    case E.ToList{}:
      0n

def cost_eq(-T: Data, +op: E.Op<T>) -> {DPS.pushcost(T, dop(T, op)) == pushcost(T, op) : Nat}:
  match op:
    case E.Length{}:
      {==}
    case E.Enqueue{x}:
      {==}
    case E.Dequeue{}:
      {==}
    case E.Peek{}:
      {==}
    case E.ToList{}:
      {==}

# The FIFO spec step is the deque spec step of the corresponding operation,
# with the observation renamed.
def qspec(-T: Data, xs: List<&2, T>, op: E.Op<T>) -> {S.step(T, xs, op) == qmap(T, SD.step(T, xs, dop(T, op))) : List<&2, T> & E.Obs<T>}:
  match xs op:
    case Nil{} E.Length{}:
      {==}
    case Nil{} E.Enqueue{x}:
      {==}
    case Nil{} E.Dequeue{}:
      {==}
    case Nil{} E.Peek{}:
      {==}
    case Nil{} E.ToList{}:
      {==}
    case Con{h, t} E.Length{}:
      {==}
    case Con{h, t} E.Enqueue{x}:
      {==}
    case Con{h, t} E.Dequeue{}:
      {==}
    case Con{h, t} E.Peek{}:
      {==}
    case Con{h, t} E.ToList{}:
      {==}

def qpair(-T: Data, p: DQ.Deque<T> & DE.Obs<T>) -> Q.Queue<T> & E.Obs<T>:
  match p:
    case Tuple{d, o}:
      (Q.QU{d}, qobs(T, o))

def nat_lift(-T: Data, p: DQ.Deque<T> & Nat) -> {Q.obs_nat(T, Q.lift_nat(T, p)) == qpair(T, DQ.obs_nat(T, p)) : Q.Queue<T> & E.Obs<T>}:
  match p:
    case Tuple{d, n}:
      {==}

def item_lift(-T: Data, p: DQ.Deque<T> & Result<&2, &2, DE.Error, T>) -> {Q.obs_item(T, Q.lift(T, p)) == qpair(T, DQ.obs_item(T, p)) : Q.Queue<T> & E.Obs<T>}:
  match p:
    case Tuple{d, x}:
      {==}

def list_lift(-T: Data, p: DQ.Deque<T> & List<&2, T>) -> {Q.obs_list(T, Q.lift_list(T, p)) == qpair(T, DQ.obs_list(T, p)) : Q.Queue<T> & E.Obs<T>}:
  match p:
    case Tuple{d, xs}:
      {==}

# One queue step IS the deque step of the corresponding deque operation.
def step_lift(-T: Data, D: DQ.Deque<T>, op: E.Op<T>) -> {Q.step(T, Q.QU{D}, op) == qpair(T, DQ.step(T, D, dop(T, op))) : Q.Queue<T> & E.Obs<T>}:
  match op:
    case E.Length{}:
      nat_lift(T, DQ.length(T, D))
    case E.Enqueue{x}:
      {==}
    case E.Dequeue{}:
      item_lift(T, DQ.pop_front(T, D))
    case E.Peek{}:
      item_lift(T, DQ.peek_front(T, D))
    case E.ToList{}:
      list_lift(T, DQ.to_list(T, D))

def StepOK(-T: Data, sh: DST.Shadow<T>, op: E.Op<T>) -> Type:
  Sigma<&1, &1, DST.Shadow<T>, sh2 => Sigma<&1, &1, E.Obs<T>, o => {Q.step(T, real(T, sh), op) == (real(T, sh2), o) : Q.Queue<T> & E.Obs<T>} & ({DST.good(T, sh2) == True{} : Bool} & ({(DST.model(T, sh2), o) == S.step(T, DST.model(T, sh), op) : List<&2, T> & E.Obs<T>} & {Nat.is_le(DPS.sh_depth(T, sh2), Nat.add(DPS.sh_depth(T, sh), pushcost(T, op))) == True{} : Bool}))>>

def mk(-T: Data, -sh: DST.Shadow<T>, -op: E.Op<T>, sh2: DST.Shadow<T>, o: E.Obs<T>, e1: {Q.step(T, real(T, sh), op) == (real(T, sh2), o) : Q.Queue<T> & E.Obs<T>}, e2: {DST.good(T, sh2) == True{} : Bool}, e3: {(DST.model(T, sh2), o) == S.step(T, DST.model(T, sh), op) : List<&2, T> & E.Obs<T>}, e4: {Nat.is_le(DPS.sh_depth(T, sh2), Nat.add(DPS.sh_depth(T, sh), pushcost(T, op))) == True{} : Bool}) -> StepOK(T, sh, op):
  (sh2, (o, (e1, (e2, (e3, e4)))))


# ---- the queue step law, derived from the deque's ----

def dq_room(-T: Data, +sh: DST.Shadow<T>, +op: E.Op<T>, +room: {Nat.is_le(Nat.add(DPS.sh_depth(T, sh), pushcost(T, op)), 31n) == True{} : Bool}) -> {Nat.is_le(Nat.add(DPS.sh_depth(T, sh), DPS.pushcost(T, dop(T, op))), 31n) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_le(Nat.add(DPS.sh_depth(T, sh), z), 31n) == True{} : Bool}, pushcost(T, op), DPS.pushcost(T, dop(T, op)), Equal.sym(Nat, DPS.pushcost(T, dop(T, op)), pushcost(T, op), cost_eq(T, op)), room)

def so_sh(-T: Data, -sh: DST.Shadow<T>, -op: DE.Op<T>, so: DPS.StepOK(T, sh, op)) -> DST.Shadow<T>:
  match so:
    case Tuple{sh2, r}:
      sh2

def so_obs(-T: Data, -sh: DST.Shadow<T>, -op: DE.Op<T>, so: DPS.StepOK(T, sh, op)) -> DE.Obs<T>:
  match so:
    case Tuple{sh2, Tuple{o, r}}:
      o

def so_step(-T: Data, -sh: DST.Shadow<T>, -op: DE.Op<T>, so: DPS.StepOK(T, sh, op)) -> {DQ.step(T, DST.real(T, sh), op) == (DST.real(T, so_sh(T, sh, op, so)), so_obs(T, sh, op, so)) : DQ.Deque<T> & DE.Obs<T>}:
  match so:
    case Tuple{sh2, Tuple{o, Tuple{e, r}}}:
      e

def so_good(-T: Data, -sh: DST.Shadow<T>, -op: DE.Op<T>, so: DPS.StepOK(T, sh, op)) -> {DST.good(T, so_sh(T, sh, op, so)) == True{} : Bool}:
  match so:
    case Tuple{sh2, Tuple{o, Tuple{e, Tuple{g, s}}}}:
      g

def so_spec(-T: Data, -sh: DST.Shadow<T>, -op: DE.Op<T>, so: DPS.StepOK(T, sh, op)) -> {(DST.model(T, so_sh(T, sh, op, so)), so_obs(T, sh, op, so)) == SD.step(T, DST.model(T, sh), op) : List<&2, T> & DE.Obs<T>}:
  match so:
    case Tuple{sh2, Tuple{o, Tuple{e, Tuple{g, Tuple{s, dd}}}}}:
      s

def so_depth(-T: Data, -sh: DST.Shadow<T>, -op: DE.Op<T>, so: DPS.StepOK(T, sh, op)) -> {Nat.is_le(DPS.sh_depth(T, so_sh(T, sh, op, so)), Nat.add(DPS.sh_depth(T, sh), DPS.pushcost(T, op))) == True{} : Bool}:
  match so:
    case Tuple{sh2, Tuple{o, Tuple{e, Tuple{g, Tuple{s, dd}}}}}:
      dd

def step_ok(-T: Data, +sh: DST.Shadow<T>, +op: E.Op<T>, +g: {DST.good(T, sh) == True{} : Bool}, +room: {Nat.is_le(Nat.add(DPS.sh_depth(T, sh), pushcost(T, op)), 31n) == True{} : Bool}) -> StepOK(T, sh, op):
  +dr = dq_room(T, sh, op, room)
  +sh2 = so_sh(T, sh, dop(T, op), DPS.step_ok(T, sh, dop(T, op), g, dr))
  +o = so_obs(T, sh, dop(T, op), DPS.step_ok(T, sh, dop(T, op), g, dr))
  mk(T, sh, op, sh2, qobs(T, o),
    %Equal.sym(Q.Queue<T> & E.Obs<T>, Q.step(T, Q.QU{DST.real(T, sh)}, op), qpair(T, DQ.step(T, DST.real(T, sh), dop(T, op))), step_lift(T, DST.real(T, sh), op)) : {_ == (real(T, sh2), qobs(T, o)) : Q.Queue<T> & E.Obs<T>}
    %Equal.sym(DQ.Deque<T> & DE.Obs<T>, DQ.step(T, DST.real(T, sh), dop(T, op)), (DST.real(T, sh2), o), so_step(T, sh, dop(T, op), DPS.step_ok(T, sh, dop(T, op), g, dr))) : {qpair(T, _) == (real(T, sh2), qobs(T, o)) : Q.Queue<T> & E.Obs<T>}
    {==},
    so_good(T, sh, dop(T, op), DPS.step_ok(T, sh, dop(T, op), g, dr)),
    %Equal.sym(List<&2, T> & E.Obs<T>, S.step(T, DST.model(T, sh), op), qmap(T, SD.step(T, DST.model(T, sh), dop(T, op))), qspec(T, DST.model(T, sh), op)) : {(DST.model(T, sh2), qobs(T, o)) == _ : List<&2, T> & E.Obs<T>}
    %so_spec(T, sh, dop(T, op), DPS.step_ok(T, sh, dop(T, op), g, dr)) : {(DST.model(T, sh2), qobs(T, o)) == qmap(T, _) : List<&2, T> & E.Obs<T>}
    {==},
    L.subst(Nat, z => {Nat.is_le(DPS.sh_depth(T, sh2), Nat.add(DPS.sh_depth(T, sh), z)) == True{} : Bool}, DPS.pushcost(T, dop(T, op)), pushcost(T, op), cost_eq(T, op), so_depth(T, sh, dop(T, op), DPS.step_ok(T, sh, dop(T, op), g, dr))))
