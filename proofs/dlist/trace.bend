import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/array.bend as AR
import ../../spec/common.bend as SC
import ../../spec/doubly_linked_list.bend as DS
import ../../src/doubly_linked_list.bend as D
import ../../types/doubly_linked_list.bend as E
import ./state.bend as ST
import ./core.bend as K
import ./reads.bend as RD
import ./nbrs.bend as NB
import ./tolist.bend as TL
import ./mut.bend as MU
import ./rm.bend as RMV
import ./insops.bend as IO

# Every operation, and arbitrary finite traces, of the doubly linked list.
#
# The room premise is the representation's capacity condition: ids are
# slot indices of Base arrays (below 2^31), so the ids issued -- fresh plus
# the number of insertions still to come -- stay below 2^q with q <= 31.

def step_ok(~T: Data, sh: ST.Shadow<T>, +op: E.Op<T>, +h: {ST.good(~T, sh) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +hroom: {Nat.is_lt(K.sfresh(~T, sh), SC.pow2(q)) == True{} : Bool}) -> K.StepOK(~T, sh, op):
  match sh:
    case ST.Sh{+tag, +fresh, +depth, +tv, +tp, +tn, +ord}:
      match op:
        case E.Length{}:
          RD.length_ok(~T, tag, fresh, depth, tv, tp, tn, ord, h)
        case E.PushFront{+x}:
          IO.push_front_ok(~T, tag, fresh, depth, tv, tp, tn, ord, x, h, q, hq, hroom)
        case E.PushBack{+x}:
          IO.push_back_ok(~T, tag, fresh, depth, tv, tp, tn, ord, x, h, q, hq, hroom)
        case E.InsertBefore{E.H{+l, +i}, +x}:
          IO.insert_before_ok(~T, tag, fresh, depth, tv, tp, tn, ord, l, i, x, h, q, hq, hroom)
        case E.InsertAfter{E.H{+l, +i}, +x}:
          IO.insert_after_ok(~T, tag, fresh, depth, tv, tp, tn, ord, l, i, x, h, q, hq, hroom)
        case E.Remove{E.H{+l, +i}}:
          RMV.remove_ok(~T, tag, fresh, depth, tv, tp, tn, ord, l, i, h)
        case E.Get{E.H{+l, +i}}:
          RD.get_ok(~T, tag, fresh, depth, tv, tp, tn, ord, l, i, h)
        case E.Set{E.H{+l, +i}, +x}:
          MU.set_ok(~T, tag, fresh, depth, tv, tp, tn, ord, l, i, x, h)
        case E.Next{E.H{+l, +i}}:
          NB.next_ok(~T, tag, fresh, depth, tv, tp, tn, ord, l, i, h)
        case E.Prev{E.H{+l, +i}}:
          NB.prev_ok(~T, tag, fresh, depth, tv, tp, tn, ord, l, i, h)
        case E.ToList{}:
          TL.tolist_ok(~T, tag, fresh, depth, tv, tp, tn, ord, h)

# ---- projections of a step ----

def so_sh(~T: Data, -sh: ST.Shadow<T>, -op: E.Op<T>, so: K.StepOK(~T, sh, op)) -> ST.Shadow<T>:
  match so:
    case Tuple{sh2, r}:
      sh2

def so_obs(~T: Data, -sh: ST.Shadow<T>, -op: E.Op<T>, so: K.StepOK(~T, sh, op)) -> E.Obs<T>:
  match so:
    case Tuple{sh2, Tuple{o, r}}:
      o

def so_step(~T: Data, -sh: ST.Shadow<T>, -op: E.Op<T>, so: K.StepOK(~T, sh, op)) -> {D.step(~T, ST.real(~T, sh), op) == (ST.real(~T, so_sh(~T, sh, op, so)), so_obs(~T, sh, op, so)) : D.DList<T> & E.Obs<T>}:
  match so:
    case Tuple{sh2, Tuple{o, Tuple{e, r}}}:
      e

def so_good(~T: Data, -sh: ST.Shadow<T>, -op: E.Op<T>, so: K.StepOK(~T, sh, op)) -> {ST.good(~T, so_sh(~T, sh, op, so)) == True{} : Bool}:
  match so:
    case Tuple{sh2, Tuple{o, Tuple{e, Tuple{g, s}}}}:
      g

def so_spec(~T: Data, -sh: ST.Shadow<T>, -op: E.Op<T>, so: K.StepOK(~T, sh, op)) -> {(ST.model(~T, so_sh(~T, sh, op, so)), so_obs(~T, sh, op, so)) == DS.step(T, ST.model(~T, sh), op) : DS.Model<T> & E.Obs<T>}:
  match so:
    case Tuple{sh2, Tuple{o, Tuple{e, Tuple{g, Tuple{s, m}}}}}:
      s

def so_fresh(~T: Data, -sh: ST.Shadow<T>, -op: E.Op<T>, so: K.StepOK(~T, sh, op)) -> {Nat.is_le(K.sfresh(~T, so_sh(~T, sh, op, so)), Nat.add(K.sfresh(~T, sh), K.icost(T, op))) == True{} : Bool}:
  match so:
    case Tuple{sh2, Tuple{o, Tuple{e, Tuple{g, Tuple{s, m}}}}}:
      m

# ---- the room budget of a trace ----

def inserts(-T: Data, ops: List<&2, E.Op<T>>) -> Nat:
  match ops:
    case Nil{}:
      0n
    case Con{op, rest}:
      Nat.add(K.icost(T, op), inserts(T, rest))

def add_le_l(+a: Nat, +b: Nat, +c: Nat, +h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(Nat.add(a, c), Nat.add(b, c)) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(a, c), Nat.add(c, a), N.add_comm(a, c)) : {Nat.is_le(_, Nat.add(b, c)) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(b, c), Nat.add(c, b), N.add_comm(b, c)) : {Nat.is_le(Nat.add(c, a), _) == True{} : Bool}
  N.le_add_left(a, b, c, h)

def budget_head(-T: Data, +m: Nat, +op: E.Op<T>, +rest: List<&2, E.Op<T>>, +q: Nat, +h: {Nat.is_lt(Nat.add(m, inserts(T, Con{op, rest})), SC.pow2(q)) == True{} : Bool}) -> {Nat.is_lt(m, SC.pow2(q)) == True{} : Bool}:
  N.le_lt_trans(m, Nat.add(m, inserts(T, Con{op, rest})), SC.pow2(q), N.le_add_right(m, inserts(T, Con{op, rest})), h)

def budget_tail(-T: Data, +m: Nat, +m1: Nat, +op: E.Op<T>, +rest: List<&2, E.Op<T>>, +q: Nat, +hm: {Nat.is_le(m1, Nat.add(m, K.icost(T, op))) == True{} : Bool}, +h: {Nat.is_lt(Nat.add(m, inserts(T, Con{op, rest})), SC.pow2(q)) == True{} : Bool}) -> {Nat.is_lt(Nat.add(m1, inserts(T, rest)), SC.pow2(q)) == True{} : Bool}:
  N.le_lt_trans(Nat.add(m1, inserts(T, rest)), Nat.add(m, inserts(T, Con{op, rest})), SC.pow2(q),
    L.subst(Nat, z => {Nat.is_le(Nat.add(m1, inserts(T, rest)), z) == True{} : Bool}, Nat.add(Nat.add(m, K.icost(T, op)), inserts(T, rest)), Nat.add(m, inserts(T, Con{op, rest})), N.add_assoc(m, K.icost(T, op), inserts(T, rest)),
      add_le_l(m1, Nat.add(m, K.icost(T, op)), inserts(T, rest), hm)),
    h)

# ---- the run ----

def srun_obs(-T: Data, ops: List<&2, E.Op<T>>, m: DS.Model<T>) -> List<&2, E.Obs<T>>:
  Pair.snd(DS.Model<T>, List<&2, E.Obs<T>>, DS.run(T, ops, m))

def srun_state(-T: Data, ops: List<&2, E.Op<T>>, m: DS.Model<T>) -> DS.Model<T>:
  Pair.fst(DS.Model<T>, List<&2, E.Obs<T>>, DS.run(T, ops, m))

def spec_run_cons(-T: Data, +op: E.Op<T>, +rest: List<&2, E.Op<T>>, +m: DS.Model<T>, +m1: DS.Model<T>, +o: E.Obs<T>, +e: {(m1, o) == DS.step(T, m, op) : DS.Model<T> & E.Obs<T>}) -> {DS.run(T, Con{op, rest}, m) == (srun_state(T, rest, m1), Con{o, srun_obs(T, rest, m1)}) : DS.Model<T> & List<&2, E.Obs<T>>}:
  %e : {DS.cons_obs(T, Pair.snd(DS.Model<T>, E.Obs<T>, _), DS.run(T, rest, Pair.fst(DS.Model<T>, E.Obs<T>, _))) == (srun_state(T, rest, m1), Con{o, srun_obs(T, rest, m1)}) : DS.Model<T> & List<&2, E.Obs<T>>}
  %Equal.sym(DS.Model<T> & List<&2, E.Obs<T>>, DS.run(T, rest, m1), (srun_state(T, rest, m1), srun_obs(T, rest, m1)), L.pair_eta(DS.Model<T>, List<&2, E.Obs<T>>, DS.run(T, rest, m1))) : {DS.cons_obs(T, o, _) == (srun_state(T, rest, m1), Con{o, srun_obs(T, rest, m1)}) : DS.Model<T> & List<&2, E.Obs<T>>}
  {==}

def RunOK(~T: Data, ops: List<&2, E.Op<T>>, sh: ST.Shadow<T>, acc: List<&2, E.Obs<T>>) -> Type:
  Sigma<&1, &1, ST.Shadow<T>, sh2 => {D.run_acc(~T, ops, (ST.real(~T, sh), acc)) == (ST.real(~T, sh2), List.reverse.go(&2, E.Obs<T>, srun_obs(T, ops, ST.model(~T, sh)), acc)) : D.DList<T> & List<&2, E.Obs<T>>} & ({ST.good(~T, sh2) == True{} : Bool} & {ST.model(~T, sh2) == srun_state(T, ops, ST.model(~T, sh)) : DS.Model<T>})>

def ro_sh(~T: Data, -ops: List<&2, E.Op<T>>, -sh: ST.Shadow<T>, -acc: List<&2, E.Obs<T>>, r: RunOK(~T, ops, sh, acc)) -> ST.Shadow<T>:
  match r:
    case Tuple{sh2, x}:
      sh2

def ro_run(~T: Data, -ops: List<&2, E.Op<T>>, -sh: ST.Shadow<T>, -acc: List<&2, E.Obs<T>>, r: RunOK(~T, ops, sh, acc)) -> {D.run_acc(~T, ops, (ST.real(~T, sh), acc)) == (ST.real(~T, ro_sh(~T, ops, sh, acc, r)), List.reverse.go(&2, E.Obs<T>, srun_obs(T, ops, ST.model(~T, sh)), acc)) : D.DList<T> & List<&2, E.Obs<T>>}:
  match r:
    case Tuple{sh2, Tuple{e, x}}:
      e

def ro_good(~T: Data, -ops: List<&2, E.Op<T>>, -sh: ST.Shadow<T>, -acc: List<&2, E.Obs<T>>, r: RunOK(~T, ops, sh, acc)) -> {ST.good(~T, ro_sh(~T, ops, sh, acc, r)) == True{} : Bool}:
  match r:
    case Tuple{sh2, Tuple{e, Tuple{g, m}}}:
      g

def ro_model(~T: Data, -ops: List<&2, E.Op<T>>, -sh: ST.Shadow<T>, -acc: List<&2, E.Obs<T>>, r: RunOK(~T, ops, sh, acc)) -> {ST.model(~T, ro_sh(~T, ops, sh, acc, r)) == srun_state(T, ops, ST.model(~T, sh)) : DS.Model<T>}:
  match r:
    case Tuple{sh2, Tuple{e, Tuple{g, m}}}:
      m

def run_ok(~T: Data, +ops: List<&2, E.Op<T>>, +sh: ST.Shadow<T>, +acc: List<&2, E.Obs<T>>, +g: {ST.good(~T, sh) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +room: {Nat.is_lt(Nat.add(K.sfresh(~T, sh), inserts(T, ops)), SC.pow2(q)) == True{} : Bool}) -> RunOK(~T, ops, sh, acc):
  match ops:
    case Nil{}:
      (sh, ({==}, (g, {==})))
    case Con{+op, +rest}:
      +m = ST.model(~T, sh)
      +hh = budget_head(T, K.sfresh(~T, sh), op, rest, q, room)
      +sh1 = so_sh(~T, sh, op, step_ok(~T, sh, op, g, q, hq, hh))
      +ob = so_obs(~T, sh, op, step_ok(~T, sh, op, g, q, hq, hh))
      +g1 = so_good(~T, sh, op, step_ok(~T, sh, op, g, q, hq, hh))
      +r1 = budget_tail(T, K.sfresh(~T, sh), K.sfresh(~T, sh1), op, rest, q, so_fresh(~T, sh, op, step_ok(~T, sh, op, g, q, hq, hh)), room)
      +m1 = ST.model(~T, sh1)
      +acc1 = {Con{ob, acc} : List<&2, E.Obs<T>>}
      +sh2 = ro_sh(~T, rest, sh1, acc1, run_ok(~T, rest, sh1, acc1, g1, q, hq, r1))
      +es = spec_run_cons(T, op, rest, m, m1, ob, so_spec(~T, sh, op, step_ok(~T, sh, op, g, q, hq, hh)))
      -R = DS.run(T, rest, m1)
      (sh2, (
        %Equal.sym(D.DList<T> & E.Obs<T>, D.step(~T, ST.real(~T, sh), op), (ST.real(~T, sh1), ob), so_step(~T, sh, op, step_ok(~T, sh, op, g, q, hq, hh))) : {D.run_acc(~T, rest, D.record(~T, acc, _)) == (ST.real(~T, sh2), List.reverse.go(&2, E.Obs<T>, srun_obs(T, Con{op, rest}, m), acc)) : D.DList<T> & List<&2, E.Obs<T>>}
        %Equal.sym(D.DList<T> & List<&2, E.Obs<T>>, D.run_acc(~T, rest, (ST.real(~T, sh1), acc1)), (ST.real(~T, sh2), List.reverse.go(&2, E.Obs<T>, srun_obs(T, rest, m1), acc1)), ro_run(~T, rest, sh1, acc1, run_ok(~T, rest, sh1, acc1, g1, q, hq, r1))) : {_ == (ST.real(~T, sh2), List.reverse.go(&2, E.Obs<T>, srun_obs(T, Con{op, rest}, m), acc)) : D.DList<T> & List<&2, E.Obs<T>>}
        %Equal.sym(DS.Model<T> & List<&2, E.Obs<T>>, DS.run(T, Con{op, rest}, m), (Pair.fst(DS.Model<T>, List<&2, E.Obs<T>>, R), Con{ob, Pair.snd(DS.Model<T>, List<&2, E.Obs<T>>, R)}), es) : {(ST.real(~T, sh2), List.reverse.go(&2, E.Obs<T>, srun_obs(T, rest, m1), acc1)) == (ST.real(~T, sh2), List.reverse.go(&2, E.Obs<T>, Pair.snd(DS.Model<T>, List<&2, E.Obs<T>>, _), acc)) : D.DList<T> & List<&2, E.Obs<T>>}
        {==},
        (ro_good(~T, rest, sh1, acc1, run_ok(~T, rest, sh1, acc1, g1, q, hq, r1)),
         %Equal.sym(DS.Model<T> & List<&2, E.Obs<T>>, DS.run(T, Con{op, rest}, m), (Pair.fst(DS.Model<T>, List<&2, E.Obs<T>>, R), Con{ob, Pair.snd(DS.Model<T>, List<&2, E.Obs<T>>, R)}), es) : {ST.model(~T, sh2) == Pair.fst(DS.Model<T>, List<&2, E.Obs<T>>, _) : DS.Model<T>}
         ro_model(~T, rest, sh1, acc1, run_ok(~T, rest, sh1, acc1, g1, q, hq, r1)))))

def run_from(~T: Data, +ops: List<&2, E.Op<T>>, +sh0: ST.Shadow<T>, +g0: {ST.good(~T, sh0) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +room: {Nat.is_lt(Nat.add(K.sfresh(~T, sh0), inserts(T, ops)), SC.pow2(q)) == True{} : Bool}) -> {D.run(~T, ops, ST.real(~T, sh0)) == (ST.real(~T, ro_sh(~T, ops, sh0, Nil{}, run_ok(~T, ops, sh0, Nil{}, g0, q, hq, room))), srun_obs(T, ops, ST.model(~T, sh0))) : D.DList<T> & List<&2, E.Obs<T>>}:
  +sh2 = ro_sh(~T, ops, sh0, Nil{}, run_ok(~T, ops, sh0, Nil{}, g0, q, hq, room))
  +os = srun_obs(T, ops, ST.model(~T, sh0))
  %Equal.sym(D.DList<T> & List<&2, E.Obs<T>>, D.run_acc(~T, ops, (ST.real(~T, sh0), Nil{})), (ST.real(~T, sh2), List.reverse.go(&2, E.Obs<T>, os, Nil{})), ro_run(~T, ops, sh0, Nil{}, run_ok(~T, ops, sh0, Nil{}, g0, q, hq, room))) : {D.finish(~T, _) == (ST.real(~T, sh2), os) : D.DList<T> & List<&2, E.Obs<T>>}
  %Equal.sym(List<&2, E.Obs<T>>, List.reverse(&2, E.Obs<T>, List.reverse.go(&2, E.Obs<T>, os, Nil{})), os, LL.rev_rev(E.Obs<T>, os)) : {(ST.real(~T, sh2), _) == (ST.real(~T, sh2), os) : D.DList<T> & List<&2, E.Obs<T>>}
  {==}

def TraceOK(~T: Data, ops: List<&2, E.Op<T>>, sh0: ST.Shadow<T>) -> Type:
  Sigma<&1, &1, ST.Shadow<T>, sh2 => {D.run(~T, ops, ST.real(~T, sh0)) == (ST.real(~T, sh2), srun_obs(T, ops, ST.model(~T, sh0))) : D.DList<T> & List<&2, E.Obs<T>>} & ({ST.good(~T, sh2) == True{} : Bool} & {ST.model(~T, sh2) == srun_state(T, ops, ST.model(~T, sh0)) : DS.Model<T>})>

def trace_from(~T: Data, +ops: List<&2, E.Op<T>>, +sh0: ST.Shadow<T>, +g0: {ST.good(~T, sh0) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +room: {Nat.is_lt(Nat.add(K.sfresh(~T, sh0), inserts(T, ops)), SC.pow2(q)) == True{} : Bool}) -> TraceOK(~T, ops, sh0):
  (ro_sh(~T, ops, sh0, Nil{}, run_ok(~T, ops, sh0, Nil{}, g0, q, hq, room)),
   (run_from(~T, ops, sh0, g0, q, hq, room),
    (ro_good(~T, ops, sh0, Nil{}, run_ok(~T, ops, sh0, Nil{}, g0, q, hq, room)),
     ro_model(~T, ops, sh0, Nil{}, run_ok(~T, ops, sh0, Nil{}, g0, q, hq, room)))))

# Traces from the real constructor new(tag).
def TraceNew(~T: Data, tag: U32, ops: List<&2, E.Op<T>>) -> Type:
  Sigma<&1, &1, ST.Shadow<T>, sh2 => {D.run(~T, ops, D.new(~T, tag)) == (ST.real(~T, sh2), srun_obs(T, ops, DS.new(T, tag))) : D.DList<T> & List<&2, E.Obs<T>>} & ({ST.good(~T, sh2) == True{} : Bool} & {ST.model(~T, sh2) == srun_state(T, ops, DS.new(T, tag)) : DS.Model<T>})>

def tn_of(~T: Data, +tag: U32, +ops: List<&2, E.Op<T>>, t: TraceOK(~T, ops, ST.initial(~T, tag))) -> TraceNew(~T, tag, ops):
  match t:
    case Tuple{sh2, Tuple{e, rest}}:
      (sh2, (Equal.trans(D.DList<T> & List<&2, E.Obs<T>>, D.run(~T, ops, D.new(~T, tag)), D.run(~T, ops, ST.real(~T, ST.initial(~T, tag))), (ST.real(~T, sh2), srun_obs(T, ops, DS.new(T, tag))),
        Equal.cong(D.DList<T>, D.DList<T> & List<&2, E.Obs<T>>, z => D.run(~T, ops, z), D.new(~T, tag), ST.real(~T, ST.initial(~T, tag)), ST.new_real(~T, tag)), e), rest))

def trace_new(~T: Data, +tag: U32, +ops: List<&2, E.Op<T>>, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +room: {Nat.is_lt(inserts(T, ops), SC.pow2(q)) == True{} : Bool}) -> TraceNew(~T, tag, ops):
  tn_of(~T, tag, ops, trace_from(~T, ops, ST.initial(~T, tag), ST.new_good(~T, tag), q, hq, room))
