import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/order.bend as O
import ../../spec/common.bend as SC
import ../../spec/binary_heap.bend as S
import ../../src/binary_heap.bend as H
import ../../types/binary_heap.bend as E
import ./state.bend as ST
import ./steps.bend as SP
import ./root.bend as RT
import ./budget.bend as BG

def add_le_a(+a: Nat, +x: Nat, +y: Nat, +h: {Nat.is_le(x, y) == True{} : Bool}) -> {Nat.is_le(Nat.add(a, x), Nat.add(a, y)) == True{} : Bool}:
  N.le_add_left(x, y, a, h)

# Arbitrary finite operation traces: the real runner refines the spec runner.
#
# The slot array is linear, so the statement is the shadow form the per-step
# laws use: running any finite list of operations on the array of a good
# shadow lands on the array of another good shadow, emits exactly the spec
# runner's observations, and the model of the final shadow is the spec
# runner's final model.
#
# `pushes(ops)` is the number of elements the list can add (one per push,
# |ys| per from_list). No operation grows the heap by more than its push
# count, so ONE premise -- size + pushes(ops) < 2^q with q <= 31 -- keeps the
# size below 2^q at every step and discharges each step's capacity
# condition. It is the representation's capacity condition (Base arrays
# have at most 2^31 slots), with no bound on the length of the trace.

def pushes(~A: Data, ops: List<&2, E.Op<A>>) -> Nat:
  match ops:
    case Nil{}:
      0n
    case Con{op, rest}:
      Nat.add(SP.pushcost(~A, op), pushes(~A, rest))

def add_le_l(+a: Nat, +b: Nat, +c: Nat, +h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(Nat.add(a, c), Nat.add(b, c)) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(a, c), Nat.add(c, a), N.add_comm(a, c)) : {Nat.is_le(_, Nat.add(b, c)) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(b, c), Nat.add(c, b), N.add_comm(b, c)) : {Nat.is_le(Nat.add(c, a), _) == True{} : Bool}
  add_le_a(c, a, b, h)

def budget_head(~A: Data, +d: Nat, +op: E.Op<A>, +rest: List<&2, E.Op<A>>, +q: Nat, +h: {Nat.is_lt(Nat.add(d, pushes(~A, Con{op, rest})), SC.pow2(q)) == True{} : Bool}) -> {Nat.is_lt(Nat.add(d, SP.pushcost(~A, op)), SC.pow2(q)) == True{} : Bool}:
  N.le_lt_trans(Nat.add(d, SP.pushcost(~A, op)), Nat.add(d, Nat.add(SP.pushcost(~A, op), pushes(~A, rest))), SC.pow2(q),
    add_le_a(d, SP.pushcost(~A, op), Nat.add(SP.pushcost(~A, op), pushes(~A, rest)), N.le_add_right(SP.pushcost(~A, op), pushes(~A, rest))), h)

def budget_tail(~A: Data, +d: Nat, +d2: Nat, +op: E.Op<A>, +rest: List<&2, E.Op<A>>, +q: Nat, +hd2: {Nat.is_le(d2, Nat.add(d, SP.pushcost(~A, op))) == True{} : Bool}, +h: {Nat.is_lt(Nat.add(d, pushes(~A, Con{op, rest})), SC.pow2(q)) == True{} : Bool}) -> {Nat.is_lt(Nat.add(d2, pushes(~A, rest)), SC.pow2(q)) == True{} : Bool}:
  N.le_lt_trans(Nat.add(d2, pushes(~A, rest)), Nat.add(Nat.add(d, SP.pushcost(~A, op)), pushes(~A, rest)), SC.pow2(q),
    add_le_l(d2, Nat.add(d, SP.pushcost(~A, op)), pushes(~A, rest), hd2),
    L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(q)) == True{} : Bool}, Nat.add(d, Nat.add(SP.pushcost(~A, op), pushes(~A, rest))), Nat.add(Nat.add(d, SP.pushcost(~A, op)), pushes(~A, rest)), Equal.sym(Nat, Nat.add(Nat.add(d, SP.pushcost(~A, op)), pushes(~A, rest)), Nat.add(d, Nat.add(SP.pushcost(~A, op), pushes(~A, rest))), N.add_assoc(d, SP.pushcost(~A, op), pushes(~A, rest))), h))

# ---- the spec step adds at most pushcost(op) elements ----

def slen_pop(-A: Data, xs: List<&2, A>) -> {Nat.is_le(SC.length(A, Pair.fst(List<&2, A>, E.Obs<A>, S.pop(A, xs))), Nat.add(SC.length(A, xs), 0n)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      N.le_trans(SC.length(A, t), 1n+SC.length(A, t), Nat.add(1n+SC.length(A, t), 0n), N.le_succ(SC.length(A, t)), SP.le_same(1n+SC.length(A, t)))

def slen_step(~A: Data, ~cmp: A -> A -> Cmp, +xs: List<&2, A>, op: E.Op<A>) -> {Nat.is_le(SC.length(A, Pair.fst(List<&2, A>, E.Obs<A>, S.step(~A, ~cmp, xs, op))), Nat.add(SC.length(A, xs), SP.pushcost(~A, op))) == True{} : Bool}:
  match op:
    case E.Length{}:
      SP.le_same(SC.length(A, xs))
    case E.Push{+x}:
      L.subst(Nat, z => {Nat.is_le(z, Nat.add(SC.length(A, xs), 1n)) == True{} : Bool}, 1n+SC.length(A, xs), SC.length(A, S.ins(~A, ~cmp, x, xs)), Equal.sym(Nat, SC.length(A, S.ins(~A, ~cmp, x, xs)), 1n+SC.length(A, xs), RT.length_ins(~A, ~cmp, x, xs)), SP.le_succ_add(SC.length(A, xs)))
    case E.Peek{}:
      SP.le_same(SC.length(A, xs))
    case E.Pop{}:
      slen_pop(A, xs)
    case E.FromList{+ys}:
      L.subst(Nat, z => {Nat.is_le(z, Nat.add(SC.length(A, xs), SC.length(A, ys))) == True{} : Bool}, Nat.add(0n, SC.length(A, ys)), SC.length(A, S.from_list(~A, ~cmp, ys, Nil{})),
        Equal.sym(Nat, SC.length(A, S.from_list(~A, ~cmp, ys, Nil{})), SC.length(A, ys), Equal.trans(Nat, SC.length(A, S.from_list(~A, ~cmp, ys, Nil{})), Nat.add(SC.length(A, ys), 0n), SC.length(A, ys), BG.len_from_list(~A, ~cmp, ys, Nil{}), N.add_zero(SC.length(A, ys)))),
        SP.le_add_zero(SC.length(A, ys), SC.length(A, xs)))
    case E.ToSortedList{}:
      SP.le_same(SC.length(A, xs))

# ---- projections of a step ----

def so_sh(~A: Data, ~cmp: A -> A -> Cmp, -sh: ST.Shadow<A>, -op: E.Op<A>, so: SP.StepOK(~A, ~cmp, sh, op)) -> ST.Shadow<A>:
  match so:
    case Tuple{sh2, r}:
      sh2

def so_obs(~A: Data, ~cmp: A -> A -> Cmp, -sh: ST.Shadow<A>, -op: E.Op<A>, so: SP.StepOK(~A, ~cmp, sh, op)) -> E.Obs<A>:
  match so:
    case Tuple{sh2, Tuple{o, r}}:
      o

def so_step(~A: Data, ~cmp: A -> A -> Cmp, -sh: ST.Shadow<A>, -op: E.Op<A>, so: SP.StepOK(~A, ~cmp, sh, op)) -> {H.step(~A, ~cmp, ST.real(~A, sh), op) == (ST.real(~A, so_sh(~A, ~cmp, sh, op, so)), so_obs(~A, ~cmp, sh, op, so)) : H.Heap<A> & E.Obs<A>}:
  match so:
    case Tuple{sh2, Tuple{o, Tuple{e, r}}}:
      e

def so_good(~A: Data, ~cmp: A -> A -> Cmp, -sh: ST.Shadow<A>, -op: E.Op<A>, so: SP.StepOK(~A, ~cmp, sh, op)) -> {ST.good(~A, ~cmp, so_sh(~A, ~cmp, sh, op, so)) == True{} : Bool}:
  match so:
    case Tuple{sh2, Tuple{o, Tuple{e, Tuple{g, s}}}}:
      g

def so_spec(~A: Data, ~cmp: A -> A -> Cmp, -sh: ST.Shadow<A>, -op: E.Op<A>, so: SP.StepOK(~A, ~cmp, sh, op)) -> {(ST.model(~A, ~cmp, so_sh(~A, ~cmp, sh, op, so)), so_obs(~A, ~cmp, sh, op, so)) == S.step(~A, ~cmp, ST.model(~A, ~cmp, sh), op) : List<&2, A> & E.Obs<A>}:
  match so:
    case Tuple{sh2, Tuple{o, Tuple{e, Tuple{g, Tuple{s, dd}}}}}:
      s

def so_depth(~A: Data, ~cmp: A -> A -> Cmp, -sh: ST.Shadow<A>, -op: E.Op<A>, so: SP.StepOK(~A, ~cmp, sh, op)) -> {Nat.is_le(ST.sh_depth(~A, so_sh(~A, ~cmp, sh, op, so)), Nat.add(ST.sh_depth(~A, sh), SP.pushcost(~A, op))) == True{} : Bool}:
  match so:
    case Tuple{sh2, Tuple{o, Tuple{e, Tuple{g, Tuple{s, dd}}}}}:
      dd

# the size grows by at most the step's push count
def so_size(~A: Data, ~cmp: A -> A -> Cmp, +sh: ST.Shadow<A>, +op: E.Op<A>, +g: {ST.good(~A, ~cmp, sh) == True{} : Bool}, so: SP.StepOK(~A, ~cmp, sh, op)) -> {Nat.is_le(ST.sh_size(~A, so_sh(~A, ~cmp, sh, op, so)), Nat.add(ST.sh_size(~A, sh), SP.pushcost(~A, op))) == True{} : Bool}:
  match so:
    case Tuple{sh2, Tuple{o, Tuple{e, Tuple{g2, Tuple{sp, dd}}}}}:
      +m1 = Pair.fst(List<&2, A>, E.Obs<A>, S.step(~A, ~cmp, ST.model(~A, ~cmp, sh), op))
      +el = Equal.trans(Nat, ST.sh_size(~A, sh2), SC.length(A, ST.model(~A, ~cmp, sh2)), SC.length(A, m1),
        BG.sz_len(~A, ~cmp, sh2, g2),
        Equal.cong(List<&2, A> & E.Obs<A>, Nat, pr => SC.length(A, Pair.fst(List<&2, A>, E.Obs<A>, pr)), (ST.model(~A, ~cmp, sh2), o), S.step(~A, ~cmp, ST.model(~A, ~cmp, sh), op), sp))
      L.subst(Nat, z => {Nat.is_le(z, Nat.add(ST.sh_size(~A, sh), SP.pushcost(~A, op))) == True{} : Bool}, SC.length(A, m1), ST.sh_size(~A, sh2), Equal.sym(Nat, ST.sh_size(~A, sh2), SC.length(A, m1), el),
        L.subst(Nat, z => {Nat.is_le(SC.length(A, m1), Nat.add(z, SP.pushcost(~A, op))) == True{} : Bool}, SC.length(A, ST.model(~A, ~cmp, sh)), ST.sh_size(~A, sh), Equal.sym(Nat, ST.sh_size(~A, sh), SC.length(A, ST.model(~A, ~cmp, sh)), BG.sz_len(~A, ~cmp, sh, g)),
          slen_step(~A, ~cmp, ST.model(~A, ~cmp, sh), op)))

# ---- the run ----

def srun_obs(~A: Data, ~cmp: A -> A -> Cmp, ops: List<&2, E.Op<A>>, m: List<&2, A>) -> List<&2, E.Obs<A>>:
  Pair.snd(List<&2, A>, List<&2, E.Obs<A>>, S.run(~A, ~cmp, ops, m))

def srun_state(~A: Data, ~cmp: A -> A -> Cmp, ops: List<&2, E.Op<A>>, m: List<&2, A>) -> List<&2, A>:
  Pair.fst(List<&2, A>, List<&2, E.Obs<A>>, S.run(~A, ~cmp, ops, m))

def spec_run_cons(~A: Data, ~cmp: A -> A -> Cmp, +op: E.Op<A>, +rest: List<&2, E.Op<A>>, +m: List<&2, A>, +m1: List<&2, A>, +o: E.Obs<A>, +e: {(m1, o) == S.step(~A, ~cmp, m, op) : List<&2, A> & E.Obs<A>}) -> {S.run(~A, ~cmp, Con{op, rest}, m) == (srun_state(~A, ~cmp, rest, m1), Con{o, srun_obs(~A, ~cmp, rest, m1)}) : List<&2, A> & List<&2, E.Obs<A>>}:
  %e : {S.cons_obs(A, Pair.snd(List<&2, A>, E.Obs<A>, _), S.run(~A, ~cmp, rest, Pair.fst(List<&2, A>, E.Obs<A>, _))) == (srun_state(~A, ~cmp, rest, m1), Con{o, srun_obs(~A, ~cmp, rest, m1)}) : List<&2, A> & List<&2, E.Obs<A>>}
  %Equal.sym(List<&2, A> & List<&2, E.Obs<A>>, S.run(~A, ~cmp, rest, m1), (srun_state(~A, ~cmp, rest, m1), srun_obs(~A, ~cmp, rest, m1)), L.pair_eta(List<&2, A>, List<&2, E.Obs<A>>, S.run(~A, ~cmp, rest, m1))) : {S.cons_obs(A, o, _) == (srun_state(~A, ~cmp, rest, m1), Con{o, srun_obs(~A, ~cmp, rest, m1)}) : List<&2, A> & List<&2, E.Obs<A>>}
  {==}

def RunOK(~A: Data, ~cmp: A -> A -> Cmp, ops: List<&2, E.Op<A>>, sh: ST.Shadow<A>, acc: List<&2, E.Obs<A>>) -> Type:
  Sigma<&1, &1, ST.Shadow<A>, sh2 => {H.run_acc(~A, ~cmp, ops, (ST.real(~A, sh), acc)) == (ST.real(~A, sh2), List.reverse.go(&2, E.Obs<A>, srun_obs(~A, ~cmp, ops, ST.model(~A, ~cmp, sh)), acc)) : H.Heap<A> & List<&2, E.Obs<A>>} & ({ST.good(~A, ~cmp, sh2) == True{} : Bool} & {ST.model(~A, ~cmp, sh2) == srun_state(~A, ~cmp, ops, ST.model(~A, ~cmp, sh)) : List<&2, A>})>

def ro_sh(~A: Data, ~cmp: A -> A -> Cmp, -ops: List<&2, E.Op<A>>, -sh: ST.Shadow<A>, -acc: List<&2, E.Obs<A>>, r: RunOK(~A, ~cmp, ops, sh, acc)) -> ST.Shadow<A>:
  match r:
    case Tuple{sh2, x}:
      sh2

def ro_run(~A: Data, ~cmp: A -> A -> Cmp, -ops: List<&2, E.Op<A>>, -sh: ST.Shadow<A>, -acc: List<&2, E.Obs<A>>, r: RunOK(~A, ~cmp, ops, sh, acc)) -> {H.run_acc(~A, ~cmp, ops, (ST.real(~A, sh), acc)) == (ST.real(~A, ro_sh(~A, ~cmp, ops, sh, acc, r)), List.reverse.go(&2, E.Obs<A>, srun_obs(~A, ~cmp, ops, ST.model(~A, ~cmp, sh)), acc)) : H.Heap<A> & List<&2, E.Obs<A>>}:
  match r:
    case Tuple{sh2, Tuple{e, x}}:
      e

def ro_good(~A: Data, ~cmp: A -> A -> Cmp, -ops: List<&2, E.Op<A>>, -sh: ST.Shadow<A>, -acc: List<&2, E.Obs<A>>, r: RunOK(~A, ~cmp, ops, sh, acc)) -> {ST.good(~A, ~cmp, ro_sh(~A, ~cmp, ops, sh, acc, r)) == True{} : Bool}:
  match r:
    case Tuple{sh2, Tuple{e, Tuple{g, m}}}:
      g

def ro_model(~A: Data, ~cmp: A -> A -> Cmp, -ops: List<&2, E.Op<A>>, -sh: ST.Shadow<A>, -acc: List<&2, E.Obs<A>>, r: RunOK(~A, ~cmp, ops, sh, acc)) -> {ST.model(~A, ~cmp, ro_sh(~A, ~cmp, ops, sh, acc, r)) == srun_state(~A, ~cmp, ops, ST.model(~A, ~cmp, sh)) : List<&2, A>}:
  match r:
    case Tuple{sh2, Tuple{e, Tuple{g, m}}}:
      m

def run_ok(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +ops: List<&2, E.Op<A>>, +sh: ST.Shadow<A>, +acc: List<&2, E.Obs<A>>, +g: {ST.good(~A, ~cmp, sh) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +room: {Nat.is_lt(Nat.add(ST.sh_size(~A, sh), pushes(~A, ops)), SC.pow2(q)) == True{} : Bool}) -> RunOK(~A, ~cmp, ops, sh, acc):
  match ops:
    case Nil{}:
      (sh, ({==}, (g, {==})))
    case Con{+op, +rest}:
      +m = ST.model(~A, ~cmp, sh)
      +hh = budget_head(~A, ST.sh_size(~A, sh), op, rest, q, room)
      +sh1 = so_sh(~A, ~cmp, sh, op, SP.step_ok(~A, ~cmp, ~o, sh, op, g, q, hq, hh))
      +ob = so_obs(~A, ~cmp, sh, op, SP.step_ok(~A, ~cmp, ~o, sh, op, g, q, hq, hh))
      +g1 = so_good(~A, ~cmp, sh, op, SP.step_ok(~A, ~cmp, ~o, sh, op, g, q, hq, hh))
      +r1 = budget_tail(~A, ST.sh_size(~A, sh), ST.sh_size(~A, sh1), op, rest, q, so_size(~A, ~cmp, sh, op, g, SP.step_ok(~A, ~cmp, ~o, sh, op, g, q, hq, hh)), room)
      +m1 = ST.model(~A, ~cmp, sh1)
      +acc1 = {Con{ob, acc} : List<&2, E.Obs<A>>}
      +sh2 = ro_sh(~A, ~cmp, rest, sh1, acc1, run_ok(~A, ~cmp, ~o, rest, sh1, acc1, g1, q, hq, r1))
      +es = spec_run_cons(~A, ~cmp, op, rest, m, m1, ob, so_spec(~A, ~cmp, sh, op, SP.step_ok(~A, ~cmp, ~o, sh, op, g, q, hq, hh)))
      -R = S.run(~A, ~cmp, rest, m1)
      (sh2, (
        %Equal.sym(H.Heap<A> & E.Obs<A>, H.step(~A, ~cmp, ST.real(~A, sh), op), (ST.real(~A, sh1), ob), so_step(~A, ~cmp, sh, op, SP.step_ok(~A, ~cmp, ~o, sh, op, g, q, hq, hh))) : {H.run_acc(~A, ~cmp, rest, H.record(~A, acc, _)) == (ST.real(~A, sh2), List.reverse.go(&2, E.Obs<A>, srun_obs(~A, ~cmp, Con{op, rest}, m), acc)) : H.Heap<A> & List<&2, E.Obs<A>>}
        %Equal.sym(H.Heap<A> & List<&2, E.Obs<A>>, H.run_acc(~A, ~cmp, rest, (ST.real(~A, sh1), acc1)), (ST.real(~A, sh2), List.reverse.go(&2, E.Obs<A>, srun_obs(~A, ~cmp, rest, m1), acc1)), ro_run(~A, ~cmp, rest, sh1, acc1, run_ok(~A, ~cmp, ~o, rest, sh1, acc1, g1, q, hq, r1))) : {_ == (ST.real(~A, sh2), List.reverse.go(&2, E.Obs<A>, srun_obs(~A, ~cmp, Con{op, rest}, m), acc)) : H.Heap<A> & List<&2, E.Obs<A>>}
        %Equal.sym(List<&2, A> & List<&2, E.Obs<A>>, S.run(~A, ~cmp, Con{op, rest}, m), (Pair.fst(List<&2, A>, List<&2, E.Obs<A>>, R), Con{ob, Pair.snd(List<&2, A>, List<&2, E.Obs<A>>, R)}), es) : {(ST.real(~A, sh2), List.reverse.go(&2, E.Obs<A>, srun_obs(~A, ~cmp, rest, m1), acc1)) == (ST.real(~A, sh2), List.reverse.go(&2, E.Obs<A>, Pair.snd(List<&2, A>, List<&2, E.Obs<A>>, _), acc)) : H.Heap<A> & List<&2, E.Obs<A>>}
        {==},
        (ro_good(~A, ~cmp, rest, sh1, acc1, run_ok(~A, ~cmp, ~o, rest, sh1, acc1, g1, q, hq, r1)),
         %Equal.sym(List<&2, A> & List<&2, E.Obs<A>>, S.run(~A, ~cmp, Con{op, rest}, m), (Pair.fst(List<&2, A>, List<&2, E.Obs<A>>, R), Con{ob, Pair.snd(List<&2, A>, List<&2, E.Obs<A>>, R)}), es) : {ST.model(~A, ~cmp, sh2) == Pair.fst(List<&2, A>, List<&2, E.Obs<A>>, _) : List<&2, A>}
         ro_model(~A, ~cmp, rest, sh1, acc1, run_ok(~A, ~cmp, ~o, rest, sh1, acc1, g1, q, hq, r1)))))

def run_from(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +ops: List<&2, E.Op<A>>, +sh0: ST.Shadow<A>, +g0: {ST.good(~A, ~cmp, sh0) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +room: {Nat.is_lt(Nat.add(ST.sh_size(~A, sh0), pushes(~A, ops)), SC.pow2(q)) == True{} : Bool}) -> {H.run(~A, ~cmp, ops, ST.real(~A, sh0)) == (ST.real(~A, ro_sh(~A, ~cmp, ops, sh0, Nil{}, run_ok(~A, ~cmp, ~o, ops, sh0, Nil{}, g0, q, hq, room))), srun_obs(~A, ~cmp, ops, ST.model(~A, ~cmp, sh0))) : H.Heap<A> & List<&2, E.Obs<A>>}:
  +sh2 = ro_sh(~A, ~cmp, ops, sh0, Nil{}, run_ok(~A, ~cmp, ~o, ops, sh0, Nil{}, g0, q, hq, room))
  +os = srun_obs(~A, ~cmp, ops, ST.model(~A, ~cmp, sh0))
  %Equal.sym(H.Heap<A> & List<&2, E.Obs<A>>, H.run_acc(~A, ~cmp, ops, (ST.real(~A, sh0), Nil{})), (ST.real(~A, sh2), List.reverse.go(&2, E.Obs<A>, os, Nil{})), ro_run(~A, ~cmp, ops, sh0, Nil{}, run_ok(~A, ~cmp, ~o, ops, sh0, Nil{}, g0, q, hq, room))) : {H.finish(~A, _) == (ST.real(~A, sh2), os) : H.Heap<A> & List<&2, E.Obs<A>>}
  %Equal.sym(List<&2, E.Obs<A>>, List.reverse(&2, E.Obs<A>, List.reverse.go(&2, E.Obs<A>, os, Nil{})), os, LL.rev_rev(E.Obs<A>, os)) : {(ST.real(~A, sh2), _) == (ST.real(~A, sh2), os) : H.Heap<A> & List<&2, E.Obs<A>>}
  {==}

def TraceOK(~A: Data, ~cmp: A -> A -> Cmp, ops: List<&2, E.Op<A>>, sh0: ST.Shadow<A>) -> Type:
  Sigma<&1, &1, ST.Shadow<A>, sh2 => {H.run(~A, ~cmp, ops, ST.real(~A, sh0)) == (ST.real(~A, sh2), srun_obs(~A, ~cmp, ops, ST.model(~A, ~cmp, sh0))) : H.Heap<A> & List<&2, E.Obs<A>>} & ({ST.good(~A, ~cmp, sh2) == True{} : Bool} & {ST.model(~A, ~cmp, sh2) == srun_state(~A, ~cmp, ops, ST.model(~A, ~cmp, sh0)) : List<&2, A>})>

def trace_from(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +ops: List<&2, E.Op<A>>, +sh0: ST.Shadow<A>, +g0: {ST.good(~A, ~cmp, sh0) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +room: {Nat.is_lt(Nat.add(ST.sh_size(~A, sh0), pushes(~A, ops)), SC.pow2(q)) == True{} : Bool}) -> TraceOK(~A, ~cmp, ops, sh0):
  (ro_sh(~A, ~cmp, ops, sh0, Nil{}, run_ok(~A, ~cmp, ~o, ops, sh0, Nil{}, g0, q, hq, room)),
   (run_from(~A, ~cmp, ~o, ops, sh0, g0, q, hq, room),
    (ro_good(~A, ~cmp, ops, sh0, Nil{}, run_ok(~A, ~cmp, ~o, ops, sh0, Nil{}, g0, q, hq, room)),
     ro_model(~A, ~cmp, ops, sh0, Nil{}, run_ok(~A, ~cmp, ~o, ops, sh0, Nil{}, g0, q, hq, room)))))
