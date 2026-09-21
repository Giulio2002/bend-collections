import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/array.bend as AR
import ../../spec/common.bend as SC
import ../../spec/lru_fast.bend as S
import ../../src/lru/fast.bend as F
import ../../types/lru_model.bend as T
import ../../types/lru_fast.bend as E
import ./state.bend as ST
import ./steps.bend as SP
import ./capstep.bend as CS

# Operation traces: from any good shadow whose capacity is within 2^q (q <= 31),
# along any trace whose Resize capacities are within 2^q, the runtime run is
# the abstraction of a good shadow, its observations are the spec's, and the
# final model is the spec's final state. Traces from the real constructor
# follow (init(cap) is the abstraction of the initial shadow).

def scap_model(~V: Data, sh: ST.Shadow<V>) -> {SP.scap(V, sh) == CS.mcap(V, ST.model(~V, sh)) : U32}:
  match sh:
    case ST.Sh{cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl}:
      {==}

def cb(-V: Data, +q: Nat, sh: ST.Shadow<V>) -> Bool:
  Nat.is_le(U32.to_nat(SP.scap(V, sh)), SC.pow2(q))

def step_ok(~V: Data, sh: ST.Shadow<V>, +op: E.Op<V>, +h: {ST.good(~V, sh) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +hc: {cb(V, q, sh) == True{} : Bool}) -> SP.StepOK(~V, sh, op):
  match sh:
    case ST.Sh{+cap, +fresh, +depth, +life, +tc, +table, +tk, +te, +tp, +tn, +ord, +fl}:
      match op:
        case E.Len{}:
          SP.len_ok(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h)
        case E.Capacity{}:
          SP.cap_ok(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h)
        case E.SetLifetime{+ns}:
          SP.life_ok(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, ns, h)
        case E.Metrics{}:
          SP.metrics_ok(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h)
        case E.Add{+key, +v, +now}:
          SP.add_ok(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, v, now, h, q, hq, hc)
        case E.Get{+key, +now}:
          SP.get_ok(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, now, h)
        case E.Peek{+key, +now}:
          SP.peek_ok(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, now, h)
        case E.Contains{+key, +now}:
          SP.contains_ok(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, now, h)
        case E.Remove{+key}:
          SP.remove_ok(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, key, h)
        case E.Purge{}:
          SP.purge_ok(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, h)
        case E.Resize{+c}:
          SP.resize_ok(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, c, h)
        case E.Keys{+now}:
          SP.keys_ok(~V, cap, fresh, depth, life, tc, table, tk, te, tp, tn, ord, fl, now, h)

# ---- projections of a step ----

def so_sh(~V: Data, -sh: ST.Shadow<V>, -op: E.Op<V>, so: SP.StepOK(~V, sh, op)) -> ST.Shadow<V>:
  match so:
    case Tuple{sh2, r}:
      sh2

def so_obs(~V: Data, -sh: ST.Shadow<V>, -op: E.Op<V>, so: SP.StepOK(~V, sh, op)) -> E.Obs<V>:
  match so:
    case Tuple{sh2, Tuple{o, r}}:
      o

def so_step(~V: Data, -sh: ST.Shadow<V>, -op: E.Op<V>, so: SP.StepOK(~V, sh, op)) -> {F.step(~V, ST.real(~V, sh), op) == (ST.real(~V, so_sh(~V, sh, op, so)), so_obs(~V, sh, op, so)) : F.Fast<V> & E.Obs<V>}:
  match so:
    case Tuple{sh2, Tuple{o, Tuple{e, r}}}:
      e

def so_good(~V: Data, -sh: ST.Shadow<V>, -op: E.Op<V>, so: SP.StepOK(~V, sh, op)) -> {ST.good(~V, so_sh(~V, sh, op, so)) == True{} : Bool}:
  match so:
    case Tuple{sh2, Tuple{o, Tuple{e, Tuple{g, s}}}}:
      g

def so_spec(~V: Data, -sh: ST.Shadow<V>, -op: E.Op<V>, so: SP.StepOK(~V, sh, op)) -> {(ST.model(~V, so_sh(~V, sh, op, so)), so_obs(~V, sh, op, so)) == S.step(V, ST.model(~V, sh), op) : S.Model<V> & E.Obs<V>}:
  match so:
    case Tuple{sh2, Tuple{o, Tuple{e, Tuple{g, s}}}}:
      s

# the capacity bound after a step, through the model
def so_cap(~V: Data, +sh: ST.Shadow<V>, +op: E.Op<V>, +g: {ST.good(~V, sh) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +hc: {cb(V, q, sh) == True{} : Bool}, +hop: {CS.op_ok(V, q, op) == True{} : Bool}) -> {cb(V, q, so_sh(~V, sh, op, step_ok(~V, sh, op, g, q, hq, hc))) == True{} : Bool}:
  +sh2 = so_sh(~V, sh, op, step_ok(~V, sh, op, g, q, hq, hc))
  +em = Equal.cong(S.Model<V> & E.Obs<V>, S.Model<V>, p => Pair.fst(S.Model<V>, E.Obs<V>, p), (ST.model(~V, sh2), so_obs(~V, sh, op, step_ok(~V, sh, op, g, q, hq, hc))), S.step(V, ST.model(~V, sh), op), so_spec(~V, sh, op, step_ok(~V, sh, op, g, q, hq, hc)))
  +hm = L.subst(U32, z => {Nat.is_le(U32.to_nat(z), SC.pow2(q)) == True{} : Bool}, SP.scap(V, sh), CS.mcap(V, ST.model(~V, sh)), scap_model(~V, sh), hc)
  +r = CS.cap_step(V, ST.model(~V, sh), op, q, hm, hop)
  +r2 = L.subst(S.Model<V>, z => {Nat.is_le(U32.to_nat(CS.mcap(V, z)), SC.pow2(q)) == True{} : Bool}, CS.fst_o(V, S.step(V, ST.model(~V, sh), op)), ST.model(~V, sh2), Equal.sym(S.Model<V>, ST.model(~V, sh2), CS.fst_o(V, S.step(V, ST.model(~V, sh), op)), em), r)
  L.subst(U32, z => {Nat.is_le(U32.to_nat(z), SC.pow2(q)) == True{} : Bool}, CS.mcap(V, ST.model(~V, sh2)), SP.scap(V, sh2), Equal.sym(U32, SP.scap(V, sh2), CS.mcap(V, ST.model(~V, sh2)), scap_model(~V, sh2)), r2)

# ---- the trace premise ----

def all_ok(-V: Data, +q: Nat, ops: List<&2, E.Op<V>>) -> Bool:
  match ops:
    case Nil{}:
      True{}
    case Con{op, rest}:
      Bool.and(CS.op_ok(V, q, op), all_ok(V, q, rest))

# ---- the run ----

def srun_obs(-V: Data, ops: List<&2, E.Op<V>>, m: S.Model<V>) -> List<&2, E.Obs<V>>:
  Pair.snd(S.Model<V>, List<&2, E.Obs<V>>, S.run(V, ops, m))

def srun_state(-V: Data, ops: List<&2, E.Op<V>>, m: S.Model<V>) -> S.Model<V>:
  Pair.fst(S.Model<V>, List<&2, E.Obs<V>>, S.run(V, ops, m))

def spec_run_cons(-V: Data, +op: E.Op<V>, +rest: List<&2, E.Op<V>>, +m: S.Model<V>, +m1: S.Model<V>, +o: E.Obs<V>, +e: {(m1, o) == S.step(V, m, op) : S.Model<V> & E.Obs<V>}) -> {S.run(V, Con{op, rest}, m) == (srun_state(V, rest, m1), Con{o, srun_obs(V, rest, m1)}) : S.Model<V> & List<&2, E.Obs<V>>}:
  %e : {S.cons_obs(V, Pair.snd(S.Model<V>, E.Obs<V>, _), S.run(V, rest, Pair.fst(S.Model<V>, E.Obs<V>, _))) == (srun_state(V, rest, m1), Con{o, srun_obs(V, rest, m1)}) : S.Model<V> & List<&2, E.Obs<V>>}
  %Equal.sym(S.Model<V> & List<&2, E.Obs<V>>, S.run(V, rest, m1), (srun_state(V, rest, m1), srun_obs(V, rest, m1)), L.pair_eta(S.Model<V>, List<&2, E.Obs<V>>, S.run(V, rest, m1))) : {S.cons_obs(V, o, _) == (srun_state(V, rest, m1), Con{o, srun_obs(V, rest, m1)}) : S.Model<V> & List<&2, E.Obs<V>>}
  {==}

def RunOK(~V: Data, ops: List<&2, E.Op<V>>, sh: ST.Shadow<V>, acc: List<&2, E.Obs<V>>) -> Type:
  Sigma<&1, &1, ST.Shadow<V>, sh2 => {F.run_acc(~V, ops, (ST.real(~V, sh), acc)) == (ST.real(~V, sh2), List.reverse.go(&2, E.Obs<V>, srun_obs(V, ops, ST.model(~V, sh)), acc)) : F.Fast<V> & List<&2, E.Obs<V>>} & ({ST.good(~V, sh2) == True{} : Bool} & {ST.model(~V, sh2) == srun_state(V, ops, ST.model(~V, sh)) : S.Model<V>})>

def ro_sh(~V: Data, -ops: List<&2, E.Op<V>>, -sh: ST.Shadow<V>, -acc: List<&2, E.Obs<V>>, r: RunOK(~V, ops, sh, acc)) -> ST.Shadow<V>:
  match r:
    case Tuple{sh2, x}:
      sh2

def ro_run(~V: Data, -ops: List<&2, E.Op<V>>, -sh: ST.Shadow<V>, -acc: List<&2, E.Obs<V>>, r: RunOK(~V, ops, sh, acc)) -> {F.run_acc(~V, ops, (ST.real(~V, sh), acc)) == (ST.real(~V, ro_sh(~V, ops, sh, acc, r)), List.reverse.go(&2, E.Obs<V>, srun_obs(V, ops, ST.model(~V, sh)), acc)) : F.Fast<V> & List<&2, E.Obs<V>>}:
  match r:
    case Tuple{sh2, Tuple{e, x}}:
      e

def ro_good(~V: Data, -ops: List<&2, E.Op<V>>, -sh: ST.Shadow<V>, -acc: List<&2, E.Obs<V>>, r: RunOK(~V, ops, sh, acc)) -> {ST.good(~V, ro_sh(~V, ops, sh, acc, r)) == True{} : Bool}:
  match r:
    case Tuple{sh2, Tuple{e, Tuple{g, m}}}:
      g

def ro_model(~V: Data, -ops: List<&2, E.Op<V>>, -sh: ST.Shadow<V>, -acc: List<&2, E.Obs<V>>, r: RunOK(~V, ops, sh, acc)) -> {ST.model(~V, ro_sh(~V, ops, sh, acc, r)) == srun_state(V, ops, ST.model(~V, sh)) : S.Model<V>}:
  match r:
    case Tuple{sh2, Tuple{e, Tuple{g, m}}}:
      m

def run_ok(~V: Data, +ops: List<&2, E.Op<V>>, +sh: ST.Shadow<V>, +acc: List<&2, E.Obs<V>>, +g: {ST.good(~V, sh) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +hc: {cb(V, q, sh) == True{} : Bool}, +hops: {all_ok(V, q, ops) == True{} : Bool}) -> RunOK(~V, ops, sh, acc):
  match ops:
    case Nil{}:
      (sh, ({==}, (g, {==})))
    case Con{+op, +rest}:
      +m = ST.model(~V, sh)
      +hop = L.and_left(CS.op_ok(V, q, op), all_ok(V, q, rest), hops)
      +hrest = L.and_right(CS.op_ok(V, q, op), all_ok(V, q, rest), hops)
      +sh1 = so_sh(~V, sh, op, step_ok(~V, sh, op, g, q, hq, hc))
      +ob = so_obs(~V, sh, op, step_ok(~V, sh, op, g, q, hq, hc))
      +g1 = so_good(~V, sh, op, step_ok(~V, sh, op, g, q, hq, hc))
      +hc1 = so_cap(~V, sh, op, g, q, hq, hc, hop)
      +m1 = ST.model(~V, sh1)
      +acc1 = {Con{ob, acc} : List<&2, E.Obs<V>>}
      +sh2 = ro_sh(~V, rest, sh1, acc1, run_ok(~V, rest, sh1, acc1, g1, q, hq, hc1, hrest))
      +es = spec_run_cons(V, op, rest, m, m1, ob, so_spec(~V, sh, op, step_ok(~V, sh, op, g, q, hq, hc)))
      -R = S.run(V, rest, m1)
      (sh2, (
        %Equal.sym(F.Fast<V> & E.Obs<V>, F.step(~V, ST.real(~V, sh), op), (ST.real(~V, sh1), ob), so_step(~V, sh, op, step_ok(~V, sh, op, g, q, hq, hc))) : {F.run_acc(~V, rest, F.record(~V, acc, _)) == (ST.real(~V, sh2), List.reverse.go(&2, E.Obs<V>, srun_obs(V, Con{op, rest}, m), acc)) : F.Fast<V> & List<&2, E.Obs<V>>}
        %Equal.sym(F.Fast<V> & List<&2, E.Obs<V>>, F.run_acc(~V, rest, (ST.real(~V, sh1), acc1)), (ST.real(~V, sh2), List.reverse.go(&2, E.Obs<V>, srun_obs(V, rest, m1), acc1)), ro_run(~V, rest, sh1, acc1, run_ok(~V, rest, sh1, acc1, g1, q, hq, hc1, hrest))) : {_ == (ST.real(~V, sh2), List.reverse.go(&2, E.Obs<V>, srun_obs(V, Con{op, rest}, m), acc)) : F.Fast<V> & List<&2, E.Obs<V>>}
        %Equal.sym(S.Model<V> & List<&2, E.Obs<V>>, S.run(V, Con{op, rest}, m), (Pair.fst(S.Model<V>, List<&2, E.Obs<V>>, R), Con{ob, Pair.snd(S.Model<V>, List<&2, E.Obs<V>>, R)}), es) : {(ST.real(~V, sh2), List.reverse.go(&2, E.Obs<V>, srun_obs(V, rest, m1), acc1)) == (ST.real(~V, sh2), List.reverse.go(&2, E.Obs<V>, Pair.snd(S.Model<V>, List<&2, E.Obs<V>>, _), acc)) : F.Fast<V> & List<&2, E.Obs<V>>}
        {==},
        (ro_good(~V, rest, sh1, acc1, run_ok(~V, rest, sh1, acc1, g1, q, hq, hc1, hrest)),
         %Equal.sym(S.Model<V> & List<&2, E.Obs<V>>, S.run(V, Con{op, rest}, m), (Pair.fst(S.Model<V>, List<&2, E.Obs<V>>, R), Con{ob, Pair.snd(S.Model<V>, List<&2, E.Obs<V>>, R)}), es) : {ST.model(~V, sh2) == Pair.fst(S.Model<V>, List<&2, E.Obs<V>>, _) : S.Model<V>}
         ro_model(~V, rest, sh1, acc1, run_ok(~V, rest, sh1, acc1, g1, q, hq, hc1, hrest)))))

def run_from(~V: Data, +ops: List<&2, E.Op<V>>, +sh0: ST.Shadow<V>, +g0: {ST.good(~V, sh0) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +hc: {cb(V, q, sh0) == True{} : Bool}, +hops: {all_ok(V, q, ops) == True{} : Bool}) -> {F.run(~V, ops, ST.real(~V, sh0)) == (ST.real(~V, ro_sh(~V, ops, sh0, Nil{}, run_ok(~V, ops, sh0, Nil{}, g0, q, hq, hc, hops))), srun_obs(V, ops, ST.model(~V, sh0))) : F.Fast<V> & List<&2, E.Obs<V>>}:
  +sh2 = ro_sh(~V, ops, sh0, Nil{}, run_ok(~V, ops, sh0, Nil{}, g0, q, hq, hc, hops))
  +os = srun_obs(V, ops, ST.model(~V, sh0))
  %Equal.sym(F.Fast<V> & List<&2, E.Obs<V>>, F.run_acc(~V, ops, (ST.real(~V, sh0), Nil{})), (ST.real(~V, sh2), List.reverse.go(&2, E.Obs<V>, os, Nil{})), ro_run(~V, ops, sh0, Nil{}, run_ok(~V, ops, sh0, Nil{}, g0, q, hq, hc, hops))) : {F.finish(~V, _) == (ST.real(~V, sh2), os) : F.Fast<V> & List<&2, E.Obs<V>>}
  %Equal.sym(List<&2, E.Obs<V>>, List.reverse(&2, E.Obs<V>, List.reverse.go(&2, E.Obs<V>, os, Nil{})), os, LL.rev_rev(E.Obs<V>, os)) : {(ST.real(~V, sh2), _) == (ST.real(~V, sh2), os) : F.Fast<V> & List<&2, E.Obs<V>>}
  {==}

def TraceOK(~V: Data, ops: List<&2, E.Op<V>>, sh0: ST.Shadow<V>) -> Type:
  Sigma<&1, &1, ST.Shadow<V>, sh2 => {F.run(~V, ops, ST.real(~V, sh0)) == (ST.real(~V, sh2), srun_obs(V, ops, ST.model(~V, sh0))) : F.Fast<V> & List<&2, E.Obs<V>>} & ({ST.good(~V, sh2) == True{} : Bool} & {ST.model(~V, sh2) == srun_state(V, ops, ST.model(~V, sh0)) : S.Model<V>})>

def trace_from(~V: Data, +ops: List<&2, E.Op<V>>, +sh0: ST.Shadow<V>, +g0: {ST.good(~V, sh0) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +hc: {cb(V, q, sh0) == True{} : Bool}, +hops: {all_ok(V, q, ops) == True{} : Bool}) -> TraceOK(~V, ops, sh0):
  (ro_sh(~V, ops, sh0, Nil{}, run_ok(~V, ops, sh0, Nil{}, g0, q, hq, hc, hops)),
   (run_from(~V, ops, sh0, g0, q, hq, hc, hops),
    (ro_good(~V, ops, sh0, Nil{}, run_ok(~V, ops, sh0, Nil{}, g0, q, hq, hc, hops)),
     ro_model(~V, ops, sh0, Nil{}, run_ok(~V, ops, sh0, Nil{}, g0, q, hq, hc, hops)))))

# Traces from the real constructor init(cap), cap positive and within 2^q.
def TraceNew(~V: Data, cap: U32, ops: List<&2, E.Op<V>>) -> Type:
  Sigma<&1, &1, ST.Shadow<V>, sh2 => {F.run(~V, ops, F.init(~V, cap)) == (ST.real(~V, sh2), srun_obs(V, ops, S.LM{cap, S.zero_time(), Nil{}, T.zero_metrics()})) : F.Fast<V> & List<&2, E.Obs<V>>} & ({ST.good(~V, sh2) == True{} : Bool} & {ST.model(~V, sh2) == srun_state(V, ops, S.LM{cap, S.zero_time(), Nil{}, T.zero_metrics()}) : S.Model<V>})>

def tn_of(~V: Data, +cap: U32, +ops: List<&2, E.Op<V>>, t: TraceOK(~V, ops, ST.initial(~V, cap))) -> TraceNew(~V, cap, ops):
  match t:
    case Tuple{sh2, Tuple{e, rest}}:
      (sh2, (Equal.trans(F.Fast<V> & List<&2, E.Obs<V>>, F.run(~V, ops, F.init(~V, cap)), F.run(~V, ops, ST.real(~V, ST.initial(~V, cap))), (ST.real(~V, sh2), srun_obs(V, ops, S.LM{cap, S.zero_time(), Nil{}, T.zero_metrics()})),
        Equal.cong(F.Fast<V>, F.Fast<V> & List<&2, E.Obs<V>>, z => F.run(~V, ops, z), F.init(~V, cap), ST.real(~V, ST.initial(~V, cap)), ST.new_real(~V, cap)), e), rest))

def trace_new(~V: Data, +cap: U32, +ops: List<&2, E.Op<V>>, +hc0: {U32.is_eq(cap, 0) == False{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +hc: {Nat.is_le(U32.to_nat(cap), SC.pow2(q)) == True{} : Bool}, +hops: {all_ok(V, q, ops) == True{} : Bool}) -> TraceNew(~V, cap, ops):
  tn_of(~V, cap, ops, trace_from(~V, ops, ST.initial(~V, cap), ST.new_good(~V, cap, hc0), q, hq, hc, hops))
