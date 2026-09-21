import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/array.bend as AR
import ../../spec/common.bend as SC
import ../../spec/graph.bend as GS
import ../../src/graph.bend as G
import ../../types/graph.bend as E
import ./state.bend as ST
import ./gstep.bend as GT
import ./rmedge.bend as RM
import ./addedge.bend as AE
import ./addv3.bend as AV3
import ./rmv3.bend as RV3

# Every operation, and arbitrary finite traces, of the indexed graph.
#
# The room premise is the representation's capacity condition. mu(sh) is the
# window size plus the maximum degree; every add_vertex / add_edge raises it
# by at most one, every other operation does not raise it. Keeping
# 3 + mu below 2^q with q <= 30 guarantees that a full vertex table
# (2^depth slots) or a full adjacency block (2^lcap words) can still double
# within 2^31 words, the index range of Base's arrays.

def step_ok(sh: ST.Shadow, +op: E.Op, +h: {ST.good(sh) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 30n) == True{} : Bool}, +hroom: {Nat.is_lt(Nat.add(3n, GT.mu(sh)), SC.pow2(q)) == True{} : Bool}) -> GT.StepOK(sh, op):
  match sh:
    case ST.Sh{+dir, +lo, +hi, +depth, +it, +at}:
      match op:
        case E.AddVertex{+v}:
          AV3.so_add_vertex(dir, lo, hi, depth, it, at, v, h, q, hq, hroom)
        case E.RemoveVertex{+v}:
          RV3.so_remove_vertex(dir, lo, hi, depth, it, at, v, h)
        case E.AddEdge{+u, +v}:
          AE.so_add_edge(dir, lo, hi, depth, it, at, u, v, h, q, hq, hroom)
        case E.RemoveEdge{+u, +v}:
          RM.so_remove_edge(dir, lo, hi, depth, it, at, u, v, h)
        case E.HasVertex{+v}:
          GT.so_has_vertex(dir, lo, hi, depth, it, at, v, h)
        case E.HasEdge{+u, +v}:
          GT.so_has_edge(dir, lo, hi, depth, it, at, u, v, h)
        case E.Neighbors{+v}:
          GT.so_neighbors(dir, lo, hi, depth, it, at, v, h)
        case E.Vertices{}:
          GT.so_vertices(dir, lo, hi, depth, it, at, h)
        case E.Edges{}:
          GT.so_edges(dir, lo, hi, depth, it, at, h)

# ---- projections of a step ----

def so_sh(-sh: ST.Shadow, -op: E.Op, so: GT.StepOK(sh, op)) -> ST.Shadow:
  match so:
    case Tuple{sh2, r}:
      sh2

def so_obs(-sh: ST.Shadow, -op: E.Op, so: GT.StepOK(sh, op)) -> E.Obs:
  match so:
    case Tuple{sh2, Tuple{o, r}}:
      o

def so_step(-sh: ST.Shadow, -op: E.Op, so: GT.StepOK(sh, op)) -> {G.step(ST.real(sh), op) == (ST.real(so_sh(sh, op, so)), so_obs(sh, op, so)) : G.Graph & E.Obs}:
  match so:
    case Tuple{sh2, Tuple{o, Tuple{e, r}}}:
      e

def so_good(-sh: ST.Shadow, -op: E.Op, so: GT.StepOK(sh, op)) -> {ST.good(so_sh(sh, op, so)) == True{} : Bool}:
  match so:
    case Tuple{sh2, Tuple{o, Tuple{e, Tuple{g, s}}}}:
      g

def so_spec(-sh: ST.Shadow, -op: E.Op, so: GT.StepOK(sh, op)) -> {(ST.model(so_sh(sh, op, so)), so_obs(sh, op, so)) == GS.step(ST.model(sh), op) : GS.Model & E.Obs}:
  match so:
    case Tuple{sh2, Tuple{o, Tuple{e, Tuple{g, Tuple{s, m}}}}}:
      s

def so_mu(-sh: ST.Shadow, -op: E.Op, so: GT.StepOK(sh, op)) -> {Nat.is_le(GT.mu(so_sh(sh, op, so)), Nat.add(GT.mu(sh), GT.cost(op))) == True{} : Bool}:
  match so:
    case Tuple{sh2, Tuple{o, Tuple{e, Tuple{g, Tuple{s, m}}}}}:
      m

# ---- the room budget of a trace ----

def adds(ops: List<&2, E.Op>) -> Nat:
  match ops:
    case Nil{}:
      0n
    case Con{op, rest}:
      Nat.add(GT.cost(op), adds(rest))

def add_le_l(+a: Nat, +b: Nat, +c: Nat, +h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(Nat.add(a, c), Nat.add(b, c)) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(a, c), Nat.add(c, a), N.add_comm(a, c)) : {Nat.is_le(_, Nat.add(b, c)) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(b, c), Nat.add(c, b), N.add_comm(b, c)) : {Nat.is_le(Nat.add(c, a), _) == True{} : Bool}
  N.le_add_left(a, b, c, h)

def budget_head(+m: Nat, +op: E.Op, +rest: List<&2, E.Op>, +q: Nat, +h: {Nat.is_lt(Nat.add(3n, Nat.add(m, adds(Con{op, rest}))), SC.pow2(q)) == True{} : Bool}) -> {Nat.is_lt(Nat.add(3n, m), SC.pow2(q)) == True{} : Bool}:
  N.le_lt_trans(Nat.add(3n, m), Nat.add(3n, Nat.add(m, adds(Con{op, rest}))), SC.pow2(q), N.le_add_left(m, Nat.add(m, adds(Con{op, rest})), 3n, N.le_add_right(m, adds(Con{op, rest}))), h)

def budget_tail(+m: Nat, +m1: Nat, +op: E.Op, +rest: List<&2, E.Op>, +q: Nat, +hm: {Nat.is_le(m1, Nat.add(m, GT.cost(op))) == True{} : Bool}, +h: {Nat.is_lt(Nat.add(3n, Nat.add(m, adds(Con{op, rest}))), SC.pow2(q)) == True{} : Bool}) -> {Nat.is_lt(Nat.add(3n, Nat.add(m1, adds(rest))), SC.pow2(q)) == True{} : Bool}:
  N.le_lt_trans(Nat.add(3n, Nat.add(m1, adds(rest))), Nat.add(3n, Nat.add(m, adds(Con{op, rest}))), SC.pow2(q),
    N.le_add_left(Nat.add(m1, adds(rest)), Nat.add(m, adds(Con{op, rest})), 3n,
      L.subst(Nat, z => {Nat.is_le(Nat.add(m1, adds(rest)), z) == True{} : Bool}, Nat.add(Nat.add(m, GT.cost(op)), adds(rest)), Nat.add(m, adds(Con{op, rest})), N.add_assoc(m, GT.cost(op), adds(rest)),
        add_le_l(m1, Nat.add(m, GT.cost(op)), adds(rest), hm))),
    h)

# ---- the run ----

def srun_obs(ops: List<&2, E.Op>, m: GS.Model) -> List<&2, E.Obs>:
  Pair.snd(GS.Model, List<&2, E.Obs>, GS.run(ops, m))

def srun_state(ops: List<&2, E.Op>, m: GS.Model) -> GS.Model:
  Pair.fst(GS.Model, List<&2, E.Obs>, GS.run(ops, m))

def spec_run_cons(+op: E.Op, +rest: List<&2, E.Op>, +m: GS.Model, +m1: GS.Model, +o: E.Obs, +e: {(m1, o) == GS.step(m, op) : GS.Model & E.Obs}) -> {GS.run(Con{op, rest}, m) == (srun_state(rest, m1), Con{o, srun_obs(rest, m1)}) : GS.Model & List<&2, E.Obs>}:
  %e : {GS.cons_obs(Pair.snd(GS.Model, E.Obs, _), GS.run(rest, Pair.fst(GS.Model, E.Obs, _))) == (srun_state(rest, m1), Con{o, srun_obs(rest, m1)}) : GS.Model & List<&2, E.Obs>}
  %Equal.sym(GS.Model & List<&2, E.Obs>, GS.run(rest, m1), (srun_state(rest, m1), srun_obs(rest, m1)), L.pair_eta(GS.Model, List<&2, E.Obs>, GS.run(rest, m1))) : {GS.cons_obs(o, _) == (srun_state(rest, m1), Con{o, srun_obs(rest, m1)}) : GS.Model & List<&2, E.Obs>}
  {==}

def RunOK(ops: List<&2, E.Op>, sh: ST.Shadow, acc: List<&2, E.Obs>) -> Type:
  Sigma<&1, &1, ST.Shadow, sh2 => {G.run_acc(ops, (ST.real(sh), acc)) == (ST.real(sh2), List.reverse.go(&2, E.Obs, srun_obs(ops, ST.model(sh)), acc)) : G.Graph & List<&2, E.Obs>} & ({ST.good(sh2) == True{} : Bool} & {ST.model(sh2) == srun_state(ops, ST.model(sh)) : GS.Model})>

def ro_sh(-ops: List<&2, E.Op>, -sh: ST.Shadow, -acc: List<&2, E.Obs>, r: RunOK(ops, sh, acc)) -> ST.Shadow:
  match r:
    case Tuple{sh2, x}:
      sh2

def ro_run(-ops: List<&2, E.Op>, -sh: ST.Shadow, -acc: List<&2, E.Obs>, r: RunOK(ops, sh, acc)) -> {G.run_acc(ops, (ST.real(sh), acc)) == (ST.real(ro_sh(ops, sh, acc, r)), List.reverse.go(&2, E.Obs, srun_obs(ops, ST.model(sh)), acc)) : G.Graph & List<&2, E.Obs>}:
  match r:
    case Tuple{sh2, Tuple{e, x}}:
      e

def ro_good(-ops: List<&2, E.Op>, -sh: ST.Shadow, -acc: List<&2, E.Obs>, r: RunOK(ops, sh, acc)) -> {ST.good(ro_sh(ops, sh, acc, r)) == True{} : Bool}:
  match r:
    case Tuple{sh2, Tuple{e, Tuple{g, m}}}:
      g

def ro_model(-ops: List<&2, E.Op>, -sh: ST.Shadow, -acc: List<&2, E.Obs>, r: RunOK(ops, sh, acc)) -> {ST.model(ro_sh(ops, sh, acc, r)) == srun_state(ops, ST.model(sh)) : GS.Model}:
  match r:
    case Tuple{sh2, Tuple{e, Tuple{g, m}}}:
      m

def run_ok(+ops: List<&2, E.Op>, +sh: ST.Shadow, +acc: List<&2, E.Obs>, +g: {ST.good(sh) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 30n) == True{} : Bool}, +room: {Nat.is_lt(Nat.add(3n, Nat.add(GT.mu(sh), adds(ops))), SC.pow2(q)) == True{} : Bool}) -> RunOK(ops, sh, acc):
  match ops:
    case Nil{}:
      (sh, ({==}, (g, {==})))
    case Con{+op, +rest}:
      +m = ST.model(sh)
      +hh = budget_head(GT.mu(sh), op, rest, q, room)
      +sh1 = so_sh(sh, op, step_ok(sh, op, g, q, hq, hh))
      +ob = so_obs(sh, op, step_ok(sh, op, g, q, hq, hh))
      +g1 = so_good(sh, op, step_ok(sh, op, g, q, hq, hh))
      +r1 = budget_tail(GT.mu(sh), GT.mu(sh1), op, rest, q, so_mu(sh, op, step_ok(sh, op, g, q, hq, hh)), room)
      +m1 = ST.model(sh1)
      +acc1 = {Con{ob, acc} : List<&2, E.Obs>}
      +sh2 = ro_sh(rest, sh1, acc1, run_ok(rest, sh1, acc1, g1, q, hq, r1))
      +es = spec_run_cons(op, rest, m, m1, ob, so_spec(sh, op, step_ok(sh, op, g, q, hq, hh)))
      -R = GS.run(rest, m1)
      (sh2, (
        %Equal.sym(G.Graph & E.Obs, G.step(ST.real(sh), op), (ST.real(sh1), ob), so_step(sh, op, step_ok(sh, op, g, q, hq, hh))) : {G.run_acc(rest, G.record(acc, _)) == (ST.real(sh2), List.reverse.go(&2, E.Obs, srun_obs(Con{op, rest}, m), acc)) : G.Graph & List<&2, E.Obs>}
        %Equal.sym(G.Graph & List<&2, E.Obs>, G.run_acc(rest, (ST.real(sh1), acc1)), (ST.real(sh2), List.reverse.go(&2, E.Obs, srun_obs(rest, m1), acc1)), ro_run(rest, sh1, acc1, run_ok(rest, sh1, acc1, g1, q, hq, r1))) : {_ == (ST.real(sh2), List.reverse.go(&2, E.Obs, srun_obs(Con{op, rest}, m), acc)) : G.Graph & List<&2, E.Obs>}
        %Equal.sym(GS.Model & List<&2, E.Obs>, GS.run(Con{op, rest}, m), (Pair.fst(GS.Model, List<&2, E.Obs>, R), Con{ob, Pair.snd(GS.Model, List<&2, E.Obs>, R)}), es) : {(ST.real(sh2), List.reverse.go(&2, E.Obs, srun_obs(rest, m1), acc1)) == (ST.real(sh2), List.reverse.go(&2, E.Obs, Pair.snd(GS.Model, List<&2, E.Obs>, _), acc)) : G.Graph & List<&2, E.Obs>}
        {==},
        (ro_good(rest, sh1, acc1, run_ok(rest, sh1, acc1, g1, q, hq, r1)),
         %Equal.sym(GS.Model & List<&2, E.Obs>, GS.run(Con{op, rest}, m), (Pair.fst(GS.Model, List<&2, E.Obs>, R), Con{ob, Pair.snd(GS.Model, List<&2, E.Obs>, R)}), es) : {ST.model(sh2) == Pair.fst(GS.Model, List<&2, E.Obs>, _) : GS.Model}
         ro_model(rest, sh1, acc1, run_ok(rest, sh1, acc1, g1, q, hq, r1)))))

def run_from(+ops: List<&2, E.Op>, +sh0: ST.Shadow, +g0: {ST.good(sh0) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 30n) == True{} : Bool}, +room: {Nat.is_lt(Nat.add(3n, Nat.add(GT.mu(sh0), adds(ops))), SC.pow2(q)) == True{} : Bool}) -> {G.run(ops, ST.real(sh0)) == (ST.real(ro_sh(ops, sh0, Nil{}, run_ok(ops, sh0, Nil{}, g0, q, hq, room))), srun_obs(ops, ST.model(sh0))) : G.Graph & List<&2, E.Obs>}:
  +sh2 = ro_sh(ops, sh0, Nil{}, run_ok(ops, sh0, Nil{}, g0, q, hq, room))
  +os = srun_obs(ops, ST.model(sh0))
  %Equal.sym(G.Graph & List<&2, E.Obs>, G.run_acc(ops, (ST.real(sh0), Nil{})), (ST.real(sh2), List.reverse.go(&2, E.Obs, os, Nil{})), ro_run(ops, sh0, Nil{}, run_ok(ops, sh0, Nil{}, g0, q, hq, room))) : {G.finish(_) == (ST.real(sh2), os) : G.Graph & List<&2, E.Obs>}
  %Equal.sym(List<&2, E.Obs>, List.reverse(&2, E.Obs, List.reverse.go(&2, E.Obs, os, Nil{})), os, LL.rev_rev(E.Obs, os)) : {(ST.real(sh2), _) == (ST.real(sh2), os) : G.Graph & List<&2, E.Obs>}
  {==}

def TraceOK(ops: List<&2, E.Op>, sh0: ST.Shadow) -> Type:
  Sigma<&1, &1, ST.Shadow, sh2 => {G.run(ops, ST.real(sh0)) == (ST.real(sh2), srun_obs(ops, ST.model(sh0))) : G.Graph & List<&2, E.Obs>} & ({ST.good(sh2) == True{} : Bool} & {ST.model(sh2) == srun_state(ops, ST.model(sh0)) : GS.Model})>

def trace_from(+ops: List<&2, E.Op>, +sh0: ST.Shadow, +g0: {ST.good(sh0) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 30n) == True{} : Bool}, +room: {Nat.is_lt(Nat.add(3n, Nat.add(GT.mu(sh0), adds(ops))), SC.pow2(q)) == True{} : Bool}) -> TraceOK(ops, sh0):
  (ro_sh(ops, sh0, Nil{}, run_ok(ops, sh0, Nil{}, g0, q, hq, room)),
   (run_from(ops, sh0, g0, q, hq, room),
    (ro_good(ops, sh0, Nil{}, run_ok(ops, sh0, Nil{}, g0, q, hq, room)),
     ro_model(ops, sh0, Nil{}, run_ok(ops, sh0, Nil{}, g0, q, hq, room)))))

# Traces from the real constructor, in both modes.
def TraceNew(d: Bool, ops: List<&2, E.Op>) -> Type:
  Sigma<&1, &1, ST.Shadow, sh2 => {G.run(ops, G.new(d)) == (ST.real(sh2), srun_obs(ops, GS.new(d))) : G.Graph & List<&2, E.Obs>} & ({ST.good(sh2) == True{} : Bool} & {ST.model(sh2) == srun_state(ops, GS.new(d)) : GS.Model})>

def tn_of(+d: Bool, +ops: List<&2, E.Op>, t: TraceOK(ops, ST.empty_shadow(d))) -> TraceNew(d, ops):
  match t:
    case Tuple{sh2, Tuple{e, rest}}:
      (sh2, (Equal.trans(G.Graph & List<&2, E.Obs>, G.run(ops, G.new(d)), G.run(ops, ST.real(ST.empty_shadow(d))), (ST.real(sh2), srun_obs(ops, GS.new(d))),
        Equal.cong(G.Graph, G.Graph & List<&2, E.Obs>, z => G.run(ops, z), G.new(d), ST.real(ST.empty_shadow(d)), ST.new_real(d)), e), rest))

def trace_new(+d: Bool, +ops: List<&2, E.Op>, +q: Nat, +hq: {Nat.is_le(q, 30n) == True{} : Bool}, +room: {Nat.is_lt(Nat.add(3n, adds(ops)), SC.pow2(q)) == True{} : Bool}) -> TraceNew(d, ops):
  tn_of(d, ops, trace_from(ops, ST.empty_shadow(d), ST.new_good(d), q, hq, room))
