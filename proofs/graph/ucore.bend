import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/u32.bend as U
import ../lib/array.bend as AR
import ../lib/array2.bend as A2
import ../../spec/common.bend as SC
import ../../spec/graph.bend as GS
import ../../src/graph.bend as G
import ../../types/balanced_search_tree.bend as BE
import ../../types/graph.bend as E
import ./state.bend as ST
import ./search.bend as SE
import ./window.bend as W
import ./lb.bend as LB
import ./ops.bend as OP
import ./edge.bend as ED
import ./gstep.bend as GT

# Operations whose result is `Result<Error, Unit>`: the core statement a
# case analysis proves, and its conversion into StepOK.

def UCore(sh: ST.Shadow, rt: G.Graph & Result<&2, &2, E.Error, Unit>, sp: GS.Model & E.Obs, +c: Nat) -> Type:
  Sigma<&1, &1, ST.Shadow, sh2 => Sigma<&1, &1, Result<&2, &2, E.Error, Unit>, res => {rt == (ST.real(sh2), res) : G.Graph & Result<&2, &2, E.Error, Unit>} & ({ST.good(sh2) == True{} : Bool} & ({(ST.model(sh2), E.OUnit{res}) == sp : GS.Model & E.Obs} & {Nat.is_le(GT.mu(sh2), Nat.add(GT.mu(sh), c)) == True{} : Bool}))>>

def uc_mk(-sh: ST.Shadow, -rt: G.Graph & Result<&2, &2, E.Error, Unit>, -sp: GS.Model & E.Obs, -c: Nat, sh2: ST.Shadow, res: Result<&2, &2, E.Error, Unit>, e1: {rt == (ST.real(sh2), res) : G.Graph & Result<&2, &2, E.Error, Unit>}, e2: {ST.good(sh2) == True{} : Bool}, e3: {(ST.model(sh2), E.OUnit{res}) == sp : GS.Model & E.Obs}, e4: {Nat.is_le(GT.mu(sh2), Nat.add(GT.mu(sh), c)) == True{} : Bool}) -> UCore(sh, rt, sp, c):
  (sh2, (res, (e1, (e2, (e3, e4)))))

# An operation that failed and left the state unchanged.
def uc_same(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, -rt: G.Graph & Result<&2, &2, E.Error, Unit>, -sp: GS.Model & E.Obs, +c: Nat, +err: E.Error, e1: {rt == (ST.real(ST.Sh{dir, lo, hi, depth, it, at}), Fail{err}) : G.Graph & Result<&2, &2, E.Error, Unit>}, e3: {(ST.model(ST.Sh{dir, lo, hi, depth, it, at}), E.OUnit{Fail{err}}) == sp : GS.Model & E.Obs}) -> UCore(ST.Sh{dir, lo, hi, depth, it, at}, rt, sp, c):
  uc_mk(ST.Sh{dir, lo, hi, depth, it, at}, rt, sp, c, ST.Sh{dir, lo, hi, depth, it, at}, Fail{err}, e1, h, e3, N.le_add_right(GT.mu(ST.Sh{dir, lo, hi, depth, it, at}), c))

# A core statement about the unit-result runtime operation gives StepOK.
def uc_step(-sh: ST.Shadow, -op: E.Op, -rt: G.Graph & Result<&2, &2, E.Error, Unit>, c: UCore(sh, rt, GS.step(ST.model(sh), op), GT.cost(op)), +hop: {G.step(ST.real(sh), op) == G.obs_unit(rt) : G.Graph & E.Obs}) -> GT.StepOK(sh, op):
  match c:
    case Tuple{sh2, Tuple{res, Tuple{e1, Tuple{e2, Tuple{e3, e4}}}}}:
      GT.mk(sh, op, sh2, E.OUnit{res},
        Equal.trans(G.Graph & E.Obs, G.step(ST.real(sh), op), G.obs_unit(rt), (ST.real(sh2), E.OUnit{res}), hop,
          Equal.cong(G.Graph & Result<&2, &2, E.Error, Unit>, G.Graph & E.Obs, z => G.obs_unit(z), rt, (ST.real(sh2), res), e1)),
        e2, e3, e4)
