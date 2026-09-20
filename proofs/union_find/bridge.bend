import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../../spec/common.bend as SC
import ../../src/union_find.bend as U
import ./cells.bend as CL
import ./model.bend as M
import ./union.bend as UN

# Relinking the roots arena, read through the zip, is exactly the model's
# relinking of the record list.

def cells_rl(ms: List<&2, Nat>, +rs: List<&2, Nat>, +zs: List<&2, Nat>, +mls: List<&2, List<&2, Nat>>, +big: Nat) -> {CL.cells(CL.rlr(ms, rs, big), zs, mls) == UN.rl(ms, CL.cells(rs, zs, mls), big) : List<&2, CL.Cell>}:
  match ms:
    case Nil{}:
      {==}
    case Con{+m, +rest}:
      Equal.trans(List<&2, CL.Cell>, CL.cells(CL.rlr(rest, SC.update(Nat, rs, m, big), big), zs, mls), UN.rl(rest, CL.cells(SC.update(Nat, rs, m, big), zs, mls), big), UN.rl(rest, SC.update(CL.Cell, CL.cells(rs, zs, mls), m, CL.with_root(M.lc(CL.cells(rs, zs, mls), m), big)), big),
        cells_rl(rest, SC.update(Nat, rs, m, big), zs, mls, big),
        Equal.cong(List<&2, CL.Cell>, List<&2, CL.Cell>, w => UN.rl(rest, w, big),
          CL.cells(SC.update(Nat, rs, m, big), zs, mls),
          SC.update(CL.Cell, CL.cells(rs, zs, mls), m, CL.with_root(M.lc(CL.cells(rs, zs, mls), m), big)),
          CL.cells_set_root(rs, zs, mls, m, big, m)))
