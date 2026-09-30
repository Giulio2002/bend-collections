import Base
import ../../../spec/lib/common.bend as SC
import ../../lib/array.bend as AR
import ../../lib/list.bend as LL
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../../src/crypto/blake/blake2b/types.bend as T
import ../../../src/crypto/argon2/types.bend as A
import ../../../src/crypto/argon2/sub.bend as SB
import ../../../src/crypto/argon2/access.bend as X
import ../../../src/crypto/argon2/memory.bend as M
import ../../../spec/crypto/argon2/argon2.bend as SA
import ./memory.bend as MEM
import ./access.bend as XP

# Reading and writing block b of the memory of a list of blocks mem
# (memory.bend's mirror tree thaw(mt(d, mem))) with M.get / M.set, which
# read and write the block row by row (access.bend).

# ---------------------------------------------------------------- reading

def drop_add(+xs: List<&2, U32>, +k: Nat, +j: Nat) -> {SC.drop(U32, xs, Nat.add(k, j)) == SC.drop(U32, SC.drop(U32, xs, j), k) : List<&2, U32>}:
  match xs j:
    case Nil{} _:
      match k:
        case 0n:
          {==}
        case 1n+p:
          {==}
    case Con{+h, +t} 0n:
      Equal.cong(Nat, List<&2, U32>, z => SC.drop(U32, Con{h, t}, z), Nat.add(k, 0n), k, N.add_zero(k))
    case Con{+h, +t} 1n+ +p:
      %Equal.sym(Nat, Nat.add(k, 1n+p), 1n+Nat.add(k, p), N.add_succ(k, p)) : {SC.drop(U32, Con{h, t}, _) == SC.drop(U32, SC.drop(U32, t, p), k) : List<&2, U32>}
      drop_add(t, k, p)

# The words of a block, row after row: rows r .. 7 of the block, then e.
def tail(+r0: T.State, +r1: T.State, +r2: T.State, +r3: T.State, +r4: T.State, +r5: T.State, +r6: T.State, +r7: T.State, +e: List<&2, U32>, +r: Nat) -> List<&2, U32>:
  match r:
    case 0n:
      SC.append(U32, SB.app(SB.row_words(r0), SB.app(SB.row_words(r1), SB.app(SB.row_words(r2), SB.app(SB.row_words(r3), SB.app(SB.row_words(r4), SB.app(SB.row_words(r5), SB.app(SB.row_words(r6), SB.app(SB.row_words(r7), Nil{})))))))), e)
    case 1n:
      SC.append(U32, SB.app(SB.row_words(r1), SB.app(SB.row_words(r2), SB.app(SB.row_words(r3), SB.app(SB.row_words(r4), SB.app(SB.row_words(r5), SB.app(SB.row_words(r6), SB.app(SB.row_words(r7), Nil{}))))))), e)
    case 2n:
      SC.append(U32, SB.app(SB.row_words(r2), SB.app(SB.row_words(r3), SB.app(SB.row_words(r4), SB.app(SB.row_words(r5), SB.app(SB.row_words(r6), SB.app(SB.row_words(r7), Nil{})))))), e)
    case 3n:
      SC.append(U32, SB.app(SB.row_words(r3), SB.app(SB.row_words(r4), SB.app(SB.row_words(r5), SB.app(SB.row_words(r6), SB.app(SB.row_words(r7), Nil{}))))), e)
    case 4n:
      SC.append(U32, SB.app(SB.row_words(r4), SB.app(SB.row_words(r5), SB.app(SB.row_words(r6), SB.app(SB.row_words(r7), Nil{})))), e)
    case 5n:
      SC.append(U32, SB.app(SB.row_words(r5), SB.app(SB.row_words(r6), SB.app(SB.row_words(r7), Nil{}))), e)
    case 6n:
      SC.append(U32, SB.app(SB.row_words(r6), SB.app(SB.row_words(r7), Nil{})), e)
    case _:
      SC.append(U32, SB.app(SB.row_words(r7), Nil{}), e)

# Rows r and r + 1 of the words from word 32 r of block i on.
def next_row(+ws: List<&2, U32>, +i: Nat, +k: Nat, +y: List<&2, U32>, +h: {SC.drop(U32, ws, Nat.add(k, i)) == y : List<&2, U32>}) -> {SC.drop(U32, ws, Nat.add(32n, Nat.add(k, i))) == SC.drop(U32, y, 32n) : List<&2, U32>}:
  Equal.trans(List<&2, U32>, SC.drop(U32, ws, Nat.add(32n, Nat.add(k, i))), SC.drop(U32, SC.drop(U32, ws, Nat.add(k, i)), 32n), SC.drop(U32, y, 32n),
    drop_add(ws, 32n, Nat.add(k, i)),
    Equal.cong(List<&2, U32>, List<&2, U32>, z => SC.drop(U32, z, 32n), SC.drop(U32, ws, Nat.add(k, i)), y, h))

# The eight rows read from word i on are the rows of g, when ws from word i
# on is g's words then e.
def blk_eq(+ws: List<&2, U32>, +i: Nat, +g: A.Block, +e: List<&2, U32>, +h: {SC.drop(U32, ws, i) == SC.append(U32, SB.words(g), e) : List<&2, U32>}) -> {A.B{XP.rowl(SC.drop(U32, ws, i)), XP.rowl(SC.drop(U32, ws, Nat.add(32n, i))), XP.rowl(SC.drop(U32, ws, Nat.add(64n, i))), XP.rowl(SC.drop(U32, ws, Nat.add(96n, i))), XP.rowl(SC.drop(U32, ws, Nat.add(128n, i))), XP.rowl(SC.drop(U32, ws, Nat.add(160n, i))), XP.rowl(SC.drop(U32, ws, Nat.add(192n, i))), XP.rowl(SC.drop(U32, ws, Nat.add(224n, i)))} == g : A.Block}:
  match g:
    case A.B{+r0, +r1, +r2, +r3, +r4, +r5, +r6, +r7}:
      +e0 = Equal.cong(Nat, List<&2, U32>, z => SC.drop(U32, ws, z), Nat.add(0n, i), i, {==})
      +d0 = Equal.trans(List<&2, U32>, SC.drop(U32, ws, Nat.add(0n, i)), SC.drop(U32, ws, i), tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 0n), e0, h)
      +d1 = Equal.trans(List<&2, U32>, SC.drop(U32, ws, Nat.add(32n, i)), SC.drop(U32, tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 0n), 32n), tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 1n), next_row(ws, i, 0n, tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 0n), d0), XP.drop_row(r0, SB.app(SB.row_words(r1), SB.app(SB.row_words(r2), SB.app(SB.row_words(r3), SB.app(SB.row_words(r4), SB.app(SB.row_words(r5), SB.app(SB.row_words(r6), SB.app(SB.row_words(r7), Nil{}))))))), e))
      +d2 = Equal.trans(List<&2, U32>, SC.drop(U32, ws, Nat.add(64n, i)), SC.drop(U32, tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 1n), 32n), tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 2n), next_row(ws, i, 32n, tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 1n), d1), XP.drop_row(r1, SB.app(SB.row_words(r2), SB.app(SB.row_words(r3), SB.app(SB.row_words(r4), SB.app(SB.row_words(r5), SB.app(SB.row_words(r6), SB.app(SB.row_words(r7), Nil{})))))), e))
      +d3 = Equal.trans(List<&2, U32>, SC.drop(U32, ws, Nat.add(96n, i)), SC.drop(U32, tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 2n), 32n), tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 3n), next_row(ws, i, 64n, tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 2n), d2), XP.drop_row(r2, SB.app(SB.row_words(r3), SB.app(SB.row_words(r4), SB.app(SB.row_words(r5), SB.app(SB.row_words(r6), SB.app(SB.row_words(r7), Nil{}))))), e))
      +d4 = Equal.trans(List<&2, U32>, SC.drop(U32, ws, Nat.add(128n, i)), SC.drop(U32, tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 3n), 32n), tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 4n), next_row(ws, i, 96n, tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 3n), d3), XP.drop_row(r3, SB.app(SB.row_words(r4), SB.app(SB.row_words(r5), SB.app(SB.row_words(r6), SB.app(SB.row_words(r7), Nil{})))), e))
      +d5 = Equal.trans(List<&2, U32>, SC.drop(U32, ws, Nat.add(160n, i)), SC.drop(U32, tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 4n), 32n), tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 5n), next_row(ws, i, 128n, tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 4n), d4), XP.drop_row(r4, SB.app(SB.row_words(r5), SB.app(SB.row_words(r6), SB.app(SB.row_words(r7), Nil{}))), e))
      +d6 = Equal.trans(List<&2, U32>, SC.drop(U32, ws, Nat.add(192n, i)), SC.drop(U32, tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 5n), 32n), tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 6n), next_row(ws, i, 160n, tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 5n), d5), XP.drop_row(r5, SB.app(SB.row_words(r6), SB.app(SB.row_words(r7), Nil{})), e))
      +d7 = Equal.trans(List<&2, U32>, SC.drop(U32, ws, Nat.add(224n, i)), SC.drop(U32, tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 6n), 32n), tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 7n), next_row(ws, i, 192n, tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 6n), d6), XP.drop_row(r6, SB.app(SB.row_words(r7), Nil{}), e))
      -goal = {A.B{r0, r1, r2, r3, r4, r5, r6, r7} : A.Block}
      %Equal.sym(List<&2, U32>, SC.drop(U32, ws, i), tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 0n), h) : {A.B{XP.rowl(_), XP.rowl(SC.drop(U32, ws, Nat.add(32n, i))), XP.rowl(SC.drop(U32, ws, Nat.add(64n, i))), XP.rowl(SC.drop(U32, ws, Nat.add(96n, i))), XP.rowl(SC.drop(U32, ws, Nat.add(128n, i))), XP.rowl(SC.drop(U32, ws, Nat.add(160n, i))), XP.rowl(SC.drop(U32, ws, Nat.add(192n, i))), XP.rowl(SC.drop(U32, ws, Nat.add(224n, i)))} == goal : A.Block}
      %Equal.sym(List<&2, U32>, SC.drop(U32, ws, Nat.add(32n, i)), tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 1n), d1) : {A.B{XP.rowl(tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 0n)), XP.rowl(_), XP.rowl(SC.drop(U32, ws, Nat.add(64n, i))), XP.rowl(SC.drop(U32, ws, Nat.add(96n, i))), XP.rowl(SC.drop(U32, ws, Nat.add(128n, i))), XP.rowl(SC.drop(U32, ws, Nat.add(160n, i))), XP.rowl(SC.drop(U32, ws, Nat.add(192n, i))), XP.rowl(SC.drop(U32, ws, Nat.add(224n, i)))} == goal : A.Block}
      %Equal.sym(List<&2, U32>, SC.drop(U32, ws, Nat.add(64n, i)), tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 2n), d2) : {A.B{XP.rowl(tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 0n)), XP.rowl(tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 1n)), XP.rowl(_), XP.rowl(SC.drop(U32, ws, Nat.add(96n, i))), XP.rowl(SC.drop(U32, ws, Nat.add(128n, i))), XP.rowl(SC.drop(U32, ws, Nat.add(160n, i))), XP.rowl(SC.drop(U32, ws, Nat.add(192n, i))), XP.rowl(SC.drop(U32, ws, Nat.add(224n, i)))} == goal : A.Block}
      %Equal.sym(List<&2, U32>, SC.drop(U32, ws, Nat.add(96n, i)), tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 3n), d3) : {A.B{XP.rowl(tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 0n)), XP.rowl(tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 1n)), XP.rowl(tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 2n)), XP.rowl(_), XP.rowl(SC.drop(U32, ws, Nat.add(128n, i))), XP.rowl(SC.drop(U32, ws, Nat.add(160n, i))), XP.rowl(SC.drop(U32, ws, Nat.add(192n, i))), XP.rowl(SC.drop(U32, ws, Nat.add(224n, i)))} == goal : A.Block}
      %Equal.sym(List<&2, U32>, SC.drop(U32, ws, Nat.add(128n, i)), tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 4n), d4) : {A.B{XP.rowl(tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 0n)), XP.rowl(tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 1n)), XP.rowl(tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 2n)), XP.rowl(tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 3n)), XP.rowl(_), XP.rowl(SC.drop(U32, ws, Nat.add(160n, i))), XP.rowl(SC.drop(U32, ws, Nat.add(192n, i))), XP.rowl(SC.drop(U32, ws, Nat.add(224n, i)))} == goal : A.Block}
      %Equal.sym(List<&2, U32>, SC.drop(U32, ws, Nat.add(160n, i)), tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 5n), d5) : {A.B{XP.rowl(tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 0n)), XP.rowl(tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 1n)), XP.rowl(tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 2n)), XP.rowl(tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 3n)), XP.rowl(tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 4n)), XP.rowl(_), XP.rowl(SC.drop(U32, ws, Nat.add(192n, i))), XP.rowl(SC.drop(U32, ws, Nat.add(224n, i)))} == goal : A.Block}
      %Equal.sym(List<&2, U32>, SC.drop(U32, ws, Nat.add(192n, i)), tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 6n), d6) : {A.B{XP.rowl(tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 0n)), XP.rowl(tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 1n)), XP.rowl(tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 2n)), XP.rowl(tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 3n)), XP.rowl(tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 4n)), XP.rowl(tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 5n)), XP.rowl(_), XP.rowl(SC.drop(U32, ws, Nat.add(224n, i)))} == goal : A.Block}
      %Equal.sym(List<&2, U32>, SC.drop(U32, ws, Nat.add(224n, i)), tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 7n), d7) : {A.B{XP.rowl(tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 0n)), XP.rowl(tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 1n)), XP.rowl(tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 2n)), XP.rowl(tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 3n)), XP.rowl(tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 4n)), XP.rowl(tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 5n)), XP.rowl(tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 6n)), XP.rowl(_)} == goal : A.Block}
      %Equal.sym(T.State, XP.rowl(tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 0n)), r0, XP.rowl_app(r0, SB.app(SB.row_words(r1), SB.app(SB.row_words(r2), SB.app(SB.row_words(r3), SB.app(SB.row_words(r4), SB.app(SB.row_words(r5), SB.app(SB.row_words(r6), SB.app(SB.row_words(r7), Nil{}))))))), e)) : {A.B{_, XP.rowl(tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 1n)), XP.rowl(tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 2n)), XP.rowl(tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 3n)), XP.rowl(tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 4n)), XP.rowl(tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 5n)), XP.rowl(tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 6n)), XP.rowl(tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 7n))} == goal : A.Block}
      %Equal.sym(T.State, XP.rowl(tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 1n)), r1, XP.rowl_app(r1, SB.app(SB.row_words(r2), SB.app(SB.row_words(r3), SB.app(SB.row_words(r4), SB.app(SB.row_words(r5), SB.app(SB.row_words(r6), SB.app(SB.row_words(r7), Nil{})))))), e)) : {A.B{r0, _, XP.rowl(tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 2n)), XP.rowl(tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 3n)), XP.rowl(tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 4n)), XP.rowl(tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 5n)), XP.rowl(tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 6n)), XP.rowl(tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 7n))} == goal : A.Block}
      %Equal.sym(T.State, XP.rowl(tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 2n)), r2, XP.rowl_app(r2, SB.app(SB.row_words(r3), SB.app(SB.row_words(r4), SB.app(SB.row_words(r5), SB.app(SB.row_words(r6), SB.app(SB.row_words(r7), Nil{}))))), e)) : {A.B{r0, r1, _, XP.rowl(tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 3n)), XP.rowl(tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 4n)), XP.rowl(tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 5n)), XP.rowl(tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 6n)), XP.rowl(tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 7n))} == goal : A.Block}
      %Equal.sym(T.State, XP.rowl(tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 3n)), r3, XP.rowl_app(r3, SB.app(SB.row_words(r4), SB.app(SB.row_words(r5), SB.app(SB.row_words(r6), SB.app(SB.row_words(r7), Nil{})))), e)) : {A.B{r0, r1, r2, _, XP.rowl(tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 4n)), XP.rowl(tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 5n)), XP.rowl(tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 6n)), XP.rowl(tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 7n))} == goal : A.Block}
      %Equal.sym(T.State, XP.rowl(tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 4n)), r4, XP.rowl_app(r4, SB.app(SB.row_words(r5), SB.app(SB.row_words(r6), SB.app(SB.row_words(r7), Nil{}))), e)) : {A.B{r0, r1, r2, r3, _, XP.rowl(tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 5n)), XP.rowl(tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 6n)), XP.rowl(tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 7n))} == goal : A.Block}
      %Equal.sym(T.State, XP.rowl(tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 5n)), r5, XP.rowl_app(r5, SB.app(SB.row_words(r6), SB.app(SB.row_words(r7), Nil{})), e)) : {A.B{r0, r1, r2, r3, r4, _, XP.rowl(tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 6n)), XP.rowl(tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 7n))} == goal : A.Block}
      %Equal.sym(T.State, XP.rowl(tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 6n)), r6, XP.rowl_app(r6, SB.app(SB.row_words(r7), Nil{}), e)) : {A.B{r0, r1, r2, r3, r4, r5, _, XP.rowl(tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 7n))} == goal : A.Block}
      %Equal.sym(T.State, XP.rowl(tail(r0, r1, r2, r3, r4, r5, r6, r7, e, 7n)), r7, XP.rowl_app(r7, Nil{}, e)) : {A.B{r0, r1, r2, r3, r4, r5, r6, _} == goal : A.Block}
      {==}

# Reading block b of the memory of mem.
def get_block(+d: Nat, +mem: List<&2, A.Block>, +b: Nat, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hc: {Nat.is_le(Nat.mul(SC.length(A.Block, mem), 256n), SC.pow2(d)) == True{} : Bool}, +hb: {Nat.is_lt(b, SC.length(A.Block, mem)) == True{} : Bool}) -> {M.get(b, AR.thaw(U32, MEM.mt(d, mem))) == (AR.thaw(U32, MEM.mt(d, mem)), SA.get(mem, b)) : Array<U32> & A.Block}:
  +ws = MEM.W(d, mem)
  +i = Nat.mul(b, 256n)
  +g = SA.get(mem, b)
  -ar = AR.thaw(U32, MEM.mt(d, mem))
  +hle = N.le_trans(Nat.add(i, 256n), Nat.mul(SC.length(A.Block, mem), 256n), SC.pow2(d), MEM.mul_lt(b, SC.length(A.Block, mem), hb), hc)
  +h = L.subst(Nat, z => {Nat.is_le(z, SC.pow2(d)) == True{} : Bool}, Nat.add(i, 256n), Nat.add(256n, i), N.add_comm(i, 256n), hle)
  +e = SC.drop(U32, SC.drop(U32, ws, i), 256n)
  +hdrop = Equal.trans(List<&2, U32>, SC.drop(U32, ws, i), SC.append(U32, SC.take(U32, SC.drop(U32, ws, i), 256n), e), SC.append(U32, SB.words(g), e),
    Equal.sym(List<&2, U32>, SC.append(U32, SC.take(U32, SC.drop(U32, ws, i), 256n), e), SC.drop(U32, ws, i), MEM.take_drop(SC.drop(U32, ws, i), 256n)),
    Equal.cong(List<&2, U32>, List<&2, U32>, z => SC.append(U32, z, e), SC.take(U32, SC.drop(U32, ws, i), 256n), SB.words(g), MEM.slice_W(d, mem, b, hb)))
  %Equal.sym(Array<U32> & A.Block, X.get(b, ar), (ar, A.B{XP.rowl(SC.drop(U32, ws, i)), XP.rowl(SC.drop(U32, ws, Nat.add(32n, i))), XP.rowl(SC.drop(U32, ws, Nat.add(64n, i))), XP.rowl(SC.drop(U32, ws, Nat.add(96n, i))), XP.rowl(SC.drop(U32, ws, Nat.add(128n, i))), XP.rowl(SC.drop(U32, ws, Nat.add(160n, i))), XP.rowl(SC.drop(U32, ws, Nat.add(192n, i))), XP.rowl(SC.drop(U32, ws, Nat.add(224n, i)))}), XP.get_eq(d, ws, b, hd, MEM.W_len(d, mem, hc), h)) : {_ == (ar, g) : Array<U32> & A.Block}
  Equal.cong(A.Block, Array<U32> & A.Block, z => (ar, z), A.B{XP.rowl(SC.drop(U32, ws, i)), XP.rowl(SC.drop(U32, ws, Nat.add(32n, i))), XP.rowl(SC.drop(U32, ws, Nat.add(64n, i))), XP.rowl(SC.drop(U32, ws, Nat.add(96n, i))), XP.rowl(SC.drop(U32, ws, Nat.add(128n, i))), XP.rowl(SC.drop(U32, ws, Nat.add(160n, i))), XP.rowl(SC.drop(U32, ws, Nat.add(192n, i))), XP.rowl(SC.drop(U32, ws, Nat.add(224n, i)))}, g, blk_eq(ws, i, g, e, hdrop))

# ---------------------------------------------------------------- writing

# Writing block b of the memory of mem.
def set_block(+d: Nat, +mem: List<&2, A.Block>, +b: Nat, +v: A.Block, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hc: {Nat.is_le(Nat.mul(SC.length(A.Block, mem), 256n), SC.pow2(d)) == True{} : Bool}, +hb: {Nat.is_lt(b, SC.length(A.Block, mem)) == True{} : Bool}) -> {M.set(b, v, AR.thaw(U32, MEM.mt(d, mem))) == AR.thaw(U32, MEM.mt(d, SA.set(mem, b, v))) : Array<U32>}:
  +hi = L.subst(Nat, z => {Nat.is_le(Nat.add(Nat.mul(b, 256n), z), SC.pow2(d)) == True{} : Bool}, 256n, SC.length(U32, SB.words(v)), Equal.sym(Nat, SC.length(U32, SB.words(v)), 256n, MEM.words_len(v)), N.le_trans(Nat.add(Nat.mul(b, 256n), 256n), Nat.mul(SC.length(A.Block, mem), 256n), SC.pow2(d), MEM.mul_lt(b, SC.length(A.Block, mem), hb), hc))
  Equal.trans(Array<U32>, X.put(b, v, AR.thaw(U32, MEM.tree(d, MEM.W(d, mem)))), MEM.wr(SB.words(v), Nat.mul(b, 256n), AR.thaw(U32, MEM.tree(d, MEM.W(d, mem)))), AR.thaw(U32, MEM.mt(d, SA.set(mem, b, v))),
    XP.put_eq(b, v, AR.thaw(U32, MEM.tree(d, MEM.W(d, mem)))),
    Equal.trans(Array<U32>, MEM.wr(SB.words(v), Nat.mul(b, 256n), AR.thaw(U32, MEM.tree(d, MEM.W(d, mem)))), AR.thaw(U32, MEM.tree(d, MEM.splice(SB.words(v), Nat.mul(b, 256n), MEM.W(d, mem)))), AR.thaw(U32, MEM.mt(d, SA.set(mem, b, v))),
      MEM.wr_words(d, SB.words(v), Nat.mul(b, 256n), MEM.W(d, mem), hd, MEM.W_len(d, mem, hc), hi),
      Equal.cong(List<&2, U32>, Array<U32>, z => AR.thaw(U32, MEM.tree(d, z)), MEM.splice(SB.words(v), Nat.mul(b, 256n), MEM.W(d, mem)), MEM.W(d, SA.set(mem, b, v)), MEM.W_splice(d, mem, b, v, hb))))
