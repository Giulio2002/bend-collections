import Base
import ../../../spec/lib/common.bend as SC
import ../../lib/array.bend as AR
import ../../lib/list.bend as LL
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/arith.bend as AR2
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../../math/natural/arith.bend as NR
import ../../../src/crypto/blake/blake2b/types.bend as T
import ../../../src/crypto/argon2/types.bend as A
import ../../../src/crypto/argon2/blamka.bend as G
import ../../../src/crypto/argon2/memory.bend as M
import ../../../src/crypto/argon2/argon2.bend as I
import ../../../spec/crypto/argon2/blamka.bend as SG
import ../../../spec/crypto/argon2/argon2.bend as SA
import ./blamka.bend as BL
import ./memory.bend as MEM
import ./hash.bend as HS
import ./fill.bend as F

# Argon2id of the implementation equals Argon2id of the specification for
# every input the implementation accepts: the first two blocks of every
# lane, the passes (fill.bend), the final XOR and H' of it.

# ---------------------------------------------------------------- the first blocks

def init_block_eq(+hh: List<&2, U32>, +i: Nat, +l: Nat) -> {I.block_of(I.hprime(1024n, I.cat(hh, I.cat(I.le32(i), I.le32(l))))) == SA.block_of(SA.hprime(1024n, SA.cat(hh, SA.cat(SA.le32(i), SA.le32(l))))) : A.Block}:
  +x = SA.cat(hh, SA.cat(SA.le32(i), SA.le32(l)))
  Equal.trans(A.Block, I.block_of(I.hprime(1024n, x)), I.block_of(SA.hprime(1024n, x)), SA.block_of(SA.hprime(1024n, x)),
    Equal.cong(List<&2, U32>, A.Block, z => I.block_of(z), I.hprime(1024n, x), SA.hprime(1024n, x), HS.hprime_eq(1024n, x)),
    HS.block_of_eq(SA.hprime(1024n, x)))

def init_len(+n: Nat, +l: Nat, +q: Nat, +hh: List<&2, U32>, +mem: List<&2, A.Block>) -> {SC.length(A.Block, SA.init_go(n, l, q, hh, mem)) == SC.length(A.Block, mem) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+ +rest:
      +b0 = SA.block_of(SA.hprime(1024n, SA.cat(hh, SA.cat(SA.le32(0n), SA.le32(l)))))
      +b1 = SA.block_of(SA.hprime(1024n, SA.cat(hh, SA.cat(SA.le32(1n), SA.le32(l)))))
      +m1 = SA.set(mem, Nat.mul(l, q), b0)
      +m2 = SA.set(m1, Nat.add(Nat.mul(l, q), 1n), b1)
      Equal.trans(Nat, SC.length(A.Block, SA.init_go(rest, Nat.add(l, 1n), q, hh, m2)), SC.length(A.Block, m2), SC.length(A.Block, mem),
        init_len(rest, Nat.add(l, 1n), q, hh, m2),
        Equal.trans(Nat, SC.length(A.Block, m2), SC.length(A.Block, m1), SC.length(A.Block, mem), LL.length_update(A.Block, m1, Nat.add(Nat.mul(l, q), 1n), b1), LL.length_update(A.Block, mem, Nat.mul(l, q), b0)))

def lt_first(+l: Nat, +p: Nat, +q: Nat, +hl: {Nat.is_lt(l, p) == True{} : Bool}, +hq2: {Nat.is_le(2n, q) == True{} : Bool}) -> {Nat.is_lt(Nat.mul(l, q), Nat.mul(p, q)) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_lt(z, Nat.mul(p, q)) == True{} : Bool}, Nat.add(Nat.mul(l, q), 0n), Nat.mul(l, q), N.add_zero(Nat.mul(l, q)), F.lt_mul_add(l, p, 0n, q, hl, N.lt_le_trans(0n, 2n, q, {==}, hq2)))

def lt_second(+l: Nat, +p: Nat, +q: Nat, +hl: {Nat.is_lt(l, p) == True{} : Bool}, +hq2: {Nat.is_le(2n, q) == True{} : Bool}) -> {Nat.is_lt(Nat.add(Nat.mul(l, q), 1n), Nat.mul(p, q)) == True{} : Bool}:
  F.lt_mul_add(l, p, 1n, q, hl, N.lt_le_trans(1n, 2n, q, {==}, hq2))

# B[l][0] and B[l][1] for the lanes l .. l + n - 1.
def init_eq(+d: Nat, +n: Nat, +l: Nat, +p: Nat, +q: Nat, +hh: List<&2, U32>, +mem: List<&2, A.Block>, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hc: {Nat.is_le(Nat.mul(SC.length(A.Block, mem), 256n), SC.pow2(d)) == True{} : Bool}, +hlen: {SC.length(A.Block, mem) == Nat.mul(p, q) : Nat}, +hq2: {Nat.is_le(2n, q) == True{} : Bool}, +hln: {Nat.is_le(Nat.add(l, n), p) == True{} : Bool}) -> {I.init_go(n, l, q, hh, AR.thaw(U32, MEM.mt(d, mem))) == AR.thaw(U32, MEM.mt(d, SA.init_go(n, l, q, hh, mem))) : Array<U32>}:
  match n:
    case 0n:
      {==}
    case 1n+ +rest:
      +b0i = I.block_of(I.hprime(1024n, I.cat(hh, I.cat(I.le32(0n), I.le32(l)))))
      +b1i = I.block_of(I.hprime(1024n, I.cat(hh, I.cat(I.le32(1n), I.le32(l)))))
      +b0 = SA.block_of(SA.hprime(1024n, SA.cat(hh, SA.cat(SA.le32(0n), SA.le32(l)))))
      +b1 = SA.block_of(SA.hprime(1024n, SA.cat(hh, SA.cat(SA.le32(1n), SA.le32(l)))))
      +i0 = Nat.mul(l, q)
      +i1 = Nat.add(Nat.mul(l, q), 1n)
      +m1 = SA.set(mem, i0, b0)
      +m2 = SA.set(m1, i1, b1)
      +hl = F.lt_of_add_succ(l, rest, p, hln)
      +e1 = LL.length_update(A.Block, mem, i0, b0)
      +e2 = Equal.trans(Nat, SC.length(A.Block, m2), SC.length(A.Block, m1), SC.length(A.Block, mem), LL.length_update(A.Block, m1, i1, b1), e1)
      -goal = AR.thaw(U32, MEM.mt(d, SA.init_go(rest, Nat.add(l, 1n), q, hh, m2)))
      %Equal.sym(A.Block, b0i, b0, init_block_eq(hh, 0n, l)) : {I.init_go(rest, Nat.add(l, 1n), q, hh, M.set(i1, b1i, M.set(i0, _, AR.thaw(U32, MEM.mt(d, mem))))) == goal : Array<U32>}
      %Equal.sym(A.Block, b1i, b1, init_block_eq(hh, 1n, l)) : {I.init_go(rest, Nat.add(l, 1n), q, hh, M.set(i1, _, M.set(i0, b0, AR.thaw(U32, MEM.mt(d, mem))))) == goal : Array<U32>}
      %Equal.sym(Array<U32>, M.set(i0, b0, AR.thaw(U32, MEM.mt(d, mem))), AR.thaw(U32, MEM.mt(d, m1)), MEM.set_block(d, mem, i0, b0, hd, hc, F.lt_len(i0, mem, p, q, hlen, lt_first(l, p, q, hl, hq2)))) : {I.init_go(rest, Nat.add(l, 1n), q, hh, M.set(i1, b1, _)) == goal : Array<U32>}
      %Equal.sym(Array<U32>, M.set(i1, b1, AR.thaw(U32, MEM.mt(d, m1))), AR.thaw(U32, MEM.mt(d, m2)), MEM.set_block(d, m1, i1, b1, hd, F.keep_c(d, mem, m1, e1, hc), F.lt_len(i1, m1, p, q, F.keep_len(mem, m1, Nat.mul(p, q), e1, hlen), lt_second(l, p, q, hl, hq2)))) : {I.init_go(rest, Nat.add(l, 1n), q, hh, _) == goal : Array<U32>}
      init_eq(d, rest, Nat.add(l, 1n), p, q, hh, m2, hd, F.keep_c(d, mem, m2, e2, hc), F.keep_len(mem, m2, Nat.mul(p, q), e2, hlen), hq2, F.le_shift(l, rest, p, hln))

# ---------------------------------------------------------------- the final block

# C = B[l][q-1] XOR .. for the lanes l .. l + n (b is B[l][q-1]).
def final_eq(+d: Nat, +n: Nat, +l: Nat, +p: Nat, +q: Nat, +c: A.Block, +b: A.Block, +mem: List<&2, A.Block>, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hc: {Nat.is_le(Nat.mul(SC.length(A.Block, mem), 256n), SC.pow2(d)) == True{} : Bool}, +hlen: {SC.length(A.Block, mem) == Nat.mul(p, q) : Nat}, +hq1: {Nat.is_le(1n, q) == True{} : Bool}, +hln: {Nat.is_lt(Nat.add(l, n), p) == True{} : Bool}) -> {I.final_go(n, l, q, c, (AR.thaw(U32, MEM.mt(d, mem)), b)) == SA.final_go(n, l, q, c, b, mem) : A.Block}:
  match n:
    case 0n:
      BL.xor_correct(c, b)
    case 1n+ +rest:
      +ix = Nat.add(Nat.mul(Nat.add(l, 1n), q), Nat.sub(q, 1n))
      +hl1 = N.le_lt_trans(Nat.add(l, 1n), Nat.add(l, 1n+rest), p, N.le_trans(Nat.add(l, 1n), Nat.add(Nat.add(l, 1n), rest), Nat.add(l, 1n+rest), N.le_add_right(Nat.add(l, 1n), rest), N.eq_le(Nat.add(Nat.add(l, 1n), rest), Nat.add(l, 1n+rest), MEM.add_one_assoc(l, rest))), hln)
      +hix = F.lt_len(ix, mem, p, q, hlen, F.lt_mul_add(Nat.add(l, 1n), p, Nat.sub(q, 1n), q, hl1, F.sub1_lt(q, hq1)))
      +hln2 = L.subst(Nat, z => {Nat.is_lt(z, p) == True{} : Bool}, Nat.add(l, 1n+rest), Nat.add(Nat.add(l, 1n), rest), Equal.sym(Nat, Nat.add(Nat.add(l, 1n), rest), Nat.add(l, 1n+rest), MEM.add_one_assoc(l, rest)), hln)
      -ar = AR.thaw(U32, MEM.mt(d, mem))
      -goal = SA.final_go(rest, Nat.add(l, 1n), q, SG.xor(c, b), SA.get(mem, ix), mem)
      %Equal.sym(Array<U32> & A.Block, M.get(ix, ar), (ar, SA.get(mem, ix)), MEM.get_block(d, mem, ix, hd, hc, hix)) : {I.final_go(rest, Nat.add(l, 1n), q, G.xor(c, b), _) == goal : A.Block}
      %Equal.sym(A.Block, G.xor(c, b), SG.xor(c, b), BL.xor_correct(c, b)) : {I.final_go(rest, Nat.add(l, 1n), q, _, (ar, SA.get(mem, ix))) == goal : A.Block}
      final_eq(d, rest, Nat.add(l, 1n), p, q, SG.xor(c, b), SA.get(mem, ix), mem, hd, hc, hlen, hq1, hln2)
