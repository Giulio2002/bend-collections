import Base
import ../../../../src/math/u64.bend as W
import ../../../../src/math/random/chacha8/block.bend as B
import ../../../../spec/math/random/chacha8rand.bend as S
import ./rounds.bend as R

# The ChaCha8Rand block and group of src/math/random/chacha8/block.bend are
# C2SP's (spec/math/random/chacha8rand.bend) for every key and counter.

# n double rounds, the model of the implementation's dr(dr(dr(dr(x))))
def drs(n: Nat, v: B.Vector) -> B.Vector:
  match n:
    case 0n:
      v
    case 1n+p:
      drs(p, B.dr(v))

def drs_correct(+n: Nat, +v: B.Vector) -> {R.vec(drs(n, v)) == S.double_rounds(n, R.vec(v)) : List<&2, U32>}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.trans(List<&2, U32>, R.vec(drs(p, B.dr(v))), S.double_rounds(p, R.vec(B.dr(v))), S.double_rounds(p, S.double_round(R.vec(v))),
        drs_correct(p, B.dr(v)),
        Equal.cong(List<&2, U32>, List<&2, U32>, x => S.double_rounds(p, x), R.vec(B.dr(v)), S.double_round(R.vec(v)), R.dr_correct(v)))

# the eight rounds on the initial state
def rounds_correct(+k: B.Key, +ctr: U32) -> {R.vec(B.dr(B.dr(B.dr(B.dr(B.init(k, ctr)))))) == S.double_rounds(4n, S.initial(S.key_list(k), ctr)) : List<&2, U32>}:
  Equal.trans(List<&2, U32>, R.vec(drs(4n, B.init(k, ctr))), S.double_rounds(4n, R.vec(B.init(k, ctr))), S.double_rounds(4n, S.initial(S.key_list(k), ctr)),
    drs_correct(4n, B.init(k, ctr)),
    Equal.cong(List<&2, U32>, List<&2, U32>, x => S.double_rounds(4n, x), R.vec(B.init(k, ctr)), S.initial(S.key_list(k), ctr), R.init_correct(k, ctr)))

# THEOREM: the implementation's block is C2SP's block ctr
def block_correct(+k: B.Key, +ctr: U32) -> {R.vec(B.block(k, ctr)) == S.c2sp_block(S.key_list(k), ctr) : List<&2, U32>}:
  +v = B.dr(B.dr(B.dr(B.dr(B.init(k, ctr)))))
  Equal.trans(List<&2, U32>, R.vec(B.finish(k, v)), S.subtract(S.add_words(R.vec(v), R.vec(B.init(k, ctr))), ctr), S.subtract(S.add_words(S.double_rounds(4n, S.initial(S.key_list(k), ctr)), S.initial(S.key_list(k), ctr)), ctr),
    R.finish_correct(k, v, ctr),
    Equal.trans(List<&2, U32>, S.subtract(S.add_words(R.vec(v), R.vec(B.init(k, ctr))), ctr), S.subtract(S.add_words(S.double_rounds(4n, S.initial(S.key_list(k), ctr)), R.vec(B.init(k, ctr))), ctr), S.subtract(S.add_words(S.double_rounds(4n, S.initial(S.key_list(k), ctr)), S.initial(S.key_list(k), ctr)), ctr),
      Equal.cong(List<&2, U32>, List<&2, U32>, x => S.subtract(S.add_words(x, R.vec(B.init(k, ctr))), ctr), R.vec(v), S.double_rounds(4n, S.initial(S.key_list(k), ctr)), rounds_correct(k, ctr)),
      Equal.cong(List<&2, U32>, List<&2, U32>, x => S.subtract(S.add_words(S.double_rounds(4n, S.initial(S.key_list(k), ctr)), x), ctr), R.vec(B.init(k, ctr)), S.initial(S.key_list(k), ctr), R.init_correct(k, ctr))))

# THEOREM: the implementation's group is C2SP's four permuted blocks ctr ..
# ctr + 3, read as little-endian 64-bit words
def group_correct(+k: B.Key, +ctr: U32) -> {B.group(k, ctr) == S.words64(S.group(S.key_list(k), ctr)) : List<&2, W.U64>}:
  +b0 = B.block(k, ctr)
  +b1 = B.block(k, U32.add(ctr, 1))
  +b2 = B.block(k, U32.add(ctr, 2))
  +b3 = B.block(k, U32.add(ctr, 3))
  +kl = S.key_list(k)
  %block_correct(k, ctr) : {B.group(k, ctr) == S.words64(S.interleave(16n, 0n, _, S.c2sp_block(kl, U32.add(ctr, 1)), S.c2sp_block(kl, U32.add(ctr, 2)), S.c2sp_block(kl, U32.add(ctr, 3)))) : List<&2, W.U64>}
  %block_correct(k, U32.add(ctr, 1)) : {B.group(k, ctr) == S.words64(S.interleave(16n, 0n, R.vec(b0), _, S.c2sp_block(kl, U32.add(ctr, 2)), S.c2sp_block(kl, U32.add(ctr, 3)))) : List<&2, W.U64>}
  %block_correct(k, U32.add(ctr, 2)) : {B.group(k, ctr) == S.words64(S.interleave(16n, 0n, R.vec(b0), R.vec(b1), _, S.c2sp_block(kl, U32.add(ctr, 3)))) : List<&2, W.U64>}
  %block_correct(k, U32.add(ctr, 3)) : {B.group(k, ctr) == S.words64(S.interleave(16n, 0n, R.vec(b0), R.vec(b1), R.vec(b2), _)) : List<&2, W.U64>}
  R.interleave_correct(b0, b1, b2, b3)
