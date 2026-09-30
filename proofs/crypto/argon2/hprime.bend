import Base
import ../../lib/nat.bend as N
import ../../../src/crypto/blake/blake2b/types.bend as T
import ../../../src/crypto/blake/blake2b/sized.bend as IH
import ../../../src/crypto/argon2/types.bend as A
import ../../../src/crypto/argon2/sub.bend as SB
import ../../../src/crypto/argon2/argon2.bend as I

# H'^1024 on words (argon2.bend's init_block) is block_of(hprime(1024n, x)):
# the digest bytes are never listed, but every word is the same term as
# H.words computes from them. The chain values stay abstract wherever a hash
# of them appears, so no BLAKE2b compression is ever unfolded.

# ---------------------------------------------------------------- one digest

def take_cb(+c: T.Chain) -> {List.take(&2, U32, IH.chain_bytes(c), 64n) == IH.chain_bytes(c) : List<&2, U32>}:
  match c:
    case T.H{T.W{l0, h0}, T.W{l1, h1}, T.W{l2, h2}, T.W{l3, h3}, T.W{l4, h4}, T.W{l5, h5}, T.W{l6, h6}, T.W{l7, h7}}:
      {==}

def len_cb(+c: T.Chain) -> {List.length(&2, U32, IH.chain_bytes(c)) == 64n : Nat}:
  match c:
    case T.H{T.W{l0, h0}, T.W{l1, h1}, T.W{l2, h2}, T.W{l3, h3}, T.W{l4, h4}, T.W{l5, h5}, T.W{l6, h6}, T.W{l7, h7}}:
      {==}

def pack_cb(+c: T.Chain) -> {IH.pack(IH.chain_bytes(c)) == I.pack_c(c) : Array<U32>}:
  match c:
    case T.H{T.W{l0, h0}, T.W{l1, h1}, T.W{l2, h2}, T.W{l3, h3}, T.W{l4, h4}, T.W{l5, h5}, T.W{l6, h6}, T.W{l7, h7}}:
      {==}

# The words of the first 32 digest bytes, then y.
def words_half(+c: T.Chain, +y: List<&2, U32>) -> {IH.words(List.append(&2, U32, List.take(&2, U32, IH.chain_bytes(c), 32n), y)) == SB.app(I.half(c), IH.words(y)) : List<&2, U32>}:
  match c:
    case T.H{T.W{l0, h0}, T.W{l1, h1}, T.W{l2, h2}, T.W{l3, h3}, T.W{l4, h4}, T.W{l5, h5}, T.W{l6, h6}, T.W{l7, h7}}:
      {==}

# H^64 of a digest.
def hash64(+c: T.Chain) -> {IH.hash(64n, IH.chain_bytes(c)) == IH.chain_bytes(I.chain64(c)) : List<&2, U32>}:
  +cb = IH.chain_bytes(c)
  Equal.trans(List<&2, U32>, List.take(&2, U32, IH.chain_bytes(IH.chain(64n, IH.pack(cb), List.length(&2, U32, cb))), 64n), List.take(&2, U32, IH.chain_bytes(IH.chain(64n, I.pack_c(c), 64n)), 64n), IH.chain_bytes(I.chain64(c)),
    Equal.trans(List<&2, U32>, List.take(&2, U32, IH.chain_bytes(IH.chain(64n, IH.pack(cb), List.length(&2, U32, cb))), 64n), List.take(&2, U32, IH.chain_bytes(IH.chain(64n, I.pack_c(c), List.length(&2, U32, cb))), 64n), List.take(&2, U32, IH.chain_bytes(IH.chain(64n, I.pack_c(c), 64n)), 64n),
      Equal.cong(Array<U32>, List<&2, U32>, z => List.take(&2, U32, IH.chain_bytes(IH.chain(64n, z, List.length(&2, U32, cb))), 64n), IH.pack(cb), I.pack_c(c), pack_cb(c)),
      Equal.cong(Nat, List<&2, U32>, z => List.take(&2, U32, IH.chain_bytes(IH.chain(64n, I.pack_c(c), z)), 64n), List.length(&2, U32, cb), 64n, len_cb(c))),
    take_cb(I.chain64(c)))

# ---------------------------------------------------------------- the chain

def nil_cb(+c: T.Chain, +e: {Nil{} == IH.chain_bytes(c) : List<&2, U32>}) -> Empty:
  N.zero_succ(63n, Equal.trans(Nat, 0n, List.length(&2, U32, IH.chain_bytes(c)), 64n, Equal.cong(List<&2, U32>, Nat, z => List.length(&2, U32, z), Nil{}, IH.chain_bytes(c), e), len_cb(c)))

# H.words(hp_go(n, v, last)) for v the digest bytes of c.
def hpw_eq(+n: Nat, +v: List<&2, U32>, +c: T.Chain, +last: Nat, +hv: {v == IH.chain_bytes(c) : List<&2, U32>}) -> {IH.words(I.hp_go(n, v, last)) == I.hpw_go(n, c, last) : List<&2, U32>}:
  match n v:
    case _ Nil{}:
      Empty.absurd({IH.words(I.hp_go(n, Nil{}, last)) == I.hpw_go(n, c, last) : List<&2, U32>}, nil_cb(c, hv))
    case 0n +x <> +r:
      %Equal.sym(List<&2, U32>, x <> r, IH.chain_bytes(c), hv) : {IH.words(List.append(&2, U32, List.take(&2, U32, _, 32n), IH.hash(last, _))) == I.hpw_go(0n, c, last) : List<&2, U32>}
      words_half(c, IH.hash(last, IH.chain_bytes(c)))
    case 1n+ +p +x <> +r:
      +cb = IH.chain_bytes(c)
      %Equal.sym(List<&2, U32>, x <> r, cb, hv) : {IH.words(List.append(&2, U32, List.take(&2, U32, _, 32n), I.hp_go(p, IH.hash(64n, _), last))) == I.hpw_go(1n+p, c, last) : List<&2, U32>}
      Equal.trans(List<&2, U32>, IH.words(List.append(&2, U32, List.take(&2, U32, cb, 32n), I.hp_go(p, IH.hash(64n, cb), last))), SB.app(I.half(c), IH.words(I.hp_go(p, IH.hash(64n, cb), last))), SB.app(I.half(c), I.hpw_go(p, I.chain64(c), last)),
        words_half(c, I.hp_go(p, IH.hash(64n, cb), last)),
        Equal.cong(List<&2, U32>, List<&2, U32>, z => SB.app(I.half(c), z), IH.words(I.hp_go(p, IH.hash(64n, cb), last)), I.hpw_go(p, I.chain64(c), last), hpw_eq(p, IH.hash(64n, cb), I.chain64(c), last, hash64(c))))

# ---------------------------------------------------------------- the first blocks

def init_block_hp(+x: List<&2, U32>) -> {I.init_block(x) == I.block_of(I.hprime(1024n, x)) : A.Block}:
  +y = I.cat(I.le32(1024n), x)
  +c1 = IH.chain(64n, IH.pack(y), I.len(y))
  Equal.sym(A.Block, SB.rows8(IH.words(I.hp_go(29n, IH.hash(64n, y), 64n))), SB.rows8(I.hpw_go(29n, c1, 64n)),
    Equal.cong(List<&2, U32>, A.Block, z => SB.rows8(z), IH.words(I.hp_go(29n, IH.hash(64n, y), 64n)), I.hpw_go(29n, c1, 64n), hpw_eq(29n, IH.hash(64n, y), c1, 64n, take_cb(c1))))
