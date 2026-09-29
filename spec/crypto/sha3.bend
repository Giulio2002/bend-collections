import Base
import ../../src/crypto/keccak/types.bend as T
import ./keccak/permutation.bend as K

# Executable specification of SHA3-256 (FIPS 202), byte oriented, in the
# shape of HACL*'s Spec.SHA3: the sponge construction (section 4) on
# KECCAK-p[1600, n_r] (section 3, spec/crypto/keccak/permutation.bend) with
# rate r = 1088 bits = 136 bytes, capacity 512 and a 256-bit output:
#
#   SHA3-256(M) = KECCAK[512](M || 01, 256)        (section 6.1)
#
# The permutation's round count is a parameter (24 for SHA3-256, section 3.4)
# so the proofs never unfold 24 rounds. Only the record types of
# src/crypto/keccak/types.bend are shared with the implementation: a lane is
# T.W{lo, hi}, the state is T.S{a0..a24} with a[x + 5y] = A[x, y].
# Bytes are U32 values, each < 256; bits are little-endian within a byte and
# bytes little-endian within a lane (section B.1).

# ---------------------------------------------------------------- padding

# M || 01 || pad10*1(r, |M| + 2) at the byte level, for q = 1..136 bytes to
# the end of the block: the suffix bits 0, 1 and the first pad bit 1 are the
# byte 0x06; the last pad bit is the top bit, 0x80, of the block's last byte;
# with one byte left both fall in it: 0x86.
def padding_bytes(q: Nat) -> List<&2, U32>:
  match q:
    case 0n:
      Nil{}
    case 1n:
      [U32.or(6, 128)]
    case 2n+k:
      6 <> List.append(&2, U32, List.replicate(U32, k, 0), [128])

def padding(+n: Nat) -> List<&2, U32>:
  padding_bytes(Nat.sub(136n, Nat.mod(n, 136n)))

def pad(+bytes: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, bytes, padding(List.length(&2, U32, bytes)))

# ---------------------------------------------------------------- lanes

def le32(a: U32, b: U32, c: U32, d: U32) -> U32:
  U32.or(U32.or(U32.or(U32.and(a, 255), U32.shln(U32.and(b, 255), 8n)),
    U32.shln(U32.and(c, 255), 16n)), U32.shln(U32.and(d, 255), 24n))

# Little-endian 64-bit lanes, eight bytes each.
def lanes(bytes: List<&2, U32>) -> List<&2, T.Lane>:
  match bytes:
    case a <> b <> c <> d <> e <> f <> g <> h <> rest:
      T.W{le32(a, b, c, d), le32(e, f, g, h)} <> lanes(rest)
    case _:
      Nil{}

# ---------------------------------------------------------------- the sponge

# S = 0^1600.
def initial() -> T.State:
  T.S{T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0},
    T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0},
    T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0},
    T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0},
    T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}, T.W{0, 0}}

def to_lanes(s: T.State) -> List<&2, T.Lane>:
  match s:
    case T.S{a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24}:
      [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24]

def of_lanes(ls: List<&2, T.Lane>) -> T.State:
  match ls:
    case a0 <> a1 <> a2 <> a3 <> a4 <> a5 <> a6 <> a7 <> a8 <> a9 <> a10 <> a11 <> a12 <> a13 <> a14 <> a15 <> a16 <> a17 <> a18 <> a19 <> a20 <> a21 <> a22 <> a23 <> a24 <> rest:
      T.S{a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24}
    case _:
      initial()

# Lane-wise XOR of a block into the leading lanes of the state.
def xor_lanes(xs: List<&2, T.Lane>, ys: List<&2, T.Lane>) -> List<&2, T.Lane>:
  match xs ys:
    case x <> xt y <> yt:
      K.xor(x, y) <> xor_lanes(xt, yt)
    case xs _:
      xs

# Section 4, step 6: S = f(S XOR (P_i || 0^c)) for each r-bit block P_i.
def absorb(ls: List<&2, T.Lane>, +rounds: Nat, s: T.State) -> T.State:
  match ls:
    case l0 <> l1 <> l2 <> l3 <> l4 <> l5 <> l6 <> l7 <> l8 <> l9 <> l10 <> l11 <> l12 <> l13 <> l14 <> l15 <> l16 <> rest:
      absorb(rest, rounds, K.rounds(rounds, 0n, of_lanes(xor_lanes(to_lanes(s),
        [l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15, l16]))))
    case _:
      s

# Section 4, steps 7-10: d = 256 <= r, so Z is the first 32 bytes of S.
def lane_bytes(l: T.Lane) -> List<&2, U32>:
  match l:
    case T.W{+lo, +hi}:
      [U32.and(lo, 255), U32.and(U32.shrn(lo, 8n), 255), U32.and(U32.shrn(lo, 16n), 255), U32.shrn(lo, 24n),
       U32.and(hi, 255), U32.and(U32.shrn(hi, 8n), 255), U32.and(U32.shrn(hi, 16n), 255), U32.shrn(hi, 24n)]

def state_bytes(ls: List<&2, T.Lane>) -> List<&2, U32>:
  match ls:
    case Nil{}:
      Nil{}
    case l <> rest:
      List.append(&2, U32, lane_bytes(l), state_bytes(rest))

def squeeze(s: T.State) -> List<&2, U32>:
  List.take(&2, U32, state_bytes(to_lanes(s)), 32n)

def keccak(bytes: List<&2, U32>, +rounds: Nat) -> List<&2, U32>:
  squeeze(absorb(lanes(pad(bytes)), rounds, initial()))

# SHA3-256(M): 32 bytes.
def sha3_256(bytes: List<&2, U32>) -> List<&2, U32>:
  keccak(bytes, 24n)
