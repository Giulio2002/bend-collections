import Base
import ./types.bend as T
import ./aes.bend as A
import ../subtle.bend as Subtle

# AES-GCM (NIST SP 800-38D) with 96-bit nonces and 128-bit tags.
#
# GHASH works on 128-bit blocks held as four big-endian U32 words: bit 0 of
# a block (the coefficient of x^0 in GCM's bit order, the leftmost bit) is
# bit 31 of the first word. The product X * H is Algorithm 1 of SP 800-38D,
# one bit of X at a time, with masks instead of branches: Z ^= V & (0 - x_i),
# then V = V * x (a right shift that folds the dropped bit back in as
# R = 0xe1 || 0^120, again through a mask). No table is indexed by secret
# data. The tag comparison is subtle.eq.

type Block is Data:
  B{w0: U32, w1: U32, w2: U32, w3: U32}

type Acc is Data:
  Acc{z: Block, v: Block}

def zero() -> Block:
  B{0, 0, 0, 0}

# V * x: the block shifted one bit toward x^127, x^128 = R.
def mulx(v: Block) -> Block:
  match v:
    case B{+a, +b, +c, +d}:
      B{U32.xor(U32.and(3774873600, U32.sub(0, U32.and(1, d))), U32.shrn(a, 1n)),
        U32.or(U32.shln(a, 31n), U32.shrn(b, 1n)),
        U32.or(U32.shln(b, 31n), U32.shrn(c, 1n)),
        U32.or(U32.shln(c, 31n), U32.shrn(d, 1n))}

# Z xor (V and (0 - bit)), bit being 0 or 1.
def add_masked(+bit: U32, z: Block, v: Block) -> Block:
  match z v:
    case B{z0, z1, z2, z3} B{v0, v1, v2, v3}:
      +m = U32.sub(0, bit)
      B{U32.xor(z0, U32.and(m, v0)), U32.xor(z1, U32.and(m, v1)),
        U32.xor(z2, U32.and(m, v2)), U32.xor(z3, U32.and(m, v3))}

def step(+bit: U32, acc: Acc) -> Acc:
  match acc:
    case Acc{z, +v}:
      Acc{add_masked(bit, z, v), mulx(v)}

# The eight bits of a byte, the most significant first.
def mul_byte(+a: U32, acc: Acc) -> Acc:
  step(U32.and(1, a), step(U32.and(1, U32.shrn(a, 1n)), step(U32.and(1, U32.shrn(a, 2n)),
    step(U32.and(1, U32.shrn(a, 3n)), step(U32.and(1, U32.shrn(a, 4n)),
    step(U32.and(1, U32.shrn(a, 5n)), step(U32.and(1, U32.shrn(a, 6n)),
    step(U32.and(1, U32.shrn(a, 7n)), acc))))))))

def mul_bytes(xs: List<&2, U32>, acc: Acc) -> Acc:
  match xs:
    case Nil{}:
      acc
    case x <> rest:
      mul_bytes(rest, mul_byte(x, acc))

def acc_z(acc: Acc) -> Block:
  match acc:
    case Acc{z, v}:
      z

# The 16 bytes of a block, and the block of 16 bytes (big-endian words).
def unpack(z: Block) -> List<&2, U32>:
  match z:
    case B{+a, +b, +c, +d}:
      [U32.and(255, U32.shrn(a, 24n)), U32.and(255, U32.shrn(a, 16n)), U32.and(255, U32.shrn(a, 8n)), U32.and(255, a),
       U32.and(255, U32.shrn(b, 24n)), U32.and(255, U32.shrn(b, 16n)), U32.and(255, U32.shrn(b, 8n)), U32.and(255, b),
       U32.and(255, U32.shrn(c, 24n)), U32.and(255, U32.shrn(c, 16n)), U32.and(255, U32.shrn(c, 8n)), U32.and(255, c),
       U32.and(255, U32.shrn(d, 24n)), U32.and(255, U32.shrn(d, 16n)), U32.and(255, U32.shrn(d, 8n)), U32.and(255, d)]

def word(q: T.Quad) -> U32:
  match q:
    case T.W{a, b, c, d}:
      U32.or(U32.shln(U32.and(255, a), 24n), U32.or(U32.shln(U32.and(255, b), 16n),
        U32.or(U32.shln(U32.and(255, c), 8n), U32.and(255, d))))

# An AES state as a block: its columns are the words.
def pack(s: T.State) -> Block:
  match s:
    case T.S{c0, c1, c2, c3}:
      B{word(c0), word(c1), word(c2), word(c3)}

def xor_bytes(xs: List<&2, U32>, ks: List<&2, U32>) -> List<&2, U32>:
  match xs ks:
    case x <> xt k <> kt:
      U32.xor(x, k) <> xor_bytes(xt, kt)
    case _ _:
      Nil{}

# (Y xor X) * H for a 16-byte X.
def absorb(+h: Block, y: Block, x: List<&2, U32>) -> Block:
  acc_z(mul_bytes(xor_bytes(unpack(y), x), Acc{zero(), h}))

def zeros(n: Nat) -> List<&2, U32>:
  List.replicate(U32, n, 0)

# GHASH_H over the bytes, a last partial block padded with zero bytes.
def ghash(+h: Block, +xs: List<&2, U32>, y: Block) -> Block:
  match xs:
    case x0 <> x1 <> x2 <> x3 <> x4 <> x5 <> x6 <> x7 <> x8 <> x9 <> x10 <> x11 <> x12 <> x13 <> x14 <> x15 <> rest:
      ghash(h, rest, absorb(h, y, [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15]))
    case Nil{}:
      y
    case _:
      absorb(h, y, List.append(&2, U32, xs, zeros(Nat.sub(16n, List.length(&2, U32, xs)))))

# [n]_(8*width), most significant byte first.
def octets(width: Nat, +n: Nat) -> List<&2, U32>:
  match width:
    case 0n:
      Nil{}
    case 1n+p:
      List.append(&2, U32, octets(p, Nat.div(n, 256n)), [U32.from_nat(Nat.mod(n, 256n))])

# [len(A)]_64 || [len(C)]_64, in bits.
def lengths(+aad: List<&2, U32>, +c: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, octets(8n, Nat.mul(8n, List.length(&2, U32, aad))),
    octets(8n, Nat.mul(8n, List.length(&2, U32, c))))

# ---- counter mode ----

# The counter block: the 96-bit nonce (three words) and a 32-bit counter.
def counter(+n0: T.Quad, +n1: T.Quad, +n2: T.Quad, +c: U32) -> T.State:
  T.S{n0, n1, n2, T.W{U32.and(255, U32.shrn(c, 24n)), U32.and(255, U32.shrn(c, 16n)), U32.and(255, U32.shrn(c, 8n)), U32.and(255, c)}}

def keystream(+sched: A.Schedule, +n0: T.Quad, +n1: T.Quad, +n2: T.Quad, +c: U32) -> List<&2, U32>:
  A.bytes_of(A.encrypt_state(sched, counter(n0, n1, n2, c)))

def gctr(+sched: A.Schedule, +xs: List<&2, U32>, +n0: T.Quad, +n1: T.Quad, +n2: T.Quad, +c: U32) -> List<&2, U32>:
  match xs:
    case x0 <> x1 <> x2 <> x3 <> x4 <> x5 <> x6 <> x7 <> x8 <> x9 <> x10 <> x11 <> x12 <> x13 <> x14 <> x15 <> rest:
      List.append(&2, U32, xor_bytes([x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15], keystream(sched, n0, n1, n2, c)),
        gctr(sched, rest, n0, n1, n2, U32.inc(c)))
    case _:
      xor_bytes(xs, keystream(sched, n0, n1, n2, c))

# ---- GCM ----

def hash_key(+sched: A.Schedule) -> Block:
  pack(A.encrypt_state(sched, T.S{T.W{0, 0, 0, 0}, T.W{0, 0, 0, 0}, T.W{0, 0, 0, 0}, T.W{0, 0, 0, 0}}))

# The tag of ciphertext c: GHASH over A || 0^v || C || 0^u || lengths,
# encrypted with the counter block J0 = nonce || 1.
def tag(+sched: A.Schedule, +n0: T.Quad, +n1: T.Quad, +n2: T.Quad, +aad: List<&2, U32>, +c: List<&2, U32>) -> List<&2, U32>:
  +h = hash_key(sched)
  gctr(sched, unpack(ghash(h, lengths(aad, c), ghash(h, c, ghash(h, aad, zero())))), n0, n1, n2, 1)

# C || T; the counter of the first data block is 2 (inc32(J0)).
def seal_core(+sched: A.Schedule, +n0: T.Quad, +n1: T.Quad, +n2: T.Quad, +aad: List<&2, U32>, pt: List<&2, U32>) -> List<&2, U32>:
  +c = gctr(sched, pt, n0, n1, n2, 2)
  List.append(&2, U32, c, tag(sched, n0, n1, n2, aad, c))

def accept(ok: Bool, p: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match ok:
    case True{}:
      Some{p}
    case False{}:
      None{}

# The plaintext when t is the tag of c; None otherwise (compared in constant time).
def open_checked(+sched: A.Schedule, +n0: T.Quad, +n1: T.Quad, +n2: T.Quad, +aad: List<&2, U32>, +c: List<&2, U32>, t: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  accept(Subtle.eq(t, tag(sched, n0, n1, n2, aad, c)), gctr(sched, c, n0, n1, n2, 2))

def open_split(+sched: A.Schedule, +n0: T.Quad, +n1: T.Quad, +n2: T.Quad, +aad: List<&2, U32>, +input: List<&2, U32>, +n: Nat, short: Bool) -> Maybe<&2, List<&2, U32>>:
  match short:
    case True{}:
      None{}
    case False{}:
      open_checked(sched, n0, n1, n2, aad, List.take(&2, U32, input, Nat.sub(n, 16n)), List.drop(&2, U32, input, Nat.sub(n, 16n)))

def open_core(+sched: A.Schedule, +n0: T.Quad, +n1: T.Quad, +n2: T.Quad, +aad: List<&2, U32>, +input: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  +n = List.length(&2, U32, input)
  open_split(sched, n0, n1, n2, aad, input, n, Nat.is_lt(n, 16n))

# ---- byte API ----

def seal_nonce(+sched: A.Schedule, nonce: List<&2, U32>, +aad: List<&2, U32>, +pt: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match nonce:
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> n7 <> n8 <> n9 <> n10 <> n11 <> Nil{}:
      Some{seal_core(sched, T.W{n0, n1, n2, n3}, T.W{n4, n5, n6, n7}, T.W{n8, n9, n10, n11}, aad, pt)}
    case _:
      None{}

def open_nonce(+sched: A.Schedule, nonce: List<&2, U32>, +aad: List<&2, U32>, +input: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match nonce:
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> n7 <> n8 <> n9 <> n10 <> n11 <> Nil{}:
      open_core(sched, T.W{n0, n1, n2, n3}, T.W{n4, n5, n6, n7}, T.W{n8, n9, n10, n11}, aad, input)
    case _:
      None{}

def seal_key(m: Maybe<&2, A.Schedule>, +nonce: List<&2, U32>, +aad: List<&2, U32>, +pt: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match m:
    case None{}:
      None{}
    case Some{sched}:
      seal_nonce(sched, nonce, aad, pt)

def open_key(m: Maybe<&2, A.Schedule>, +nonce: List<&2, U32>, +aad: List<&2, U32>, +input: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match m:
    case None{}:
      None{}
    case Some{sched}:
      open_nonce(sched, nonce, aad, input)

def schedule_if(ok: Bool, +key: List<&2, U32>) -> Maybe<&2, A.Schedule>:
  match ok:
    case True{}:
      A.expand_key(key)
    case False{}:
      None{}

# The expanded key when the key has the given length.
def schedule_of(+width: Nat, +key: List<&2, U32>) -> Maybe<&2, A.Schedule>:
  schedule_if(Nat.is_eq(List.length(&2, U32, key), width), key)
