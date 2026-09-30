import Base
import ../../../src/crypto/blake/blake2b/types.bend as T
import ../../../src/crypto/blake/blake2b/blake2b.bend as IB
import ../../../src/crypto/blake/blake2b/sized.bend as IH
import ../../../src/crypto/argon2/types.bend as A
import ../../../src/crypto/argon2/sub.bend as SB
import ../../../src/crypto/argon2/argon2.bend as I
import ../../../spec/crypto/blake/blake2b.bend as SBL
import ../../../spec/crypto/argon2/argon2.bend as SA
import ../blake/blake2b/blocks.bend as BB

# BLAKE2b with a digest length, H' and H0 of the implementation equal those
# of the specification for every input; so do the conversions between
# blocks and bytes. The implementation packs and hashes exactly as the
# specification does, with its own (identical) byte packing and the proved
# BLAKE2b-512 block function (proofs/crypto/blake/blake2b/blocks.bend).

# ---------------------------------------------------------------- packing

def words_eq(+bs: List<&2, U32>) -> {IH.words(bs) == SA.words(bs) : List<&2, U32>}:
  match bs:
    case Nil{}:
      {==}
    case b0 <> Nil{}:
      {==}
    case b0 <> b1 <> Nil{}:
      {==}
    case b0 <> b1 <> b2 <> Nil{}:
      {==}
    case +b0 <> +b1 <> +b2 <> +b3 <> +rest:
      Equal.cong(List<&2, U32>, List<&2, U32>, z => IH.word(b0, b1, b2, b3) <> z, IH.words(rest), SA.words(rest), words_eq(rest))

def fill_eq(+ws: List<&2, U32>, +i: U32, a: Array<U32>) -> {IH.fill(ws, i, a) == SA.fill(ws, i, a) : Array<U32>}:
  match ws:
    case Nil{}:
      {==}
    case +w <> +rest:
      fill_eq(rest, U32.inc(i), Array.set(U32, a, i, w))

def pw_eq(+k: Nat) -> {IH.pw(k) == SA.pw(k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+ +p:
      Equal.cong(Nat, Nat, z => Nat.double(z), IH.pw(p), SA.pw(p), pw_eq(p))

def depth_eq(+fuel: Nat, +n: Nat, +d: Nat, +done: Bool) -> {IH.depth_go(fuel, n, d, done) == SA.depth_go(fuel, n, d, done) : Nat}:
  match fuel done:
    case _ True{}:
      {==}
    case 0n False{}:
      {==}
    case 1n+ +f False{}:
      Equal.trans(Nat, IH.depth_go(f, n, 1n+d, Nat.is_le(n, IH.pw(1n+d))), IH.depth_go(f, n, 1n+d, Nat.is_le(n, SA.pw(1n+d))), SA.depth_go(f, n, 1n+d, Nat.is_le(n, SA.pw(1n+d))),
        Equal.cong(Nat, Nat, z => IH.depth_go(f, n, 1n+d, Nat.is_le(n, z)), IH.pw(1n+d), SA.pw(1n+d), pw_eq(1n+d)),
        depth_eq(f, n, 1n+d, Nat.is_le(n, SA.pw(1n+d))))

def pack_fin(+ws: List<&2, U32>) -> {IH.fill(ws, 0, Array.new(U32, IH.depth_go(32n, List.length(&2, U32, ws), 0n, Nat.is_le(List.length(&2, U32, ws), 1n)), 0)) == SA.fill(ws, 0, Array.new(U32, SA.depth_go(32n, List.length(&2, U32, ws), 0n, Nat.is_le(List.length(&2, U32, ws), 1n)), 0)) : Array<U32>}:
  +n = List.length(&2, U32, ws)
  Equal.trans(Array<U32>, IH.fill(ws, 0, Array.new(U32, IH.depth_go(32n, n, 0n, Nat.is_le(n, 1n)), 0)), IH.fill(ws, 0, Array.new(U32, SA.depth_go(32n, n, 0n, Nat.is_le(n, 1n)), 0)), SA.fill(ws, 0, Array.new(U32, SA.depth_go(32n, n, 0n, Nat.is_le(n, 1n)), 0)),
    Equal.cong(Nat, Array<U32>, z => IH.fill(ws, 0, Array.new(U32, z, 0)), IH.depth_go(32n, n, 0n, Nat.is_le(n, 1n)), SA.depth_go(32n, n, 0n, Nat.is_le(n, 1n)), depth_eq(32n, n, 0n, Nat.is_le(n, 1n))),
    fill_eq(ws, 0, Array.new(U32, SA.depth_go(32n, n, 0n, Nat.is_le(n, 1n)), 0)))

def pack_eq(+bs: List<&2, U32>) -> {IH.pack(bs) == SA.pack(bs) : Array<U32>}:
  Equal.trans(Array<U32>, IH.fill(IH.words(bs), 0, Array.new(U32, IH.depth_go(32n, List.length(&2, U32, IH.words(bs)), 0n, Nat.is_le(List.length(&2, U32, IH.words(bs)), 1n)), 0)), IH.fill(SA.words(bs), 0, Array.new(U32, IH.depth_go(32n, List.length(&2, U32, SA.words(bs)), 0n, Nat.is_le(List.length(&2, U32, SA.words(bs)), 1n)), 0)), SA.pack(bs),
    Equal.cong(List<&2, U32>, Array<U32>, +z => IH.fill(z, 0, Array.new(U32, IH.depth_go(32n, List.length(&2, U32, z), 0n, Nat.is_le(List.length(&2, U32, z), 1n)), 0)), IH.words(bs), SA.words(bs), words_eq(bs)),
    pack_fin(SA.words(bs)))

# ---------------------------------------------------------------- BLAKE2b with digest length nn

def initial_eq(+nn: U32) -> {IH.initial(nn) == SA.initial(nn) : T.Chain}:
  {==}

def chain_bytes_eq(+h: T.Chain) -> {IH.chain_bytes(h) == SA.chain_bytes(h) : List<&2, U32>}:
  match h:
    case T.H{T.W{l0, u0}, T.W{l1, u1}, T.W{l2, u2}, T.W{l3, u3}, T.W{l4, u4}, T.W{l5, u5}, T.W{l6, u6}, T.W{l7, u7}}:
      {==}

def hash_eq(+nn: Nat, +bs: List<&2, U32>) -> {IH.hash(nn, bs) == SA.hash(nn, bs) : List<&2, U32>}:
  +ll = List.length(&2, U32, bs)
  +n = Nat.div(Nat.sub(ll, 1n), 128n)
  +rem = Nat.sub(ll, Nat.mul(n, 128n))
  +f = U32.from_nat(nn)
  Equal.trans(List<&2, U32>, List.take(&2, U32, IH.chain_bytes(IB.blocks(n, 0, rem, T.C{0, 0, 0, 0}, (IH.pack(bs), IH.initial(f)))), nn), List.take(&2, U32, IH.chain_bytes(IB.blocks(n, 0, rem, T.C{0, 0, 0, 0}, (SA.pack(bs), SA.initial(f)))), nn), SA.hash(nn, bs),
    Equal.trans(List<&2, U32>, List.take(&2, U32, IH.chain_bytes(IB.blocks(n, 0, rem, T.C{0, 0, 0, 0}, (IH.pack(bs), IH.initial(f)))), nn), List.take(&2, U32, IH.chain_bytes(IB.blocks(n, 0, rem, T.C{0, 0, 0, 0}, (SA.pack(bs), IH.initial(f)))), nn), List.take(&2, U32, IH.chain_bytes(IB.blocks(n, 0, rem, T.C{0, 0, 0, 0}, (SA.pack(bs), SA.initial(f)))), nn),
      Equal.cong(Array<U32>, List<&2, U32>, z => List.take(&2, U32, IH.chain_bytes(IB.blocks(n, 0, rem, T.C{0, 0, 0, 0}, (z, IH.initial(f)))), nn), IH.pack(bs), SA.pack(bs), pack_eq(bs)),
      Equal.cong(T.Chain, List<&2, U32>, z => List.take(&2, U32, IH.chain_bytes(IB.blocks(n, 0, rem, T.C{0, 0, 0, 0}, (SA.pack(bs), z))), nn), IH.initial(f), SA.initial(f), initial_eq(f))),
    Equal.trans(List<&2, U32>, List.take(&2, U32, IH.chain_bytes(IB.blocks(n, 0, rem, T.C{0, 0, 0, 0}, (SA.pack(bs), SA.initial(f)))), nn), List.take(&2, U32, IH.chain_bytes(SBL.blocks(n, 0, rem, T.C{0, 0, 0, 0}, (SA.pack(bs), SA.initial(f)))), nn), SA.hash(nn, bs),
      Equal.cong(T.Chain, List<&2, U32>, z => List.take(&2, U32, IH.chain_bytes(z), nn), IB.blocks(n, 0, rem, T.C{0, 0, 0, 0}, (SA.pack(bs), SA.initial(f))), SBL.blocks(n, 0, rem, T.C{0, 0, 0, 0}, (SA.pack(bs), SA.initial(f))), BB.blocks_correct(n, 0, rem, T.C{0, 0, 0, 0}, (SA.pack(bs), SA.initial(f)))),
      Equal.cong(List<&2, U32>, List<&2, U32>, z => List.take(&2, U32, z, nn), IH.chain_bytes(SBL.blocks(n, 0, rem, T.C{0, 0, 0, 0}, (SA.pack(bs), SA.initial(f)))), SA.chain_bytes(SBL.blocks(n, 0, rem, T.C{0, 0, 0, 0}, (SA.pack(bs), SA.initial(f)))), chain_bytes_eq(SBL.blocks(n, 0, rem, T.C{0, 0, 0, 0}, (SA.pack(bs), SA.initial(f)))))))

# ---------------------------------------------------------------- H' and H0

def hp_go_eq(+n: Nat, +v: List<&2, U32>, +last: Nat) -> {I.hp_go(n, v, last) == SA.hp_go(n, v, last) : List<&2, U32>}:
  match n v:
    case _ Nil{}:
      {==}
    case 0n +x <> +r:
      Equal.cong(List<&2, U32>, List<&2, U32>, z => List.append(&2, U32, List.take(&2, U32, x <> r, 32n), z), IH.hash(last, x <> r), SA.hash(last, x <> r), hash_eq(last, x <> r))
    case 1n+ +p +x <> +r:
      Equal.trans(List<&2, U32>, List.append(&2, U32, List.take(&2, U32, x <> r, 32n), I.hp_go(p, IH.hash(64n, x <> r), last)), List.append(&2, U32, List.take(&2, U32, x <> r, 32n), I.hp_go(p, SA.hash(64n, x <> r), last)), List.append(&2, U32, List.take(&2, U32, x <> r, 32n), SA.hp_go(p, SA.hash(64n, x <> r), last)),
        Equal.cong(List<&2, U32>, List<&2, U32>, z => List.append(&2, U32, List.take(&2, U32, x <> r, 32n), I.hp_go(p, z, last)), IH.hash(64n, x <> r), SA.hash(64n, x <> r), hash_eq(64n, x <> r)),
        Equal.cong(List<&2, U32>, List<&2, U32>, z => List.append(&2, U32, List.take(&2, U32, x <> r, 32n), z), I.hp_go(p, SA.hash(64n, x <> r), last), SA.hp_go(p, SA.hash(64n, x <> r), last), hp_go_eq(p, SA.hash(64n, x <> r), last)))

def hp_pick_eq(+tl: Nat, +x: List<&2, U32>, +short: Bool) -> {I.hp_pick(tl, x, short) == SA.hp_pick(tl, x, short) : List<&2, U32>}:
  match short:
    case True{}:
      hash_eq(tl, x)
    case False{}:
      +r = Nat.sub(Nat.div(Nat.add(tl, 31n), 32n), 2n)
      +last = Nat.sub(tl, Nat.mul(32n, r))
      Equal.trans(List<&2, U32>, I.hp_go(Nat.sub(r, 1n), IH.hash(64n, x), last), I.hp_go(Nat.sub(r, 1n), SA.hash(64n, x), last), SA.hp_go(Nat.sub(r, 1n), SA.hash(64n, x), last),
        Equal.cong(List<&2, U32>, List<&2, U32>, z => I.hp_go(Nat.sub(r, 1n), z, last), IH.hash(64n, x), SA.hash(64n, x), hash_eq(64n, x)),
        hp_go_eq(Nat.sub(r, 1n), SA.hash(64n, x), last))

# H'^T
def hprime_eq(+tl: Nat, +a: List<&2, U32>) -> {I.hprime(tl, a) == SA.hprime(tl, a) : List<&2, U32>}:
  hp_pick_eq(tl, SA.cat(SA.le32(tl), a), Nat.is_le(tl, 64n))

# H0
def h0_eq(+p: Nat, +tl: Nat, +m: Nat, +t: Nat, +pw: List<&2, U32>, +salt: List<&2, U32>, +key: List<&2, U32>, +ad: List<&2, U32>) -> {I.h0(p, tl, m, t, pw, salt, key, ad) == SA.h0(p, tl, m, t, pw, salt, key, ad) : List<&2, U32>}:
  hash_eq(64n, SA.cat(SA.le32(p), SA.cat(SA.le32(tl), SA.cat(SA.le32(m), SA.cat(SA.le32(t), SA.cat(SA.le32(19n), SA.cat(SA.le32(2n), SA.cat(SA.le32(SA.len(pw)), SA.cat(pw, SA.cat(SA.le32(SA.len(salt)), SA.cat(salt, SA.cat(SA.le32(SA.len(key)), SA.cat(key, SA.cat(SA.le32(SA.len(ad)), ad))))))))))))))

# ---------------------------------------------------------------- blocks and bytes

def row_eq(+ws: List<&2, U32>) -> {SB.row(ws) == SA.row_of(ws) : T.State & List<&2, U32>}:
  match ws:
    case Nil{}:
      {==}
    case w0 <> Nil{}:
      {==}
    case w0 <> w1 <> Nil{}:
      {==}
    case w0 <> w1 <> w2 <> Nil{}:
      {==}
    case w0 <> w1 <> w2 <> w3 <> Nil{}:
      {==}
    case w0 <> w1 <> w2 <> w3 <> w4 <> Nil{}:
      {==}
    case w0 <> w1 <> w2 <> w3 <> w4 <> w5 <> Nil{}:
      {==}
    case w0 <> w1 <> w2 <> w3 <> w4 <> w5 <> w6 <> Nil{}:
      {==}
    case w0 <> w1 <> w2 <> w3 <> w4 <> w5 <> w6 <> w7 <> Nil{}:
      {==}
    case w0 <> w1 <> w2 <> w3 <> w4 <> w5 <> w6 <> w7 <> w8 <> Nil{}:
      {==}
    case w0 <> w1 <> w2 <> w3 <> w4 <> w5 <> w6 <> w7 <> w8 <> w9 <> Nil{}:
      {==}
    case w0 <> w1 <> w2 <> w3 <> w4 <> w5 <> w6 <> w7 <> w8 <> w9 <> w10 <> Nil{}:
      {==}
    case w0 <> w1 <> w2 <> w3 <> w4 <> w5 <> w6 <> w7 <> w8 <> w9 <> w10 <> w11 <> Nil{}:
      {==}
    case w0 <> w1 <> w2 <> w3 <> w4 <> w5 <> w6 <> w7 <> w8 <> w9 <> w10 <> w11 <> w12 <> Nil{}:
      {==}
    case w0 <> w1 <> w2 <> w3 <> w4 <> w5 <> w6 <> w7 <> w8 <> w9 <> w10 <> w11 <> w12 <> w13 <> Nil{}:
      {==}
    case w0 <> w1 <> w2 <> w3 <> w4 <> w5 <> w6 <> w7 <> w8 <> w9 <> w10 <> w11 <> w12 <> w13 <> w14 <> Nil{}:
      {==}
    case w0 <> w1 <> w2 <> w3 <> w4 <> w5 <> w6 <> w7 <> w8 <> w9 <> w10 <> w11 <> w12 <> w13 <> w14 <> w15 <> Nil{}:
      {==}
    case w0 <> w1 <> w2 <> w3 <> w4 <> w5 <> w6 <> w7 <> w8 <> w9 <> w10 <> w11 <> w12 <> w13 <> w14 <> w15 <> w16 <> Nil{}:
      {==}
    case w0 <> w1 <> w2 <> w3 <> w4 <> w5 <> w6 <> w7 <> w8 <> w9 <> w10 <> w11 <> w12 <> w13 <> w14 <> w15 <> w16 <> w17 <> Nil{}:
      {==}
    case w0 <> w1 <> w2 <> w3 <> w4 <> w5 <> w6 <> w7 <> w8 <> w9 <> w10 <> w11 <> w12 <> w13 <> w14 <> w15 <> w16 <> w17 <> w18 <> Nil{}:
      {==}
    case w0 <> w1 <> w2 <> w3 <> w4 <> w5 <> w6 <> w7 <> w8 <> w9 <> w10 <> w11 <> w12 <> w13 <> w14 <> w15 <> w16 <> w17 <> w18 <> w19 <> Nil{}:
      {==}
    case w0 <> w1 <> w2 <> w3 <> w4 <> w5 <> w6 <> w7 <> w8 <> w9 <> w10 <> w11 <> w12 <> w13 <> w14 <> w15 <> w16 <> w17 <> w18 <> w19 <> w20 <> Nil{}:
      {==}
    case w0 <> w1 <> w2 <> w3 <> w4 <> w5 <> w6 <> w7 <> w8 <> w9 <> w10 <> w11 <> w12 <> w13 <> w14 <> w15 <> w16 <> w17 <> w18 <> w19 <> w20 <> w21 <> Nil{}:
      {==}
    case w0 <> w1 <> w2 <> w3 <> w4 <> w5 <> w6 <> w7 <> w8 <> w9 <> w10 <> w11 <> w12 <> w13 <> w14 <> w15 <> w16 <> w17 <> w18 <> w19 <> w20 <> w21 <> w22 <> Nil{}:
      {==}
    case w0 <> w1 <> w2 <> w3 <> w4 <> w5 <> w6 <> w7 <> w8 <> w9 <> w10 <> w11 <> w12 <> w13 <> w14 <> w15 <> w16 <> w17 <> w18 <> w19 <> w20 <> w21 <> w22 <> w23 <> Nil{}:
      {==}
    case w0 <> w1 <> w2 <> w3 <> w4 <> w5 <> w6 <> w7 <> w8 <> w9 <> w10 <> w11 <> w12 <> w13 <> w14 <> w15 <> w16 <> w17 <> w18 <> w19 <> w20 <> w21 <> w22 <> w23 <> w24 <> Nil{}:
      {==}
    case w0 <> w1 <> w2 <> w3 <> w4 <> w5 <> w6 <> w7 <> w8 <> w9 <> w10 <> w11 <> w12 <> w13 <> w14 <> w15 <> w16 <> w17 <> w18 <> w19 <> w20 <> w21 <> w22 <> w23 <> w24 <> w25 <> Nil{}:
      {==}
    case w0 <> w1 <> w2 <> w3 <> w4 <> w5 <> w6 <> w7 <> w8 <> w9 <> w10 <> w11 <> w12 <> w13 <> w14 <> w15 <> w16 <> w17 <> w18 <> w19 <> w20 <> w21 <> w22 <> w23 <> w24 <> w25 <> w26 <> Nil{}:
      {==}
    case w0 <> w1 <> w2 <> w3 <> w4 <> w5 <> w6 <> w7 <> w8 <> w9 <> w10 <> w11 <> w12 <> w13 <> w14 <> w15 <> w16 <> w17 <> w18 <> w19 <> w20 <> w21 <> w22 <> w23 <> w24 <> w25 <> w26 <> w27 <> Nil{}:
      {==}
    case w0 <> w1 <> w2 <> w3 <> w4 <> w5 <> w6 <> w7 <> w8 <> w9 <> w10 <> w11 <> w12 <> w13 <> w14 <> w15 <> w16 <> w17 <> w18 <> w19 <> w20 <> w21 <> w22 <> w23 <> w24 <> w25 <> w26 <> w27 <> w28 <> Nil{}:
      {==}
    case w0 <> w1 <> w2 <> w3 <> w4 <> w5 <> w6 <> w7 <> w8 <> w9 <> w10 <> w11 <> w12 <> w13 <> w14 <> w15 <> w16 <> w17 <> w18 <> w19 <> w20 <> w21 <> w22 <> w23 <> w24 <> w25 <> w26 <> w27 <> w28 <> w29 <> Nil{}:
      {==}
    case w0 <> w1 <> w2 <> w3 <> w4 <> w5 <> w6 <> w7 <> w8 <> w9 <> w10 <> w11 <> w12 <> w13 <> w14 <> w15 <> w16 <> w17 <> w18 <> w19 <> w20 <> w21 <> w22 <> w23 <> w24 <> w25 <> w26 <> w27 <> w28 <> w29 <> w30 <> Nil{}:
      {==}
    case w0 <> w1 <> w2 <> w3 <> w4 <> w5 <> w6 <> w7 <> w8 <> w9 <> w10 <> w11 <> w12 <> w13 <> w14 <> w15 <> w16 <> w17 <> w18 <> w19 <> w20 <> w21 <> w22 <> w23 <> w24 <> w25 <> w26 <> w27 <> w28 <> w29 <> w30 <> w31 <> rest:
      {==}

def rows_eq7(+r0: T.State, +r1: T.State, +r2: T.State, +r3: T.State, +r4: T.State, +r5: T.State, +r6: T.State, p: T.State & List<&2, U32>) -> {SB.rows8_7(r0, r1, r2, r3, r4, r5, r6, p) == SA.rows_of7(r0, r1, r2, r3, r4, r5, r6, p) : A.Block}:
  match p:
    case Tuple{+x, ws}:
      {==}

def rows_eq6(+r0: T.State, +r1: T.State, +r2: T.State, +r3: T.State, +r4: T.State, +r5: T.State, p: T.State & List<&2, U32>) -> {SB.rows8_6(r0, r1, r2, r3, r4, r5, p) == SA.rows_of6(r0, r1, r2, r3, r4, r5, p) : A.Block}:
  match p:
    case Tuple{+x, +ws}:
      Equal.trans(A.Block, SB.rows8_7(r0, r1, r2, r3, r4, r5, x, SB.row(ws)), SB.rows8_7(r0, r1, r2, r3, r4, r5, x, SA.row_of(ws)), SA.rows_of7(r0, r1, r2, r3, r4, r5, x, SA.row_of(ws)),
        Equal.cong(T.State & List<&2, U32>, A.Block, z => SB.rows8_7(r0, r1, r2, r3, r4, r5, x, z), SB.row(ws), SA.row_of(ws), row_eq(ws)),
        rows_eq7(r0, r1, r2, r3, r4, r5, x, SA.row_of(ws)))

def rows_eq5(+r0: T.State, +r1: T.State, +r2: T.State, +r3: T.State, +r4: T.State, p: T.State & List<&2, U32>) -> {SB.rows8_5(r0, r1, r2, r3, r4, p) == SA.rows_of5(r0, r1, r2, r3, r4, p) : A.Block}:
  match p:
    case Tuple{+x, +ws}:
      Equal.trans(A.Block, SB.rows8_6(r0, r1, r2, r3, r4, x, SB.row(ws)), SB.rows8_6(r0, r1, r2, r3, r4, x, SA.row_of(ws)), SA.rows_of6(r0, r1, r2, r3, r4, x, SA.row_of(ws)),
        Equal.cong(T.State & List<&2, U32>, A.Block, z => SB.rows8_6(r0, r1, r2, r3, r4, x, z), SB.row(ws), SA.row_of(ws), row_eq(ws)),
        rows_eq6(r0, r1, r2, r3, r4, x, SA.row_of(ws)))

def rows_eq4(+r0: T.State, +r1: T.State, +r2: T.State, +r3: T.State, p: T.State & List<&2, U32>) -> {SB.rows8_4(r0, r1, r2, r3, p) == SA.rows_of4(r0, r1, r2, r3, p) : A.Block}:
  match p:
    case Tuple{+x, +ws}:
      Equal.trans(A.Block, SB.rows8_5(r0, r1, r2, r3, x, SB.row(ws)), SB.rows8_5(r0, r1, r2, r3, x, SA.row_of(ws)), SA.rows_of5(r0, r1, r2, r3, x, SA.row_of(ws)),
        Equal.cong(T.State & List<&2, U32>, A.Block, z => SB.rows8_5(r0, r1, r2, r3, x, z), SB.row(ws), SA.row_of(ws), row_eq(ws)),
        rows_eq5(r0, r1, r2, r3, x, SA.row_of(ws)))

def rows_eq3(+r0: T.State, +r1: T.State, +r2: T.State, p: T.State & List<&2, U32>) -> {SB.rows8_3(r0, r1, r2, p) == SA.rows_of3(r0, r1, r2, p) : A.Block}:
  match p:
    case Tuple{+x, +ws}:
      Equal.trans(A.Block, SB.rows8_4(r0, r1, r2, x, SB.row(ws)), SB.rows8_4(r0, r1, r2, x, SA.row_of(ws)), SA.rows_of4(r0, r1, r2, x, SA.row_of(ws)),
        Equal.cong(T.State & List<&2, U32>, A.Block, z => SB.rows8_4(r0, r1, r2, x, z), SB.row(ws), SA.row_of(ws), row_eq(ws)),
        rows_eq4(r0, r1, r2, x, SA.row_of(ws)))

def rows_eq2(+r0: T.State, +r1: T.State, p: T.State & List<&2, U32>) -> {SB.rows8_2(r0, r1, p) == SA.rows_of2(r0, r1, p) : A.Block}:
  match p:
    case Tuple{+x, +ws}:
      Equal.trans(A.Block, SB.rows8_3(r0, r1, x, SB.row(ws)), SB.rows8_3(r0, r1, x, SA.row_of(ws)), SA.rows_of3(r0, r1, x, SA.row_of(ws)),
        Equal.cong(T.State & List<&2, U32>, A.Block, z => SB.rows8_3(r0, r1, x, z), SB.row(ws), SA.row_of(ws), row_eq(ws)),
        rows_eq3(r0, r1, x, SA.row_of(ws)))

def rows_eq1(+r0: T.State, p: T.State & List<&2, U32>) -> {SB.rows8_1(r0, p) == SA.rows_of1(r0, p) : A.Block}:
  match p:
    case Tuple{+x, +ws}:
      Equal.trans(A.Block, SB.rows8_2(r0, x, SB.row(ws)), SB.rows8_2(r0, x, SA.row_of(ws)), SA.rows_of2(r0, x, SA.row_of(ws)),
        Equal.cong(T.State & List<&2, U32>, A.Block, z => SB.rows8_2(r0, x, z), SB.row(ws), SA.row_of(ws), row_eq(ws)),
        rows_eq2(r0, x, SA.row_of(ws)))

def rows_eq0(p: T.State & List<&2, U32>) -> {SB.rows8_0(p) == SA.rows_of0(p) : A.Block}:
  match p:
    case Tuple{+x, +ws}:
      Equal.trans(A.Block, SB.rows8_1(x, SB.row(ws)), SB.rows8_1(x, SA.row_of(ws)), SA.rows_of1(x, SA.row_of(ws)),
        Equal.cong(T.State & List<&2, U32>, A.Block, z => SB.rows8_1(x, z), SB.row(ws), SA.row_of(ws), row_eq(ws)),
        rows_eq1(x, SA.row_of(ws)))

def rows8_eq(+ws: List<&2, U32>) -> {SB.rows8(ws) == SA.rows_of0(SA.row_of(ws)) : A.Block}:
  Equal.trans(A.Block, SB.rows8_0(SB.row(ws)), SB.rows8_0(SA.row_of(ws)), SA.rows_of0(SA.row_of(ws)),
    Equal.cong(T.State & List<&2, U32>, A.Block, z => SB.rows8_0(z), SB.row(ws), SA.row_of(ws), row_eq(ws)),
    rows_eq0(SA.row_of(ws)))

# A block from 1024 bytes.
def block_of_eq(+bs: List<&2, U32>) -> {I.block_of(bs) == SA.block_of(bs) : A.Block}:
  Equal.trans(A.Block, SB.rows8(IH.words(bs)), SB.rows8(SA.words(bs)), SA.block_of(bs),
    Equal.cong(List<&2, U32>, A.Block, z => SB.rows8(z), IH.words(bs), SA.words(bs), words_eq(bs)),
    rows8_eq(SA.words(bs)))

def state_bytes_eq(+v: T.State) -> {I.state_bytes(v) == SA.state_bytes(v) : List<&2, U32>}:
  match v:
    case T.V{T.W{l0, h0}, T.W{l1, h1}, T.W{l2, h2}, T.W{l3, h3}, T.W{l4, h4}, T.W{l5, h5}, T.W{l6, h6}, T.W{l7, h7}, T.W{l8, h8}, T.W{l9, h9}, T.W{l10, h10}, T.W{l11, h11}, T.W{l12, h12}, T.W{l13, h13}, T.W{l14, h14}, T.W{l15, h15}}:
      {==}

# The bytes of a block, row by row.
def block_bytes_eq(+b: A.Block) -> {I.block_bytes(b) == SA.block_bytes(b) : List<&2, U32>}:
  match b:
    case A.B{+r0, +r1, +r2, +r3, +r4, +r5, +r6, +r7}:
      %Equal.sym(List<&2, U32>, I.state_bytes(r0), SA.state_bytes(r0), state_bytes_eq(r0)) : {List.concat(&2, U32, [_, I.state_bytes(r1), I.state_bytes(r2), I.state_bytes(r3), I.state_bytes(r4), I.state_bytes(r5), I.state_bytes(r6), I.state_bytes(r7)]) == SA.block_bytes(A.B{r0, r1, r2, r3, r4, r5, r6, r7}) : List<&2, U32>}
      %Equal.sym(List<&2, U32>, I.state_bytes(r1), SA.state_bytes(r1), state_bytes_eq(r1)) : {List.concat(&2, U32, [SA.state_bytes(r0), _, I.state_bytes(r2), I.state_bytes(r3), I.state_bytes(r4), I.state_bytes(r5), I.state_bytes(r6), I.state_bytes(r7)]) == SA.block_bytes(A.B{r0, r1, r2, r3, r4, r5, r6, r7}) : List<&2, U32>}
      %Equal.sym(List<&2, U32>, I.state_bytes(r2), SA.state_bytes(r2), state_bytes_eq(r2)) : {List.concat(&2, U32, [SA.state_bytes(r0), SA.state_bytes(r1), _, I.state_bytes(r3), I.state_bytes(r4), I.state_bytes(r5), I.state_bytes(r6), I.state_bytes(r7)]) == SA.block_bytes(A.B{r0, r1, r2, r3, r4, r5, r6, r7}) : List<&2, U32>}
      %Equal.sym(List<&2, U32>, I.state_bytes(r3), SA.state_bytes(r3), state_bytes_eq(r3)) : {List.concat(&2, U32, [SA.state_bytes(r0), SA.state_bytes(r1), SA.state_bytes(r2), _, I.state_bytes(r4), I.state_bytes(r5), I.state_bytes(r6), I.state_bytes(r7)]) == SA.block_bytes(A.B{r0, r1, r2, r3, r4, r5, r6, r7}) : List<&2, U32>}
      %Equal.sym(List<&2, U32>, I.state_bytes(r4), SA.state_bytes(r4), state_bytes_eq(r4)) : {List.concat(&2, U32, [SA.state_bytes(r0), SA.state_bytes(r1), SA.state_bytes(r2), SA.state_bytes(r3), _, I.state_bytes(r5), I.state_bytes(r6), I.state_bytes(r7)]) == SA.block_bytes(A.B{r0, r1, r2, r3, r4, r5, r6, r7}) : List<&2, U32>}
      %Equal.sym(List<&2, U32>, I.state_bytes(r5), SA.state_bytes(r5), state_bytes_eq(r5)) : {List.concat(&2, U32, [SA.state_bytes(r0), SA.state_bytes(r1), SA.state_bytes(r2), SA.state_bytes(r3), SA.state_bytes(r4), _, I.state_bytes(r6), I.state_bytes(r7)]) == SA.block_bytes(A.B{r0, r1, r2, r3, r4, r5, r6, r7}) : List<&2, U32>}
      %Equal.sym(List<&2, U32>, I.state_bytes(r6), SA.state_bytes(r6), state_bytes_eq(r6)) : {List.concat(&2, U32, [SA.state_bytes(r0), SA.state_bytes(r1), SA.state_bytes(r2), SA.state_bytes(r3), SA.state_bytes(r4), SA.state_bytes(r5), _, I.state_bytes(r7)]) == SA.block_bytes(A.B{r0, r1, r2, r3, r4, r5, r6, r7}) : List<&2, U32>}
      %Equal.sym(List<&2, U32>, I.state_bytes(r7), SA.state_bytes(r7), state_bytes_eq(r7)) : {List.concat(&2, U32, [SA.state_bytes(r0), SA.state_bytes(r1), SA.state_bytes(r2), SA.state_bytes(r3), SA.state_bytes(r4), SA.state_bytes(r5), SA.state_bytes(r6), _]) == SA.block_bytes(A.B{r0, r1, r2, r3, r4, r5, r6, r7}) : List<&2, U32>}
      {==}
