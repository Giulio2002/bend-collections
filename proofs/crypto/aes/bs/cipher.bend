import Base
import ../../../lib/nat.bend as N
import ../../../../src/crypto/aes/types.bend as T
import ../../../../src/crypto/aes/aes.bend as A
import ../../../../src/crypto/aes/bitslice.bend as X
import ../../../../src/crypto/aes/fast.bend as F
import ./defs.bend as D
import ./layers.bend as L

# The bitsliced cipher of fast.bend on two blocks gives the 32 output bytes of
# aes.bend's cipher on each block, for every key schedule of the right length
# (2 + (Nr - 1) round keys: fast.bend checks it and otherwise uses gcm.bend).

def nat_disc(n: Nat) -> Type:
  match n:
    case 0n: Unit
    case 1n+p: Empty

def zero_succ(-G: Type, +n: Nat, h: {0n == 1n+n : Nat}) -> G:
  Empty.absurd(G, %h : nat_disc(_); Unit{})

def rounds_ok(+n: Nat, +sa: T.State, +sb: T.State, +ks: List<&2, T.State>, +h: {List.length(&2, T.State, ks) == 1n+n : Nat}) -> {F.stream(F.unplane(F.rounds(n, D.B(sa, sb), F.key_planes(ks)))) == List.append(&2, U32, A.bytes_of(A.rounds(n, sa, ks)), A.bytes_of(A.rounds(n, sb, ks))) : List<&2, U32>}:
  match n ks:
    case 0n k <> rest:
      %Equal.sym(X.Q8, X.shift_rows(X.sub_bytes(D.B(sa, sb))), D.B(A.shift_rows(A.sub_bytes(sa)), A.shift_rows(A.sub_bytes(sb))), L.last_ok(sa, sb)) : {F.stream(F.Out{X.ortho(_), k}) == List.append(&2, U32, A.bytes_of(A.last_round(sa, k)), A.bytes_of(A.last_round(sb, k))) : List<&2, U32>}
      %Equal.sym(List<&2, U32>, F.stream(F.Out{X.ortho(D.B(A.shift_rows(A.sub_bytes(sa)), A.shift_rows(A.sub_bytes(sb)))), k}), D.store(A.shift_rows(A.sub_bytes(sa)), A.shift_rows(A.sub_bytes(sb)), k), L.store_ok(A.shift_rows(A.sub_bytes(sa)), A.shift_rows(A.sub_bytes(sb)), k)) : {_ == List.append(&2, U32, A.bytes_of(A.last_round(sa, k)), A.bytes_of(A.last_round(sb, k))) : List<&2, U32>}
      L.store_last(sa, sb, k)
    case 1n+m k <> rest:
      %Equal.sym(X.Q8, X.round(D.B(sa, sb), F.plane_key(k)), D.B(A.round(sa, k), A.round(sb, k)), L.round_ok(sa, sb, k)) : {F.stream(F.unplane(F.rounds(m, _, F.key_planes(rest)))) == List.append(&2, U32, A.bytes_of(A.rounds(m, A.round(sa, k), rest)), A.bytes_of(A.rounds(m, A.round(sb, k), rest))) : List<&2, U32>}
      rounds_ok(m, A.round(sa, k), A.round(sb, k), rest, N.succ_inj(List.length(&2, T.State, rest), 1n+m, h))
    case 0n Nil{}:
      zero_succ({F.stream(F.unplane(F.rounds(0n, D.B(sa, sb), F.key_planes(Nil{})))) == List.append(&2, U32, A.bytes_of(A.rounds(0n, sa, Nil{})), A.bytes_of(A.rounds(0n, sb, Nil{}))) : List<&2, U32>}, 0n, h)
    case 1n+m Nil{}:
      zero_succ({F.stream(F.unplane(F.rounds(1n+m, D.B(sa, sb), F.key_planes(Nil{})))) == List.append(&2, U32, A.bytes_of(A.rounds(1n+m, sa, Nil{})), A.bytes_of(A.rounds(1n+m, sb, Nil{}))) : List<&2, U32>}, 1n+m, h)

def cipher_ok(+nr: Nat, +sa: T.State, +sb: T.State, +ks: List<&2, T.State>, +h: {List.length(&2, T.State, ks) == 2n+Nat.sub(nr, 1n) : Nat}) -> {F.stream(F.unplane(F.cipher(nr, D.B(sa, sb), F.key_planes(ks)))) == List.append(&2, U32, A.bytes_of(A.cipher(nr, sa, ks)), A.bytes_of(A.cipher(nr, sb, ks))) : List<&2, U32>}:
  match ks:
    case k <> rest:
      %Equal.sym(X.Q8, F.plane_key(k), D.B(k, k), L.key_ok(k)) : {F.stream(F.unplane(F.rounds(Nat.sub(nr, 1n), X.add_round_key(D.B(sa, sb), _), F.key_planes(rest)))) == List.append(&2, U32, A.bytes_of(A.rounds(Nat.sub(nr, 1n), A.add_round_key(sa, k), rest)), A.bytes_of(A.rounds(Nat.sub(nr, 1n), A.add_round_key(sb, k), rest))) : List<&2, U32>}
      %Equal.sym(X.Q8, X.add_round_key(D.B(sa, sb), D.B(k, k)), D.B(A.add_round_key(sa, k), A.add_round_key(sb, k)), L.ark_ok(sa, sb, k)) : {F.stream(F.unplane(F.rounds(Nat.sub(nr, 1n), _, F.key_planes(rest)))) == List.append(&2, U32, A.bytes_of(A.rounds(Nat.sub(nr, 1n), A.add_round_key(sa, k), rest)), A.bytes_of(A.rounds(Nat.sub(nr, 1n), A.add_round_key(sb, k), rest))) : List<&2, U32>}
      rounds_ok(Nat.sub(nr, 1n), A.add_round_key(sa, k), A.add_round_key(sb, k), rest, N.succ_inj(List.length(&2, T.State, rest), 1n+Nat.sub(nr, 1n), h))
    case Nil{}:
      zero_succ({F.stream(F.unplane(F.cipher(nr, D.B(sa, sb), F.key_planes(Nil{})))) == List.append(&2, U32, A.bytes_of(A.cipher(nr, sa, Nil{})), A.bytes_of(A.cipher(nr, sb, Nil{}))) : List<&2, U32>}, 1n+Nat.sub(nr, 1n), h)

# Two blocks given as words: the output bytes of the two byte-level ciphers.
def encrypt2_ok(+nr: Nat, +ks: List<&2, T.State>, +h: {List.length(&2, T.State, ks) == 2n+Nat.sub(nr, 1n) : Nat}, +qa0: T.Quad, +qa1: T.Quad, +qa2: T.Quad, +qa3: T.Quad, +qb0: T.Quad, +qb1: T.Quad, +qb2: T.Quad, +qb3: T.Quad) -> {F.stream(F.encrypt2(F.Keys{nr, F.key_planes(ks)}, F.quad_word(qa0), F.quad_word(qa1), F.quad_word(qa2), F.quad_word(qa3), F.quad_word(qb0), F.quad_word(qb1), F.quad_word(qb2), F.quad_word(qb3))) == List.append(&2, U32, A.bytes_of(A.cipher(nr, T.S{qa0, qa1, qa2, qa3}, ks)), A.bytes_of(A.cipher(nr, T.S{qb0, qb1, qb2, qb3}, ks))) : List<&2, U32>}:
  %Equal.sym(X.Q8, X.ortho(X.Q8{F.quad_word(qa0), F.quad_word(qb0), F.quad_word(qa1), F.quad_word(qb1), F.quad_word(qa2), F.quad_word(qb2), F.quad_word(qa3), F.quad_word(qb3)}), D.B(T.S{qa0, qa1, qa2, qa3}, T.S{qb0, qb1, qb2, qb3}), L.load_ok(qa0, qa1, qa2, qa3, qb0, qb1, qb2, qb3)) : {F.stream(F.unplane(F.cipher(nr, _, F.key_planes(ks)))) == List.append(&2, U32, A.bytes_of(A.cipher(nr, T.S{qa0, qa1, qa2, qa3}, ks)), A.bytes_of(A.cipher(nr, T.S{qb0, qb1, qb2, qb3}, ks))) : List<&2, U32>}
  cipher_ok(nr, T.S{qa0, qa1, qa2, qa3}, T.S{qb0, qb1, qb2, qb3}, ks, h)
