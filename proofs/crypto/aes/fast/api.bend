import Base
import ../../../lib/nat.bend as N
import ../../../../src/crypto/aes/types.bend as T
import ../../../../src/crypto/aes/aes.bend as A
import ../../../../src/crypto/aes/gcm.bend as G
import ../../../../src/crypto/aes/fast.bend as F
import ../../../../src/crypto/aesgcm.bend as GCM
import ./gcm.bend as FG

# The byte API of aesgcm.bend (the fast path of fast.bend for well-formed key
# schedules, gcm.bend otherwise) is gcm.bend's, for every input.

def seal_path_ok(+nr: Nat, +ks: List<&2, T.State>, +ok: Bool, +hok: {Nat.is_eq(List.length(&2, T.State, ks), 2n+Nat.sub(nr, 1n)) == ok : Bool}, +nonce: List<&2, U32>, +aad: List<&2, U32>, +pt: List<&2, U32>) -> {GCM.seal_path(ok, A.Schedule{nr, ks}, nonce, aad, pt) == G.seal_nonce(A.Schedule{nr, ks}, nonce, aad, pt) : Maybe<&2, List<&2, U32>>}:
  match ok:
    case True{}:
      FG.seal_nonce_ok(nr, ks, N.eq_from_is_eq(List.length(&2, T.State, ks), 2n+Nat.sub(nr, 1n), hok), nonce, aad, pt)
    case False{}:
      {==}

def open_path_ok(+nr: Nat, +ks: List<&2, T.State>, +ok: Bool, +hok: {Nat.is_eq(List.length(&2, T.State, ks), 2n+Nat.sub(nr, 1n)) == ok : Bool}, +nonce: List<&2, U32>, +aad: List<&2, U32>, +ct: List<&2, U32>) -> {GCM.open_path(ok, A.Schedule{nr, ks}, nonce, aad, ct) == G.open_nonce(A.Schedule{nr, ks}, nonce, aad, ct) : Maybe<&2, List<&2, U32>>}:
  match ok:
    case True{}:
      FG.open_nonce_ok(nr, ks, N.eq_from_is_eq(List.length(&2, T.State, ks), 2n+Nat.sub(nr, 1n), hok), nonce, aad, ct)
    case False{}:
      {==}

def seal_key_ok(+m: Maybe<&2, A.Schedule>, +nonce: List<&2, U32>, +aad: List<&2, U32>, +pt: List<&2, U32>) -> {GCM.seal_key(m, nonce, aad, pt) == G.seal_key(m, nonce, aad, pt) : Maybe<&2, List<&2, U32>>}:
  match m:
    case None{}:
      {==}
    case Some{A.Schedule{nr, ks}}:
      seal_path_ok(nr, ks, F.well_formed(A.Schedule{nr, ks}), {==}, nonce, aad, pt)

def open_key_ok(+m: Maybe<&2, A.Schedule>, +nonce: List<&2, U32>, +aad: List<&2, U32>, +ct: List<&2, U32>) -> {GCM.open_key(m, nonce, aad, ct) == G.open_key(m, nonce, aad, ct) : Maybe<&2, List<&2, U32>>}:
  match m:
    case None{}:
      {==}
    case Some{A.Schedule{nr, ks}}:
      open_path_ok(nr, ks, F.well_formed(A.Schedule{nr, ks}), {==}, nonce, aad, ct)
