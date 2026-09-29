import Base
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../../../src/crypto/aes/types.bend as T
import ../../../src/crypto/aes/aes.bend as A
import ../../../src/crypto/aes/gcm.bend as GI
import ../../../src/crypto/aesgcm.bend as GCM
import ../../../spec/crypto/aes/aes.bend as S
import ../../../spec/crypto/aes/gcm.bend as G
import ./gcm.bend as GP
import ./aead.bend as AD

# The AES-128-GCM / AES-256-GCM API clauses of laws.bend (Api128/Api256
# encrypt, decrypt, roundtrip, forgery) as plain lemmas: proof.bend fills the
# laws with them, and the AEAD facade (proofs/crypto/aead) imports them
# (importing proof.bend would stop it being the aes package's root). The
# *_l versions take the nonce and tag as lists of the right length.

def valid_of(+key: List<&2, U32>, +w: Nat, +h: {List.length(&2, U32, key) == w : Nat}, +v: {A.valid_length(w) == True{} : Bool}) -> {A.valid_length(List.length(&2, U32, key)) == True{} : Bool}:
  %Equal.sym(Nat, List.length(&2, U32, key), w, h) : {A.valid_length(_) == True{} : Bool}
  v

# Decrypt what an encryption returned (None stays None).
def open128(+key: List<&2, U32>, +nonce: List<&2, U32>, +aad: List<&2, U32>, m: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match m:
    case None{}:
      None{}
    case Some{ct}:
      GCM.aes128_gcm_decrypt(key, nonce, aad, ct)

def open256(+key: List<&2, U32>, +nonce: List<&2, U32>, +aad: List<&2, U32>, m: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match m:
    case None{}:
      None{}
    case Some{ct}:
      GCM.aes256_gcm_decrypt(key, nonce, aad, ct)

law aes128_encrypt:
  for +key: List<&2, U32>
  for +h: {List.length(&2, U32, key) == 16n : Nat}
  for +n0: U32
  for +n1: U32
  for +n2: U32
  for +n3: U32
  for +n4: U32
  for +n5: U32
  for +n6: U32
  for +n7: U32
  for +n8: U32
  for +n9: U32
  for +n10: U32
  for +n11: U32
  for +aad: List<&2, U32>
  for +pt: List<&2, U32>
  {GCM.aes128_gcm_encrypt(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, pt) == Some{G.aes_seal(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, pt)} : Maybe<&2, List<&2, U32>>}

def aes128_encrypt(key, h, n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, aad, pt):
  %Equal.sym(Nat, List.length(&2, U32, key), 16n, h) : {GI.seal_key(GI.schedule_if(Nat.is_eq(_, 16n), key), [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, pt) == Some{G.aes_seal(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, pt)} : Maybe<&2, List<&2, U32>>}
  %Equal.sym(Bool, A.valid_length(List.length(&2, U32, key)), True{}, valid_of(key, 16n, h, {==})) : {GI.seal_key(A.schedule_if(_, Nat.div(List.length(&2, U32, key), 4n), key), [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, pt) == Some{G.aes_seal(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, pt)} : Maybe<&2, List<&2, U32>>}
  %GP.seal_ok(S.nk(key), S.nr(key), key, T.W{n0, n1, n2, n3}, T.W{n4, n5, n6, n7}, T.W{n8, n9, n10, n11}, aad, pt) : {Some{GI.seal_core(A.Schedule{S.nr(key), A.expand(S.nk(key), S.nr(key), key)}, T.W{n0, n1, n2, n3}, T.W{n4, n5, n6, n7}, T.W{n8, n9, n10, n11}, aad, pt)} == Some{_} : Maybe<&2, List<&2, U32>>}
  {==}

law aes128_decrypt:
  for +key: List<&2, U32>
  for +h: {List.length(&2, U32, key) == 16n : Nat}
  for +n0: U32
  for +n1: U32
  for +n2: U32
  for +n3: U32
  for +n4: U32
  for +n5: U32
  for +n6: U32
  for +n7: U32
  for +n8: U32
  for +n9: U32
  for +n10: U32
  for +n11: U32
  for +aad: List<&2, U32>
  for +ct: List<&2, U32>
  {GCM.aes128_gcm_decrypt(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, ct) == G.aes_open(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, ct) : Maybe<&2, List<&2, U32>>}

def aes128_decrypt(key, h, n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, aad, ct):
  %Equal.sym(Nat, List.length(&2, U32, key), 16n, h) : {GI.open_key(GI.schedule_if(Nat.is_eq(_, 16n), key), [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, ct) == G.aes_open(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, ct) : Maybe<&2, List<&2, U32>>}
  %Equal.sym(Bool, A.valid_length(List.length(&2, U32, key)), True{}, valid_of(key, 16n, h, {==})) : {GI.open_key(A.schedule_if(_, Nat.div(List.length(&2, U32, key), 4n), key), [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, ct) == G.aes_open(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, ct) : Maybe<&2, List<&2, U32>>}
  GP.open_ok(S.nk(key), S.nr(key), key, T.W{n0, n1, n2, n3}, T.W{n4, n5, n6, n7}, T.W{n8, n9, n10, n11}, aad, ct)

law aes128_roundtrip:
  for +key: List<&2, U32>
  for +h: {List.length(&2, U32, key) == 16n : Nat}
  for +n0: U32
  for +n1: U32
  for +n2: U32
  for +n3: U32
  for +n4: U32
  for +n5: U32
  for +n6: U32
  for +n7: U32
  for +n8: U32
  for +n9: U32
  for +n10: U32
  for +n11: U32
  for +aad: List<&2, U32>
  for +pt: List<&2, U32>
  {open128(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, GCM.aes128_gcm_encrypt(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, pt)) == Some{pt} : Maybe<&2, List<&2, U32>>}

def aes128_roundtrip(key, h, n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, aad, pt):
  %Equal.sym(Maybe<&2, List<&2, U32>>, GCM.aes128_gcm_encrypt(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, pt), Some{G.aes_seal(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, pt)}, aes128_encrypt(key, h, n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, aad, pt)) : {open128(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, _) == Some{pt} : Maybe<&2, List<&2, U32>>}
  %Equal.sym(Maybe<&2, List<&2, U32>>, GCM.aes128_gcm_decrypt(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, G.aes_seal(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, pt)), G.aes_open(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, G.aes_seal(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, pt)), aes128_decrypt(key, h, n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, aad, G.aes_seal(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, pt))) : {_ == Some{pt} : Maybe<&2, List<&2, U32>>}
  AD.roundtrip(S.nk(key), S.nr(key), key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, pt)

law aes128_forgery:
  for +key: List<&2, U32>
  for +h: {List.length(&2, U32, key) == 16n : Nat}
  for +n0: U32
  for +n1: U32
  for +n2: U32
  for +n3: U32
  for +n4: U32
  for +n5: U32
  for +n6: U32
  for +n7: U32
  for +n8: U32
  for +n9: U32
  for +n10: U32
  for +n11: U32
  for +aad: List<&2, U32>
  for +c: List<&2, U32>
  for +t0: U32
  for +t1: U32
  for +t2: U32
  for +t3: U32
  for +t4: U32
  for +t5: U32
  for +t6: U32
  for +t7: U32
  for +t8: U32
  for +t9: U32
  for +t10: U32
  for +t11: U32
  for +t12: U32
  for +t13: U32
  for +t14: U32
  for +t15: U32
  for ne: {[t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15] != G.aes_tag(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, c) : List<&2, U32>}
  {GCM.aes128_gcm_decrypt(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, List.append(&2, U32, c, [t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15])) == None{} : Maybe<&2, List<&2, U32>>}

def aes128_forgery(key, h, n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, aad, c, t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, ne):
  %Equal.sym(Maybe<&2, List<&2, U32>>, GCM.aes128_gcm_decrypt(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, List.append(&2, U32, c, [t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15])), G.aes_open(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, List.append(&2, U32, c, [t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15])), aes128_decrypt(key, h, n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, aad, List.append(&2, U32, c, [t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15]))) : {_ == None{} : Maybe<&2, List<&2, U32>>}
  AD.forgery(S.nk(key), S.nr(key), key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, c, t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, ne)

law aes256_encrypt:
  for +key: List<&2, U32>
  for +h: {List.length(&2, U32, key) == 32n : Nat}
  for +n0: U32
  for +n1: U32
  for +n2: U32
  for +n3: U32
  for +n4: U32
  for +n5: U32
  for +n6: U32
  for +n7: U32
  for +n8: U32
  for +n9: U32
  for +n10: U32
  for +n11: U32
  for +aad: List<&2, U32>
  for +pt: List<&2, U32>
  {GCM.aes256_gcm_encrypt(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, pt) == Some{G.aes_seal(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, pt)} : Maybe<&2, List<&2, U32>>}

def aes256_encrypt(key, h, n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, aad, pt):
  %Equal.sym(Nat, List.length(&2, U32, key), 32n, h) : {GI.seal_key(GI.schedule_if(Nat.is_eq(_, 32n), key), [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, pt) == Some{G.aes_seal(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, pt)} : Maybe<&2, List<&2, U32>>}
  %Equal.sym(Bool, A.valid_length(List.length(&2, U32, key)), True{}, valid_of(key, 32n, h, {==})) : {GI.seal_key(A.schedule_if(_, Nat.div(List.length(&2, U32, key), 4n), key), [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, pt) == Some{G.aes_seal(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, pt)} : Maybe<&2, List<&2, U32>>}
  %GP.seal_ok(S.nk(key), S.nr(key), key, T.W{n0, n1, n2, n3}, T.W{n4, n5, n6, n7}, T.W{n8, n9, n10, n11}, aad, pt) : {Some{GI.seal_core(A.Schedule{S.nr(key), A.expand(S.nk(key), S.nr(key), key)}, T.W{n0, n1, n2, n3}, T.W{n4, n5, n6, n7}, T.W{n8, n9, n10, n11}, aad, pt)} == Some{_} : Maybe<&2, List<&2, U32>>}
  {==}

law aes256_decrypt:
  for +key: List<&2, U32>
  for +h: {List.length(&2, U32, key) == 32n : Nat}
  for +n0: U32
  for +n1: U32
  for +n2: U32
  for +n3: U32
  for +n4: U32
  for +n5: U32
  for +n6: U32
  for +n7: U32
  for +n8: U32
  for +n9: U32
  for +n10: U32
  for +n11: U32
  for +aad: List<&2, U32>
  for +ct: List<&2, U32>
  {GCM.aes256_gcm_decrypt(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, ct) == G.aes_open(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, ct) : Maybe<&2, List<&2, U32>>}

def aes256_decrypt(key, h, n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, aad, ct):
  %Equal.sym(Nat, List.length(&2, U32, key), 32n, h) : {GI.open_key(GI.schedule_if(Nat.is_eq(_, 32n), key), [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, ct) == G.aes_open(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, ct) : Maybe<&2, List<&2, U32>>}
  %Equal.sym(Bool, A.valid_length(List.length(&2, U32, key)), True{}, valid_of(key, 32n, h, {==})) : {GI.open_key(A.schedule_if(_, Nat.div(List.length(&2, U32, key), 4n), key), [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, ct) == G.aes_open(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, ct) : Maybe<&2, List<&2, U32>>}
  GP.open_ok(S.nk(key), S.nr(key), key, T.W{n0, n1, n2, n3}, T.W{n4, n5, n6, n7}, T.W{n8, n9, n10, n11}, aad, ct)

law aes256_roundtrip:
  for +key: List<&2, U32>
  for +h: {List.length(&2, U32, key) == 32n : Nat}
  for +n0: U32
  for +n1: U32
  for +n2: U32
  for +n3: U32
  for +n4: U32
  for +n5: U32
  for +n6: U32
  for +n7: U32
  for +n8: U32
  for +n9: U32
  for +n10: U32
  for +n11: U32
  for +aad: List<&2, U32>
  for +pt: List<&2, U32>
  {open256(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, GCM.aes256_gcm_encrypt(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, pt)) == Some{pt} : Maybe<&2, List<&2, U32>>}

def aes256_roundtrip(key, h, n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, aad, pt):
  %Equal.sym(Maybe<&2, List<&2, U32>>, GCM.aes256_gcm_encrypt(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, pt), Some{G.aes_seal(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, pt)}, aes256_encrypt(key, h, n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, aad, pt)) : {open256(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, _) == Some{pt} : Maybe<&2, List<&2, U32>>}
  %Equal.sym(Maybe<&2, List<&2, U32>>, GCM.aes256_gcm_decrypt(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, G.aes_seal(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, pt)), G.aes_open(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, G.aes_seal(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, pt)), aes256_decrypt(key, h, n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, aad, G.aes_seal(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, pt))) : {_ == Some{pt} : Maybe<&2, List<&2, U32>>}
  AD.roundtrip(S.nk(key), S.nr(key), key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, pt)

law aes256_forgery:
  for +key: List<&2, U32>
  for +h: {List.length(&2, U32, key) == 32n : Nat}
  for +n0: U32
  for +n1: U32
  for +n2: U32
  for +n3: U32
  for +n4: U32
  for +n5: U32
  for +n6: U32
  for +n7: U32
  for +n8: U32
  for +n9: U32
  for +n10: U32
  for +n11: U32
  for +aad: List<&2, U32>
  for +c: List<&2, U32>
  for +t0: U32
  for +t1: U32
  for +t2: U32
  for +t3: U32
  for +t4: U32
  for +t5: U32
  for +t6: U32
  for +t7: U32
  for +t8: U32
  for +t9: U32
  for +t10: U32
  for +t11: U32
  for +t12: U32
  for +t13: U32
  for +t14: U32
  for +t15: U32
  for ne: {[t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15] != G.aes_tag(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, c) : List<&2, U32>}
  {GCM.aes256_gcm_decrypt(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, List.append(&2, U32, c, [t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15])) == None{} : Maybe<&2, List<&2, U32>>}

def aes256_forgery(key, h, n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, aad, c, t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, ne):
  %Equal.sym(Maybe<&2, List<&2, U32>>, GCM.aes256_gcm_decrypt(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, List.append(&2, U32, c, [t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15])), G.aes_open(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, List.append(&2, U32, c, [t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15])), aes256_decrypt(key, h, n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, aad, List.append(&2, U32, c, [t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15]))) : {_ == None{} : Maybe<&2, List<&2, U32>>}
  AD.forgery(S.nk(key), S.nr(key), key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, c, t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, ne)


# ---- the same for any nonce (and tag) list of the right length

def no_len(-G: Type, +n: Nat, +m: Nat, +h: {n == m : Nat}, +hf: {Nat.is_eq(n, m) == False{} : Bool}) -> G:
  Empty.absurd(G, L.false_true(Equal.trans(Bool, False{}, Nat.is_eq(n, m), True{}, Equal.sym(Bool, Nat.is_eq(n, m), False{}, hf),
    Equal.trans(Bool, Nat.is_eq(n, m), Nat.is_eq(m, m), True{}, Equal.cong(Nat, Bool, x => Nat.is_eq(x, m), n, m, h), N.is_eq_refl(m)))))

law aes128_encrypt_l:
  for +key: List<&2, U32>
  for +h: {List.length(&2, U32, key) == 16n : Nat}
  for +nonce: List<&2, U32>
  for +hn: {List.length(&2, U32, nonce) == 12n : Nat}
  for +aad: List<&2, U32>
  for +pt: List<&2, U32>
  {GCM.aes128_gcm_encrypt(key, nonce, aad, pt) == Some{G.aes_seal(key, nonce, aad, pt)} : Maybe<&2, List<&2, U32>>}

def aes128_encrypt_l(key, h, nonce, hn, aad, pt):
  match nonce:
    case Nil{}: no_len({GCM.aes128_gcm_encrypt(key, {Nil{} : List<&2, U32>}, aad, pt) == Some{G.aes_seal(key, {Nil{} : List<&2, U32>}, aad, pt)} : Maybe<&2, List<&2, U32>>}, 0n, 12n, hn, {==})
    case n0 <> Nil{}: no_len({GCM.aes128_gcm_encrypt(key, {[n0] : List<&2, U32>}, aad, pt) == Some{G.aes_seal(key, {[n0] : List<&2, U32>}, aad, pt)} : Maybe<&2, List<&2, U32>>}, 1n, 12n, hn, {==})
    case n0 <> n1 <> Nil{}: no_len({GCM.aes128_gcm_encrypt(key, {[n0, n1] : List<&2, U32>}, aad, pt) == Some{G.aes_seal(key, {[n0, n1] : List<&2, U32>}, aad, pt)} : Maybe<&2, List<&2, U32>>}, 2n, 12n, hn, {==})
    case n0 <> n1 <> n2 <> Nil{}: no_len({GCM.aes128_gcm_encrypt(key, {[n0, n1, n2] : List<&2, U32>}, aad, pt) == Some{G.aes_seal(key, {[n0, n1, n2] : List<&2, U32>}, aad, pt)} : Maybe<&2, List<&2, U32>>}, 3n, 12n, hn, {==})
    case n0 <> n1 <> n2 <> n3 <> Nil{}: no_len({GCM.aes128_gcm_encrypt(key, {[n0, n1, n2, n3] : List<&2, U32>}, aad, pt) == Some{G.aes_seal(key, {[n0, n1, n2, n3] : List<&2, U32>}, aad, pt)} : Maybe<&2, List<&2, U32>>}, 4n, 12n, hn, {==})
    case n0 <> n1 <> n2 <> n3 <> n4 <> Nil{}: no_len({GCM.aes128_gcm_encrypt(key, {[n0, n1, n2, n3, n4] : List<&2, U32>}, aad, pt) == Some{G.aes_seal(key, {[n0, n1, n2, n3, n4] : List<&2, U32>}, aad, pt)} : Maybe<&2, List<&2, U32>>}, 5n, 12n, hn, {==})
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> Nil{}: no_len({GCM.aes128_gcm_encrypt(key, {[n0, n1, n2, n3, n4, n5] : List<&2, U32>}, aad, pt) == Some{G.aes_seal(key, {[n0, n1, n2, n3, n4, n5] : List<&2, U32>}, aad, pt)} : Maybe<&2, List<&2, U32>>}, 6n, 12n, hn, {==})
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> Nil{}: no_len({GCM.aes128_gcm_encrypt(key, {[n0, n1, n2, n3, n4, n5, n6] : List<&2, U32>}, aad, pt) == Some{G.aes_seal(key, {[n0, n1, n2, n3, n4, n5, n6] : List<&2, U32>}, aad, pt)} : Maybe<&2, List<&2, U32>>}, 7n, 12n, hn, {==})
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> n7 <> Nil{}: no_len({GCM.aes128_gcm_encrypt(key, {[n0, n1, n2, n3, n4, n5, n6, n7] : List<&2, U32>}, aad, pt) == Some{G.aes_seal(key, {[n0, n1, n2, n3, n4, n5, n6, n7] : List<&2, U32>}, aad, pt)} : Maybe<&2, List<&2, U32>>}, 8n, 12n, hn, {==})
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> n7 <> n8 <> Nil{}: no_len({GCM.aes128_gcm_encrypt(key, {[n0, n1, n2, n3, n4, n5, n6, n7, n8] : List<&2, U32>}, aad, pt) == Some{G.aes_seal(key, {[n0, n1, n2, n3, n4, n5, n6, n7, n8] : List<&2, U32>}, aad, pt)} : Maybe<&2, List<&2, U32>>}, 9n, 12n, hn, {==})
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> n7 <> n8 <> n9 <> Nil{}: no_len({GCM.aes128_gcm_encrypt(key, {[n0, n1, n2, n3, n4, n5, n6, n7, n8, n9] : List<&2, U32>}, aad, pt) == Some{G.aes_seal(key, {[n0, n1, n2, n3, n4, n5, n6, n7, n8, n9] : List<&2, U32>}, aad, pt)} : Maybe<&2, List<&2, U32>>}, 10n, 12n, hn, {==})
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> n7 <> n8 <> n9 <> n10 <> Nil{}: no_len({GCM.aes128_gcm_encrypt(key, {[n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10] : List<&2, U32>}, aad, pt) == Some{G.aes_seal(key, {[n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10] : List<&2, U32>}, aad, pt)} : Maybe<&2, List<&2, U32>>}, 11n, 12n, hn, {==})
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> n7 <> n8 <> n9 <> n10 <> n11 <> Nil{}: aes128_encrypt(key, h, n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, aad, pt)
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> n7 <> n8 <> n9 <> n10 <> n11 <> nx <> nrest: no_len({GCM.aes128_gcm_encrypt(key, {n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> n7 <> n8 <> n9 <> n10 <> n11 <> nx <> nrest : List<&2, U32>}, aad, pt) == Some{G.aes_seal(key, {n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> n7 <> n8 <> n9 <> n10 <> n11 <> nx <> nrest : List<&2, U32>}, aad, pt)} : Maybe<&2, List<&2, U32>>}, 13n+List.length(&2, U32, nrest), 12n, hn, {==})

law aes128_decrypt_l:
  for +key: List<&2, U32>
  for +h: {List.length(&2, U32, key) == 16n : Nat}
  for +nonce: List<&2, U32>
  for +hn: {List.length(&2, U32, nonce) == 12n : Nat}
  for +aad: List<&2, U32>
  for +ct: List<&2, U32>
  {GCM.aes128_gcm_decrypt(key, nonce, aad, ct) == G.aes_open(key, nonce, aad, ct) : Maybe<&2, List<&2, U32>>}

def aes128_decrypt_l(key, h, nonce, hn, aad, ct):
  match nonce:
    case Nil{}: no_len({GCM.aes128_gcm_decrypt(key, {Nil{} : List<&2, U32>}, aad, ct) == G.aes_open(key, {Nil{} : List<&2, U32>}, aad, ct) : Maybe<&2, List<&2, U32>>}, 0n, 12n, hn, {==})
    case n0 <> Nil{}: no_len({GCM.aes128_gcm_decrypt(key, {[n0] : List<&2, U32>}, aad, ct) == G.aes_open(key, {[n0] : List<&2, U32>}, aad, ct) : Maybe<&2, List<&2, U32>>}, 1n, 12n, hn, {==})
    case n0 <> n1 <> Nil{}: no_len({GCM.aes128_gcm_decrypt(key, {[n0, n1] : List<&2, U32>}, aad, ct) == G.aes_open(key, {[n0, n1] : List<&2, U32>}, aad, ct) : Maybe<&2, List<&2, U32>>}, 2n, 12n, hn, {==})
    case n0 <> n1 <> n2 <> Nil{}: no_len({GCM.aes128_gcm_decrypt(key, {[n0, n1, n2] : List<&2, U32>}, aad, ct) == G.aes_open(key, {[n0, n1, n2] : List<&2, U32>}, aad, ct) : Maybe<&2, List<&2, U32>>}, 3n, 12n, hn, {==})
    case n0 <> n1 <> n2 <> n3 <> Nil{}: no_len({GCM.aes128_gcm_decrypt(key, {[n0, n1, n2, n3] : List<&2, U32>}, aad, ct) == G.aes_open(key, {[n0, n1, n2, n3] : List<&2, U32>}, aad, ct) : Maybe<&2, List<&2, U32>>}, 4n, 12n, hn, {==})
    case n0 <> n1 <> n2 <> n3 <> n4 <> Nil{}: no_len({GCM.aes128_gcm_decrypt(key, {[n0, n1, n2, n3, n4] : List<&2, U32>}, aad, ct) == G.aes_open(key, {[n0, n1, n2, n3, n4] : List<&2, U32>}, aad, ct) : Maybe<&2, List<&2, U32>>}, 5n, 12n, hn, {==})
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> Nil{}: no_len({GCM.aes128_gcm_decrypt(key, {[n0, n1, n2, n3, n4, n5] : List<&2, U32>}, aad, ct) == G.aes_open(key, {[n0, n1, n2, n3, n4, n5] : List<&2, U32>}, aad, ct) : Maybe<&2, List<&2, U32>>}, 6n, 12n, hn, {==})
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> Nil{}: no_len({GCM.aes128_gcm_decrypt(key, {[n0, n1, n2, n3, n4, n5, n6] : List<&2, U32>}, aad, ct) == G.aes_open(key, {[n0, n1, n2, n3, n4, n5, n6] : List<&2, U32>}, aad, ct) : Maybe<&2, List<&2, U32>>}, 7n, 12n, hn, {==})
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> n7 <> Nil{}: no_len({GCM.aes128_gcm_decrypt(key, {[n0, n1, n2, n3, n4, n5, n6, n7] : List<&2, U32>}, aad, ct) == G.aes_open(key, {[n0, n1, n2, n3, n4, n5, n6, n7] : List<&2, U32>}, aad, ct) : Maybe<&2, List<&2, U32>>}, 8n, 12n, hn, {==})
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> n7 <> n8 <> Nil{}: no_len({GCM.aes128_gcm_decrypt(key, {[n0, n1, n2, n3, n4, n5, n6, n7, n8] : List<&2, U32>}, aad, ct) == G.aes_open(key, {[n0, n1, n2, n3, n4, n5, n6, n7, n8] : List<&2, U32>}, aad, ct) : Maybe<&2, List<&2, U32>>}, 9n, 12n, hn, {==})
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> n7 <> n8 <> n9 <> Nil{}: no_len({GCM.aes128_gcm_decrypt(key, {[n0, n1, n2, n3, n4, n5, n6, n7, n8, n9] : List<&2, U32>}, aad, ct) == G.aes_open(key, {[n0, n1, n2, n3, n4, n5, n6, n7, n8, n9] : List<&2, U32>}, aad, ct) : Maybe<&2, List<&2, U32>>}, 10n, 12n, hn, {==})
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> n7 <> n8 <> n9 <> n10 <> Nil{}: no_len({GCM.aes128_gcm_decrypt(key, {[n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10] : List<&2, U32>}, aad, ct) == G.aes_open(key, {[n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10] : List<&2, U32>}, aad, ct) : Maybe<&2, List<&2, U32>>}, 11n, 12n, hn, {==})
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> n7 <> n8 <> n9 <> n10 <> n11 <> Nil{}: aes128_decrypt(key, h, n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, aad, ct)
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> n7 <> n8 <> n9 <> n10 <> n11 <> nx <> nrest: no_len({GCM.aes128_gcm_decrypt(key, {n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> n7 <> n8 <> n9 <> n10 <> n11 <> nx <> nrest : List<&2, U32>}, aad, ct) == G.aes_open(key, {n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> n7 <> n8 <> n9 <> n10 <> n11 <> nx <> nrest : List<&2, U32>}, aad, ct) : Maybe<&2, List<&2, U32>>}, 13n+List.length(&2, U32, nrest), 12n, hn, {==})

law aes128_roundtrip_l:
  for +key: List<&2, U32>
  for +h: {List.length(&2, U32, key) == 16n : Nat}
  for +nonce: List<&2, U32>
  for +hn: {List.length(&2, U32, nonce) == 12n : Nat}
  for +aad: List<&2, U32>
  for +pt: List<&2, U32>
  {open128(key, nonce, aad, GCM.aes128_gcm_encrypt(key, nonce, aad, pt)) == Some{pt} : Maybe<&2, List<&2, U32>>}

def aes128_roundtrip_l(key, h, nonce, hn, aad, pt):
  match nonce:
    case Nil{}: no_len({open128(key, {Nil{} : List<&2, U32>}, aad, GCM.aes128_gcm_encrypt(key, {Nil{} : List<&2, U32>}, aad, pt)) == Some{pt} : Maybe<&2, List<&2, U32>>}, 0n, 12n, hn, {==})
    case n0 <> Nil{}: no_len({open128(key, {[n0] : List<&2, U32>}, aad, GCM.aes128_gcm_encrypt(key, {[n0] : List<&2, U32>}, aad, pt)) == Some{pt} : Maybe<&2, List<&2, U32>>}, 1n, 12n, hn, {==})
    case n0 <> n1 <> Nil{}: no_len({open128(key, {[n0, n1] : List<&2, U32>}, aad, GCM.aes128_gcm_encrypt(key, {[n0, n1] : List<&2, U32>}, aad, pt)) == Some{pt} : Maybe<&2, List<&2, U32>>}, 2n, 12n, hn, {==})
    case n0 <> n1 <> n2 <> Nil{}: no_len({open128(key, {[n0, n1, n2] : List<&2, U32>}, aad, GCM.aes128_gcm_encrypt(key, {[n0, n1, n2] : List<&2, U32>}, aad, pt)) == Some{pt} : Maybe<&2, List<&2, U32>>}, 3n, 12n, hn, {==})
    case n0 <> n1 <> n2 <> n3 <> Nil{}: no_len({open128(key, {[n0, n1, n2, n3] : List<&2, U32>}, aad, GCM.aes128_gcm_encrypt(key, {[n0, n1, n2, n3] : List<&2, U32>}, aad, pt)) == Some{pt} : Maybe<&2, List<&2, U32>>}, 4n, 12n, hn, {==})
    case n0 <> n1 <> n2 <> n3 <> n4 <> Nil{}: no_len({open128(key, {[n0, n1, n2, n3, n4] : List<&2, U32>}, aad, GCM.aes128_gcm_encrypt(key, {[n0, n1, n2, n3, n4] : List<&2, U32>}, aad, pt)) == Some{pt} : Maybe<&2, List<&2, U32>>}, 5n, 12n, hn, {==})
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> Nil{}: no_len({open128(key, {[n0, n1, n2, n3, n4, n5] : List<&2, U32>}, aad, GCM.aes128_gcm_encrypt(key, {[n0, n1, n2, n3, n4, n5] : List<&2, U32>}, aad, pt)) == Some{pt} : Maybe<&2, List<&2, U32>>}, 6n, 12n, hn, {==})
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> Nil{}: no_len({open128(key, {[n0, n1, n2, n3, n4, n5, n6] : List<&2, U32>}, aad, GCM.aes128_gcm_encrypt(key, {[n0, n1, n2, n3, n4, n5, n6] : List<&2, U32>}, aad, pt)) == Some{pt} : Maybe<&2, List<&2, U32>>}, 7n, 12n, hn, {==})
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> n7 <> Nil{}: no_len({open128(key, {[n0, n1, n2, n3, n4, n5, n6, n7] : List<&2, U32>}, aad, GCM.aes128_gcm_encrypt(key, {[n0, n1, n2, n3, n4, n5, n6, n7] : List<&2, U32>}, aad, pt)) == Some{pt} : Maybe<&2, List<&2, U32>>}, 8n, 12n, hn, {==})
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> n7 <> n8 <> Nil{}: no_len({open128(key, {[n0, n1, n2, n3, n4, n5, n6, n7, n8] : List<&2, U32>}, aad, GCM.aes128_gcm_encrypt(key, {[n0, n1, n2, n3, n4, n5, n6, n7, n8] : List<&2, U32>}, aad, pt)) == Some{pt} : Maybe<&2, List<&2, U32>>}, 9n, 12n, hn, {==})
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> n7 <> n8 <> n9 <> Nil{}: no_len({open128(key, {[n0, n1, n2, n3, n4, n5, n6, n7, n8, n9] : List<&2, U32>}, aad, GCM.aes128_gcm_encrypt(key, {[n0, n1, n2, n3, n4, n5, n6, n7, n8, n9] : List<&2, U32>}, aad, pt)) == Some{pt} : Maybe<&2, List<&2, U32>>}, 10n, 12n, hn, {==})
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> n7 <> n8 <> n9 <> n10 <> Nil{}: no_len({open128(key, {[n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10] : List<&2, U32>}, aad, GCM.aes128_gcm_encrypt(key, {[n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10] : List<&2, U32>}, aad, pt)) == Some{pt} : Maybe<&2, List<&2, U32>>}, 11n, 12n, hn, {==})
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> n7 <> n8 <> n9 <> n10 <> n11 <> Nil{}: aes128_roundtrip(key, h, n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, aad, pt)
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> n7 <> n8 <> n9 <> n10 <> n11 <> nx <> nrest: no_len({open128(key, {n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> n7 <> n8 <> n9 <> n10 <> n11 <> nx <> nrest : List<&2, U32>}, aad, GCM.aes128_gcm_encrypt(key, {n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> n7 <> n8 <> n9 <> n10 <> n11 <> nx <> nrest : List<&2, U32>}, aad, pt)) == Some{pt} : Maybe<&2, List<&2, U32>>}, 13n+List.length(&2, U32, nrest), 12n, hn, {==})

law aes128_forgery_t:
  for +key: List<&2, U32>
  for +h: {List.length(&2, U32, key) == 16n : Nat}
  for +n0: U32
  for +n1: U32
  for +n2: U32
  for +n3: U32
  for +n4: U32
  for +n5: U32
  for +n6: U32
  for +n7: U32
  for +n8: U32
  for +n9: U32
  for +n10: U32
  for +n11: U32
  for +aad: List<&2, U32>
  for +c: List<&2, U32>
  for +t: List<&2, U32>
  for +ht: {List.length(&2, U32, t) == 16n : Nat}
  for ne: {t != G.aes_tag(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, c) : List<&2, U32>}
  {GCM.aes128_gcm_decrypt(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, List.append(&2, U32, c, t)) == None{} : Maybe<&2, List<&2, U32>>}

def aes128_forgery_t(key, h, n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, aad, c, t, ht, ne):
  match t:
    case Nil{}: no_len({GCM.aes128_gcm_decrypt(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, List.append(&2, U32, c, {Nil{} : List<&2, U32>})) == None{} : Maybe<&2, List<&2, U32>>}, 0n, 16n, ht, {==})
    case t0 <> Nil{}: no_len({GCM.aes128_gcm_decrypt(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, List.append(&2, U32, c, {[t0] : List<&2, U32>})) == None{} : Maybe<&2, List<&2, U32>>}, 1n, 16n, ht, {==})
    case t0 <> t1 <> Nil{}: no_len({GCM.aes128_gcm_decrypt(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, List.append(&2, U32, c, {[t0, t1] : List<&2, U32>})) == None{} : Maybe<&2, List<&2, U32>>}, 2n, 16n, ht, {==})
    case t0 <> t1 <> t2 <> Nil{}: no_len({GCM.aes128_gcm_decrypt(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, List.append(&2, U32, c, {[t0, t1, t2] : List<&2, U32>})) == None{} : Maybe<&2, List<&2, U32>>}, 3n, 16n, ht, {==})
    case t0 <> t1 <> t2 <> t3 <> Nil{}: no_len({GCM.aes128_gcm_decrypt(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, List.append(&2, U32, c, {[t0, t1, t2, t3] : List<&2, U32>})) == None{} : Maybe<&2, List<&2, U32>>}, 4n, 16n, ht, {==})
    case t0 <> t1 <> t2 <> t3 <> t4 <> Nil{}: no_len({GCM.aes128_gcm_decrypt(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, List.append(&2, U32, c, {[t0, t1, t2, t3, t4] : List<&2, U32>})) == None{} : Maybe<&2, List<&2, U32>>}, 5n, 16n, ht, {==})
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> Nil{}: no_len({GCM.aes128_gcm_decrypt(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, List.append(&2, U32, c, {[t0, t1, t2, t3, t4, t5] : List<&2, U32>})) == None{} : Maybe<&2, List<&2, U32>>}, 6n, 16n, ht, {==})
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> Nil{}: no_len({GCM.aes128_gcm_decrypt(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, List.append(&2, U32, c, {[t0, t1, t2, t3, t4, t5, t6] : List<&2, U32>})) == None{} : Maybe<&2, List<&2, U32>>}, 7n, 16n, ht, {==})
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> t7 <> Nil{}: no_len({GCM.aes128_gcm_decrypt(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, List.append(&2, U32, c, {[t0, t1, t2, t3, t4, t5, t6, t7] : List<&2, U32>})) == None{} : Maybe<&2, List<&2, U32>>}, 8n, 16n, ht, {==})
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> t7 <> t8 <> Nil{}: no_len({GCM.aes128_gcm_decrypt(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, List.append(&2, U32, c, {[t0, t1, t2, t3, t4, t5, t6, t7, t8] : List<&2, U32>})) == None{} : Maybe<&2, List<&2, U32>>}, 9n, 16n, ht, {==})
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> t7 <> t8 <> t9 <> Nil{}: no_len({GCM.aes128_gcm_decrypt(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, List.append(&2, U32, c, {[t0, t1, t2, t3, t4, t5, t6, t7, t8, t9] : List<&2, U32>})) == None{} : Maybe<&2, List<&2, U32>>}, 10n, 16n, ht, {==})
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> t7 <> t8 <> t9 <> t10 <> Nil{}: no_len({GCM.aes128_gcm_decrypt(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, List.append(&2, U32, c, {[t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10] : List<&2, U32>})) == None{} : Maybe<&2, List<&2, U32>>}, 11n, 16n, ht, {==})
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> t7 <> t8 <> t9 <> t10 <> t11 <> Nil{}: no_len({GCM.aes128_gcm_decrypt(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, List.append(&2, U32, c, {[t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11] : List<&2, U32>})) == None{} : Maybe<&2, List<&2, U32>>}, 12n, 16n, ht, {==})
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> t7 <> t8 <> t9 <> t10 <> t11 <> t12 <> Nil{}: no_len({GCM.aes128_gcm_decrypt(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, List.append(&2, U32, c, {[t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12] : List<&2, U32>})) == None{} : Maybe<&2, List<&2, U32>>}, 13n, 16n, ht, {==})
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> t7 <> t8 <> t9 <> t10 <> t11 <> t12 <> t13 <> Nil{}: no_len({GCM.aes128_gcm_decrypt(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, List.append(&2, U32, c, {[t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13] : List<&2, U32>})) == None{} : Maybe<&2, List<&2, U32>>}, 14n, 16n, ht, {==})
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> t7 <> t8 <> t9 <> t10 <> t11 <> t12 <> t13 <> t14 <> Nil{}: no_len({GCM.aes128_gcm_decrypt(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, List.append(&2, U32, c, {[t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14] : List<&2, U32>})) == None{} : Maybe<&2, List<&2, U32>>}, 15n, 16n, ht, {==})
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> t7 <> t8 <> t9 <> t10 <> t11 <> t12 <> t13 <> t14 <> t15 <> Nil{}: aes128_forgery(key, h, n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, aad, c, t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, ne)
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> t7 <> t8 <> t9 <> t10 <> t11 <> t12 <> t13 <> t14 <> t15 <> tx <> trest: no_len({GCM.aes128_gcm_decrypt(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, List.append(&2, U32, c, {t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> t7 <> t8 <> t9 <> t10 <> t11 <> t12 <> t13 <> t14 <> t15 <> tx <> trest : List<&2, U32>})) == None{} : Maybe<&2, List<&2, U32>>}, 17n+List.length(&2, U32, trest), 16n, ht, {==})

law aes128_forgery_l:
  for +key: List<&2, U32>
  for +h: {List.length(&2, U32, key) == 16n : Nat}
  for +nonce: List<&2, U32>
  for +hn: {List.length(&2, U32, nonce) == 12n : Nat}
  for +aad: List<&2, U32>
  for +c: List<&2, U32>
  for +t: List<&2, U32>
  for +ht: {List.length(&2, U32, t) == 16n : Nat}
  for ne: {t != G.aes_tag(key, nonce, aad, c) : List<&2, U32>}
  {GCM.aes128_gcm_decrypt(key, nonce, aad, List.append(&2, U32, c, t)) == None{} : Maybe<&2, List<&2, U32>>}

def aes128_forgery_l(key, h, nonce, hn, aad, c, t, ht, ne):
  match nonce:
    case Nil{}: no_len({GCM.aes128_gcm_decrypt(key, {Nil{} : List<&2, U32>}, aad, List.append(&2, U32, c, t)) == None{} : Maybe<&2, List<&2, U32>>}, 0n, 12n, hn, {==})
    case n0 <> Nil{}: no_len({GCM.aes128_gcm_decrypt(key, {[n0] : List<&2, U32>}, aad, List.append(&2, U32, c, t)) == None{} : Maybe<&2, List<&2, U32>>}, 1n, 12n, hn, {==})
    case n0 <> n1 <> Nil{}: no_len({GCM.aes128_gcm_decrypt(key, {[n0, n1] : List<&2, U32>}, aad, List.append(&2, U32, c, t)) == None{} : Maybe<&2, List<&2, U32>>}, 2n, 12n, hn, {==})
    case n0 <> n1 <> n2 <> Nil{}: no_len({GCM.aes128_gcm_decrypt(key, {[n0, n1, n2] : List<&2, U32>}, aad, List.append(&2, U32, c, t)) == None{} : Maybe<&2, List<&2, U32>>}, 3n, 12n, hn, {==})
    case n0 <> n1 <> n2 <> n3 <> Nil{}: no_len({GCM.aes128_gcm_decrypt(key, {[n0, n1, n2, n3] : List<&2, U32>}, aad, List.append(&2, U32, c, t)) == None{} : Maybe<&2, List<&2, U32>>}, 4n, 12n, hn, {==})
    case n0 <> n1 <> n2 <> n3 <> n4 <> Nil{}: no_len({GCM.aes128_gcm_decrypt(key, {[n0, n1, n2, n3, n4] : List<&2, U32>}, aad, List.append(&2, U32, c, t)) == None{} : Maybe<&2, List<&2, U32>>}, 5n, 12n, hn, {==})
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> Nil{}: no_len({GCM.aes128_gcm_decrypt(key, {[n0, n1, n2, n3, n4, n5] : List<&2, U32>}, aad, List.append(&2, U32, c, t)) == None{} : Maybe<&2, List<&2, U32>>}, 6n, 12n, hn, {==})
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> Nil{}: no_len({GCM.aes128_gcm_decrypt(key, {[n0, n1, n2, n3, n4, n5, n6] : List<&2, U32>}, aad, List.append(&2, U32, c, t)) == None{} : Maybe<&2, List<&2, U32>>}, 7n, 12n, hn, {==})
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> n7 <> Nil{}: no_len({GCM.aes128_gcm_decrypt(key, {[n0, n1, n2, n3, n4, n5, n6, n7] : List<&2, U32>}, aad, List.append(&2, U32, c, t)) == None{} : Maybe<&2, List<&2, U32>>}, 8n, 12n, hn, {==})
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> n7 <> n8 <> Nil{}: no_len({GCM.aes128_gcm_decrypt(key, {[n0, n1, n2, n3, n4, n5, n6, n7, n8] : List<&2, U32>}, aad, List.append(&2, U32, c, t)) == None{} : Maybe<&2, List<&2, U32>>}, 9n, 12n, hn, {==})
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> n7 <> n8 <> n9 <> Nil{}: no_len({GCM.aes128_gcm_decrypt(key, {[n0, n1, n2, n3, n4, n5, n6, n7, n8, n9] : List<&2, U32>}, aad, List.append(&2, U32, c, t)) == None{} : Maybe<&2, List<&2, U32>>}, 10n, 12n, hn, {==})
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> n7 <> n8 <> n9 <> n10 <> Nil{}: no_len({GCM.aes128_gcm_decrypt(key, {[n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10] : List<&2, U32>}, aad, List.append(&2, U32, c, t)) == None{} : Maybe<&2, List<&2, U32>>}, 11n, 12n, hn, {==})
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> n7 <> n8 <> n9 <> n10 <> n11 <> Nil{}: aes128_forgery_t(key, h, n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, aad, c, t, ht, ne)
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> n7 <> n8 <> n9 <> n10 <> n11 <> nx <> nrest: no_len({GCM.aes128_gcm_decrypt(key, {n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> n7 <> n8 <> n9 <> n10 <> n11 <> nx <> nrest : List<&2, U32>}, aad, List.append(&2, U32, c, t)) == None{} : Maybe<&2, List<&2, U32>>}, 13n+List.length(&2, U32, nrest), 12n, hn, {==})

law aes256_encrypt_l:
  for +key: List<&2, U32>
  for +h: {List.length(&2, U32, key) == 32n : Nat}
  for +nonce: List<&2, U32>
  for +hn: {List.length(&2, U32, nonce) == 12n : Nat}
  for +aad: List<&2, U32>
  for +pt: List<&2, U32>
  {GCM.aes256_gcm_encrypt(key, nonce, aad, pt) == Some{G.aes_seal(key, nonce, aad, pt)} : Maybe<&2, List<&2, U32>>}

def aes256_encrypt_l(key, h, nonce, hn, aad, pt):
  match nonce:
    case Nil{}: no_len({GCM.aes256_gcm_encrypt(key, {Nil{} : List<&2, U32>}, aad, pt) == Some{G.aes_seal(key, {Nil{} : List<&2, U32>}, aad, pt)} : Maybe<&2, List<&2, U32>>}, 0n, 12n, hn, {==})
    case n0 <> Nil{}: no_len({GCM.aes256_gcm_encrypt(key, {[n0] : List<&2, U32>}, aad, pt) == Some{G.aes_seal(key, {[n0] : List<&2, U32>}, aad, pt)} : Maybe<&2, List<&2, U32>>}, 1n, 12n, hn, {==})
    case n0 <> n1 <> Nil{}: no_len({GCM.aes256_gcm_encrypt(key, {[n0, n1] : List<&2, U32>}, aad, pt) == Some{G.aes_seal(key, {[n0, n1] : List<&2, U32>}, aad, pt)} : Maybe<&2, List<&2, U32>>}, 2n, 12n, hn, {==})
    case n0 <> n1 <> n2 <> Nil{}: no_len({GCM.aes256_gcm_encrypt(key, {[n0, n1, n2] : List<&2, U32>}, aad, pt) == Some{G.aes_seal(key, {[n0, n1, n2] : List<&2, U32>}, aad, pt)} : Maybe<&2, List<&2, U32>>}, 3n, 12n, hn, {==})
    case n0 <> n1 <> n2 <> n3 <> Nil{}: no_len({GCM.aes256_gcm_encrypt(key, {[n0, n1, n2, n3] : List<&2, U32>}, aad, pt) == Some{G.aes_seal(key, {[n0, n1, n2, n3] : List<&2, U32>}, aad, pt)} : Maybe<&2, List<&2, U32>>}, 4n, 12n, hn, {==})
    case n0 <> n1 <> n2 <> n3 <> n4 <> Nil{}: no_len({GCM.aes256_gcm_encrypt(key, {[n0, n1, n2, n3, n4] : List<&2, U32>}, aad, pt) == Some{G.aes_seal(key, {[n0, n1, n2, n3, n4] : List<&2, U32>}, aad, pt)} : Maybe<&2, List<&2, U32>>}, 5n, 12n, hn, {==})
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> Nil{}: no_len({GCM.aes256_gcm_encrypt(key, {[n0, n1, n2, n3, n4, n5] : List<&2, U32>}, aad, pt) == Some{G.aes_seal(key, {[n0, n1, n2, n3, n4, n5] : List<&2, U32>}, aad, pt)} : Maybe<&2, List<&2, U32>>}, 6n, 12n, hn, {==})
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> Nil{}: no_len({GCM.aes256_gcm_encrypt(key, {[n0, n1, n2, n3, n4, n5, n6] : List<&2, U32>}, aad, pt) == Some{G.aes_seal(key, {[n0, n1, n2, n3, n4, n5, n6] : List<&2, U32>}, aad, pt)} : Maybe<&2, List<&2, U32>>}, 7n, 12n, hn, {==})
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> n7 <> Nil{}: no_len({GCM.aes256_gcm_encrypt(key, {[n0, n1, n2, n3, n4, n5, n6, n7] : List<&2, U32>}, aad, pt) == Some{G.aes_seal(key, {[n0, n1, n2, n3, n4, n5, n6, n7] : List<&2, U32>}, aad, pt)} : Maybe<&2, List<&2, U32>>}, 8n, 12n, hn, {==})
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> n7 <> n8 <> Nil{}: no_len({GCM.aes256_gcm_encrypt(key, {[n0, n1, n2, n3, n4, n5, n6, n7, n8] : List<&2, U32>}, aad, pt) == Some{G.aes_seal(key, {[n0, n1, n2, n3, n4, n5, n6, n7, n8] : List<&2, U32>}, aad, pt)} : Maybe<&2, List<&2, U32>>}, 9n, 12n, hn, {==})
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> n7 <> n8 <> n9 <> Nil{}: no_len({GCM.aes256_gcm_encrypt(key, {[n0, n1, n2, n3, n4, n5, n6, n7, n8, n9] : List<&2, U32>}, aad, pt) == Some{G.aes_seal(key, {[n0, n1, n2, n3, n4, n5, n6, n7, n8, n9] : List<&2, U32>}, aad, pt)} : Maybe<&2, List<&2, U32>>}, 10n, 12n, hn, {==})
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> n7 <> n8 <> n9 <> n10 <> Nil{}: no_len({GCM.aes256_gcm_encrypt(key, {[n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10] : List<&2, U32>}, aad, pt) == Some{G.aes_seal(key, {[n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10] : List<&2, U32>}, aad, pt)} : Maybe<&2, List<&2, U32>>}, 11n, 12n, hn, {==})
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> n7 <> n8 <> n9 <> n10 <> n11 <> Nil{}: aes256_encrypt(key, h, n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, aad, pt)
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> n7 <> n8 <> n9 <> n10 <> n11 <> nx <> nrest: no_len({GCM.aes256_gcm_encrypt(key, {n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> n7 <> n8 <> n9 <> n10 <> n11 <> nx <> nrest : List<&2, U32>}, aad, pt) == Some{G.aes_seal(key, {n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> n7 <> n8 <> n9 <> n10 <> n11 <> nx <> nrest : List<&2, U32>}, aad, pt)} : Maybe<&2, List<&2, U32>>}, 13n+List.length(&2, U32, nrest), 12n, hn, {==})

law aes256_decrypt_l:
  for +key: List<&2, U32>
  for +h: {List.length(&2, U32, key) == 32n : Nat}
  for +nonce: List<&2, U32>
  for +hn: {List.length(&2, U32, nonce) == 12n : Nat}
  for +aad: List<&2, U32>
  for +ct: List<&2, U32>
  {GCM.aes256_gcm_decrypt(key, nonce, aad, ct) == G.aes_open(key, nonce, aad, ct) : Maybe<&2, List<&2, U32>>}

def aes256_decrypt_l(key, h, nonce, hn, aad, ct):
  match nonce:
    case Nil{}: no_len({GCM.aes256_gcm_decrypt(key, {Nil{} : List<&2, U32>}, aad, ct) == G.aes_open(key, {Nil{} : List<&2, U32>}, aad, ct) : Maybe<&2, List<&2, U32>>}, 0n, 12n, hn, {==})
    case n0 <> Nil{}: no_len({GCM.aes256_gcm_decrypt(key, {[n0] : List<&2, U32>}, aad, ct) == G.aes_open(key, {[n0] : List<&2, U32>}, aad, ct) : Maybe<&2, List<&2, U32>>}, 1n, 12n, hn, {==})
    case n0 <> n1 <> Nil{}: no_len({GCM.aes256_gcm_decrypt(key, {[n0, n1] : List<&2, U32>}, aad, ct) == G.aes_open(key, {[n0, n1] : List<&2, U32>}, aad, ct) : Maybe<&2, List<&2, U32>>}, 2n, 12n, hn, {==})
    case n0 <> n1 <> n2 <> Nil{}: no_len({GCM.aes256_gcm_decrypt(key, {[n0, n1, n2] : List<&2, U32>}, aad, ct) == G.aes_open(key, {[n0, n1, n2] : List<&2, U32>}, aad, ct) : Maybe<&2, List<&2, U32>>}, 3n, 12n, hn, {==})
    case n0 <> n1 <> n2 <> n3 <> Nil{}: no_len({GCM.aes256_gcm_decrypt(key, {[n0, n1, n2, n3] : List<&2, U32>}, aad, ct) == G.aes_open(key, {[n0, n1, n2, n3] : List<&2, U32>}, aad, ct) : Maybe<&2, List<&2, U32>>}, 4n, 12n, hn, {==})
    case n0 <> n1 <> n2 <> n3 <> n4 <> Nil{}: no_len({GCM.aes256_gcm_decrypt(key, {[n0, n1, n2, n3, n4] : List<&2, U32>}, aad, ct) == G.aes_open(key, {[n0, n1, n2, n3, n4] : List<&2, U32>}, aad, ct) : Maybe<&2, List<&2, U32>>}, 5n, 12n, hn, {==})
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> Nil{}: no_len({GCM.aes256_gcm_decrypt(key, {[n0, n1, n2, n3, n4, n5] : List<&2, U32>}, aad, ct) == G.aes_open(key, {[n0, n1, n2, n3, n4, n5] : List<&2, U32>}, aad, ct) : Maybe<&2, List<&2, U32>>}, 6n, 12n, hn, {==})
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> Nil{}: no_len({GCM.aes256_gcm_decrypt(key, {[n0, n1, n2, n3, n4, n5, n6] : List<&2, U32>}, aad, ct) == G.aes_open(key, {[n0, n1, n2, n3, n4, n5, n6] : List<&2, U32>}, aad, ct) : Maybe<&2, List<&2, U32>>}, 7n, 12n, hn, {==})
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> n7 <> Nil{}: no_len({GCM.aes256_gcm_decrypt(key, {[n0, n1, n2, n3, n4, n5, n6, n7] : List<&2, U32>}, aad, ct) == G.aes_open(key, {[n0, n1, n2, n3, n4, n5, n6, n7] : List<&2, U32>}, aad, ct) : Maybe<&2, List<&2, U32>>}, 8n, 12n, hn, {==})
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> n7 <> n8 <> Nil{}: no_len({GCM.aes256_gcm_decrypt(key, {[n0, n1, n2, n3, n4, n5, n6, n7, n8] : List<&2, U32>}, aad, ct) == G.aes_open(key, {[n0, n1, n2, n3, n4, n5, n6, n7, n8] : List<&2, U32>}, aad, ct) : Maybe<&2, List<&2, U32>>}, 9n, 12n, hn, {==})
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> n7 <> n8 <> n9 <> Nil{}: no_len({GCM.aes256_gcm_decrypt(key, {[n0, n1, n2, n3, n4, n5, n6, n7, n8, n9] : List<&2, U32>}, aad, ct) == G.aes_open(key, {[n0, n1, n2, n3, n4, n5, n6, n7, n8, n9] : List<&2, U32>}, aad, ct) : Maybe<&2, List<&2, U32>>}, 10n, 12n, hn, {==})
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> n7 <> n8 <> n9 <> n10 <> Nil{}: no_len({GCM.aes256_gcm_decrypt(key, {[n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10] : List<&2, U32>}, aad, ct) == G.aes_open(key, {[n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10] : List<&2, U32>}, aad, ct) : Maybe<&2, List<&2, U32>>}, 11n, 12n, hn, {==})
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> n7 <> n8 <> n9 <> n10 <> n11 <> Nil{}: aes256_decrypt(key, h, n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, aad, ct)
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> n7 <> n8 <> n9 <> n10 <> n11 <> nx <> nrest: no_len({GCM.aes256_gcm_decrypt(key, {n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> n7 <> n8 <> n9 <> n10 <> n11 <> nx <> nrest : List<&2, U32>}, aad, ct) == G.aes_open(key, {n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> n7 <> n8 <> n9 <> n10 <> n11 <> nx <> nrest : List<&2, U32>}, aad, ct) : Maybe<&2, List<&2, U32>>}, 13n+List.length(&2, U32, nrest), 12n, hn, {==})

law aes256_roundtrip_l:
  for +key: List<&2, U32>
  for +h: {List.length(&2, U32, key) == 32n : Nat}
  for +nonce: List<&2, U32>
  for +hn: {List.length(&2, U32, nonce) == 12n : Nat}
  for +aad: List<&2, U32>
  for +pt: List<&2, U32>
  {open256(key, nonce, aad, GCM.aes256_gcm_encrypt(key, nonce, aad, pt)) == Some{pt} : Maybe<&2, List<&2, U32>>}

def aes256_roundtrip_l(key, h, nonce, hn, aad, pt):
  match nonce:
    case Nil{}: no_len({open256(key, {Nil{} : List<&2, U32>}, aad, GCM.aes256_gcm_encrypt(key, {Nil{} : List<&2, U32>}, aad, pt)) == Some{pt} : Maybe<&2, List<&2, U32>>}, 0n, 12n, hn, {==})
    case n0 <> Nil{}: no_len({open256(key, {[n0] : List<&2, U32>}, aad, GCM.aes256_gcm_encrypt(key, {[n0] : List<&2, U32>}, aad, pt)) == Some{pt} : Maybe<&2, List<&2, U32>>}, 1n, 12n, hn, {==})
    case n0 <> n1 <> Nil{}: no_len({open256(key, {[n0, n1] : List<&2, U32>}, aad, GCM.aes256_gcm_encrypt(key, {[n0, n1] : List<&2, U32>}, aad, pt)) == Some{pt} : Maybe<&2, List<&2, U32>>}, 2n, 12n, hn, {==})
    case n0 <> n1 <> n2 <> Nil{}: no_len({open256(key, {[n0, n1, n2] : List<&2, U32>}, aad, GCM.aes256_gcm_encrypt(key, {[n0, n1, n2] : List<&2, U32>}, aad, pt)) == Some{pt} : Maybe<&2, List<&2, U32>>}, 3n, 12n, hn, {==})
    case n0 <> n1 <> n2 <> n3 <> Nil{}: no_len({open256(key, {[n0, n1, n2, n3] : List<&2, U32>}, aad, GCM.aes256_gcm_encrypt(key, {[n0, n1, n2, n3] : List<&2, U32>}, aad, pt)) == Some{pt} : Maybe<&2, List<&2, U32>>}, 4n, 12n, hn, {==})
    case n0 <> n1 <> n2 <> n3 <> n4 <> Nil{}: no_len({open256(key, {[n0, n1, n2, n3, n4] : List<&2, U32>}, aad, GCM.aes256_gcm_encrypt(key, {[n0, n1, n2, n3, n4] : List<&2, U32>}, aad, pt)) == Some{pt} : Maybe<&2, List<&2, U32>>}, 5n, 12n, hn, {==})
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> Nil{}: no_len({open256(key, {[n0, n1, n2, n3, n4, n5] : List<&2, U32>}, aad, GCM.aes256_gcm_encrypt(key, {[n0, n1, n2, n3, n4, n5] : List<&2, U32>}, aad, pt)) == Some{pt} : Maybe<&2, List<&2, U32>>}, 6n, 12n, hn, {==})
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> Nil{}: no_len({open256(key, {[n0, n1, n2, n3, n4, n5, n6] : List<&2, U32>}, aad, GCM.aes256_gcm_encrypt(key, {[n0, n1, n2, n3, n4, n5, n6] : List<&2, U32>}, aad, pt)) == Some{pt} : Maybe<&2, List<&2, U32>>}, 7n, 12n, hn, {==})
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> n7 <> Nil{}: no_len({open256(key, {[n0, n1, n2, n3, n4, n5, n6, n7] : List<&2, U32>}, aad, GCM.aes256_gcm_encrypt(key, {[n0, n1, n2, n3, n4, n5, n6, n7] : List<&2, U32>}, aad, pt)) == Some{pt} : Maybe<&2, List<&2, U32>>}, 8n, 12n, hn, {==})
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> n7 <> n8 <> Nil{}: no_len({open256(key, {[n0, n1, n2, n3, n4, n5, n6, n7, n8] : List<&2, U32>}, aad, GCM.aes256_gcm_encrypt(key, {[n0, n1, n2, n3, n4, n5, n6, n7, n8] : List<&2, U32>}, aad, pt)) == Some{pt} : Maybe<&2, List<&2, U32>>}, 9n, 12n, hn, {==})
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> n7 <> n8 <> n9 <> Nil{}: no_len({open256(key, {[n0, n1, n2, n3, n4, n5, n6, n7, n8, n9] : List<&2, U32>}, aad, GCM.aes256_gcm_encrypt(key, {[n0, n1, n2, n3, n4, n5, n6, n7, n8, n9] : List<&2, U32>}, aad, pt)) == Some{pt} : Maybe<&2, List<&2, U32>>}, 10n, 12n, hn, {==})
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> n7 <> n8 <> n9 <> n10 <> Nil{}: no_len({open256(key, {[n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10] : List<&2, U32>}, aad, GCM.aes256_gcm_encrypt(key, {[n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10] : List<&2, U32>}, aad, pt)) == Some{pt} : Maybe<&2, List<&2, U32>>}, 11n, 12n, hn, {==})
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> n7 <> n8 <> n9 <> n10 <> n11 <> Nil{}: aes256_roundtrip(key, h, n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, aad, pt)
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> n7 <> n8 <> n9 <> n10 <> n11 <> nx <> nrest: no_len({open256(key, {n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> n7 <> n8 <> n9 <> n10 <> n11 <> nx <> nrest : List<&2, U32>}, aad, GCM.aes256_gcm_encrypt(key, {n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> n7 <> n8 <> n9 <> n10 <> n11 <> nx <> nrest : List<&2, U32>}, aad, pt)) == Some{pt} : Maybe<&2, List<&2, U32>>}, 13n+List.length(&2, U32, nrest), 12n, hn, {==})

law aes256_forgery_t:
  for +key: List<&2, U32>
  for +h: {List.length(&2, U32, key) == 32n : Nat}
  for +n0: U32
  for +n1: U32
  for +n2: U32
  for +n3: U32
  for +n4: U32
  for +n5: U32
  for +n6: U32
  for +n7: U32
  for +n8: U32
  for +n9: U32
  for +n10: U32
  for +n11: U32
  for +aad: List<&2, U32>
  for +c: List<&2, U32>
  for +t: List<&2, U32>
  for +ht: {List.length(&2, U32, t) == 16n : Nat}
  for ne: {t != G.aes_tag(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, c) : List<&2, U32>}
  {GCM.aes256_gcm_decrypt(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, List.append(&2, U32, c, t)) == None{} : Maybe<&2, List<&2, U32>>}

def aes256_forgery_t(key, h, n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, aad, c, t, ht, ne):
  match t:
    case Nil{}: no_len({GCM.aes256_gcm_decrypt(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, List.append(&2, U32, c, {Nil{} : List<&2, U32>})) == None{} : Maybe<&2, List<&2, U32>>}, 0n, 16n, ht, {==})
    case t0 <> Nil{}: no_len({GCM.aes256_gcm_decrypt(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, List.append(&2, U32, c, {[t0] : List<&2, U32>})) == None{} : Maybe<&2, List<&2, U32>>}, 1n, 16n, ht, {==})
    case t0 <> t1 <> Nil{}: no_len({GCM.aes256_gcm_decrypt(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, List.append(&2, U32, c, {[t0, t1] : List<&2, U32>})) == None{} : Maybe<&2, List<&2, U32>>}, 2n, 16n, ht, {==})
    case t0 <> t1 <> t2 <> Nil{}: no_len({GCM.aes256_gcm_decrypt(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, List.append(&2, U32, c, {[t0, t1, t2] : List<&2, U32>})) == None{} : Maybe<&2, List<&2, U32>>}, 3n, 16n, ht, {==})
    case t0 <> t1 <> t2 <> t3 <> Nil{}: no_len({GCM.aes256_gcm_decrypt(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, List.append(&2, U32, c, {[t0, t1, t2, t3] : List<&2, U32>})) == None{} : Maybe<&2, List<&2, U32>>}, 4n, 16n, ht, {==})
    case t0 <> t1 <> t2 <> t3 <> t4 <> Nil{}: no_len({GCM.aes256_gcm_decrypt(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, List.append(&2, U32, c, {[t0, t1, t2, t3, t4] : List<&2, U32>})) == None{} : Maybe<&2, List<&2, U32>>}, 5n, 16n, ht, {==})
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> Nil{}: no_len({GCM.aes256_gcm_decrypt(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, List.append(&2, U32, c, {[t0, t1, t2, t3, t4, t5] : List<&2, U32>})) == None{} : Maybe<&2, List<&2, U32>>}, 6n, 16n, ht, {==})
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> Nil{}: no_len({GCM.aes256_gcm_decrypt(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, List.append(&2, U32, c, {[t0, t1, t2, t3, t4, t5, t6] : List<&2, U32>})) == None{} : Maybe<&2, List<&2, U32>>}, 7n, 16n, ht, {==})
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> t7 <> Nil{}: no_len({GCM.aes256_gcm_decrypt(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, List.append(&2, U32, c, {[t0, t1, t2, t3, t4, t5, t6, t7] : List<&2, U32>})) == None{} : Maybe<&2, List<&2, U32>>}, 8n, 16n, ht, {==})
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> t7 <> t8 <> Nil{}: no_len({GCM.aes256_gcm_decrypt(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, List.append(&2, U32, c, {[t0, t1, t2, t3, t4, t5, t6, t7, t8] : List<&2, U32>})) == None{} : Maybe<&2, List<&2, U32>>}, 9n, 16n, ht, {==})
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> t7 <> t8 <> t9 <> Nil{}: no_len({GCM.aes256_gcm_decrypt(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, List.append(&2, U32, c, {[t0, t1, t2, t3, t4, t5, t6, t7, t8, t9] : List<&2, U32>})) == None{} : Maybe<&2, List<&2, U32>>}, 10n, 16n, ht, {==})
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> t7 <> t8 <> t9 <> t10 <> Nil{}: no_len({GCM.aes256_gcm_decrypt(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, List.append(&2, U32, c, {[t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10] : List<&2, U32>})) == None{} : Maybe<&2, List<&2, U32>>}, 11n, 16n, ht, {==})
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> t7 <> t8 <> t9 <> t10 <> t11 <> Nil{}: no_len({GCM.aes256_gcm_decrypt(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, List.append(&2, U32, c, {[t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11] : List<&2, U32>})) == None{} : Maybe<&2, List<&2, U32>>}, 12n, 16n, ht, {==})
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> t7 <> t8 <> t9 <> t10 <> t11 <> t12 <> Nil{}: no_len({GCM.aes256_gcm_decrypt(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, List.append(&2, U32, c, {[t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12] : List<&2, U32>})) == None{} : Maybe<&2, List<&2, U32>>}, 13n, 16n, ht, {==})
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> t7 <> t8 <> t9 <> t10 <> t11 <> t12 <> t13 <> Nil{}: no_len({GCM.aes256_gcm_decrypt(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, List.append(&2, U32, c, {[t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13] : List<&2, U32>})) == None{} : Maybe<&2, List<&2, U32>>}, 14n, 16n, ht, {==})
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> t7 <> t8 <> t9 <> t10 <> t11 <> t12 <> t13 <> t14 <> Nil{}: no_len({GCM.aes256_gcm_decrypt(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, List.append(&2, U32, c, {[t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14] : List<&2, U32>})) == None{} : Maybe<&2, List<&2, U32>>}, 15n, 16n, ht, {==})
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> t7 <> t8 <> t9 <> t10 <> t11 <> t12 <> t13 <> t14 <> t15 <> Nil{}: aes256_forgery(key, h, n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, aad, c, t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, ne)
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> t7 <> t8 <> t9 <> t10 <> t11 <> t12 <> t13 <> t14 <> t15 <> tx <> trest: no_len({GCM.aes256_gcm_decrypt(key, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, List.append(&2, U32, c, {t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> t7 <> t8 <> t9 <> t10 <> t11 <> t12 <> t13 <> t14 <> t15 <> tx <> trest : List<&2, U32>})) == None{} : Maybe<&2, List<&2, U32>>}, 17n+List.length(&2, U32, trest), 16n, ht, {==})

law aes256_forgery_l:
  for +key: List<&2, U32>
  for +h: {List.length(&2, U32, key) == 32n : Nat}
  for +nonce: List<&2, U32>
  for +hn: {List.length(&2, U32, nonce) == 12n : Nat}
  for +aad: List<&2, U32>
  for +c: List<&2, U32>
  for +t: List<&2, U32>
  for +ht: {List.length(&2, U32, t) == 16n : Nat}
  for ne: {t != G.aes_tag(key, nonce, aad, c) : List<&2, U32>}
  {GCM.aes256_gcm_decrypt(key, nonce, aad, List.append(&2, U32, c, t)) == None{} : Maybe<&2, List<&2, U32>>}

def aes256_forgery_l(key, h, nonce, hn, aad, c, t, ht, ne):
  match nonce:
    case Nil{}: no_len({GCM.aes256_gcm_decrypt(key, {Nil{} : List<&2, U32>}, aad, List.append(&2, U32, c, t)) == None{} : Maybe<&2, List<&2, U32>>}, 0n, 12n, hn, {==})
    case n0 <> Nil{}: no_len({GCM.aes256_gcm_decrypt(key, {[n0] : List<&2, U32>}, aad, List.append(&2, U32, c, t)) == None{} : Maybe<&2, List<&2, U32>>}, 1n, 12n, hn, {==})
    case n0 <> n1 <> Nil{}: no_len({GCM.aes256_gcm_decrypt(key, {[n0, n1] : List<&2, U32>}, aad, List.append(&2, U32, c, t)) == None{} : Maybe<&2, List<&2, U32>>}, 2n, 12n, hn, {==})
    case n0 <> n1 <> n2 <> Nil{}: no_len({GCM.aes256_gcm_decrypt(key, {[n0, n1, n2] : List<&2, U32>}, aad, List.append(&2, U32, c, t)) == None{} : Maybe<&2, List<&2, U32>>}, 3n, 12n, hn, {==})
    case n0 <> n1 <> n2 <> n3 <> Nil{}: no_len({GCM.aes256_gcm_decrypt(key, {[n0, n1, n2, n3] : List<&2, U32>}, aad, List.append(&2, U32, c, t)) == None{} : Maybe<&2, List<&2, U32>>}, 4n, 12n, hn, {==})
    case n0 <> n1 <> n2 <> n3 <> n4 <> Nil{}: no_len({GCM.aes256_gcm_decrypt(key, {[n0, n1, n2, n3, n4] : List<&2, U32>}, aad, List.append(&2, U32, c, t)) == None{} : Maybe<&2, List<&2, U32>>}, 5n, 12n, hn, {==})
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> Nil{}: no_len({GCM.aes256_gcm_decrypt(key, {[n0, n1, n2, n3, n4, n5] : List<&2, U32>}, aad, List.append(&2, U32, c, t)) == None{} : Maybe<&2, List<&2, U32>>}, 6n, 12n, hn, {==})
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> Nil{}: no_len({GCM.aes256_gcm_decrypt(key, {[n0, n1, n2, n3, n4, n5, n6] : List<&2, U32>}, aad, List.append(&2, U32, c, t)) == None{} : Maybe<&2, List<&2, U32>>}, 7n, 12n, hn, {==})
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> n7 <> Nil{}: no_len({GCM.aes256_gcm_decrypt(key, {[n0, n1, n2, n3, n4, n5, n6, n7] : List<&2, U32>}, aad, List.append(&2, U32, c, t)) == None{} : Maybe<&2, List<&2, U32>>}, 8n, 12n, hn, {==})
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> n7 <> n8 <> Nil{}: no_len({GCM.aes256_gcm_decrypt(key, {[n0, n1, n2, n3, n4, n5, n6, n7, n8] : List<&2, U32>}, aad, List.append(&2, U32, c, t)) == None{} : Maybe<&2, List<&2, U32>>}, 9n, 12n, hn, {==})
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> n7 <> n8 <> n9 <> Nil{}: no_len({GCM.aes256_gcm_decrypt(key, {[n0, n1, n2, n3, n4, n5, n6, n7, n8, n9] : List<&2, U32>}, aad, List.append(&2, U32, c, t)) == None{} : Maybe<&2, List<&2, U32>>}, 10n, 12n, hn, {==})
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> n7 <> n8 <> n9 <> n10 <> Nil{}: no_len({GCM.aes256_gcm_decrypt(key, {[n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10] : List<&2, U32>}, aad, List.append(&2, U32, c, t)) == None{} : Maybe<&2, List<&2, U32>>}, 11n, 12n, hn, {==})
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> n7 <> n8 <> n9 <> n10 <> n11 <> Nil{}: aes256_forgery_t(key, h, n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, aad, c, t, ht, ne)
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> n7 <> n8 <> n9 <> n10 <> n11 <> nx <> nrest: no_len({GCM.aes256_gcm_decrypt(key, {n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> n7 <> n8 <> n9 <> n10 <> n11 <> nx <> nrest : List<&2, U32>}, aad, List.append(&2, U32, c, t)) == None{} : Maybe<&2, List<&2, U32>>}, 13n+List.length(&2, U32, nrest), 12n, hn, {==})
