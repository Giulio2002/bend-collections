import Base
import ../../../src/crypto/aead.bend as A
import ../../../src/crypto/aead/chacha20poly1305.bend as CP
import ../../../spec/crypto/chacha20poly1305.bend as R
import ../../lib/nat.bend as N
import ./laws.bend as Laws
import ./chacha20poly1305.bend as C

# Entry point: `bend proofs/crypto/aead/proof.bend` checks the clauses of
# laws.bend. Each algorithm-generic clause is proved by one case per
# constructor of A.Alg.

def Laws.chacha20poly1305.seal(key, nonce, aad, pt):
  C.seal_eq(key, nonce, aad, pt)

def Laws.chacha20poly1305.open(key, nonce, aad, data):
  C.open_eq(key, nonce, aad, data)

def Laws.xchacha20poly1305.seal(key, nonce, aad, pt):
  C.xseal_eq(key, nonce, aad, pt)

def Laws.xchacha20poly1305.open(key, nonce, aad, data):
  C.xopen_eq(key, nonce, aad, data)

law when_same:
  for +ok: Bool
  for +x: List<&2, U32>
  {CP.when(ok, x) == A.when(ok, x) : Maybe<&2, List<&2, U32>>}

def when_same(ok, x):
  match ok:
    case True{}: {==}
    case False{}: {==}

law when_open_same:
  for +ok: Bool
  for +r: Maybe<&2, List<&2, U32>>
  {CP.when_open(ok, r) == A.when_open(ok, r) : Maybe<&2, List<&2, U32>>}

def when_open_same(ok, r):
  match ok:
    case True{}: {==}
    case False{}: {==}

def Laws.chacha20poly1305.encrypt(key, nonce, aad, pt):
  when_same(CP.lengths_ok(key, nonce, 12n), CP.seal(key, nonce, aad, pt))

def Laws.chacha20poly1305.decrypt(key, nonce, aad, data):
  when_open_same(CP.lengths_ok(key, nonce, 12n), CP.open(key, nonce, aad, data))

def Laws.xchacha20poly1305.encrypt(key, nonce, aad, pt):
  when_same(CP.lengths_ok(key, nonce, 24n), CP.xseal(key, nonce, aad, pt))

def Laws.xchacha20poly1305.decrypt(key, nonce, aad, data):
  when_open_same(CP.lengths_ok(key, nonce, 24n), CP.xopen(key, nonce, aad, data))

# ---- the checked API

law valid_true:
  for +alg: A.Alg
  for +key: List<&2, U32>
  for +nonce: List<&2, U32>
  for +hk: {List.length(&2, U32, key) == A.key_size(alg) : Nat}
  for +hn: {List.length(&2, U32, nonce) == A.nonce_size(alg) : Nat}
  {A.valid(alg, key, nonce) == True{} : Bool}

def valid_true(alg, key, nonce, hk, hn):
  %Equal.sym(Nat, List.length(&2, U32, key), A.key_size(alg), hk) :
    {Bool.and(Nat.is_eq(_, A.key_size(alg)), Nat.is_eq(List.length(&2, U32, nonce), A.nonce_size(alg))) == True{} : Bool}
  %Equal.sym(Nat, List.length(&2, U32, nonce), A.nonce_size(alg), hn) :
    {Bool.and(Nat.is_eq(A.key_size(alg), A.key_size(alg)), Nat.is_eq(_, A.nonce_size(alg))) == True{} : Bool}
  %Equal.sym(Bool, Nat.is_eq(A.key_size(alg), A.key_size(alg)), True{}, N.is_eq_refl(A.key_size(alg))) :
    {Bool.and(_, Nat.is_eq(A.nonce_size(alg), A.nonce_size(alg))) == True{} : Bool}
  N.is_eq_refl(A.nonce_size(alg))

def Laws.encrypt.valid(alg, key, nonce, aad, pt, hk, hn):
  %Equal.sym(Bool, A.valid(alg, key, nonce), True{}, valid_true(alg, key, nonce, hk, hn)) :
    {A.when(_, A.seal(alg, key, nonce, aad, pt)) == Some{A.seal(alg, key, nonce, aad, pt)} : Maybe<&2, List<&2, U32>>}
  {==}

def Laws.encrypt.invalid(alg, key, nonce, aad, pt, h):
  %Equal.sym(Bool, A.valid(alg, key, nonce), False{}, h) :
    {A.when(_, A.seal(alg, key, nonce, aad, pt)) == None{} : Maybe<&2, List<&2, U32>>}
  {==}

law decrypt_valid:
  for +alg: A.Alg
  for +key: List<&2, U32>
  for +nonce: List<&2, U32>
  for +aad: List<&2, U32>
  for +data: List<&2, U32>
  for +hk: {List.length(&2, U32, key) == A.key_size(alg) : Nat}
  for +hn: {List.length(&2, U32, nonce) == A.nonce_size(alg) : Nat}
  {A.decrypt(alg, key, nonce, aad, data) == A.open(alg, key, nonce, aad, data) : Maybe<&2, List<&2, U32>>}

def decrypt_valid(alg, key, nonce, aad, data, hk, hn):
  %Equal.sym(Bool, A.valid(alg, key, nonce), True{}, valid_true(alg, key, nonce, hk, hn)) :
    {A.when_open(_, A.open(alg, key, nonce, aad, data)) == A.open(alg, key, nonce, aad, data) : Maybe<&2, List<&2, U32>>}
  {==}

def Laws.decrypt.valid(alg, key, nonce, aad, data, hk, hn):
  decrypt_valid(alg, key, nonce, aad, data, hk, hn)

def Laws.decrypt.invalid(alg, key, nonce, aad, data, h):
  %Equal.sym(Bool, A.valid(alg, key, nonce), False{}, h) :
    {A.when_open(_, A.open(alg, key, nonce, aad, data)) == None{} : Maybe<&2, List<&2, U32>>}
  {==}

# ---- the AEAD properties

law open_seal:
  for +alg: A.Alg
  for +key: List<&2, U32>
  for +nonce: List<&2, U32>
  for +aad: List<&2, U32>
  for +pt: List<&2, U32>
  {A.open(alg, key, nonce, aad, A.seal(alg, key, nonce, aad, pt)) == Some{pt} : Maybe<&2, List<&2, U32>>}

def open_seal(alg, key, nonce, aad, pt):
  match alg:
    case A.CHACHA20_POLY1305{}: C.iroundtrip(key, nonce, aad, pt)
    case A.XCHACHA20_POLY1305{}: C.iroundtrip(CP.xkey(key, nonce), CP.xnonce(nonce), aad, pt)

def Laws.roundtrip(alg, key, nonce, aad, pt, hk, hn):
  Equal.trans(Maybe<&2, List<&2, U32>>, A.decrypt(alg, key, nonce, aad, A.seal(alg, key, nonce, aad, pt)), A.open(alg, key, nonce, aad, A.seal(alg, key, nonce, aad, pt)), Some{pt},
    decrypt_valid(alg, key, nonce, aad, A.seal(alg, key, nonce, aad, pt), hk, hn),
    open_seal(alg, key, nonce, aad, pt))

law open_forged:
  for +alg: A.Alg
  for +key: List<&2, U32>
  for +nonce: List<&2, U32>
  for +aad: List<&2, U32>
  for +ct: List<&2, U32>
  for +t: List<&2, U32>
  for +ht: {List.length(&2, U32, t) == 16n : Nat}
  for ne: {t != A.expected_tag(alg, key, nonce, aad, ct) : List<&2, U32>}
  {A.open(alg, key, nonce, aad, List.append(&2, U32, ct, t)) == None{} : Maybe<&2, List<&2, U32>>}

def open_forged(alg, key, nonce, aad, ct, t, ht, ne):
  match alg:
    case A.CHACHA20_POLY1305{}: C.iforgery(key, nonce, aad, ct, t, ht, ne)
    case A.XCHACHA20_POLY1305{}: C.iforgery(CP.xkey(key, nonce), CP.xnonce(nonce), aad, ct, t, ht, ne)

def Laws.forgery(alg, key, nonce, aad, ct, t, hk, hn, ht, ne):
  Equal.trans(Maybe<&2, List<&2, U32>>, A.decrypt(alg, key, nonce, aad, List.append(&2, U32, ct, t)), A.open(alg, key, nonce, aad, List.append(&2, U32, ct, t)), None{},
    decrypt_valid(alg, key, nonce, aad, List.append(&2, U32, ct, t), hk, hn),
    open_forged(alg, key, nonce, aad, ct, t, ht, ne))

def Laws.seal_layout(alg, key, nonce, aad, pt):
  match alg:
    case A.CHACHA20_POLY1305{}: (CP.encrypt_ct(key, nonce, pt), {==})
    case A.XCHACHA20_POLY1305{}: (CP.encrypt_ct(CP.xkey(key, nonce), CP.xnonce(nonce), pt), {==})
