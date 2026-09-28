import Base
import ../../../src/crypto/aead.bend as A
import ../../../src/crypto/aead/chacha20poly1305.bend as CP
import ../../../src/crypto/aesgcm.bend as GCM
import ../../../spec/crypto/chacha.bend as RC
import ../../../spec/crypto/chacha20poly1305.bend as R
import ../../../spec/crypto/aes/aes.bend as S
import ../../../spec/crypto/aes/gcm.bend as G
import ../../lib/nat.bend as N
import ./laws.bend as Laws
import ./chacha20poly1305.bend as C
import ./aes.bend as AE

# Entry point: `bend proofs/crypto/aead/proof.bend` checks the clauses of
# laws.bend. Each algorithm-generic clause is proved by one case per
# constructor of A.Alg: ChaCha20-Poly1305 and XChaCha20-Poly1305 through
# chacha20poly1305.bend, AES-GCM through aes.bend (the AES-GCM API lemmas of
# proofs/crypto/aes).

# ---- each algorithm is its specification

def Laws.chacha20poly1305.seal(key, nonce, aad, pt):
  Equal.cong(List<&2, U32>, Maybe<&2, List<&2, U32>>, l => Some{l}, CP.seal(key, nonce, aad, pt), R.seal(key, nonce, aad, pt), C.seal_eq(key, nonce, aad, pt))

def Laws.chacha20poly1305.open(key, nonce, aad, data):
  C.open_eq(key, nonce, aad, data)

def Laws.xchacha20poly1305.seal(key, nonce, aad, pt):
  Equal.cong(List<&2, U32>, Maybe<&2, List<&2, U32>>, l => Some{l}, CP.xseal(key, nonce, aad, pt), R.xseal(key, nonce, aad, pt), C.xseal_eq(key, nonce, aad, pt))

def Laws.xchacha20poly1305.open(key, nonce, aad, data):
  C.xopen_eq(key, nonce, aad, data)

def Laws.aes128gcm.seal(key, hk, nonce, hn, aad, pt):
  AE.aes128_encrypt_l(key, hk, nonce, hn, aad, pt)

def Laws.aes128gcm.open(key, hk, nonce, hn, aad, data):
  AE.aes128_decrypt_l(key, hk, nonce, hn, aad, data)

def Laws.aes256gcm.seal(key, hk, nonce, hn, aad, pt):
  AE.aes256_encrypt_l(key, hk, nonce, hn, aad, pt)

def Laws.aes256gcm.open(key, hk, nonce, hn, aad, data):
  AE.aes256_decrypt_l(key, hk, nonce, hn, aad, data)

law when_same:
  for +ok: Bool
  for +x: List<&2, U32>
  {CP.when(ok, x) == A.when_open(ok, Some{x}) : Maybe<&2, List<&2, U32>>}

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

law encrypt_valid:
  for +alg: A.Alg
  for +key: List<&2, U32>
  for +nonce: List<&2, U32>
  for +aad: List<&2, U32>
  for +pt: List<&2, U32>
  for +hk: {List.length(&2, U32, key) == A.key_size(alg) : Nat}
  for +hn: {List.length(&2, U32, nonce) == A.nonce_size(alg) : Nat}
  {A.encrypt(alg, key, nonce, aad, pt) == A.seal(alg, key, nonce, aad, pt) : Maybe<&2, List<&2, U32>>}

def encrypt_valid(alg, key, nonce, aad, pt, hk, hn):
  %Equal.sym(Bool, A.valid(alg, key, nonce), True{}, valid_true(alg, key, nonce, hk, hn)) :
    {A.when_open(_, A.seal(alg, key, nonce, aad, pt)) == A.seal(alg, key, nonce, aad, pt) : Maybe<&2, List<&2, U32>>}
  {==}

def Laws.encrypt.valid(alg, key, nonce, aad, pt, hk, hn):
  encrypt_valid(alg, key, nonce, aad, pt, hk, hn)

def Laws.encrypt.invalid(alg, key, nonce, aad, pt, h):
  %Equal.sym(Bool, A.valid(alg, key, nonce), False{}, h) :
    {A.when_open(_, A.seal(alg, key, nonce, aad, pt)) == None{} : Maybe<&2, List<&2, U32>>}
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

# ---- round trip

# decrypt after encrypt is open after seal (on valid lengths).
def open_sealed(+alg: A.Alg, +key: List<&2, U32>, +nonce: List<&2, U32>, +aad: List<&2, U32>, m: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match m:
    case None{}: None{}
    case Some{c}: A.open(alg, key, nonce, aad, c)

law ds_open:
  for +alg: A.Alg
  for +key: List<&2, U32>
  for +nonce: List<&2, U32>
  for +aad: List<&2, U32>
  for +m: Maybe<&2, List<&2, U32>>
  for +hk: {List.length(&2, U32, key) == A.key_size(alg) : Nat}
  for +hn: {List.length(&2, U32, nonce) == A.nonce_size(alg) : Nat}
  {Laws.decrypt_sealed(alg, key, nonce, aad, m) == open_sealed(alg, key, nonce, aad, m) : Maybe<&2, List<&2, U32>>}

def ds_open(alg, key, nonce, aad, m, hk, hn):
  match m:
    case None{}: {==}
    case Some{c}: decrypt_valid(alg, key, nonce, aad, c, hk, hn)

law os128:
  for +key: List<&2, U32>
  for +nonce: List<&2, U32>
  for +aad: List<&2, U32>
  for +m: Maybe<&2, List<&2, U32>>
  {open_sealed(A.AES_128_GCM{}, key, nonce, aad, m) == AE.open128(key, nonce, aad, m) : Maybe<&2, List<&2, U32>>}

def os128(key, nonce, aad, m):
  match m:
    case None{}: {==}
    case Some{c}: {==}

law os256:
  for +key: List<&2, U32>
  for +nonce: List<&2, U32>
  for +aad: List<&2, U32>
  for +m: Maybe<&2, List<&2, U32>>
  {open_sealed(A.AES_256_GCM{}, key, nonce, aad, m) == AE.open256(key, nonce, aad, m) : Maybe<&2, List<&2, U32>>}

def os256(key, nonce, aad, m):
  match m:
    case None{}: {==}
    case Some{c}: {==}

law open_seal:
  for +alg: A.Alg
  for +key: List<&2, U32>
  for +nonce: List<&2, U32>
  for +aad: List<&2, U32>
  for +pt: List<&2, U32>
  for +hk: {List.length(&2, U32, key) == A.key_size(alg) : Nat}
  for +hn: {List.length(&2, U32, nonce) == A.nonce_size(alg) : Nat}
  {open_sealed(alg, key, nonce, aad, A.seal(alg, key, nonce, aad, pt)) == Some{pt} : Maybe<&2, List<&2, U32>>}

def open_seal(alg, key, nonce, aad, pt, hk, hn):
  match alg:
    case A.CHACHA20_POLY1305{}: C.iroundtrip(key, nonce, aad, pt)
    case A.XCHACHA20_POLY1305{}: C.iroundtrip(CP.xkey(key, nonce), CP.xnonce(nonce), aad, pt)
    case A.AES_128_GCM{}:
      Equal.trans(Maybe<&2, List<&2, U32>>, open_sealed(A.AES_128_GCM{}, key, nonce, aad, GCM.aes128_gcm_encrypt(key, nonce, aad, pt)), AE.open128(key, nonce, aad, GCM.aes128_gcm_encrypt(key, nonce, aad, pt)), Some{pt},
        os128(key, nonce, aad, GCM.aes128_gcm_encrypt(key, nonce, aad, pt)),
        AE.aes128_roundtrip_l(key, hk, nonce, hn, aad, pt))
    case A.AES_256_GCM{}:
      Equal.trans(Maybe<&2, List<&2, U32>>, open_sealed(A.AES_256_GCM{}, key, nonce, aad, GCM.aes256_gcm_encrypt(key, nonce, aad, pt)), AE.open256(key, nonce, aad, GCM.aes256_gcm_encrypt(key, nonce, aad, pt)), Some{pt},
        os256(key, nonce, aad, GCM.aes256_gcm_encrypt(key, nonce, aad, pt)),
        AE.aes256_roundtrip_l(key, hk, nonce, hn, aad, pt))

def Laws.roundtrip(alg, key, nonce, aad, pt, hk, hn):
  +E = A.encrypt(alg, key, nonce, aad, pt)
  +SE = A.seal(alg, key, nonce, aad, pt)
  Equal.trans(Maybe<&2, List<&2, U32>>, Laws.decrypt_sealed(alg, key, nonce, aad, E), open_sealed(alg, key, nonce, aad, E), Some{pt},
    ds_open(alg, key, nonce, aad, E, hk, hn),
    Equal.trans(Maybe<&2, List<&2, U32>>, open_sealed(alg, key, nonce, aad, E), open_sealed(alg, key, nonce, aad, SE), Some{pt},
      Equal.cong(Maybe<&2, List<&2, U32>>, Maybe<&2, List<&2, U32>>, m => open_sealed(alg, key, nonce, aad, m), E, SE, encrypt_valid(alg, key, nonce, aad, pt, hk, hn)),
      open_seal(alg, key, nonce, aad, pt, hk, hn)))

# ---- forgery

law open_forged:
  for +alg: A.Alg
  for +key: List<&2, U32>
  for +nonce: List<&2, U32>
  for +aad: List<&2, U32>
  for +ct: List<&2, U32>
  for +t: List<&2, U32>
  for +hk: {List.length(&2, U32, key) == A.key_size(alg) : Nat}
  for +hn: {List.length(&2, U32, nonce) == A.nonce_size(alg) : Nat}
  for +ht: {List.length(&2, U32, t) == 16n : Nat}
  for ne: {t != Laws.expected_tag(alg, key, nonce, aad, ct) : List<&2, U32>}
  {A.open(alg, key, nonce, aad, List.append(&2, U32, ct, t)) == None{} : Maybe<&2, List<&2, U32>>}

def open_forged(alg, key, nonce, aad, ct, t, hk, hn, ht, ne):
  match alg:
    case A.CHACHA20_POLY1305{}:
      Equal.trans(Maybe<&2, List<&2, U32>>, CP.open(key, nonce, aad, List.append(&2, U32, ct, t)), R.open(key, nonce, aad, List.append(&2, U32, ct, t)), None{},
        C.open_eq(key, nonce, aad, List.append(&2, U32, ct, t)),
        C.forgery(key, nonce, aad, ct, t, ht, ne))
    case A.XCHACHA20_POLY1305{}:
      Equal.trans(Maybe<&2, List<&2, U32>>, CP.xopen(key, nonce, aad, List.append(&2, U32, ct, t)), R.xopen(key, nonce, aad, List.append(&2, U32, ct, t)), None{},
        C.xopen_eq(key, nonce, aad, List.append(&2, U32, ct, t)),
        C.forgery(RC.xsubkey(key, nonce), RC.xnonce(nonce), aad, ct, t, ht, ne))
    case A.AES_128_GCM{}: AE.aes128_forgery_l(key, hk, nonce, hn, aad, ct, t, ht, ne)
    case A.AES_256_GCM{}: AE.aes256_forgery_l(key, hk, nonce, hn, aad, ct, t, ht, ne)

def Laws.forgery(alg, key, nonce, aad, ct, t, hk, hn, ht, ne):
  Equal.trans(Maybe<&2, List<&2, U32>>, A.decrypt(alg, key, nonce, aad, List.append(&2, U32, ct, t)), A.open(alg, key, nonce, aad, List.append(&2, U32, ct, t)), None{},
    decrypt_valid(alg, key, nonce, aad, List.append(&2, U32, ct, t), hk, hn),
    open_forged(alg, key, nonce, aad, ct, t, hk, hn, ht, ne))

# ---- layout

def sapp(+ct: List<&2, U32>, +t: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  Some{List.append(&2, U32, ct, t)}

law layout_cp:
  for +key: List<&2, U32>
  for +nonce: List<&2, U32>
  for +aad: List<&2, U32>
  for +pt: List<&2, U32>
  {A.seal(A.CHACHA20_POLY1305{}, key, nonce, aad, pt) == sapp(CP.encrypt_ct(key, nonce, pt), R.tag(key, nonce, aad, CP.encrypt_ct(key, nonce, pt))) : Maybe<&2, List<&2, U32>>}

def layout_cp(key, nonce, aad, pt):
  +ct = CP.encrypt_ct(key, nonce, pt)
  Equal.cong(List<&2, U32>, Maybe<&2, List<&2, U32>>, l => sapp(ct, l), CP.tag(key, nonce, aad, ct), R.tag(key, nonce, aad, ct), C.tag_eq(key, nonce, aad, ct))

law layout_x:
  for +key: List<&2, U32>
  for +nonce: List<&2, U32>
  for +aad: List<&2, U32>
  for +pt: List<&2, U32>
  {A.seal(A.XCHACHA20_POLY1305{}, key, nonce, aad, pt) == sapp(CP.encrypt_ct(CP.xkey(key, nonce), CP.xnonce(nonce), pt), R.tag(RC.xsubkey(key, nonce), RC.xnonce(nonce), aad, CP.encrypt_ct(CP.xkey(key, nonce), CP.xnonce(nonce), pt))) : Maybe<&2, List<&2, U32>>}

def layout_x(key, nonce, aad, pt):
  +k = CP.xkey(key, nonce)
  +n = CP.xnonce(nonce)
  +ct = CP.encrypt_ct(k, n, pt)
  Equal.trans(Maybe<&2, List<&2, U32>>, sapp(ct, CP.tag(k, n, aad, ct)), sapp(ct, R.tag(k, n, aad, ct)), sapp(ct, R.tag(RC.xsubkey(key, nonce), RC.xnonce(nonce), aad, ct)),
    Equal.cong(List<&2, U32>, Maybe<&2, List<&2, U32>>, l => sapp(ct, l), CP.tag(k, n, aad, ct), R.tag(k, n, aad, ct), C.tag_eq(k, n, aad, ct)),
    Equal.trans(Maybe<&2, List<&2, U32>>, sapp(ct, R.tag(k, n, aad, ct)), sapp(ct, R.tag(RC.xsubkey(key, nonce), n, aad, ct)), sapp(ct, R.tag(RC.xsubkey(key, nonce), RC.xnonce(nonce), aad, ct)),
      Equal.cong(List<&2, U32>, Maybe<&2, List<&2, U32>>, l => sapp(ct, R.tag(l, n, aad, ct)), k, RC.xsubkey(key, nonce), C.xkey_eq(key, nonce)),
      Equal.cong(List<&2, U32>, Maybe<&2, List<&2, U32>>, l => sapp(ct, R.tag(RC.xsubkey(key, nonce), l, aad, ct)), n, RC.xnonce(nonce), C.xnonce_eq(nonce))))

def gct(+key: List<&2, U32>, +nonce: List<&2, U32>, +pt: List<&2, U32>) -> List<&2, U32>:
  G.gctr(S.nk(key), S.nr(key), key, pt, G.inc32(G.j0(nonce)))

def Laws.seal_layout(alg, key, nonce, aad, pt, hk, hn):
  match alg:
    case A.CHACHA20_POLY1305{}:
      (CP.encrypt_ct(key, nonce, pt), Equal.trans(Maybe<&2, List<&2, U32>>, A.encrypt(A.CHACHA20_POLY1305{}, key, nonce, aad, pt), A.seal(A.CHACHA20_POLY1305{}, key, nonce, aad, pt), sapp(CP.encrypt_ct(key, nonce, pt), R.tag(key, nonce, aad, CP.encrypt_ct(key, nonce, pt))),
        encrypt_valid(A.CHACHA20_POLY1305{}, key, nonce, aad, pt, hk, hn), layout_cp(key, nonce, aad, pt)))
    case A.XCHACHA20_POLY1305{}:
      (CP.encrypt_ct(CP.xkey(key, nonce), CP.xnonce(nonce), pt), Equal.trans(Maybe<&2, List<&2, U32>>, A.encrypt(A.XCHACHA20_POLY1305{}, key, nonce, aad, pt), A.seal(A.XCHACHA20_POLY1305{}, key, nonce, aad, pt), sapp(CP.encrypt_ct(CP.xkey(key, nonce), CP.xnonce(nonce), pt), R.tag(RC.xsubkey(key, nonce), RC.xnonce(nonce), aad, CP.encrypt_ct(CP.xkey(key, nonce), CP.xnonce(nonce), pt))),
        encrypt_valid(A.XCHACHA20_POLY1305{}, key, nonce, aad, pt, hk, hn), layout_x(key, nonce, aad, pt)))
    case A.AES_128_GCM{}:
      (gct(key, nonce, pt), Equal.trans(Maybe<&2, List<&2, U32>>, A.encrypt(A.AES_128_GCM{}, key, nonce, aad, pt), A.seal(A.AES_128_GCM{}, key, nonce, aad, pt), Some{G.aes_seal(key, nonce, aad, pt)},
        encrypt_valid(A.AES_128_GCM{}, key, nonce, aad, pt, hk, hn), AE.aes128_encrypt_l(key, hk, nonce, hn, aad, pt)))
    case A.AES_256_GCM{}:
      (gct(key, nonce, pt), Equal.trans(Maybe<&2, List<&2, U32>>, A.encrypt(A.AES_256_GCM{}, key, nonce, aad, pt), A.seal(A.AES_256_GCM{}, key, nonce, aad, pt), Some{G.aes_seal(key, nonce, aad, pt)},
        encrypt_valid(A.AES_256_GCM{}, key, nonce, aad, pt, hk, hn), AE.aes256_encrypt_l(key, hk, nonce, hn, aad, pt)))
