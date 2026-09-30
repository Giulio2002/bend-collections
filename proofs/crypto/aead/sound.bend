import Base
import ../../../spec/crypto/chacha.bend as RC
import ../../../spec/crypto/chacha20poly1305.bend as R
import ../../../spec/crypto/subtle.bend as RS
import ../../../spec/crypto/aes/gcm.bend as G
import ../../lib/logic.bend as L
import ../chacha/involution.bend as V
import ../aes/aead.bend as AD
import ./subtle_eq.bend as SE

# Decryption is sound: whatever the specification opens to a plaintext p is
# exactly the sealing of p (same key, nonce and aad). So no input other than
# the honest ciphertext of p ever decrypts to p: an accepted ciphertext
# carries the tag of its body, and the body is the encryption of p (the
# stream is an involution). Stated for the ChaCha20-Poly1305 specification
# (spec/crypto/chacha20poly1305.bend) and the GCM specification
# (spec/crypto/aes/gcm.bend); the facade clause decrypt_sound follows.

# ---------------------------------------------------------------- Maybe

law none_some:
  for +p: List<&2, U32>
  for +h: {None{} == Some{p} : Maybe<&2, List<&2, U32>>}
  Empty

def none_some(p, h):
  L.false_true(Equal.cong(Maybe<&2, List<&2, U32>>, Bool, m => Maybe.is_some(&2, List<&2, U32>, m), None{}, Some{p}, h))

law some_inj:
  for +x: List<&2, U32>
  for +p: List<&2, U32>
  for +h: {Some{x} == Some{p} : Maybe<&2, List<&2, U32>>}
  {x == p : List<&2, U32>}

def some_inj(x, p, h):
  Equal.cong(Maybe<&2, List<&2, U32>>, List<&2, U32>, m => Maybe.default(&2, List<&2, U32>, m, Nil{}), Some{x}, Some{p}, h)

# ---------------------------------------------------------------- splits

law prefix_suffix:
  for +n: Nat
  for +xs: List<&2, U32>
  {List.append(&2, U32, RC.prefix(n, xs), RC.suffix(n, xs)) == xs : List<&2, U32>}

def prefix_suffix(n, xs):
  match n xs:
    case 0n _: {==}
    case 1n+k Nil{}: {==}
    case 1n+k x <> rest:
      Equal.cong(List<&2, U32>, List<&2, U32>, l => x <> l, List.append(&2, U32, RC.prefix(k, rest), RC.suffix(k, rest)), rest, prefix_suffix(k, rest))

law take_drop:
  for +xs: List<&2, U32>
  for +n: Nat
  {List.append(&2, U32, List.take(&2, U32, xs, n), List.drop(&2, U32, xs, n)) == xs : List<&2, U32>}

def take_drop(xs, n):
  match xs n:
    case Nil{} _: {==}
    case x <> rest 0n: {==}
    case x <> rest 1n+k:
      Equal.cong(List<&2, U32>, List<&2, U32>, l => x <> l, List.append(&2, U32, List.take(&2, U32, rest, k), List.drop(&2, U32, rest, k)), rest, take_drop(rest, k))

# ---------------------------------------------------------------- ChaCha20-Poly1305

def csa(+key: List<&2, U32>, +nonce: List<&2, U32>, +aad: List<&2, U32>, +c: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, c, R.tag(key, nonce, aad, c))

law c_tag:
  for +ok: Bool
  for +key: List<&2, U32>
  for +nonce: List<&2, U32>
  for +aad: List<&2, U32>
  for +ct: List<&2, U32>
  for +t: List<&2, U32>
  for +p: List<&2, U32>
  for +hok: {RS.equal(t, R.tag(key, nonce, aad, ct)) == ok : Bool}
  for +h: {R.open_tag(ok, key, nonce, ct) == Some{p} : Maybe<&2, List<&2, U32>>}
  {R.seal(key, nonce, aad, p) == List.append(&2, U32, ct, t) : List<&2, U32>}

def c_tag(ok, key, nonce, aad, ct, t, p, hok, h):
  match ok:
    case False{}: Empty.absurd({R.seal(key, nonce, aad, p) == List.append(&2, U32, ct, t) : List<&2, U32>}, none_some(p, h))
    case True{}:
      +e = RC.encrypt(key, 1, nonce, ct)
      +ep = some_inj(e, p, h)
      +et = SE.equal_sound(t, R.tag(key, nonce, aad, ct), hok)
      Equal.trans(List<&2, U32>, R.seal(key, nonce, aad, p), csa(key, nonce, aad, RC.encrypt(key, 1, nonce, e)), List.append(&2, U32, ct, t),
        Equal.trans(List<&2, U32>, R.seal(key, nonce, aad, p), R.seal(key, nonce, aad, e), csa(key, nonce, aad, RC.encrypt(key, 1, nonce, e)),
          Equal.cong(List<&2, U32>, List<&2, U32>, q => R.seal(key, nonce, aad, q), p, e, Equal.sym(List<&2, U32>, e, p, ep)),
          {==}),
        Equal.trans(List<&2, U32>, csa(key, nonce, aad, RC.encrypt(key, 1, nonce, e)), csa(key, nonce, aad, ct), List.append(&2, U32, ct, t),
          Equal.cong(List<&2, U32>, List<&2, U32>, q => csa(key, nonce, aad, q), RC.encrypt(key, 1, nonce, e), ct, V.involution(10n, key, 1, nonce, ct)),
          Equal.cong(List<&2, U32>, List<&2, U32>, q => List.append(&2, U32, ct, q), R.tag(key, nonce, aad, ct), t, Equal.sym(List<&2, U32>, t, R.tag(key, nonce, aad, ct), et))))

law c_len:
  for +short: Bool
  for +key: List<&2, U32>
  for +nonce: List<&2, U32>
  for +aad: List<&2, U32>
  for +data: List<&2, U32>
  for +p: List<&2, U32>
  for +h: {R.open_len(short, key, nonce, aad, data) == Some{p} : Maybe<&2, List<&2, U32>>}
  {R.seal(key, nonce, aad, p) == data : List<&2, U32>}

def c_len(short, key, nonce, aad, data, p, h):
  match short:
    case True{}: Empty.absurd({R.seal(key, nonce, aad, p) == data : List<&2, U32>}, none_some(p, h))
    case False{}:
      +n = Nat.sub(List.length(&2, U32, data), 16n)
      +ct = RC.prefix(n, data)
      +t = RC.suffix(n, data)
      Equal.trans(List<&2, U32>, R.seal(key, nonce, aad, p), List.append(&2, U32, ct, t), data,
        c_tag(RS.equal(t, R.tag(key, nonce, aad, ct)), key, nonce, aad, ct, t, p, {==}, h),
        prefix_suffix(n, data))

# Whatever opens to p is the sealing of p.
law chacha_sound:
  for +key: List<&2, U32>
  for +nonce: List<&2, U32>
  for +aad: List<&2, U32>
  for +data: List<&2, U32>
  for +p: List<&2, U32>
  for +h: {R.open(key, nonce, aad, data) == Some{p} : Maybe<&2, List<&2, U32>>}
  {R.seal(key, nonce, aad, p) == data : List<&2, U32>}

def chacha_sound(key, nonce, aad, data, p, h):
  c_len(Nat.is_lt(List.length(&2, U32, data), 16n), key, nonce, aad, data, p, h)

# ---------------------------------------------------------------- GCM

def gsa(+nk: Nat, +nr: Nat, +key: List<&2, U32>, +iv: List<&2, U32>, +aad: List<&2, U32>, +c: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, c, G.tag(nk, nr, key, iv, aad, c))

law g_tag:
  for +ok: Bool
  for +nk: Nat
  for +nr: Nat
  for +key: List<&2, U32>
  for +iv: List<&2, U32>
  for +aad: List<&2, U32>
  for +c: List<&2, U32>
  for +t: List<&2, U32>
  for +p: List<&2, U32>
  for +hok: {RS.equal(t, G.tag(nk, nr, key, iv, aad, c)) == ok : Bool}
  for +h: {G.accept(ok, G.gctr(nk, nr, key, c, G.inc32(G.j0(iv)))) == Some{p} : Maybe<&2, List<&2, U32>>}
  {G.seal(nk, nr, key, iv, aad, p) == List.append(&2, U32, c, t) : List<&2, U32>}

def g_tag(ok, nk, nr, key, iv, aad, c, t, p, hok, h):
  match ok:
    case False{}: Empty.absurd({G.seal(nk, nr, key, iv, aad, p) == List.append(&2, U32, c, t) : List<&2, U32>}, none_some(p, h))
    case True{}:
      +cb = G.inc32(G.j0(iv))
      +e = G.gctr(nk, nr, key, c, cb)
      +ep = some_inj(e, p, h)
      +et = SE.equal_sound(t, G.tag(nk, nr, key, iv, aad, c), hok)
      Equal.trans(List<&2, U32>, G.seal(nk, nr, key, iv, aad, p), gsa(nk, nr, key, iv, aad, G.gctr(nk, nr, key, e, cb)), List.append(&2, U32, c, t),
        Equal.trans(List<&2, U32>, G.seal(nk, nr, key, iv, aad, p), G.seal(nk, nr, key, iv, aad, e), gsa(nk, nr, key, iv, aad, G.gctr(nk, nr, key, e, cb)),
          Equal.cong(List<&2, U32>, List<&2, U32>, q => G.seal(nk, nr, key, iv, aad, q), p, e, Equal.sym(List<&2, U32>, e, p, ep)),
          {==}),
        Equal.trans(List<&2, U32>, gsa(nk, nr, key, iv, aad, G.gctr(nk, nr, key, e, cb)), gsa(nk, nr, key, iv, aad, c), List.append(&2, U32, c, t),
          Equal.cong(List<&2, U32>, List<&2, U32>, q => gsa(nk, nr, key, iv, aad, q), G.gctr(nk, nr, key, e, cb), c, AD.gctr_inv(nk, nr, key, c, cb)),
          Equal.cong(List<&2, U32>, List<&2, U32>, q => List.append(&2, U32, c, q), G.tag(nk, nr, key, iv, aad, c), t, Equal.sym(List<&2, U32>, t, G.tag(nk, nr, key, iv, aad, c), et))))

law g_len:
  for +short: Bool
  for +nk: Nat
  for +nr: Nat
  for +key: List<&2, U32>
  for +iv: List<&2, U32>
  for +aad: List<&2, U32>
  for +input: List<&2, U32>
  for +p: List<&2, U32>
  for +h: {G.open_split(nk, nr, key, iv, aad, input, List.length(&2, U32, input), short) == Some{p} : Maybe<&2, List<&2, U32>>}
  {G.seal(nk, nr, key, iv, aad, p) == input : List<&2, U32>}

def g_len(short, nk, nr, key, iv, aad, input, p, h):
  match short:
    case True{}: Empty.absurd({G.seal(nk, nr, key, iv, aad, p) == input : List<&2, U32>}, none_some(p, h))
    case False{}:
      +n = Nat.sub(List.length(&2, U32, input), 16n)
      +c = List.take(&2, U32, input, n)
      +t = List.drop(&2, U32, input, n)
      Equal.trans(List<&2, U32>, G.seal(nk, nr, key, iv, aad, p), List.append(&2, U32, c, t), input,
        g_tag(RS.equal(t, G.tag(nk, nr, key, iv, aad, c)), nk, nr, key, iv, aad, c, t, p, {==}, h),
        take_drop(input, n))

law gcm_sound:
  for +nk: Nat
  for +nr: Nat
  for +key: List<&2, U32>
  for +iv: List<&2, U32>
  for +aad: List<&2, U32>
  for +input: List<&2, U32>
  for +p: List<&2, U32>
  for +h: {G.open(nk, nr, key, iv, aad, input) == Some{p} : Maybe<&2, List<&2, U32>>}
  {G.seal(nk, nr, key, iv, aad, p) == input : List<&2, U32>}

def gcm_sound(nk, nr, key, iv, aad, input, p, h):
  g_len(Nat.is_lt(List.length(&2, U32, input), 16n), nk, nr, key, iv, aad, input, p, h)
