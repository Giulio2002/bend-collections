import Base
import ../../../src/crypto/chacha/chacha20.bend as CH
import ../../../src/crypto/aead/chacha20poly1305.bend as I
import ../../../src/crypto/subtle.bend as S
import ../../../spec/crypto/chacha.bend as RC
import ../../../spec/crypto/poly1305.bend as RP
import ../../../spec/crypto/subtle.bend as RS
import ../../../spec/crypto/chacha20poly1305.bend as R
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../chacha/laws.bend as CL
import ../chacha/proof.bend as CLP
import ../chacha/stream.bend as T
import ../chacha/involution.bend as V
import ../poly1305/laws.bend as PL
import ../poly1305/proof.bend as PLP
import ../subtle/laws.bend as SL
import ../subtle/proof.bend as SLP

# ChaCha20-Poly1305 and XChaCha20-Poly1305 of src/crypto/aead/ against
# spec/crypto/chacha20poly1305.bend (for every key, nonce, aad and message
# list), and the two properties of the specification: opening a sealed
# message gives the plaintext back, and opening ciphertext || t fails for
# every 16-byte t other than the tag of the ciphertext. The composition
# follows HACL*'s Spec.Chacha20Poly1305 / Hacl.Impl.Chacha20Poly1305 and the
# EasyCrypt proof of Almeida et al. 2020 (the AEAD is its two primitives
# plus framing), the primitives being proved in proofs/crypto/chacha and
# proofs/crypto/poly1305.

# ---------------------------------------------------------------- implementation == specification

law poly_key_eq:
  for +key: List<&2, U32>
  for +nonce: List<&2, U32>
  {I.poly_key(key, nonce) == R.poly_key(key, nonce) : List<&2, U32>}

def poly_key_eq(key, nonce):
  Equal.trans(List<&2, U32>, CH.take(32n, CH.block_rounds(10n, key, 0, nonce)), RC.prefix(32n, CH.block_rounds(10n, key, 0, nonce)), RC.prefix(32n, RC.block(key, 0, nonce)),
    T.take_eq(32n, CH.block_rounds(10n, key, 0, nonce)),
    Equal.cong(List<&2, U32>, List<&2, U32>, l => RC.prefix(32n, l), CH.block_rounds(10n, key, 0, nonce), RC.block(key, 0, nonce), CL.block_rounds(10n, key, 0, nonce)))

law mac_data_eq:
  for +aad: List<&2, U32>
  for +ct: List<&2, U32>
  {I.mac_data(aad, ct) == R.mac_data(aad, ct) : List<&2, U32>}

def mac_data_eq(aad, ct):
  {==}

law tag_eq:
  for +key: List<&2, U32>
  for +nonce: List<&2, U32>
  for +aad: List<&2, U32>
  for +ct: List<&2, U32>
  {I.tag(key, nonce, aad, ct) == R.tag(key, nonce, aad, ct) : List<&2, U32>}

def tag_eq(key, nonce, aad, ct):
  Equal.trans(List<&2, U32>, I.tag(key, nonce, aad, ct), RP.mac(I.poly_key(key, nonce), I.mac_data(aad, ct)), R.tag(key, nonce, aad, ct),
    PL.mac_correct(I.poly_key(key, nonce), I.mac_data(aad, ct)),
    Equal.trans(List<&2, U32>, RP.mac(I.poly_key(key, nonce), I.mac_data(aad, ct)), RP.mac(R.poly_key(key, nonce), I.mac_data(aad, ct)), R.tag(key, nonce, aad, ct),
      Equal.cong(List<&2, U32>, List<&2, U32>, l => RP.mac(l, I.mac_data(aad, ct)), I.poly_key(key, nonce), R.poly_key(key, nonce), poly_key_eq(key, nonce)),
      Equal.cong(List<&2, U32>, List<&2, U32>, l => RP.mac(R.poly_key(key, nonce), l), I.mac_data(aad, ct), R.mac_data(aad, ct), mac_data_eq(aad, ct))))

def iseal(+key: List<&2, U32>, +nonce: List<&2, U32>, +aad: List<&2, U32>, +ct: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, ct, I.tag(key, nonce, aad, ct))

law seal_eq:
  for +key: List<&2, U32>
  for +nonce: List<&2, U32>
  for +aad: List<&2, U32>
  for +pt: List<&2, U32>
  {I.seal(key, nonce, aad, pt) == R.seal(key, nonce, aad, pt) : List<&2, U32>}

def seal_eq(key, nonce, aad, pt):
  +ci = CH.encrypt_rounds(10n, key, 1, nonce, pt)
  +cr = RC.encrypt(key, 1, nonce, pt)
  Equal.trans(List<&2, U32>, iseal(key, nonce, aad, ci), iseal(key, nonce, aad, cr), R.seal(key, nonce, aad, pt),
    Equal.cong(List<&2, U32>, List<&2, U32>, l => iseal(key, nonce, aad, l), ci, cr, CL.encrypt_rounds(10n, key, 1, nonce, pt)),
    Equal.cong(List<&2, U32>, List<&2, U32>, l => List.append(&2, U32, cr, l), I.tag(key, nonce, aad, cr), R.tag(key, nonce, aad, cr), tag_eq(key, nonce, aad, cr)))

law open_tag_eq:
  for +ok: Bool
  for +key: List<&2, U32>
  for +nonce: List<&2, U32>
  for +ct: List<&2, U32>
  {I.open_tag(ok, key, nonce, ct) == R.open_tag(ok, key, nonce, ct) : Maybe<&2, List<&2, U32>>}

def open_tag_eq(ok, key, nonce, ct):
  match ok:
    case True{}:
      Equal.cong(List<&2, U32>, Maybe<&2, List<&2, U32>>, l => Some{l}, CH.encrypt_rounds(10n, key, 1, nonce, ct), RC.encrypt(key, 1, nonce, ct), CL.encrypt_rounds(10n, key, 1, nonce, ct))
    case False{}: {==}

law open_split_eq:
  for +key: List<&2, U32>
  for +nonce: List<&2, U32>
  for +aad: List<&2, U32>
  for +ct: List<&2, U32>
  for +t: List<&2, U32>
  {I.open_split(key, nonce, aad, ct, t) == R.open_split(key, nonce, aad, ct, t) : Maybe<&2, List<&2, U32>>}

def open_split_eq(key, nonce, aad, ct, t):
  Equal.trans(Maybe<&2, List<&2, U32>>, I.open_tag(S.eq(t, I.tag(key, nonce, aad, ct)), key, nonce, ct), I.open_tag(RS.equal(t, R.tag(key, nonce, aad, ct)), key, nonce, ct), R.open_split(key, nonce, aad, ct, t),
    Equal.trans(Maybe<&2, List<&2, U32>>, I.open_tag(S.eq(t, I.tag(key, nonce, aad, ct)), key, nonce, ct), I.open_tag(RS.equal(t, I.tag(key, nonce, aad, ct)), key, nonce, ct), I.open_tag(RS.equal(t, R.tag(key, nonce, aad, ct)), key, nonce, ct),
      Equal.cong(Bool, Maybe<&2, List<&2, U32>>, b => I.open_tag(b, key, nonce, ct), S.eq(t, I.tag(key, nonce, aad, ct)), RS.equal(t, I.tag(key, nonce, aad, ct)), SL.Eq.value(t, I.tag(key, nonce, aad, ct))),
      Equal.cong(List<&2, U32>, Maybe<&2, List<&2, U32>>, l => I.open_tag(RS.equal(t, l), key, nonce, ct), I.tag(key, nonce, aad, ct), R.tag(key, nonce, aad, ct), tag_eq(key, nonce, aad, ct))),
    open_tag_eq(RS.equal(t, R.tag(key, nonce, aad, ct)), key, nonce, ct))

law open_len_eq:
  for +short: Bool
  for +key: List<&2, U32>
  for +nonce: List<&2, U32>
  for +aad: List<&2, U32>
  for +data: List<&2, U32>
  {I.open_len(short, key, nonce, aad, data) == R.open_len(short, key, nonce, aad, data) : Maybe<&2, List<&2, U32>>}

def ospl(+key: List<&2, U32>, +nonce: List<&2, U32>, +aad: List<&2, U32>, +ct: List<&2, U32>, +t: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  I.open_split(key, nonce, aad, ct, t)

def open_len_eq(short, key, nonce, aad, data):
  match short:
    case True{}: {==}
    case False{}:
      +n = Nat.sub(List.length(&2, U32, data), 16n)
      Equal.trans(Maybe<&2, List<&2, U32>>, ospl(key, nonce, aad, CH.take(n, data), CH.skip(n, data)), ospl(key, nonce, aad, RC.prefix(n, data), RC.suffix(n, data)), R.open_split(key, nonce, aad, RC.prefix(n, data), RC.suffix(n, data)),
        Equal.trans(Maybe<&2, List<&2, U32>>, ospl(key, nonce, aad, CH.take(n, data), CH.skip(n, data)), ospl(key, nonce, aad, RC.prefix(n, data), CH.skip(n, data)), ospl(key, nonce, aad, RC.prefix(n, data), RC.suffix(n, data)),
          Equal.cong(List<&2, U32>, Maybe<&2, List<&2, U32>>, l => ospl(key, nonce, aad, l, CH.skip(n, data)), CH.take(n, data), RC.prefix(n, data), T.take_eq(n, data)),
          Equal.cong(List<&2, U32>, Maybe<&2, List<&2, U32>>, l => ospl(key, nonce, aad, RC.prefix(n, data), l), CH.skip(n, data), RC.suffix(n, data), T.skip_eq(n, data))),
        open_split_eq(key, nonce, aad, RC.prefix(n, data), RC.suffix(n, data)))

law open_eq:
  for +key: List<&2, U32>
  for +nonce: List<&2, U32>
  for +aad: List<&2, U32>
  for +data: List<&2, U32>
  {I.open(key, nonce, aad, data) == R.open(key, nonce, aad, data) : Maybe<&2, List<&2, U32>>}

def open_eq(key, nonce, aad, data):
  open_len_eq(Nat.is_lt(List.length(&2, U32, data), 16n), key, nonce, aad, data)

law xkey_eq:
  for +key: List<&2, U32>
  for +nonce: List<&2, U32>
  {I.xkey(key, nonce) == RC.xsubkey(key, nonce) : List<&2, U32>}

def xkey_eq(key, nonce):
  Equal.trans(List<&2, U32>, CH.hchacha20_unchecked(key, CH.take(16n, nonce)), RC.hchacha20(key, CH.take(16n, nonce)), RC.hchacha20(key, RC.prefix(16n, nonce)),
    CL.hchacha20(key, CH.take(16n, nonce)),
    Equal.cong(List<&2, U32>, List<&2, U32>, l => RC.hchacha20(key, l), CH.take(16n, nonce), RC.prefix(16n, nonce), T.take_eq(16n, nonce)))

law xnonce_eq:
  for +nonce: List<&2, U32>
  {I.xnonce(nonce) == RC.xnonce(nonce) : List<&2, U32>}

def xnonce_eq(nonce):
  Equal.cong(List<&2, U32>, List<&2, U32>, l => 0 <> 0 <> 0 <> 0 <> l, CH.skip(16n, nonce), RC.suffix(16n, nonce), T.skip_eq(16n, nonce))

law xseal_eq:
  for +key: List<&2, U32>
  for +nonce: List<&2, U32>
  for +aad: List<&2, U32>
  for +pt: List<&2, U32>
  {I.xseal(key, nonce, aad, pt) == R.xseal(key, nonce, aad, pt) : List<&2, U32>}

def xseal_eq(key, nonce, aad, pt):
  Equal.trans(List<&2, U32>, I.seal(I.xkey(key, nonce), I.xnonce(nonce), aad, pt), R.seal(I.xkey(key, nonce), I.xnonce(nonce), aad, pt), R.xseal(key, nonce, aad, pt),
    seal_eq(I.xkey(key, nonce), I.xnonce(nonce), aad, pt),
    Equal.trans(List<&2, U32>, R.seal(I.xkey(key, nonce), I.xnonce(nonce), aad, pt), R.seal(RC.xsubkey(key, nonce), I.xnonce(nonce), aad, pt), R.xseal(key, nonce, aad, pt),
      Equal.cong(List<&2, U32>, List<&2, U32>, l => R.seal(l, I.xnonce(nonce), aad, pt), I.xkey(key, nonce), RC.xsubkey(key, nonce), xkey_eq(key, nonce)),
      Equal.cong(List<&2, U32>, List<&2, U32>, l => R.seal(RC.xsubkey(key, nonce), l, aad, pt), I.xnonce(nonce), RC.xnonce(nonce), xnonce_eq(nonce))))

law xopen_eq:
  for +key: List<&2, U32>
  for +nonce: List<&2, U32>
  for +aad: List<&2, U32>
  for +data: List<&2, U32>
  {I.xopen(key, nonce, aad, data) == R.xopen(key, nonce, aad, data) : Maybe<&2, List<&2, U32>>}

def xopen_eq(key, nonce, aad, data):
  Equal.trans(Maybe<&2, List<&2, U32>>, I.open(I.xkey(key, nonce), I.xnonce(nonce), aad, data), R.open(I.xkey(key, nonce), I.xnonce(nonce), aad, data), R.xopen(key, nonce, aad, data),
    open_eq(I.xkey(key, nonce), I.xnonce(nonce), aad, data),
    Equal.trans(Maybe<&2, List<&2, U32>>, R.open(I.xkey(key, nonce), I.xnonce(nonce), aad, data), R.open(RC.xsubkey(key, nonce), I.xnonce(nonce), aad, data), R.xopen(key, nonce, aad, data),
      Equal.cong(List<&2, U32>, Maybe<&2, List<&2, U32>>, l => R.open(l, I.xnonce(nonce), aad, data), I.xkey(key, nonce), RC.xsubkey(key, nonce), xkey_eq(key, nonce)),
      Equal.cong(List<&2, U32>, Maybe<&2, List<&2, U32>>, l => R.open(RC.xsubkey(key, nonce), l, aad, data), I.xnonce(nonce), RC.xnonce(nonce), xnonce_eq(nonce))))

# ---------------------------------------------------------------- framing

law length_append:
  for +xs: List<&2, U32>
  for +ys: List<&2, U32>
  {List.length(&2, U32, List.append(&2, U32, xs, ys)) == Nat.add(List.length(&2, U32, xs), List.length(&2, U32, ys)) : Nat}

def length_append(xs, ys):
  V.length_append(xs, ys)

law prefix_append:
  for +xs: List<&2, U32>
  for +ys: List<&2, U32>
  {RC.prefix(List.length(&2, U32, xs), List.append(&2, U32, xs, ys)) == xs : List<&2, U32>}

def prefix_append(xs, ys):
  match xs:
    case Nil{}: {==}
    case x <> xt:
      Equal.cong(List<&2, U32>, List<&2, U32>, l => x <> l, RC.prefix(List.length(&2, U32, xt), List.append(&2, U32, xt, ys)), xt, prefix_append(xt, ys))

law suffix_append:
  for +xs: List<&2, U32>
  for +ys: List<&2, U32>
  {RC.suffix(List.length(&2, U32, xs), List.append(&2, U32, xs, ys)) == ys : List<&2, U32>}

def suffix_append(xs, ys):
  match xs:
    case Nil{}: {==}
    case x <> xt: suffix_append(xt, ys)

# a + 16 is not below 16, and (a + 16) - 16 == a.
law add16_not_lt:
  for +a: Nat
  {Nat.is_lt(Nat.add(a, 16n), 16n) == False{} : Bool}

def add16_not_lt(a):
  %N.add_comm(16n, a) : {Nat.is_lt(_, 16n) == False{} : Bool}
  N.not_lt_zero(a)

law add16_sub:
  for +a: Nat
  {Nat.sub(Nat.add(a, 16n), 16n) == a : Nat}

def add16_sub(a):
  %N.add_comm(16n, a) : {Nat.sub(_, 16n) == a : Nat}
  N.sub_zero(a)

# Opening ct || t with a 16-byte t checks t against the tag of ct.
law open_append:
  for +key: List<&2, U32>
  for +nonce: List<&2, U32>
  for +aad: List<&2, U32>
  for +ct: List<&2, U32>
  for +t: List<&2, U32>
  for +ht: {List.length(&2, U32, t) == 16n : Nat}
  {R.open(key, nonce, aad, List.append(&2, U32, ct, t)) == R.open_split(key, nonce, aad, ct, t) : Maybe<&2, List<&2, U32>>}

def olen(+key: List<&2, U32>, +nonce: List<&2, U32>, +aad: List<&2, U32>, +d: List<&2, U32>, short: Bool) -> Maybe<&2, List<&2, U32>>:
  R.open_len(short, key, nonce, aad, d)

def osplit_at(+key: List<&2, U32>, +nonce: List<&2, U32>, +aad: List<&2, U32>, +d: List<&2, U32>, +n: Nat) -> Maybe<&2, List<&2, U32>>:
  R.open_split(key, nonce, aad, RC.prefix(n, d), RC.suffix(n, d))

def open_append(key, nonce, aad, ct, t, ht):
  +D = List.append(&2, U32, ct, t)
  +lc = List.length(&2, U32, ct)
  +elen = Equal.trans(Nat, List.length(&2, U32, D), Nat.add(lc, List.length(&2, U32, t)), Nat.add(lc, 16n),
    length_append(ct, t),
    Equal.cong(Nat, Nat, m => Nat.add(lc, m), List.length(&2, U32, t), 16n, ht))
  +eshort = Equal.trans(Bool, Nat.is_lt(List.length(&2, U32, D), 16n), Nat.is_lt(Nat.add(lc, 16n), 16n), False{},
    Equal.cong(Nat, Bool, m => Nat.is_lt(m, 16n), List.length(&2, U32, D), Nat.add(lc, 16n), elen),
    add16_not_lt(lc))
  +esub = Equal.trans(Nat, Nat.sub(List.length(&2, U32, D), 16n), Nat.sub(Nat.add(lc, 16n), 16n), lc,
    Equal.cong(Nat, Nat, m => Nat.sub(m, 16n), List.length(&2, U32, D), Nat.add(lc, 16n), elen),
    add16_sub(lc))
  Equal.trans(Maybe<&2, List<&2, U32>>, olen(key, nonce, aad, D, Nat.is_lt(List.length(&2, U32, D), 16n)), olen(key, nonce, aad, D, False{}), R.open_split(key, nonce, aad, ct, t),
    Equal.cong(Bool, Maybe<&2, List<&2, U32>>, b => olen(key, nonce, aad, D, b), Nat.is_lt(List.length(&2, U32, D), 16n), False{}, eshort),
    Equal.trans(Maybe<&2, List<&2, U32>>, osplit_at(key, nonce, aad, D, Nat.sub(List.length(&2, U32, D), 16n)), osplit_at(key, nonce, aad, D, lc), R.open_split(key, nonce, aad, ct, t),
      Equal.cong(Nat, Maybe<&2, List<&2, U32>>, m => osplit_at(key, nonce, aad, D, m), Nat.sub(List.length(&2, U32, D), 16n), lc, esub),
      Equal.trans(Maybe<&2, List<&2, U32>>, R.open_split(key, nonce, aad, RC.prefix(lc, D), RC.suffix(lc, D)), R.open_split(key, nonce, aad, ct, RC.suffix(lc, D)), R.open_split(key, nonce, aad, ct, t),
        Equal.cong(List<&2, U32>, Maybe<&2, List<&2, U32>>, l => R.open_split(key, nonce, aad, l, RC.suffix(lc, D)), RC.prefix(lc, D), ct, prefix_append(ct, t)),
        Equal.cong(List<&2, U32>, Maybe<&2, List<&2, U32>>, l => R.open_split(key, nonce, aad, ct, l), RC.suffix(lc, D), t, suffix_append(ct, t)))))

# ---------------------------------------------------------------- properties of the specification

# Opening what was sealed gives the plaintext back (for every key, nonce,
# aad and plaintext list).
law roundtrip:
  for +key: List<&2, U32>
  for +nonce: List<&2, U32>
  for +aad: List<&2, U32>
  for +pt: List<&2, U32>
  {R.open(key, nonce, aad, R.seal(key, nonce, aad, pt)) == Some{pt} : Maybe<&2, List<&2, U32>>}

def roundtrip(key, nonce, aad, pt):
  +ct = RC.encrypt(key, 1, nonce, pt)
  +t = R.tag(key, nonce, aad, ct)
  Equal.trans(Maybe<&2, List<&2, U32>>, R.open(key, nonce, aad, List.append(&2, U32, ct, t)), R.open_split(key, nonce, aad, ct, t), Some{pt},
    open_append(key, nonce, aad, ct, t, PL.mac_length(R.poly_key(key, nonce), R.mac_data(aad, ct))),
    Equal.trans(Maybe<&2, List<&2, U32>>, R.open_tag(RS.equal(t, t), key, nonce, ct), R.open_tag(True{}, key, nonce, ct), Some{pt},
      Equal.cong(Bool, Maybe<&2, List<&2, U32>>, b => R.open_tag(b, key, nonce, ct), RS.equal(t, t), True{}, SLP.equal_refl(t)),
      Equal.cong(List<&2, U32>, Maybe<&2, List<&2, U32>>, l => Some{l}, RC.encrypt(key, 1, nonce, ct), pt, V.involution(10n, key, 1, nonce, pt))))

law open_tag_false:
  for +key: List<&2, U32>
  for +nonce: List<&2, U32>
  for +aad: List<&2, U32>
  for +ct: List<&2, U32>
  for +t: List<&2, U32>
  for ne: {t != R.tag(key, nonce, aad, ct) : List<&2, U32>}
  for +b: Bool
  for +hb: {RS.equal(t, R.tag(key, nonce, aad, ct)) == b : Bool}
  {R.open_tag(b, key, nonce, ct) == None{} : Maybe<&2, List<&2, U32>>}

def open_tag_false(key, nonce, aad, ct, t, ne, b, hb):
  match b:
    case True{}: Empty.absurd({R.open_tag(True{}, key, nonce, ct) == None{} : Maybe<&2, List<&2, U32>>}, ne(SLP.equal_sound(t, R.tag(key, nonce, aad, ct), hb)))
    case False{}: {==}

# Opening ciphertext || t fails for every 16-byte t that is not the tag of
# the ciphertext (under the key, nonce and aad given).
law forgery:
  for +key: List<&2, U32>
  for +nonce: List<&2, U32>
  for +aad: List<&2, U32>
  for +ct: List<&2, U32>
  for +t: List<&2, U32>
  for +ht: {List.length(&2, U32, t) == 16n : Nat}
  for ne: {t != R.tag(key, nonce, aad, ct) : List<&2, U32>}
  {R.open(key, nonce, aad, List.append(&2, U32, ct, t)) == None{} : Maybe<&2, List<&2, U32>>}

def forgery(key, nonce, aad, ct, t, ht, ne):
  Equal.trans(Maybe<&2, List<&2, U32>>, R.open(key, nonce, aad, List.append(&2, U32, ct, t)), R.open_split(key, nonce, aad, ct, t), None{},
    open_append(key, nonce, aad, ct, t, ht),
    open_tag_false(key, nonce, aad, ct, t, ne, RS.equal(t, R.tag(key, nonce, aad, ct)), {==}))

# The implementation's tag is the specification's, so a t other than the
# implementation's tag is rejected by the implementation.
law iforgery:
  for +key: List<&2, U32>
  for +nonce: List<&2, U32>
  for +aad: List<&2, U32>
  for +ct: List<&2, U32>
  for +t: List<&2, U32>
  for +ht: {List.length(&2, U32, t) == 16n : Nat}
  for ne: {t != I.tag(key, nonce, aad, ct) : List<&2, U32>}
  {I.open(key, nonce, aad, List.append(&2, U32, ct, t)) == None{} : Maybe<&2, List<&2, U32>>}

def iforgery(key, nonce, aad, ct, t, ht, ne):
  Equal.trans(Maybe<&2, List<&2, U32>>, I.open(key, nonce, aad, List.append(&2, U32, ct, t)), R.open(key, nonce, aad, List.append(&2, U32, ct, t)), None{},
    open_eq(key, nonce, aad, List.append(&2, U32, ct, t)),
    forgery(key, nonce, aad, ct, t, ht, e => ne(Equal.trans(List<&2, U32>, t, R.tag(key, nonce, aad, ct), I.tag(key, nonce, aad, ct), e, Equal.sym(List<&2, U32>, I.tag(key, nonce, aad, ct), R.tag(key, nonce, aad, ct), tag_eq(key, nonce, aad, ct))))))

law iroundtrip:
  for +key: List<&2, U32>
  for +nonce: List<&2, U32>
  for +aad: List<&2, U32>
  for +pt: List<&2, U32>
  {I.open(key, nonce, aad, I.seal(key, nonce, aad, pt)) == Some{pt} : Maybe<&2, List<&2, U32>>}

def iroundtrip(key, nonce, aad, pt):
  Equal.trans(Maybe<&2, List<&2, U32>>, I.open(key, nonce, aad, I.seal(key, nonce, aad, pt)), R.open(key, nonce, aad, I.seal(key, nonce, aad, pt)), Some{pt},
    open_eq(key, nonce, aad, I.seal(key, nonce, aad, pt)),
    Equal.trans(Maybe<&2, List<&2, U32>>, R.open(key, nonce, aad, I.seal(key, nonce, aad, pt)), R.open(key, nonce, aad, R.seal(key, nonce, aad, pt)), Some{pt},
      Equal.cong(List<&2, U32>, Maybe<&2, List<&2, U32>>, l => R.open(key, nonce, aad, l), I.seal(key, nonce, aad, pt), R.seal(key, nonce, aad, pt), seal_eq(key, nonce, aad, pt)),
      roundtrip(key, nonce, aad, pt)))
