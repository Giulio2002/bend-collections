import Base
import ../../../src/crypto/chacha/chacha20.bend as I
import ../../../spec/crypto/chacha.bend as R
import ./laws.bend as Laws
import ./stream.bend as T
import ./xchacha.bend as X
import ./involution.bend as V

# Entry point: `bend proofs/crypto/chacha/proof.bend` checks every clause of
# laws.bend (the core refinement is proofs/crypto/chacha/core.bend, the
# byte-level stream stream.bend, HChaCha20/XChaCha20 xchacha.bend, the
# involution involution.bend).

def Laws.block_rounds(r, key, counter, nonce):
  T.block_rounds_correct(r, key, counter, nonce)

def Laws.encrypt_rounds(r, key, counter, nonce, plaintext):
  T.encrypt_correct(r, key, counter, nonce, plaintext)

def Laws.hchacha_rounds(r, key, nonce):
  X.hchacha_rounds_correct(r, key, nonce)

def Laws.hchacha20(key, nonce):
  X.hchacha20_correct(key, nonce)

def Laws.xencrypt(key, counter, nonce, plaintext):
  X.xencrypt_correct(key, counter, nonce, plaintext)

# ---- checked API

law when_true:
  for +ok: Bool
  for +x: List<&2, U32>
  for +h: {ok == True{} : Bool}
  {I.when(ok, x) == Some{x} : Maybe<&2, List<&2, U32>>}

def when_true(ok, x, h):
  %Equal.sym(Bool, ok, True{}, h) : {I.when(_, x) == Some{x} : Maybe<&2, List<&2, U32>>}
  {==}

law when_false:
  for +ok: Bool
  for +x: List<&2, U32>
  for +h: {ok == False{} : Bool}
  {I.when(ok, x) == None{} : Maybe<&2, List<&2, U32>>}

def when_false(ok, x, h):
  %Equal.sym(Bool, ok, False{}, h) : {I.when(_, x) == None{} : Maybe<&2, List<&2, U32>>}
  {==}

law valid_true:
  for +key: List<&2, U32>
  for +nonce: List<&2, U32>
  for +n: Nat
  for +hk: {List.length(&2, U32, key) == 32n : Nat}
  for +hn: {List.length(&2, U32, nonce) == n : Nat}
  {I.valid(key, nonce, n) == True{} : Bool}

def is_eq_self(+n: Nat) -> {Nat.is_eq(n, n) == True{} : Bool}:
  match n:
    case 0n: {==}
    case 1n+p: is_eq_self(p)

def valid_true(key, nonce, n, hk, hn):
  %Equal.sym(Nat, List.length(&2, U32, key), 32n, hk) :
    {Bool.and(Nat.is_eq(_, 32n), Nat.is_eq(List.length(&2, U32, nonce), n)) == True{} : Bool}
  %Equal.sym(Nat, List.length(&2, U32, nonce), n, hn) :
    {Bool.and(Nat.is_eq(32n, 32n), Nat.is_eq(_, n)) == True{} : Bool}
  is_eq_self(n)

def Laws.chacha20_block.valid(key, counter, nonce, hk, hn):
  Equal.trans(Maybe<&2, List<&2, U32>>, I.chacha20_block(key, counter, nonce), Some{I.block_rounds(10n, key, counter, nonce)}, Some{R.block(key, counter, nonce)},
    when_true(I.valid(key, nonce, 12n), I.block_rounds(10n, key, counter, nonce), valid_true(key, nonce, 12n, hk, hn)),
    Equal.cong(List<&2, U32>, Maybe<&2, List<&2, U32>>, l => Some{l}, I.block_rounds(10n, key, counter, nonce), R.block(key, counter, nonce), T.block_rounds_correct(10n, key, counter, nonce)))

def Laws.chacha20_block.invalid(key, counter, nonce, h):
  when_false(I.valid(key, nonce, 12n), I.block_rounds(10n, key, counter, nonce), h)

def Laws.chacha20.valid(key, counter, nonce, plaintext, hk, hn):
  Equal.trans(Maybe<&2, List<&2, U32>>, I.chacha20(key, counter, nonce, plaintext), Some{I.encrypt_rounds(10n, key, counter, nonce, plaintext)}, Some{R.encrypt(key, counter, nonce, plaintext)},
    when_true(I.valid(key, nonce, 12n), I.encrypt_rounds(10n, key, counter, nonce, plaintext), valid_true(key, nonce, 12n, hk, hn)),
    Equal.cong(List<&2, U32>, Maybe<&2, List<&2, U32>>, l => Some{l}, I.encrypt_rounds(10n, key, counter, nonce, plaintext), R.encrypt(key, counter, nonce, plaintext), T.encrypt_correct(10n, key, counter, nonce, plaintext)))

def Laws.chacha20.invalid(key, counter, nonce, plaintext, h):
  when_false(I.valid(key, nonce, 12n), I.encrypt_rounds(10n, key, counter, nonce, plaintext), h)

def Laws.hchacha20.valid(key, nonce, hk, hn):
  Equal.trans(Maybe<&2, List<&2, U32>>, I.hchacha20(key, nonce), Some{I.hchacha20_unchecked(key, nonce)}, Some{R.hchacha20(key, nonce)},
    when_true(I.valid(key, nonce, 16n), I.hchacha20_unchecked(key, nonce), valid_true(key, nonce, 16n, hk, hn)),
    Equal.cong(List<&2, U32>, Maybe<&2, List<&2, U32>>, l => Some{l}, I.hchacha20_unchecked(key, nonce), R.hchacha20(key, nonce), X.hchacha20_correct(key, nonce)))

def Laws.hchacha20.invalid(key, nonce, h):
  when_false(I.valid(key, nonce, 16n), I.hchacha20_unchecked(key, nonce), h)

def Laws.xchacha20.valid(key, counter, nonce, plaintext, hk, hn):
  Equal.trans(Maybe<&2, List<&2, U32>>, I.xchacha20(key, counter, nonce, plaintext), Some{I.xencrypt_unchecked(key, counter, nonce, plaintext)}, Some{R.xencrypt(key, counter, nonce, plaintext)},
    when_true(I.valid(key, nonce, 24n), I.xencrypt_unchecked(key, counter, nonce, plaintext), valid_true(key, nonce, 24n, hk, hn)),
    Equal.cong(List<&2, U32>, Maybe<&2, List<&2, U32>>, l => Some{l}, I.xencrypt_unchecked(key, counter, nonce, plaintext), R.xencrypt(key, counter, nonce, plaintext), X.xencrypt_correct(key, counter, nonce, plaintext)))

def Laws.xchacha20.invalid(key, counter, nonce, plaintext, h):
  when_false(I.valid(key, nonce, 24n), I.xencrypt_unchecked(key, counter, nonce, plaintext), h)

# ---- properties

def Laws.involution(r, key, counter, nonce, plaintext):
  +ct = I.encrypt_rounds(r, key, counter, nonce, plaintext)
  +sct = R.encrypt_rounds(r, key, counter, nonce, plaintext)
  Equal.trans(List<&2, U32>, I.encrypt_rounds(r, key, counter, nonce, ct), R.encrypt_rounds(r, key, counter, nonce, ct), plaintext,
    T.encrypt_correct(r, key, counter, nonce, ct),
    Equal.trans(List<&2, U32>, R.encrypt_rounds(r, key, counter, nonce, ct), R.encrypt_rounds(r, key, counter, nonce, sct), plaintext,
      Equal.cong(List<&2, U32>, List<&2, U32>, l => R.encrypt_rounds(r, key, counter, nonce, l), ct, sct, T.encrypt_correct(r, key, counter, nonce, plaintext)),
      V.involution(r, key, counter, nonce, plaintext)))

def Laws.xinvolution(key, counter, nonce, plaintext):
  +ct = I.xencrypt_unchecked(key, counter, nonce, plaintext)
  +sct = R.xencrypt(key, counter, nonce, plaintext)
  Equal.trans(List<&2, U32>, I.xencrypt_unchecked(key, counter, nonce, ct), R.xencrypt(key, counter, nonce, ct), plaintext,
    X.xencrypt_correct(key, counter, nonce, ct),
    Equal.trans(List<&2, U32>, R.xencrypt(key, counter, nonce, ct), R.xencrypt(key, counter, nonce, sct), plaintext,
      Equal.cong(List<&2, U32>, List<&2, U32>, l => R.xencrypt(key, counter, nonce, l), ct, sct, X.xencrypt_correct(key, counter, nonce, plaintext)),
      V.involution(10n, R.xsubkey(key, nonce), counter, R.xnonce(nonce), plaintext)))

def Laws.encrypt_length(r, key, counter, nonce, plaintext):
  %Equal.sym(List<&2, U32>, I.encrypt_rounds(r, key, counter, nonce, plaintext), R.encrypt_rounds(r, key, counter, nonce, plaintext), T.encrypt_correct(r, key, counter, nonce, plaintext)) :
    {List.length(&2, U32, _) == List.length(&2, U32, plaintext) : Nat}
  V.encrypt_length(r, key, counter, nonce, plaintext)

def Laws.block_length(r, key, counter, nonce):
  T.block_length(r, key, counter, nonce)

def Laws.hchacha_length(r, key, nonce):
  match key:
    case Nil{}: {==}
    case b <> rest: {==}
