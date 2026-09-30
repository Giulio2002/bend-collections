import Base
import ../../../src/crypto/chacha/core.bend as C
import ../../../src/crypto/chacha/chacha20.bend as I
import ../../../spec/crypto/chacha.bend as R
import ../../lib/nat.bend as N
import ./core.bend as K

# The byte-level ChaCha20 / HChaCha20 / XChaCha20 of src/crypto/chacha/
# against spec/crypto/chacha.bend, for every key, nonce, counter and byte
# list, and every number of double rounds.

# ---------------------------------------------------------------- bytes to words

law words_eq:
  for +xs: List<&2, U32>
  {I.words(xs) == R.words(xs) : List<&2, U32>}

def words_eq(xs):
  match xs:
    case Nil{}: {==}
    case b0 <> Nil{}: {==}
    case b0 <> b1 <> Nil{}: {==}
    case b0 <> b1 <> b2 <> Nil{}: {==}
    case b0 <> b1 <> b2 <> b3 <> rest:
      %Equal.sym(List<&2, U32>, I.words(rest), R.words(rest), words_eq(rest)) :
        {I.word(b0, b1, b2, b3) <> _ == R.word(b0, b1, b2, b3) <> R.words(rest) : List<&2, U32>}
      {==}

law key_eq:
  for +ws: List<&2, U32>
  {I.key_words(ws) == I.K{R.get(ws, 0n), R.get(ws, 1n), R.get(ws, 2n), R.get(ws, 3n), R.get(ws, 4n), R.get(ws, 5n), R.get(ws, 6n), R.get(ws, 7n)} : I.Key}

def key_eq(ws):
  match ws:
    case Nil{}: {==}
    case w0 <> Nil{}: {==}
    case w0 <> w1 <> Nil{}: {==}
    case w0 <> w1 <> w2 <> Nil{}: {==}
    case w0 <> w1 <> w2 <> w3 <> Nil{}: {==}
    case w0 <> w1 <> w2 <> w3 <> w4 <> Nil{}: {==}
    case w0 <> w1 <> w2 <> w3 <> w4 <> w5 <> Nil{}: {==}
    case w0 <> w1 <> w2 <> w3 <> w4 <> w5 <> w6 <> Nil{}: {==}
    case w0 <> w1 <> w2 <> w3 <> w4 <> w5 <> w6 <> w7 <> rest: {==}

law nonce_eq:
  for +ws: List<&2, U32>
  {I.nonce_words(ws) == I.N{R.get(ws, 0n), R.get(ws, 1n), R.get(ws, 2n)} : I.Nonce}

def nonce_eq(ws):
  match ws:
    case Nil{}: {==}
    case w0 <> Nil{}: {==}
    case w0 <> w1 <> Nil{}: {==}
    case w0 <> w1 <> w2 <> rest: {==}

# The four HChaCha20 nonce words.
law hnonce_eq:
  for +ws: List<&2, U32>
  {[I.at(ws, 0n), I.at(ws, 1n), I.at(ws, 2n), I.at(ws, 3n)] == [R.get(ws, 0n), R.get(ws, 1n), R.get(ws, 2n), R.get(ws, 3n)] : List<&2, U32>}

def hnonce_eq(ws):
  match ws:
    case Nil{}: {==}
    case w0 <> Nil{}: {==}
    case w0 <> w1 <> Nil{}: {==}
    case w0 <> w1 <> w2 <> Nil{}: {==}
    case w0 <> w1 <> w2 <> w3 <> rest: {==}

# ---------------------------------------------------------------- states

law state_eq:
  for +ks: List<&2, U32>
  for +c: U32
  for +ns: List<&2, U32>
  {K.vec(I.state(I.key_words(ks), c, I.nonce_words(ns))) == R.state(ks, c, ns) : List<&2, U32>}

def state_eq(ks, c, ns):
  %Equal.sym(I.Key, I.key_words(ks), I.K{R.get(ks, 0n), R.get(ks, 1n), R.get(ks, 2n), R.get(ks, 3n), R.get(ks, 4n), R.get(ks, 5n), R.get(ks, 6n), R.get(ks, 7n)}, key_eq(ks)) :
    {K.vec(I.state(_, c, I.nonce_words(ns))) == R.state(ks, c, ns) : List<&2, U32>}
  %Equal.sym(I.Nonce, I.nonce_words(ns), I.N{R.get(ns, 0n), R.get(ns, 1n), R.get(ns, 2n)}, nonce_eq(ns)) :
    {K.vec(I.state(I.K{R.get(ks, 0n), R.get(ks, 1n), R.get(ks, 2n), R.get(ks, 3n), R.get(ks, 4n), R.get(ks, 5n), R.get(ks, 6n), R.get(ks, 7n)}, c, _)) == R.state(ks, c, ns) : List<&2, U32>}
  {==}

law hstate_eq:
  for +ks: List<&2, U32>
  for +ns: List<&2, U32>
  {K.vec(I.hstate(I.key_words(ks), ns)) == R.hstate(ks, ns) : List<&2, U32>}

def hsl(+k0: U32, +k1: U32, +k2: U32, +k3: U32, +k4: U32, +k5: U32, +k6: U32, +k7: U32, l: List<&2, U32>) -> List<&2, U32>:
  match l:
    case n0 <> n1 <> n2 <> n3 <> rest: R.hstate([k0, k1, k2, k3, k4, k5, k6, k7], [n0, n1, n2, n3])
    case _: Nil{}

def hstate_eq(ks, ns):
  %Equal.sym(I.Key, I.key_words(ks), I.K{R.get(ks, 0n), R.get(ks, 1n), R.get(ks, 2n), R.get(ks, 3n), R.get(ks, 4n), R.get(ks, 5n), R.get(ks, 6n), R.get(ks, 7n)}, key_eq(ks)) :
    {K.vec(I.hstate(_, ns)) == R.hstate(ks, ns) : List<&2, U32>}
  Equal.trans(List<&2, U32>,
    K.vec(I.hstate(I.K{R.get(ks, 0n), R.get(ks, 1n), R.get(ks, 2n), R.get(ks, 3n), R.get(ks, 4n), R.get(ks, 5n), R.get(ks, 6n), R.get(ks, 7n)}, ns)),
    hsl(R.get(ks, 0n), R.get(ks, 1n), R.get(ks, 2n), R.get(ks, 3n), R.get(ks, 4n), R.get(ks, 5n), R.get(ks, 6n), R.get(ks, 7n), [I.at(ns, 0n), I.at(ns, 1n), I.at(ns, 2n), I.at(ns, 3n)]),
    R.hstate(ks, ns),
    {==},
    Equal.cong(List<&2, U32>, List<&2, U32>, l => hsl(R.get(ks, 0n), R.get(ks, 1n), R.get(ks, 2n), R.get(ks, 3n), R.get(ks, 4n), R.get(ks, 5n), R.get(ks, 6n), R.get(ks, 7n), l),
      [I.at(ns, 0n), I.at(ns, 1n), I.at(ns, 2n), I.at(ns, 3n)], [R.get(ns, 0n), R.get(ns, 1n), R.get(ns, 2n), R.get(ns, 3n)], hnonce_eq(ns)))

# ---------------------------------------------------------------- block

law body_correct:
  for +r: Nat
  for +kb: List<&2, U32>
  for +c: U32
  for +nb: List<&2, U32>
  {I.keystream(r, I.key(kb), c, I.nonce(nb)) == R.block_body(r, kb, c, nb) : List<&2, U32>}

def sblock(+r: Nat, +s: List<&2, U32>) -> List<&2, U32>:
  R.serialize(R.add_words(s, R.inner_blocks(r, s)))

def body_correct(r, kb, c, nb):
  +S = I.state(I.key_words(I.words(kb)), c, I.nonce_words(I.words(nb)))
  Equal.trans(List<&2, U32>, C.bytes(C.block(r, S)), sblock(r, K.vec(S)), R.block_body(r, kb, c, nb),
    K.block_correct(r, S),
    Equal.trans(List<&2, U32>, sblock(r, K.vec(S)), sblock(r, R.state(I.words(kb), c, I.words(nb))), R.block_body(r, kb, c, nb),
      Equal.cong(List<&2, U32>, List<&2, U32>, l => sblock(r, l), K.vec(S), R.state(I.words(kb), c, I.words(nb)), state_eq(I.words(kb), c, I.words(nb))),
      Equal.trans(List<&2, U32>, sblock(r, R.state(I.words(kb), c, I.words(nb))), sblock(r, R.state(R.words(kb), c, I.words(nb))), R.block_body(r, kb, c, nb),
        Equal.cong(List<&2, U32>, List<&2, U32>, l => sblock(r, R.state(l, c, I.words(nb))), I.words(kb), R.words(kb), words_eq(kb)),
        Equal.cong(List<&2, U32>, List<&2, U32>, l => sblock(r, R.state(R.words(kb), c, l)), I.words(nb), R.words(nb), words_eq(nb)))))

law keystream_correct:
  for +r: Nat
  for +kb: List<&2, U32>
  for +c: U32
  for +nb: List<&2, U32>
  {I.keystream(r, I.key(kb), c, I.nonce(nb)) == R.block_rounds(r, kb, c, nb) : List<&2, U32>}

def keystream_correct(r, kb, c, nb):
  match kb:
    case Nil{}: body_correct(r, Nil{}, c, nb)
    case b <> rest: body_correct(r, b <> rest, c, nb)

law block_rounds_correct:
  for +r: Nat
  for +kb: List<&2, U32>
  for +c: U32
  for +nb: List<&2, U32>
  {I.block_rounds(r, kb, c, nb) == R.block_rounds(r, kb, c, nb) : List<&2, U32>}

def block_rounds_correct(r, kb, c, nb):
  match kb:
    case Nil{}: body_correct(r, Nil{}, c, nb)
    case b <> rest: body_correct(r, b <> rest, c, nb)

# 64 keystream bytes.
law bytes_length:
  for +s: C.State
  {List.length(&2, U32, C.bytes(s)) == 64n : Nat}

def bytes_length(s):
  match s:
    case C.S{a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15}: {==}

law block_length:
  for +r: Nat
  for +kb: List<&2, U32>
  for +c: U32
  for +nb: List<&2, U32>
  {List.length(&2, U32, R.block_rounds(r, kb, c, nb)) == 64n : Nat}

def block_length(r, kb, c, nb):
  %keystream_correct(r, kb, c, nb) : {List.length(&2, U32, _) == 64n : Nat}
  bytes_length(C.block(r, I.state(I.key(kb), c, I.nonce(nb))))

# ---------------------------------------------------------------- stream

law xor_front_eq:
  for +ks: List<&2, U32>
  for +xs: List<&2, U32>
  {I.xor_front(ks, xs) == R.xor_bytes(R.prefix(List.length(&2, U32, ks), xs), ks) : List<&2, U32>}

def xor_front_eq(ks, xs):
  match ks xs:
    case Nil{} _: {==}
    case k <> kt Nil{}: {==}
    case k <> kt x <> xt:
      %Equal.sym(List<&2, U32>, I.xor_front(kt, xt), R.xor_bytes(R.prefix(List.length(&2, U32, kt), xt), kt), xor_front_eq(kt, xt)) :
        {U32.xor(x, k) <> _ == U32.xor(x, k) <> R.xor_bytes(R.prefix(List.length(&2, U32, kt), xt), kt) : List<&2, U32>}
      {==}

law skip_eq:
  for +n: Nat
  for +xs: List<&2, U32>
  {I.skip(n, xs) == R.suffix(n, xs) : List<&2, U32>}

def skip_eq(n, xs):
  match n xs:
    case 0n _: {==}
    case 1n+p Nil{}: {==}
    case 1n+p x <> rest: skip_eq(p, rest)

law take_eq:
  for +n: Nat
  for +xs: List<&2, U32>
  {I.take(n, xs) == R.prefix(n, xs) : List<&2, U32>}

def take_eq(n, xs):
  match n xs:
    case 0n _: {==}
    case 1n+p Nil{}: {==}
    case 1n+p x <> rest:
      %Equal.sym(List<&2, U32>, I.take(p, rest), R.prefix(p, rest), take_eq(p, rest)) : {x <> _ == x <> R.prefix(p, rest) : List<&2, U32>}
      {==}

# One block of the stream: the XORed front is the spec's.
law front_correct:
  for +r: Nat
  for +kb: List<&2, U32>
  for +c: U32
  for +nb: List<&2, U32>
  for +xs: List<&2, U32>
  {I.xor_front(I.keystream(r, I.key(kb), c, I.nonce(nb)), xs) == R.xor_bytes(R.prefix(64n, xs), R.block_rounds(r, kb, c, nb)) : List<&2, U32>}

def front_correct(r, kb, c, nb, xs):
  +ks = I.keystream(r, I.key(kb), c, I.nonce(nb))
  Equal.trans(List<&2, U32>, I.xor_front(ks, xs), R.xor_bytes(R.prefix(List.length(&2, U32, ks), xs), ks), R.xor_bytes(R.prefix(64n, xs), R.block_rounds(r, kb, c, nb)),
    xor_front_eq(ks, xs),
    Equal.trans(List<&2, U32>, R.xor_bytes(R.prefix(List.length(&2, U32, ks), xs), ks), R.xor_bytes(R.prefix(64n, xs), ks), R.xor_bytes(R.prefix(64n, xs), R.block_rounds(r, kb, c, nb)),
      Equal.cong(Nat, List<&2, U32>, n => R.xor_bytes(R.prefix(n, xs), ks), List.length(&2, U32, ks), 64n, bytes_length(C.block(r, I.state(I.key(kb), c, I.nonce(nb))))),
      Equal.cong(List<&2, U32>, List<&2, U32>, l => R.xor_bytes(R.prefix(64n, xs), l), ks, R.block_rounds(r, kb, c, nb), keystream_correct(r, kb, c, nb))))

law stream_correct:
  for +fuel: Nat
  for +xs: List<&2, U32>
  for +r: Nat
  for +kb: List<&2, U32>
  for +c: U32
  for +nb: List<&2, U32>
  {I.stream(fuel, xs, r, I.key(kb), c, I.nonce(nb)) == R.encrypt_blocks(R.blocks(fuel, xs), r, kb, c, nb) : List<&2, U32>}

def stream_correct(fuel, xs, r, kb, c, nb):
  match fuel xs:
    case 0n _: {==}
    case 1n+p Nil{}: {==}
    case 1n+p x <> xt:
      +c1 = U32.add(c, 1)
      +ih = stream_correct(p, R.suffix(64n, x <> xt), r, kb, c1, nb)
      +fr = front_correct(r, kb, c, nb, x <> xt)
      +sk = skip_eq(64n, x <> xt)
      %Equal.sym(List<&2, U32>, I.skip(64n, x <> xt), R.suffix(64n, x <> xt), sk) :
        {List.append(&2, U32, I.xor_front(I.keystream(r, I.key(kb), c, I.nonce(nb)), x <> xt), I.stream(p, _, r, I.key(kb), c1, I.nonce(nb))) == R.encrypt_blocks(R.blocks(1n+p, x <> xt), r, kb, c, nb) : List<&2, U32>}
      %Equal.sym(List<&2, U32>, I.stream(p, R.suffix(64n, x <> xt), r, I.key(kb), c1, I.nonce(nb)), R.encrypt_blocks(R.blocks(p, R.suffix(64n, x <> xt)), r, kb, c1, nb), ih) :
        {List.append(&2, U32, I.xor_front(I.keystream(r, I.key(kb), c, I.nonce(nb)), x <> xt), _) == R.encrypt_blocks(R.blocks(1n+p, x <> xt), r, kb, c, nb) : List<&2, U32>}
      %Equal.sym(List<&2, U32>, I.xor_front(I.keystream(r, I.key(kb), c, I.nonce(nb)), x <> xt), R.xor_bytes(R.prefix(64n, x <> xt), R.block_rounds(r, kb, c, nb)), fr) :
        {List.append(&2, U32, _, R.encrypt_blocks(R.blocks(p, R.suffix(64n, x <> xt)), r, kb, c1, nb)) == R.encrypt_blocks(R.blocks(1n+p, x <> xt), r, kb, c, nb) : List<&2, U32>}
      {==}

# The one-pass stream of the implementation is the append/skip stream.
law stream_nil:
  for +fuel: Nat
  for +r: Nat
  for +k: I.Key
  for +c: U32
  for +n: I.Nonce
  {I.stream(fuel, [], r, k, c, n) == [] : List<&2, U32>}

def stream_nil(fuel, r, k, c, n):
  match fuel:
    case 0n: {==}
    case 1n+p: {==}

law xstream_eq:
  for fuel: Nat
  for ks: List<&2, U32>
  for +xs: List<&2, U32>
  for +r: Nat
  for +k: I.Key
  for +c: U32
  for +n: I.Nonce
  {I.xstream(fuel, ks, xs, r, k, c, n) == List.append(&2, U32, I.xor_front(ks, xs), I.stream(fuel, I.skip(List.length(&2, U32, ks), xs), r, k, c, n)) : List<&2, U32>}

def xstream_eq(fuel, ks, xs, r, k, c, n):
  match fuel ks xs:
    case _ y <> kt x <> xt:
      %Equal.sym(List<&2, U32>, I.xstream(fuel, kt, xt, r, k, c, n), List.append(&2, U32, I.xor_front(kt, xt), I.stream(fuel, I.skip(List.length(&2, U32, kt), xt), r, k, c, n)), xstream_eq(fuel, kt, xt, r, k, c, n)) :
        {U32.xor(x, y) <> _ == U32.xor(x, y) <> List.append(&2, U32, I.xor_front(kt, xt), I.stream(fuel, I.skip(List.length(&2, U32, kt), xt), r, k, c, n)) : List<&2, U32>}
      {==}
    case 1n+p Nil{} x <> xt:
      +ks2 = I.keystream(r, k, c, n)
      +c1 = U32.add(c, 1)
      %Equal.sym(List<&2, U32>, I.xstream(p, ks2, x <> xt, r, k, c1, n), List.append(&2, U32, I.xor_front(ks2, x <> xt), I.stream(p, I.skip(List.length(&2, U32, ks2), x <> xt), r, k, c1, n)), xstream_eq(p, ks2, x <> xt, r, k, c1, n)) :
        {_ == List.append(&2, U32, I.xor_front(ks2, x <> xt), I.stream(p, I.skip(64n, x <> xt), r, k, c1, n)) : List<&2, U32>}
      %Equal.sym(Nat, List.length(&2, U32, ks2), 64n, bytes_length(C.block(r, I.state(k, c, n)))) :
        {List.append(&2, U32, I.xor_front(ks2, x <> xt), I.stream(p, I.skip(_, x <> xt), r, k, c1, n)) == List.append(&2, U32, I.xor_front(ks2, x <> xt), I.stream(p, I.skip(64n, x <> xt), r, k, c1, n)) : List<&2, U32>}
      {==}
    case 1n+p Nil{} Nil{}: {==}
    case 0n Nil{} _: {==}
    case _ y <> kt Nil{}:
      Equal.sym(List<&2, U32>, I.stream(fuel, [], r, k, c, n), [], stream_nil(fuel, r, k, c, n))

law encrypt_correct:
  for +r: Nat
  for +kb: List<&2, U32>
  for +c: U32
  for +nb: List<&2, U32>
  for +pt: List<&2, U32>
  {I.encrypt_rounds(r, kb, c, nb, pt) == R.encrypt_rounds(r, kb, c, nb, pt) : List<&2, U32>}

def encrypt_correct(r, kb, c, nb, pt):
  +f = List.length(&2, U32, pt)
  Equal.trans(List<&2, U32>, I.xstream(f, [], pt, r, I.key(kb), c, I.nonce(nb)), I.stream(f, pt, r, I.key(kb), c, I.nonce(nb)), R.encrypt_rounds(r, kb, c, nb, pt),
    xstream_eq(f, [], pt, r, I.key(kb), c, I.nonce(nb)),
    stream_correct(f, pt, r, kb, c, nb))

