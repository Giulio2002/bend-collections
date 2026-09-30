import Base
import ../../../spec/crypto/chacha.bend as R
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ./stream.bend as T

# The ChaCha20 stream cipher is an involution: encrypting the ciphertext
# with the same key, counter and nonce gives the plaintext back, for every
# byte list (every list of U32: the XOR works on whole words) and every
# number of double rounds. The specification's block-by-block encryption is
# first shown to be one XOR with the concatenated keystream ks, whose length
# covers the message; XOR with the same keystream twice cancels.

# ---------------------------------------------------------------- words

law wxor_inv:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  {Word.xor(n, Word.xor(n, a, b), b) == a : Word(n)}

def wxor_inv(n, a, b):
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}: {==}
    case 1n+p:
      match a b:
        case WCon{False{}, at} WCon{False{}, bt}: Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w}, Word.xor(p, Word.xor(p, at, bt), bt), at, wxor_inv(p, at, bt))
        case WCon{False{}, at} WCon{True{}, bt}: Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w}, Word.xor(p, Word.xor(p, at, bt), bt), at, wxor_inv(p, at, bt))
        case WCon{True{}, at} WCon{False{}, bt}: Equal.cong(Word(p), Word(1n+p), w => WCon{True{}, w}, Word.xor(p, Word.xor(p, at, bt), bt), at, wxor_inv(p, at, bt))
        case WCon{True{}, at} WCon{True{}, bt}: Equal.cong(Word(p), Word(1n+p), w => WCon{True{}, w}, Word.xor(p, Word.xor(p, at, bt), bt), at, wxor_inv(p, at, bt))

law u32_xor_inv:
  for +a: U32
  for +b: U32
  {U32.xor(U32.xor(a, b), b) == a : U32}

def u32_xor_inv(a, b):
  match a b:
    case U32{x} U32{y}:
      Equal.cong(Word(32n), U32, w => U32{w}, Word.xor(32n, Word.xor(32n, x, y), y), x, wxor_inv(32n, x, y))

# ---------------------------------------------------------------- lengths

law length_append:
  for +xs: List<&2, U32>
  for +ys: List<&2, U32>
  {List.length(&2, U32, List.append(&2, U32, xs, ys)) == Nat.add(List.length(&2, U32, xs), List.length(&2, U32, ys)) : Nat}

def length_append(xs, ys):
  match xs:
    case Nil{}: {==}
    case x <> xt:
      Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, U32, List.append(&2, U32, xt, ys)), Nat.add(List.length(&2, U32, xt), List.length(&2, U32, ys)), length_append(xt, ys))

law le_add:
  for +p: Nat
  for +l: Nat
  for +k: Nat
  for +h: {Nat.is_le(p, l) == True{} : Bool}
  {Nat.is_le(p, Nat.add(k, l)) == True{} : Bool}

def le_add(p, l, k, h):
  match k:
    case 0n: h
    case 1n+j: N.le_trans(p, Nat.add(j, l), 1n+Nat.add(j, l), le_add(p, l, j, h), N.le_succ(Nat.add(j, l)))

law xor_length:
  for +xs: List<&2, U32>
  for +ks: List<&2, U32>
  for +h: {Nat.is_le(List.length(&2, U32, xs), List.length(&2, U32, ks)) == True{} : Bool}
  {List.length(&2, U32, R.xor_bytes(xs, ks)) == List.length(&2, U32, xs) : Nat}

def xor_length(xs, ks, h):
  match xs ks:
    case Nil{} _: {==}
    case x <> xt Nil{}: Empty.absurd({0n == 1n+List.length(&2, U32, xt) : Nat}, L.false_true(h))
    case x <> xt k <> kt:
      Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, U32, R.xor_bytes(xt, kt)), List.length(&2, U32, xt), xor_length(xt, kt, h))

law xor_twice:
  for +xs: List<&2, U32>
  for +ks: List<&2, U32>
  for +h: {Nat.is_le(List.length(&2, U32, xs), List.length(&2, U32, ks)) == True{} : Bool}
  {R.xor_bytes(R.xor_bytes(xs, ks), ks) == xs : List<&2, U32>}

def xor_twice(xs, ks, h):
  match xs ks:
    case Nil{} _: {==}
    case x <> xt Nil{}: Empty.absurd({Nil{} == x <> xt : List<&2, U32>}, L.false_true(h))
    case x <> xt k <> kt:
      %Equal.sym(List<&2, U32>, R.xor_bytes(R.xor_bytes(xt, kt), kt), xt, xor_twice(xt, kt, h)) :
        {U32.xor(U32.xor(x, k), k) <> _ == x <> xt : List<&2, U32>}
      %Equal.sym(U32, U32.xor(U32.xor(x, k), k), x, u32_xor_inv(x, k)) :
        {_ <> xt == x <> xt : List<&2, U32>}
      {==}

# ---------------------------------------------------------------- one keystream

# The keystream of fuel blocks from counter c.
def ks(fuel: Nat, +r: Nat, +kb: List<&2, U32>, +c: U32, +nb: List<&2, U32>) -> List<&2, U32>:
  match fuel:
    case 0n: Nil{}
    case 1n+p: List.append(&2, U32, R.block_rounds(r, kb, c, nb), ks(p, r, kb, U32.add(c, 1), nb))

law ks_length:
  for +fuel: Nat
  for +r: Nat
  for +kb: List<&2, U32>
  for +c: U32
  for +nb: List<&2, U32>
  {Nat.is_le(fuel, List.length(&2, U32, ks(fuel, r, kb, c, nb))) == True{} : Bool}

def ks_length(fuel, r, kb, c, nb):
  match fuel:
    case 0n: {==}
    case 1n+p:
      +c1 = U32.add(c, 1)
      %Equal.sym(Nat, List.length(&2, U32, List.append(&2, U32, R.block_rounds(r, kb, c, nb), ks(p, r, kb, c1, nb))), Nat.add(List.length(&2, U32, R.block_rounds(r, kb, c, nb)), List.length(&2, U32, ks(p, r, kb, c1, nb))), length_append(R.block_rounds(r, kb, c, nb), ks(p, r, kb, c1, nb))) :
        {Nat.is_le(1n+p, _) == True{} : Bool}
      %Equal.sym(Nat, List.length(&2, U32, R.block_rounds(r, kb, c, nb)), 64n, T.block_length(r, kb, c, nb)) :
        {Nat.is_le(1n+p, Nat.add(_, List.length(&2, U32, ks(p, r, kb, c1, nb)))) == True{} : Bool}
      le_add(p, List.length(&2, U32, ks(p, r, kb, c1, nb)), 63n, ks_length(p, r, kb, c1, nb))

law xor_append:
  for +bs: List<&2, U32>
  for +xs: List<&2, U32>
  for +k: List<&2, U32>
  {R.xor_bytes(xs, List.append(&2, U32, bs, k)) == List.append(&2, U32, R.xor_bytes(R.prefix(List.length(&2, U32, bs), xs), bs), R.xor_bytes(R.suffix(List.length(&2, U32, bs), xs), k)) : List<&2, U32>}

def xor_append(bs, xs, k):
  match bs xs:
    case Nil{} _: {==}
    case b <> bt Nil{}: {==}
    case b <> bt x <> xt:
      %xor_append(bt, xt, k) :
        {U32.xor(x, b) <> R.xor_bytes(xt, List.append(&2, U32, bt, k)) == U32.xor(x, b) <> _ : List<&2, U32>}
      {==}

law enc_ks:
  for +fuel: Nat
  for +xs: List<&2, U32>
  for +r: Nat
  for +kb: List<&2, U32>
  for +c: U32
  for +nb: List<&2, U32>
  {R.encrypt_blocks(R.blocks(fuel, xs), r, kb, c, nb) == R.xor_bytes(xs, ks(fuel, r, kb, c, nb)) : List<&2, U32>}

def enc_ks(fuel, xs, r, kb, c, nb):
  match fuel xs:
    case 0n Nil{}: {==}
    case 0n x <> xt: {==}
    case 1n+p Nil{}: {==}
    case 1n+p x <> xt:
      +c1 = U32.add(c, 1)
      +B = R.block_rounds(r, kb, c, nb)
      +K = ks(p, r, kb, c1, nb)
      +X = {x <> xt : List<&2, U32>}
      +left = List.append(&2, U32, R.xor_bytes(R.prefix(64n, X), B), R.xor_bytes(R.suffix(64n, X), K))
      Equal.trans(List<&2, U32>,
        List.append(&2, U32, R.xor_bytes(R.prefix(64n, X), B), R.encrypt_blocks(R.blocks(p, R.suffix(64n, X)), r, kb, c1, nb)),
        left,
        R.xor_bytes(X, List.append(&2, U32, B, K)),
        Equal.cong(List<&2, U32>, List<&2, U32>, l => List.append(&2, U32, R.xor_bytes(R.prefix(64n, X), B), l),
          R.encrypt_blocks(R.blocks(p, R.suffix(64n, X)), r, kb, c1, nb), R.xor_bytes(R.suffix(64n, X), K), enc_ks(p, R.suffix(64n, X), r, kb, c1, nb)),
        Equal.sym(List<&2, U32>, R.xor_bytes(X, List.append(&2, U32, B, K)), left,
          Equal.trans(List<&2, U32>, R.xor_bytes(X, List.append(&2, U32, B, K)),
            List.append(&2, U32, R.xor_bytes(R.prefix(List.length(&2, U32, B), X), B), R.xor_bytes(R.suffix(List.length(&2, U32, B), X), K)),
            left,
            xor_append(B, X, K),
            Equal.cong(Nat, List<&2, U32>, n => List.append(&2, U32, R.xor_bytes(R.prefix(n, X), B), R.xor_bytes(R.suffix(n, X), K)),
              List.length(&2, U32, B), 64n, T.block_length(r, kb, c, nb)))))

# ---------------------------------------------------------------- the involution

law encrypt_xor:
  for +r: Nat
  for +kb: List<&2, U32>
  for +c: U32
  for +nb: List<&2, U32>
  for +pt: List<&2, U32>
  {R.encrypt_rounds(r, kb, c, nb, pt) == R.xor_bytes(pt, ks(List.length(&2, U32, pt), r, kb, c, nb)) : List<&2, U32>}

def encrypt_xor(r, kb, c, nb, pt):
  enc_ks(List.length(&2, U32, pt), pt, r, kb, c, nb)

# The ciphertext is as long as the plaintext.
law encrypt_length:
  for +r: Nat
  for +kb: List<&2, U32>
  for +c: U32
  for +nb: List<&2, U32>
  for +pt: List<&2, U32>
  {List.length(&2, U32, R.encrypt_rounds(r, kb, c, nb, pt)) == List.length(&2, U32, pt) : Nat}

def encrypt_length(r, kb, c, nb, pt):
  +K = ks(List.length(&2, U32, pt), r, kb, c, nb)
  %Equal.sym(List<&2, U32>, R.encrypt_rounds(r, kb, c, nb, pt), R.xor_bytes(pt, K), encrypt_xor(r, kb, c, nb, pt)) :
    {List.length(&2, U32, _) == List.length(&2, U32, pt) : Nat}
  xor_length(pt, K, ks_length(List.length(&2, U32, pt), r, kb, c, nb))

law involution:
  for +r: Nat
  for +kb: List<&2, U32>
  for +c: U32
  for +nb: List<&2, U32>
  for +pt: List<&2, U32>
  {R.encrypt_rounds(r, kb, c, nb, R.encrypt_rounds(r, kb, c, nb, pt)) == pt : List<&2, U32>}

def involution(r, kb, c, nb, pt):
  +ct = R.encrypt_rounds(r, kb, c, nb, pt)
  +K = ks(List.length(&2, U32, pt), r, kb, c, nb)
  Equal.trans(List<&2, U32>, R.encrypt_rounds(r, kb, c, nb, ct), R.xor_bytes(ct, ks(List.length(&2, U32, ct), r, kb, c, nb)), pt,
    encrypt_xor(r, kb, c, nb, ct),
    Equal.trans(List<&2, U32>, R.xor_bytes(ct, ks(List.length(&2, U32, ct), r, kb, c, nb)), R.xor_bytes(ct, K), pt,
      Equal.cong(Nat, List<&2, U32>, n => R.xor_bytes(ct, ks(n, r, kb, c, nb)), List.length(&2, U32, ct), List.length(&2, U32, pt), encrypt_length(r, kb, c, nb, pt)),
      Equal.trans(List<&2, U32>, R.xor_bytes(ct, K), R.xor_bytes(R.xor_bytes(pt, K), K), pt,
        Equal.cong(List<&2, U32>, List<&2, U32>, l => R.xor_bytes(l, K), ct, R.xor_bytes(pt, K), encrypt_xor(r, kb, c, nb, pt)),
        xor_twice(pt, K, ks_length(List.length(&2, U32, pt), r, kb, c, nb)))))
