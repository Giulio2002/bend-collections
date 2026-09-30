import Base
import ../../../src/crypto/kdf.bend as KDF
import ../../../src/crypto/mac.bend as MAC
import ../../../spec/crypto/hkdf.bend as Spec
import ../../../spec/crypto/hmac.bend as HMAC
import ../mac/hmac.bend as MacP
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N

# HKDF-SHA256: the implementation src/crypto/kdf.bend equals the RFC 5869
# specification spec/crypto/hkdf.bend for every salt, key material, info
# and length (the statement of HACL*'s Hacl.HKDF against Spec.HKDF); the
# output has the requested length and a shorter output is a prefix of a
# longer one. HMAC enters only through MacP.sign_correct.

# ---- lists ----

def take_zero(+xs: List<&2, U32>) -> {List.take(&2, U32, xs, 0n) == Nil{} : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case x <> rest:
      {==}

def take_append_short(+xs: List<&2, U32>, +ys: List<&2, U32>, +n: Nat, +h: {Nat.is_le(n, List.length(&2, U32, xs)) == True{} : Bool}) -> {List.take(&2, U32, List.append(&2, U32, xs, ys), n) == List.take(&2, U32, xs, n) : List<&2, U32>}:
  match xs n:
    case Nil{} 0n:
      take_zero(ys)
    case Nil{} 1n+p:
      Empty.absurd({List.take(&2, U32, ys, 1n+p) == Nil{} : List<&2, U32>}, L.false_true(h))
    case x <> rest 0n:
      {==}
    case +x <> +rest 1n+ +p:
      %take_append_short(rest, ys, p, h) : {x <> List.take(&2, U32, List.append(&2, U32, rest, ys), p) == x <> _ : List<&2, U32>}
      {==}

def take_append_len(+xs: List<&2, U32>, +ys: List<&2, U32>, +k: Nat) -> {List.take(&2, U32, List.append(&2, U32, xs, ys), Nat.add(List.length(&2, U32, xs), k)) == List.append(&2, U32, xs, List.take(&2, U32, ys, k)) : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      %take_append_len(rest, ys, k) : {x <> List.take(&2, U32, List.append(&2, U32, rest, ys), Nat.add(List.length(&2, U32, rest), k)) == x <> _ : List<&2, U32>}
      {==}

def take_take(+xs: List<&2, U32>, +a: Nat, +b: Nat, +h: {Nat.is_le(a, b) == True{} : Bool}) -> {List.take(&2, U32, List.take(&2, U32, xs, b), a) == List.take(&2, U32, xs, a) : List<&2, U32>}:
  match xs a b:
    case Nil{} _ _:
      {==}
    case +x <> +rest 0n _:
      take_zero(List.take(&2, U32, x <> rest, b))
    case x <> rest 1n+p 0n:
      Empty.absurd({List.take(&2, U32, List.take(&2, U32, x <> rest, 0n), 1n+p) == List.take(&2, U32, x <> rest, 1n+p) : List<&2, U32>}, L.false_true(h))
    case +x <> +rest 1n+ +p 1n+ +q:
      %take_take(rest, p, q, h) : {x <> List.take(&2, U32, List.take(&2, U32, rest, q), p) == x <> _ : List<&2, U32>}
      {==}

def length_take(+xs: List<&2, U32>, +n: Nat, +h: {Nat.is_le(n, List.length(&2, U32, xs)) == True{} : Bool}) -> {List.length(&2, U32, List.take(&2, U32, xs, n)) == n : Nat}:
  match xs n:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+p:
      Empty.absurd({0n == 1n+p : Nat}, L.false_true(h))
    case x <> rest 0n:
      {==}
    case +x <> +rest 1n+ +p:
      %length_take(rest, p, h) : {1n+List.length(&2, U32, List.take(&2, U32, rest, p)) == 1n+_ : Nat}
      {==}

def length_append(+xs: List<&2, U32>, +ys: List<&2, U32>) -> {List.length(&2, U32, List.append(&2, U32, xs, ys)) == Nat.add(List.length(&2, U32, xs), List.length(&2, U32, ys)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      %length_append(rest, ys) : {1n+List.length(&2, U32, List.append(&2, U32, rest, ys)) == 1n+_ : Nat}
      {==}

def le_len(+xs: List<&2, U32>, +k: Nat, +e: {List.length(&2, U32, xs) == 32n : Nat}, +h: {Nat.is_le(k, 32n) == True{} : Bool}) -> {Nat.is_le(k, List.length(&2, U32, xs)) == True{} : Bool}:
  %Equal.sym(Nat, List.length(&2, U32, xs), 32n, e) : {Nat.is_le(k, _) == True{} : Bool}
  h

# ---- N = ceil(L/32) covers L ----

def peel32(+q: Nat) -> {Nat.divmod.go(Nat.add(32n+q, 31n), 31n, 0n, 0n) == Nat.divmod.go(Nat.add(q, 31n), 31n, 1n, 0n) : Nat & Nat}:
  {==}

def div_step(+q: Nat) -> {Nat.div(Nat.add(32n+q, 31n), 32n) == 1n+Nat.div(Nat.add(q, 31n), 32n) : Nat}:
  Equal.trans(Nat, Nat.div.fin(Nat.divmod.go(Nat.add(32n+q, 31n), 31n, 0n, 0n)), Nat.div.fin(N.bump2(Nat.divmod.go(Nat.add(q, 31n), 31n, 0n, 0n))), 1n+Nat.div.fin(Nat.divmod.go(Nat.add(q, 31n), 31n, 0n, 0n)),
    Equal.cong(Nat & Nat, Nat, Nat.div.fin, Nat.divmod.go(Nat.add(32n+q, 31n), 31n, 0n, 0n), N.bump2(Nat.divmod.go(Nat.add(q, 31n), 31n, 0n, 0n)),
      Equal.trans(Nat & Nat, Nat.divmod.go(Nat.add(32n+q, 31n), 31n, 0n, 0n), Nat.divmod.go(Nat.add(q, 31n), 31n, 1n, 0n), N.bump2(Nat.divmod.go(Nat.add(q, 31n), 31n, 0n, 0n)),
        peel32(q), N.acc2(Nat.add(q, 31n), 31n, 0n, 0n))),
    N.fst_bump2(Nat.divmod.go(Nat.add(q, 31n), 31n, 0n, 0n)))

def ceil_ok(len: Nat) -> {Nat.is_le(len, Nat.mul(Spec.block_count(len), 32n)) == True{} : Bool}:
  match len:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n:
      {==}
    case 5n:
      {==}
    case 6n:
      {==}
    case 7n:
      {==}
    case 8n:
      {==}
    case 9n:
      {==}
    case 10n:
      {==}
    case 11n:
      {==}
    case 12n:
      {==}
    case 13n:
      {==}
    case 14n:
      {==}
    case 15n:
      {==}
    case 16n:
      {==}
    case 17n:
      {==}
    case 18n:
      {==}
    case 19n:
      {==}
    case 20n:
      {==}
    case 21n:
      {==}
    case 22n:
      {==}
    case 23n:
      {==}
    case 24n:
      {==}
    case 25n:
      {==}
    case 26n:
      {==}
    case 27n:
      {==}
    case 28n:
      {==}
    case 29n:
      {==}
    case 30n:
      {==}
    case 31n:
      {==}
    case 32n+ +q:
      %Equal.sym(Nat, Nat.div(Nat.add(32n+q, 31n), 32n), 1n+Nat.div(Nat.add(q, 31n), 32n), div_step(q)) : {Nat.is_le(32n+q, Nat.mul(_, 32n)) == True{} : Bool}
      ceil_ok(q)

# ---- the block chain ----

# A last, partial block: 1+p <= 32 bytes of T(i+1).
def short_case(+p: Nat, n: Nat, +prk: List<&2, U32>, +info: List<&2, U32>, +prev: List<&2, U32>, +i: Nat, +hp: {Nat.is_le(1n+p, 32n) == True{} : Bool}, +h: {Nat.is_le(1n+p, Nat.mul(n, 32n)) == True{} : Bool}) -> {List.take(&2, U32, MAC.sign(prk, List.append(&2, U32, prev, List.append(&2, U32, info, [U32.from_nat(1n+i)]))), 1n+p) == List.take(&2, U32, Spec.t_blocks(n, prk, info, prev, i), 1n+p) : List<&2, U32>}:
  match n:
    case 0n:
      Empty.absurd({List.take(&2, U32, MAC.sign(prk, List.append(&2, U32, prev, List.append(&2, U32, info, [U32.from_nat(1n+i)]))), 1n+p) == List.take(&2, U32, Spec.t_blocks(0n, prk, info, prev, i), 1n+p) : List<&2, U32>}, L.false_true(h))
    case 1n+ +m:
      %MacP.sign_correct(prk, List.append(&2, U32, prev, List.append(&2, U32, info, [U32.from_nat(1n+i)]))) : {List.take(&2, U32, MAC.sign(prk, List.append(&2, U32, prev, List.append(&2, U32, info, [U32.from_nat(1n+i)]))), 1n+p) == List.take(&2, U32, List.append(&2, U32, _, Spec.t_blocks(m, prk, info, _, 1n+i)), 1n+p) : List<&2, U32>}
      Equal.sym(List<&2, U32>, List.take(&2, U32, List.append(&2, U32, MAC.sign(prk, List.append(&2, U32, prev, List.append(&2, U32, info, [U32.from_nat(1n+i)]))), Spec.t_blocks(m, prk, info, MAC.sign(prk, List.append(&2, U32, prev, List.append(&2, U32, info, [U32.from_nat(1n+i)]))), 1n+i)), 1n+p), List.take(&2, U32, MAC.sign(prk, List.append(&2, U32, prev, List.append(&2, U32, info, [U32.from_nat(1n+i)]))), 1n+p),
        take_append_short(MAC.sign(prk, List.append(&2, U32, prev, List.append(&2, U32, info, [U32.from_nat(1n+i)]))), Spec.t_blocks(m, prk, info, MAC.sign(prk, List.append(&2, U32, prev, List.append(&2, U32, info, [U32.from_nat(1n+i)]))), 1n+i), 1n+p, le_len(MAC.sign(prk, List.append(&2, U32, prev, List.append(&2, U32, info, [U32.from_nat(1n+i)]))), 1n+p, MacP.sign_len(prk, List.append(&2, U32, prev, List.append(&2, U32, info, [U32.from_nat(1n+i)]))), hp)))

# The implementation's stream of blocks, cut to rem bytes, is the first rem
# bytes of RFC 5869's T(i+1) | ... | T(i+n), whenever those have rem bytes.
def go_chain(rem: Nat, n: Nat, +prk: List<&2, U32>, +info: List<&2, U32>, +prev: List<&2, U32>, +i: Nat, +h: {Nat.is_le(rem, Nat.mul(n, 32n)) == True{} : Bool}) -> {KDF.blocks(rem, prk, info, prev, U32.from_nat(1n+i)) == List.take(&2, U32, Spec.t_blocks(n, prk, info, prev, i), rem) : List<&2, U32>}:
  match rem n:
    case 0n _:
      Equal.sym(List<&2, U32>, List.take(&2, U32, Spec.t_blocks(n, prk, info, prev, i), 0n), Nil{}, take_zero(Spec.t_blocks(n, prk, info, prev, i)))
    case 1n _:
      short_case(0n, n, prk, info, prev, i, {==}, h)
    case 2n _:
      short_case(1n, n, prk, info, prev, i, {==}, h)
    case 3n _:
      short_case(2n, n, prk, info, prev, i, {==}, h)
    case 4n _:
      short_case(3n, n, prk, info, prev, i, {==}, h)
    case 5n _:
      short_case(4n, n, prk, info, prev, i, {==}, h)
    case 6n _:
      short_case(5n, n, prk, info, prev, i, {==}, h)
    case 7n _:
      short_case(6n, n, prk, info, prev, i, {==}, h)
    case 8n _:
      short_case(7n, n, prk, info, prev, i, {==}, h)
    case 9n _:
      short_case(8n, n, prk, info, prev, i, {==}, h)
    case 10n _:
      short_case(9n, n, prk, info, prev, i, {==}, h)
    case 11n _:
      short_case(10n, n, prk, info, prev, i, {==}, h)
    case 12n _:
      short_case(11n, n, prk, info, prev, i, {==}, h)
    case 13n _:
      short_case(12n, n, prk, info, prev, i, {==}, h)
    case 14n _:
      short_case(13n, n, prk, info, prev, i, {==}, h)
    case 15n _:
      short_case(14n, n, prk, info, prev, i, {==}, h)
    case 16n _:
      short_case(15n, n, prk, info, prev, i, {==}, h)
    case 17n _:
      short_case(16n, n, prk, info, prev, i, {==}, h)
    case 18n _:
      short_case(17n, n, prk, info, prev, i, {==}, h)
    case 19n _:
      short_case(18n, n, prk, info, prev, i, {==}, h)
    case 20n _:
      short_case(19n, n, prk, info, prev, i, {==}, h)
    case 21n _:
      short_case(20n, n, prk, info, prev, i, {==}, h)
    case 22n _:
      short_case(21n, n, prk, info, prev, i, {==}, h)
    case 23n _:
      short_case(22n, n, prk, info, prev, i, {==}, h)
    case 24n _:
      short_case(23n, n, prk, info, prev, i, {==}, h)
    case 25n _:
      short_case(24n, n, prk, info, prev, i, {==}, h)
    case 26n _:
      short_case(25n, n, prk, info, prev, i, {==}, h)
    case 27n _:
      short_case(26n, n, prk, info, prev, i, {==}, h)
    case 28n _:
      short_case(27n, n, prk, info, prev, i, {==}, h)
    case 29n _:
      short_case(28n, n, prk, info, prev, i, {==}, h)
    case 30n _:
      short_case(29n, n, prk, info, prev, i, {==}, h)
    case 31n _:
      short_case(30n, n, prk, info, prev, i, {==}, h)
    case 32n+r 0n:
      Empty.absurd({KDF.blocks(32n+r, prk, info, prev, U32.from_nat(1n+i)) == List.take(&2, U32, Spec.t_blocks(0n, prk, info, prev, i), 32n+r) : List<&2, U32>}, L.false_true(h))
    case 32n+ +r 1n+ +m:
      +t = MAC.sign(prk, List.append(&2, U32, prev, List.append(&2, U32, info, [U32.from_nat(1n+i)])))
      +tb = Spec.t_blocks(m, prk, info, t, 1n+i)
      %MacP.sign_correct(prk, List.append(&2, U32, prev, List.append(&2, U32, info, [U32.from_nat(1n+i)]))) : {List.append(&2, U32, t, KDF.blocks(r, prk, info, t, U32.from_nat(1n+(1n+i)))) == List.take(&2, U32, List.append(&2, U32, _, Spec.t_blocks(m, prk, info, _, 1n+i)), 32n+r) : List<&2, U32>}
      %MacP.sign_len(prk, List.append(&2, U32, prev, List.append(&2, U32, info, [U32.from_nat(1n+i)]))) : {List.append(&2, U32, t, KDF.blocks(r, prk, info, t, U32.from_nat(1n+(1n+i)))) == List.take(&2, U32, List.append(&2, U32, t, tb), Nat.add(_, r)) : List<&2, U32>}
      %Equal.sym(List<&2, U32>, List.take(&2, U32, List.append(&2, U32, t, tb), Nat.add(List.length(&2, U32, t), r)), List.append(&2, U32, t, List.take(&2, U32, tb, r)), take_append_len(t, tb, r)) : {List.append(&2, U32, t, KDF.blocks(r, prk, info, t, U32.from_nat(1n+(1n+i)))) == _ : List<&2, U32>}
      %go_chain(r, m, prk, info, t, 1n+i, h) : {List.append(&2, U32, t, KDF.blocks(r, prk, info, t, U32.from_nat(1n+(1n+i)))) == List.append(&2, U32, t, _) : List<&2, U32>}
      {==}

# RFC 5869's T(1) | ... | T(n) has 32n bytes.
def blocks_len(n: Nat, +prk: List<&2, U32>, +info: List<&2, U32>, +prev: List<&2, U32>, +i: Nat) -> {List.length(&2, U32, Spec.t_blocks(n, prk, info, prev, i)) == Nat.mul(n, 32n) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+ +m:
      +s = HMAC.hmac(prk, List.append(&2, U32, prev, List.append(&2, U32, info, [U32.from_nat(1n+i)])))
      +tb = Spec.t_blocks(m, prk, info, s, 1n+i)
      %Equal.sym(Nat, List.length(&2, U32, List.append(&2, U32, s, tb)), Nat.add(List.length(&2, U32, s), List.length(&2, U32, tb)), length_append(s, tb)) : {_ == Nat.mul(1n+m, 32n) : Nat}
      %Equal.sym(Nat, List.length(&2, U32, s), 32n, MacP.hmac_len(prk, List.append(&2, U32, prev, List.append(&2, U32, info, [U32.from_nat(1n+i)])))) : {Nat.add(_, List.length(&2, U32, tb)) == Nat.mul(1n+m, 32n) : Nat}
      %Equal.sym(Nat, List.length(&2, U32, tb), Nat.mul(m, 32n), blocks_len(m, prk, info, s, 1n+i)) : {Nat.add(32n, _) == Nat.mul(1n+m, 32n) : Nat}
      {==}

# ---- OKM ----

def okm_correct(+prk: List<&2, U32>, +info: List<&2, U32>, +len: Nat) -> {KDF.blocks(len, prk, info, Nil{}, 1) == Spec.okm(prk, info, len) : List<&2, U32>}:
  go_chain(len, Spec.block_count(len), prk, info, Nil{}, 0n, ceil_ok(len))

def okm_length(+prk: List<&2, U32>, +info: List<&2, U32>, +len: Nat) -> {List.length(&2, U32, Spec.okm(prk, info, len)) == len : Nat}:
  +tb = Spec.t_blocks(Spec.block_count(len), prk, info, Nil{}, 0n)
  length_take(tb, len, %Equal.sym(Nat, List.length(&2, U32, tb), Nat.mul(Spec.block_count(len), 32n), blocks_len(Spec.block_count(len), prk, info, Nil{}, 0n)) : {Nat.is_le(len, _) == True{} : Bool}; ceil_ok(len))

def okm_prefix(+prk: List<&2, U32>, +info: List<&2, U32>, +a: Nat, +b: Nat, +h: {Nat.is_le(a, b) == True{} : Bool}) -> {Spec.okm(prk, info, a) == List.take(&2, U32, Spec.okm(prk, info, b), a) : List<&2, U32>}:
  +x = KDF.blocks(a, prk, info, Nil{}, 1)
  +tb = Spec.t_blocks(Spec.block_count(b), prk, info, Nil{}, 0n)
  Equal.trans(List<&2, U32>, Spec.okm(prk, info, a), x, List.take(&2, U32, Spec.okm(prk, info, b), a),
    Equal.sym(List<&2, U32>, x, Spec.okm(prk, info, a), okm_correct(prk, info, a)),
    Equal.trans(List<&2, U32>, x, List.take(&2, U32, tb, a), List.take(&2, U32, Spec.okm(prk, info, b), a),
      go_chain(a, Spec.block_count(b), prk, info, Nil{}, 0n, N.le_trans(a, b, Nat.mul(Spec.block_count(b), 32n), h, ceil_ok(b))),
      Equal.sym(List<&2, U32>, List.take(&2, U32, List.take(&2, U32, tb, b), a), List.take(&2, U32, tb, a), take_take(tb, a, b, h))))
