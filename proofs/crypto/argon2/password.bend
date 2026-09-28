import Base
import ../../../spec/lib/common.bend as C
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../../math/natural/arith.bend as NR
import ../../math/hash/hash.bend as HH
import ../../math/typed/u32laws.bend as LW
import ../../math/typed/width.bend as WW
import ../../math/typed/w64sh.bend as SH
import ../../math/typed/shrn.bend as SR
import ../subtle/word.bend as SW
import ../../../src/crypto/blake/blake2b/types.bend as T
import ../../../src/crypto/blake/blake2b/sized.bend as H
import ../../../src/crypto/argon2/argon2.bend as A2
import ../../../src/crypto/argon2/blamka.bend as G
import ../../../src/crypto/argon2/memory.bend as M
import ../../../src/crypto/argon2/phc.bend as PH
import ../../../src/crypto/password.bend as PW
import ../../../src/crypto/subtle.bend as Subtle
import ./phc.bend as PP

# The password facade: a hash that hash_password returns verifies with the
# same password, and does not need a rehash with the same parameters. The
# tag has T bytes, each below 256, so its PHC string parses back (phc.bend).

# ---------------------------------------------------------------- lengths

def len(xs: List<&2, U32>) -> Nat:
  List.length(&2, U32, xs)

def len_append(+a: List<&2, U32>, +b: List<&2, U32>) -> {len(List.append(&2, U32, a, b)) == Nat.add(len(a), len(b)) : Nat}:
  match a:
    case Nil{}:
      {==}
    case +x <> +r:
      Equal.cong(Nat, Nat, z => 1n+z, len(List.append(&2, U32, r, b)), Nat.add(len(r), len(b)), len_append(r, b))

def len_take(+xs: List<&2, U32>, +k: Nat, +h: {Nat.is_le(k, len(xs)) == True{} : Bool}) -> {len(List.take(&2, U32, xs, k)) == k : Nat}:
  match xs k:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+j:
      Empty.absurd({len(List.take(&2, U32, Nil{}, 1n+j)) == 1n+j : Nat}, L.false_true(h))
    case Con{x, r} 0n:
      {==}
    case Con{+x, +r} 1n+ +j:
      Equal.cong(Nat, Nat, z => 1n+z, len(List.take(&2, U32, r, j)), j, len_take(r, j, h))

def chain_len(+h: T.Chain) -> {len(H.chain_bytes(h)) == 64n : Nat}:
  match h:
    case T.H{T.W{a0, b0}, T.W{a1, b1}, T.W{a2, b2}, T.W{a3, b3}, T.W{a4, b4}, T.W{a5, b5}, T.W{a6, b6}, T.W{a7, b7}}:
      {==}

def hash_len(+nn: Nat, +bs: List<&2, U32>, +h: {Nat.is_le(nn, 64n) == True{} : Bool}) -> {len(H.hash(nn, bs)) == nn : Nat}:
  +c = H.chain(nn, H.pack(bs), List.length(&2, U32, bs))
  len_take(H.chain_bytes(c), nn, L.subst(Nat, z => {Nat.is_le(nn, z) == True{} : Bool}, 64n, len(H.chain_bytes(c)), Equal.sym(Nat, len(H.chain_bytes(c)), 64n, chain_len(c)), h))

# W1 || .. : 32 bytes per chained digest, then the last digest.
def hp_go_len(+n: Nat, +v: List<&2, U32>, +last: Nat, +hv: {len(v) == 64n : Nat}, +hl: {Nat.is_le(last, 64n) == True{} : Bool}) -> {len(A2.hp_go(n, v, last)) == Nat.add(Nat.mul(1n+n, 32n), last) : Nat}:
  match n v:
    case _ Nil{}:
      Empty.absurd({len(Nil{}) == Nat.add(Nat.mul(1n+n, 32n), last) : Nat}, N.zero_succ(63n, hv))
    case 0n +x <> +r:
      %Equal.sym(Nat, len(List.append(&2, U32, List.take(&2, U32, x <> r, 32n), H.hash(last, x <> r))), Nat.add(len(List.take(&2, U32, x <> r, 32n)), len(H.hash(last, x <> r))), len_append(List.take(&2, U32, x <> r, 32n), H.hash(last, x <> r))) : {_ == Nat.add(32n, last) : Nat}
      %Equal.sym(Nat, len(List.take(&2, U32, x <> r, 32n)), 32n, len_take(x <> r, 32n, L.subst(Nat, z => {Nat.is_le(32n, z) == True{} : Bool}, 64n, len(x <> r), Equal.sym(Nat, len(x <> r), 64n, hv), {==}))) : {Nat.add(_, len(H.hash(last, x <> r))) == Nat.add(32n, last) : Nat}
      %Equal.sym(Nat, len(H.hash(last, x <> r)), last, hash_len(last, x <> r, hl)) : {Nat.add(32n, _) == Nat.add(32n, last) : Nat}
      {==}
    case 1n+ +p +x <> +r:
      +w = H.hash(64n, x <> r)
      %Equal.sym(Nat, len(List.append(&2, U32, List.take(&2, U32, x <> r, 32n), A2.hp_go(p, w, last))), Nat.add(len(List.take(&2, U32, x <> r, 32n)), len(A2.hp_go(p, w, last))), len_append(List.take(&2, U32, x <> r, 32n), A2.hp_go(p, w, last))) : {_ == Nat.add(Nat.mul(2n+p, 32n), last) : Nat}
      %Equal.sym(Nat, len(List.take(&2, U32, x <> r, 32n)), 32n, len_take(x <> r, 32n, L.subst(Nat, z => {Nat.is_le(32n, z) == True{} : Bool}, 64n, len(x <> r), Equal.sym(Nat, len(x <> r), 64n, hv), {==}))) : {Nat.add(_, len(A2.hp_go(p, w, last))) == Nat.add(Nat.mul(2n+p, 32n), last) : Nat}
      %Equal.sym(Nat, len(A2.hp_go(p, w, last)), Nat.add(Nat.mul(1n+p, 32n), last), hp_go_len(p, w, last, hash_len(64n, x <> r, {==}), hl)) : {Nat.add(32n, _) == Nat.add(Nat.mul(2n+p, 32n), last) : Nat}
      Equal.sym(Nat, Nat.add(Nat.add(32n, Nat.mul(1n+p, 32n)), last), Nat.add(32n, Nat.add(Nat.mul(1n+p, 32n), last)), NA.add_assoc(32n, Nat.mul(1n+p, 32n), last))

def lt96(+q: Nat, +r: Nat, +hq: {Nat.is_lt(q, 3n) == True{} : Bool}, +hr: {Nat.is_lt(r, 32n) == True{} : Bool}) -> {Nat.is_lt(Nat.add(Nat.mul(q, 32n), r), 96n) == True{} : Bool}:
  match q:
    case 0n:
      N.lt_trans(r, 32n, 96n, hr, {==})
    case 1n:
      N.lt_trans(r, 32n, 64n, hr, {==})
    case 2n:
      hr
    case 3n+j:
      Empty.absurd({Nat.is_lt(Nat.add(Nat.mul(3n+j, 32n), r), 96n) == True{} : Bool}, N.lt_zero_absurd(j, hq))

def ge96(+tl: Nat, +h: {Nat.is_le(65n, tl) == True{} : Bool}) -> {Nat.is_le(96n, Nat.add(tl, 31n)) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(tl, 31n), Nat.add(31n, tl), N.add_comm(tl, 31n)) : {Nat.is_le(96n, _) == True{} : Bool}
  h

def sub_cancel(+c: Nat, +m: Nat, +r: Nat) -> {Nat.sub(Nat.add(c, Nat.add(m, r)), m) == Nat.add(c, r) : Nat}:
  %Equal.sym(Nat, Nat.add(c, Nat.add(m, r)), Nat.add(m, Nat.add(c, r)), NA.add_swap(c, m, r)) : {Nat.sub(_, m) == Nat.add(c, r) : Nat}
  N.add_sub_cancel(m, Nat.add(c, r))

def big(+tl: Nat, +q: Nat, +r: Nat, +e: {Nat.add(tl, 31n) == Nat.add(Nat.mul(q, 32n), r) : Nat}, +hr: {Nat.is_lt(r, 32n) == True{} : Bool}, +ht: {Nat.is_le(65n, tl) == True{} : Bool}, +hq: {Nat.is_lt(q, 3n) == True{} : Bool}) -> Empty:
  +h1 = ge96(tl, ht)
  +h2 = L.subst(Nat, z => {Nat.is_lt(z, 96n) == True{} : Bool}, Nat.add(Nat.mul(q, 32n), r), Nat.add(tl, 31n), Equal.sym(Nat, Nat.add(tl, 31n), Nat.add(Nat.mul(q, 32n), r), e), lt96(q, r, hq, hr))
  L.true_false(Equal.trans(Bool, True{}, Nat.is_lt(96n, 96n), False{}, Equal.sym(Bool, Nat.is_lt(96n, 96n), True{}, N.le_lt_trans(96n, Nat.add(tl, 31n), 96n, h1, h2)), N.lt_irrefl(96n)))

# The long case of H': with Q = (T + 31) / 32, r = Q - 2 digests of 32 bytes and a last one of T - 32 r.
def long_len(+tl: Nat, +q: Nat, +r: Nat, +v: List<&2, U32>, +e: {Nat.add(tl, 31n) == Nat.add(Nat.mul(q, 32n), r) : Nat}, +hr: {Nat.is_lt(r, 32n) == True{} : Bool}, +ht: {Nat.is_le(65n, tl) == True{} : Bool}, +hv: {len(v) == 64n : Nat}) -> {len(A2.hp_go(Nat.sub(Nat.sub(q, 2n), 1n), v, Nat.sub(tl, Nat.mul(32n, Nat.sub(q, 2n))))) == tl : Nat}:
  match q:
    case 0n:
      Empty.absurd({len(A2.hp_go(0n, v, Nat.sub(tl, 0n))) == tl : Nat}, big(tl, 0n, r, e, hr, ht, {==}))
    case 1n:
      Empty.absurd({len(A2.hp_go(0n, v, Nat.sub(tl, 0n))) == tl : Nat}, big(tl, 1n, r, e, hr, ht, {==}))
    case 2n:
      Empty.absurd({len(A2.hp_go(0n, v, Nat.sub(tl, 0n))) == tl : Nat}, big(tl, 2n, r, e, hr, ht, {==}))
    case 3n+ +j:
      +m = Nat.mul(j, 32n)
      +et = NR.add_cancel(31n, tl, Nat.add(65n, Nat.add(m, r)), Equal.trans(Nat, Nat.add(31n, tl), Nat.add(tl, 31n), Nat.add(Nat.mul(3n+j, 32n), r), N.add_comm(31n, tl), e))
      %Equal.sym(Nat, tl, Nat.add(65n, Nat.add(m, r)), et) : {len(A2.hp_go(Nat.sub(j, 0n), v, Nat.sub(_, Nat.mul(32n, 1n+j)))) == _ : Nat}
      %Equal.sym(Nat, Nat.sub(j, 0n), j, N.sub_zero(j)) : {len(A2.hp_go(_, v, Nat.sub(Nat.add(65n, Nat.add(m, r)), Nat.mul(32n, 1n+j)))) == Nat.add(65n, Nat.add(m, r)) : Nat}
      %Equal.sym(Nat, Nat.mul(32n, 1n+j), Nat.mul(1n+j, 32n), NA.mul_comm(32n, 1n+j)) : {len(A2.hp_go(j, v, Nat.sub(Nat.add(65n, Nat.add(m, r)), _))) == Nat.add(65n, Nat.add(m, r)) : Nat}
      %Equal.sym(Nat, Nat.sub(Nat.add(33n, Nat.add(m, r)), m), Nat.add(33n, r), sub_cancel(33n, m, r)) : {len(A2.hp_go(j, v, _)) == Nat.add(65n, Nat.add(m, r)) : Nat}
      %Equal.sym(Nat, len(A2.hp_go(j, v, Nat.add(33n, r))), Nat.add(Nat.mul(1n+j, 32n), Nat.add(33n, r)), hp_go_len(j, v, Nat.add(33n, r), hv, N.lt_succ_le(r, 31n, hr))) : {_ == Nat.add(65n, Nat.add(m, r)) : Nat}
      %Equal.sym(Nat, Nat.add(m, Nat.add(33n, r)), Nat.add(33n, Nat.add(m, r)), NA.add_swap(m, 33n, r)) : {Nat.add(32n, _) == Nat.add(65n, Nat.add(m, r)) : Nat}
      {==}

def pick_len(+tl: Nat, +x: List<&2, U32>, +short: Bool, +es: {Nat.is_le(tl, 64n) == short : Bool}) -> {len(A2.hp_pick(tl, x, short)) == tl : Nat}:
  match short:
    case True{}:
      hash_len(tl, x, es)
    case False{}:
      +a = Nat.add(tl, 31n)
      +ht = N.lt_succ_le_succ(64n, tl, N.not_le_lt(tl, 64n, es))
      long_len(tl, Nat.div(a, 32n), Nat.mod(a, 32n), H.hash(64n, x), NR.dm_eq(31n, a), NR.dm_lt(31n, a), ht, hash_len(64n, x, {==}))

# H'^T has T bytes.
def hprime_len(+tl: Nat, +a: List<&2, U32>) -> {len(A2.hprime(tl, a)) == tl : Nat}:
  pick_len(tl, A2.cat(A2.le32(tl), a), Nat.is_le(tl, 64n), {==})

# ---------------------------------------------------------------- bytes below 256

def ok_append(+a: List<&2, U32>, +b: List<&2, U32>, +ha: {PP.ok(a) == True{} : Bool}, +hb: {PP.ok(b) == True{} : Bool}) -> {PP.ok(List.append(&2, U32, a, b)) == True{} : Bool}:
  match a:
    case Nil{}:
      hb
    case +x <> +r:
      L.and_intro(Nat.is_lt(U32.to_nat(x), 256n), PP.ok(List.append(&2, U32, r, b)), PP.ok_head(x, r, ha), ok_append(r, b, PP.ok_tail(x, r, ha), hb))

def ok_take(+xs: List<&2, U32>, +k: Nat, +h: {PP.ok(xs) == True{} : Bool}) -> {PP.ok(List.take(&2, U32, xs, k)) == True{} : Bool}:
  match xs k:
    case Nil{} _:
      {==}
    case Con{x, r} 0n:
      {==}
    case Con{+x, +r} 1n+ +j:
      L.and_intro(Nat.is_lt(U32.to_nat(x), 256n), PP.ok(List.take(&2, U32, r, j)), PP.ok_head(x, r, h), ok_take(r, j, PP.ok_tail(x, r, h)))

def and255(+w: U32) -> {Nat.is_lt(U32.to_nat(U32.and(w, 255)), 256n) == True{} : Bool}:
  N.le_lt_succ(U32.to_nat(U32.and(w, 255)), 255n, HH.and_le32(w, 255))

def top8(+w: U32) -> {Nat.is_lt(U32.to_nat(U32.shrn(w, 24n)), 256n) == True{} : Bool}:
  +f = SH.fits_high(24n, 8n, LW.v(w), LW.vb(w))
  %Equal.sym(Nat, SR.v(U32.shrn(w, 24n)), C.high(24n, SR.v(w)), SR.shrn_high(w, 24n)) : {Nat.is_lt(_, 256n) == True{} : Bool}
  WW.lt_of_fits(8n, C.high(24n, LW.v(w)), f)

def le_ok(+w: U32) -> {PP.ok(H.le(w)) == True{} : Bool}:
  L.and_intro(Nat.is_lt(U32.to_nat(U32.and(w, 255)), 256n), PP.ok([U32.and(U32.shrn(w, 8n), 255), U32.and(U32.shrn(w, 16n), 255), U32.shrn(w, 24n)]), and255(w),
    L.and_intro(Nat.is_lt(U32.to_nat(U32.and(U32.shrn(w, 8n), 255)), 256n), PP.ok([U32.and(U32.shrn(w, 16n), 255), U32.shrn(w, 24n)]), and255(U32.shrn(w, 8n)),
      L.and_intro(Nat.is_lt(U32.to_nat(U32.and(U32.shrn(w, 16n), 255)), 256n), PP.ok([U32.shrn(w, 24n)]), and255(U32.shrn(w, 16n)),
        L.and_intro(Nat.is_lt(U32.to_nat(U32.shrn(w, 24n)), 256n), True{}, top8(w), {==}))))

def lane_ok(+l: T.Lane) -> {PP.ok(H.lane_bytes(l)) == True{} : Bool}:
  match l:
    case T.W{+a, +b}:
      ok_append(H.le(a), H.le(b), le_ok(a), le_ok(b))

def chain_ok(+h: T.Chain) -> {PP.ok(H.chain_bytes(h)) == True{} : Bool}:
  match h:
    case T.H{+h0, +h1, +h2, +h3, +h4, +h5, +h6, +h7}:
      ok_append(H.lane_bytes(h0), List.concat(&2, U32, [H.lane_bytes(h1), H.lane_bytes(h2), H.lane_bytes(h3), H.lane_bytes(h4), H.lane_bytes(h5), H.lane_bytes(h6), H.lane_bytes(h7)]), lane_ok(h0),
        ok_append(H.lane_bytes(h1), List.concat(&2, U32, [H.lane_bytes(h2), H.lane_bytes(h3), H.lane_bytes(h4), H.lane_bytes(h5), H.lane_bytes(h6), H.lane_bytes(h7)]), lane_ok(h1),
          ok_append(H.lane_bytes(h2), List.concat(&2, U32, [H.lane_bytes(h3), H.lane_bytes(h4), H.lane_bytes(h5), H.lane_bytes(h6), H.lane_bytes(h7)]), lane_ok(h2),
            ok_append(H.lane_bytes(h3), List.concat(&2, U32, [H.lane_bytes(h4), H.lane_bytes(h5), H.lane_bytes(h6), H.lane_bytes(h7)]), lane_ok(h3),
              ok_append(H.lane_bytes(h4), List.concat(&2, U32, [H.lane_bytes(h5), H.lane_bytes(h6), H.lane_bytes(h7)]), lane_ok(h4),
                ok_append(H.lane_bytes(h5), List.concat(&2, U32, [H.lane_bytes(h6), H.lane_bytes(h7)]), lane_ok(h5),
                  ok_append(H.lane_bytes(h6), List.concat(&2, U32, [H.lane_bytes(h7)]), lane_ok(h6),
                    ok_append(H.lane_bytes(h7), Nil{}, lane_ok(h7), {==}))))))))

def hash_ok(+nn: Nat, +bs: List<&2, U32>) -> {PP.ok(H.hash(nn, bs)) == True{} : Bool}:
  +c = H.chain(nn, H.pack(bs), List.length(&2, U32, bs))
  ok_take(H.chain_bytes(c), nn, chain_ok(c))

def hp_go_ok(+n: Nat, +v: List<&2, U32>, +last: Nat, +hv: {PP.ok(v) == True{} : Bool}) -> {PP.ok(A2.hp_go(n, v, last)) == True{} : Bool}:
  match n v:
    case _ Nil{}:
      {==}
    case 0n +x <> +r:
      ok_append(List.take(&2, U32, x <> r, 32n), H.hash(last, x <> r), ok_take(x <> r, 32n, hv), hash_ok(last, x <> r))
    case 1n+ +p +x <> +r:
      ok_append(List.take(&2, U32, x <> r, 32n), A2.hp_go(p, H.hash(64n, x <> r), last), ok_take(x <> r, 32n, hv), hp_go_ok(p, H.hash(64n, x <> r), last, hash_ok(64n, x <> r)))

def pick_ok(+tl: Nat, +x: List<&2, U32>, +short: Bool) -> {PP.ok(A2.hp_pick(tl, x, short)) == True{} : Bool}:
  match short:
    case True{}:
      hash_ok(tl, x)
    case False{}:
      +r = Nat.sub(Nat.div(Nat.add(tl, 31n), 32n), 2n)
      hp_go_ok(Nat.sub(r, 1n), H.hash(64n, x), Nat.sub(tl, Nat.mul(32n, r)), hash_ok(64n, x))

# Every byte of H'^T is below 256.
def hprime_ok(+tl: Nat, +a: List<&2, U32>) -> {PP.ok(A2.hprime(tl, a)) == True{} : Bool}:
  pick_ok(tl, A2.cat(A2.le32(tl), a), Nat.is_le(tl, 64n))

# ---------------------------------------------------------------- the tag of a hash

def tag_of(+ok: Bool, +pw: List<&2, U32>, +salt: List<&2, U32>, +t: Nat, +m: Nat, +p: Nat, +tl: Nat, +tag: List<&2, U32>, +e: {A2.checked(ok, pw, salt, Nil{}, Nil{}, t, m, p, tl) == Some{tag} : Maybe<&2, List<&2, U32>>}) -> {A2.run(pw, salt, Nil{}, Nil{}, t, m, p, tl) == tag : List<&2, U32>}:
  match ok:
    case True{}:
      L.some_inj(List<&2, U32>, A2.run(pw, salt, Nil{}, Nil{}, t, m, p, tl), tag, e)
    case False{}:
      Empty.absurd({A2.run(pw, salt, Nil{}, Nil{}, t, m, p, tl) == tag : List<&2, U32>}, L.none_some(List<&2, U32>, tag, e))

# The bytes H' is applied to in run.
def run_arg(+pw: List<&2, U32>, +salt: List<&2, U32>, +t: Nat, +m: Nat, +p: Nat, +tl: Nat) -> List<&2, U32>:
  +mm = A2.blocks(m, p)
  +q = Nat.div(mm, p)
  A2.block_bytes(A2.final_go(Nat.sub(p, 1n), 0n, q, G.zero(), M.get(Nat.sub(q, 1n), A2.passes_go(t, 0n, p, q, Nat.div(q, 4n), mm, t, A2.init_go(p, 0n, q, A2.h0(p, tl, m, t, pw, salt, Nil{}, Nil{}), M.new(M.levels(mm)))))))

def run_ok(+pw: List<&2, U32>, +salt: List<&2, U32>, +t: Nat, +m: Nat, +p: Nat, +tl: Nat) -> {PP.ok(A2.run(pw, salt, Nil{}, Nil{}, t, m, p, tl)) == True{} : Bool}:
  hprime_ok(tl, run_arg(pw, salt, t, m, p, tl))

def run_len(+pw: List<&2, U32>, +salt: List<&2, U32>, +t: Nat, +m: Nat, +p: Nat, +tl: Nat) -> {len(A2.run(pw, salt, Nil{}, Nil{}, t, m, p, tl)) == tl : Nat}:
  hprime_len(tl, run_arg(pw, salt, t, m, p, tl))

def tag_ok(+pw: List<&2, U32>, +salt: List<&2, U32>, +t: Nat, +m: Nat, +p: Nat, +tl: Nat, +tag: List<&2, U32>, +er: {A2.argon2id(pw, salt, Nil{}, Nil{}, t, m, p, tl) == Some{tag} : Maybe<&2, List<&2, U32>>}) -> {PP.ok(tag) == True{} : Bool}:
  +ok = Bool.and(A2.valid(pw, salt, Nil{}, Nil{}, t, m, p, tl), A2.fits(m, p))
  L.subst(List<&2, U32>, z => {PP.ok(z) == True{} : Bool}, A2.run(pw, salt, Nil{}, Nil{}, t, m, p, tl), tag, tag_of(ok, pw, salt, t, m, p, tl, tag, er), run_ok(pw, salt, t, m, p, tl))

def tag_len(+pw: List<&2, U32>, +salt: List<&2, U32>, +t: Nat, +m: Nat, +p: Nat, +tl: Nat, +tag: List<&2, U32>, +er: {A2.argon2id(pw, salt, Nil{}, Nil{}, t, m, p, tl) == Some{tag} : Maybe<&2, List<&2, U32>>}) -> {len(tag) == tl : Nat}:
  +ok = Bool.and(A2.valid(pw, salt, Nil{}, Nil{}, t, m, p, tl), A2.fits(m, p))
  L.subst(List<&2, U32>, z => {len(z) == tl : Nat}, A2.run(pw, salt, Nil{}, Nil{}, t, m, p, tl), tag, tag_of(ok, pw, salt, t, m, p, tl, tag, er), run_len(pw, salt, t, m, p, tl))

# ---------------------------------------------------------------- subtle.eq(a, a)

def diff_self(+a: List<&2, U32>, +acc: U32, +h: {U32.is_eq(acc, 0) == True{} : Bool}) -> {U32.is_eq(Subtle.diff(a, a, acc), 0) == True{} : Bool}:
  match a:
    case Nil{}:
      h
    case +x <> +xs:
      +acc2 = U32.or(acc, U32.xor(x, x))
      +e = Equal.trans(Bool, U32.is_eq(acc2, 0), Bool.and(U32.is_eq(acc, 0), U32.is_eq(U32.xor(x, x), 0)), True{}, SW.u32_or_zero(acc, U32.xor(x, x)),
        L.and_intro(U32.is_eq(acc, 0), U32.is_eq(U32.xor(x, x), 0), h, Equal.trans(Bool, U32.is_eq(U32.xor(x, x), 0), U32.is_eq(x, x), True{}, SW.u32_xor_zero(x, x), SW.u32_refl(x))))
      diff_self(xs, acc2, e)

# subtle.eq(a, a) == True (proofs/crypto/subtle proves it too, as Eq.refl).
def eq_refl(+a: List<&2, U32>) -> {Subtle.eq(a, a) == True{} : Bool}:
  L.and_intro(Nat.is_eq(List.length(&2, U32, a), List.length(&2, U32, a)), U32.is_eq(Subtle.diff(a, a, 0), 0), N.is_eq_refl(List.length(&2, U32, a)), diff_self(a, 0, {==}))

# ---------------------------------------------------------------- the facade

# The result of hash_password verifies (vacuously when it is None).
def verified(+pw: List<&2, U32>, r: Maybe<&2, String>) -> Bool:
  match r:
    case None{}:
      True{}
    case Some{s}:
      PW.verify_password(pw, s)

# The result of hash_password does not need a rehash (vacuously when None).
def fresh(r: Maybe<&2, String>, +params: PW.Params) -> Bool:
  match r:
    case None{}:
      False{}
    case Some{s}:
      PW.needs_rehash(s, params)

def enc_ver(+pw: List<&2, U32>, +salt: List<&2, U32>, +m: Nat, +t: Nat, +p: Nat, +tl: Nat, +r: Maybe<&2, List<&2, U32>>, +er: {A2.argon2id(pw, salt, Nil{}, Nil{}, t, m, p, tl) == r : Maybe<&2, List<&2, U32>>}, +hs: {PP.ok(salt) == True{} : Bool}) -> {verified(pw, PW.encode(m, t, p, salt, r)) == True{} : Bool}:
  match r:
    case None{}:
      {==}
    case Some{+h}:
      %Equal.sym(Maybe<&2, PH.Phc>, PH.parse(PH.format(PH.Phc{m, t, p, salt, h})), Some{PH.Phc{m, t, p, salt, h}}, PP.parse_format(m, t, p, salt, h, hs, tag_ok(pw, salt, t, m, p, tl, h, er))) : {PW.verify_parsed(pw, _) == True{} : Bool}
      %Equal.sym(Nat, len(h), tl, tag_len(pw, salt, t, m, p, tl, h, er)) : {PW.verify_tag(h, A2.argon2id(pw, salt, Nil{}, Nil{}, t, m, p, _)) == True{} : Bool}
      %Equal.sym(Maybe<&2, List<&2, U32>>, A2.argon2id(pw, salt, Nil{}, Nil{}, t, m, p, tl), Some{h}, er) : {PW.verify_tag(h, _) == True{} : Bool}
      eq_refl(h)

# verify_password(pw, hash_password(pw, salt, params)) == True whenever
# hash_password returns a string, for every salt of bytes below 256.
def verify_hash(+pw: List<&2, U32>, +salt: List<&2, U32>, +params: PW.Params, +hs: {PP.ok(salt) == True{} : Bool}) -> {verified(pw, PW.hash_password(pw, salt, params)) == True{} : Bool}:
  match params:
    case PW.Params{+m, +t, +p, +tl, +sl}:
      enc_ver(pw, salt, m, t, p, tl, A2.argon2id(pw, salt, Nil{}, Nil{}, t, m, p, tl), {==}, hs)

def enc_fresh(+pw: List<&2, U32>, +salt: List<&2, U32>, +m: Nat, +t: Nat, +p: Nat, +tl: Nat, +sl: Nat, +r: Maybe<&2, List<&2, U32>>, +er: {A2.argon2id(pw, salt, Nil{}, Nil{}, t, m, p, tl) == r : Maybe<&2, List<&2, U32>>}, +hs: {PP.ok(salt) == True{} : Bool}, +hl: {len(salt) == sl : Nat}) -> {fresh(PW.encode(m, t, p, salt, r), PW.Params{m, t, p, tl, sl}) == False{} : Bool}:
  match r:
    case None{}:
      {==}
    case Some{+h}:
      %Equal.sym(Maybe<&2, PH.Phc>, PH.parse(PH.format(PH.Phc{m, t, p, salt, h})), Some{PH.Phc{m, t, p, salt, h}}, PP.parse_format(m, t, p, salt, h, hs, tag_ok(pw, salt, t, m, p, tl, h, er))) : {PW.rehash_parsed(_, PW.Params{m, t, p, tl, sl}) == False{} : Bool}
      %Equal.sym(Nat, len(h), tl, tag_len(pw, salt, t, m, p, tl, h, er)) : {Bool.not(Bool.and(Bool.and(Nat.is_eq(m, m), Bool.and(Nat.is_eq(t, t), Nat.is_eq(p, p))), Bool.and(Nat.is_eq(_, tl), Nat.is_eq(PW.len(salt), sl)))) == False{} : Bool}
      %Equal.sym(Nat, len(salt), sl, hl) : {Bool.not(Bool.and(Bool.and(Nat.is_eq(m, m), Bool.and(Nat.is_eq(t, t), Nat.is_eq(p, p))), Bool.and(Nat.is_eq(tl, tl), Nat.is_eq(_, sl)))) == False{} : Bool}
      %Equal.sym(Bool, Nat.is_eq(m, m), True{}, N.is_eq_refl(m)) : {Bool.not(Bool.and(Bool.and(_, Bool.and(Nat.is_eq(t, t), Nat.is_eq(p, p))), Bool.and(Nat.is_eq(tl, tl), Nat.is_eq(sl, sl)))) == False{} : Bool}
      %Equal.sym(Bool, Nat.is_eq(t, t), True{}, N.is_eq_refl(t)) : {Bool.not(Bool.and(Bool.and(True{}, Bool.and(_, Nat.is_eq(p, p))), Bool.and(Nat.is_eq(tl, tl), Nat.is_eq(sl, sl)))) == False{} : Bool}
      %Equal.sym(Bool, Nat.is_eq(p, p), True{}, N.is_eq_refl(p)) : {Bool.not(Bool.and(Bool.and(True{}, Bool.and(True{}, _)), Bool.and(Nat.is_eq(tl, tl), Nat.is_eq(sl, sl)))) == False{} : Bool}
      %Equal.sym(Bool, Nat.is_eq(tl, tl), True{}, N.is_eq_refl(tl)) : {Bool.not(Bool.and(Bool.and(True{}, Bool.and(True{}, True{})), Bool.and(_, Nat.is_eq(sl, sl)))) == False{} : Bool}
      %Equal.sym(Bool, Nat.is_eq(sl, sl), True{}, N.is_eq_refl(sl)) : {Bool.not(Bool.and(Bool.and(True{}, Bool.and(True{}, True{})), Bool.and(True{}, _))) == False{} : Bool}
      {==}

# needs_rehash(hash_password(pw, salt, params), params) == False whenever
# hash_password returns a string, for every salt of bytes below 256 with the
# parameters' salt length.
def rehash_hash(+pw: List<&2, U32>, +salt: List<&2, U32>, +params: PW.Params, +hs: {PP.ok(salt) == True{} : Bool}, +hl: {len(salt) == PW.salt_len(params) : Nat}) -> {fresh(PW.hash_password(pw, salt, params), params) == False{} : Bool}:
  match params:
    case PW.Params{+m, +t, +p, +tl, +sl}:
      enc_fresh(pw, salt, m, t, p, tl, sl, A2.argon2id(pw, salt, Nil{}, Nil{}, t, m, p, tl), {==}, hs, hl)
