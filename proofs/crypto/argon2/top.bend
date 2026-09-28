import Base
import ../../../spec/lib/common.bend as SC
import ../../lib/array.bend as AR
import ../../lib/list.bend as LL
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/arith.bend as AR2
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../../math/natural/arith.bend as NR
import ../../../src/crypto/blake/blake2b/types.bend as T
import ../../../src/crypto/argon2/types.bend as A
import ../../../src/crypto/argon2/blamka.bend as G
import ../../../src/crypto/argon2/memory.bend as M
import ../../../src/crypto/argon2/argon2.bend as I
import ../../../spec/crypto/argon2/blamka.bend as SG
import ../../../spec/crypto/argon2/argon2.bend as SA
import ./blamka.bend as BL
import ./memory.bend as MEM
import ./hash.bend as HS
import ./fill.bend as F
import ./run.bend as R

# Argon2id of the implementation equals Argon2id of the specification for
# every input the implementation accepts.

# ---------------------------------------------------------------- the memory geometry

def X(+m: Nat, +p: Nat) -> Nat:
  Nat.div(m, Nat.mul(4n, p))

def mm_swap(+p: Nat, +x: Nat) -> {Nat.mul(Nat.mul(4n, p), x) == Nat.mul(Nat.mul(4n, x), p) : Nat}:
  Equal.trans(Nat, Nat.mul(Nat.mul(4n, p), x), Nat.mul(4n, Nat.mul(p, x)), Nat.mul(Nat.mul(4n, x), p),
    NA.mul_assoc(4n, p, x),
    Equal.trans(Nat, Nat.mul(4n, Nat.mul(p, x)), Nat.mul(4n, Nat.mul(x, p)), Nat.mul(Nat.mul(4n, x), p),
      Equal.cong(Nat, Nat, z => Nat.mul(4n, z), Nat.mul(p, x), Nat.mul(x, p), NA.mul_comm(p, x)),
      Equal.sym(Nat, Nat.mul(Nat.mul(4n, x), p), Nat.mul(4n, Nat.mul(x, p)), NA.mul_assoc(4n, x, p))))

# Exact division: y * d / d = y for d >= 1.
def div_exact(+y: Nat, +d: Nat, +hd: {Nat.is_le(1n, d) == True{} : Bool}) -> {Nat.div(Nat.mul(y, d), d) == y : Nat}:
  match d:
    case 0n:
      Empty.absurd({Nat.div(Nat.mul(y, 0n), 0n) == y : Nat}, L.false_true(hd))
    case 1n+ +b:
      %NA.add_zero(Nat.mul(y, 1n+b)) : {Nat.div(_, 1n+b) == y : Nat}
      NR.div_of(y, b, 0n, {==})

# q = m' / p = 4 X.
def q_eq(+m: Nat, +p: Nat, +hp: {Nat.is_le(1n, p) == True{} : Bool}) -> {Nat.div(I.blocks(m, p), p) == Nat.mul(4n, X(m, p)) : Nat}:
  %Equal.sym(Nat, Nat.mul(Nat.mul(4n, p), X(m, p)), Nat.mul(Nat.mul(4n, X(m, p)), p), mm_swap(p, X(m, p))) : {Nat.div(_, p) == Nat.mul(4n, X(m, p)) : Nat}
  div_exact(Nat.mul(4n, X(m, p)), p, hp)

# sl = q / 4 = X.
def div4(+x: Nat) -> {Nat.div(Nat.mul(4n, x), 4n) == x : Nat}:
  %Equal.sym(Nat, Nat.mul(4n, x), Nat.mul(x, 4n), NA.mul_comm(4n, x)) : {Nat.div(_, 4n) == x : Nat}
  div_exact(x, 4n, {==})

def sl_eq(+m: Nat, +p: Nat, +hp: {Nat.is_le(1n, p) == True{} : Bool}) -> {Nat.div(Nat.div(I.blocks(m, p), p), 4n) == X(m, p) : Nat}:
  %Equal.sym(Nat, Nat.div(I.blocks(m, p), p), Nat.mul(4n, X(m, p)), q_eq(m, p, hp)) : {Nat.div(_, 4n) == X(m, p) : Nat}
  div4(X(m, p))

# q = 4 sl
def hq(+m: Nat, +p: Nat, +hp: {Nat.is_le(1n, p) == True{} : Bool}) -> {Nat.div(I.blocks(m, p), p) == Nat.mul(4n, Nat.div(Nat.div(I.blocks(m, p), p), 4n)) : Nat}:
  %Equal.sym(Nat, Nat.div(Nat.div(I.blocks(m, p), p), 4n), X(m, p), sl_eq(m, p, hp)) : {Nat.div(I.blocks(m, p), p) == Nat.mul(4n, _) : Nat}
  q_eq(m, p, hp)

# m' = p q
def hlen(+m: Nat, +p: Nat, +hp: {Nat.is_le(1n, p) == True{} : Bool}) -> {I.blocks(m, p) == Nat.mul(p, Nat.div(I.blocks(m, p), p)) : Nat}:
  %Equal.sym(Nat, Nat.div(I.blocks(m, p), p), Nat.mul(4n, X(m, p)), q_eq(m, p, hp)) : {I.blocks(m, p) == Nat.mul(p, _) : Nat}
  Equal.trans(Nat, Nat.mul(Nat.mul(4n, p), X(m, p)), Nat.mul(Nat.mul(p, 4n), X(m, p)), Nat.mul(p, Nat.mul(4n, X(m, p))),
    Equal.cong(Nat, Nat, z => Nat.mul(z, X(m, p)), Nat.mul(4n, p), Nat.mul(p, 4n), NA.mul_comm(4n, p)),
    NA.mul_assoc(p, 4n, X(m, p)))

# 8p <= m gives X >= 2.
def x_ge2(+m: Nat, +p: Nat, +hp: {Nat.is_le(1n, p) == True{} : Bool}, +h8: {Nat.is_le(Nat.mul(8n, p), m) == True{} : Bool}) -> {Nat.is_le(2n, X(m, p)) == True{} : Bool}:
  match p:
    case 0n:
      Empty.absurd({Nat.is_le(2n, X(m, 0n)) == True{} : Bool}, L.false_true(hp))
    case 1n+ +b:
      +e = NR.le_div(Nat.add(b, Nat.mul(3n, 1n+b)), 2n, m)
      +h2 = L.subst(Nat, z => {Nat.is_le(z, m) == True{} : Bool}, Nat.mul(8n, 1n+b), Nat.mul(2n, Nat.mul(4n, 1n+b)), NA.mul_assoc(2n, 4n, 1n+b), h8)
      Equal.trans(Bool, Nat.is_le(2n, X(m, 1n+b)), Nat.is_le(Nat.mul(2n, Nat.mul(4n, 1n+b)), m), True{}, e, h2)

# ---------------------------------------------------------------- the memory size

def pw_eq(+k: Nat) -> {M.pw(k) == SC.pow2(k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+ +j:
      Equal.cong(Nat, Nat, z => Nat.double(z), M.pw(j), SC.pow2(j), pw_eq(j))

def d8(+b: Nat) -> {Nat.mul(b, 256n) == Nat.double(Nat.double(Nat.double(Nat.double(Nat.double(Nat.double(Nat.double(Nat.double(b)))))))) : Nat}:
  match b:
    case 0n:
      {==}
    case 1n+ +c:
      %Equal.sym(Nat, Nat.mul(c, 256n), Nat.double(Nat.double(Nat.double(Nat.double(Nat.double(Nat.double(Nat.double(Nat.double(c)))))))), d8(c)) : {Nat.add(256n, _) == Nat.double(Nat.double(Nat.double(Nat.double(Nat.double(Nat.double(Nat.double(Nat.double(1n+c)))))))) : Nat}
      {==}

# levels(n) = k with k <= 23 gives n <= 2^k.
def levels_go_ok(+f: Nat, +n: Nat, +k: Nat, +done: Bool, +hd: {done == Nat.is_le(n, M.pw(k)) : Bool}, +hr: {Nat.is_lt(M.levels_go(f, n, k, done), Nat.add(k, f)) == True{} : Bool}) -> {Nat.is_le(n, M.pw(M.levels_go(f, n, k, done))) == True{} : Bool}:
  match f done:
    case _ True{}:
      Equal.sym(Bool, True{}, Nat.is_le(n, M.pw(k)), hd)
    case 0n False{}:
      Empty.absurd({Nat.is_le(n, M.pw(k)) == True{} : Bool}, L.false_true(Equal.trans(Bool, False{}, Nat.is_lt(k, Nat.add(k, 0n)), True{}, Equal.trans(Bool, False{}, Nat.is_lt(k, k), Nat.is_lt(k, Nat.add(k, 0n)), Equal.sym(Bool, Nat.is_lt(k, k), False{}, N.lt_irrefl(k)), Equal.cong(Nat, Bool, z => Nat.is_lt(k, z), k, Nat.add(k, 0n), Equal.sym(Nat, Nat.add(k, 0n), k, N.add_zero(k)))), hr)))
    case 1n+ +g False{}:
      +r = M.levels_go(g, n, 1n+k, Nat.is_le(n, M.pw(1n+k)))
      levels_go_ok(g, n, 1n+k, Nat.is_le(n, M.pw(1n+k)), {==}, L.subst(Nat, z => {Nat.is_lt(r, z) == True{} : Bool}, Nat.add(k, 1n+g), 1n+Nat.add(k, g), N.add_succ(k, g), hr))

def levels_ok(+n: Nat, +h: {Nat.is_le(M.levels(n), 23n) == True{} : Bool}) -> {Nat.is_le(n, SC.pow2(M.levels(n))) == True{} : Bool}:
  +hr = N.le_lt_trans(M.levels(n), 23n, 32n, h, {==})
  L.subst(Nat, z => {Nat.is_le(n, z) == True{} : Bool}, M.pw(M.levels(n)), SC.pow2(M.levels(n)), pw_eq(M.levels(n)), levels_go_ok(32n, n, 0n, Nat.is_le(n, 1n), {==}, hr))

# 256 m' <= 2^(8 + k).
def cap(+n: Nat, +h: {Nat.is_le(M.levels(n), 23n) == True{} : Bool}) -> {Nat.is_le(Nat.mul(SC.length(A.Block, SC.replicate(A.Block, n, SG.zero())), 256n), SC.pow2(Nat.add(8n, M.levels(n)))) == True{} : Bool}:
  +k = M.levels(n)
  %Equal.sym(Nat, SC.length(A.Block, SC.replicate(A.Block, n, SG.zero())), n, LL.length_replicate(A.Block, n, SG.zero())) : {Nat.is_le(Nat.mul(_, 256n), SC.pow2(Nat.add(8n, k))) == True{} : Bool}
  %d8(SC.pow2(k)) : {Nat.is_le(Nat.mul(n, 256n), _) == True{} : Bool}
  AR2.mul_le(n, SC.pow2(k), 256n, levels_ok(n, h))

def depth_lt(+n: Nat, +h: {Nat.is_le(M.levels(n), 23n) == True{} : Bool}) -> {Nat.is_lt(Nat.add(8n, M.levels(n)), 32n) == True{} : Bool}:
  N.le_lt_succ(M.levels(n), 23n, h)

# ---------------------------------------------------------------- the passes on the first blocks

def q2(+q: Nat, +sl: Nat, +hq: {q == Nat.mul(4n, sl) : Nat}, +hsl: {Nat.is_le(2n, sl) == True{} : Bool}) -> {Nat.is_le(2n, q) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_le(2n, z) == True{} : Bool}, Nat.mul(4n, sl), q, Equal.sym(Nat, q, Nat.mul(4n, sl), hq), N.le_trans(2n, sl, Nat.mul(4n, sl), hsl, N.le_add_right(sl, Nat.mul(3n, sl))))

def fill_eq(+d: Nat, +t: Nat, +p: Nat, +q: Nat, +sl: Nat, +mm: Nat, +hh: List<&2, U32>, +z: List<&2, A.Block>, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hc: {Nat.is_le(Nat.mul(SC.length(A.Block, z), 256n), SC.pow2(d)) == True{} : Bool}, +hlen: {SC.length(A.Block, z) == Nat.mul(p, q) : Nat}, +hq: {q == Nat.mul(4n, sl) : Nat}, +hp: {Nat.is_le(1n, p) == True{} : Bool}, +hsl: {Nat.is_le(2n, sl) == True{} : Bool}) -> {I.passes_go(t, 0n, p, q, sl, mm, t, I.init_go(p, 0n, q, hh, AR.thaw(U32, MEM.mt(d, z)))) == AR.thaw(U32, MEM.mt(d, SA.passes_go(t, 0n, p, q, sl, mm, t, SA.init_go(p, 0n, q, hh, z)))) : Array<U32>}:
  +m1 = SA.init_go(p, 0n, q, hh, z)
  +e = R.init_len(p, 0n, q, hh, z)
  %Equal.sym(Array<U32>, I.init_go(p, 0n, q, hh, AR.thaw(U32, MEM.mt(d, z))), AR.thaw(U32, MEM.mt(d, m1)), R.init_eq(d, p, 0n, p, q, hh, z, hd, hc, hlen, q2(q, sl, hq, hsl), N.le_refl(p))) : {I.passes_go(t, 0n, p, q, sl, mm, t, _) == AR.thaw(U32, MEM.mt(d, SA.passes_go(t, 0n, p, q, sl, mm, t, m1))) : Array<U32>}
  F.passes_eq(d, t, 0n, p, q, sl, mm, t, m1, hd, F.keep_c(d, z, m1, e, hc), F.keep_len(z, m1, Nat.mul(p, q), e, hlen), hq, hp, hsl)

# ---------------------------------------------------------------- the tag

def tail_i(+tl: Nat, +p: Nat, +q: Nat, a: Array<U32>) -> List<&2, U32>:
  I.hprime(tl, I.block_bytes(I.final_go(Nat.sub(p, 1n), 0n, q, G.zero(), M.get(Nat.sub(q, 1n), a))))

def tail_s(+tl: Nat, +p: Nat, +q: Nat, +mem: List<&2, A.Block>) -> List<&2, U32>:
  SA.hprime(tl, SA.block_bytes(SA.final_go(Nat.sub(p, 1n), 0n, q, SG.zero(), SA.get(mem, Nat.sub(q, 1n)), mem)))

def tail_eq(+d: Nat, +tl: Nat, +p: Nat, +q: Nat, +mem: List<&2, A.Block>, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hc: {Nat.is_le(Nat.mul(SC.length(A.Block, mem), 256n), SC.pow2(d)) == True{} : Bool}, +hlen: {SC.length(A.Block, mem) == Nat.mul(p, q) : Nat}, +hp: {Nat.is_le(1n, p) == True{} : Bool}, +hq1: {Nat.is_le(1n, q) == True{} : Bool}) -> {tail_i(tl, p, q, AR.thaw(U32, MEM.mt(d, mem))) == tail_s(tl, p, q, mem) : List<&2, U32>}:
  +b = SA.get(mem, Nat.sub(q, 1n))
  +c = SA.final_go(Nat.sub(p, 1n), 0n, q, SG.zero(), b, mem)
  +hb = F.lt_len(Nat.sub(q, 1n), mem, p, q, hlen, N.lt_le_trans(Nat.sub(q, 1n), q, Nat.mul(p, q), F.sub1_lt(q, hq1), F.le_mul_left(p, q, hp)))
  -ar = AR.thaw(U32, MEM.mt(d, mem))
  %Equal.sym(Array<U32> & A.Block, M.get(Nat.sub(q, 1n), ar), (ar, b), MEM.get_block(d, mem, Nat.sub(q, 1n), hd, hc, hb)) : {I.hprime(tl, I.block_bytes(I.final_go(Nat.sub(p, 1n), 0n, q, G.zero(), _))) == tail_s(tl, p, q, mem) : List<&2, U32>}
  %Equal.sym(A.Block, G.zero(), SG.zero(), BL.zero_correct()) : {I.hprime(tl, I.block_bytes(I.final_go(Nat.sub(p, 1n), 0n, q, _, (ar, b)))) == tail_s(tl, p, q, mem) : List<&2, U32>}
  %Equal.sym(A.Block, I.final_go(Nat.sub(p, 1n), 0n, q, SG.zero(), (ar, b)), c, R.final_eq(d, Nat.sub(p, 1n), 0n, p, q, SG.zero(), b, mem, hd, hc, hlen, hq1, F.sub1_lt(p, hp))) : {I.hprime(tl, I.block_bytes(_)) == tail_s(tl, p, q, mem) : List<&2, U32>}
  Equal.trans(List<&2, U32>, I.hprime(tl, I.block_bytes(c)), I.hprime(tl, SA.block_bytes(c)), SA.hprime(tl, SA.block_bytes(c)),
    Equal.cong(List<&2, U32>, List<&2, U32>, x => I.hprime(tl, x), I.block_bytes(c), SA.block_bytes(c), HS.block_bytes_eq(c)),
    HS.hprime_eq(tl, SA.block_bytes(c)))

# ---------------------------------------------------------------- Argon2id

def valid_p1(+pw: List<&2, U32>, +salt: List<&2, U32>, +key: List<&2, U32>, +ad: List<&2, U32>, +t: Nat, +m: Nat, +p: Nat, +tl: Nat, +hv: {SA.valid(pw, salt, key, ad, t, m, p, tl) == True{} : Bool}) -> {Nat.is_le(1n, p) == True{} : Bool}:
  +a1 = Bool.and(Nat.is_le(1n, p), Nat.is_le(p, 16777215n))
  +a2 = Bool.and(Nat.is_le(4n, tl), Nat.is_le(tl, 4294967295n))
  +b1 = Bool.and(Nat.is_le(Nat.mul(8n, p), m), Nat.is_le(m, 4294967295n))
  +b2 = Bool.and(Nat.is_le(1n, t), Nat.is_le(t, 4294967295n))
  +cs = Bool.and(Bool.and(Nat.is_le(8n, SA.len(salt)), Nat.is_le(SA.len(salt), 4294967295n)), Bool.and(Nat.is_le(SA.len(pw), 4294967295n), Bool.and(Nat.is_le(SA.len(key), 4294967295n), Nat.is_le(SA.len(ad), 4294967295n))))
  +ha = L.and_left(Bool.and(a1, a2), Bool.and(Bool.and(b1, b2), cs), hv)
  +hb = L.and_right(Bool.and(a1, a2), Bool.and(Bool.and(b1, b2), cs), hv)
  L.and_left(Nat.is_le(1n, p), Nat.is_le(p, 16777215n), L.and_left(a1, a2, ha))

def valid_p8(+pw: List<&2, U32>, +salt: List<&2, U32>, +key: List<&2, U32>, +ad: List<&2, U32>, +t: Nat, +m: Nat, +p: Nat, +tl: Nat, +hv: {SA.valid(pw, salt, key, ad, t, m, p, tl) == True{} : Bool}) -> {Nat.is_le(Nat.mul(8n, p), m) == True{} : Bool}:
  +a1 = Bool.and(Nat.is_le(1n, p), Nat.is_le(p, 16777215n))
  +a2 = Bool.and(Nat.is_le(4n, tl), Nat.is_le(tl, 4294967295n))
  +b1 = Bool.and(Nat.is_le(Nat.mul(8n, p), m), Nat.is_le(m, 4294967295n))
  +b2 = Bool.and(Nat.is_le(1n, t), Nat.is_le(t, 4294967295n))
  +cs = Bool.and(Bool.and(Nat.is_le(8n, SA.len(salt)), Nat.is_le(SA.len(salt), 4294967295n)), Bool.and(Nat.is_le(SA.len(pw), 4294967295n), Bool.and(Nat.is_le(SA.len(key), 4294967295n), Nat.is_le(SA.len(ad), 4294967295n))))
  +ha = L.and_left(Bool.and(a1, a2), Bool.and(Bool.and(b1, b2), cs), hv)
  +hb = L.and_right(Bool.and(a1, a2), Bool.and(Bool.and(b1, b2), cs), hv)
  L.and_left(Nat.is_le(Nat.mul(8n, p), m), Nat.is_le(m, 4294967295n), L.and_left(b1, b2, L.and_left(Bool.and(b1, b2), cs, hb)))

def run_body(+pw: List<&2, U32>, +salt: List<&2, U32>, +key: List<&2, U32>, +ad: List<&2, U32>, +t: Nat, +m: Nat, +p: Nat, +tl: Nat, +hp: {Nat.is_le(1n, p) == True{} : Bool}, +h8: {Nat.is_le(Nat.mul(8n, p), m) == True{} : Bool}, +hf: {I.fits(m, p) == True{} : Bool}) -> {I.run(pw, salt, key, ad, t, m, p, tl) == SA.run(pw, salt, key, ad, t, m, p, tl) : List<&2, U32>}:
  +mm = I.blocks(m, p)
  +q = Nat.div(mm, p)
  +sl = Nat.div(q, 4n)
  +k = M.levels(mm)
  +d = Nat.add(8n, k)
  +z = SC.replicate(A.Block, mm, SG.zero())
  +hi = I.h0(p, tl, m, t, pw, salt, key, ad)
  +hs = SA.h0(p, tl, m, t, pw, salt, key, ad)
  +hd = depth_lt(mm, hf)
  +hc = cap(mm, hf)
  +hlz = LL.length_replicate(A.Block, mm, SG.zero())
  +hc0 = L.subst(Nat, x => {Nat.is_le(Nat.mul(x, 256n), SC.pow2(d)) == True{} : Bool}, SC.length(A.Block, z), mm, hlz, hc)
  +hlen0 = Equal.trans(Nat, SC.length(A.Block, z), mm, Nat.mul(p, q), hlz, hlen(m, p, hp))
  +hq0 = hq(m, p, hp)
  +hsl = L.subst(Nat, x => {Nat.is_le(2n, x) == True{} : Bool}, X(m, p), sl, Equal.sym(Nat, sl, X(m, p), sl_eq(m, p, hp)), x_ge2(m, p, hp, h8))
  +hq1 = N.le_trans(1n, 2n, q, {==}, q2(q, sl, hq0, hsl))
  +m2 = SA.passes_go(t, 0n, p, q, sl, mm, t, SA.init_go(p, 0n, q, hs, z))
  +e2 = Equal.trans(Nat, SC.length(A.Block, m2), SC.length(A.Block, SA.init_go(p, 0n, q, hs, z)), SC.length(A.Block, z), F.passes_len(t, 0n, p, q, sl, mm, t, SA.init_go(p, 0n, q, hs, z)), R.init_len(p, 0n, q, hs, z))
  -goal = SA.run(pw, salt, key, ad, t, m, p, tl)
  %Equal.sym(Array<U32>, Array.new(U32, d, 0), AR.thaw(U32, MEM.mt(d, z)), MEM.new_mem(d, mm, hc0)) : {tail_i(tl, p, q, I.passes_go(t, 0n, p, q, sl, mm, t, I.init_go(p, 0n, q, hi, _))) == goal : List<&2, U32>}
  %Equal.sym(List<&2, U32>, hi, hs, HS.h0_eq(p, tl, m, t, pw, salt, key, ad)) : {tail_i(tl, p, q, I.passes_go(t, 0n, p, q, sl, mm, t, I.init_go(p, 0n, q, _, AR.thaw(U32, MEM.mt(d, z))))) == goal : List<&2, U32>}
  %Equal.sym(Array<U32>, I.passes_go(t, 0n, p, q, sl, mm, t, I.init_go(p, 0n, q, hs, AR.thaw(U32, MEM.mt(d, z)))), AR.thaw(U32, MEM.mt(d, m2)), fill_eq(d, t, p, q, sl, mm, hs, z, hd, hc, hlen0, hq0, hp, hsl)) : {tail_i(tl, p, q, _) == goal : List<&2, U32>}
  tail_eq(d, tl, p, q, m2, hd, F.keep_c(d, z, m2, e2, hc), F.keep_len(z, m2, Nat.mul(p, q), e2, hlen0), hp, hq1)

def run_eq(+pw: List<&2, U32>, +salt: List<&2, U32>, +key: List<&2, U32>, +ad: List<&2, U32>, +t: Nat, +m: Nat, +p: Nat, +tl: Nat, +hv: {SA.valid(pw, salt, key, ad, t, m, p, tl) == True{} : Bool}, +hf: {I.fits(m, p) == True{} : Bool}) -> {I.run(pw, salt, key, ad, t, m, p, tl) == SA.run(pw, salt, key, ad, t, m, p, tl) : List<&2, U32>}:
  run_body(pw, salt, key, ad, t, m, p, tl, valid_p1(pw, salt, key, ad, t, m, p, tl, hv), valid_p8(pw, salt, key, ad, t, m, p, tl, hv), hf)

def checked_eq(+ok: Bool, +pw: List<&2, U32>, +salt: List<&2, U32>, +key: List<&2, U32>, +ad: List<&2, U32>, +t: Nat, +m: Nat, +p: Nat, +tl: Nat, +e: {SA.valid(pw, salt, key, ad, t, m, p, tl) == ok : Bool}, +hf: {I.fits(m, p) == True{} : Bool}) -> {I.checked(ok, pw, salt, key, ad, t, m, p, tl) == SA.checked(ok, pw, salt, key, ad, t, m, p, tl) : Maybe<&2, List<&2, U32>>}:
  match ok:
    case False{}:
      {==}
    case True{}:
      Equal.cong(List<&2, U32>, Maybe<&2, List<&2, U32>>, x => Some{x}, I.run(pw, salt, key, ad, t, m, p, tl), SA.run(pw, salt, key, ad, t, m, p, tl), run_eq(pw, salt, key, ad, t, m, p, tl, e, hf))

def valid_eq(+pw: List<&2, U32>, +salt: List<&2, U32>, +key: List<&2, U32>, +ad: List<&2, U32>, +t: Nat, +m: Nat, +p: Nat, +tl: Nat) -> {I.valid(pw, salt, key, ad, t, m, p, tl) == SA.valid(pw, salt, key, ad, t, m, p, tl) : Bool}:
  {==}

def and_true(+b: Bool) -> {Bool.and(b, True{}) == b : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# Argon2id: for every password, salt, secret, associated data and parameters
# whose memory fits this implementation (m' <= 2^23 blocks), the
# implementation's tag (or None) is the specification's.
def argon2id_correct(+pw: List<&2, U32>, +salt: List<&2, U32>, +key: List<&2, U32>, +ad: List<&2, U32>, +t: Nat, +m: Nat, +p: Nat, +tl: Nat, +hf: {I.fits(m, p) == True{} : Bool}) -> {I.argon2id(pw, salt, key, ad, t, m, p, tl) == SA.argon2id(pw, salt, key, ad, t, m, p, tl) : Maybe<&2, List<&2, U32>>}:
  +v = SA.valid(pw, salt, key, ad, t, m, p, tl)
  -goal = SA.argon2id(pw, salt, key, ad, t, m, p, tl)
  %Equal.sym(Bool, I.fits(m, p), True{}, hf) : {I.checked(Bool.and(I.valid(pw, salt, key, ad, t, m, p, tl), _), pw, salt, key, ad, t, m, p, tl) == goal : Maybe<&2, List<&2, U32>>}
  %Equal.sym(Bool, I.valid(pw, salt, key, ad, t, m, p, tl), v, valid_eq(pw, salt, key, ad, t, m, p, tl)) : {I.checked(Bool.and(_, True{}), pw, salt, key, ad, t, m, p, tl) == goal : Maybe<&2, List<&2, U32>>}
  %Equal.sym(Bool, Bool.and(v, True{}), v, and_true(v)) : {I.checked(_, pw, salt, key, ad, t, m, p, tl) == goal : Maybe<&2, List<&2, U32>>}
  checked_eq(v, pw, salt, key, ad, t, m, p, tl, {==}, hf)
