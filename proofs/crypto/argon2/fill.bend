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
import ./index.bend as IX

# Filling the memory: every segment, slice, lane and pass of the
# implementation (on the packed array) equals the specification's (on the
# list of blocks), as the array thaw(mt(d, mem)) of the specification's list.

# ---------------------------------------------------------------- arithmetic

def mod_lt(+v: Nat, +q: Nat, +hq: {Nat.is_le(1n, q) == True{} : Bool}) -> {Nat.is_lt(Nat.mod(v, q), q) == True{} : Bool}:
  match q:
    case 0n:
      Empty.absurd({Nat.is_lt(Nat.mod(v, 0n), 0n) == True{} : Bool}, L.false_true(hq))
    case 1n+ +b:
      NR.dm_lt(b, v)

# a < p and b < q give a * q + b < p * q.
def lt_mul_add(+a: Nat, +p: Nat, +b: Nat, +q: Nat, +ha: {Nat.is_lt(a, p) == True{} : Bool}, +hb: {Nat.is_lt(b, q) == True{} : Bool}) -> {Nat.is_lt(Nat.add(Nat.mul(a, q), b), Nat.mul(p, q)) == True{} : Bool}:
  +h1 = N.lt_add_left(b, q, Nat.mul(a, q), hb)
  +h2 = AR2.mul_le(1n+a, p, q, N.lt_succ_le_succ(a, p, ha))
  N.lt_le_trans(Nat.add(Nat.mul(a, q), b), Nat.add(Nat.mul(a, q), q), Nat.mul(p, q), h1,
    L.subst(Nat, z => {Nat.is_le(z, Nat.mul(p, q)) == True{} : Bool}, Nat.mul(1n+a, q), Nat.add(Nat.mul(a, q), q), NA.add_comm(q, Nat.mul(a, q)), h2))

# s < 4 and idx < sl give s * sl + idx < 4 sl.
def seg_lt(+s: Nat, +sl: Nat, +idx: Nat, +hs: {Nat.is_lt(s, 4n) == True{} : Bool}, +hi: {Nat.is_lt(idx, sl) == True{} : Bool}) -> {Nat.is_lt(Nat.add(Nat.mul(s, sl), idx), Nat.mul(4n, sl)) == True{} : Bool}:
  lt_mul_add(s, 4n, idx, sl, hs, hi)

def le_of_lt(+a: Nat, +b: Nat, +h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(a, b) == True{} : Bool}:
  N.lt_le(a, b, h)

def other_le(+base: Nat, +z: Bool) -> {Nat.is_le(SA.area_other(base, z), base) == True{} : Bool}:
  match z:
    case True{}:
      AR2.sub_le2(base, 1n)
    case False{}:
      N.le_refl(base)

# The size of the reference area is below the base plus the index.
def area_le(+base: Nat, +idx: Nat, +same: Bool) -> {Nat.is_le(SA.area(base, idx, same), Nat.add(base, idx)) == True{} : Bool}:
  match same:
    case True{}:
      AR2.sub_le2(Nat.add(base, idx), 1n)
    case False{}:
      N.le_trans(SA.area_other(base, Nat.is_eq(idx, 0n)), base, Nat.add(base, idx), other_le(base, Nat.is_eq(idx, 0n)), N.le_add_right(base, idx))

# The base of the reference area plus the index stays below q = 4 sl.
def base_lt(+r0: Bool, +s: Nat, +sl: Nat, +idx: Nat, +hs: {Nat.is_lt(s, 4n) == True{} : Bool}, +hi: {Nat.is_lt(idx, sl) == True{} : Bool}) -> {Nat.is_lt(Nat.add(SA.area_base(r0, s, sl, Nat.mul(4n, sl)), idx), Nat.mul(4n, sl)) == True{} : Bool}:
  match r0:
    case True{}:
      seg_lt(s, sl, idx, hs, hi)
    case False{}:
      +q = Nat.mul(4n, sl)
      +hsq = N.le_trans(sl, Nat.add(sl, Nat.mul(3n, sl)), q, N.le_add_right(sl, Nat.mul(3n, sl)), N.le_refl(q))
      +e = N.sub_add(q, sl, hsq)
      +h1 = N.lt_add_left(idx, sl, Nat.sub(q, sl), hi)
      L.subst(Nat, z => {Nat.is_lt(Nat.add(Nat.sub(q, sl), idx), z) == True{} : Bool}, Nat.add(Nat.sub(q, sl), sl), q,
        Equal.trans(Nat, Nat.add(Nat.sub(q, sl), sl), Nat.add(sl, Nat.sub(q, sl)), q, NA.add_comm(Nat.sub(q, sl), sl), e), h1)

# ---------------------------------------------------------------- one block

def store_eq(+d: Nat, +mem: List<&2, A.Block>, +r0: Bool, +cur: Nat, +prev: A.Block, +refb: A.Block, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hc: {Nat.is_le(Nat.mul(SC.length(A.Block, mem), 256n), SC.pow2(d)) == True{} : Bool}, +hcur: {Nat.is_lt(cur, SC.length(A.Block, mem)) == True{} : Bool}) -> {I.store(r0, cur, prev, refb, AR.thaw(U32, MEM.mt(d, mem))) == AR.thaw(U32, MEM.mt(d, SA.store(r0, cur, prev, refb, mem))) : Array<U32>}:
  match r0:
    case True{}:
      %Equal.sym(A.Block, G.compress(prev, refb), SG.G(prev, refb), BL.compress_correct(prev, refb)) : {M.set(cur, _, AR.thaw(U32, MEM.mt(d, mem))) == AR.thaw(U32, MEM.mt(d, SA.set(mem, cur, SG.G(prev, refb)))) : Array<U32>}
      MEM.set_block(d, mem, cur, SG.G(prev, refb), hd, hc, hcur)
    case False{}:
      +old = SA.get(mem, cur)
      %Equal.sym(Array<U32> & A.Block, M.get(cur, AR.thaw(U32, MEM.mt(d, mem))), (AR.thaw(U32, MEM.mt(d, mem)), old), MEM.get_block(d, mem, cur, hd, hc, hcur)) : {I.store_xor(cur, prev, refb, _) == AR.thaw(U32, MEM.mt(d, SA.set(mem, cur, SG.xor(SG.G(prev, refb), old)))) : Array<U32>}
      %Equal.sym(A.Block, G.compress_xor(prev, refb, old), SG.xor(SG.G(prev, refb), old), BL.compress_xor_correct(prev, refb, old)) : {M.set(cur, _, AR.thaw(U32, MEM.mt(d, mem))) == AR.thaw(U32, MEM.mt(d, SA.set(mem, cur, SG.xor(SG.G(prev, refb), old)))) : Array<U32>}
      MEM.set_block(d, mem, cur, SG.xor(SG.G(prev, refb), old), hd, hc, hcur)

def store_len(+r0: Bool, +cur: Nat, +prev: A.Block, +refb: A.Block, +mem: List<&2, A.Block>) -> {SC.length(A.Block, SA.store(r0, cur, prev, refb, mem)) == SC.length(A.Block, mem) : Nat}:
  match r0:
    case True{}:
      LL.length_update(A.Block, mem, cur, SG.G(prev, refb))
    case False{}:
      LL.length_update(A.Block, mem, cur, SG.xor(SG.G(prev, refb), SA.get(mem, cur)))

# The reference block index from the pseudo-random lane pr, as the implementation computes it.
def ixi(+r0: Bool, +s: Nat, +l: Nat, +idx: Nat, +p: Nat, +q: Nat, +sl: Nat, +pr: T.Lane) -> Nat:
  +rl = I.ref_lane(Bool.and(r0, Nat.is_eq(s, 0n)), l, I.hi(pr), p)
  +w = I.area(I.area_base(r0, s, sl, q), idx, Nat.is_eq(rl, l))
  Nat.add(Nat.mul(rl, q), Nat.mod(Nat.add(I.start(r0, s, sl), I.rel(w, G.lo(pr))), q))

# The same after the reference lane, and as the specification computes it.
def ixi_mid(+r0: Bool, +s: Nat, +l: Nat, +idx: Nat, +q: Nat, +sl: Nat, +pr: T.Lane, +rl: Nat) -> Nat:
  Nat.add(Nat.mul(rl, q), Nat.mod(Nat.add(I.start(r0, s, sl), I.rel(I.area(I.area_base(r0, s, sl, q), idx, Nat.is_eq(rl, l)), G.lo(pr))), q))

def ixs_mid(+r0: Bool, +s: Nat, +l: Nat, +idx: Nat, +q: Nat, +sl: Nat, +pr: T.Lane, +rl: Nat) -> Nat:
  Nat.add(Nat.mul(rl, q), Nat.mod(Nat.add(SA.start(r0, s, sl), SA.rel(SA.area(SA.area_base(r0, s, sl, q), idx, Nat.is_eq(rl, l)), SA.lo(pr))), q))

def ixs(+r0: Bool, +s: Nat, +l: Nat, +idx: Nat, +p: Nat, +q: Nat, +sl: Nat, +pr: T.Lane) -> Nat:
  +rl = SA.ref_lane(Bool.and(r0, Nat.is_eq(s, 0n)), l, SA.hi(pr), p)
  +w = SA.area(SA.area_base(r0, s, sl, q), idx, Nat.is_eq(rl, l))
  Nat.add(Nat.mul(rl, q), Nat.mod(Nat.add(SA.start(r0, s, sl), SA.rel(w, SA.lo(pr))), q))

def le_mul256(+n: Nat) -> {Nat.is_le(n, Nat.mul(n, 256n)) == True{} : Bool}:
  %Equal.sym(Nat, Nat.mul(n, 256n), Nat.mul(256n, n), NA.mul_comm(n, 256n)) : {Nat.is_le(n, _) == True{} : Bool}
  N.le_add_right(n, Nat.mul(255n, n))

# |W| < 2^d.
def area_bound(+d: Nat, +n: Nat, +r0: Bool, +s: Nat, +sl: Nat, +q: Nat, +idx: Nat, +same: Bool, +hq: {q == Nat.mul(4n, sl) : Nat}, +hs: {Nat.is_lt(s, 4n) == True{} : Bool}, +hi: {Nat.is_lt(idx, sl) == True{} : Bool}, +hqn: {Nat.is_le(q, n) == True{} : Bool}, +hn: {Nat.is_le(Nat.mul(n, 256n), SC.pow2(d)) == True{} : Bool}) -> {Nat.is_lt(SA.area(SA.area_base(r0, s, sl, q), idx, same), SC.pow2(d)) == True{} : Bool}:
  +base = SA.area_base(r0, s, sl, q)
  +h1 = area_le(base, idx, same)
  +h2 = L.subst(Nat, z => {Nat.is_lt(Nat.add(SA.area_base(r0, s, sl, z), idx), z) == True{} : Bool}, Nat.mul(4n, sl), q, Equal.sym(Nat, q, Nat.mul(4n, sl), hq), base_lt(r0, s, sl, idx, hs, hi))
  +h3 = N.le_trans(n, Nat.mul(n, 256n), SC.pow2(d), le_mul256(n), hn)
  N.le_lt_trans(SA.area(base, idx, same), Nat.add(base, idx), SC.pow2(d), h1, N.lt_le_trans(Nat.add(base, idx), q, SC.pow2(d), h2, N.le_trans(q, n, SC.pow2(d), hqn, h3)))

def mid_eq(+d: Nat, +n: Nat, +r0: Bool, +s: Nat, +l: Nat, +idx: Nat, +q: Nat, +sl: Nat, +pr: T.Lane, +rl: Nat, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hq: {q == Nat.mul(4n, sl) : Nat}, +hs: {Nat.is_lt(s, 4n) == True{} : Bool}, +hi: {Nat.is_lt(idx, sl) == True{} : Bool}, +hqn: {Nat.is_le(q, n) == True{} : Bool}, +hn: {Nat.is_le(Nat.mul(n, 256n), SC.pow2(d)) == True{} : Bool}) -> {ixi_mid(r0, s, l, idx, q, sl, pr, rl) == ixs_mid(r0, s, l, idx, q, sl, pr, rl) : Nat}:
  +same = Nat.is_eq(rl, l)
  +wi = I.area(I.area_base(r0, s, sl, q), idx, same)
  +ws = SA.area(SA.area_base(r0, s, sl, q), idx, same)
  +ew = Equal.trans(Nat, wi, I.area(SA.area_base(r0, s, sl, q), idx, same), ws,
    Equal.cong(Nat, Nat, z => I.area(z, idx, same), I.area_base(r0, s, sl, q), SA.area_base(r0, s, sl, q), IX.area_base_eq(r0, s, sl, q)),
    IX.area_eq(SA.area_base(r0, s, sl, q), idx, same))
  +erel = Equal.trans(Nat, I.rel(wi, G.lo(pr)), I.rel(ws, G.lo(pr)), SA.rel(ws, SA.lo(pr)),
    Equal.cong(Nat, Nat, z => I.rel(z, G.lo(pr)), wi, ws, ew),
    Equal.trans(Nat, I.rel(ws, G.lo(pr)), I.rel(ws, SA.lo(pr)), SA.rel(ws, SA.lo(pr)),
      Equal.cong(U32, Nat, z => I.rel(ws, z), G.lo(pr), SA.lo(pr), IX.lo_eq(pr)),
      IX.rel_eq(ws, SA.lo(pr), d, N.lt_le(d, 32n, hd), area_bound(d, n, r0, s, sl, q, idx, same, hq, hs, hi, hqn, hn))))
  Equal.trans(Nat, ixi_mid(r0, s, l, idx, q, sl, pr, rl), Nat.add(Nat.mul(rl, q), Nat.mod(Nat.add(SA.start(r0, s, sl), I.rel(wi, G.lo(pr))), q)), ixs_mid(r0, s, l, idx, q, sl, pr, rl),
    Equal.cong(Nat, Nat, z => Nat.add(Nat.mul(rl, q), Nat.mod(Nat.add(z, I.rel(wi, G.lo(pr))), q)), I.start(r0, s, sl), SA.start(r0, s, sl), IX.start_eq(r0, s, sl)),
    Equal.cong(Nat, Nat, z => Nat.add(Nat.mul(rl, q), Nat.mod(Nat.add(SA.start(r0, s, sl), z), q)), I.rel(wi, G.lo(pr)), SA.rel(ws, SA.lo(pr)), erel))

def ix_eq(+d: Nat, +n: Nat, +r0: Bool, +s: Nat, +l: Nat, +idx: Nat, +p: Nat, +q: Nat, +sl: Nat, +pr: T.Lane, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hq: {q == Nat.mul(4n, sl) : Nat}, +hs: {Nat.is_lt(s, 4n) == True{} : Bool}, +hi: {Nat.is_lt(idx, sl) == True{} : Bool}, +hqn: {Nat.is_le(q, n) == True{} : Bool}, +hn: {Nat.is_le(Nat.mul(n, 256n), SC.pow2(d)) == True{} : Bool}) -> {ixi(r0, s, l, idx, p, q, sl, pr) == ixs(r0, s, l, idx, p, q, sl, pr) : Nat}:
  +f = Bool.and(r0, Nat.is_eq(s, 0n))
  +rli = I.ref_lane(f, l, I.hi(pr), p)
  +rls = SA.ref_lane(f, l, SA.hi(pr), p)
  +erl = Equal.trans(Nat, rli, SA.ref_lane(f, l, I.hi(pr), p), rls,
    IX.ref_lane_eq(f, l, I.hi(pr), p),
    Equal.cong(U32, Nat, z => SA.ref_lane(f, l, z, p), I.hi(pr), SA.hi(pr), IX.hi_eq(pr)))
  Equal.trans(Nat, ixi_mid(r0, s, l, idx, q, sl, pr, rli), ixi_mid(r0, s, l, idx, q, sl, pr, rls), ixs_mid(r0, s, l, idx, q, sl, pr, rls),
    Equal.cong(Nat, Nat, z => ixi_mid(r0, s, l, idx, q, sl, pr, z), rli, rls, erl),
    mid_eq(d, n, r0, s, l, idx, q, sl, pr, rls, hd, hq, hs, hi, hqn, hn))

def ref_lane_lt(+f: Bool, +l: Nat, +j2: U32, +p: Nat, +hl: {Nat.is_lt(l, p) == True{} : Bool}, +hp: {Nat.is_le(1n, p) == True{} : Bool}) -> {Nat.is_lt(SA.ref_lane(f, l, j2, p), p) == True{} : Bool}:
  match f:
    case True{}:
      hl
    case False{}:
      mod_lt(U32.to_nat(j2), p, hp)

def q_pos(+q: Nat, +sl: Nat, +hq: {q == Nat.mul(4n, sl) : Nat}, +hsl: {Nat.is_le(1n, sl) == True{} : Bool}) -> {Nat.is_le(1n, q) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_le(1n, z) == True{} : Bool}, Nat.mul(4n, sl), q, Equal.sym(Nat, q, Nat.mul(4n, sl), hq), N.le_trans(1n, sl, Nat.mul(4n, sl), hsl, N.le_add_right(sl, Nat.mul(3n, sl))))

# The reference block is in the memory.
def ix_lt(+r0: Bool, +s: Nat, +l: Nat, +idx: Nat, +p: Nat, +q: Nat, +sl: Nat, +pr: T.Lane, +hl: {Nat.is_lt(l, p) == True{} : Bool}, +hp: {Nat.is_le(1n, p) == True{} : Bool}, +hq1: {Nat.is_le(1n, q) == True{} : Bool}) -> {Nat.is_lt(ixs(r0, s, l, idx, p, q, sl, pr), Nat.mul(p, q)) == True{} : Bool}:
  +rl = SA.ref_lane(Bool.and(r0, Nat.is_eq(s, 0n)), l, SA.hi(pr), p)
  lt_mul_add(rl, p, Nat.mod(Nat.add(SA.start(r0, s, sl), SA.rel(SA.area(SA.area_base(r0, s, sl, q), idx, Nat.is_eq(rl, l)), SA.lo(pr))), q), q, ref_lane_lt(Bool.and(r0, Nat.is_eq(s, 0n)), l, SA.hi(pr), p, hl, hp), mod_lt(Nat.add(SA.start(r0, s, sl), SA.rel(SA.area(SA.area_base(r0, s, sl, q), idx, Nat.is_eq(rl, l)), SA.lo(pr))), q, hq1))

def le_mul_left(+p: Nat, +q: Nat, +hp: {Nat.is_le(1n, p) == True{} : Bool}) -> {Nat.is_le(q, Nat.mul(p, q)) == True{} : Bool}:
  match p:
    case 0n:
      Empty.absurd({Nat.is_le(q, 0n) == True{} : Bool}, L.false_true(hp))
    case 1n+k:
      N.le_add_right(q, Nat.mul(k, q))

# One block of a segment.
def step_eq(+d: Nat, +mem: List<&2, A.Block>, +r: Nat, +l: Nat, +s: Nat, +idx: Nat, +p: Nat, +q: Nat, +sl: Nat, +cur: Nat, +indep: Bool, +addr: A.Block, +pb: A.Block, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hc: {Nat.is_le(Nat.mul(SC.length(A.Block, mem), 256n), SC.pow2(d)) == True{} : Bool}, +hlen: {SC.length(A.Block, mem) == Nat.mul(p, q) : Nat}, +hq: {q == Nat.mul(4n, sl) : Nat}, +hp: {Nat.is_le(1n, p) == True{} : Bool}, +hsl: {Nat.is_le(1n, sl) == True{} : Bool}, +hl: {Nat.is_lt(l, p) == True{} : Bool}, +hs: {Nat.is_lt(s, 4n) == True{} : Bool}, +hi: {Nat.is_lt(idx, sl) == True{} : Bool}, +hcur: {Nat.is_lt(cur, SC.length(A.Block, mem)) == True{} : Bool}) -> {I.step(r, l, s, idx, p, q, sl, cur, indep, addr, (AR.thaw(U32, MEM.mt(d, mem)), pb)) == AR.thaw(U32, MEM.mt(d, SA.step(r, l, s, idx, p, q, sl, cur, indep, addr, pb, mem))) : Array<U32>}:
  +r0 = Nat.is_eq(r, 0n)
  +pri = I.pick(indep, addr, idx, pb)
  +prs = SA.pick(indep, addr, idx, pb)
  +n = SC.length(A.Block, mem)
  +hq1 = q_pos(q, sl, hq, hsl)
  +hqn = L.subst(Nat, z => {Nat.is_le(q, z) == True{} : Bool}, Nat.mul(p, q), n, Equal.sym(Nat, n, Nat.mul(p, q), hlen), le_mul_left(p, q, hp))
  +ei = Equal.trans(Nat, ixi(r0, s, l, idx, p, q, sl, pri), ixi(r0, s, l, idx, p, q, sl, prs), ixs(r0, s, l, idx, p, q, sl, prs),
    Equal.cong(T.Lane, Nat, z => ixi(r0, s, l, idx, p, q, sl, z), pri, prs, IX.pick_eq(indep, addr, idx, pb)),
    ix_eq(d, n, r0, s, l, idx, p, q, sl, prs, hd, hq, hs, hi, hqn, hc))
  +ix = ixs(r0, s, l, idx, p, q, sl, prs)
  +hix = L.subst(Nat, z => {Nat.is_lt(ix, z) == True{} : Bool}, Nat.mul(p, q), n, Equal.sym(Nat, n, Nat.mul(p, q), hlen), ix_lt(r0, s, l, idx, p, q, sl, prs, hl, hp, hq1))
  %Equal.sym(Nat, ixi(r0, s, l, idx, p, q, sl, pri), ix, ei) : {I.with_ref(r0, cur, pb, M.get(_, AR.thaw(U32, MEM.mt(d, mem)))) == AR.thaw(U32, MEM.mt(d, SA.store(r0, cur, pb, SA.get(mem, ix), mem))) : Array<U32>}
  %Equal.sym(Array<U32> & A.Block, M.get(ix, AR.thaw(U32, MEM.mt(d, mem))), (AR.thaw(U32, MEM.mt(d, mem)), SA.get(mem, ix)), MEM.get_block(d, mem, ix, hd, hc, hix)) : {I.with_ref(r0, cur, pb, _) == AR.thaw(U32, MEM.mt(d, SA.store(r0, cur, pb, SA.get(mem, ix), mem))) : Array<U32>}
  store_eq(d, mem, r0, cur, pb, SA.get(mem, ix), hd, hc, hcur)

# ---------------------------------------------------------------- segments

def step_len(+r: Nat, +l: Nat, +s: Nat, +idx: Nat, +p: Nat, +q: Nat, +sl: Nat, +cur: Nat, +indep: Bool, +addr: A.Block, +pb: A.Block, +mem: List<&2, A.Block>) -> {SC.length(A.Block, SA.step(r, l, s, idx, p, q, sl, cur, indep, addr, pb, mem)) == SC.length(A.Block, mem) : Nat}:
  +r0 = Nat.is_eq(r, 0n)
  store_len(r0, cur, pb, SA.get(mem, ixs(r0, s, l, idx, p, q, sl, SA.pick(indep, addr, idx, pb))), mem)

def sub1_lt(+q: Nat, +hq1: {Nat.is_le(1n, q) == True{} : Bool}) -> {Nat.is_lt(Nat.sub(q, 1n), q) == True{} : Bool}:
  match q:
    case 0n:
      Empty.absurd({Nat.is_lt(Nat.sub(0n, 1n), 0n) == True{} : Bool}, L.false_true(hq1))
    case 1n+ +k:
      %Equal.sym(Nat, Nat.sub(k, 0n), k, N.sub_zero(k)) : {Nat.is_lt(_, 1n+k) == True{} : Bool}
      N.lt_succ(k)

# The previous block is in the memory.
def prev_lt(+l: Nat, +p: Nat, +q: Nat, +j: Nat, +b: Bool, +hl: {Nat.is_lt(l, p) == True{} : Bool}, +hj: {Nat.is_lt(j, q) == True{} : Bool}, +hq1: {Nat.is_le(1n, q) == True{} : Bool}) -> {Nat.is_lt(SA.prev_index(l, q, j, b), Nat.mul(p, q)) == True{} : Bool}:
  match b:
    case True{}:
      lt_mul_add(l, p, Nat.sub(q, 1n), q, hl, sub1_lt(q, hq1))
    case False{}:
      N.le_lt_trans(Nat.sub(Nat.add(Nat.mul(l, q), j), 1n), Nat.add(Nat.mul(l, q), j), Nat.mul(p, q), AR2.sub_le2(Nat.add(Nat.mul(l, q), j), 1n), lt_mul_add(l, p, j, q, hl, hj))

def lt_of_add_succ(+a: Nat, +r: Nat, +n: Nat, +h: {Nat.is_le(Nat.add(a, 1n+r), n) == True{} : Bool}) -> {Nat.is_lt(a, n) == True{} : Bool}:
  N.lt_le_trans(a, Nat.add(a, 1n+r), n, MEM.lt_add_succ(a, r), h)

def le_shift(+a: Nat, +r: Nat, +n: Nat, +h: {Nat.is_le(Nat.add(a, 1n+r), n) == True{} : Bool}) -> {Nat.is_le(Nat.add(Nat.add(a, 1n), r), n) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_le(z, n) == True{} : Bool}, Nat.add(a, 1n+r), Nat.add(Nat.add(a, 1n), r), Equal.sym(Nat, Nat.add(Nat.add(a, 1n), r), Nat.add(a, 1n+r), MEM.add_one_assoc(a, r)), h)

def lt_q(+q: Nat, +sl: Nat, +x: Nat, +hq: {q == Nat.mul(4n, sl) : Nat}, +h: {Nat.is_lt(x, Nat.mul(4n, sl)) == True{} : Bool}) -> {Nat.is_lt(x, q) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_lt(x, z) == True{} : Bool}, Nat.mul(4n, sl), q, Equal.sym(Nat, q, Nat.mul(4n, sl), hq), h)

def lt_len(+x: Nat, +mem: List<&2, A.Block>, +p: Nat, +q: Nat, +hlen: {SC.length(A.Block, mem) == Nat.mul(p, q) : Nat}, +h: {Nat.is_lt(x, Nat.mul(p, q)) == True{} : Bool}) -> {Nat.is_lt(x, SC.length(A.Block, mem)) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_lt(x, z) == True{} : Bool}, Nat.mul(p, q), SC.length(A.Block, mem), Equal.sym(Nat, SC.length(A.Block, mem), Nat.mul(p, q), hlen), h)

def seg_len(+n: Nat, +idx: Nat, +first: Bool, +addr: A.Block, +mem: List<&2, A.Block>, +r: Nat, +l: Nat, +s: Nat, +p: Nat, +q: Nat, +sl: Nat, +mm: Nat, +t: Nat, +indep: Bool) -> {SC.length(A.Block, SA.seg_go(n, idx, first, addr, mem, r, l, s, p, q, sl, mm, t, indep)) == SC.length(A.Block, mem) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+ +rest:
      +a2 = SA.regen(Bool.and(indep, Bool.or(first, Nat.is_eq(Nat.mod(idx, 128n), 0n))), addr, r, l, s, mm, t, idx)
      +j = Nat.add(Nat.mul(s, sl), idx)
      +m2 = SA.step(r, l, s, idx, p, q, sl, Nat.add(Nat.mul(l, q), j), indep, a2, SA.get(mem, SA.prev_index(l, q, j, Nat.is_eq(j, 0n))), mem)
      Equal.trans(Nat, SC.length(A.Block, SA.seg_go(rest, Nat.add(idx, 1n), False{}, a2, m2, r, l, s, p, q, sl, mm, t, indep)), SC.length(A.Block, m2), SC.length(A.Block, mem),
        seg_len(rest, Nat.add(idx, 1n), False{}, a2, m2, r, l, s, p, q, sl, mm, t, indep),
        step_len(r, l, s, idx, p, q, sl, Nat.add(Nat.mul(l, q), j), indep, a2, SA.get(mem, SA.prev_index(l, q, j, Nat.is_eq(j, 0n))), mem))

# Positions idx .. idx + n - 1 of a segment.
def seg_eq(+d: Nat, +n: Nat, +idx: Nat, +first: Bool, +addr: A.Block, +mem: List<&2, A.Block>, +r: Nat, +l: Nat, +s: Nat, +p: Nat, +q: Nat, +sl: Nat, +mm: Nat, +t: Nat, +indep: Bool, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hc: {Nat.is_le(Nat.mul(SC.length(A.Block, mem), 256n), SC.pow2(d)) == True{} : Bool}, +hlen: {SC.length(A.Block, mem) == Nat.mul(p, q) : Nat}, +hq: {q == Nat.mul(4n, sl) : Nat}, +hp: {Nat.is_le(1n, p) == True{} : Bool}, +hsl: {Nat.is_le(1n, sl) == True{} : Bool}, +hl: {Nat.is_lt(l, p) == True{} : Bool}, +hs: {Nat.is_lt(s, 4n) == True{} : Bool}, +hidx: {Nat.is_le(Nat.add(idx, n), sl) == True{} : Bool}) -> {I.seg_go(n, idx, first, addr, AR.thaw(U32, MEM.mt(d, mem)), r, l, s, p, q, sl, mm, t, indep) == AR.thaw(U32, MEM.mt(d, SA.seg_go(n, idx, first, addr, mem, r, l, s, p, q, sl, mm, t, indep))) : Array<U32>}:
  match n:
    case 0n:
      {==}
    case 1n+ +rest:
      +need = Bool.and(indep, Bool.or(first, Nat.is_eq(Nat.mod(idx, 128n), 0n)))
      +a2i = I.regen(need, addr, r, l, s, mm, t, idx)
      +a2s = SA.regen(need, addr, r, l, s, mm, t, idx)
      +j = Nat.add(Nat.mul(s, sl), idx)
      +cur = Nat.add(Nat.mul(l, q), j)
      +b0 = Nat.is_eq(j, 0n)
      +pvi = I.prev_index(l, q, j, b0)
      +pvs = SA.prev_index(l, q, j, b0)
      +hi = lt_of_add_succ(idx, rest, sl, hidx)
      +hq1 = q_pos(q, sl, hq, hsl)
      +hj = lt_q(q, sl, j, hq, seg_lt(s, sl, idx, hs, hi))
      +hcur = lt_len(cur, mem, p, q, hlen, lt_mul_add(l, p, j, q, hl, hj))
      +hpv = lt_len(pvs, mem, p, q, hlen, prev_lt(l, p, q, j, b0, hl, hj, hq1))
      +pb = SA.get(mem, pvs)
      +m2 = SA.step(r, l, s, idx, p, q, sl, cur, indep, a2s, pb, mem)
      +hl2 = step_len(r, l, s, idx, p, q, sl, cur, indep, a2s, pb, mem)
      +hc2 = L.subst(Nat, z => {Nat.is_le(Nat.mul(z, 256n), SC.pow2(d)) == True{} : Bool}, SC.length(A.Block, mem), SC.length(A.Block, m2), Equal.sym(Nat, SC.length(A.Block, m2), SC.length(A.Block, mem), hl2), hc)
      +hlen2 = Equal.trans(Nat, SC.length(A.Block, m2), SC.length(A.Block, mem), Nat.mul(p, q), hl2, hlen)
      -ar = AR.thaw(U32, MEM.mt(d, mem))
      -goal = AR.thaw(U32, MEM.mt(d, SA.seg_go(rest, Nat.add(idx, 1n), False{}, a2s, m2, r, l, s, p, q, sl, mm, t, indep)))
      %Equal.sym(A.Block, a2i, a2s, IX.regen_eq(need, addr, r, l, s, mm, t, idx)) : {I.seg_go(rest, Nat.add(idx, 1n), False{}, _, I.step(r, l, s, idx, p, q, sl, cur, indep, _, M.get(pvi, ar)), r, l, s, p, q, sl, mm, t, indep) == goal : Array<U32>}
      %Equal.sym(Nat, pvi, pvs, IX.prev_index_eq(l, q, j, b0)) : {I.seg_go(rest, Nat.add(idx, 1n), False{}, a2s, I.step(r, l, s, idx, p, q, sl, cur, indep, a2s, M.get(_, ar)), r, l, s, p, q, sl, mm, t, indep) == goal : Array<U32>}
      %Equal.sym(Array<U32> & A.Block, M.get(pvs, ar), (ar, pb), MEM.get_block(d, mem, pvs, hd, hc, hpv)) : {I.seg_go(rest, Nat.add(idx, 1n), False{}, a2s, I.step(r, l, s, idx, p, q, sl, cur, indep, a2s, _), r, l, s, p, q, sl, mm, t, indep) == goal : Array<U32>}
      %Equal.sym(Array<U32>, I.step(r, l, s, idx, p, q, sl, cur, indep, a2s, (ar, pb)), AR.thaw(U32, MEM.mt(d, m2)), step_eq(d, mem, r, l, s, idx, p, q, sl, cur, indep, a2s, pb, hd, hc, hlen, hq, hp, hsl, hl, hs, hi, hcur)) : {I.seg_go(rest, Nat.add(idx, 1n), False{}, a2s, _, r, l, s, p, q, sl, mm, t, indep) == goal : Array<U32>}
      seg_eq(d, rest, Nat.add(idx, 1n), False{}, a2s, m2, r, l, s, p, q, sl, mm, t, indep, hd, hc2, hlen2, hq, hp, hsl, hl, hs, le_shift(idx, rest, sl, hidx))
