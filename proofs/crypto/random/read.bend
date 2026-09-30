import Base
import ../../../src/math/u64.bend as W
import ../../../src/math/w64.bend as X
import ../../../src/math/random/chacha8.bend as C8
import ../../../src/crypto/random.bend as CR
import ../../../spec/math/random/source.bend as SRC
import ../../../spec/crypto/random.bend as SCR
import ../../../spec/lib/common.bend as CM
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/u32.bend as U
import ../../lib/list.bend as LL
import ../../lib/array.bend as AR
import ../../math/random/ashuffle.bend as AS
import ../../math/random/lshuffle.bend as LS

# read_words (Go's Read into a word buffer): the loop rw writes the words of
# the outputs one after another (rw_fl: it is fl, a Base Array.set per word,
# of the list of those words); on thaw(t) of a perfect tree each Array.set
# is proofs/lib/array.bend's update of t's slots (fl_thaw), and the slots
# before the written ones are kept while the written ones are the words
# (fl_take).

# write the words ws into slots j, j + 1, ... of a
def fl(ws: List<&2, U32>, +j: Nat, a: Array<U32>) -> Array<U32>:
  match ws:
    case Nil{}:
      a
    case Con{w, rest}:
      fl(rest, 1n+j, Array.set(U32, a, U32.from_nat(j), w))

# rw writes the words of the output in r and of k more outputs
def rw_fl(k: Nat, +j: Nat, a: Array<U32>, r: W.U64 & C8.ChaCha8) -> {CR.rw(k, j, a, r) == (fl(SCR.words(Con{SRC.fst64(C8.ChaCha8, r), SRC.outputs(~C8.ChaCha8, ~C8.next, k, SRC.snd64(C8.ChaCha8, r))}), j, a), SCR.after(k, SRC.snd64(C8.ChaCha8, r))) : Array<U32> & C8.ChaCha8}:
  match k r:
    case 0n Tuple{+x, +c}:
      {==}
    case 1n+m Tuple{+x, +c}:
      rw_fl(m, 2n+j, CR.put2(a, j, x), C8.next(c))

# ---- fl on a perfect tree ----

def tfl(+d: Nat, ws: List<&2, U32>, +j: Nat, +t: AR.Tree<U32>) -> AR.Tree<U32>:
  match ws:
    case Nil{}:
      t
    case Con{+w, rest}:
      tfl(d, rest, 1n+j, AR.upd(U32, d, t, U32.to_nat(U32.from_nat(j)), w))

def tfl_perfect(+d: Nat, +ws: List<&2, U32>, +j: Nat, +t: AR.Tree<U32>, +pf: {AR.perfect(U32, d, t) == True{} : Bool}) -> {AR.perfect(U32, d, tfl(d, ws, j, t)) == True{} : Bool}:
  match ws:
    case Nil{}:
      pf
    case Con{+w, +rest}:
      tfl_perfect(d, rest, 1n+j, AR.upd(U32, d, t, U32.to_nat(U32.from_nat(j)), w), AR.upd_perfect(U32, d, t, U32.to_nat(U32.from_nat(j)), w, pf))

def fl_thaw(+d: Nat, +ws: List<&2, U32>, +j: Nat, +t: AR.Tree<U32>, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hk: {Nat.is_le(Nat.add(j, CM.length(U32, ws)), CM.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(U32, d, t) == True{} : Bool}) -> {fl(ws, j, AR.thaw(U32, t)) == AR.thaw(U32, tfl(d, ws, j, t)) : Array<U32>}:
  match ws:
    case Nil{}:
      {==}
    case Con{+w, +rest}:
      +jj = U32.to_nat(U32.from_nat(j))
      +hj = AS.idx_i(d, j, hd, LS.fill_bounds(d, j, CM.length(U32, rest), hk))
      +t2 = AR.upd(U32, d, t, jj, w)
      Equal.trans(Array<U32>, fl(rest, 1n+j, Array.set(U32, AR.thaw(U32, t), U32.from_nat(j), w)), fl(rest, 1n+j, AR.thaw(U32, t2)), AR.thaw(U32, tfl(d, rest, 1n+j, t2)),
        Equal.cong(Array<U32>, Array<U32>, z => fl(rest, 1n+j, z), Array.set(U32, AR.thaw(U32, t), U32.from_nat(j), w), AR.thaw(U32, t2),
          AR.set(U32, d, t, U32.from_nat(j), w, AS.at(U32, t, jj), hd, hj, AS.at_nth(U32, d, t, jj, pf, hj), pf)),
        fl_thaw(d, rest, 1n+j, t2, hd, LS.fill_next(d, j, CM.length(U32, rest), hk), AR.upd_perfect(U32, d, t, jj, w, pf)))

def take0(+xs: List<&2, U32>) -> {CM.take(U32, xs, 0n) == Nil{} : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      {==}

# j < length xs: the first j + 1 of xs with slot j set are the first j, then w
def take_upd(+xs: List<&2, U32>, +j: Nat, +w: U32, +h: {Nat.is_lt(j, CM.length(U32, xs)) == True{} : Bool}) -> {CM.take(U32, CM.update(U32, xs, j, w), 1n+j) == CM.append(U32, CM.take(U32, xs, j), [w]) : List<&2, U32>}:
  match xs j:
    case Nil{} _:
      Empty.absurd({CM.take(U32, CM.update(U32, Nil{}, j, w), 1n+j) == CM.append(U32, CM.take(U32, Nil{}, j), [w]) : List<&2, U32>}, N.lt_zero_absurd(j, h))
    case Con{+hd, +tl} 0n:
      LL.cons_cong(U32, w, CM.take(U32, tl, 0n), Nil{}, take0(tl))
    case Con{+hd, +tl} 1n+q:
      LL.cons_cong(U32, hd, CM.take(U32, CM.update(U32, tl, q, w), 1n+q), CM.append(U32, CM.take(U32, tl, q), [w]), take_upd(tl, q, w, h))

def add_shift(+j: Nat, +r: Nat) -> {Nat.add(j, 1n+r) == Nat.add(1n+j, r) : Nat}:
  Equal.trans(Nat, Nat.add(j, 1n+r), 1n+Nat.add(j, r), Nat.add(1n+j, r), N.add_succ(j, r), Equal.sym(Nat, Nat.add(1n+j, r), 1n+Nat.add(j, r), LS.succ_add(j, r)))

# the first j slots are kept and the next ones are ws
def fl_take(+d: Nat, +ws: List<&2, U32>, +j: Nat, +t: AR.Tree<U32>, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hk: {Nat.is_le(Nat.add(j, CM.length(U32, ws)), CM.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(U32, d, t) == True{} : Bool}) -> {CM.take(U32, AR.slots(U32, tfl(d, ws, j, t)), Nat.add(j, CM.length(U32, ws))) == CM.append(U32, CM.take(U32, AR.slots(U32, t), j), ws) : List<&2, U32>}:
  match ws:
    case Nil{}:
      +L0 = AR.slots(U32, t)
      %Equal.sym(Nat, Nat.add(j, 0n), j, N.add_zero(j)) : {CM.take(U32, L0, _) == CM.append(U32, CM.take(U32, L0, j), Nil{}) : List<&2, U32>}
      Equal.sym(List<&2, U32>, CM.append(U32, CM.take(U32, L0, j), Nil{}), CM.take(U32, L0, j), LL.append_nil(U32, CM.take(U32, L0, j)))
    case Con{+w, +rest}:
      +L0 = AR.slots(U32, t)
      +jj = U32.to_nat(U32.from_nat(j))
      +hjl = LS.fill_bounds(d, j, CM.length(U32, rest), hk)
      +hj = AS.idx_i(d, j, hd, hjl)
      +t2 = AR.upd(U32, d, t, jj, w)
      +ejj = U.to_nat_from_nat(j, d, N.lt_le(d, 32n, hd), hjl)
      +ih = fl_take(d, rest, 1n+j, t2, hd, LS.fill_next(d, j, CM.length(U32, rest), hk), AR.upd_perfect(U32, d, t, jj, w, pf))
      +hlen = L.subst(Nat, z => {Nat.is_lt(j, z) == True{} : Bool}, CM.pow2(d), CM.length(U32, L0), Equal.sym(Nat, CM.length(U32, L0), CM.pow2(d), AR.slots_length(U32, d, t, pf)), hjl)
      +s2 = L.subst(Nat, z => {AR.slots(U32, t2) == CM.update(U32, L0, z, w) : List<&2, U32>}, jj, j, ejj, AR.upd_slots(U32, d, t, jj, w, hj, pf))
      +e2 = Equal.trans(List<&2, U32>, CM.take(U32, AR.slots(U32, t2), 1n+j), CM.take(U32, CM.update(U32, L0, j, w), 1n+j), CM.append(U32, CM.take(U32, L0, j), [w]),
        Equal.cong(List<&2, U32>, List<&2, U32>, z => CM.take(U32, z, 1n+j), AR.slots(U32, t2), CM.update(U32, L0, j, w), s2),
        take_upd(L0, j, w, hlen))
      %Equal.sym(Nat, Nat.add(j, 1n+CM.length(U32, rest)), 1n+Nat.add(j, CM.length(U32, rest)), N.add_succ(j, CM.length(U32, rest))) : {CM.take(U32, AR.slots(U32, tfl(d, rest, 1n+j, t2)), _) == CM.append(U32, CM.take(U32, L0, j), Con{w, rest}) : List<&2, U32>}
      Equal.trans(List<&2, U32>, CM.take(U32, AR.slots(U32, tfl(d, rest, 1n+j, t2)), Nat.add(1n+j, CM.length(U32, rest))), CM.append(U32, CM.take(U32, AR.slots(U32, t2), 1n+j), rest), CM.append(U32, CM.take(U32, L0, j), Con{w, rest}),
        ih,
        Equal.trans(List<&2, U32>, CM.append(U32, CM.take(U32, AR.slots(U32, t2), 1n+j), rest), CM.append(U32, CM.append(U32, CM.take(U32, L0, j), [w]), rest), CM.append(U32, CM.take(U32, L0, j), Con{w, rest}),
          Equal.cong(List<&2, U32>, List<&2, U32>, z => CM.append(U32, z, rest), CM.take(U32, AR.slots(U32, t2), 1n+j), CM.append(U32, CM.take(U32, L0, j), [w]), e2),
          LL.append_assoc(U32, CM.take(U32, L0, j), [w], rest)))

# ---- lengths ----

# 2 + D == add(2, D)
def two_add(+D: Nat) -> {1n+1n+D == Nat.add(2n, D) : Nat}:
  Equal.sym(Nat, Nat.add(2n, D), 1n+1n+D,
    Equal.trans(Nat, Nat.add(2n, D), 1n+Nat.add(1n, D), 1n+1n+D, LS.succ_add(1n, D),
      N.succ_cong(Nat.add(1n, D), 1n+D, Equal.trans(Nat, Nat.add(1n, D), 1n+Nat.add(0n, D), 1n+D, LS.succ_add(0n, D), N.succ_cong(Nat.add(0n, D), D, LS.zero_add(D))))))

def len_words(+xs: List<&2, W.U64>) -> {CM.length(U32, SCR.words(xs)) == Nat.double(CM.length(W.U64, xs)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      +L = CM.length(U32, SCR.words(rest))
      +D = Nat.double(CM.length(W.U64, rest))
      Equal.trans(Nat, 1n+1n+L, Nat.add(2n, D), Nat.double(1n+CM.length(W.U64, rest)),
        Equal.trans(Nat, 1n+1n+L, 1n+1n+D, Nat.add(2n, D), N.succ_cong(1n+L, 1n+D, N.succ_cong(L, D, len_words(rest))), two_add(D)),
        Equal.sym(Nat, Nat.double(1n+CM.length(W.U64, rest)), Nat.add(2n, D), N.double_succ(CM.length(W.U64, rest))))

def len_outputs(+k: Nat, +c: C8.ChaCha8) -> {CM.length(W.U64, SRC.outputs(~C8.ChaCha8, ~C8.next, k, c)) == k : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+m:
      N.succ_cong(CM.length(W.U64, SRC.outputs(~C8.ChaCha8, ~C8.next, m, SRC.snd64(C8.ChaCha8, C8.next(c)))), m, len_outputs(m, SRC.snd64(C8.ChaCha8, C8.next(c))))

# ---- the clauses ----

def rw_pair(+j: Nat, a: Array<U32>, +k: Nat, +c: C8.ChaCha8, +p: List<&2, U32>) -> {CR.rw_fin(p, CR.rw(k, j, a, C8.next(c))) == (fl(SCR.words(SRC.outputs(~C8.ChaCha8, ~C8.next, 1n+k, c)), j, a), CR.G{SCR.after(1n+k, c), p}) : Array<U32> & CR.Gen}:
  Equal.cong(Array<U32> & C8.ChaCha8, Array<U32> & CR.Gen, z => CR.rw_fin(p, z), CR.rw(k, j, a, C8.next(c)), (fl(SCR.words(SRC.outputs(~C8.ChaCha8, ~C8.next, 1n+k, c)), j, a), SCR.after(1n+k, c)), rw_fl(k, j, a, C8.next(c)))

# THEOREM (Random.read_gen)
def read_gen(+t: AR.Tree<U32>, +j: Nat, +k: Nat, +c: C8.ChaCha8, +p: List<&2, U32>) -> SCR.Random.read_gen(t, j, k, c, p):
  match k:
    case 0n:
      {==}
    case 1n+m:
      Equal.cong(Array<U32> & CR.Gen, CR.Gen, z => SCR.rgen(z), CR.rw_fin(p, CR.rw(m, j, AR.thaw(U32, t), C8.next(c))), (fl(SCR.words(SRC.outputs(~C8.ChaCha8, ~C8.next, 1n+m, c)), j, AR.thaw(U32, t)), CR.G{SCR.after(1n+m, c), p}), rw_pair(j, AR.thaw(U32, t), m, c, p))

# THEOREM (Random.read_words)
def read_words(+d: Nat, +t: AR.Tree<U32>, +j: Nat, +k: Nat, +c: C8.ChaCha8, +p: List<&2, U32>, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hk: {Nat.is_le(Nat.add(j, Nat.double(k)), CM.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(U32, d, t) == True{} : Bool}) -> SCR.Random.read_words(d, t, j, k, c, p, hd, hk, pf):
  match k:
    case 0n:
      +L0 = AR.slots(U32, t)
      %Equal.sym(AR.Tree<U32>, AR.freeze(U32, AR.thaw(U32, t)), t, AR.freeze_thaw(U32, t)) : {CM.take(U32, AR.slots(U32, _), Nat.add(j, 0n)) == CM.append(U32, CM.take(U32, L0, j), Nil{}) : List<&2, U32>}
      %Equal.sym(Nat, Nat.add(j, 0n), j, N.add_zero(j)) : {CM.take(U32, L0, _) == CM.append(U32, CM.take(U32, L0, j), Nil{}) : List<&2, U32>}
      Equal.sym(List<&2, U32>, CM.append(U32, CM.take(U32, L0, j), Nil{}), CM.take(U32, L0, j), LL.append_nil(U32, CM.take(U32, L0, j)))
    case 1n+m:
      +ws = SCR.words(SRC.outputs(~C8.ChaCha8, ~C8.next, 1n+m, c))
      +elen = Equal.trans(Nat, CM.length(U32, ws), Nat.double(CM.length(W.U64, SRC.outputs(~C8.ChaCha8, ~C8.next, 1n+m, c))), Nat.double(1n+m),
        len_words(SRC.outputs(~C8.ChaCha8, ~C8.next, 1n+m, c)),
        Equal.cong(Nat, Nat, z => Nat.double(z), CM.length(W.U64, SRC.outputs(~C8.ChaCha8, ~C8.next, 1n+m, c)), 1n+m, len_outputs(1n+m, c)))
      +hk2 = L.subst(Nat, z => {Nat.is_le(Nat.add(j, z), CM.pow2(d)) == True{} : Bool}, Nat.double(1n+m), CM.length(U32, ws), Equal.sym(Nat, CM.length(U32, ws), Nat.double(1n+m), elen), hk)
      +e1 = Equal.cong(Array<U32> & CR.Gen, List<&2, U32>, z => CM.take(U32, AR.slots(U32, AR.freeze(U32, SCR.rarr(z))), Nat.add(j, Nat.double(1n+m))), CR.rw_fin(p, CR.rw(m, j, AR.thaw(U32, t), C8.next(c))), (fl(ws, j, AR.thaw(U32, t)), CR.G{SCR.after(1n+m, c), p}), rw_pair(j, AR.thaw(U32, t), m, c, p))
      +e2 = Equal.cong(Array<U32>, List<&2, U32>, z => CM.take(U32, AR.slots(U32, AR.freeze(U32, z)), Nat.add(j, Nat.double(1n+m))), fl(ws, j, AR.thaw(U32, t)), AR.thaw(U32, tfl(d, ws, j, t)), fl_thaw(d, ws, j, t, hd, hk2, pf))
      +e3 = Equal.cong(AR.Tree<U32>, List<&2, U32>, z => CM.take(U32, AR.slots(U32, z), Nat.add(j, Nat.double(1n+m))), AR.freeze(U32, AR.thaw(U32, tfl(d, ws, j, t))), tfl(d, ws, j, t), AR.freeze_thaw(U32, tfl(d, ws, j, t)))
      +e4 = L.subst(Nat, z => {CM.take(U32, AR.slots(U32, tfl(d, ws, j, t)), Nat.add(j, z)) == CM.append(U32, CM.take(U32, AR.slots(U32, t), j), ws) : List<&2, U32>}, CM.length(U32, ws), Nat.double(1n+m), elen, fl_take(d, ws, j, t, hd, hk2, pf))
      Equal.trans(List<&2, U32>, CM.take(U32, AR.slots(U32, AR.freeze(U32, SCR.rarr(CR.rw_fin(p, CR.rw(m, j, AR.thaw(U32, t), C8.next(c)))))), Nat.add(j, Nat.double(1n+m))), CM.take(U32, AR.slots(U32, AR.freeze(U32, fl(ws, j, AR.thaw(U32, t)))), Nat.add(j, Nat.double(1n+m))), CM.append(U32, CM.take(U32, AR.slots(U32, t), j), ws),
        e1,
        Equal.trans(List<&2, U32>, CM.take(U32, AR.slots(U32, AR.freeze(U32, fl(ws, j, AR.thaw(U32, t)))), Nat.add(j, Nat.double(1n+m))), CM.take(U32, AR.slots(U32, AR.freeze(U32, AR.thaw(U32, tfl(d, ws, j, t)))), Nat.add(j, Nat.double(1n+m))), CM.append(U32, CM.take(U32, AR.slots(U32, t), j), ws),
          e2,
          Equal.trans(List<&2, U32>, CM.take(U32, AR.slots(U32, AR.freeze(U32, AR.thaw(U32, tfl(d, ws, j, t)))), Nat.add(j, Nat.double(1n+m))), CM.take(U32, AR.slots(U32, tfl(d, ws, j, t)), Nat.add(j, Nat.double(1n+m))), CM.append(U32, CM.take(U32, AR.slots(U32, t), j), ws),
            e3, e4)))

# THEOREM (Random.read_bytes)
def read_bytes(+xs: List<&2, W.U64>) -> SCR.Random.read_bytes(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{W.U64{+l, +h}, +rest}:
      +B = {[SCR.byte_of(l, 0n), SCR.byte_of(l, 8n), SCR.byte_of(l, 16n), SCR.byte_of(l, 24n), SCR.byte_of(h, 0n), SCR.byte_of(h, 8n), SCR.byte_of(h, 16n), SCR.byte_of(h, 24n)] : List<&2, U32>}
      Equal.cong(List<&2, U32>, List<&2, U32>, z => CM.append(U32, B, z), SCR.unpack(SCR.words(rest)), SCR.flat(rest), read_bytes(rest))
