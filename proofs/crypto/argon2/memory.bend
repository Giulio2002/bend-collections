import Base
import ../../../spec/lib/common.bend as SC
import ../../lib/array.bend as AR
import ../../lib/list.bend as LL
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/u32.bend as U
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../../../src/crypto/blake/blake2b/types.bend as T
import ../../../src/crypto/argon2/types.bend as A
import ../../../src/crypto/argon2/sub.bend as SB
import ../../../src/crypto/argon2/memory.bend as M
import ../../../spec/crypto/argon2/blamka.bend as SG
import ../../../spec/crypto/argon2/argon2.bend as SA

# The implementation's memory (a packed Array<U32> of 2^d words, block b at
# words 256 b .. 256 b + 255) against the specification's (a list of blocks).
#
# Arrays are linear, so the relation is stated through proofs/lib/array.bend's
# mirror trees: the memory of the list mem is thaw(mt(d, mem)), the perfect
# tree of depth d whose words are mem's blocks one after the other, then
# zeros. Reading block b with 256 Array.get and writing it with 256
# Array.set (Base's own algorithms, proved in proofs/lib/array.bend) is then
# get and update on mem.

# ---------------------------------------------------------------- lists

def nthv(ws: List<&2, U32>, i: Nat) -> U32:
  Maybe.default(&2, U32, SC.nth(U32, ws, i), 0)

def take_drop(+xs: List<&2, U32>, +n: Nat) -> {SC.append(U32, SC.take(U32, xs, n), SC.drop(U32, xs, n)) == xs : List<&2, U32>}:
  match xs n:
    case Nil{} _:
      {==}
    case Con{h, t} 0n:
      {==}
    case Con{+h, +t} 1n+ +p:
      Equal.cong(List<&2, U32>, List<&2, U32>, z => Con{h, z}, SC.append(U32, SC.take(U32, t, p), SC.drop(U32, t, p)), t, take_drop(t, p))

def zsub(+n: Nat) -> {Nat.sub(0n, n) == 0n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def length_drop(+xs: List<&2, U32>, +n: Nat) -> {SC.length(U32, SC.drop(U32, xs, n)) == Nat.sub(SC.length(U32, xs), n) : Nat}:
  match xs n:
    case Nil{} _:
      Equal.sym(Nat, Nat.sub(0n, n), 0n, zsub(n))
    case Con{h, t} 0n:
      {==}
    case Con{+h, +t} 1n+ +p:
      length_drop(t, p)

def take_all(+xs: List<&2, U32>, +n: Nat, +h: {SC.length(U32, xs) == n : Nat}) -> {SC.take(U32, xs, n) == xs : List<&2, U32>}:
  match xs n:
    case Nil{} _:
      {==}
    case Con{h1, t} 0n:
      Empty.absurd({SC.take(U32, Con{h1, t}, 0n) == Con{h1, t} : List<&2, U32>}, N.succ_zero(SC.length(U32, t), h))
    case Con{+h1, +t} 1n+ +p:
      Equal.cong(List<&2, U32>, List<&2, U32>, z => Con{h1, z}, SC.take(U32, t, p), t, take_all(t, p, N.succ_inj(SC.length(U32, t), p, h)))

def drop_zero(+ys: List<&2, U32>) -> {SC.drop(U32, ys, 0n) == ys : List<&2, U32>}:
  match ys:
    case Nil{}:
      {==}
    case Con{h, t}:
      {==}

def drop_all(+xs: List<&2, U32>, +ys: List<&2, U32>, +n: Nat, +h: {SC.length(U32, xs) == n : Nat}) -> {SC.drop(U32, SC.append(U32, xs, ys), n) == ys : List<&2, U32>}:
  match xs n:
    case Nil{} 0n:
      drop_zero(ys)
    case Nil{} 1n+p:
      Empty.absurd({SC.drop(U32, ys, 1n+p) == ys : List<&2, U32>}, N.zero_succ(p, h))
    case Con{h1, t} 0n:
      Empty.absurd({SC.drop(U32, SC.append(U32, Con{h1, t}, ys), 0n) == ys : List<&2, U32>}, N.succ_zero(SC.length(U32, t), h))
    case Con{+h1, +t} 1n+ +p:
      drop_all(t, ys, p, N.succ_inj(SC.length(U32, t), p, h))

# ---------------------------------------------------------------- mirror trees of word lists

# The perfect tree of depth d holding ws (padded by zeros, truncated at 2^d).
def tree(d: Nat, +ws: List<&2, U32>) -> AR.Tree<U32>:
  match d:
    case 0n:
      AR.TLeaf{nthv(ws, 0n)}
    case 1n+ +p:
      AR.TNode{tree(p, SC.take(U32, ws, SC.pow2(p))), tree(p, SC.drop(U32, ws, SC.pow2(p)))}

def tree_perfect(+d: Nat, +ws: List<&2, U32>) -> {AR.perfect(U32, d, tree(d, ws)) == True{} : Bool}:
  match d:
    case 0n:
      {==}
    case 1n+ +p:
      L.and_intro(AR.perfect(U32, p, tree(p, SC.take(U32, ws, SC.pow2(p)))), AR.perfect(U32, p, tree(p, SC.drop(U32, ws, SC.pow2(p)))), tree_perfect(p, SC.take(U32, ws, SC.pow2(p))), tree_perfect(p, SC.drop(U32, ws, SC.pow2(p))))

def leaf_slots(+ws: List<&2, U32>, +h: {SC.length(U32, ws) == 1n : Nat}) -> {Con{nthv(ws, 0n), Nil{}} == ws : List<&2, U32>}:
  match ws:
    case Nil{}:
      Empty.absurd({Con{nthv(Nil{}, 0n), Nil{}} == Nil{} : List<&2, U32>}, N.zero_succ(0n, h))
    case Con{x, Nil{}}:
      {==}
    case Con{x, Con{y, r}}:
      Empty.absurd({Con{nthv(Con{x, Con{y, r}}, 0n), Nil{}} == Con{x, Con{y, r}} : List<&2, U32>}, N.succ_zero(SC.length(U32, r), N.succ_inj(1n+SC.length(U32, r), 0n, h)))

def double_sub(+x: Nat) -> {Nat.sub(Nat.double(x), x) == x : Nat}:
  %Equal.sym(Nat, Nat.double(x), Nat.add(x, x), NA.double_self(x)) : {Nat.sub(_, x) == x : Nat}
  N.add_sub_cancel(x, x)

def pow2_le_succ(+p: Nat) -> {Nat.is_le(SC.pow2(p), SC.pow2(1n+p)) == True{} : Bool}:
  N.lt_le(SC.pow2(p), SC.pow2(1n+p), N.pow2_lt_succ(p))

# The words of tree(d, ws) are ws, for 2^d words.
def tree_slots(+d: Nat, +ws: List<&2, U32>, +h: {SC.length(U32, ws) == SC.pow2(d) : Nat}) -> {AR.slots(U32, tree(d, ws)) == ws : List<&2, U32>}:
  match d:
    case 0n:
      leaf_slots(ws, h)
    case 1n+ +p:
      +k = SC.pow2(p)
      +ht = LL.sc_length_take(U32, ws, k, L.subst(Nat, z => {Nat.is_le(k, z) == True{} : Bool}, SC.pow2(1n+p), SC.length(U32, ws), Equal.sym(Nat, SC.length(U32, ws), SC.pow2(1n+p), h), pow2_le_succ(p)))
      +hd = Equal.trans(Nat, SC.length(U32, SC.drop(U32, ws, k)), Nat.sub(SC.length(U32, ws), k), k, length_drop(ws, k),
        Equal.trans(Nat, Nat.sub(SC.length(U32, ws), k), Nat.sub(Nat.double(k), k), k, Equal.cong(Nat, Nat, z => Nat.sub(z, k), SC.length(U32, ws), Nat.double(k), h), double_sub(k)))
      Equal.trans(List<&2, U32>, SC.append(U32, AR.slots(U32, tree(p, SC.take(U32, ws, k))), AR.slots(U32, tree(p, SC.drop(U32, ws, k)))), SC.append(U32, SC.take(U32, ws, k), SC.drop(U32, ws, k)), ws,
        Equal.trans(List<&2, U32>, SC.append(U32, AR.slots(U32, tree(p, SC.take(U32, ws, k))), AR.slots(U32, tree(p, SC.drop(U32, ws, k)))), SC.append(U32, SC.take(U32, ws, k), AR.slots(U32, tree(p, SC.drop(U32, ws, k)))), SC.append(U32, SC.take(U32, ws, k), SC.drop(U32, ws, k)),
          Equal.cong(List<&2, U32>, List<&2, U32>, z => SC.append(U32, z, AR.slots(U32, tree(p, SC.drop(U32, ws, k)))), AR.slots(U32, tree(p, SC.take(U32, ws, k))), SC.take(U32, ws, k), tree_slots(p, SC.take(U32, ws, k), ht)),
          Equal.cong(List<&2, U32>, List<&2, U32>, z => SC.append(U32, SC.take(U32, ws, k), z), AR.slots(U32, tree(p, SC.drop(U32, ws, k))), SC.drop(U32, ws, k), tree_slots(p, SC.drop(U32, ws, k), hd))),
        take_drop(ws, k))

# A perfect tree is the tree of its words.
def tree_ext(+d: Nat, +t: AR.Tree<U32>, +pf: {AR.perfect(U32, d, t) == True{} : Bool}) -> {t == tree(d, AR.slots(U32, t)) : AR.Tree<U32>}:
  match d t:
    case 0n AR.TLeaf{x}:
      {==}
    case 0n AR.TNode{l, r}:
      Empty.absurd({AR.TNode{l, r} == tree(0n, AR.slots(U32, AR.TNode{l, r})) : AR.Tree<U32>}, L.false_true(pf))
    case 1n+p AR.TLeaf{x}:
      Empty.absurd({AR.TLeaf{x} == tree(1n+p, AR.slots(U32, AR.TLeaf{x})) : AR.Tree<U32>}, L.false_true(pf))
    case 1n+ +p AR.TNode{+l, +r}:
      +pl = AR.pf_left(U32, p, l, r, pf)
      +pr = AR.pf_right(U32, p, l, r, pf)
      +sl = AR.slots(U32, l)
      +sr = AR.slots(U32, r)
      +hl = AR.slots_length(U32, p, l, pl)
      +et = Equal.trans(List<&2, U32>, SC.take(U32, SC.append(U32, sl, sr), SC.pow2(p)), SC.take(U32, sl, SC.pow2(p)), sl,
        LL.sc_take_append_left(U32, sl, sr, SC.pow2(p), N.eq_le(SC.pow2(p), SC.length(U32, sl), Equal.sym(Nat, SC.length(U32, sl), SC.pow2(p), hl))),
        take_all(sl, SC.pow2(p), hl))
      +ed = drop_all(sl, sr, SC.pow2(p), hl)
      Equal.trans(AR.Tree<U32>, AR.TNode{l, r}, AR.TNode{tree(p, sl), tree(p, sr)}, AR.TNode{tree(p, SC.take(U32, SC.append(U32, sl, sr), SC.pow2(p))), tree(p, SC.drop(U32, SC.append(U32, sl, sr), SC.pow2(p)))},
        Equal.trans(AR.Tree<U32>, AR.TNode{l, r}, AR.TNode{tree(p, sl), r}, AR.TNode{tree(p, sl), tree(p, sr)},
          Equal.cong(AR.Tree<U32>, AR.Tree<U32>, z => AR.TNode{z, r}, l, tree(p, sl), tree_ext(p, l, pl)),
          Equal.cong(AR.Tree<U32>, AR.Tree<U32>, z => AR.TNode{tree(p, sl), z}, r, tree(p, sr), tree_ext(p, r, pr))),
        Equal.sym(AR.Tree<U32>, AR.TNode{tree(p, SC.take(U32, SC.append(U32, sl, sr), SC.pow2(p))), tree(p, SC.drop(U32, SC.append(U32, sl, sr), SC.pow2(p)))}, AR.TNode{tree(p, sl), tree(p, sr)},
          Equal.trans(AR.Tree<U32>, AR.TNode{tree(p, SC.take(U32, SC.append(U32, sl, sr), SC.pow2(p))), tree(p, SC.drop(U32, SC.append(U32, sl, sr), SC.pow2(p)))}, AR.TNode{tree(p, sl), tree(p, SC.drop(U32, SC.append(U32, sl, sr), SC.pow2(p)))}, AR.TNode{tree(p, sl), tree(p, sr)},
            Equal.cong(List<&2, U32>, AR.Tree<U32>, z => AR.TNode{tree(p, z), tree(p, SC.drop(U32, SC.append(U32, sl, sr), SC.pow2(p)))}, SC.take(U32, SC.append(U32, sl, sr), SC.pow2(p)), sl, et),
            Equal.cong(List<&2, U32>, AR.Tree<U32>, z => AR.TNode{tree(p, sl), tree(p, z)}, SC.drop(U32, SC.append(U32, sl, sr), SC.pow2(p)), sr, ed))))

# ---------------------------------------------------------------- one word

def nth_some(+xs: List<&2, U32>, +j: Nat, +h: {Nat.is_lt(j, SC.length(U32, xs)) == True{} : Bool}) -> {SC.nth(U32, xs, j) == Some{nthv(xs, j)} : Maybe<&2, U32>}:
  match xs j:
    case Nil{} _:
      Empty.absurd({SC.nth(U32, Nil{}, j) == Some{nthv(Nil{}, j)} : Maybe<&2, U32>}, N.lt_zero_absurd(j, h))
    case Con{x, t} 0n:
      {==}
    case Con{x, +t} 1n+ +p:
      nth_some(t, p, h)

def le32(+d: Nat, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}) -> {Nat.is_le(d, 32n) == True{} : Bool}:
  N.lt_le(d, 32n, hd)

# Array.get at word j of the tree of ws.
def get_word(+d: Nat, +ws: List<&2, U32>, +j: Nat, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hl: {SC.length(U32, ws) == SC.pow2(d) : Nat}, +hj: {Nat.is_lt(j, SC.pow2(d)) == True{} : Bool}) -> {Array.get(U32, AR.thaw(U32, tree(d, ws)), U32.from_nat(j)) == (AR.thaw(U32, tree(d, ws)), nthv(ws, j)) : Array<U32> & U32}:
  +t = tree(d, ws)
  +ej = U.to_nat_from_nat(j, d, le32(d, hd), hj)
  +hi = L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(d)) == True{} : Bool}, j, U32.to_nat(U32.from_nat(j)), Equal.sym(Nat, U32.to_nat(U32.from_nat(j)), j, ej), hj)
  +hn = nth_some(ws, j, L.subst(Nat, z => {Nat.is_lt(j, z) == True{} : Bool}, SC.pow2(d), SC.length(U32, ws), Equal.sym(Nat, SC.length(U32, ws), SC.pow2(d), hl), hj))
  +hx = L.subst(List<&2, U32>, z => {SC.nth(U32, z, U32.to_nat(U32.from_nat(j))) == Some{nthv(ws, j)} : Maybe<&2, U32>}, ws, AR.slots(U32, t), Equal.sym(List<&2, U32>, AR.slots(U32, t), ws, tree_slots(d, ws, hl)),
    L.subst(Nat, z => {SC.nth(U32, ws, z) == Some{nthv(ws, j)} : Maybe<&2, U32>}, j, U32.to_nat(U32.from_nat(j)), Equal.sym(Nat, U32.to_nat(U32.from_nat(j)), j, ej), hn))
  AR.get(U32, d, t, U32.from_nat(j), nthv(ws, j), hd, hi, hx, tree_perfect(d, ws))

# ---------------------------------------------------------------- reading a run of words

def slice(ws: List<&2, U32>, +base: Nat, n: Nat) -> List<&2, U32>:
  SC.take(U32, SC.drop(U32, ws, base), n)

def nth_drop(+ws: List<&2, U32>, +base: Nat, +k: Nat) -> {nthv(SC.drop(U32, ws, base), k) == nthv(ws, Nat.add(base, k)) : U32}:
  match ws base:
    case Nil{} _:
      {==}
    case Con{h, t} 0n:
      {==}
    case Con{h, +t} 1n+ +b:
      nth_drop(t, b, k)

def take_snoc(+ys: List<&2, U32>, +k: Nat, +h: {Nat.is_lt(k, SC.length(U32, ys)) == True{} : Bool}) -> {SC.take(U32, ys, 1n+k) == SC.append(U32, SC.take(U32, ys, k), Con{nthv(ys, k), Nil{}}) : List<&2, U32>}:
  match ys k:
    case Nil{} _:
      Empty.absurd({SC.take(U32, Nil{}, 1n+k) == SC.append(U32, SC.take(U32, Nil{}, k), Con{nthv(Nil{}, k), Nil{}}) : List<&2, U32>}, N.lt_zero_absurd(k, h))
    case Con{+x, +t} 0n:
      Equal.cong(List<&2, U32>, List<&2, U32>, z => Con{x, z}, SC.take(U32, t, 0n), Nil{}, LL.sc_take_zero(U32, t))
    case Con{+x, +t} 1n+ +p:
      Equal.cong(List<&2, U32>, List<&2, U32>, z => Con{x, z}, SC.take(U32, t, 1n+p), SC.append(U32, SC.take(U32, t, p), Con{nthv(t, p), Nil{}}), take_snoc(t, p, h))

def lt_sub(+base: Nat, +k: Nat, +n: Nat, +h: {Nat.is_lt(Nat.add(base, k), n) == True{} : Bool}) -> {Nat.is_lt(k, Nat.sub(n, base)) == True{} : Bool}:
  match base n:
    case 0n _:
      L.subst(Nat, z => {Nat.is_lt(k, z) == True{} : Bool}, n, Nat.sub(n, 0n), Equal.sym(Nat, Nat.sub(n, 0n), n, N.sub_zero(n)), h)
    case 1n+b 0n:
      Empty.absurd({Nat.is_lt(k, Nat.sub(0n, 1n+b)) == True{} : Bool}, N.lt_zero_absurd(Nat.add(1n+b, k), h))
    case 1n+ +b 1n+ +m:
      lt_sub(b, k, m, h)

# slice(ws, base, k + 1) is slice(ws, base, k) and word base + k.
def slice_snoc(+ws: List<&2, U32>, +base: Nat, +k: Nat, +h: {Nat.is_lt(Nat.add(base, k), SC.length(U32, ws)) == True{} : Bool}) -> {slice(ws, base, 1n+k) == SC.append(U32, slice(ws, base, k), Con{nthv(ws, Nat.add(base, k)), Nil{}}) : List<&2, U32>}:
  +ys = SC.drop(U32, ws, base)
  +hk = L.subst(Nat, z => {Nat.is_lt(k, z) == True{} : Bool}, Nat.sub(SC.length(U32, ws), base), SC.length(U32, ys), Equal.sym(Nat, SC.length(U32, ys), Nat.sub(SC.length(U32, ws), base), length_drop(ws, base)), lt_sub(base, k, SC.length(U32, ws), h))
  Equal.trans(List<&2, U32>, SC.take(U32, ys, 1n+k), SC.append(U32, SC.take(U32, ys, k), Con{nthv(ys, k), Nil{}}), SC.append(U32, SC.take(U32, ys, k), Con{nthv(ws, Nat.add(base, k)), Nil{}}),
    take_snoc(ys, k, hk),
    Equal.cong(U32, List<&2, U32>, z => SC.append(U32, SC.take(U32, ys, k), Con{z, Nil{}}), nthv(ys, k), nthv(ws, Nat.add(base, k)), nth_drop(ws, base, k)))

def slice_one(+ws: List<&2, U32>, +base: Nat, +h: {Nat.is_lt(base, SC.length(U32, ws)) == True{} : Bool}) -> {slice(ws, base, 1n) == Con{nthv(ws, base), Nil{}} : List<&2, U32>}:
  match ws base:
    case Nil{} _:
      Empty.absurd({slice(Nil{}, base, 1n) == Con{nthv(Nil{}, base), Nil{}} : List<&2, U32>}, N.lt_zero_absurd(base, h))
    case Con{+x, +t} 0n:
      Equal.cong(List<&2, U32>, List<&2, U32>, z => Con{x, z}, SC.take(U32, t, 0n), Nil{}, LL.sc_take_zero(U32, t))
    case Con{x, +t} 1n+ +b:
      slice_one(t, b, h)

def append_cons(+xs: List<&2, U32>, +w: U32, +acc: List<&2, U32>) -> {SC.append(U32, SC.append(U32, xs, Con{w, Nil{}}), acc) == SC.append(U32, xs, Con{w, acc}) : List<&2, U32>}:
  LL.append_assoc(U32, xs, Con{w, Nil{}}, acc)

def lt_pred(+base: Nat, +p: Nat, +n: Nat, +h: {Nat.is_lt(Nat.add(base, 1n+p), n) == True{} : Bool}) -> {Nat.is_lt(Nat.add(base, p), n) == True{} : Bool}:
  N.lt_trans(Nat.add(base, p), Nat.add(base, 1n+p), n, L.subst(Nat, z => {Nat.is_lt(Nat.add(base, p), z) == True{} : Bool}, 1n+Nat.add(base, p), Nat.add(base, 1n+p), Equal.sym(Nat, Nat.add(base, 1n+p), 1n+Nat.add(base, p), N.add_succ(base, p)), N.lt_succ(Nat.add(base, p))), h)

def pred_add(+base: Nat, +p: Nat) -> {Nat.sub(Nat.add(base, 1n+p), 1n) == Nat.add(base, p) : Nat}:
  %Equal.sym(Nat, Nat.add(base, 1n+p), 1n+Nat.add(base, p), N.add_succ(base, p)) : {Nat.sub(_, 1n) == Nat.add(base, p) : Nat}
  N.sub_zero(Nat.add(base, p))

# M.rd reads words base + n down to base (onto acc), leaving the memory unchanged.
def rd_words(+d: Nat, +ws: List<&2, U32>, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hl: {SC.length(U32, ws) == SC.pow2(d) : Nat}, +n: Nat, +base: Nat, +acc: List<&2, U32>, +h: {Nat.is_lt(Nat.add(base, n), SC.pow2(d)) == True{} : Bool}) -> {M.rd(n, Nat.add(base, n), acc, (AR.thaw(U32, tree(d, ws)), nthv(ws, Nat.add(base, n)))) == (AR.thaw(U32, tree(d, ws)), SC.append(U32, slice(ws, base, 1n+n), acc)) : Array<U32> & List<&2, U32>}:
  match n:
    case 0n:
      +hw = L.subst(Nat, z => {Nat.is_lt(Nat.add(base, 0n), z) == True{} : Bool}, SC.pow2(d), SC.length(U32, ws), Equal.sym(Nat, SC.length(U32, ws), SC.pow2(d), hl), h)
      %Equal.sym(Nat, Nat.add(base, 0n), base, N.add_zero(base)) : {(AR.thaw(U32, tree(d, ws)), Con{nthv(ws, _), acc}) == (AR.thaw(U32, tree(d, ws)), SC.append(U32, slice(ws, base, 1n), acc)) : Array<U32> & List<&2, U32>}
      %Equal.sym(List<&2, U32>, slice(ws, base, 1n), Con{nthv(ws, base), Nil{}}, slice_one(ws, base, L.subst(Nat, z => {Nat.is_lt(z, SC.length(U32, ws)) == True{} : Bool}, Nat.add(base, 0n), base, N.add_zero(base), hw))) : {(AR.thaw(U32, tree(d, ws)), Con{nthv(ws, base), acc}) == (AR.thaw(U32, tree(d, ws)), SC.append(U32, _, acc)) : Array<U32> & List<&2, U32>}
      {==}
    case 1n+ +p:
      +hw = L.subst(Nat, z => {Nat.is_lt(Nat.add(base, 1n+p), z) == True{} : Bool}, SC.pow2(d), SC.length(U32, ws), Equal.sym(Nat, SC.length(U32, ws), SC.pow2(d), hl), h)
      +w = nthv(ws, Nat.add(base, 1n+p))
      +j = Nat.add(base, p)
      +hj = lt_pred(base, p, SC.pow2(d), h)
      %Equal.sym(Nat, Nat.sub(Nat.add(base, 1n+p), 1n), Nat.add(base, p), pred_add(base, p)) : {M.rd(p, _, Con{w, acc}, Array.get(U32, AR.thaw(U32, tree(d, ws)), U32.from_nat(_))) == (AR.thaw(U32, tree(d, ws)), SC.append(U32, slice(ws, base, 2n+p), acc)) : Array<U32> & List<&2, U32>}
      %Equal.sym(Array<U32> & U32, Array.get(U32, AR.thaw(U32, tree(d, ws)), U32.from_nat(j)), (AR.thaw(U32, tree(d, ws)), nthv(ws, j)), get_word(d, ws, j, hd, hl, hj)) : {M.rd(p, j, Con{w, acc}, _) == (AR.thaw(U32, tree(d, ws)), SC.append(U32, slice(ws, base, 2n+p), acc)) : Array<U32> & List<&2, U32>}
      %Equal.sym(Array<U32> & List<&2, U32>, M.rd(p, j, Con{w, acc}, (AR.thaw(U32, tree(d, ws)), nthv(ws, j))), (AR.thaw(U32, tree(d, ws)), SC.append(U32, slice(ws, base, 1n+p), Con{w, acc})), rd_words(d, ws, hd, hl, p, base, Con{w, acc}, hj)) : {_ == (AR.thaw(U32, tree(d, ws)), SC.append(U32, slice(ws, base, 2n+p), acc)) : Array<U32> & List<&2, U32>}
      %Equal.sym(List<&2, U32>, slice(ws, base, 2n+p), SC.append(U32, slice(ws, base, 1n+p), Con{w, Nil{}}), slice_snoc(ws, base, 1n+p, hw)) : {(AR.thaw(U32, tree(d, ws)), SC.append(U32, slice(ws, base, 1n+p), Con{w, acc})) == (AR.thaw(U32, tree(d, ws)), SC.append(U32, _, acc)) : Array<U32> & List<&2, U32>}
      %Equal.sym(List<&2, U32>, SC.append(U32, SC.append(U32, slice(ws, base, 1n+p), Con{w, Nil{}}), acc), SC.append(U32, slice(ws, base, 1n+p), Con{w, acc}), append_cons(slice(ws, base, 1n+p), w, acc)) : {(AR.thaw(U32, tree(d, ws)), SC.append(U32, slice(ws, base, 1n+p), Con{w, acc})) == (AR.thaw(U32, tree(d, ws)), _) : Array<U32> & List<&2, U32>}
      {==}

# ---------------------------------------------------------------- the memory of a list of blocks

def flat(mem: List<&2, A.Block>) -> List<&2, U32>:
  match mem:
    case Nil{}:
      Nil{}
    case b <> rest:
      SC.append(U32, SB.words(b), flat(rest))

def pad(+d: Nat, +n: Nat) -> List<&2, U32>:
  SC.replicate(U32, Nat.sub(SC.pow2(d), Nat.mul(n, 256n)), 0)

# The words of the memory mem in an array of 2^d words.
def W(+d: Nat, +mem: List<&2, A.Block>) -> List<&2, U32>:
  SC.append(U32, flat(mem), pad(d, SC.length(A.Block, mem)))

def mt(+d: Nat, +mem: List<&2, A.Block>) -> AR.Tree<U32>:
  tree(d, W(d, mem))

def words_len(+b: A.Block) -> {SC.length(U32, SB.words(b)) == 256n : Nat}:
  match b:
    case A.B{T.V{T.W{a0, b0}, T.W{a1, b1}, T.W{a2, b2}, T.W{a3, b3}, T.W{a4, b4}, T.W{a5, b5}, T.W{a6, b6}, T.W{a7, b7}, T.W{a8, b8}, T.W{a9, b9}, T.W{a10, b10}, T.W{a11, b11}, T.W{a12, b12}, T.W{a13, b13}, T.W{a14, b14}, T.W{a15, b15}}, T.V{T.W{a16, b16}, T.W{a17, b17}, T.W{a18, b18}, T.W{a19, b19}, T.W{a20, b20}, T.W{a21, b21}, T.W{a22, b22}, T.W{a23, b23}, T.W{a24, b24}, T.W{a25, b25}, T.W{a26, b26}, T.W{a27, b27}, T.W{a28, b28}, T.W{a29, b29}, T.W{a30, b30}, T.W{a31, b31}}, T.V{T.W{a32, b32}, T.W{a33, b33}, T.W{a34, b34}, T.W{a35, b35}, T.W{a36, b36}, T.W{a37, b37}, T.W{a38, b38}, T.W{a39, b39}, T.W{a40, b40}, T.W{a41, b41}, T.W{a42, b42}, T.W{a43, b43}, T.W{a44, b44}, T.W{a45, b45}, T.W{a46, b46}, T.W{a47, b47}}, T.V{T.W{a48, b48}, T.W{a49, b49}, T.W{a50, b50}, T.W{a51, b51}, T.W{a52, b52}, T.W{a53, b53}, T.W{a54, b54}, T.W{a55, b55}, T.W{a56, b56}, T.W{a57, b57}, T.W{a58, b58}, T.W{a59, b59}, T.W{a60, b60}, T.W{a61, b61}, T.W{a62, b62}, T.W{a63, b63}}, T.V{T.W{a64, b64}, T.W{a65, b65}, T.W{a66, b66}, T.W{a67, b67}, T.W{a68, b68}, T.W{a69, b69}, T.W{a70, b70}, T.W{a71, b71}, T.W{a72, b72}, T.W{a73, b73}, T.W{a74, b74}, T.W{a75, b75}, T.W{a76, b76}, T.W{a77, b77}, T.W{a78, b78}, T.W{a79, b79}}, T.V{T.W{a80, b80}, T.W{a81, b81}, T.W{a82, b82}, T.W{a83, b83}, T.W{a84, b84}, T.W{a85, b85}, T.W{a86, b86}, T.W{a87, b87}, T.W{a88, b88}, T.W{a89, b89}, T.W{a90, b90}, T.W{a91, b91}, T.W{a92, b92}, T.W{a93, b93}, T.W{a94, b94}, T.W{a95, b95}}, T.V{T.W{a96, b96}, T.W{a97, b97}, T.W{a98, b98}, T.W{a99, b99}, T.W{a100, b100}, T.W{a101, b101}, T.W{a102, b102}, T.W{a103, b103}, T.W{a104, b104}, T.W{a105, b105}, T.W{a106, b106}, T.W{a107, b107}, T.W{a108, b108}, T.W{a109, b109}, T.W{a110, b110}, T.W{a111, b111}}, T.V{T.W{a112, b112}, T.W{a113, b113}, T.W{a114, b114}, T.W{a115, b115}, T.W{a116, b116}, T.W{a117, b117}, T.W{a118, b118}, T.W{a119, b119}, T.W{a120, b120}, T.W{a121, b121}, T.W{a122, b122}, T.W{a123, b123}, T.W{a124, b124}, T.W{a125, b125}, T.W{a126, b126}, T.W{a127, b127}}}:
      {==}

def rows8_words(+b: A.Block) -> {SB.rows8(SB.words(b)) == b : A.Block}:
  match b:
    case A.B{T.V{T.W{a0, b0}, T.W{a1, b1}, T.W{a2, b2}, T.W{a3, b3}, T.W{a4, b4}, T.W{a5, b5}, T.W{a6, b6}, T.W{a7, b7}, T.W{a8, b8}, T.W{a9, b9}, T.W{a10, b10}, T.W{a11, b11}, T.W{a12, b12}, T.W{a13, b13}, T.W{a14, b14}, T.W{a15, b15}}, T.V{T.W{a16, b16}, T.W{a17, b17}, T.W{a18, b18}, T.W{a19, b19}, T.W{a20, b20}, T.W{a21, b21}, T.W{a22, b22}, T.W{a23, b23}, T.W{a24, b24}, T.W{a25, b25}, T.W{a26, b26}, T.W{a27, b27}, T.W{a28, b28}, T.W{a29, b29}, T.W{a30, b30}, T.W{a31, b31}}, T.V{T.W{a32, b32}, T.W{a33, b33}, T.W{a34, b34}, T.W{a35, b35}, T.W{a36, b36}, T.W{a37, b37}, T.W{a38, b38}, T.W{a39, b39}, T.W{a40, b40}, T.W{a41, b41}, T.W{a42, b42}, T.W{a43, b43}, T.W{a44, b44}, T.W{a45, b45}, T.W{a46, b46}, T.W{a47, b47}}, T.V{T.W{a48, b48}, T.W{a49, b49}, T.W{a50, b50}, T.W{a51, b51}, T.W{a52, b52}, T.W{a53, b53}, T.W{a54, b54}, T.W{a55, b55}, T.W{a56, b56}, T.W{a57, b57}, T.W{a58, b58}, T.W{a59, b59}, T.W{a60, b60}, T.W{a61, b61}, T.W{a62, b62}, T.W{a63, b63}}, T.V{T.W{a64, b64}, T.W{a65, b65}, T.W{a66, b66}, T.W{a67, b67}, T.W{a68, b68}, T.W{a69, b69}, T.W{a70, b70}, T.W{a71, b71}, T.W{a72, b72}, T.W{a73, b73}, T.W{a74, b74}, T.W{a75, b75}, T.W{a76, b76}, T.W{a77, b77}, T.W{a78, b78}, T.W{a79, b79}}, T.V{T.W{a80, b80}, T.W{a81, b81}, T.W{a82, b82}, T.W{a83, b83}, T.W{a84, b84}, T.W{a85, b85}, T.W{a86, b86}, T.W{a87, b87}, T.W{a88, b88}, T.W{a89, b89}, T.W{a90, b90}, T.W{a91, b91}, T.W{a92, b92}, T.W{a93, b93}, T.W{a94, b94}, T.W{a95, b95}}, T.V{T.W{a96, b96}, T.W{a97, b97}, T.W{a98, b98}, T.W{a99, b99}, T.W{a100, b100}, T.W{a101, b101}, T.W{a102, b102}, T.W{a103, b103}, T.W{a104, b104}, T.W{a105, b105}, T.W{a106, b106}, T.W{a107, b107}, T.W{a108, b108}, T.W{a109, b109}, T.W{a110, b110}, T.W{a111, b111}}, T.V{T.W{a112, b112}, T.W{a113, b113}, T.W{a114, b114}, T.W{a115, b115}, T.W{a116, b116}, T.W{a117, b117}, T.W{a118, b118}, T.W{a119, b119}, T.W{a120, b120}, T.W{a121, b121}, T.W{a122, b122}, T.W{a123, b123}, T.W{a124, b124}, T.W{a125, b125}, T.W{a126, b126}, T.W{a127, b127}}}:
      {==}

def flat_len(+mem: List<&2, A.Block>) -> {SC.length(U32, flat(mem)) == Nat.mul(SC.length(A.Block, mem), 256n) : Nat}:
  match mem:
    case Nil{}:
      {==}
    case +b <> +rest:
      Equal.trans(Nat, SC.length(U32, SC.append(U32, SB.words(b), flat(rest))), Nat.add(SC.length(U32, SB.words(b)), SC.length(U32, flat(rest))), Nat.add(256n, Nat.mul(SC.length(A.Block, rest), 256n)),
        LL.length_append(U32, SB.words(b), flat(rest)),
        Equal.trans(Nat, Nat.add(SC.length(U32, SB.words(b)), SC.length(U32, flat(rest))), Nat.add(256n, SC.length(U32, flat(rest))), Nat.add(256n, Nat.mul(SC.length(A.Block, rest), 256n)),
          Equal.cong(Nat, Nat, z => Nat.add(z, SC.length(U32, flat(rest))), SC.length(U32, SB.words(b)), 256n, words_len(b)),
          Equal.cong(Nat, Nat, z => Nat.add(256n, z), SC.length(U32, flat(rest)), Nat.mul(SC.length(A.Block, rest), 256n), flat_len(rest))))

def W_len(+d: Nat, +mem: List<&2, A.Block>, +hc: {Nat.is_le(Nat.mul(SC.length(A.Block, mem), 256n), SC.pow2(d)) == True{} : Bool}) -> {SC.length(U32, W(d, mem)) == SC.pow2(d) : Nat}:
  +n = Nat.mul(SC.length(A.Block, mem), 256n)
  Equal.trans(Nat, SC.length(U32, W(d, mem)), Nat.add(SC.length(U32, flat(mem)), SC.length(U32, pad(d, SC.length(A.Block, mem)))), SC.pow2(d),
    LL.length_append(U32, flat(mem), pad(d, SC.length(A.Block, mem))),
    Equal.trans(Nat, Nat.add(SC.length(U32, flat(mem)), SC.length(U32, pad(d, SC.length(A.Block, mem)))), Nat.add(n, Nat.sub(SC.pow2(d), n)), SC.pow2(d),
      Equal.trans(Nat, Nat.add(SC.length(U32, flat(mem)), SC.length(U32, pad(d, SC.length(A.Block, mem)))), Nat.add(n, SC.length(U32, pad(d, SC.length(A.Block, mem)))), Nat.add(n, Nat.sub(SC.pow2(d), n)),
        Equal.cong(Nat, Nat, z => Nat.add(z, SC.length(U32, pad(d, SC.length(A.Block, mem)))), SC.length(U32, flat(mem)), n, flat_len(mem)),
        Equal.cong(Nat, Nat, z => Nat.add(n, z), SC.length(U32, pad(d, SC.length(A.Block, mem))), Nat.sub(SC.pow2(d), n), LL.length_replicate(U32, Nat.sub(SC.pow2(d), n), 0))),
      N.sub_add(SC.pow2(d), n, hc)))

# ---------------------------------------------------------------- reading block b

def drop_append_add(+xs: List<&2, U32>, +ys: List<&2, U32>, +n: Nat, +k: Nat, +h: {SC.length(U32, xs) == n : Nat}) -> {SC.drop(U32, SC.append(U32, xs, ys), Nat.add(n, k)) == SC.drop(U32, ys, k) : List<&2, U32>}:
  match xs n:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+p:
      Empty.absurd({SC.drop(U32, ys, Nat.add(1n+p, k)) == SC.drop(U32, ys, k) : List<&2, U32>}, N.zero_succ(p, h))
    case Con{x, t} 0n:
      Empty.absurd({SC.drop(U32, SC.append(U32, Con{x, t}, ys), k) == SC.drop(U32, ys, k) : List<&2, U32>}, N.succ_zero(SC.length(U32, t), h))
    case Con{x, +t} 1n+ +p:
      drop_append_add(t, ys, p, k, N.succ_inj(SC.length(U32, t), p, h))

def drop_append_le(+xs: List<&2, U32>, +ys: List<&2, U32>, +n: Nat, +h: {Nat.is_le(n, SC.length(U32, xs)) == True{} : Bool}) -> {SC.drop(U32, SC.append(U32, xs, ys), n) == SC.append(U32, SC.drop(U32, xs, n), ys) : List<&2, U32>}:
  match xs n:
    case Nil{} 0n:
      Equal.trans(List<&2, U32>, SC.drop(U32, ys, 0n), ys, SC.append(U32, SC.drop(U32, Nil{}, 0n), ys), drop_zero(ys), {==})
    case Nil{} 1n+p:
      Empty.absurd({SC.drop(U32, ys, 1n+p) == SC.append(U32, SC.drop(U32, Nil{}, 1n+p), ys) : List<&2, U32>}, L.false_true(h))
    case Con{x, t} 0n:
      {==}
    case Con{x, +t} 1n+ +p:
      drop_append_le(t, ys, p, h)

# The 256 words of block b of the flattened blocks.
def flat_slice(+mem: List<&2, A.Block>, +b: Nat, +hb: {Nat.is_lt(b, SC.length(A.Block, mem)) == True{} : Bool}) -> {slice(flat(mem), Nat.mul(b, 256n), 256n) == SB.words(SA.get(mem, b)) : List<&2, U32>}:
  match mem b:
    case Nil{} _:
      Empty.absurd({slice(Nil{}, Nat.mul(b, 256n), 256n) == SB.words(SA.get(Nil{}, b)) : List<&2, U32>}, N.lt_zero_absurd(b, hb))
    case +x <> +rest 0n:
      +e1 = drop_zero(SC.append(U32, SB.words(x), flat(rest)))
      +e2 = LL.sc_take_append_left(U32, SB.words(x), flat(rest), 256n, N.eq_le(256n, SC.length(U32, SB.words(x)), Equal.sym(Nat, SC.length(U32, SB.words(x)), 256n, words_len(x))))
      +e3 = take_all(SB.words(x), 256n, words_len(x))
      Equal.trans(List<&2, U32>, SC.take(U32, SC.drop(U32, SC.append(U32, SB.words(x), flat(rest)), 0n), 256n), SC.take(U32, SC.append(U32, SB.words(x), flat(rest)), 256n), SB.words(x),
        Equal.cong(List<&2, U32>, List<&2, U32>, z => SC.take(U32, z, 256n), SC.drop(U32, SC.append(U32, SB.words(x), flat(rest)), 0n), SC.append(U32, SB.words(x), flat(rest)), e1),
        Equal.trans(List<&2, U32>, SC.take(U32, SC.append(U32, SB.words(x), flat(rest)), 256n), SC.take(U32, SB.words(x), 256n), SB.words(x), e2, e3))
    case +x <> +rest 1n+ +c:
      Equal.trans(List<&2, U32>, SC.take(U32, SC.drop(U32, SC.append(U32, SB.words(x), flat(rest)), Nat.add(256n, Nat.mul(c, 256n))), 256n), slice(flat(rest), Nat.mul(c, 256n), 256n), SB.words(SA.get(rest, c)),
        Equal.cong(List<&2, U32>, List<&2, U32>, z => SC.take(U32, z, 256n), SC.drop(U32, SC.append(U32, SB.words(x), flat(rest)), Nat.add(256n, Nat.mul(c, 256n))), SC.drop(U32, flat(rest), Nat.mul(c, 256n)), drop_append_add(SB.words(x), flat(rest), 256n, Nat.mul(c, 256n), words_len(x))),
        flat_slice(rest, c, hb))

def mul_lt(+b: Nat, +n: Nat, +hb: {Nat.is_lt(b, n) == True{} : Bool}) -> {Nat.is_le(Nat.add(Nat.mul(b, 256n), 256n), Nat.mul(n, 256n)) == True{} : Bool}:
  match b n:
    case _ 0n:
      Empty.absurd({Nat.is_le(Nat.add(Nat.mul(b, 256n), 256n), 0n) == True{} : Bool}, N.lt_zero_absurd(b, hb))
    case 0n 1n+m:
      N.le_add_right(256n, Nat.mul(m, 256n))
    case 1n+ +c 1n+ +m:
      %Equal.sym(Nat, Nat.add(Nat.add(256n, Nat.mul(c, 256n)), 256n), Nat.add(256n, Nat.add(Nat.mul(c, 256n), 256n)), NA.add_assoc(256n, Nat.mul(c, 256n), 256n)) : {Nat.is_le(_, Nat.add(256n, Nat.mul(m, 256n))) == True{} : Bool}
      N.le_add_left(Nat.add(Nat.mul(c, 256n), 256n), Nat.mul(m, 256n), 256n, mul_lt(c, m, hb))

def le_sub(+base: Nat, +k: Nat, +n: Nat, +h: {Nat.is_le(Nat.add(base, k), n) == True{} : Bool}) -> {Nat.is_le(k, Nat.sub(n, base)) == True{} : Bool}:
  match base n:
    case 0n _:
      L.subst(Nat, z => {Nat.is_le(k, z) == True{} : Bool}, n, Nat.sub(n, 0n), Equal.sym(Nat, Nat.sub(n, 0n), n, N.sub_zero(n)), h)
    case 1n+b 0n:
      Empty.absurd({Nat.is_le(k, Nat.sub(0n, 1n+b)) == True{} : Bool}, L.false_true(h))
    case 1n+ +b 1n+ +m:
      le_sub(b, k, m, h)

def slice_W(+d: Nat, +mem: List<&2, A.Block>, +b: Nat, +hb: {Nat.is_lt(b, SC.length(A.Block, mem)) == True{} : Bool}) -> {slice(W(d, mem), Nat.mul(b, 256n), 256n) == SB.words(SA.get(mem, b)) : List<&2, U32>}:
  +F = flat(mem)
  +P = pad(d, SC.length(A.Block, mem))
  +base = Nat.mul(b, 256n)
  +hn = mul_lt(b, SC.length(A.Block, mem), hb)
  +hfl = Equal.sym(Nat, SC.length(U32, F), Nat.mul(SC.length(A.Block, mem), 256n), flat_len(mem))
  +hle = N.le_trans(base, Nat.add(base, 256n), SC.length(U32, F), N.le_add_right(base, 256n), L.subst(Nat, z => {Nat.is_le(Nat.add(base, 256n), z) == True{} : Bool}, Nat.mul(SC.length(A.Block, mem), 256n), SC.length(U32, F), hfl, hn))
  +h256 = L.subst(Nat, z => {Nat.is_le(256n, z) == True{} : Bool}, Nat.sub(SC.length(U32, F), base), SC.length(U32, SC.drop(U32, F, base)), Equal.sym(Nat, SC.length(U32, SC.drop(U32, F, base)), Nat.sub(SC.length(U32, F), base), length_drop(F, base)),
    le_sub(base, 256n, SC.length(U32, F), L.subst(Nat, z => {Nat.is_le(Nat.add(base, 256n), z) == True{} : Bool}, Nat.mul(SC.length(A.Block, mem), 256n), SC.length(U32, F), hfl, hn)))
  Equal.trans(List<&2, U32>, SC.take(U32, SC.drop(U32, SC.append(U32, F, P), base), 256n), SC.take(U32, SC.drop(U32, F, base), 256n), SB.words(SA.get(mem, b)),
    Equal.trans(List<&2, U32>, SC.take(U32, SC.drop(U32, SC.append(U32, F, P), base), 256n), SC.take(U32, SC.append(U32, SC.drop(U32, F, base), P), 256n), SC.take(U32, SC.drop(U32, F, base), 256n),
      Equal.cong(List<&2, U32>, List<&2, U32>, z => SC.take(U32, z, 256n), SC.drop(U32, SC.append(U32, F, P), base), SC.append(U32, SC.drop(U32, F, base), P), drop_append_le(F, P, base, hle)),
      LL.sc_take_append_left(U32, SC.drop(U32, F, base), P, 256n, h256)),
    flat_slice(mem, b, hb))

def lt_last(+base: Nat, +n: Nat, +h: {Nat.is_le(Nat.add(base, 256n), n) == True{} : Bool}) -> {Nat.is_lt(Nat.add(base, 255n), n) == True{} : Bool}:
  N.lt_le_trans(Nat.add(base, 255n), Nat.add(base, 256n), n, N.lt_add_left(255n, 256n, base, {==}), h)

# Reading block b of the memory of mem.
def get_block(+d: Nat, +mem: List<&2, A.Block>, +b: Nat, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hc: {Nat.is_le(Nat.mul(SC.length(A.Block, mem), 256n), SC.pow2(d)) == True{} : Bool}, +hb: {Nat.is_lt(b, SC.length(A.Block, mem)) == True{} : Bool}) -> {M.get(b, AR.thaw(U32, mt(d, mem))) == (AR.thaw(U32, mt(d, mem)), SA.get(mem, b)) : Array<U32> & A.Block}:
  +ws = W(d, mem)
  +hl = W_len(d, mem, hc)
  +base = Nat.mul(b, 256n)
  +last = Nat.add(base, 255n)
  -ar = AR.thaw(U32, mt(d, mem))
  +hlast = lt_last(base, SC.pow2(d), N.le_trans(Nat.add(base, 256n), Nat.mul(SC.length(A.Block, mem), 256n), SC.pow2(d), mul_lt(b, SC.length(A.Block, mem), hb), hc))
  +g = SA.get(mem, b)
  %Equal.sym(Array<U32> & U32, Array.get(U32, ar, U32.from_nat(last)), (ar, nthv(ws, last)), get_word(d, ws, last, hd, hl, hlast)) : {M.read_fin(M.rd(255n, last, Nil{}, _)) == (ar, g) : Array<U32> & A.Block}
  %Equal.sym(Array<U32> & List<&2, U32>, M.rd(255n, last, Nil{}, (ar, nthv(ws, last))), (ar, SC.append(U32, slice(ws, base, 256n), Nil{})), rd_words(d, ws, hd, hl, 255n, base, Nil{}, hlast)) : {M.read_fin(_) == (ar, g) : Array<U32> & A.Block}
  %Equal.sym(List<&2, U32>, SC.append(U32, slice(ws, base, 256n), Nil{}), slice(ws, base, 256n), LL.append_nil(U32, slice(ws, base, 256n))) : {M.read_fin((ar, _)) == (ar, g) : Array<U32> & A.Block}
  %Equal.sym(List<&2, U32>, slice(ws, base, 256n), SB.words(g), slice_W(d, mem, b, hb)) : {M.read_fin((ar, _)) == (ar, g) : Array<U32> & A.Block}
  Equal.cong(A.Block, Array<U32> & A.Block, z => (ar, z), SB.rows8(SB.words(g)), g, rows8_words(g))

# ---------------------------------------------------------------- writing block b

# Words ws stored from index i on.
def splice(ws: List<&2, U32>, +i: Nat, V: List<&2, U32>) -> List<&2, U32>:
  match ws:
    case Nil{}:
      V
    case w <> rest:
      splice(rest, Nat.add(i, 1n), SC.update(U32, V, i, w))

def lt_add_succ(+i: Nat, +r: Nat) -> {Nat.is_lt(i, Nat.add(i, 1n+r)) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(i, 1n+r), 1n+Nat.add(i, r), N.add_succ(i, r)) : {Nat.is_lt(i, _) == True{} : Bool}
  N.le_lt_succ(i, Nat.add(i, r), N.le_add_right(i, r))

def add_one_assoc(+i: Nat, +r: Nat) -> {Nat.add(Nat.add(i, 1n), r) == Nat.add(i, 1n+r) : Nat}:
  NA.add_assoc(i, 1n, r)

# M.wr stores the words ws from word i on.
def wr_words(+d: Nat, +ws: List<&2, U32>, +i: Nat, +V: List<&2, U32>, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hl: {SC.length(U32, V) == SC.pow2(d) : Nat}, +hi: {Nat.is_le(Nat.add(i, SC.length(U32, ws)), SC.pow2(d)) == True{} : Bool}) -> {M.wr(ws, i, AR.thaw(U32, tree(d, V))) == AR.thaw(U32, tree(d, splice(ws, i, V))) : Array<U32>}:
  match ws:
    case Nil{}:
      {==}
    case +w <> +rest:
      +t = tree(d, V)
      +hi1 = N.lt_le_trans(i, Nat.add(i, 1n+SC.length(U32, rest)), SC.pow2(d), lt_add_succ(i, SC.length(U32, rest)), hi)
      +ei = U.to_nat_from_nat(i, d, le32(d, hd), hi1)
      +hin = L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(d)) == True{} : Bool}, i, U32.to_nat(U32.from_nat(i)), Equal.sym(Nat, U32.to_nat(U32.from_nat(i)), i, ei), hi1)
      +hn = nth_some(V, i, L.subst(Nat, z => {Nat.is_lt(i, z) == True{} : Bool}, SC.pow2(d), SC.length(U32, V), Equal.sym(Nat, SC.length(U32, V), SC.pow2(d), hl), hi1))
      +hx = L.subst(List<&2, U32>, z => {SC.nth(U32, z, U32.to_nat(U32.from_nat(i))) == Some{nthv(V, i)} : Maybe<&2, U32>}, V, AR.slots(U32, t), Equal.sym(List<&2, U32>, AR.slots(U32, t), V, tree_slots(d, V, hl)),
        L.subst(Nat, z => {SC.nth(U32, V, z) == Some{nthv(V, i)} : Maybe<&2, U32>}, i, U32.to_nat(U32.from_nat(i)), Equal.sym(Nat, U32.to_nat(U32.from_nat(i)), i, ei), hn))
      +es = AR.set(U32, d, t, U32.from_nat(i), w, nthv(V, i), hd, hin, hx, tree_perfect(d, V))
      +t2 = AR.upd(U32, d, t, i, w)
      +V2 = SC.update(U32, V, i, w)
      +e_slots = Equal.trans(List<&2, U32>, AR.slots(U32, t2), SC.update(U32, AR.slots(U32, t), i, w), V2,
        AR.upd_slots(U32, d, t, i, w, hi1, tree_perfect(d, V)),
        Equal.cong(List<&2, U32>, List<&2, U32>, z => SC.update(U32, z, i, w), AR.slots(U32, t), V, tree_slots(d, V, hl)))
      +e_ext = Equal.trans(AR.Tree<U32>, t2, tree(d, AR.slots(U32, t2)), tree(d, V2), tree_ext(d, t2, AR.upd_perfect(U32, d, t, i, w, tree_perfect(d, V))), Equal.cong(List<&2, U32>, AR.Tree<U32>, z => tree(d, z), AR.slots(U32, t2), V2, e_slots))
      +hl2 = Equal.trans(Nat, SC.length(U32, V2), SC.length(U32, V), SC.pow2(d), LL.length_update(U32, V, i, w), hl)
      +hi2 = L.subst(Nat, z => {Nat.is_le(z, SC.pow2(d)) == True{} : Bool}, Nat.add(i, 1n+SC.length(U32, rest)), Nat.add(Nat.add(i, 1n), SC.length(U32, rest)), Equal.sym(Nat, Nat.add(Nat.add(i, 1n), SC.length(U32, rest)), Nat.add(i, 1n+SC.length(U32, rest)), add_one_assoc(i, SC.length(U32, rest))), hi)
      %Equal.sym(Array<U32>, Array.set(U32, AR.thaw(U32, t), U32.from_nat(i), w), AR.thaw(U32, AR.upd(U32, d, t, U32.to_nat(U32.from_nat(i)), w)), es) : {M.wr(rest, Nat.add(i, 1n), _) == AR.thaw(U32, tree(d, splice(rest, Nat.add(i, 1n), V2))) : Array<U32>}
      %Equal.sym(Array<U32>, AR.thaw(U32, AR.upd(U32, d, t, U32.to_nat(U32.from_nat(i)), w)), AR.thaw(U32, t2), Equal.cong(Nat, Array<U32>, z => AR.thaw(U32, AR.upd(U32, d, t, z, w)), U32.to_nat(U32.from_nat(i)), i, ei)) : {M.wr(rest, Nat.add(i, 1n), _) == AR.thaw(U32, tree(d, splice(rest, Nat.add(i, 1n), V2))) : Array<U32>}
      %Equal.sym(Array<U32>, AR.thaw(U32, t2), AR.thaw(U32, tree(d, V2)), Equal.cong(AR.Tree<U32>, Array<U32>, z => AR.thaw(U32, z), t2, tree(d, V2), e_ext)) : {M.wr(rest, Nat.add(i, 1n), _) == AR.thaw(U32, tree(d, splice(rest, Nat.add(i, 1n), V2))) : Array<U32>}
      wr_words(d, rest, Nat.add(i, 1n), V2, hd, hl2, hi2)

def splice_app_left(+ws: List<&2, U32>, +i: Nat, +X: List<&2, U32>, +P: List<&2, U32>, +h: {Nat.is_le(Nat.add(i, SC.length(U32, ws)), SC.length(U32, X)) == True{} : Bool}) -> {splice(ws, i, SC.append(U32, X, P)) == SC.append(U32, splice(ws, i, X), P) : List<&2, U32>}:
  match ws:
    case Nil{}:
      {==}
    case +w <> +rest:
      +hi = N.lt_le_trans(i, Nat.add(i, 1n+SC.length(U32, rest)), SC.length(U32, X), lt_add_succ(i, SC.length(U32, rest)), h)
      +X2 = SC.update(U32, X, i, w)
      +h2 = L.subst(Nat, z => {Nat.is_le(Nat.add(Nat.add(i, 1n), SC.length(U32, rest)), z) == True{} : Bool}, SC.length(U32, X), SC.length(U32, X2), Equal.sym(Nat, SC.length(U32, X2), SC.length(U32, X), LL.length_update(U32, X, i, w)),
        L.subst(Nat, z => {Nat.is_le(z, SC.length(U32, X)) == True{} : Bool}, Nat.add(i, 1n+SC.length(U32, rest)), Nat.add(Nat.add(i, 1n), SC.length(U32, rest)), Equal.sym(Nat, Nat.add(Nat.add(i, 1n), SC.length(U32, rest)), Nat.add(i, 1n+SC.length(U32, rest)), add_one_assoc(i, SC.length(U32, rest))), h))
      %Equal.sym(List<&2, U32>, SC.update(U32, SC.append(U32, X, P), i, w), SC.append(U32, X2, P), LL.update_append_left(U32, X, P, i, w, hi)) : {splice(rest, Nat.add(i, 1n), _) == SC.append(U32, splice(rest, Nat.add(i, 1n), X2), P) : List<&2, U32>}
      splice_app_left(rest, Nat.add(i, 1n), X2, P, h2)

def splice_app_right(+ws: List<&2, U32>, +n: Nat, +k: Nat, +X: List<&2, U32>, +Y: List<&2, U32>, +hX: {SC.length(U32, X) == n : Nat}) -> {splice(ws, Nat.add(n, k), SC.append(U32, X, Y)) == SC.append(U32, X, splice(ws, k, Y)) : List<&2, U32>}:
  match ws:
    case Nil{}:
      {==}
    case +w <> +rest:
      +hle = L.subst(Nat, z => {Nat.is_le(z, Nat.add(n, k)) == True{} : Bool}, n, SC.length(U32, X), Equal.sym(Nat, SC.length(U32, X), n, hX), N.le_add_right(n, k))
      +ek = Equal.trans(Nat, Nat.sub(Nat.add(n, k), SC.length(U32, X)), Nat.sub(Nat.add(n, k), n), k, Equal.cong(Nat, Nat, z => Nat.sub(Nat.add(n, k), z), SC.length(U32, X), n, hX), N.add_sub_cancel(n, k))
      +Y2 = SC.update(U32, Y, k, w)
      %Equal.sym(List<&2, U32>, SC.update(U32, SC.append(U32, X, Y), Nat.add(n, k), w), SC.append(U32, X, SC.update(U32, Y, Nat.sub(Nat.add(n, k), SC.length(U32, X)), w)), LL.update_append_right(U32, X, Y, Nat.add(n, k), w, hle)) : {splice(rest, Nat.add(Nat.add(n, k), 1n), _) == SC.append(U32, X, splice(rest, Nat.add(k, 1n), Y2)) : List<&2, U32>}
      %Equal.sym(Nat, Nat.sub(Nat.add(n, k), SC.length(U32, X)), k, ek) : {splice(rest, Nat.add(Nat.add(n, k), 1n), SC.append(U32, X, SC.update(U32, Y, _, w))) == SC.append(U32, X, splice(rest, Nat.add(k, 1n), Y2)) : List<&2, U32>}
      %Equal.sym(Nat, Nat.add(Nat.add(n, k), 1n), Nat.add(n, Nat.add(k, 1n)), NA.add_assoc(n, k, 1n)) : {splice(rest, _, SC.append(U32, X, Y2)) == SC.append(U32, X, splice(rest, Nat.add(k, 1n), Y2)) : List<&2, U32>}
      splice_app_right(rest, n, Nat.add(k, 1n), X, Y2, hX)

def splice_full(+b: A.Block, +v: A.Block) -> {splice(SB.words(v), 0n, SB.words(b)) == SB.words(v) : List<&2, U32>}:
  match b v:
    case A.B{T.V{T.W{a0, b0}, T.W{a1, b1}, T.W{a2, b2}, T.W{a3, b3}, T.W{a4, b4}, T.W{a5, b5}, T.W{a6, b6}, T.W{a7, b7}, T.W{a8, b8}, T.W{a9, b9}, T.W{a10, b10}, T.W{a11, b11}, T.W{a12, b12}, T.W{a13, b13}, T.W{a14, b14}, T.W{a15, b15}}, T.V{T.W{a16, b16}, T.W{a17, b17}, T.W{a18, b18}, T.W{a19, b19}, T.W{a20, b20}, T.W{a21, b21}, T.W{a22, b22}, T.W{a23, b23}, T.W{a24, b24}, T.W{a25, b25}, T.W{a26, b26}, T.W{a27, b27}, T.W{a28, b28}, T.W{a29, b29}, T.W{a30, b30}, T.W{a31, b31}}, T.V{T.W{a32, b32}, T.W{a33, b33}, T.W{a34, b34}, T.W{a35, b35}, T.W{a36, b36}, T.W{a37, b37}, T.W{a38, b38}, T.W{a39, b39}, T.W{a40, b40}, T.W{a41, b41}, T.W{a42, b42}, T.W{a43, b43}, T.W{a44, b44}, T.W{a45, b45}, T.W{a46, b46}, T.W{a47, b47}}, T.V{T.W{a48, b48}, T.W{a49, b49}, T.W{a50, b50}, T.W{a51, b51}, T.W{a52, b52}, T.W{a53, b53}, T.W{a54, b54}, T.W{a55, b55}, T.W{a56, b56}, T.W{a57, b57}, T.W{a58, b58}, T.W{a59, b59}, T.W{a60, b60}, T.W{a61, b61}, T.W{a62, b62}, T.W{a63, b63}}, T.V{T.W{a64, b64}, T.W{a65, b65}, T.W{a66, b66}, T.W{a67, b67}, T.W{a68, b68}, T.W{a69, b69}, T.W{a70, b70}, T.W{a71, b71}, T.W{a72, b72}, T.W{a73, b73}, T.W{a74, b74}, T.W{a75, b75}, T.W{a76, b76}, T.W{a77, b77}, T.W{a78, b78}, T.W{a79, b79}}, T.V{T.W{a80, b80}, T.W{a81, b81}, T.W{a82, b82}, T.W{a83, b83}, T.W{a84, b84}, T.W{a85, b85}, T.W{a86, b86}, T.W{a87, b87}, T.W{a88, b88}, T.W{a89, b89}, T.W{a90, b90}, T.W{a91, b91}, T.W{a92, b92}, T.W{a93, b93}, T.W{a94, b94}, T.W{a95, b95}}, T.V{T.W{a96, b96}, T.W{a97, b97}, T.W{a98, b98}, T.W{a99, b99}, T.W{a100, b100}, T.W{a101, b101}, T.W{a102, b102}, T.W{a103, b103}, T.W{a104, b104}, T.W{a105, b105}, T.W{a106, b106}, T.W{a107, b107}, T.W{a108, b108}, T.W{a109, b109}, T.W{a110, b110}, T.W{a111, b111}}, T.V{T.W{a112, b112}, T.W{a113, b113}, T.W{a114, b114}, T.W{a115, b115}, T.W{a116, b116}, T.W{a117, b117}, T.W{a118, b118}, T.W{a119, b119}, T.W{a120, b120}, T.W{a121, b121}, T.W{a122, b122}, T.W{a123, b123}, T.W{a124, b124}, T.W{a125, b125}, T.W{a126, b126}, T.W{a127, b127}}} A.B{T.V{T.W{c0, e0}, T.W{c1, e1}, T.W{c2, e2}, T.W{c3, e3}, T.W{c4, e4}, T.W{c5, e5}, T.W{c6, e6}, T.W{c7, e7}, T.W{c8, e8}, T.W{c9, e9}, T.W{c10, e10}, T.W{c11, e11}, T.W{c12, e12}, T.W{c13, e13}, T.W{c14, e14}, T.W{c15, e15}}, T.V{T.W{c16, e16}, T.W{c17, e17}, T.W{c18, e18}, T.W{c19, e19}, T.W{c20, e20}, T.W{c21, e21}, T.W{c22, e22}, T.W{c23, e23}, T.W{c24, e24}, T.W{c25, e25}, T.W{c26, e26}, T.W{c27, e27}, T.W{c28, e28}, T.W{c29, e29}, T.W{c30, e30}, T.W{c31, e31}}, T.V{T.W{c32, e32}, T.W{c33, e33}, T.W{c34, e34}, T.W{c35, e35}, T.W{c36, e36}, T.W{c37, e37}, T.W{c38, e38}, T.W{c39, e39}, T.W{c40, e40}, T.W{c41, e41}, T.W{c42, e42}, T.W{c43, e43}, T.W{c44, e44}, T.W{c45, e45}, T.W{c46, e46}, T.W{c47, e47}}, T.V{T.W{c48, e48}, T.W{c49, e49}, T.W{c50, e50}, T.W{c51, e51}, T.W{c52, e52}, T.W{c53, e53}, T.W{c54, e54}, T.W{c55, e55}, T.W{c56, e56}, T.W{c57, e57}, T.W{c58, e58}, T.W{c59, e59}, T.W{c60, e60}, T.W{c61, e61}, T.W{c62, e62}, T.W{c63, e63}}, T.V{T.W{c64, e64}, T.W{c65, e65}, T.W{c66, e66}, T.W{c67, e67}, T.W{c68, e68}, T.W{c69, e69}, T.W{c70, e70}, T.W{c71, e71}, T.W{c72, e72}, T.W{c73, e73}, T.W{c74, e74}, T.W{c75, e75}, T.W{c76, e76}, T.W{c77, e77}, T.W{c78, e78}, T.W{c79, e79}}, T.V{T.W{c80, e80}, T.W{c81, e81}, T.W{c82, e82}, T.W{c83, e83}, T.W{c84, e84}, T.W{c85, e85}, T.W{c86, e86}, T.W{c87, e87}, T.W{c88, e88}, T.W{c89, e89}, T.W{c90, e90}, T.W{c91, e91}, T.W{c92, e92}, T.W{c93, e93}, T.W{c94, e94}, T.W{c95, e95}}, T.V{T.W{c96, e96}, T.W{c97, e97}, T.W{c98, e98}, T.W{c99, e99}, T.W{c100, e100}, T.W{c101, e101}, T.W{c102, e102}, T.W{c103, e103}, T.W{c104, e104}, T.W{c105, e105}, T.W{c106, e106}, T.W{c107, e107}, T.W{c108, e108}, T.W{c109, e109}, T.W{c110, e110}, T.W{c111, e111}}, T.V{T.W{c112, e112}, T.W{c113, e113}, T.W{c114, e114}, T.W{c115, e115}, T.W{c116, e116}, T.W{c117, e117}, T.W{c118, e118}, T.W{c119, e119}, T.W{c120, e120}, T.W{c121, e121}, T.W{c122, e122}, T.W{c123, e123}, T.W{c124, e124}, T.W{c125, e125}, T.W{c126, e126}, T.W{c127, e127}}}:
      {==}

def flat_splice(+mem: List<&2, A.Block>, +b: Nat, +v: A.Block, +hb: {Nat.is_lt(b, SC.length(A.Block, mem)) == True{} : Bool}) -> {splice(SB.words(v), Nat.mul(b, 256n), flat(mem)) == flat(SA.set(mem, b, v)) : List<&2, U32>}:
  match mem b:
    case Nil{} _:
      Empty.absurd({splice(SB.words(v), Nat.mul(b, 256n), Nil{}) == flat(SA.set(Nil{}, b, v)) : List<&2, U32>}, N.lt_zero_absurd(b, hb))
    case +x <> +rest 0n:
      Equal.trans(List<&2, U32>, splice(SB.words(v), 0n, SC.append(U32, SB.words(x), flat(rest))), SC.append(U32, splice(SB.words(v), 0n, SB.words(x)), flat(rest)), SC.append(U32, SB.words(v), flat(rest)),
        splice_app_left(SB.words(v), 0n, SB.words(x), flat(rest), L.subst(Nat, z => {Nat.is_le(z, SC.length(U32, SB.words(x))) == True{} : Bool}, SC.length(U32, SB.words(x)), SC.length(U32, SB.words(v)), Equal.trans(Nat, SC.length(U32, SB.words(x)), 256n, SC.length(U32, SB.words(v)), words_len(x), Equal.sym(Nat, SC.length(U32, SB.words(v)), 256n, words_len(v))), N.le_refl(SC.length(U32, SB.words(x))))),
        Equal.cong(List<&2, U32>, List<&2, U32>, z => SC.append(U32, z, flat(rest)), splice(SB.words(v), 0n, SB.words(x)), SB.words(v), splice_full(x, v)))
    case +x <> +rest 1n+ +c:
      Equal.trans(List<&2, U32>, splice(SB.words(v), Nat.add(256n, Nat.mul(c, 256n)), SC.append(U32, SB.words(x), flat(rest))), SC.append(U32, SB.words(x), splice(SB.words(v), Nat.mul(c, 256n), flat(rest))), SC.append(U32, SB.words(x), flat(SA.set(rest, c, v))),
        splice_app_right(SB.words(v), 256n, Nat.mul(c, 256n), SB.words(x), flat(rest), words_len(x)),
        Equal.cong(List<&2, U32>, List<&2, U32>, z => SC.append(U32, SB.words(x), z), splice(SB.words(v), Nat.mul(c, 256n), flat(rest)), flat(SA.set(rest, c, v)), flat_splice(rest, c, v, hb)))

def W_splice(+d: Nat, +mem: List<&2, A.Block>, +b: Nat, +v: A.Block, +hb: {Nat.is_lt(b, SC.length(A.Block, mem)) == True{} : Bool}) -> {splice(SB.words(v), Nat.mul(b, 256n), W(d, mem)) == W(d, SA.set(mem, b, v)) : List<&2, U32>}:
  +F = flat(mem)
  +hn = mul_lt(b, SC.length(A.Block, mem), hb)
  +hfl = Equal.sym(Nat, SC.length(U32, F), Nat.mul(SC.length(A.Block, mem), 256n), flat_len(mem))
  +h = L.subst(Nat, z => {Nat.is_le(Nat.add(Nat.mul(b, 256n), z), SC.length(U32, F)) == True{} : Bool}, 256n, SC.length(U32, SB.words(v)), Equal.sym(Nat, SC.length(U32, SB.words(v)), 256n, words_len(v)), L.subst(Nat, z => {Nat.is_le(Nat.add(Nat.mul(b, 256n), 256n), z) == True{} : Bool}, Nat.mul(SC.length(A.Block, mem), 256n), SC.length(U32, F), hfl, hn))
  +P = pad(d, SC.length(A.Block, mem))
  Equal.trans(List<&2, U32>, splice(SB.words(v), Nat.mul(b, 256n), SC.append(U32, F, P)), SC.append(U32, splice(SB.words(v), Nat.mul(b, 256n), F), P), W(d, SA.set(mem, b, v)),
    splice_app_left(SB.words(v), Nat.mul(b, 256n), F, P, h),
    Equal.trans(List<&2, U32>, SC.append(U32, splice(SB.words(v), Nat.mul(b, 256n), F), P), SC.append(U32, flat(SA.set(mem, b, v)), P), W(d, SA.set(mem, b, v)),
      Equal.cong(List<&2, U32>, List<&2, U32>, z => SC.append(U32, z, P), splice(SB.words(v), Nat.mul(b, 256n), F), flat(SA.set(mem, b, v)), flat_splice(mem, b, v, hb)),
      Equal.cong(Nat, List<&2, U32>, z => SC.append(U32, flat(SA.set(mem, b, v)), pad(d, z)), SC.length(A.Block, mem), SC.length(A.Block, SA.set(mem, b, v)), Equal.sym(Nat, SC.length(A.Block, SA.set(mem, b, v)), SC.length(A.Block, mem), LL.length_update(A.Block, mem, b, v)))))

# Writing block b of the memory of mem.
def set_block(+d: Nat, +mem: List<&2, A.Block>, +b: Nat, +v: A.Block, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hc: {Nat.is_le(Nat.mul(SC.length(A.Block, mem), 256n), SC.pow2(d)) == True{} : Bool}, +hb: {Nat.is_lt(b, SC.length(A.Block, mem)) == True{} : Bool}) -> {M.set(b, v, AR.thaw(U32, mt(d, mem))) == AR.thaw(U32, mt(d, SA.set(mem, b, v))) : Array<U32>}:
  +hi = L.subst(Nat, z => {Nat.is_le(Nat.add(Nat.mul(b, 256n), z), SC.pow2(d)) == True{} : Bool}, 256n, SC.length(U32, SB.words(v)), Equal.sym(Nat, SC.length(U32, SB.words(v)), 256n, words_len(v)), N.le_trans(Nat.add(Nat.mul(b, 256n), 256n), Nat.mul(SC.length(A.Block, mem), 256n), SC.pow2(d), mul_lt(b, SC.length(A.Block, mem), hb), hc))
  Equal.trans(Array<U32>, M.wr(SB.words(v), Nat.mul(b, 256n), AR.thaw(U32, tree(d, W(d, mem)))), AR.thaw(U32, tree(d, splice(SB.words(v), Nat.mul(b, 256n), W(d, mem)))), AR.thaw(U32, mt(d, SA.set(mem, b, v))),
    wr_words(d, SB.words(v), Nat.mul(b, 256n), W(d, mem), hd, W_len(d, mem, hc), hi),
    Equal.cong(List<&2, U32>, Array<U32>, z => AR.thaw(U32, tree(d, z)), splice(SB.words(v), Nat.mul(b, 256n), W(d, mem)), W(d, SA.set(mem, b, v)), W_splice(d, mem, b, v, hb)))

# ---------------------------------------------------------------- the zero memory

def zero_words() -> {SB.words(SG.zero()) == SC.replicate(U32, 256n, 0) : List<&2, U32>}:
  {==}

def flat_zero(+n: Nat) -> {flat(SC.replicate(A.Block, n, SG.zero())) == SC.replicate(U32, Nat.mul(n, 256n), 0) : List<&2, U32>}:
  match n:
    case 0n:
      {==}
    case 1n+ +k:
      Equal.trans(List<&2, U32>, SC.append(U32, SB.words(SG.zero()), flat(SC.replicate(A.Block, k, SG.zero()))), SC.append(U32, SC.replicate(U32, 256n, 0), SC.replicate(U32, Nat.mul(k, 256n), 0)), SC.replicate(U32, Nat.add(256n, Nat.mul(k, 256n)), 0),
        Equal.trans(List<&2, U32>, SC.append(U32, SB.words(SG.zero()), flat(SC.replicate(A.Block, k, SG.zero()))), SC.append(U32, SC.replicate(U32, 256n, 0), flat(SC.replicate(A.Block, k, SG.zero()))), SC.append(U32, SC.replicate(U32, 256n, 0), SC.replicate(U32, Nat.mul(k, 256n), 0)),
          Equal.cong(List<&2, U32>, List<&2, U32>, z => SC.append(U32, z, flat(SC.replicate(A.Block, k, SG.zero()))), SB.words(SG.zero()), SC.replicate(U32, 256n, 0), zero_words()),
          Equal.cong(List<&2, U32>, List<&2, U32>, z => SC.append(U32, SC.replicate(U32, 256n, 0), z), flat(SC.replicate(A.Block, k, SG.zero())), SC.replicate(U32, Nat.mul(k, 256n), 0), flat_zero(k))),
        LL.replicate_add(U32, 256n, Nat.mul(k, 256n), 0))

# The zeroed array is the memory of mm zero blocks.
def new_mem(+d: Nat, +mm: Nat, +hc: {Nat.is_le(Nat.mul(mm, 256n), SC.pow2(d)) == True{} : Bool}) -> {Array.new(U32, d, 0) == AR.thaw(U32, mt(d, SC.replicate(A.Block, mm, SG.zero()))) : Array<U32>}:
  +z = SC.replicate(A.Block, mm, SG.zero())
  +n = Nat.mul(mm, 256n)
  +t = AR.trep(U32, d, 0)
  +ew = Equal.trans(List<&2, U32>, W(d, z), SC.append(U32, SC.replicate(U32, n, 0), SC.replicate(U32, Nat.sub(SC.pow2(d), n), 0)), SC.replicate(U32, SC.pow2(d), 0),
    Equal.trans(List<&2, U32>, W(d, z), SC.append(U32, SC.replicate(U32, n, 0), pad(d, SC.length(A.Block, z))), SC.append(U32, SC.replicate(U32, n, 0), SC.replicate(U32, Nat.sub(SC.pow2(d), n), 0)),
      Equal.cong(List<&2, U32>, List<&2, U32>, x => SC.append(U32, x, pad(d, SC.length(A.Block, z))), flat(z), SC.replicate(U32, n, 0), flat_zero(mm)),
      Equal.cong(Nat, List<&2, U32>, x => SC.append(U32, SC.replicate(U32, n, 0), pad(d, x)), SC.length(A.Block, z), mm, LL.length_replicate(A.Block, mm, SG.zero()))),
    Equal.trans(List<&2, U32>, SC.append(U32, SC.replicate(U32, n, 0), SC.replicate(U32, Nat.sub(SC.pow2(d), n), 0)), SC.replicate(U32, Nat.add(n, Nat.sub(SC.pow2(d), n)), 0), SC.replicate(U32, SC.pow2(d), 0),
      LL.replicate_add(U32, n, Nat.sub(SC.pow2(d), n), 0),
      Equal.cong(Nat, List<&2, U32>, x => SC.replicate(U32, x, 0), Nat.add(n, Nat.sub(SC.pow2(d), n)), SC.pow2(d), N.sub_add(SC.pow2(d), n, hc))))
  +et = Equal.trans(AR.Tree<U32>, t, tree(d, AR.slots(U32, t)), tree(d, W(d, z)),
    tree_ext(d, t, AR.trep_perfect(U32, d, 0)),
    Equal.cong(List<&2, U32>, AR.Tree<U32>, x => tree(d, x), AR.slots(U32, t), W(d, z), Equal.trans(List<&2, U32>, AR.slots(U32, t), SC.replicate(U32, SC.pow2(d), 0), W(d, z), AR.trep_slots(U32, d, 0), Equal.sym(List<&2, U32>, W(d, z), SC.replicate(U32, SC.pow2(d), 0), ew))))
  Equal.trans(Array<U32>, Array.new(U32, d, 0), AR.thaw(U32, t), AR.thaw(U32, mt(d, z)), AR.new(U32, d, 0), Equal.cong(AR.Tree<U32>, Array<U32>, x => AR.thaw(U32, x), t, tree(d, W(d, z)), et))
