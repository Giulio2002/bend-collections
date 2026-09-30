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

def rw_len(+v: T.State) -> {SC.length(U32, SB.row_words(v)) == 32n : Nat}:
  match v:
    case T.V{T.W{l0, h0}, T.W{l1, h1}, T.W{l2, h2}, T.W{l3, h3}, T.W{l4, h4}, T.W{l5, h5}, T.W{l6, h6}, T.W{l7, h7}, T.W{l8, h8}, T.W{l9, h9}, T.W{l10, h10}, T.W{l11, h11}, T.W{l12, h12}, T.W{l13, h13}, T.W{l14, h14}, T.W{l15, h15}}:
      {==}

def len_app(+a: List<&2, U32>, +b: List<&2, U32>) -> {SC.length(U32, SB.app(a, b)) == Nat.add(SC.length(U32, a), SC.length(U32, b)) : Nat}:
  match a:
    case Nil{}:
      {==}
    case +x <> +r:
      Equal.cong(Nat, Nat, z => 1n+z, SC.length(U32, SB.app(r, b)), Nat.add(SC.length(U32, r), SC.length(U32, b)), len_app(r, b))

# One more row: 32 more words.
def len_row(+v: T.State, +rest: List<&2, U32>) -> {SC.length(U32, SB.app(SB.row_words(v), rest)) == Nat.add(32n, SC.length(U32, rest)) : Nat}:
  %Equal.sym(Nat, SC.length(U32, SB.app(SB.row_words(v), rest)), Nat.add(SC.length(U32, SB.row_words(v)), SC.length(U32, rest)), len_app(SB.row_words(v), rest)) : {_ == Nat.add(32n, SC.length(U32, rest)) : Nat}
  %Equal.sym(Nat, SC.length(U32, SB.row_words(v)), 32n, rw_len(v)) : {Nat.add(_, SC.length(U32, rest)) == Nat.add(32n, SC.length(U32, rest)) : Nat}
  {==}

def words_len(+b: A.Block) -> {SC.length(U32, SB.words(b)) == 256n : Nat}:
  match b:
    case A.B{+r0, +r1, +r2, +r3, +r4, +r5, +r6, +r7}:
      %Equal.sym(Nat, SC.length(U32, SB.app(SB.row_words(r0), SB.app(SB.row_words(r1), SB.app(SB.row_words(r2), SB.app(SB.row_words(r3), SB.app(SB.row_words(r4), SB.app(SB.row_words(r5), SB.app(SB.row_words(r6), SB.app(SB.row_words(r7), Nil{}))))))))), Nat.add(32n, SC.length(U32, SB.app(SB.row_words(r1), SB.app(SB.row_words(r2), SB.app(SB.row_words(r3), SB.app(SB.row_words(r4), SB.app(SB.row_words(r5), SB.app(SB.row_words(r6), SB.app(SB.row_words(r7), Nil{}))))))))), len_row(r0, SB.app(SB.row_words(r1), SB.app(SB.row_words(r2), SB.app(SB.row_words(r3), SB.app(SB.row_words(r4), SB.app(SB.row_words(r5), SB.app(SB.row_words(r6), SB.app(SB.row_words(r7), Nil{}))))))))) : {_ == 256n : Nat}
      %Equal.sym(Nat, SC.length(U32, SB.app(SB.row_words(r1), SB.app(SB.row_words(r2), SB.app(SB.row_words(r3), SB.app(SB.row_words(r4), SB.app(SB.row_words(r5), SB.app(SB.row_words(r6), SB.app(SB.row_words(r7), Nil{})))))))), Nat.add(32n, SC.length(U32, SB.app(SB.row_words(r2), SB.app(SB.row_words(r3), SB.app(SB.row_words(r4), SB.app(SB.row_words(r5), SB.app(SB.row_words(r6), SB.app(SB.row_words(r7), Nil{})))))))), len_row(r1, SB.app(SB.row_words(r2), SB.app(SB.row_words(r3), SB.app(SB.row_words(r4), SB.app(SB.row_words(r5), SB.app(SB.row_words(r6), SB.app(SB.row_words(r7), Nil{})))))))) : {Nat.add(32n, _) == 256n : Nat}
      %Equal.sym(Nat, SC.length(U32, SB.app(SB.row_words(r2), SB.app(SB.row_words(r3), SB.app(SB.row_words(r4), SB.app(SB.row_words(r5), SB.app(SB.row_words(r6), SB.app(SB.row_words(r7), Nil{}))))))), Nat.add(32n, SC.length(U32, SB.app(SB.row_words(r3), SB.app(SB.row_words(r4), SB.app(SB.row_words(r5), SB.app(SB.row_words(r6), SB.app(SB.row_words(r7), Nil{}))))))), len_row(r2, SB.app(SB.row_words(r3), SB.app(SB.row_words(r4), SB.app(SB.row_words(r5), SB.app(SB.row_words(r6), SB.app(SB.row_words(r7), Nil{}))))))) : {Nat.add(32n, Nat.add(32n, _)) == 256n : Nat}
      %Equal.sym(Nat, SC.length(U32, SB.app(SB.row_words(r3), SB.app(SB.row_words(r4), SB.app(SB.row_words(r5), SB.app(SB.row_words(r6), SB.app(SB.row_words(r7), Nil{})))))), Nat.add(32n, SC.length(U32, SB.app(SB.row_words(r4), SB.app(SB.row_words(r5), SB.app(SB.row_words(r6), SB.app(SB.row_words(r7), Nil{})))))), len_row(r3, SB.app(SB.row_words(r4), SB.app(SB.row_words(r5), SB.app(SB.row_words(r6), SB.app(SB.row_words(r7), Nil{})))))) : {Nat.add(32n, Nat.add(32n, Nat.add(32n, _))) == 256n : Nat}
      %Equal.sym(Nat, SC.length(U32, SB.app(SB.row_words(r4), SB.app(SB.row_words(r5), SB.app(SB.row_words(r6), SB.app(SB.row_words(r7), Nil{}))))), Nat.add(32n, SC.length(U32, SB.app(SB.row_words(r5), SB.app(SB.row_words(r6), SB.app(SB.row_words(r7), Nil{}))))), len_row(r4, SB.app(SB.row_words(r5), SB.app(SB.row_words(r6), SB.app(SB.row_words(r7), Nil{}))))) : {Nat.add(32n, Nat.add(32n, Nat.add(32n, Nat.add(32n, _)))) == 256n : Nat}
      %Equal.sym(Nat, SC.length(U32, SB.app(SB.row_words(r5), SB.app(SB.row_words(r6), SB.app(SB.row_words(r7), Nil{})))), Nat.add(32n, SC.length(U32, SB.app(SB.row_words(r6), SB.app(SB.row_words(r7), Nil{})))), len_row(r5, SB.app(SB.row_words(r6), SB.app(SB.row_words(r7), Nil{})))) : {Nat.add(32n, Nat.add(32n, Nat.add(32n, Nat.add(32n, Nat.add(32n, _))))) == 256n : Nat}
      %Equal.sym(Nat, SC.length(U32, SB.app(SB.row_words(r6), SB.app(SB.row_words(r7), Nil{}))), Nat.add(32n, SC.length(U32, SB.app(SB.row_words(r7), Nil{}))), len_row(r6, SB.app(SB.row_words(r7), Nil{}))) : {Nat.add(32n, Nat.add(32n, Nat.add(32n, Nat.add(32n, Nat.add(32n, Nat.add(32n, _)))))) == 256n : Nat}
      %Equal.sym(Nat, SC.length(U32, SB.app(SB.row_words(r7), Nil{})), Nat.add(32n, SC.length(U32, Nil{})), len_row(r7, Nil{})) : {Nat.add(32n, Nat.add(32n, Nat.add(32n, Nat.add(32n, Nat.add(32n, Nat.add(32n, Nat.add(32n, _))))))) == 256n : Nat}
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

# ---------------------------------------------------------------- writing block b

# Words ws stored from word i on, one Array.set each (the reference for
# access.bend's X.put).
def wr(ws: List<&2, U32>, +i: Nat, a: Array<U32>) -> Array<U32>:
  match ws:
    case Nil{}:
      a
    case w <> rest:
      wr(rest, Nat.add(i, 1n), Array.set(U32, a, U32.from_nat(i), w))

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
def wr_words(+d: Nat, +ws: List<&2, U32>, +i: Nat, +V: List<&2, U32>, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hl: {SC.length(U32, V) == SC.pow2(d) : Nat}, +hi: {Nat.is_le(Nat.add(i, SC.length(U32, ws)), SC.pow2(d)) == True{} : Bool}) -> {wr(ws, i, AR.thaw(U32, tree(d, V))) == AR.thaw(U32, tree(d, splice(ws, i, V))) : Array<U32>}:
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
      %Equal.sym(Array<U32>, Array.set(U32, AR.thaw(U32, t), U32.from_nat(i), w), AR.thaw(U32, AR.upd(U32, d, t, U32.to_nat(U32.from_nat(i)), w)), es) : {wr(rest, Nat.add(i, 1n), _) == AR.thaw(U32, tree(d, splice(rest, Nat.add(i, 1n), V2))) : Array<U32>}
      %Equal.sym(Array<U32>, AR.thaw(U32, AR.upd(U32, d, t, U32.to_nat(U32.from_nat(i)), w)), AR.thaw(U32, t2), Equal.cong(Nat, Array<U32>, z => AR.thaw(U32, AR.upd(U32, d, t, z, w)), U32.to_nat(U32.from_nat(i)), i, ei)) : {wr(rest, Nat.add(i, 1n), _) == AR.thaw(U32, tree(d, splice(rest, Nat.add(i, 1n), V2))) : Array<U32>}
      %Equal.sym(Array<U32>, AR.thaw(U32, t2), AR.thaw(U32, tree(d, V2)), Equal.cong(AR.Tree<U32>, Array<U32>, z => AR.thaw(U32, z), t2, tree(d, V2), e_ext)) : {wr(rest, Nat.add(i, 1n), _) == AR.thaw(U32, tree(d, splice(rest, Nat.add(i, 1n), V2))) : Array<U32>}
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

def take_upd(+V: List<&2, U32>, +i: Nat, +w: U32, +h: {Nat.is_lt(i, SC.length(U32, V)) == True{} : Bool}) -> {SC.take(U32, SC.update(U32, V, i, w), 1n+i) == SC.append(U32, SC.take(U32, V, i), Con{w, Nil{}}) : List<&2, U32>}:
  match V i:
    case Nil{} _:
      Empty.absurd({SC.take(U32, SC.update(U32, Nil{}, i, w), 1n+i) == SC.append(U32, SC.take(U32, Nil{}, i), Con{w, Nil{}}) : List<&2, U32>}, N.lt_zero_absurd(i, h))
    case Con{x, +r} 0n:
      Equal.cong(List<&2, U32>, List<&2, U32>, z => Con{w, z}, SC.take(U32, r, 0n), Nil{}, LL.sc_take_zero(U32, r))
    case Con{+x, +r} 1n+ +j:
      Equal.cong(List<&2, U32>, List<&2, U32>, z => Con{x, z}, SC.take(U32, SC.update(U32, r, j, w), 1n+j), SC.append(U32, SC.take(U32, r, j), Con{w, Nil{}}), take_upd(r, j, w, h))

# Storing ws from word i over V, when V ends exactly there: the first i words of V, then ws.
def splice_self(+ws: List<&2, U32>, +i: Nat, +V: List<&2, U32>, +h: {SC.length(U32, V) == Nat.add(i, SC.length(U32, ws)) : Nat}) -> {splice(ws, i, V) == SC.append(U32, SC.take(U32, V, i), ws) : List<&2, U32>}:
  match ws:
    case Nil{}:
      +hv = Equal.trans(Nat, SC.length(U32, V), Nat.add(i, 0n), i, h, N.add_zero(i))
      Equal.trans(List<&2, U32>, V, SC.take(U32, V, i), SC.append(U32, SC.take(U32, V, i), Nil{}), Equal.sym(List<&2, U32>, SC.take(U32, V, i), V, take_all(V, i, hv)), Equal.sym(List<&2, U32>, SC.append(U32, SC.take(U32, V, i), Nil{}), SC.take(U32, V, i), LL.append_nil(U32, SC.take(U32, V, i))))
    case +w <> +rest:
      +V2 = SC.update(U32, V, i, w)
      +hi = L.subst(Nat, z => {Nat.is_lt(i, z) == True{} : Bool}, Nat.add(i, 1n+SC.length(U32, rest)), SC.length(U32, V), Equal.sym(Nat, SC.length(U32, V), Nat.add(i, 1n+SC.length(U32, rest)), h), lt_add_succ(i, SC.length(U32, rest)))
      +h2 = Equal.trans(Nat, SC.length(U32, V2), SC.length(U32, V), Nat.add(Nat.add(i, 1n), SC.length(U32, rest)), LL.length_update(U32, V, i, w), Equal.trans(Nat, SC.length(U32, V), Nat.add(i, 1n+SC.length(U32, rest)), Nat.add(Nat.add(i, 1n), SC.length(U32, rest)), h, Equal.sym(Nat, Nat.add(Nat.add(i, 1n), SC.length(U32, rest)), Nat.add(i, 1n+SC.length(U32, rest)), add_one_assoc(i, SC.length(U32, rest)))))
      %Equal.sym(List<&2, U32>, splice(rest, Nat.add(i, 1n), V2), SC.append(U32, SC.take(U32, V2, Nat.add(i, 1n)), rest), splice_self(rest, Nat.add(i, 1n), V2, h2)) : {_ == SC.append(U32, SC.take(U32, V, i), Con{w, rest}) : List<&2, U32>}
      %Equal.sym(Nat, Nat.add(i, 1n), 1n+i, Equal.trans(Nat, Nat.add(i, 1n), 1n+Nat.add(i, 0n), 1n+i, N.add_succ(i, 0n), Equal.cong(Nat, Nat, z => 1n+z, Nat.add(i, 0n), i, N.add_zero(i)))) : {SC.append(U32, SC.take(U32, V2, _), rest) == SC.append(U32, SC.take(U32, V, i), Con{w, rest}) : List<&2, U32>}
      %Equal.sym(List<&2, U32>, SC.take(U32, V2, 1n+i), SC.append(U32, SC.take(U32, V, i), Con{w, Nil{}}), take_upd(V, i, w, hi)) : {SC.append(U32, _, rest) == SC.append(U32, SC.take(U32, V, i), Con{w, rest}) : List<&2, U32>}
      LL.append_assoc(U32, SC.take(U32, V, i), Con{w, Nil{}}, rest)

def splice_full(+b: A.Block, +v: A.Block) -> {splice(SB.words(v), 0n, SB.words(b)) == SB.words(v) : List<&2, U32>}:
  Equal.trans(List<&2, U32>, splice(SB.words(v), 0n, SB.words(b)), SC.append(U32, SC.take(U32, SB.words(b), 0n), SB.words(v)), SB.words(v),
    splice_self(SB.words(v), 0n, SB.words(b), Equal.trans(Nat, SC.length(U32, SB.words(b)), 256n, SC.length(U32, SB.words(v)), words_len(b), Equal.sym(Nat, SC.length(U32, SB.words(v)), 256n, words_len(v)))),
    Equal.cong(List<&2, U32>, List<&2, U32>, z => SC.append(U32, z, SB.words(v)), SC.take(U32, SB.words(b), 0n), Nil{}, LL.sc_take_zero(U32, SB.words(b))))

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
