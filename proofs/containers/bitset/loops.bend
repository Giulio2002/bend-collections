import Base
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../../lib/list.bend as LL
import ../../lib/array.bend as A
import ../../../spec/lib/common.bend as SC
import ../../../src/containers/bitset.bend as B
import ./fastcount.bend as FC
import ./model.bend as MD
import ./walk.bend as WK
import ./listx.bend as LX
import ./arr.bend as AR

# The two read-only whole-array loops of src/bitset.bend (`count_go` and
# `members_go`) compute exactly what the word-list model of
# proofs/bitset/model.bend says, on the list of the array's slots.

# q + (1 + r) <= P  =>  q < P
def lt_of_sum(+q: Nat, +r: Nat, +p: Nat, +h: {Nat.is_le(Nat.add(q, 1n+r), p) == True{} : Bool}) -> {Nat.is_lt(q, p) == True{} : Bool}:
  N.lt_le_trans(q, Nat.add(q, 1n+r), p,
    %Equal.sym(Nat, Nat.add(q, 1n+r), 1n+Nat.add(q, r), N.add_succ(q, r)) : {Nat.is_lt(q, _) == True{} : Bool}
    N.le_lt_succ(q, Nat.add(q, r), N.le_add_right(q, r)),
    h)

def le_of_sum(+q: Nat, +r: Nat, +p: Nat, +h: {Nat.is_le(Nat.add(q, 1n+r), p) == True{} : Bool}) -> {Nat.is_le(Nat.add(1n+q, r), p) == True{} : Bool}:
  L.subst(Nat, x => {Nat.is_le(x, p) == True{} : Bool}, Nat.add(q, 1n+r), 1n+Nat.add(q, r), N.add_succ(q, r), h)

# The word at q, as the head of what remains from q.
def head_at(+d: Nat, +t: A.Tree<B.Wd>, +q: Nat, +pf: {A.perfect(B.Wd, d, t) == True{} : Bool}, +hq: {Nat.is_lt(q, SC.pow2(d)) == True{} : Bool}) -> {SC.drop(U32, AR.ws(t), q) == Con{WK.nthw(AR.ws(t), q), SC.drop(U32, AR.ws(t), 1n+q)} : List<&2, U32>}:
  LX.drop_cons(U32, AR.ws(t), q, WK.nthw(AR.ws(t), q),
    WK.nthw_nth(AR.ws(t), q,
      L.subst(Nat, z => {Nat.is_lt(q, z) == True{} : Bool}, SC.pow2(d), SC.length(U32, AR.ws(t)),
        Equal.sym(Nat, SC.length(U32, AR.ws(t)), SC.pow2(d), AR.ws_length(d, t, pf)), hq)))

# ---- count ----

def count_go_ok(m: Nat, +d: Nat, +t: A.Tree<B.Wd>, +q: Nat, +acc: Nat, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +pf: {A.perfect(B.Wd, d, t) == True{} : Bool}, +hm: {Nat.is_le(Nat.add(q, m), SC.pow2(d)) == True{} : Bool}) -> {B.count_go(m, (A.thaw(B.Wd, t), acc), d, q) == (A.thaw(B.Wd, t), Nat.add(acc, MD.count_words(SC.take(U32, SC.drop(U32, AR.ws(t), q), m)))) : Array<B.Wd> & Nat}:
  match m:
    case 0n:
      %Equal.sym(List<&2, U32>, SC.take(U32, SC.drop(U32, AR.ws(t), q), 0n), Nil{}, LX.take_zero(U32, SC.drop(U32, AR.ws(t), q))) : {(A.thaw(B.Wd, t), acc) == (A.thaw(B.Wd, t), Nat.add(acc, MD.count_words(_))) : Array<B.Wd> & Nat}
      %N.add_zero(acc) : {(A.thaw(B.Wd, t), _) == (A.thaw(B.Wd, t), Nat.add(acc, 0n)) : Array<B.Wd> & Nat}
      {==}
    case 1n+ +r:
      +hq = lt_of_sum(q, r, SC.pow2(d), hm)
      %Equal.sym(List<&2, U32>, SC.drop(U32, AR.ws(t), q), Con{WK.nthw(AR.ws(t), q), SC.drop(U32, AR.ws(t), 1n+q)}, head_at(d, t, q, pf, hq)) : {B.count_go(1n+r, (A.thaw(B.Wd, t), acc), d, q) == (A.thaw(B.Wd, t), Nat.add(acc, MD.count_words(SC.take(U32, _, 1n+r)))) : Array<B.Wd> & Nat}
      %N.add_assoc(acc, B.word_count(32n, WK.nthw(AR.ws(t), q)), MD.count_words(SC.take(U32, SC.drop(U32, AR.ws(t), 1n+q), r))) : {B.count_go(1n+r, (A.thaw(B.Wd, t), acc), d, q) == (A.thaw(B.Wd, t), _) : Array<B.Wd> & Nat}
      %Equal.sym(Array<B.Wd> & U32, B.read(A.thaw(B.Wd, t), d, q), (A.thaw(B.Wd, t), WK.nthw(AR.ws(t), q)), AR.read_ok(d, t, q, hd, hq, pf)) : {B.count_go(r, B.count_add(_, acc), d, 1n+q) == (A.thaw(B.Wd, t), Nat.add(Nat.add(acc, B.word_count(32n, WK.nthw(AR.ws(t), q))), MD.count_words(SC.take(U32, SC.drop(U32, AR.ws(t), 1n+q), r)))) : Array<B.Wd> & Nat}
      %Equal.sym(Nat, B.count_word(WK.nthw(AR.ws(t), q), acc, U32.is_eq(WK.nthw(AR.ws(t), q), 0)), Nat.add(acc, B.word_count(32n, WK.nthw(AR.ws(t), q))), FC.count_word_ok(WK.nthw(AR.ws(t), q), acc, U32.is_eq(WK.nthw(AR.ws(t), q), 0), {==})) : {B.count_go(r, (A.thaw(B.Wd, t), _), d, 1n+q) == (A.thaw(B.Wd, t), Nat.add(Nat.add(acc, B.word_count(32n, WK.nthw(AR.ws(t), q))), MD.count_words(SC.take(U32, SC.drop(U32, AR.ws(t), 1n+q), r)))) : Array<B.Wd> & Nat}
      count_go_ok(r, d, t, 1n+q, Nat.add(acc, B.word_count(32n, WK.nthw(AR.ws(t), q))), hd, pf, le_of_sum(q, r, SC.pow2(d), hm))

def full_range(+d: Nat, +t: A.Tree<B.Wd>, +pf: {A.perfect(B.Wd, d, t) == True{} : Bool}) -> {SC.take(U32, SC.drop(U32, AR.ws(t), 0n), SC.pow2(d)) == AR.ws(t) : List<&2, U32>}:
  %Equal.sym(List<&2, U32>, SC.drop(U32, AR.ws(t), 0n), AR.ws(t), LX.drop_zero(U32, AR.ws(t))) : {SC.take(U32, _, SC.pow2(d)) == AR.ws(t) : List<&2, U32>}
  %AR.ws_length(d, t, pf) : {SC.take(U32, AR.ws(t), _) == AR.ws(t) : List<&2, U32>}
  LX.take_all(U32, AR.ws(t))

def take_full(+d: Nat, +t: A.Tree<B.Wd>, +pf: {A.perfect(B.Wd, d, t) == True{} : Bool}) -> {SC.take(U32, AR.ws(t), SC.pow2(d)) == AR.ws(t) : List<&2, U32>}:
  %AR.ws_length(d, t, pf) : {SC.take(U32, AR.ws(t), _) == AR.ws(t) : List<&2, U32>}
  LX.take_all(U32, AR.ws(t))

def count_ok(+d: Nat, +t: A.Tree<B.Wd>, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +pf: {A.perfect(B.Wd, d, t) == True{} : Bool}) -> {B.count_go(SC.pow2(d), (A.thaw(B.Wd, t), 0n), d, 0n) == (A.thaw(B.Wd, t), MD.count_words(AR.ws(t))) : Array<B.Wd> & Nat}:
  Equal.trans(Array<B.Wd> & Nat,
    B.count_go(SC.pow2(d), (A.thaw(B.Wd, t), 0n), d, 0n),
    (A.thaw(B.Wd, t), Nat.add(0n, MD.count_words(SC.take(U32, SC.drop(U32, AR.ws(t), 0n), SC.pow2(d))))),
    (A.thaw(B.Wd, t), MD.count_words(AR.ws(t))),
    count_go_ok(SC.pow2(d), d, t, 0n, 0n, hd, pf, N.le_refl(SC.pow2(d))),
    Equal.cong(List<&2, U32>, Array<B.Wd> & Nat, z => (A.thaw(B.Wd, t), MD.count_words(z)),
      SC.take(U32, SC.drop(U32, AR.ws(t), 0n), SC.pow2(d)), AR.ws(t), full_range(d, t, pf)))

# ---- to_list ----

# members_words with an explicit tail, which is the shape members_go builds.
def mw_acc(ws: List<&2, U32>, +off: Nat, acc: List<&2, Nat>) -> List<&2, Nat>:
  match ws:
    case Nil{}:
      acc
    case Con{w, t}:
      B.word_members(32n, w, off, mw_acc(t, Nat.add(32n, off), acc))

def mw_nil(ws: List<&2, U32>, +off: Nat) -> {mw_acc(ws, off, Nil{}) == MD.members_words(ws, off) : List<&2, Nat>}:
  match ws:
    case Nil{}:
      {==}
    case Con{+w, +t}:
      Equal.cong(List<&2, Nat>, List<&2, Nat>, z => B.word_members(32n, w, off, z),
        mw_acc(t, Nat.add(32n, off), Nil{}), MD.members_words(t, Nat.add(32n, off)),
        mw_nil(t, Nat.add(32n, off)))

def off_shift(+x: Nat, +off: Nat) -> {Nat.add(x, Nat.add(32n, off)) == Nat.add(Nat.add(32n, x), off) : Nat}:
  Equal.trans(Nat, Nat.add(x, Nat.add(32n, off)), Nat.add(Nat.add(x, 32n), off), Nat.add(Nat.add(32n, x), off),
    Equal.sym(Nat, Nat.add(Nat.add(x, 32n), off), Nat.add(x, Nat.add(32n, off)), N.add_assoc(x, 32n, off)),
    Equal.cong(Nat, Nat, z => Nat.add(z, off), Nat.add(x, 32n), Nat.add(32n, x), N.add_comm(x, 32n)))

def mw_snoc(zs: List<&2, U32>, +off: Nat, +w: U32, acc: List<&2, Nat>) -> {mw_acc(SC.snoc(U32, zs, w), off, acc) == mw_acc(zs, off, B.word_members(32n, w, Nat.add(Nat.mul(SC.length(U32, zs), 32n), off), acc)) : List<&2, Nat>}:
  match zs:
    case Nil{}:
      {==}
    case Con{+z, +t}:
      %off_shift(Nat.mul(SC.length(U32, t), 32n), off) : {B.word_members(32n, z, off, mw_acc(SC.snoc(U32, t, w), Nat.add(32n, off), acc)) == B.word_members(32n, z, off, mw_acc(t, Nat.add(32n, off), B.word_members(32n, w, _, acc))) : List<&2, Nat>}
      Equal.cong(List<&2, Nat>, List<&2, Nat>, y => B.word_members(32n, z, off, y),
        mw_acc(SC.snoc(U32, t, w), Nat.add(32n, off), acc),
        mw_acc(t, Nat.add(32n, off), B.word_members(32n, w, Nat.add(Nat.mul(SC.length(U32, t), 32n), Nat.add(32n, off)), acc)),
        mw_snoc(t, Nat.add(32n, off), w, acc))

def take_len(+d: Nat, +t: A.Tree<B.Wd>, +r: Nat, +pf: {A.perfect(B.Wd, d, t) == True{} : Bool}, +hr: {Nat.is_lt(r, SC.pow2(d)) == True{} : Bool}) -> {SC.length(U32, SC.take(U32, AR.ws(t), r)) == r : Nat}:
  LL.sc_length_take(U32, AR.ws(t), r,
    N.lt_le(r, SC.length(U32, AR.ws(t)),
      L.subst(Nat, z => {Nat.is_lt(r, z) == True{} : Bool}, SC.pow2(d), SC.length(U32, AR.ws(t)),
        Equal.sym(Nat, SC.length(U32, AR.ws(t)), SC.pow2(d), AR.ws_length(d, t, pf)), hr)))

def members_go_ok(m: Nat, +d: Nat, +t: A.Tree<B.Wd>, +acc: List<&2, Nat>, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +pf: {A.perfect(B.Wd, d, t) == True{} : Bool}, +hm: {Nat.is_le(m, SC.pow2(d)) == True{} : Bool}) -> {B.members_go(m, (A.thaw(B.Wd, t), acc), d) == (A.thaw(B.Wd, t), mw_acc(SC.take(U32, AR.ws(t), m), 0n, acc)) : Array<B.Wd> & List<&2, Nat>}:
  match m:
    case 0n:
      %Equal.sym(List<&2, U32>, SC.take(U32, AR.ws(t), 0n), Nil{}, LX.take_zero(U32, AR.ws(t))) : {(A.thaw(B.Wd, t), acc) == (A.thaw(B.Wd, t), mw_acc(_, 0n, acc)) : Array<B.Wd> & List<&2, Nat>}
      {==}
    case 1n+ +r:
      +hr = N.lt_le_trans(r, 1n+r, SC.pow2(d), N.lt_succ(r), hm)
      +hnth = WK.nthw_nth(AR.ws(t), r,
        L.subst(Nat, z => {Nat.is_lt(r, z) == True{} : Bool}, SC.pow2(d), SC.length(U32, AR.ws(t)),
          Equal.sym(Nat, SC.length(U32, AR.ws(t)), SC.pow2(d), AR.ws_length(d, t, pf)), hr))
      %Equal.sym(List<&2, U32>, SC.take(U32, AR.ws(t), 1n+r), SC.snoc(U32, SC.take(U32, AR.ws(t), r), WK.nthw(AR.ws(t), r)), LX.take_succ(U32, AR.ws(t), r, WK.nthw(AR.ws(t), r), hnth)) : {B.members_go(1n+r, (A.thaw(B.Wd, t), acc), d) == (A.thaw(B.Wd, t), mw_acc(_, 0n, acc)) : Array<B.Wd> & List<&2, Nat>}
      %Equal.sym(List<&2, Nat>, mw_acc(SC.snoc(U32, SC.take(U32, AR.ws(t), r), WK.nthw(AR.ws(t), r)), 0n, acc), mw_acc(SC.take(U32, AR.ws(t), r), 0n, B.word_members(32n, WK.nthw(AR.ws(t), r), Nat.add(Nat.mul(SC.length(U32, SC.take(U32, AR.ws(t), r)), 32n), 0n), acc)), mw_snoc(SC.take(U32, AR.ws(t), r), 0n, WK.nthw(AR.ws(t), r), acc)) : {B.members_go(1n+r, (A.thaw(B.Wd, t), acc), d) == (A.thaw(B.Wd, t), _) : Array<B.Wd> & List<&2, Nat>}
      %Equal.sym(Nat, SC.length(U32, SC.take(U32, AR.ws(t), r)), r, take_len(d, t, r, pf, hr)) : {B.members_go(1n+r, (A.thaw(B.Wd, t), acc), d) == (A.thaw(B.Wd, t), mw_acc(SC.take(U32, AR.ws(t), r), 0n, B.word_members(32n, WK.nthw(AR.ws(t), r), Nat.add(Nat.mul(_, 32n), 0n), acc))) : Array<B.Wd> & List<&2, Nat>}
      %Equal.sym(Nat, Nat.add(Nat.mul(r, 32n), 0n), Nat.mul(r, 32n), N.add_zero(Nat.mul(r, 32n))) : {B.members_go(1n+r, (A.thaw(B.Wd, t), acc), d) == (A.thaw(B.Wd, t), mw_acc(SC.take(U32, AR.ws(t), r), 0n, B.word_members(32n, WK.nthw(AR.ws(t), r), _, acc))) : Array<B.Wd> & List<&2, Nat>}
      %Equal.sym(Array<B.Wd> & U32, B.read(A.thaw(B.Wd, t), d, r), (A.thaw(B.Wd, t), WK.nthw(AR.ws(t), r)), AR.read_ok(d, t, r, hd, hr, pf)) : {B.members_go(r, B.members_cons(_, Nat.mul(r, 32n), acc), d) == (A.thaw(B.Wd, t), mw_acc(SC.take(U32, AR.ws(t), r), 0n, B.word_members(32n, WK.nthw(AR.ws(t), r), Nat.mul(r, 32n), acc))) : Array<B.Wd> & List<&2, Nat>}
      %Equal.sym(List<&2, Nat>, B.members_word(WK.nthw(AR.ws(t), r), Nat.mul(r, 32n), acc, U32.is_eq(WK.nthw(AR.ws(t), r), 0)), B.word_members(32n, WK.nthw(AR.ws(t), r), Nat.mul(r, 32n), acc), FC.members_word_ok(WK.nthw(AR.ws(t), r), Nat.mul(r, 32n), acc, U32.is_eq(WK.nthw(AR.ws(t), r), 0), {==})) : {B.members_go(r, (A.thaw(B.Wd, t), _), d) == (A.thaw(B.Wd, t), mw_acc(SC.take(U32, AR.ws(t), r), 0n, B.word_members(32n, WK.nthw(AR.ws(t), r), Nat.mul(r, 32n), acc))) : Array<B.Wd> & List<&2, Nat>}
      members_go_ok(r, d, t, B.word_members(32n, WK.nthw(AR.ws(t), r), Nat.mul(r, 32n), acc), hd, pf, N.lt_le(r, SC.pow2(d), hr))

def to_list_ok(+d: Nat, +t: A.Tree<B.Wd>, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +pf: {A.perfect(B.Wd, d, t) == True{} : Bool}) -> {B.members_go(SC.pow2(d), (A.thaw(B.Wd, t), Nil{}), d) == (A.thaw(B.Wd, t), MD.members_words(AR.ws(t), 0n)) : Array<B.Wd> & List<&2, Nat>}:
  Equal.trans(Array<B.Wd> & List<&2, Nat>,
    B.members_go(SC.pow2(d), (A.thaw(B.Wd, t), Nil{}), d),
    (A.thaw(B.Wd, t), mw_acc(SC.take(U32, AR.ws(t), SC.pow2(d)), 0n, Nil{})),
    (A.thaw(B.Wd, t), MD.members_words(AR.ws(t), 0n)),
    members_go_ok(SC.pow2(d), d, t, Nil{}, hd, pf, N.le_refl(SC.pow2(d))),
    Equal.trans(Array<B.Wd> & List<&2, Nat>,
      (A.thaw(B.Wd, t), mw_acc(SC.take(U32, AR.ws(t), SC.pow2(d)), 0n, Nil{})),
      (A.thaw(B.Wd, t), mw_acc(AR.ws(t), 0n, Nil{})),
      (A.thaw(B.Wd, t), MD.members_words(AR.ws(t), 0n)),
      Equal.cong(List<&2, U32>, Array<B.Wd> & List<&2, Nat>, z => (A.thaw(B.Wd, t), mw_acc(z, 0n, Nil{})),
        SC.take(U32, AR.ws(t), SC.pow2(d)), AR.ws(t), take_full(d, t, pf)),
      Equal.cong(List<&2, Nat>, Array<B.Wd> & List<&2, Nat>, z => (A.thaw(B.Wd, t), z),
        mw_acc(AR.ws(t), 0n, Nil{}), MD.members_words(AR.ws(t), 0n), mw_nil(AR.ws(t), 0n))))
