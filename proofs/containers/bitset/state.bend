import Base
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../../lib/list.bend as LL
import ../../../spec/lib/common.bend as SC
import ../../../spec/containers/bitset.bend as S
import ../../../src/containers/bitset.bend as B
import ../../lib/array.bend as A
import ./model.bend as MD
import ./arr.bend as AR
import ./depth.bend as DP
import ./lists.bend as BL
import ./word.bend as W

# Abstraction and invariant of the packed representation.
#   flat(ws)  all stored bits, word by word, bit 0 first
#   abs       the first `len` stored bits
#   inv       len <= |flat| < len + 32 (exactly ceil(len/32) words) and
#             every stored bit at position >= len is zero (masked tail)

def flat(ws: List<&2, U32>) -> List<&2, Bool>:
  match ws:
    case Nil{}:
      Nil{}
    case Con{w, t}:
      SC.append(Bool, W.ubits(w), flat(t))

def invf(+n: Nat, +xs: List<&2, Bool>) -> Bool:
  Bool.and(Nat.is_le(n, SC.length(Bool, xs)), BL.allf(SC.drop(Bool, xs, n)))

def inv_le(+n: Nat, +xs: List<&2, Bool>, +g: {invf(n, xs) == True{} : Bool}) -> {Nat.is_le(n, SC.length(Bool, xs)) == True{} : Bool}:
  L.and_left(Nat.is_le(n, SC.length(Bool, xs)), BL.allf(SC.drop(Bool, xs, n)), g)

def inv_tail(+n: Nat, +xs: List<&2, Bool>, +g: {invf(n, xs) == True{} : Bool}) -> {BL.allf(SC.drop(Bool, xs, n)) == True{} : Bool}:
  L.and_right(Nat.is_le(n, SC.length(Bool, xs)), BL.allf(SC.drop(Bool, xs, n)), g)

def inv_mk(+n: Nat, +xs: List<&2, Bool>, +a: {Nat.is_le(n, SC.length(Bool, xs)) == True{} : Bool}, +c: {BL.allf(SC.drop(Bool, xs, n)) == True{} : Bool}) -> {invf(n, xs) == True{} : Bool}:
  L.and_intro(Nat.is_le(n, SC.length(Bool, xs)), BL.allf(SC.drop(Bool, xs, n)), a, c)

# The logical length is len.
def length_abs(+n: Nat, +xs: List<&2, Bool>, +g: {invf(n, xs) == True{} : Bool}) -> {SC.length(Bool, SC.take(Bool, xs, n)) == n : Nat}:
  BL.length_take(xs, n, inv_le(n, xs, g))

# The stored bits are the logical bits followed by the zero tail.
def split(+n: Nat, +xs: List<&2, Bool>) -> {xs == SC.append(Bool, SC.take(Bool, xs, n), SC.drop(Bool, xs, n)) : List<&2, Bool>}:
  Equal.sym(List<&2, Bool>, SC.append(Bool, SC.take(Bool, xs, n), SC.drop(Bool, xs, n)), xs, BL.take_drop(xs, n))

def take32(+w: U32) -> {SC.take(Bool, W.ubits(w), 32n) == W.ubits(w) : List<&2, Bool>}:
  L.subst(Nat, k => {SC.take(Bool, W.ubits(w), k) == W.ubits(w) : List<&2, Bool>}, SC.length(Bool, W.ubits(w)), 32n, W.ulen(w), BL.take_all(W.ubits(w)))

def length_flat_cons(+w: U32, +t: List<&2, U32>) -> {SC.length(Bool, flat(Con{w, t})) == Nat.add(32n, SC.length(Bool, flat(t))) : Nat}:
  %Equal.sym(Nat, SC.length(Bool, SC.append(Bool, W.ubits(w), flat(t))), Nat.add(SC.length(Bool, W.ubits(w)), SC.length(Bool, flat(t))), LL.length_append(Bool, W.ubits(w), flat(t))) : {_ == Nat.add(32n, SC.length(Bool, flat(t))) : Nat}
  %Equal.sym(Nat, SC.length(Bool, W.ubits(w)), 32n, W.ulen(w)) : {Nat.add(_, SC.length(Bool, flat(t))) == Nat.add(32n, SC.length(Bool, flat(t))) : Nat}
  {==}

# ---- word-list walks ----

def get_case(+w: U32, +t: List<&2, U32>, +i: Nat, b: Bool, +eb: {Nat.is_lt(i, 32n) == b : Bool}, +h: {Nat.is_lt(i, Nat.add(32n, SC.length(Bool, flat(t)))) == True{} : Bool}, ih: @+h2: {Nat.is_lt(Nat.sub(i, 32n), SC.length(Bool, flat(t))) == True{} : Bool} -> {Some{MD.get_walk(t, Nat.sub(i, 32n))} == SC.nth(Bool, flat(t), Nat.sub(i, 32n)) : Maybe<&2, Bool>}) -> {Some{MD.get_pick(b, w, i, MD.get_walk(t, Nat.sub(i, 32n)))} == SC.nth(Bool, SC.append(Bool, W.ubits(w), flat(t)), i) : Maybe<&2, Bool>}:
  match b:
    case True{}:
      +hl = L.subst(Nat, k => {Nat.is_lt(i, k) == True{} : Bool}, 32n, SC.length(Bool, W.ubits(w)), Equal.sym(Nat, SC.length(Bool, W.ubits(w)), 32n, W.ulen(w)), eb)
      Equal.trans(Maybe<&2, Bool>, Some{B.word_get(w, i)}, SC.nth(Bool, W.ubits(w), i), SC.nth(Bool, SC.append(Bool, W.ubits(w), flat(t)), i),
        W.word_get(w, i, eb),
        Equal.sym(Maybe<&2, Bool>, SC.nth(Bool, SC.append(Bool, W.ubits(w), flat(t)), i), SC.nth(Bool, W.ubits(w), i), LL.nth_append_left(Bool, W.ubits(w), flat(t), i, hl)))
    case False{}:
      +le = N.not_lt_le(i, 32n, eb)
      +hr = L.subst(Nat, k => {Nat.is_le(k, i) == True{} : Bool}, 32n, SC.length(Bool, W.ubits(w)), Equal.sym(Nat, SC.length(Bool, W.ubits(w)), 32n, W.ulen(w)), le)
      %Equal.sym(Maybe<&2, Bool>, SC.nth(Bool, SC.append(Bool, W.ubits(w), flat(t)), i), SC.nth(Bool, flat(t), Nat.sub(i, SC.length(Bool, W.ubits(w)))), LL.nth_append_right(Bool, W.ubits(w), flat(t), i, hr)) : {Some{MD.get_walk(t, Nat.sub(i, 32n))} == _ : Maybe<&2, Bool>}
      %Equal.sym(Nat, SC.length(Bool, W.ubits(w)), 32n, W.ulen(w)) : {Some{MD.get_walk(t, Nat.sub(i, 32n))} == SC.nth(Bool, flat(t), Nat.sub(i, _)) : Maybe<&2, Bool>}
      ih(N.sub_lt(i, 32n, SC.length(Bool, flat(t)), le, h))

def get_walk(+ws: List<&2, U32>, +i: Nat, +h: {Nat.is_lt(i, SC.length(Bool, flat(ws))) == True{} : Bool}) -> {Some{MD.get_walk(ws, i)} == SC.nth(Bool, flat(ws), i) : Maybe<&2, Bool>}:
  match ws:
    case Nil{}:
      Empty.absurd({Some{MD.get_walk(Nil{}, i)} == SC.nth(Bool, flat(Nil{}), i) : Maybe<&2, Bool>}, N.lt_zero_absurd(i, h))
    case Con{w, t}:
      get_case(w, t, i, Nat.is_lt(i, 32n), {==}, L.subst(Nat, k => {Nat.is_lt(i, k) == True{} : Bool}, SC.length(Bool, flat(Con{w, t})), Nat.add(32n, SC.length(Bool, flat(t))), length_flat_cons(w, t), h), h2 => get_walk(t, Nat.sub(i, 32n), h2))

def put_case(+v: Bool, +w: U32, +i: Nat, +t: List<&2, U32>, b: Bool, +eb: {Nat.is_lt(i, 32n) == b : Bool}, +ih: {flat(MD.put_walk(t, Nat.sub(i, 32n), v)) == SC.update(Bool, flat(t), Nat.sub(i, 32n), v) : List<&2, Bool>}) -> {flat(MD.put_pick(b, v, w, i, t, MD.put_walk(t, Nat.sub(i, 32n), v))) == SC.update(Bool, SC.append(Bool, W.ubits(w), flat(t)), i, v) : List<&2, Bool>}:
  match b:
    case True{}:
      +hl = L.subst(Nat, k => {Nat.is_lt(i, k) == True{} : Bool}, 32n, SC.length(Bool, W.ubits(w)), Equal.sym(Nat, SC.length(Bool, W.ubits(w)), 32n, W.ulen(w)), eb)
      %Equal.sym(List<&2, Bool>, SC.update(Bool, SC.append(Bool, W.ubits(w), flat(t)), i, v), SC.append(Bool, SC.update(Bool, W.ubits(w), i, v), flat(t)), LL.update_append_left(Bool, W.ubits(w), flat(t), i, v, hl)) : {SC.append(Bool, W.ubits(B.word_put(v, w, i)), flat(t)) == _ : List<&2, Bool>}
      %Equal.sym(List<&2, Bool>, W.ubits(B.word_put(v, w, i)), SC.update(Bool, W.ubits(w), i, v), W.word_put(v, w, i, eb)) : {SC.append(Bool, _, flat(t)) == SC.append(Bool, SC.update(Bool, W.ubits(w), i, v), flat(t)) : List<&2, Bool>}
      {==}
    case False{}:
      +le = N.not_lt_le(i, 32n, eb)
      +hr = L.subst(Nat, k => {Nat.is_le(k, i) == True{} : Bool}, 32n, SC.length(Bool, W.ubits(w)), Equal.sym(Nat, SC.length(Bool, W.ubits(w)), 32n, W.ulen(w)), le)
      %Equal.sym(List<&2, Bool>, SC.update(Bool, SC.append(Bool, W.ubits(w), flat(t)), i, v), SC.append(Bool, W.ubits(w), SC.update(Bool, flat(t), Nat.sub(i, SC.length(Bool, W.ubits(w))), v)), LL.update_append_right(Bool, W.ubits(w), flat(t), i, v, hr)) : {SC.append(Bool, W.ubits(w), flat(MD.put_walk(t, Nat.sub(i, 32n), v))) == _ : List<&2, Bool>}
      %Equal.sym(Nat, SC.length(Bool, W.ubits(w)), 32n, W.ulen(w)) : {SC.append(Bool, W.ubits(w), flat(MD.put_walk(t, Nat.sub(i, 32n), v))) == SC.append(Bool, W.ubits(w), SC.update(Bool, flat(t), Nat.sub(i, _), v)) : List<&2, Bool>}
      %Equal.sym(List<&2, Bool>, flat(MD.put_walk(t, Nat.sub(i, 32n), v)), SC.update(Bool, flat(t), Nat.sub(i, 32n), v), ih) : {SC.append(Bool, W.ubits(w), _) == SC.append(Bool, W.ubits(w), SC.update(Bool, flat(t), Nat.sub(i, 32n), v)) : List<&2, Bool>}
      {==}

def put_walk(+ws: List<&2, U32>, +i: Nat, +v: Bool) -> {flat(MD.put_walk(ws, i, v)) == SC.update(Bool, flat(ws), i, v) : List<&2, Bool>}:
  match ws:
    case Nil{}:
      {==}
    case Con{w, t}:
      put_case(v, w, i, t, Nat.is_lt(i, 32n), {==}, put_walk(t, Nat.sub(i, 32n), v))

def zip_words(+k: B.WordOp, +ws: List<&2, U32>, +vs: List<&2, U32>) -> {flat(MD.zip_words(k, ws, vs)) == BL.zipk(k, flat(ws), flat(vs)) : List<&2, Bool>}:
  match ws vs:
    case Nil{} _:
      {==}
    case Con{a, s} Nil{}:
      Equal.sym(List<&2, Bool>, BL.zipk(k, SC.append(Bool, W.ubits(a), flat(s)), Nil{}), Nil{}, BL.zipk_nil_r(k, SC.append(Bool, W.ubits(a), flat(s))))
    case Con{a, s} Con{b, t}:
      %Equal.sym(List<&2, Bool>, W.ubits(B.word_op(k, a, b)), BL.zipk(k, W.ubits(a), W.ubits(b)), W.u_op(k, a, b)) : {SC.append(Bool, _, flat(MD.zip_words(k, s, t))) == BL.zipk(k, SC.append(Bool, W.ubits(a), flat(s)), SC.append(Bool, W.ubits(b), flat(t))) : List<&2, Bool>}
      %Equal.sym(List<&2, Bool>, flat(MD.zip_words(k, s, t)), BL.zipk(k, flat(s), flat(t)), zip_words(k, s, t)) : {SC.append(Bool, BL.zipk(k, W.ubits(a), W.ubits(b)), _) == BL.zipk(k, SC.append(Bool, W.ubits(a), flat(s)), SC.append(Bool, W.ubits(b), flat(t))) : List<&2, Bool>}
      Equal.sym(List<&2, Bool>, BL.zipk(k, SC.append(Bool, W.ubits(a), flat(s)), SC.append(Bool, W.ubits(b), flat(t))), SC.append(Bool, BL.zipk(k, W.ubits(a), W.ubits(b)), BL.zipk(k, flat(s), flat(t))),
        BL.zipk_append(k, W.ubits(a), W.ubits(b), flat(s), flat(t), Equal.trans(Nat, SC.length(Bool, W.ubits(a)), 32n, SC.length(Bool, W.ubits(b)), W.ulen(a), Equal.sym(Nat, SC.length(Bool, W.ubits(b)), 32n, W.ulen(b)))))

def count_words(+ws: List<&2, U32>) -> {MD.count_words(ws) == S.count(flat(ws)) : Nat}:
  match ws:
    case Nil{}:
      {==}
    case Con{w, t}:
      %Equal.sym(Nat, B.word_count(32n, w), S.count(SC.take(Bool, W.ubits(w), 32n)), W.word_count(32n, w)) : {Nat.add(_, MD.count_words(t)) == S.count(SC.append(Bool, W.ubits(w), flat(t))) : Nat}
      %Equal.sym(List<&2, Bool>, SC.take(Bool, W.ubits(w), 32n), W.ubits(w), take32(w)) : {Nat.add(S.count(_), MD.count_words(t)) == S.count(SC.append(Bool, W.ubits(w), flat(t))) : Nat}
      %Equal.sym(Nat, MD.count_words(t), S.count(flat(t)), count_words(t)) : {Nat.add(S.count(W.ubits(w)), _) == S.count(SC.append(Bool, W.ubits(w), flat(t))) : Nat}
      Equal.sym(Nat, S.count(SC.append(Bool, W.ubits(w), flat(t))), Nat.add(S.count(W.ubits(w)), S.count(flat(t))), BL.count_append(W.ubits(w), flat(t)))

def members_words(+ws: List<&2, U32>, +off: Nat) -> {MD.members_words(ws, off) == S.members(flat(ws), off) : List<&2, Nat>}:
  match ws:
    case Nil{}:
      {==}
    case Con{w, t}:
      %Equal.sym(List<&2, Nat>, B.word_members(32n, w, off, MD.members_words(t, Nat.add(32n, off))), SC.append(Nat, S.members(SC.take(Bool, W.ubits(w), 32n), off), MD.members_words(t, Nat.add(32n, off))), W.word_members(32n, w, off, MD.members_words(t, Nat.add(32n, off)))) : {_ == S.members(SC.append(Bool, W.ubits(w), flat(t)), off) : List<&2, Nat>}
      %Equal.sym(List<&2, Bool>, SC.take(Bool, W.ubits(w), 32n), W.ubits(w), take32(w)) : {SC.append(Nat, S.members(_, off), MD.members_words(t, Nat.add(32n, off))) == S.members(SC.append(Bool, W.ubits(w), flat(t)), off) : List<&2, Nat>}
      %Equal.sym(List<&2, Nat>, MD.members_words(t, Nat.add(32n, off)), S.members(flat(t), Nat.add(32n, off)), members_words(t, Nat.add(32n, off))) : {SC.append(Nat, S.members(W.ubits(w), off), _) == S.members(SC.append(Bool, W.ubits(w), flat(t)), off) : List<&2, Nat>}
      %Equal.sym(List<&2, Nat>, S.members(SC.append(Bool, W.ubits(w), flat(t)), off), SC.append(Nat, S.members(W.ubits(w), off), S.members(flat(t), Nat.add(SC.length(Bool, W.ubits(w)), off))), BL.members_append(W.ubits(w), flat(t), off)) : {SC.append(Nat, S.members(W.ubits(w), off), S.members(flat(t), Nat.add(32n, off))) == _ : List<&2, Nat>}
      %Equal.sym(Nat, SC.length(Bool, W.ubits(w)), 32n, W.ulen(w)) : {SC.append(Nat, S.members(W.ubits(w), off), S.members(flat(t), Nat.add(32n, off))) == SC.append(Nat, S.members(W.ubits(w), off), S.members(flat(t), Nat.add(_, off))) : List<&2, Nat>}
      {==}

# ---- invariant preservation facts ----

def invf_update(+n: Nat, +xs: List<&2, Bool>, +i: Nat, +v: Bool, +h: {Nat.is_lt(i, n) == True{} : Bool}, +g: {invf(n, xs) == True{} : Bool}) -> {invf(n, SC.update(Bool, xs, i, v)) == True{} : Bool}:
  +el = Equal.sym(Nat, SC.length(Bool, SC.update(Bool, xs, i, v)), SC.length(Bool, xs), LL.length_update(Bool, xs, i, v))
  inv_mk(n, SC.update(Bool, xs, i, v),
    L.subst(Nat, k => {Nat.is_le(n, k) == True{} : Bool}, SC.length(Bool, xs), SC.length(Bool, SC.update(Bool, xs, i, v)), el, inv_le(n, xs, g)),
    L.subst(List<&2, Bool>, d => {BL.allf(d) == True{} : Bool}, SC.drop(Bool, xs, n), SC.drop(Bool, SC.update(Bool, xs, i, v), n), Equal.sym(List<&2, Bool>, SC.drop(Bool, SC.update(Bool, xs, i, v), n), SC.drop(Bool, xs, n), BL.drop_update(xs, i, v, n, h)), inv_tail(n, xs, g)))

def invf_zipk(+k: B.WordOp, +n: Nat, +xs: List<&2, Bool>, +ys: List<&2, Bool>, +gx: {invf(n, xs) == True{} : Bool}, +gy: {invf(n, ys) == True{} : Bool}) -> {invf(n, BL.zipk(k, xs, ys)) == True{} : Bool}:
  inv_mk(n, BL.zipk(k, xs, ys),
    BL.le_length_zipk(k, n, xs, ys, inv_le(n, xs, gx), inv_le(n, ys, gy)),
    %Equal.sym(List<&2, Bool>, SC.drop(Bool, BL.zipk(k, xs, ys), n), BL.zipk(k, SC.drop(Bool, xs, n), SC.drop(Bool, ys, n)), BL.drop_zipk(k, xs, ys, n)) : {BL.allf(_) == True{} : Bool}
    BL.allf_zipk(k, SC.drop(Bool, xs, n), SC.drop(Bool, ys, n), inv_tail(n, xs, gx), inv_tail(n, ys, gy)))

# put_walk as seen through the abstraction.
def put_abs(+n: Nat, +ws: List<&2, U32>, +i: Nat, +v: Bool) -> {SC.take(Bool, flat(MD.put_walk(ws, i, v)), n) == SC.update(Bool, SC.take(Bool, flat(ws), n), i, v) : List<&2, Bool>}:
  %Equal.sym(List<&2, Bool>, flat(MD.put_walk(ws, i, v)), SC.update(Bool, flat(ws), i, v), put_walk(ws, i, v)) : {SC.take(Bool, _, n) == SC.update(Bool, SC.take(Bool, flat(ws), n), i, v) : List<&2, Bool>}
  BL.take_update(flat(ws), i, v, n)

def put_inv(+n: Nat, +ws: List<&2, U32>, +i: Nat, +v: Bool, +h: {Nat.is_lt(i, n) == True{} : Bool}, +g: {invf(n, flat(ws)) == True{} : Bool}) -> {invf(n, flat(MD.put_walk(ws, i, v))) == True{} : Bool}:
  L.subst(List<&2, Bool>, x => {invf(n, x) == True{} : Bool}, SC.update(Bool, flat(ws), i, v), flat(MD.put_walk(ws, i, v)), Equal.sym(List<&2, Bool>, flat(MD.put_walk(ws, i, v)), SC.update(Bool, flat(ws), i, v), put_walk(ws, i, v)), invf_update(n, flat(ws), i, v, h, g))

# ---- the representation: a word array of depth d holding n logical bits ----
#
# Base.Array is linear, so (exactly as in proofs/dynamic_array) the statements
# are about `A.thaw(t)`, the array built from the Data mirror tree t.

def rep(+n: Nat, +d: Nat, +t: A.Tree<B.Wd>) -> Bool:
  Bool.and(Nat.is_eq(d, B.depth_for(n)), Bool.and(A.perfect(B.Wd, d, t), invf(n, flat(AR.ws(t)))))

def abs(+n: Nat, +t: A.Tree<B.Wd>) -> List<&2, Bool>:
  SC.take(Bool, flat(AR.ws(t)), n)

def rep_depth(+n: Nat, +d: Nat, +t: A.Tree<B.Wd>, +g: {rep(n, d, t) == True{} : Bool}) -> {Nat.is_eq(d, B.depth_for(n)) == True{} : Bool}:
  L.and_left(Nat.is_eq(d, B.depth_for(n)), Bool.and(A.perfect(B.Wd, d, t), invf(n, flat(AR.ws(t)))), g)

def rep_perfect(+n: Nat, +d: Nat, +t: A.Tree<B.Wd>, +g: {rep(n, d, t) == True{} : Bool}) -> {A.perfect(B.Wd, d, t) == True{} : Bool}:
  L.and_left(A.perfect(B.Wd, d, t), invf(n, flat(AR.ws(t))),
    L.and_right(Nat.is_eq(d, B.depth_for(n)), Bool.and(A.perfect(B.Wd, d, t), invf(n, flat(AR.ws(t)))), g))

def rep_invf(+n: Nat, +d: Nat, +t: A.Tree<B.Wd>, +g: {rep(n, d, t) == True{} : Bool}) -> {invf(n, flat(AR.ws(t))) == True{} : Bool}:
  L.and_right(A.perfect(B.Wd, d, t), invf(n, flat(AR.ws(t))),
    L.and_right(Nat.is_eq(d, B.depth_for(n)), Bool.and(A.perfect(B.Wd, d, t), invf(n, flat(AR.ws(t)))), g))

def rep_mk(+n: Nat, +d: Nat, +t: A.Tree<B.Wd>, +a: {Nat.is_eq(d, B.depth_for(n)) == True{} : Bool}, +b: {A.perfect(B.Wd, d, t) == True{} : Bool}, +c: {invf(n, flat(AR.ws(t))) == True{} : Bool}) -> {rep(n, d, t) == True{} : Bool}:
  L.and_intro(Nat.is_eq(d, B.depth_for(n)), Bool.and(A.perfect(B.Wd, d, t), invf(n, flat(AR.ws(t)))), a,
    L.and_intro(A.perfect(B.Wd, d, t), invf(n, flat(AR.ws(t))), b, c))

def rep_lt(+n: Nat, +d: Nat, +t: A.Tree<B.Wd>, +g: {rep(n, d, t) == True{} : Bool}) -> {Nat.is_lt(d, 32n) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_lt(z, 32n) == True{} : Bool}, B.depth_for(n), d,
    Equal.sym(Nat, d, B.depth_for(n), N.eq_from_is_eq(d, B.depth_for(n), rep_depth(n, d, t, g))),
    DP.depth_lt(n))

# ---- the all-zero array ----

def length_flat(ws: List<&2, U32>) -> {SC.length(Bool, flat(ws)) == Nat.mul(SC.length(U32, ws), 32n) : Nat}:
  match ws:
    case Nil{}:
      {==}
    case Con{+w, +t}:
      %Equal.sym(Nat, SC.length(Bool, flat(Con{w, t})), Nat.add(32n, SC.length(Bool, flat(t))), length_flat_cons(w, t)) : {_ == Nat.mul(SC.length(U32, Con{w, t}), 32n) : Nat}
      Equal.cong(Nat, Nat, z => Nat.add(32n, z), SC.length(Bool, flat(t)), Nat.mul(SC.length(U32, t), 32n), length_flat(t))

def flat_zeros(+m: Nat) -> {BL.allf(flat(SC.replicate(U32, m, 0))) == True{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+p:
      BL.allf_append(W.ubits(0), flat(SC.replicate(U32, p, 0)), {==}, flat_zeros(p))

def zero_length(+d: Nat) -> {SC.length(Bool, flat(AR.ws(A.trep(B.Wd, d, B.W{0})))) == Nat.mul(SC.pow2(d), 32n) : Nat}:
  %Equal.sym(List<&2, U32>, AR.ws(A.trep(B.Wd, d, B.W{0})), SC.replicate(U32, SC.pow2(d), 0), AR.ws_trep(d, 0)) : {SC.length(Bool, flat(_)) == Nat.mul(SC.pow2(d), 32n) : Nat}
  %LL.length_replicate(U32, SC.pow2(d), 0) : {SC.length(Bool, flat(SC.replicate(U32, SC.pow2(d), 0))) == Nat.mul(_, 32n) : Nat}
  length_flat(SC.replicate(U32, SC.pow2(d), 0))

def zero_allf(+d: Nat) -> {BL.allf(flat(AR.ws(A.trep(B.Wd, d, B.W{0})))) == True{} : Bool}:
  %Equal.sym(List<&2, U32>, AR.ws(A.trep(B.Wd, d, B.W{0})), SC.replicate(U32, SC.pow2(d), 0), AR.ws_trep(d, 0)) : {BL.allf(flat(_)) == True{} : Bool}
  flat_zeros(SC.pow2(d))

# `fits` is the documented capacity condition: the depth the representation is
# allowed to reach (2^31 words = 2^36 bits) must cover n.
def new_le(+n: Nat, +h: {Nat.is_le(n, Nat.mul(SC.pow2(B.depth_for(n)), 32n)) == True{} : Bool}) -> {Nat.is_le(n, SC.length(Bool, flat(AR.ws(A.trep(B.Wd, B.depth_for(n), B.W{0}))))) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_le(n, z) == True{} : Bool}, Nat.mul(SC.pow2(B.depth_for(n)), 32n), SC.length(Bool, flat(AR.ws(A.trep(B.Wd, B.depth_for(n), B.W{0})))),
    Equal.sym(Nat, SC.length(Bool, flat(AR.ws(A.trep(B.Wd, B.depth_for(n), B.W{0})))), Nat.mul(SC.pow2(B.depth_for(n)), 32n), zero_length(B.depth_for(n))), h)

def new_rep(+n: Nat, +h: {Nat.is_le(n, Nat.mul(SC.pow2(B.depth_for(n)), 32n)) == True{} : Bool}) -> {rep(n, B.depth_for(n), A.trep(B.Wd, B.depth_for(n), B.W{0})) == True{} : Bool}:
  rep_mk(n, B.depth_for(n), A.trep(B.Wd, B.depth_for(n), B.W{0}),
    N.is_eq_refl(B.depth_for(n)),
    A.trep_perfect(B.Wd, B.depth_for(n), B.W{0}),
    inv_mk(n, flat(AR.ws(A.trep(B.Wd, B.depth_for(n), B.W{0}))), new_le(n, h),
      BL.drop_allf(flat(AR.ws(A.trep(B.Wd, B.depth_for(n), B.W{0}))), n, zero_allf(B.depth_for(n)))))

def new_abs(+n: Nat, +h: {Nat.is_le(n, Nat.mul(SC.pow2(B.depth_for(n)), 32n)) == True{} : Bool}) -> {abs(n, A.trep(B.Wd, B.depth_for(n), B.W{0})) == S.new(n) : List<&2, Bool>}:
  BL.take_allf(flat(AR.ws(A.trep(B.Wd, B.depth_for(n), B.W{0}))), n, zero_allf(B.depth_for(n)), new_le(n, h))

# `new(n)` is that array, thawed.
def new_form(+n: Nat) -> {B.new(n) == B.BS{n, B.depth_for(n), A.thaw(B.Wd, A.trep(B.Wd, B.depth_for(n), B.W{0}))} : B.Bitset}:
  Equal.cong(Array<B.Wd>, B.Bitset, a => B.BS{n, B.depth_for(n), a},
    Array.new(B.Wd, B.depth_for(n), B.W{0}), A.thaw(B.Wd, A.trep(B.Wd, B.depth_for(n), B.W{0})),
    A.new(B.Wd, B.depth_for(n), B.W{0}))

# ---- the shadow: the Data mirror of a live bitset ----

type Sh is Data:
  Sh{len: Nat, depth: Nat, tree: A.Tree<B.Wd>}

def real(sh: Sh) -> B.Bitset:
  match sh:
    case Sh{n, d, t}:
      B.BS{n, d, A.thaw(B.Wd, t)}

def good(sh: Sh) -> Bool:
  match sh:
    case Sh{n, d, t}:
      rep(n, d, t)

def model(sh: Sh) -> List<&2, Bool>:
  match sh:
    case Sh{n, d, t}:
      abs(n, t)

# The stored bit count is 32 per word.
def flat_len(+d: Nat, +t: A.Tree<B.Wd>, +pf: {A.perfect(B.Wd, d, t) == True{} : Bool}) -> {SC.length(Bool, flat(AR.ws(t))) == Nat.mul(SC.pow2(d), 32n) : Nat}:
  %AR.ws_length(d, t, pf) : {SC.length(Bool, flat(AR.ws(t))) == Nat.mul(_, 32n) : Nat}
  length_flat(AR.ws(t))

# Any bitset satisfying the invariant is within the capacity.
def rep_fits(+n: Nat, +d: Nat, +t: A.Tree<B.Wd>, +g: {rep(n, d, t) == True{} : Bool}) -> {Nat.is_le(n, Nat.mul(SC.pow2(B.depth_for(n)), 32n)) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_le(n, Nat.mul(SC.pow2(z), 32n)) == True{} : Bool}, d, B.depth_for(n),
    N.eq_from_is_eq(d, B.depth_for(n), rep_depth(n, d, t, g)),
    L.subst(Nat, z => {Nat.is_le(n, z) == True{} : Bool}, SC.length(Bool, flat(AR.ws(t))), Nat.mul(SC.pow2(d), 32n),
      flat_len(d, t, rep_perfect(n, d, t, g)), inv_le(n, flat(AR.ws(t)), rep_invf(n, d, t, g))))

# A bit index below the logical size addresses a word inside the array.
def wordix_go(m: Nat, +i: Nat, b: Bool, +eb: {Nat.is_lt(i, 32n) == b : Bool}, +h: {Nat.is_lt(i, Nat.mul(m, 32n)) == True{} : Bool}) -> {Nat.is_lt(B.wordix(i), m) == True{} : Bool}:
  match m b:
    case 0n _:
      Empty.absurd({Nat.is_lt(B.wordix(i), 0n) == True{} : Bool}, N.lt_zero_absurd(i, h))
    case 1n+ +p True{}:
      %Equal.sym(Nat, B.wordix(i), 0n, DP.wordix_small_alias(i, eb)) : {Nat.is_lt(_, 1n+p) == True{} : Bool}
      {==}
    case 1n+ +p False{}:
      %Equal.sym(Nat, B.wordix(i), 1n+B.wordix(Nat.sub(i, 32n)), DP.wordix_step_alias(i, eb)) : {Nat.is_lt(_, 1n+p) == True{} : Bool}
      wordix_go(p, Nat.sub(i, 32n), Nat.is_lt(Nat.sub(i, 32n), 32n), {==},
        N.sub_lt(i, 32n, Nat.mul(p, 32n), N.not_lt_le(i, 32n, eb), h))

def wordix_lt(+i: Nat, +m: Nat, +h: {Nat.is_lt(i, Nat.mul(m, 32n)) == True{} : Bool}) -> {Nat.is_lt(B.wordix(i), m) == True{} : Bool}:
  wordix_go(m, i, Nat.is_lt(i, 32n), {==}, h)

# Releasing a bitset is the unit: `burn_list` consumes any finite list.
def burn_any(xs: List<B.Wd>) -> {B.burn_list(xs) == Unit{} : Unit}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, t}:
      burn_any(t)

def dispose_ok(+n: Nat, +d: Nat, t: A.Tree<B.Wd>) -> {B.dispose(B.BS{n, d, A.thaw(B.Wd, t)}) == Unit{} : Unit}:
  {==}

# ---- the shadow of a live bitset is unique ----
#
# Every law about an operation says "the real operation lands on the array of
# THIS shadow", and then states the model and the invariant of that shadow.
# That is only meaningful if a runtime bitset determines its shadow, i.e. if
# `real` is injective - otherwise a proof could name a different shadow that
# happens to have the same `real` and claim its model. It is.

def blen_go(+n: Nat, u: Unit) -> Nat:
  match u:
    case Unit{}:
      n

def blen(s: B.Bitset) -> Nat:
  match s:
    case B.BS{+n, d, a}:
      blen_go(n, B.burn(a))

def bdepth(s: B.Bitset) -> Nat:
  match s:
    case B.BS{n, +d, a}:
      blen_go(d, B.burn(a))

def btree(s: B.Bitset) -> A.Tree<B.Wd>:
  match s:
    case B.BS{n, d, a}:
      A.freeze(B.Wd, a)

def sh_len(sh: Sh) -> Nat:
  match sh:
    case Sh{n, d, t}:
      n

def sh_depth(sh: Sh) -> Nat:
  match sh:
    case Sh{n, d, t}:
      d

def sh_tree(sh: Sh) -> A.Tree<B.Wd>:
  match sh:
    case Sh{n, d, t}:
      t

def real_len(+sh: Sh) -> {blen(real(sh)) == sh_len(sh) : Nat}:
  match sh:
    case Sh{+n, d, t}:
      {==}

def real_depth(+sh: Sh) -> {bdepth(real(sh)) == sh_depth(sh) : Nat}:
  match sh:
    case Sh{n, +d, t}:
      {==}

def real_tree(+sh: Sh) -> {btree(real(sh)) == sh_tree(sh) : A.Tree<B.Wd>}:
  match sh:
    case Sh{n, d, +t}:
      A.freeze_thaw(B.Wd, t)

def sh_eta(+sh: Sh) -> {sh == Sh{sh_len(sh), sh_depth(sh), sh_tree(sh)} : Sh}:
  match sh:
    case Sh{n, d, t}:
      {==}

def real_inj_parts(+a: Sh, +b: Sh, +e: {real(a) == real(b) : B.Bitset}) -> {Sh{sh_len(a), sh_depth(a), sh_tree(a)} == Sh{sh_len(b), sh_depth(b), sh_tree(b)} : Sh}:
  %real_len(a) : {Sh{_, sh_depth(a), sh_tree(a)} == Sh{sh_len(b), sh_depth(b), sh_tree(b)} : Sh}
  %real_depth(a) : {Sh{blen(real(a)), _, sh_tree(a)} == Sh{sh_len(b), sh_depth(b), sh_tree(b)} : Sh}
  %real_tree(a) : {Sh{blen(real(a)), bdepth(real(a)), _} == Sh{sh_len(b), sh_depth(b), sh_tree(b)} : Sh}
  %real_len(b) : {Sh{blen(real(a)), bdepth(real(a)), btree(real(a))} == Sh{_, sh_depth(b), sh_tree(b)} : Sh}
  %real_depth(b) : {Sh{blen(real(a)), bdepth(real(a)), btree(real(a))} == Sh{blen(real(b)), _, sh_tree(b)} : Sh}
  %real_tree(b) : {Sh{blen(real(a)), bdepth(real(a)), btree(real(a))} == Sh{blen(real(b)), bdepth(real(b)), _} : Sh}
  Equal.cong(B.Bitset, Sh, s => Sh{blen(s), bdepth(s), btree(s)}, real(a), real(b), e)

def real_inj(+a: Sh, +b: Sh, +e: {real(a) == real(b) : B.Bitset}) -> {a == b : Sh}:
  Equal.trans(Sh, a, Sh{sh_len(a), sh_depth(a), sh_tree(a)}, b,
    sh_eta(a),
    Equal.trans(Sh, Sh{sh_len(a), sh_depth(a), sh_tree(a)}, Sh{sh_len(b), sh_depth(b), sh_tree(b)}, b,
      real_inj_parts(a, b, e),
      Equal.sym(Sh, b, Sh{sh_len(b), sh_depth(b), sh_tree(b)}, sh_eta(b))))
