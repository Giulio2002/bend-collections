import Base
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../../lib/list.bend as LL
import ../../../spec/lib/common.bend as SC
import ../../../spec/containers/bitset.bend as S
import ../../../src/containers/bitset.bend as B

# Boolean-sequence facts used by the bitset proof: element-wise combination
# (zipk, indexed by the implementation's word-operation tag), all-False
# tails, counting and member enumeration over take/drop/append.

def bop(k: B.WordOp, a: Bool, b: Bool) -> Bool:
  match k:
    case B.KOr{}:
      Bool.or(a, b)
    case B.KAnd{}:
      Bool.and(a, b)
    case B.KDiff{}:
      Bool.and(a, Bool.not(b))
    case B.KXor{}:
      Bool.xor(a, b)

def zipk(+k: B.WordOp, xs: List<&2, Bool>, ys: List<&2, Bool>) -> List<&2, Bool>:
  match xs ys:
    case Nil{} _:
      Nil{}
    case Con{a, s} Nil{}:
      Nil{}
    case Con{a, s} Con{b, t}:
      Con{bop(k, a, b), zipk(k, s, t)}

def allf(xs: List<&2, Bool>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{False{}, t}:
      allf(t)
    case Con{True{}, t}:
      False{}

def rep(n: Nat) -> List<&2, Bool>:
  SC.replicate(Bool, n, False{})

# ---- spec combinators are zipk instances ----

def spec_or(+xs: List<&2, Bool>, +ys: List<&2, Bool>) -> {S.zip_or(xs, ys) == zipk(B.KOr{}, xs, ys) : List<&2, Bool>}:
  match xs ys:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{b, t}:
      {==}
    case Con{a, s} Nil{}:
      {==}
    case Con{a, s} Con{b, t}:
      LL.cons_cong(Bool, Bool.or(a, b), S.zip_or(s, t), zipk(B.KOr{}, s, t), spec_or(s, t))

def spec_and(+xs: List<&2, Bool>, +ys: List<&2, Bool>) -> {S.zip_and(xs, ys) == zipk(B.KAnd{}, xs, ys) : List<&2, Bool>}:
  match xs ys:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{b, t}:
      {==}
    case Con{a, s} Nil{}:
      {==}
    case Con{a, s} Con{b, t}:
      LL.cons_cong(Bool, Bool.and(a, b), S.zip_and(s, t), zipk(B.KAnd{}, s, t), spec_and(s, t))

def spec_diff(+xs: List<&2, Bool>, +ys: List<&2, Bool>) -> {S.zip_diff(xs, ys) == zipk(B.KDiff{}, xs, ys) : List<&2, Bool>}:
  match xs ys:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{b, t}:
      {==}
    case Con{a, s} Nil{}:
      {==}
    case Con{a, s} Con{b, t}:
      LL.cons_cong(Bool, Bool.and(a, Bool.not(b)), S.zip_diff(s, t), zipk(B.KDiff{}, s, t), spec_diff(s, t))

def spec_xor(+xs: List<&2, Bool>, +ys: List<&2, Bool>) -> {S.zip_xor(xs, ys) == zipk(B.KXor{}, xs, ys) : List<&2, Bool>}:
  match xs ys:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{b, t}:
      {==}
    case Con{a, s} Nil{}:
      {==}
    case Con{a, s} Con{b, t}:
      LL.cons_cong(Bool, Bool.xor(a, b), S.zip_xor(s, t), zipk(B.KXor{}, s, t), spec_xor(s, t))

# ---- zipk structure ----

def zipk_nil_r(+k: B.WordOp, +xs: List<&2, Bool>) -> {zipk(k, xs, Nil{}) == Nil{} : List<&2, Bool>}:
  match xs:
    case Nil{}:
      {==}
    case Con{a, s}:
      {==}

def zipk_append(+k: B.WordOp, +xs: List<&2, Bool>, +ys: List<&2, Bool>, +xs2: List<&2, Bool>, +ys2: List<&2, Bool>, +h: {SC.length(Bool, xs) == SC.length(Bool, ys) : Nat}) -> {zipk(k, SC.append(Bool, xs, xs2), SC.append(Bool, ys, ys2)) == SC.append(Bool, zipk(k, xs, ys), zipk(k, xs2, ys2)) : List<&2, Bool>}:
  match xs ys:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{b, t}:
      Empty.absurd({zipk(k, xs2, SC.append(Bool, Con{b, t}, ys2)) == zipk(k, xs2, ys2) : List<&2, Bool>}, N.zero_succ(SC.length(Bool, t), h))
    case Con{a, s} Nil{}:
      Empty.absurd({zipk(k, SC.append(Bool, Con{a, s}, xs2), ys2) == SC.append(Bool, zipk(k, Con{a, s}, Nil{}), zipk(k, xs2, ys2)) : List<&2, Bool>}, N.succ_zero(SC.length(Bool, s), h))
    case Con{a, s} Con{b, t}:
      LL.cons_cong(Bool, bop(k, a, b), zipk(k, SC.append(Bool, s, xs2), SC.append(Bool, t, ys2)), SC.append(Bool, zipk(k, s, t), zipk(k, xs2, ys2)), zipk_append(k, s, t, xs2, ys2, N.succ_inj(SC.length(Bool, s), SC.length(Bool, t), h)))

def take_zipk(+k: B.WordOp, +xs: List<&2, Bool>, +ys: List<&2, Bool>, +n: Nat) -> {SC.take(Bool, zipk(k, xs, ys), n) == zipk(k, SC.take(Bool, xs, n), SC.take(Bool, ys, n)) : List<&2, Bool>}:
  match xs ys n:
    case Nil{} _ _:
      {==}
    case Con{a, s} Nil{} _:
      Equal.sym(List<&2, Bool>, zipk(k, SC.take(Bool, Con{a, s}, n), Nil{}), Nil{}, zipk_nil_r(k, SC.take(Bool, Con{a, s}, n)))
    case Con{a, s} Con{b, t} 0n:
      {==}
    case Con{a, s} Con{b, t} 1n+m:
      LL.cons_cong(Bool, bop(k, a, b), SC.take(Bool, zipk(k, s, t), m), zipk(k, SC.take(Bool, s, m), SC.take(Bool, t, m)), take_zipk(k, s, t, m))

def drop_zipk(+k: B.WordOp, +xs: List<&2, Bool>, +ys: List<&2, Bool>, +n: Nat) -> {SC.drop(Bool, zipk(k, xs, ys), n) == zipk(k, SC.drop(Bool, xs, n), SC.drop(Bool, ys, n)) : List<&2, Bool>}:
  match xs ys n:
    case Nil{} _ _:
      {==}
    case Con{a, s} Nil{} _:
      Equal.sym(List<&2, Bool>, zipk(k, SC.drop(Bool, Con{a, s}, n), Nil{}), Nil{}, zipk_nil_r(k, SC.drop(Bool, Con{a, s}, n)))
    case Con{a, s} Con{b, t} 0n:
      {==}
    case Con{a, s} Con{b, t} 1n+m:
      drop_zipk(k, s, t, m)

def bop_ff(+k: B.WordOp) -> {bop(k, False{}, False{}) == False{} : Bool}:
  match k:
    case B.KOr{}:
      {==}
    case B.KAnd{}:
      {==}
    case B.KDiff{}:
      {==}
    case B.KXor{}:
      {==}

def allf_zipk(+k: B.WordOp, +xs: List<&2, Bool>, +ys: List<&2, Bool>, +hx: {allf(xs) == True{} : Bool}, +hy: {allf(ys) == True{} : Bool}) -> {allf(zipk(k, xs, ys)) == True{} : Bool}:
  match xs ys:
    case Nil{} _:
      {==}
    case Con{a, s} Nil{}:
      {==}
    case Con{True{}, s} Con{b, t}:
      Empty.absurd({allf(zipk(k, Con{True{}, s}, Con{b, t})) == True{} : Bool}, L.false_true(hx))
    case Con{False{}, s} Con{True{}, t}:
      Empty.absurd({allf(zipk(k, Con{False{}, s}, Con{True{}, t})) == True{} : Bool}, L.false_true(hy))
    case Con{False{}, s} Con{False{}, t}:
      %Equal.sym(Bool, bop(k, False{}, False{}), False{}, bop_ff(k)) : {allf(Con{_, zipk(k, s, t)}) == True{} : Bool}
      allf_zipk(k, s, t, hx, hy)

def length_zipk_le(+k: B.WordOp, +xs: List<&2, Bool>, +ys: List<&2, Bool>) -> {Nat.is_le(SC.length(Bool, zipk(k, xs, ys)), SC.length(Bool, xs)) == True{} : Bool}:
  match xs ys:
    case Nil{} _:
      {==}
    case Con{a, s} Nil{}:
      {==}
    case Con{a, s} Con{b, t}:
      length_zipk_le(k, s, t)

def le_length_zipk(+k: B.WordOp, +n: Nat, +xs: List<&2, Bool>, +ys: List<&2, Bool>, +hx: {Nat.is_le(n, SC.length(Bool, xs)) == True{} : Bool}, +hy: {Nat.is_le(n, SC.length(Bool, ys)) == True{} : Bool}) -> {Nat.is_le(n, SC.length(Bool, zipk(k, xs, ys))) == True{} : Bool}:
  match n xs ys:
    case 0n _ _:
      N.zero_le(SC.length(Bool, zipk(k, xs, ys)))
    case 1n+m Nil{} _:
      Empty.absurd({Nat.is_le(1n+m, SC.length(Bool, zipk(k, Nil{}, ys))) == True{} : Bool}, L.false_true(hx))
    case 1n+m Con{a, s} Nil{}:
      Empty.absurd({Nat.is_le(1n+m, SC.length(Bool, zipk(k, Con{a, s}, Nil{}))) == True{} : Bool}, L.false_true(hy))
    case 1n+m Con{a, s} Con{b, t}:
      le_length_zipk(k, m, s, t, hx, hy)

# ---- all-False sequences ----

def allf_append(+xs: List<&2, Bool>, +ys: List<&2, Bool>, +hx: {allf(xs) == True{} : Bool}, +hy: {allf(ys) == True{} : Bool}) -> {allf(SC.append(Bool, xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      hy
    case Con{False{}, t}:
      allf_append(t, ys, hx, hy)
    case Con{True{}, t}:
      Empty.absurd({allf(SC.append(Bool, Con{True{}, t}, ys)) == True{} : Bool}, L.false_true(hx))

def allf_rep(+n: Nat) -> {allf(rep(n)) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      allf_rep(m)

def drop_allf(+xs: List<&2, Bool>, +n: Nat, +h: {allf(xs) == True{} : Bool}) -> {allf(SC.drop(Bool, xs, n)) == True{} : Bool}:
  match xs n:
    case Nil{} _:
      {==}
    case Con{a, t} 0n:
      h
    case Con{False{}, t} 1n+m:
      drop_allf(t, m, h)
    case Con{True{}, t} 1n+m:
      Empty.absurd({allf(SC.drop(Bool, Con{True{}, t}, 1n+m)) == True{} : Bool}, L.false_true(h))

def take_allf(+xs: List<&2, Bool>, +n: Nat, +h: {allf(xs) == True{} : Bool}, +hn: {Nat.is_le(n, SC.length(Bool, xs)) == True{} : Bool}) -> {SC.take(Bool, xs, n) == rep(n) : List<&2, Bool>}:
  match xs n:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+m:
      Empty.absurd({SC.take(Bool, Nil{}, 1n+m) == rep(1n+m) : List<&2, Bool>}, L.false_true(hn))
    case Con{a, t} 0n:
      {==}
    case Con{False{}, t} 1n+m:
      LL.cons_cong(Bool, False{}, SC.take(Bool, t, m), rep(m), take_allf(t, m, h, hn))
    case Con{True{}, t} 1n+m:
      Empty.absurd({SC.take(Bool, Con{True{}, t}, 1n+m) == rep(1n+m) : List<&2, Bool>}, L.false_true(h))

def count_allf(+xs: List<&2, Bool>, +h: {allf(xs) == True{} : Bool}) -> {S.count(xs) == 0n : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{False{}, t}:
      count_allf(t, h)
    case Con{True{}, t}:
      Empty.absurd({S.count(Con{True{}, t}) == 0n : Nat}, L.false_true(h))

def members_allf(+xs: List<&2, Bool>, +off: Nat, +h: {allf(xs) == True{} : Bool}) -> {S.members(xs, off) == Nil{} : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case Con{False{}, t}:
      members_allf(t, 1n+off, h)
    case Con{True{}, t}:
      Empty.absurd({S.members(Con{True{}, t}, off) == Nil{} : List<&2, Nat>}, L.false_true(h))

# ---- count / members over append, take ----

def count_append(+xs: List<&2, Bool>, +ys: List<&2, Bool>) -> {S.count(SC.append(Bool, xs, ys)) == Nat.add(S.count(xs), S.count(ys)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{False{}, t}:
      count_append(t, ys)
    case Con{True{}, t}:
      N.succ_cong(S.count(SC.append(Bool, t, ys)), Nat.add(S.count(t), S.count(ys)), count_append(t, ys))

def members_append(+xs: List<&2, Bool>, +ys: List<&2, Bool>, +off: Nat) -> {S.members(SC.append(Bool, xs, ys), off) == SC.append(Nat, S.members(xs, off), S.members(ys, Nat.add(SC.length(Bool, xs), off))) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case Con{False{}, t}:
      %N.add_succ(SC.length(Bool, t), off) : {S.members(SC.append(Bool, t, ys), 1n+off) == SC.append(Nat, S.members(t, 1n+off), S.members(ys, _)) : List<&2, Nat>}
      members_append(t, ys, 1n+off)
    case Con{True{}, t}:
      %N.add_succ(SC.length(Bool, t), off) : {Con{off, S.members(SC.append(Bool, t, ys), 1n+off)} == Con{off, SC.append(Nat, S.members(t, 1n+off), S.members(ys, _))} : List<&2, Nat>}
      LL.cons_cong(Nat, off, S.members(SC.append(Bool, t, ys), 1n+off), SC.append(Nat, S.members(t, 1n+off), S.members(ys, Nat.add(SC.length(Bool, t), 1n+off))), members_append(t, ys, 1n+off))

def count_take_snoc(+xs: List<&2, Bool>, +m: Nat) -> {S.count(SC.take(Bool, SC.snoc(Bool, xs, False{}), m)) == S.count(SC.take(Bool, xs, m)) : Nat}:
  match xs m:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+p:
      {==}
    case Con{a, t} 0n:
      {==}
    case Con{False{}, t} 1n+p:
      count_take_snoc(t, p)
    case Con{True{}, t} 1n+p:
      N.succ_cong(S.count(SC.take(Bool, SC.snoc(Bool, t, False{}), p)), S.count(SC.take(Bool, t, p)), count_take_snoc(t, p))

def members_take_snoc(+xs: List<&2, Bool>, +m: Nat, +off: Nat) -> {S.members(SC.take(Bool, SC.snoc(Bool, xs, False{}), m), off) == S.members(SC.take(Bool, xs, m), off) : List<&2, Nat>}:
  match xs m:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+p:
      {==}
    case Con{a, t} 0n:
      {==}
    case Con{False{}, t} 1n+p:
      members_take_snoc(t, p, 1n+off)
    case Con{True{}, t} 1n+p:
      LL.cons_cong(Nat, off, S.members(SC.take(Bool, SC.snoc(Bool, t, False{}), p), 1n+off), S.members(SC.take(Bool, t, p), 1n+off), members_take_snoc(t, p, 1n+off))

# ---- take / drop / update ----

def take_all(+xs: List<&2, Bool>) -> {SC.take(Bool, xs, SC.length(Bool, xs)) == xs : List<&2, Bool>}:
  match xs:
    case Nil{}:
      {==}
    case Con{a, t}:
      LL.cons_cong(Bool, a, SC.take(Bool, t, SC.length(Bool, t)), t, take_all(t))

def take_drop(+xs: List<&2, Bool>, +n: Nat) -> {SC.append(Bool, SC.take(Bool, xs, n), SC.drop(Bool, xs, n)) == xs : List<&2, Bool>}:
  match xs n:
    case Nil{} _:
      {==}
    case Con{a, t} 0n:
      {==}
    case Con{a, t} 1n+m:
      LL.cons_cong(Bool, a, SC.append(Bool, SC.take(Bool, t, m), SC.drop(Bool, t, m)), t, take_drop(t, m))

def length_take(+xs: List<&2, Bool>, +n: Nat, +h: {Nat.is_le(n, SC.length(Bool, xs)) == True{} : Bool}) -> {SC.length(Bool, SC.take(Bool, xs, n)) == n : Nat}:
  match xs n:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+m:
      Empty.absurd({SC.length(Bool, SC.take(Bool, Nil{}, 1n+m)) == 1n+m : Nat}, L.false_true(h))
    case Con{a, t} 0n:
      {==}
    case Con{a, t} 1n+m:
      N.succ_cong(SC.length(Bool, SC.take(Bool, t, m)), m, length_take(t, m, h))

def nth_take(+xs: List<&2, Bool>, +n: Nat, +i: Nat, +h: {Nat.is_lt(i, n) == True{} : Bool}) -> {SC.nth(Bool, SC.take(Bool, xs, n), i) == SC.nth(Bool, xs, i) : Maybe<&2, Bool>}:
  match xs n i:
    case Nil{} _ _:
      {==}
    case Con{a, t} 0n _:
      Empty.absurd({SC.nth(Bool, SC.take(Bool, Con{a, t}, 0n), i) == SC.nth(Bool, Con{a, t}, i) : Maybe<&2, Bool>}, N.lt_zero_absurd(i, h))
    case Con{a, t} 1n+m 0n:
      {==}
    case Con{a, t} 1n+m 1n+j:
      nth_take(t, m, j, h)

def take_update(+xs: List<&2, Bool>, +i: Nat, +v: Bool, +n: Nat) -> {SC.take(Bool, SC.update(Bool, xs, i, v), n) == SC.update(Bool, SC.take(Bool, xs, n), i, v) : List<&2, Bool>}:
  match xs i n:
    case Nil{} _ _:
      {==}
    case Con{a, t} 0n 0n:
      {==}
    case Con{a, t} 1n+j 0n:
      {==}
    case Con{a, t} 0n 1n+m:
      {==}
    case Con{a, t} 1n+j 1n+m:
      LL.cons_cong(Bool, a, SC.take(Bool, SC.update(Bool, t, j, v), m), SC.update(Bool, SC.take(Bool, t, m), j, v), take_update(t, j, v, m))

def drop_update(+xs: List<&2, Bool>, +i: Nat, +v: Bool, +n: Nat, +h: {Nat.is_lt(i, n) == True{} : Bool}) -> {SC.drop(Bool, SC.update(Bool, xs, i, v), n) == SC.drop(Bool, xs, n) : List<&2, Bool>}:
  match xs i n:
    case Nil{} _ _:
      {==}
    case Con{a, t} _ 0n:
      Empty.absurd({SC.drop(Bool, SC.update(Bool, Con{a, t}, i, v), 0n) == SC.drop(Bool, Con{a, t}, 0n) : List<&2, Bool>}, N.lt_zero_absurd(i, h))
    case Con{a, t} 0n 1n+m:
      {==}
    case Con{a, t} 1n+j 1n+m:
      drop_update(t, j, v, m, h)

# ---- single-bit masks ----

def take_rep_succ(+m: Nat) -> {SC.take(Bool, rep(1n+m), m) == rep(m) : List<&2, Bool>}:
  match m:
    case 0n:
      {==}
    case 1n+q:
      LL.cons_cong(Bool, False{}, SC.take(Bool, rep(1n+q), q), rep(q), take_rep_succ(q))

# Shifting a one-hot mask up by one position.
def take_onehot(+m: Nat, +p: Nat, +h: {Nat.is_lt(p, m) == True{} : Bool}) -> {SC.take(Bool, SC.update(Bool, rep(1n+m), p, True{}), m) == SC.update(Bool, rep(m), p, True{}) : List<&2, Bool>}:
  match m p:
    case 0n _:
      Empty.absurd({SC.take(Bool, SC.update(Bool, rep(1n), p, True{}), 0n) == SC.update(Bool, rep(0n), p, True{}) : List<&2, Bool>}, N.lt_zero_absurd(p, h))
    case 1n+q 0n:
      LL.cons_cong(Bool, True{}, SC.take(Bool, rep(1n+q), q), rep(q), take_rep_succ(q))
    case 1n+q 1n+j:
      LL.cons_cong(Bool, False{}, SC.take(Bool, SC.update(Bool, rep(1n+q), j, True{}), q), SC.update(Bool, rep(q), j, True{}), take_onehot(q, j, h))

def or_rep(+xs: List<&2, Bool>) -> {zipk(B.KOr{}, xs, rep(SC.length(Bool, xs))) == xs : List<&2, Bool>}:
  match xs:
    case Nil{}:
      {==}
    case Con{True{}, t}:
      LL.cons_cong(Bool, True{}, zipk(B.KOr{}, t, rep(SC.length(Bool, t))), t, or_rep(t))
    case Con{False{}, t}:
      LL.cons_cong(Bool, False{}, zipk(B.KOr{}, t, rep(SC.length(Bool, t))), t, or_rep(t))

def diff_rep(+xs: List<&2, Bool>) -> {zipk(B.KDiff{}, xs, rep(SC.length(Bool, xs))) == xs : List<&2, Bool>}:
  match xs:
    case Nil{}:
      {==}
    case Con{True{}, t}:
      LL.cons_cong(Bool, True{}, zipk(B.KDiff{}, t, rep(SC.length(Bool, t))), t, diff_rep(t))
    case Con{False{}, t}:
      LL.cons_cong(Bool, False{}, zipk(B.KDiff{}, t, rep(SC.length(Bool, t))), t, diff_rep(t))

# OR with the one-hot mask for k sets bit k.
def or_onehot(+xs: List<&2, Bool>, +k: Nat) -> {zipk(B.KOr{}, xs, SC.update(Bool, rep(SC.length(Bool, xs)), k, True{})) == SC.update(Bool, xs, k, True{}) : List<&2, Bool>}:
  match xs k:
    case Nil{} _:
      {==}
    case Con{True{}, t} 0n:
      LL.cons_cong(Bool, True{}, zipk(B.KOr{}, t, rep(SC.length(Bool, t))), t, or_rep(t))
    case Con{False{}, t} 0n:
      LL.cons_cong(Bool, True{}, zipk(B.KOr{}, t, rep(SC.length(Bool, t))), t, or_rep(t))
    case Con{True{}, t} 1n+j:
      LL.cons_cong(Bool, True{}, zipk(B.KOr{}, t, SC.update(Bool, rep(SC.length(Bool, t)), j, True{})), SC.update(Bool, t, j, True{}), or_onehot(t, j))
    case Con{False{}, t} 1n+j:
      LL.cons_cong(Bool, False{}, zipk(B.KOr{}, t, SC.update(Bool, rep(SC.length(Bool, t)), j, True{})), SC.update(Bool, t, j, True{}), or_onehot(t, j))

# AND NOT with the one-hot mask for k clears bit k.
def diff_onehot(+xs: List<&2, Bool>, +k: Nat) -> {zipk(B.KDiff{}, xs, SC.update(Bool, rep(SC.length(Bool, xs)), k, True{})) == SC.update(Bool, xs, k, False{}) : List<&2, Bool>}:
  match xs k:
    case Nil{} _:
      {==}
    case Con{True{}, t} 0n:
      LL.cons_cong(Bool, False{}, zipk(B.KDiff{}, t, rep(SC.length(Bool, t))), t, diff_rep(t))
    case Con{False{}, t} 0n:
      LL.cons_cong(Bool, False{}, zipk(B.KDiff{}, t, rep(SC.length(Bool, t))), t, diff_rep(t))
    case Con{True{}, t} 1n+j:
      LL.cons_cong(Bool, True{}, zipk(B.KDiff{}, t, SC.update(Bool, rep(SC.length(Bool, t)), j, True{})), SC.update(Bool, t, j, False{}), diff_onehot(t, j))
    case Con{False{}, t} 1n+j:
      LL.cons_cong(Bool, False{}, zipk(B.KDiff{}, t, SC.update(Bool, rep(SC.length(Bool, t)), j, True{})), SC.update(Bool, t, j, False{}), diff_onehot(t, j))
