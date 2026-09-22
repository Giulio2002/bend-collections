import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../spec/common.bend as SC
import ../spec/hash_table.bend as S
import ../math/u32div.bend as UD
import ../../src/containers/hash_table.bend as H
import ./buckets.bend as B

# Reading the implementation's arrays as a bucket list.
#   tab   (check word, link) pairs: bucket i is (tab[2i], tab[2i+1])
#   ks    the slot arena's stored keys: a long key's String, "" for a
#         one-character key (its word is the key)

def nth0(tb: List<&2, U32>, +i: Nat) -> U32:
  match tb i:
    case Nil{} _:
      0
    case Con{x, t} 0n:
      x
    case Con{x, t} 1n+p:
      nth0(t, p)

def nths(ks: List<&2, String>, +i: Nat) -> String:
  match ks i:
    case Nil{} _:
      SNil{}
    case Con{x, t} 0n:
      x
    case Con{x, t} 1n+p:
      nths(t, p)

# the key of a full bucket with word w and stored string s
def keyof_c(+w: U32, s: String, short: Bool) -> String:
  match short:
    case True{}:
      SCon{Chr{U32.and(w, 2147483647)}, SNil{}}
    case False{}:
      s

def keyof(+w: U32, s: String) -> String:
  keyof_c(w, s, H.is_short(w))

def dec_c(+w: U32, +l: U32, +ks: List<&2, String>, empty: Bool) -> B.Bk:
  match empty:
    case True{}:
      B.BE{}
    case False{}:
      B.BF{w, l, keyof(w, nths(ks, UD.v(H.slot(l))))}

# bucket i of the arrays
def dec(+tb: List<&2, U32>, +ks: List<&2, String>, +i: Nat) -> B.Bk:
  dec_c(nth0(tb, Nat.double(i)), nth0(tb, 1n+Nat.double(i)), ks, U32.is_eq(nth0(tb, Nat.double(i)), 0))

# buckets i .. i + m - 1
def dlist(+tb: List<&2, U32>, +ks: List<&2, String>, +m: Nat, +i: Nat) -> List<&2, B.Bk>:
  match m:
    case 0n:
      Nil{}
    case 1n+p:
      Con{dec(tb, ks, i), dlist(tb, ks, p, 1n+i)}

def at_dlist(+tb: List<&2, U32>, +ks: List<&2, String>, +m: Nat, +i: Nat, +j: Nat, +hj: {Nat.is_lt(j, m) == True{} : Bool}) -> {B.at(dlist(tb, ks, m, i), j) == dec(tb, ks, Nat.add(i, j)) : B.Bk}:
  match m j:
    case 0n _:
      Empty.absurd({B.at(dlist(tb, ks, 0n, i), j) == dec(tb, ks, Nat.add(i, j)) : B.Bk}, N.lt_zero_absurd(j, hj))
    case 1n+p 0n:
      Equal.cong(Nat, B.Bk, z => dec(tb, ks, z), i, Nat.add(i, 0n), Equal.sym(Nat, Nat.add(i, 0n), i, N.add_zero(i)))
    case 1n+p 1n+q:
      Equal.trans(B.Bk, B.at(dlist(tb, ks, p, 1n+i), q), dec(tb, ks, Nat.add(1n+i, q)), dec(tb, ks, Nat.add(i, 1n+q)), at_dlist(tb, ks, p, 1n+i, q, hj), Equal.cong(Nat, B.Bk, z => dec(tb, ks, z), 1n+Nat.add(i, q), Nat.add(i, 1n+q), Equal.sym(Nat, Nat.add(i, 1n+q), 1n+Nat.add(i, q), N.add_succ(i, q))))

# the bucket list of a table of n buckets
def buckets(+tb: List<&2, U32>, +ks: List<&2, String>, +n: Nat) -> List<&2, B.Bk>:
  dlist(tb, ks, n, 0n)

def at_buckets(+tb: List<&2, U32>, +ks: List<&2, String>, +n: Nat, +j: Nat, +hj: {Nat.is_lt(j, n) == True{} : Bool}) -> {B.at(buckets(tb, ks, n), j) == dec(tb, ks, j) : B.Bk}:
  at_dlist(tb, ks, n, 0n, j, hj)

# a list index below the length reads its element
def nth_some(+tb: List<&2, U32>, +i: Nat, +h: {Nat.is_lt(i, SC.length(U32, tb)) == True{} : Bool}) -> {SC.nth(U32, tb, i) == Some{nth0(tb, i)} : Maybe<&2, U32>}:
  match tb i:
    case Nil{} _:
      Empty.absurd({SC.nth(U32, Nil{}, i) == Some{nth0(Nil{}, i)} : Maybe<&2, U32>}, N.lt_zero_absurd(i, h))
    case Con{x, t} 0n:
      {==}
    case Con{x, t} 1n+p:
      nth_some(t, p, h)

def nths_some(+ks: List<&2, String>, +i: Nat, +h: {Nat.is_lt(i, SC.length(String, ks)) == True{} : Bool}) -> {SC.nth(String, ks, i) == Some{nths(ks, i)} : Maybe<&2, String>}:
  match ks i:
    case Nil{} _:
      Empty.absurd({SC.nth(String, Nil{}, i) == Some{nths(Nil{}, i)} : Maybe<&2, String>}, N.lt_zero_absurd(i, h))
    case Con{x, t} 0n:
      {==}
    case Con{x, t} 1n+p:
      nths_some(t, p, h)

def upd_upd(+xs: List<&2, String>, +i: Nat, +a: String, +b: String) -> {SC.update(String, SC.update(String, xs, i, a), i, b) == SC.update(String, xs, i, b) : List<&2, String>}:
  match xs i:
    case Nil{} _:
      {==}
    case Con{h, t} 0n:
      {==}
    case Con{h, t} 1n+p:
      Equal.cong(List<&2, String>, List<&2, String>, r => Con{h, r}, SC.update(String, SC.update(String, t, p, a), p, b), SC.update(String, t, p, b), upd_upd(t, p, a, b))

def upd_self(+xs: List<&2, String>, +i: Nat) -> {SC.update(String, xs, i, nths(xs, i)) == xs : List<&2, String>}:
  match xs i:
    case Nil{} _:
      {==}
    case Con{h, t} 0n:
      {==}
    case Con{h, t} 1n+p:
      Equal.cong(List<&2, String>, List<&2, String>, r => Con{h, r}, SC.update(String, t, p, nths(t, p)), t, upd_self(t, p))
