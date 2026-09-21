import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../../spec/common.bend as SC
import ./state.bend as ST
import ./shift.bend as SH
import ./search.bend as SE
import ./lists.bend as LS
import ./ext.bend as X
import ./nbrs.bend as NB

# Order bridges: an ascending window is the index-level `asc_at`, and
# deleting an element keeps a list ascending.

def above_at_of_win(+m: Nat, +xs: List<&2, U32>, +i: Nat, +from: Nat, +x: U32, +hx: {SC.nth(U32, xs, i) == Some{x} : Maybe<&2, U32>}, +hlen: {Nat.is_le(Nat.add(from, m), SC.length(U32, xs)) == True{} : Bool}, +h: {ST.above(x, ST.win(U32, xs, from, m)) == True{} : Bool}) -> {SE.above_at(m, xs, i, from) == True{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+r:
      +hle = L.subst(Nat, z => {Nat.is_le(z, SC.length(U32, xs)) == True{} : Bool}, Nat.add(from, 1n+r), 1n+Nat.add(from, r), N.add_succ(from, r), hlen)
      +hf = N.lt_le_trans(from, 1n+from, SC.length(U32, xs), N.lt_succ(from), N.le_trans(1n+from, 1n+Nat.add(from, r), SC.length(U32, xs), N.le_add_right(1n+from, r), hle))
      +y = SH.val_at(xs, from)
      +h2 = L.subst(List<&2, U32>, z => {ST.above(x, z) == True{} : Bool}, ST.win(U32, xs, from, 1n+r), Con{y, ST.win(U32, xs, 1n+from, r)}, X.win_cons(xs, from, r, hf), h)
      +hy = NB.val_some(xs, from, hf)
      L.and_intro(SE.ltat2(xs, i, from), SE.above_at(r, xs, i, 1n+from),
        L.subst(Maybe<&2, U32>, z => {SE.ltm2(z, SC.nth(U32, xs, from)) == True{} : Bool}, Some{x}, SC.nth(U32, xs, i), Equal.sym(Maybe<&2, U32>, SC.nth(U32, xs, i), Some{x}, hx),
          L.subst(Maybe<&2, U32>, z => {SE.ltm2(Some{x}, z) == True{} : Bool}, Some{y}, SC.nth(U32, xs, from), Equal.sym(Maybe<&2, U32>, SC.nth(U32, xs, from), Some{y}, hy),
            L.and_left(Cmp.is_lt(U32.cmp(x, y)), ST.above(x, ST.win(U32, xs, 1n+from, r)), h2))),
        above_at_of_win(r, xs, i, 1n+from, x, hx, hle, L.and_right(Cmp.is_lt(U32.cmp(x, y)), ST.above(x, ST.win(U32, xs, 1n+from, r)), h2)))

def asc_at_of_win(+k: Nat, +xs: List<&2, U32>, +from: Nat, +hlen: {Nat.is_le(Nat.add(from, k), SC.length(U32, xs)) == True{} : Bool}, +h: {ST.asc(ST.win(U32, xs, from, k)) == True{} : Bool}) -> {SE.asc_at(k, xs, from) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+m:
      +hle = L.subst(Nat, z => {Nat.is_le(z, SC.length(U32, xs)) == True{} : Bool}, Nat.add(from, 1n+m), 1n+Nat.add(from, m), N.add_succ(from, m), hlen)
      +hf = N.lt_le_trans(from, 1n+from, SC.length(U32, xs), N.lt_succ(from), N.le_trans(1n+from, 1n+Nat.add(from, m), SC.length(U32, xs), N.le_add_right(1n+from, m), hle))
      +x = SH.val_at(xs, from)
      +w = ST.win(U32, xs, 1n+from, m)
      +h2 = L.subst(List<&2, U32>, z => {ST.asc(z) == True{} : Bool}, ST.win(U32, xs, from, 1n+m), Con{x, w}, X.win_cons(xs, from, m, hf), h)
      L.and_intro(SE.above_at(m, xs, from, 1n+from), SE.asc_at(m, xs, 1n+from),
        above_at_of_win(m, xs, from, 1n+from, x, NB.val_some(xs, from, hf), hle, L.and_left(ST.above(x, w), ST.asc(w), h2)),
        asc_at_of_win(m, xs, 1n+from, hle, L.and_right(ST.above(x, w), ST.asc(w), h2)))

def above_dl(+x: U32, +ws: List<&2, U32>, +l: Nat, +h: {ST.above(x, ws) == True{} : Bool}) -> {ST.above(x, LS.dl(ws, l)) == True{} : Bool}:
  match ws l:
    case Nil{} l0:
      {==}
    case Con{+w, +t} 0n:
      L.and_right(Cmp.is_lt(U32.cmp(x, w)), ST.above(x, t), h)
    case Con{+w, +t} 1n+p:
      L.and_intro(Cmp.is_lt(U32.cmp(x, w)), ST.above(x, LS.dl(t, p)), L.and_left(Cmp.is_lt(U32.cmp(x, w)), ST.above(x, t), h), above_dl(x, t, p, L.and_right(Cmp.is_lt(U32.cmp(x, w)), ST.above(x, t), h)))

def asc_dl(+ws: List<&2, U32>, +l: Nat, +h: {ST.asc(ws) == True{} : Bool}) -> {ST.asc(LS.dl(ws, l)) == True{} : Bool}:
  match ws l:
    case Nil{} l0:
      {==}
    case Con{+w, +t} 0n:
      L.and_right(ST.above(w, t), ST.asc(t), h)
    case Con{+w, +t} 1n+p:
      L.and_intro(ST.above(w, LS.dl(t, p)), ST.asc(LS.dl(t, p)), above_dl(w, t, p, L.and_left(ST.above(w, t), ST.asc(t), h)), asc_dl(t, p, L.and_right(ST.above(w, t), ST.asc(t), h)))
