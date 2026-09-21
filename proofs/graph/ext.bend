import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../../spec/common.bend as SC
import ./lists.bend as LS
import ./state.bend as ST
import ./shift.bend as SH
import ./window.bend as W

# Lists are equal when they agree at every index; the index behaviour of
# windows past their end and of index deletion/insertion.

def none_some(-A: Data, +y: A, +h: {None{} == Some{y} : Maybe<&2, A>}) -> Empty:
  L.false_true(Equal.cong(Maybe<&2, A>, Bool, m => Maybe.is_some(&2, A, m), None{}, Some{y}, h))

# ---- windows by construction ----

def drop_cons(+xs: List<&2, U32>, +a: Nat, +ha: {Nat.is_lt(a, SC.length(U32, xs)) == True{} : Bool}) -> {SC.drop(U32, xs, a) == Con{SH.val_at(xs, a), SC.drop(U32, xs, 1n+a)} : List<&2, U32>}:
  match xs a:
    case Nil{} a0:
      Empty.absurd({SC.drop(U32, Nil{}, a0) == Con{SH.val_at(Nil{}, a0), SC.drop(U32, Nil{}, 1n+a0)} : List<&2, U32>}, L.false_true(Equal.trans(Bool, False{}, Nat.is_lt(a0, 0n), True{}, Equal.sym(Bool, Nat.is_lt(a0, 0n), False{}, N.not_lt_zero(a0)), ha)))
    case Con{+w, +t} 0n:
      LL.cons_cong(U32, w, t, SC.drop(U32, t, 0n), Equal.sym(List<&2, U32>, SC.drop(U32, t, 0n), t, W.drop_zero(U32, t)))
    case Con{+w, +t} 1n+p:
      drop_cons(t, p, ha)

def win_cons(+xs: List<&2, U32>, +a: Nat, +m: Nat, +ha: {Nat.is_lt(a, SC.length(U32, xs)) == True{} : Bool}) -> {ST.win(U32, xs, a, 1n+m) == Con{SH.val_at(xs, a), ST.win(U32, xs, 1n+a, m)} : List<&2, U32>}:
  W.win_cons(xs, a, m, SH.val_at(xs, a), SC.drop(U32, xs, 1n+a), drop_cons(xs, a, ha))

# One step of a window equality: equal first values, equal rests.
def win_step(+ys: List<&2, U32>, +xs: List<&2, U32>, +a: Nat, +b: Nat, +m: Nat, +ha: {Nat.is_lt(a, SC.length(U32, ys)) == True{} : Bool}, +hb: {Nat.is_lt(b, SC.length(U32, xs)) == True{} : Bool}, +hv: {SC.nth(U32, ys, a) == SC.nth(U32, xs, b) : Maybe<&2, U32>}, +ht: {ST.win(U32, ys, 1n+a, m) == ST.win(U32, xs, 1n+b, m) : List<&2, U32>}) -> {ST.win(U32, ys, a, 1n+m) == ST.win(U32, xs, b, 1n+m) : List<&2, U32>}:
  +ev = Equal.cong(Maybe<&2, U32>, U32, mm => L.some_value(U32, mm, 0), SC.nth(U32, ys, a), SC.nth(U32, xs, b), hv)
  Equal.trans(List<&2, U32>, ST.win(U32, ys, a, 1n+m), Con{SH.val_at(ys, a), ST.win(U32, ys, 1n+a, m)}, ST.win(U32, xs, b, 1n+m),
    win_cons(ys, a, m, ha),
    Equal.trans(List<&2, U32>, Con{SH.val_at(ys, a), ST.win(U32, ys, 1n+a, m)}, Con{SH.val_at(xs, b), ST.win(U32, xs, 1n+b, m)}, ST.win(U32, xs, b, 1n+m),
      Equal.trans(List<&2, U32>, Con{SH.val_at(ys, a), ST.win(U32, ys, 1n+a, m)}, Con{SH.val_at(xs, b), ST.win(U32, ys, 1n+a, m)}, Con{SH.val_at(xs, b), ST.win(U32, xs, 1n+b, m)},
        Equal.cong(U32, List<&2, U32>, z => Con{z, ST.win(U32, ys, 1n+a, m)}, SH.val_at(ys, a), SH.val_at(xs, b), ev),
        LL.cons_cong(U32, SH.val_at(xs, b), ST.win(U32, ys, 1n+a, m), ST.win(U32, xs, 1n+b, m), ht)),
      Equal.sym(List<&2, U32>, ST.win(U32, xs, b, 1n+m), Con{SH.val_at(xs, b), ST.win(U32, xs, 1n+b, m)}, win_cons(xs, b, m, hb))))

def win_zero(-A: Data, +xs: List<&2, A>, +a: Nat) -> {ST.win(A, xs, a, 0n) == Nil{} : List<&2, A>}:
  LL.sc_take_zero(A, SC.drop(A, xs, a))

def win_zero2(+ys: List<&2, U32>, +xs: List<&2, U32>, +a: Nat, +b: Nat) -> {ST.win(U32, ys, a, 0n) == ST.win(U32, xs, b, 0n) : List<&2, U32>}:
  Equal.trans(List<&2, U32>, ST.win(U32, ys, a, 0n), Nil{}, ST.win(U32, xs, b, 0n), win_zero(U32, ys, a), Equal.sym(List<&2, U32>, ST.win(U32, xs, b, 0n), Nil{}, win_zero(U32, xs, b)))

def drop_drop(-A: Data, +xs: List<&2, A>, +a: Nat, +b: Nat) -> {SC.drop(A, SC.drop(A, xs, a), b) == SC.drop(A, xs, Nat.add(a, b)) : List<&2, A>}:
  match xs a:
    case Nil{} a0:
      Equal.trans(List<&2, A>, SC.drop(A, SC.drop(A, Nil{}, a0), b), Nil{}, SC.drop(A, Nil{}, Nat.add(a0, b)),
        L.subst(List<&2, A>, z => {SC.drop(A, z, b) == Nil{} : List<&2, A>}, Nil{}, SC.drop(A, Nil{}, a0), Equal.sym(List<&2, A>, SC.drop(A, Nil{}, a0), Nil{}, W.nil_drop(A, a0)), W.nil_drop(A, b)),
        Equal.sym(List<&2, A>, SC.drop(A, Nil{}, Nat.add(a0, b)), Nil{}, W.nil_drop(A, Nat.add(a0, b))))
    case Con{+w, +t} 0n:
      {==}
    case Con{+w, +t} 1n+p:
      drop_drop(A, t, p, b)

# A window splits at any point inside it.
def win_split(-A: Data, +xs: List<&2, A>, +a: Nat, +l: Nat, +r: Nat, +h: {Nat.is_le(l, r) == True{} : Bool}) -> {ST.win(A, xs, a, r) == SC.append(A, ST.win(A, xs, a, l), ST.win(A, xs, Nat.add(a, l), Nat.sub(r, l))) : List<&2, A>}:
  Equal.trans(List<&2, A>, ST.win(A, xs, a, r), SC.append(A, ST.win(A, xs, a, l), SC.take(A, SC.drop(A, SC.drop(A, xs, a), l), Nat.sub(r, l))), SC.append(A, ST.win(A, xs, a, l), ST.win(A, xs, Nat.add(a, l), Nat.sub(r, l))),
    LL.sc_take_split(A, SC.drop(A, xs, a), l, r, h),
    Equal.cong(List<&2, A>, List<&2, A>, z => SC.append(A, ST.win(A, xs, a, l), SC.take(A, z, Nat.sub(r, l))), SC.drop(A, SC.drop(A, xs, a), l), SC.drop(A, xs, Nat.add(a, l)), drop_drop(A, xs, a, l)))

# ---- deletion and insertion at the end of a prefix ----

def dl_app(+as: List<&2, U32>, +x: U32, +bs: List<&2, U32>) -> {LS.dl(SC.append(U32, as, Con{x, bs}), SC.length(U32, as)) == SC.append(U32, as, bs) : List<&2, U32>}:
  match as:
    case Nil{}:
      {==}
    case Con{+w, +t}:
      LL.cons_cong(U32, w, LS.dl(SC.append(U32, t, Con{x, bs}), SC.length(U32, t)), SC.append(U32, t, bs), dl_app(t, x, bs))

def il_app(+as: List<&2, U32>, +x: U32, +bs: List<&2, U32>) -> {LS.il(SC.append(U32, as, bs), SC.length(U32, as), x) == SC.append(U32, as, Con{x, bs}) : List<&2, U32>}:
  match as bs:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{b, bt}:
      {==}
    case Con{+w, +t} bs0:
      LL.cons_cong(U32, w, LS.il(SC.append(U32, t, bs0), SC.length(U32, t), x), SC.append(U32, t, Con{x, bs0}), il_app(t, x, bs0))

def nth_take_ge(-A: Data, +ys: List<&2, A>, +k: Nat, +i: Nat, +h: {Nat.is_le(k, i) == True{} : Bool}) -> {SC.nth(A, SC.take(A, ys, k), i) == None{} : Maybe<&2, A>}:
  match ys k i:
    case Nil{} k0 i0:
      {==}
    case Con{y, t} 0n i0:
      {==}
    case Con{y, t} 1n+q 0n:
      Empty.absurd({SC.nth(A, SC.take(A, Con{y, t}, 1n+q), 0n) == None{} : Maybe<&2, A>}, L.false_true(h))
    case Con{+y, +t} 1n+q 1n+j:
      nth_take_ge(A, t, q, j, h)
