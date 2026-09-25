import Base
import ./logic.bend as L
import ./nat.bend as N
import ./list.bend as LL
import ../../spec/lib/common.bend as SC
import ../../spec/lib/sequence.bend as Q

# Lemmas on the SPARK formal-vector model predicates (spec/lib/sequence.bend).
# Lean 4's List lemmas (List.getElem_append_left, getElem_set_ne,
# getElem_dropLast, getElem_reverse) are the shape of the lemmas below.

# ---- arithmetic ----

def succ_sub_one(+n: Nat) -> {Nat.sub(1n+n, 1n) == n : Nat}:
  %Equal.sym(Nat, Nat.sub(1n+n, 0n+1n), Nat.sub(n, 0n), {==}) : {_ == n : Nat}
  N.sub_zero(n)

def add_one(+i: Nat) -> {Nat.add(i, 1n) == 1n+i : Nat}:
  Equal.trans(Nat, Nat.add(i, 1n), 1n+Nat.add(i, 0n), 1n+i, N.add_succ(i, 0n), N.succ_cong(Nat.add(i, 0n), i, N.add_zero(i)))

# ---- Append (snoc): Length + 1, Equal_Prefix (old, new), the new element last ----

def re_snoc(-A: Data, +xs: List<&2, A>, +x: A, +i: Nat, +h: {Nat.is_lt(i, SC.length(A, xs)) == True{} : Bool}) -> {SC.nth(A, xs, i) == SC.nth(A, SC.snoc(A, xs, x), i) : Maybe<&2, A>}:
  match xs i:
    case Nil{} _:
      Empty.absurd({SC.nth(A, Nil{}, i) == SC.nth(A, SC.snoc(A, Nil{}, x), i) : Maybe<&2, A>}, N.lt_zero_absurd(i, h))
    case Con{a, t} 0n:
      {==}
    case Con{a, +t} 1n+p:
      re_snoc(A, t, x, p, h)

def snoc_prefix(-A: Data, +xs: List<&2, A>, +x: A) -> Q.EqualPrefix(A, xs, SC.snoc(A, xs, x)):
  %Equal.sym(Nat, SC.length(A, SC.snoc(A, xs, x)), 1n+SC.length(A, xs), LL.length_snoc(A, xs, x)) : {Nat.is_le(SC.length(A, xs), _) == True{} : Bool} & Q.RangeEqual(A, xs, SC.snoc(A, xs, x), 0n, SC.length(A, xs))
  (N.le_succ(SC.length(A, xs)), i => h1 => h2 => re_snoc(A, xs, x, i, h2))

def snoc_last(-A: Data, +xs: List<&2, A>, +x: A) -> {SC.nth(A, SC.snoc(A, xs, x), SC.length(A, xs)) == Some{x} : Maybe<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+a, +t}:
      snoc_last(A, t, x)

def snoc_length(-A: Data, +xs: List<&2, A>, +x: A) -> {SC.length(A, SC.snoc(A, xs, x)) == 1n+SC.length(A, xs) : Nat}:
  LL.length_snoc(A, xs, x)

# Last_Element after Append is the new item
def snoc_last_elem(-A: Data, +xs: List<&2, A>, +x: A) -> {Q.last_elem(A, SC.snoc(A, xs, x)) == Some{x} : Maybe<&2, A>}:
  %Equal.sym(Nat, SC.length(A, SC.snoc(A, xs, x)), 1n+SC.length(A, xs), LL.length_snoc(A, xs, x)) : {SC.nth(A, SC.snoc(A, xs, x), Nat.sub(_, 1n)) == Some{x} : Maybe<&2, A>}
  %Equal.sym(Nat, Nat.sub(1n+SC.length(A, xs), 1n), SC.length(A, xs), succ_sub_one(SC.length(A, xs))) : {SC.nth(A, SC.snoc(A, xs, x), _) == Some{x} : Maybe<&2, A>}
  snoc_last(A, xs, x)

# ---- Prepend (cons): Length + 1, the new element first, Range_Shifted (old, new, 0, Last, 1) ----

def cons_shift_at(-A: Data, +xs: List<&2, A>, +x: A, +i: Nat) -> {SC.nth(A, xs, i) == SC.nth(A, Con{x, xs}, Nat.add(i, 1n)) : Maybe<&2, A>}:
  %Equal.sym(Nat, Nat.add(i, 1n), 1n+i, add_one(i)) : {SC.nth(A, xs, i) == SC.nth(A, Con{x, xs}, _) : Maybe<&2, A>}
  {==}

def cons_shifted(-A: Data, +xs: List<&2, A>, +x: A) -> Q.RangeShifted(A, xs, Con{x, xs}, 0n, SC.length(A, xs), 1n):
  i => h1 => h2 => cons_shift_at(A, xs, x, i)

def cons_first(-A: Data, +xs: List<&2, A>, +x: A) -> {SC.nth(A, Con{x, xs}, 0n) == Some{x} : Maybe<&2, A>}:
  {==}

def cons_length(-A: Data, +xs: List<&2, A>, +x: A) -> {SC.length(A, Con{x, xs}) == 1n+SC.length(A, xs) : Nat}:
  {==}

# ---- Delete_First (tail): Length - 1, Range_Shifted (new, old, 0, Last (new), 1) ----
# with new = t and old = Con{h, t} this is the Prepend shift read backwards

def tail_shifted(-A: Data, +h: A, +t: List<&2, A>) -> Q.RangeShifted(A, t, Con{h, t}, 0n, SC.length(A, t), 1n):
  cons_shifted(A, t, h)

# First_Element is Element (Model, First_Index)
def first_elem(-A: Data, +xs: List<&2, A>) -> {SC.head(A, xs) == SC.nth(A, xs, 0n) : Maybe<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      {==}

# ---- Delete_Last (init): Length - 1, Equal_Prefix (new, old); the dropped element was Last_Element ----

def re_init(-A: Data, +t: List<&2, A>, +h: A, +i: Nat, +hi: {Nat.is_lt(i, SC.length(A, SC.init(A, Con{h, t}))) == True{} : Bool}) -> {SC.nth(A, SC.init(A, Con{h, t}), i) == SC.nth(A, Con{h, t}, i) : Maybe<&2, A>}:
  match t i:
    case Nil{} _:
      Empty.absurd({SC.nth(A, SC.init(A, Con{h, Nil{}}), i) == SC.nth(A, Con{h, Nil{}}, i) : Maybe<&2, A>}, N.lt_zero_absurd(i, hi))
    case Con{a, b} 0n:
      {==}
    case Con{+a, +b} 1n+p:
      re_init(A, b, a, p, hi)

def init_length(-A: Data, +t: List<&2, A>, +h: A) -> {SC.length(A, SC.init(A, Con{h, t})) == SC.length(A, t) : Nat}:
  match t:
    case Nil{}:
      {==}
    case Con{+a, +b}:
      N.succ_cong(SC.length(A, SC.init(A, Con{a, b})), SC.length(A, b), init_length(A, b, a))

def init_prefix(-A: Data, +t: List<&2, A>, +h: A) -> Q.EqualPrefix(A, SC.init(A, Con{h, t}), Con{h, t}):
  %Equal.sym(Nat, SC.length(A, SC.init(A, Con{h, t})), SC.length(A, t), init_length(A, t, h)) : {Nat.is_le(_, 1n+SC.length(A, t)) == True{} : Bool} & Q.RangeEqual(A, SC.init(A, Con{h, t}), Con{h, t}, 0n, SC.length(A, SC.init(A, Con{h, t})))
  (N.le_succ(SC.length(A, t)), i => h1 => h2 => re_init(A, t, h, i, h2))

def last_is_elem(-A: Data, +t: List<&2, A>, +h: A) -> {SC.last(A, Con{h, t}) == Q.last_elem(A, Con{h, t}) : Maybe<&2, A>}:
  match t:
    case Nil{}:
      {==}
    case Con{+a, +b}:
      %Equal.sym(Nat, Nat.sub(1n+(1n+SC.length(A, b)), 1n), 1n+SC.length(A, b), succ_sub_one(1n+SC.length(A, b))) : {SC.last(A, Con{a, b}) == SC.nth(A, Con{h, Con{a, b}}, _) : Maybe<&2, A>}
      Equal.trans(Maybe<&2, A>, SC.last(A, Con{a, b}), SC.nth(A, Con{a, b}, Nat.sub(1n+SC.length(A, b), 1n)), SC.nth(A, Con{a, b}, SC.length(A, b)), last_is_elem(A, b, a), Equal.cong(Nat, Maybe<&2, A>, z => SC.nth(A, Con{a, b}, z), Nat.sub(1n+SC.length(A, b), 1n), SC.length(A, b), succ_sub_one(SC.length(A, b))))

# ---- Replace_Element (update): Length kept, the element at Index replaced, Equal_Except elsewhere ----

def update_except(-A: Data, +xs: List<&2, A>, +i: Nat, +v: A) -> Q.EqualExcept(A, xs, SC.update(A, xs, i, v), i):
  (Equal.sym(Nat, SC.length(A, SC.update(A, xs, i, v)), SC.length(A, xs), LL.length_update(A, xs, i, v)), j => ne => Equal.sym(Maybe<&2, A>, SC.nth(A, SC.update(A, xs, i, v), j), SC.nth(A, xs, j), LL.nth_update_other(A, xs, i, j, v, ne)))

def update_at(-A: Data, +xs: List<&2, A>, +i: Nat, +v: A, +h: {Nat.is_lt(i, SC.length(A, xs)) == True{} : Bool}) -> {SC.nth(A, SC.update(A, xs, i, v), i) == Some{v} : Maybe<&2, A>}:
  LL.nth_update_same(A, xs, i, v, h)

def update_length(-A: Data, +xs: List<&2, A>, +i: Nat, +v: A) -> {SC.length(A, SC.update(A, xs, i, v)) == SC.length(A, xs) : Nat}:
  LL.length_update(A, xs, i, v)

# ---- Reserve_Capacity / Assign / reads: the model is unchanged (M.Equal) ----

def same_prefix(-A: Data, +xs: List<&2, A>) -> Q.EqualPrefix(A, xs, xs):
  (N.le_refl(SC.length(A, xs)), i => h1 => h2 => {==})

# ---- Insert in the middle: a ++ c becomes a ++ [n] ++ c (Insert at Before = Length (a)) ----
# Range_Equal (old, new, First, Before - 1), Element (new, Before) = New_Item,
# Range_Shifted (old, new, Before, Last'Old, 1), Length + 1. Read with the
# roles swapped (old = a ++ [n] ++ c, new = a ++ c) it is Delete at Before.

def mid_equal(-A: Data, +a: List<&2, A>, +c: List<&2, A>, +n: A) -> Q.RangeEqual(A, SC.append(A, a, c), SC.append(A, a, Con{n, c}), 0n, SC.length(A, a)):
  i => h1 => h2 => Equal.trans(Maybe<&2, A>, SC.nth(A, SC.append(A, a, c), i), SC.nth(A, a, i), SC.nth(A, SC.append(A, a, Con{n, c}), i), LL.nth_append_left(A, a, c, i, h2), Equal.sym(Maybe<&2, A>, SC.nth(A, SC.append(A, a, Con{n, c}), i), SC.nth(A, a, i), LL.nth_append_left(A, a, Con{n, c}, i, h2)))

def mid_at(-A: Data, +a: List<&2, A>, +c: List<&2, A>, +n: A) -> {SC.nth(A, SC.append(A, a, Con{n, c}), SC.length(A, a)) == Some{n} : Maybe<&2, A>}:
  %Equal.sym(Maybe<&2, A>, SC.nth(A, SC.append(A, a, Con{n, c}), SC.length(A, a)), SC.nth(A, Con{n, c}, Nat.sub(SC.length(A, a), SC.length(A, a))), LL.nth_append_right(A, a, Con{n, c}, SC.length(A, a), N.le_refl(SC.length(A, a)))) : {_ == Some{n} : Maybe<&2, A>}
  %Equal.sym(Nat, Nat.sub(SC.length(A, a), SC.length(A, a)), 0n, N.sub_self(SC.length(A, a))) : {SC.nth(A, Con{n, c}, _) == Some{n} : Maybe<&2, A>}
  {==}

def mid_shift_at(-A: Data, +a: List<&2, A>, +c: List<&2, A>, +n: A, +i: Nat, +h1: {Nat.is_le(SC.length(A, a), i) == True{} : Bool}) -> {SC.nth(A, SC.append(A, a, c), i) == SC.nth(A, SC.append(A, a, Con{n, c}), Nat.add(i, 1n)) : Maybe<&2, A>}:
  %Equal.sym(Nat, Nat.add(i, 1n), 1n+i, add_one(i)) : {SC.nth(A, SC.append(A, a, c), i) == SC.nth(A, SC.append(A, a, Con{n, c}), _) : Maybe<&2, A>}
  %Equal.sym(Maybe<&2, A>, SC.nth(A, SC.append(A, a, c), i), SC.nth(A, c, Nat.sub(i, SC.length(A, a))), LL.nth_append_right(A, a, c, i, h1)) : {_ == SC.nth(A, SC.append(A, a, Con{n, c}), 1n+i) : Maybe<&2, A>}
  %Equal.sym(Maybe<&2, A>, SC.nth(A, SC.append(A, a, Con{n, c}), 1n+i), SC.nth(A, Con{n, c}, Nat.sub(1n+i, SC.length(A, a))), LL.nth_append_right(A, a, Con{n, c}, 1n+i, N.le_trans(SC.length(A, a), i, 1n+i, h1, N.le_succ(i)))) : {SC.nth(A, c, Nat.sub(i, SC.length(A, a))) == _ : Maybe<&2, A>}
  %Equal.sym(Nat, Nat.sub(1n+i, SC.length(A, a)), 1n+Nat.sub(i, SC.length(A, a)), N.sub_succ_left(i, SC.length(A, a), h1)) : {SC.nth(A, c, Nat.sub(i, SC.length(A, a))) == SC.nth(A, Con{n, c}, _) : Maybe<&2, A>}
  {==}

def mid_shifted(-A: Data, +a: List<&2, A>, +c: List<&2, A>, +n: A) -> Q.RangeShifted(A, SC.append(A, a, c), SC.append(A, a, Con{n, c}), SC.length(A, a), SC.length(A, SC.append(A, a, c)), 1n):
  i => h1 => h2 => mid_shift_at(A, a, c, n, i, h1)

def mid_length(-A: Data, +a: List<&2, A>, +c: List<&2, A>, +n: A) -> {SC.length(A, SC.append(A, a, Con{n, c})) == 1n+SC.length(A, SC.append(A, a, c)) : Nat}:
  %Equal.sym(Nat, SC.length(A, SC.append(A, a, Con{n, c})), Nat.add(SC.length(A, a), 1n+SC.length(A, c)), LL.length_append(A, a, Con{n, c})) : {_ == 1n+SC.length(A, SC.append(A, a, c)) : Nat}
  %Equal.sym(Nat, SC.length(A, SC.append(A, a, c)), Nat.add(SC.length(A, a), SC.length(A, c)), LL.length_append(A, a, c)) : {Nat.add(SC.length(A, a), 1n+SC.length(A, c)) == 1n+_ : Nat}
  N.add_succ(SC.length(A, a), SC.length(A, c))
