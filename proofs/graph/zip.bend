import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../../spec/common.bend as SC

# List-level effect of the vertex-table shift loops of src/graph.bend.
#
# A left shift of k steps starting at j performs, for each step,
#   xs[j] := xs[j+1]           (and, for the adjacency array, xs[j+1] := f)
# and a right shift performs xs[j] := xs[j-1] (and xs[j-1] := f). When the
# caller then writes the new entry at the vacated position, the result is
# an insertion. The lemmas state that with the list split as a zipper, so
# no index arithmetic beyond `length` is needed.

def clr(-T: Data, +c: Bool, +f: T, xs: List<&2, T>, +i: Nat) -> List<&2, T>:
  match c:
    case True{}:
      SC.update(T, xs, i, f)
    case False{}:
      xs

def vget(-T: Data, +d: T, +xs: List<&2, T>, +i: Nat) -> T:
  L.some_value(T, SC.nth(T, xs, i), d)

def lsl(-T: Data, +c: Bool, +f: T, +d: T, k: Nat, +xs: List<&2, T>, +j: Nat) -> List<&2, T>:
  match k:
    case 0n:
      xs
    case 1n+m:
      lsl(T, c, f, d, m, SC.update(T, clr(T, c, f, xs, 1n+j), j, vget(T, d, xs, 1n+j)), 1n+j)

def lsr(-T: Data, +c: Bool, +f: T, +d: T, k: Nat, +xs: List<&2, T>, +j: Nat) -> List<&2, T>:
  match k:
    case 0n:
      xs
    case 1n+m:
      lsr(T, c, f, d, m, SC.update(T, clr(T, c, f, xs, Nat.sub(j, 1n)), j, vget(T, d, xs, Nat.sub(j, 1n))), Nat.sub(j, 1n))

# ---- positional facts about a zipper P ++ rest ----

def upd0(-T: Data, +p: List<&2, T>, +y: T, +rest: List<&2, T>, +v: T) -> {SC.update(T, SC.append(T, p, Con{y, rest}), SC.length(T, p), v) == SC.append(T, p, Con{v, rest}) : List<&2, T>}:
  match p:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      LL.cons_cong(T, h, SC.update(T, SC.append(T, t, Con{y, rest}), SC.length(T, t), v), SC.append(T, t, Con{v, rest}), upd0(T, t, y, rest, v))

def upd1(-T: Data, +p: List<&2, T>, +y: T, +a: T, +rest: List<&2, T>, +v: T) -> {SC.update(T, SC.append(T, p, Con{y, Con{a, rest}}), 1n+SC.length(T, p), v) == SC.append(T, p, Con{y, Con{v, rest}}) : List<&2, T>}:
  match p:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      LL.cons_cong(T, h, SC.update(T, SC.append(T, t, Con{y, Con{a, rest}}), 1n+SC.length(T, t), v), SC.append(T, t, Con{y, Con{v, rest}}), upd1(T, t, y, a, rest, v))

def nth0(-T: Data, +p: List<&2, T>, +y: T, +rest: List<&2, T>) -> {SC.nth(T, SC.append(T, p, Con{y, rest}), SC.length(T, p)) == Some{y} : Maybe<&2, T>}:
  match p:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      nth0(T, t, y, rest)

def nth1(-T: Data, +p: List<&2, T>, +y: T, +a: T, +rest: List<&2, T>) -> {SC.nth(T, SC.append(T, p, Con{y, Con{a, rest}}), 1n+SC.length(T, p)) == Some{a} : Maybe<&2, T>}:
  match p:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      nth1(T, t, y, a, rest)

def cf(-T: Data, +c: Bool, +f: T, +a: T) -> T:
  match c:
    case True{}:
      f
    case False{}:
      a

def clr1(-T: Data, +c: Bool, +f: T, +p: List<&2, T>, +y: T, +a: T, +rest: List<&2, T>) -> {clr(T, c, f, SC.append(T, p, Con{y, Con{a, rest}}), 1n+SC.length(T, p)) == SC.append(T, p, Con{y, Con{cf(T, c, f, a), rest}}) : List<&2, T>}:
  match c:
    case True{}:
      upd1(T, p, y, a, rest, f)
    case False{}:
      {==}

def clr0(-T: Data, +c: Bool, +f: T, +p: List<&2, T>, +y: T, +rest: List<&2, T>) -> {clr(T, c, f, SC.append(T, p, Con{y, rest}), SC.length(T, p)) == SC.append(T, p, Con{cf(T, c, f, y), rest}) : List<&2, T>}:
  match c:
    case True{}:
      upd0(T, p, y, rest, f)
    case False{}:
      {==}

# ---- left shift then write: an insertion ----

# The list after the first step of a left shift, as a zipper one to the right.
def zl_step(-T: Data, +c: Bool, +f: T, +d: T, +a: T, +p: List<&2, T>, +y: T, +rest: List<&2, T>) -> {SC.update(T, clr(T, c, f, SC.append(T, p, Con{y, Con{a, rest}}), 1n+SC.length(T, p)), SC.length(T, p), vget(T, d, SC.append(T, p, Con{y, Con{a, rest}}), 1n+SC.length(T, p))) == SC.append(T, SC.snoc(T, p, a), Con{cf(T, c, f, a), rest}) : List<&2, T>}:
  +xs = SC.append(T, p, Con{y, Con{a, rest}})
  +n = SC.length(T, p)
  Equal.trans(List<&2, T>, SC.update(T, clr(T, c, f, xs, 1n+n), n, vget(T, d, xs, 1n+n)), SC.update(T, clr(T, c, f, xs, 1n+n), n, a), SC.append(T, SC.snoc(T, p, a), Con{cf(T, c, f, a), rest}),
    Equal.cong(Maybe<&2, T>, List<&2, T>, m => SC.update(T, clr(T, c, f, xs, 1n+n), n, L.some_value(T, m, d)), SC.nth(T, xs, 1n+n), Some{a}, nth1(T, p, y, a, rest)),
    Equal.trans(List<&2, T>, SC.update(T, clr(T, c, f, xs, 1n+n), n, a), SC.update(T, SC.append(T, p, Con{y, Con{cf(T, c, f, a), rest}}), n, a), SC.append(T, SC.snoc(T, p, a), Con{cf(T, c, f, a), rest}),
      Equal.cong(List<&2, T>, List<&2, T>, z => SC.update(T, z, n, a), clr(T, c, f, xs, 1n+n), SC.append(T, p, Con{y, Con{cf(T, c, f, a), rest}}), clr1(T, c, f, p, y, a, rest)),
      Equal.trans(List<&2, T>, SC.update(T, SC.append(T, p, Con{y, Con{cf(T, c, f, a), rest}}), n, a), SC.append(T, p, Con{a, Con{cf(T, c, f, a), rest}}), SC.append(T, SC.snoc(T, p, a), Con{cf(T, c, f, a), rest}),
        upd0(T, p, y, Con{cf(T, c, f, a), rest}, a),
        Equal.sym(List<&2, T>, SC.append(T, SC.snoc(T, p, a), Con{cf(T, c, f, a), rest}), SC.append(T, p, Con{a, Con{cf(T, c, f, a), rest}}), LL.snoc_append_cons(T, p, a, Con{cf(T, c, f, a), rest})))))

# Shifting A one slot left over y and writing v after it: P ++ A ++ [v] ++ R.
def zl(-T: Data, +c: Bool, +f: T, +d: T, +qa: List<&2, T>, +p: List<&2, T>, +y: T, +r: List<&2, T>, +v: T) -> {SC.update(T, lsl(T, c, f, d, SC.length(T, qa), SC.append(T, p, Con{y, SC.append(T, qa, r)}), SC.length(T, p)), Nat.add(SC.length(T, p), SC.length(T, qa)), v) == SC.append(T, p, SC.append(T, qa, Con{v, r})) : List<&2, T>}:
  match qa:
    case Nil{}:
      L.subst(Nat, z => {SC.update(T, SC.append(T, p, Con{y, r}), z, v) == SC.append(T, p, Con{v, r}) : List<&2, T>}, SC.length(T, p), Nat.add(SC.length(T, p), 0n), Equal.sym(Nat, Nat.add(SC.length(T, p), 0n), SC.length(T, p), N.add_zero(SC.length(T, p))), upd0(T, p, y, r, v))
    case Con{+a, +qt}:
      +n = SC.length(T, p)
      +m = SC.length(T, qt)
      +rest = SC.append(T, qt, r)
      +xs = SC.append(T, p, Con{y, Con{a, rest}})
      +x1 = SC.update(T, clr(T, c, f, xs, 1n+n), n, vget(T, d, xs, 1n+n))
      +x2 = SC.append(T, SC.snoc(T, p, a), Con{cf(T, c, f, a), rest})
      +rhs = SC.append(T, SC.snoc(T, p, a), SC.append(T, qt, Con{v, r}))
      +ih = L.subst(Nat, k => {SC.update(T, lsl(T, c, f, d, m, x2, k), Nat.add(k, m), v) == rhs : List<&2, T>}, SC.length(T, SC.snoc(T, p, a)), 1n+n, LL.length_snoc(T, p, a), zl(T, c, f, d, qt, SC.snoc(T, p, a), cf(T, c, f, a), r, v))
      +ih2 = L.subst(List<&2, T>, z => {SC.update(T, lsl(T, c, f, d, m, z, 1n+n), 1n+Nat.add(n, m), v) == rhs : List<&2, T>}, x2, x1, Equal.sym(List<&2, T>, x1, x2, zl_step(T, c, f, d, a, p, y, rest)), ih)
      +ih3 = Equal.trans(List<&2, T>, SC.update(T, lsl(T, c, f, d, m, x1, 1n+n), 1n+Nat.add(n, m), v), rhs, SC.append(T, p, Con{a, SC.append(T, qt, Con{v, r})}), ih2, LL.snoc_append_cons(T, p, a, SC.append(T, qt, Con{v, r})))
      L.subst(Nat, z => {SC.update(T, lsl(T, c, f, d, m, x1, 1n+n), z, v) == SC.append(T, p, Con{a, SC.append(T, qt, Con{v, r})}) : List<&2, T>}, 1n+Nat.add(n, m), Nat.add(n, 1n+m), Equal.sym(Nat, Nat.add(n, 1n+m), 1n+Nat.add(n, m), N.add_succ(n, m)), ih3)

# ---- right shift then write: an insertion ----

def zr_core(-T: Data, +c: Bool, +f: T, +d: T, +q: List<&2, T>, +c0: T, +y: T, +r: List<&2, T>) -> {SC.update(T, clr(T, c, f, SC.append(T, q, Con{c0, Con{y, r}}), SC.length(T, q)), 1n+SC.length(T, q), vget(T, d, SC.append(T, q, Con{c0, Con{y, r}}), SC.length(T, q))) == SC.append(T, q, Con{cf(T, c, f, c0), Con{c0, r}}) : List<&2, T>}:
  +xq = SC.append(T, q, Con{c0, Con{y, r}})
  +l = SC.length(T, q)
  Equal.trans(List<&2, T>, SC.update(T, clr(T, c, f, xq, l), 1n+l, vget(T, d, xq, l)), SC.update(T, clr(T, c, f, xq, l), 1n+l, c0), SC.append(T, q, Con{cf(T, c, f, c0), Con{c0, r}}),
    Equal.cong(Maybe<&2, T>, List<&2, T>, m => SC.update(T, clr(T, c, f, xq, l), 1n+l, L.some_value(T, m, d)), SC.nth(T, xq, l), Some{c0}, nth0(T, q, c0, Con{y, r})),
    Equal.trans(List<&2, T>, SC.update(T, clr(T, c, f, xq, l), 1n+l, c0), SC.update(T, SC.append(T, q, Con{cf(T, c, f, c0), Con{y, r}}), 1n+l, c0), SC.append(T, q, Con{cf(T, c, f, c0), Con{c0, r}}),
      Equal.cong(List<&2, T>, List<&2, T>, z => SC.update(T, z, 1n+l, c0), clr(T, c, f, xq, l), SC.append(T, q, Con{cf(T, c, f, c0), Con{y, r}}), clr0(T, c, f, q, c0, Con{y, r})),
      upd1(T, q, cf(T, c, f, c0), y, r, c0)))

def FS(-T: Data, +c: Bool, +f: T, +d: T, +z: List<&2, T>, +s: Nat, +j: Nat) -> List<&2, T>:
  SC.update(T, clr(T, c, f, z, s), j, vget(T, d, z, s))

def zr_step(-T: Data, +c: Bool, +f: T, +d: T, +c0: T, +cs: List<&2, T>, +p: List<&2, T>, +y: T, +r: List<&2, T>) -> {FS(T, c, f, d, SC.append(T, p, SC.append(T, SC.snoc(T, SC.reverse(T, cs), c0), Con{y, r})), Nat.sub(Nat.add(SC.length(T, p), 1n+SC.length(T, cs)), 1n), Nat.add(SC.length(T, p), 1n+SC.length(T, cs))) == SC.append(T, p, SC.append(T, SC.reverse(T, cs), Con{cf(T, c, f, c0), Con{c0, r}})) : List<&2, T>}:
  +bs = SC.reverse(T, cs)
  +q = SC.append(T, p, bs)
  +n = Nat.add(SC.length(T, p), SC.length(T, cs))
  +j = Nat.add(SC.length(T, p), 1n+SC.length(T, cs))
  +xs = SC.append(T, p, SC.append(T, SC.snoc(T, bs, c0), Con{y, r}))
  +xq = SC.append(T, q, Con{c0, Con{y, r}})
  +ej = N.add_succ(SC.length(T, p), SC.length(T, cs))
  +es = Equal.trans(Nat, Nat.sub(j, 1n), Nat.sub(1n+n, 1n), n, Equal.cong(Nat, Nat, z => Nat.sub(z, 1n), j, 1n+n, ej), N.sub_zero(n))
  +el = Equal.trans(Nat, SC.length(T, q), Nat.add(SC.length(T, p), SC.length(T, bs)), n, LL.length_append(T, p, bs), Equal.cong(Nat, Nat, z => Nat.add(SC.length(T, p), z), SC.length(T, bs), SC.length(T, cs), LL.length_rev(T, cs)))
  +hxs = Equal.trans(List<&2, T>, xs, SC.append(T, p, SC.append(T, bs, Con{c0, Con{y, r}})), xq,
    Equal.cong(List<&2, T>, List<&2, T>, z => SC.append(T, p, z), SC.append(T, SC.snoc(T, bs, c0), Con{y, r}), SC.append(T, bs, Con{c0, Con{y, r}}), LL.snoc_append_cons(T, bs, c0, Con{y, r})),
    Equal.sym(List<&2, T>, xq, SC.append(T, p, SC.append(T, bs, Con{c0, Con{y, r}})), LL.append_assoc(T, p, bs, Con{c0, Con{y, r}})))
  +e1 = Equal.cong(List<&2, T>, List<&2, T>, z => FS(T, c, f, d, z, Nat.sub(j, 1n), j), xs, xq, hxs)
  +e2 = Equal.cong(Nat, List<&2, T>, s => FS(T, c, f, d, xq, s, j), Nat.sub(j, 1n), n, es)
  +e3 = Equal.cong(Nat, List<&2, T>, k => FS(T, c, f, d, xq, n, k), j, 1n+n, ej)
  +e4 = Equal.cong(Nat, List<&2, T>, k => FS(T, c, f, d, xq, k, 1n+k), n, SC.length(T, q), Equal.sym(Nat, SC.length(T, q), n, el))
  +e5 = zr_core(T, c, f, d, q, c0, y, r)
  +e6 = LL.append_assoc(T, p, bs, Con{cf(T, c, f, c0), Con{c0, r}})
  Equal.trans(List<&2, T>, FS(T, c, f, d, xs, Nat.sub(j, 1n), j), FS(T, c, f, d, xq, Nat.sub(j, 1n), j), SC.append(T, p, SC.append(T, bs, Con{cf(T, c, f, c0), Con{c0, r}})), e1,
    Equal.trans(List<&2, T>, FS(T, c, f, d, xq, Nat.sub(j, 1n), j), FS(T, c, f, d, xq, n, j), SC.append(T, p, SC.append(T, bs, Con{cf(T, c, f, c0), Con{c0, r}})), e2,
      Equal.trans(List<&2, T>, FS(T, c, f, d, xq, n, j), FS(T, c, f, d, xq, n, 1n+n), SC.append(T, p, SC.append(T, bs, Con{cf(T, c, f, c0), Con{c0, r}})), e3,
        Equal.trans(List<&2, T>, FS(T, c, f, d, xq, n, 1n+n), FS(T, c, f, d, xq, SC.length(T, q), 1n+SC.length(T, q)), SC.append(T, p, SC.append(T, bs, Con{cf(T, c, f, c0), Con{c0, r}})), e4,
          Equal.trans(List<&2, T>, FS(T, c, f, d, xq, SC.length(T, q), 1n+SC.length(T, q)), SC.append(T, q, Con{cf(T, c, f, c0), Con{c0, r}}), SC.append(T, p, SC.append(T, bs, Con{cf(T, c, f, c0), Con{c0, r}})), e5, e6)))))

# Shifting reverse(C) one slot right into y and writing v before it: P ++ [v] ++ reverse(C) ++ R.
def zr(-T: Data, +c: Bool, +f: T, +d: T, +cs: List<&2, T>, +p: List<&2, T>, +y: T, +r: List<&2, T>, +v: T) -> {SC.update(T, lsr(T, c, f, d, SC.length(T, cs), SC.append(T, p, SC.append(T, SC.reverse(T, cs), Con{y, r})), Nat.add(SC.length(T, p), SC.length(T, cs))), SC.length(T, p), v) == SC.append(T, p, Con{v, SC.append(T, SC.reverse(T, cs), r)}) : List<&2, T>}:
  match cs:
    case Nil{}:
      upd0(T, p, y, r, v)
    case Con{+c0, +ct}:
      +bs = SC.reverse(T, ct)
      +n = Nat.add(SC.length(T, p), SC.length(T, ct))
      +j = Nat.add(SC.length(T, p), 1n+SC.length(T, ct))
      +xs = SC.append(T, p, SC.append(T, SC.snoc(T, bs, c0), Con{y, r}))
      +fx = FS(T, c, f, d, xs, Nat.sub(j, 1n), j)
      +x1 = SC.append(T, p, SC.append(T, bs, Con{cf(T, c, f, c0), Con{c0, r}}))
      +rh = SC.append(T, p, Con{v, SC.append(T, bs, Con{c0, r})})
      +es = Equal.trans(Nat, Nat.sub(j, 1n), Nat.sub(1n+n, 1n), n, Equal.cong(Nat, Nat, z => Nat.sub(z, 1n), j, 1n+n, N.add_succ(SC.length(T, p), SC.length(T, ct))), N.sub_zero(n))
      +ih = zr(T, c, f, d, ct, p, cf(T, c, f, c0), Con{c0, r}, v)
      +ih2 = L.subst(List<&2, T>, z => {SC.update(T, lsr(T, c, f, d, SC.length(T, ct), z, n), SC.length(T, p), v) == rh : List<&2, T>}, x1, fx, Equal.sym(List<&2, T>, fx, x1, zr_step(T, c, f, d, c0, ct, p, y, r)), ih)
      +ih3 = L.subst(Nat, s => {SC.update(T, lsr(T, c, f, d, SC.length(T, ct), fx, s), SC.length(T, p), v) == rh : List<&2, T>}, n, Nat.sub(j, 1n), Equal.sym(Nat, Nat.sub(j, 1n), n, es), ih2)
      Equal.trans(List<&2, T>, SC.update(T, lsr(T, c, f, d, SC.length(T, ct), fx, Nat.sub(j, 1n)), SC.length(T, p), v), rh, SC.append(T, p, Con{v, SC.append(T, SC.snoc(T, bs, c0), r)}), ih3,
        Equal.cong(List<&2, T>, List<&2, T>, z => SC.append(T, p, Con{v, z}), SC.append(T, bs, Con{c0, r}), SC.append(T, SC.snoc(T, bs, c0), r), Equal.sym(List<&2, T>, SC.append(T, SC.snoc(T, bs, c0), r), SC.append(T, bs, Con{c0, r}), LL.snoc_append_cons(T, bs, c0, r))))

# ---- take / drop around a zipper ----

def drop0(-T: Data, +xs: List<&2, T>) -> {SC.drop(T, xs, 0n) == xs : List<&2, T>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      {==}

def take_app_len(-T: Data, +a: List<&2, T>, +z: List<&2, T>, +m: Nat) -> {SC.take(T, SC.append(T, a, z), Nat.add(SC.length(T, a), m)) == SC.append(T, a, SC.take(T, z, m)) : List<&2, T>}:
  match a:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      LL.cons_cong(T, h, SC.take(T, SC.append(T, t, z), Nat.add(SC.length(T, t), m)), SC.append(T, t, SC.take(T, z, m)), take_app_len(T, t, z, m))

def take_app_exact(-T: Data, +b: List<&2, T>, +r: List<&2, T>) -> {SC.take(T, SC.append(T, b, r), SC.length(T, b)) == b : List<&2, T>}:
  match b:
    case Nil{}:
      LL.sc_take_zero(T, r)
    case Con{+h, +t}:
      LL.cons_cong(T, h, SC.take(T, SC.append(T, t, r), SC.length(T, t)), t, take_app_exact(T, t, r))

def drop_app_len(-T: Data, +p: List<&2, T>, +w: List<&2, T>) -> {SC.drop(T, SC.append(T, p, w), SC.length(T, p)) == w : List<&2, T>}:
  match p:
    case Nil{}:
      drop0(T, w)
    case Con{+h, +t}:
      drop_app_len(T, t, w)

def take_drop_app(-T: Data, +xs: List<&2, T>, +n: Nat) -> {SC.append(T, SC.take(T, xs, n), SC.drop(T, xs, n)) == xs : List<&2, T>}:
  match xs n:
    case Nil{} n0:
      {==}
    case Con{+h, +t} 0n:
      {==}
    case Con{+h, +t} 1n+p:
      LL.cons_cong(T, h, SC.append(T, SC.take(T, t, p), SC.drop(T, t, p)), t, take_drop_app(T, t, p))

def drop_cons_g(-T: Data, +xs: List<&2, T>, +a: Nat, +d: T, +ha: {Nat.is_lt(a, SC.length(T, xs)) == True{} : Bool}) -> {SC.drop(T, xs, a) == Con{vget(T, d, xs, a), SC.drop(T, xs, 1n+a)} : List<&2, T>}:
  match xs a:
    case Nil{} a0:
      Empty.absurd({SC.drop(T, Nil{}, a0) == Con{vget(T, d, Nil{}, a0), SC.drop(T, Nil{}, 1n+a0)} : List<&2, T>}, L.false_true(Equal.trans(Bool, False{}, Nat.is_lt(a0, 0n), True{}, Equal.sym(Bool, Nat.is_lt(a0, 0n), False{}, N.not_lt_zero(a0)), ha)))
    case Con{+h, +t} 0n:
      LL.cons_cong(T, h, t, SC.drop(T, t, 0n), Equal.sym(List<&2, T>, SC.drop(T, t, 0n), t, drop0(T, t)))
    case Con{+h, +t} 1n+p:
      drop_cons_g(T, t, p, d, ha)

def le_cancel(+c: Nat, +a: Nat, +b: Nat, +h: {Nat.is_le(Nat.add(c, a), Nat.add(c, b)) == True{} : Bool}) -> {Nat.is_le(a, b) == True{} : Bool}:
  match c:
    case 0n:
      h
    case 1n+p:
      le_cancel(p, a, b, h)

def lt_cancel(+c: Nat, +a: Nat, +b: Nat, +h: {Nat.is_lt(Nat.add(c, a), Nat.add(c, b)) == True{} : Bool}) -> {Nat.is_lt(a, b) == True{} : Bool}:
  match c:
    case 0n:
      h
    case 1n+p:
      lt_cancel(p, a, b, h)

# The length of the list after position n (n within the list).
def len_split(-T: Data, +xs: List<&2, T>, +n: Nat, +h: {Nat.is_le(n, SC.length(T, xs)) == True{} : Bool}) -> {Nat.add(n, SC.length(T, SC.drop(T, xs, n))) == SC.length(T, xs) : Nat}:
  +e = Equal.trans(Nat, SC.length(T, xs), SC.length(T, SC.append(T, SC.take(T, xs, n), SC.drop(T, xs, n))), Nat.add(SC.length(T, SC.take(T, xs, n)), SC.length(T, SC.drop(T, xs, n))),
    Equal.cong(List<&2, T>, Nat, z => SC.length(T, z), xs, SC.append(T, SC.take(T, xs, n), SC.drop(T, xs, n)), Equal.sym(List<&2, T>, SC.append(T, SC.take(T, xs, n), SC.drop(T, xs, n)), xs, take_drop_app(T, xs, n))),
    LL.length_append(T, SC.take(T, xs, n), SC.drop(T, xs, n)))
  Equal.sym(Nat, SC.length(T, xs), Nat.add(n, SC.length(T, SC.drop(T, xs, n))),
    L.subst(Nat, z => {SC.length(T, xs) == Nat.add(z, SC.length(T, SC.drop(T, xs, n))) : Nat}, SC.length(T, SC.take(T, xs, n)), n, LL.sc_length_take(T, xs, n, h), e))

# The final window: P ++ A ++ [v] ++ B ++ R seen from |P| for 1 + |A| + |B| slots.
def wt(-T: Data, +p: List<&2, T>, +a: List<&2, T>, +v: T, +b: List<&2, T>, +r: List<&2, T>) -> {SC.take(T, SC.drop(T, SC.append(T, p, SC.append(T, a, Con{v, SC.append(T, b, r)})), SC.length(T, p)), 1n+Nat.add(SC.length(T, a), SC.length(T, b))) == SC.append(T, a, Con{v, b}) : List<&2, T>}:
  +w = SC.append(T, a, Con{v, SC.append(T, b, r)})
  Equal.trans(List<&2, T>, SC.take(T, SC.drop(T, SC.append(T, p, w), SC.length(T, p)), 1n+Nat.add(SC.length(T, a), SC.length(T, b))), SC.take(T, w, 1n+Nat.add(SC.length(T, a), SC.length(T, b))), SC.append(T, a, Con{v, b}),
    Equal.cong(List<&2, T>, List<&2, T>, z => SC.take(T, z, 1n+Nat.add(SC.length(T, a), SC.length(T, b))), SC.drop(T, SC.append(T, p, w), SC.length(T, p)), w, drop_app_len(T, p, w)),
    Equal.trans(List<&2, T>, SC.take(T, w, 1n+Nat.add(SC.length(T, a), SC.length(T, b))), SC.take(T, w, Nat.add(SC.length(T, a), 1n+SC.length(T, b))), SC.append(T, a, Con{v, b}),
      Equal.cong(Nat, List<&2, T>, k => SC.take(T, w, k), 1n+Nat.add(SC.length(T, a), SC.length(T, b)), Nat.add(SC.length(T, a), 1n+SC.length(T, b)), Equal.sym(Nat, Nat.add(SC.length(T, a), 1n+SC.length(T, b)), 1n+Nat.add(SC.length(T, a), SC.length(T, b)), N.add_succ(SC.length(T, a), SC.length(T, b)))),
      Equal.trans(List<&2, T>, SC.take(T, w, Nat.add(SC.length(T, a), 1n+SC.length(T, b))), SC.append(T, a, Con{v, SC.take(T, SC.append(T, b, r), SC.length(T, b))}), SC.append(T, a, Con{v, b}),
        take_app_len(T, a, Con{v, SC.append(T, b, r)}, 1n+SC.length(T, b)),
        Equal.cong(List<&2, T>, List<&2, T>, z => SC.append(T, a, Con{v, z}), SC.take(T, SC.append(T, b, r), SC.length(T, b)), b, take_app_exact(T, b, r)))))

# ---- the window after an insertion by shifting ----

# Left shift of the first l window entries into the free slot lo1 = lo - 1,
# then the write at lo1 + l.
def ins_left_win(-T: Data, +c: Bool, +f: T, +d: T, +xs: List<&2, T>, +lo1: Nat, +k: Nat, +l: Nat, +v: T, +hl: {Nat.is_le(l, k) == True{} : Bool}, +hk: {Nat.is_le(Nat.add(1n+lo1, k), SC.length(T, xs)) == True{} : Bool}) -> {SC.take(T, SC.drop(T, SC.update(T, lsl(T, c, f, d, l, xs, lo1), Nat.add(lo1, l), v), lo1), 1n+k) == SC.append(T, SC.take(T, SC.take(T, SC.drop(T, xs, 1n+lo1), k), l), Con{v, SC.drop(T, SC.take(T, SC.drop(T, xs, 1n+lo1), k), l)}) : List<&2, T>}:
  +p = SC.take(T, xs, lo1)
  +y = vget(T, d, xs, lo1)
  +dd = SC.drop(T, xs, 1n+lo1)
  +ks = SC.take(T, dd, k)
  +r = SC.drop(T, dd, k)
  +a = SC.take(T, ks, l)
  +b = SC.drop(T, ks, l)
  +h1 = N.le_trans(1n+lo1, Nat.add(1n+lo1, k), SC.length(T, xs), N.le_add_right(1n+lo1, k), hk)
  +hle = N.le_trans(lo1, 1n+lo1, SC.length(T, xs), N.le_succ(lo1), h1)
  +hlt = N.lt_le_trans(lo1, 1n+lo1, SC.length(T, xs), N.lt_succ(lo1), h1)
  +hxs = Equal.trans(List<&2, T>, xs, SC.append(T, p, SC.drop(T, xs, lo1)), SC.append(T, p, Con{y, SC.append(T, a, SC.append(T, b, r))}),
    Equal.sym(List<&2, T>, SC.append(T, p, SC.drop(T, xs, lo1)), xs, take_drop_app(T, xs, lo1)),
    Equal.cong(List<&2, T>, List<&2, T>, z => SC.append(T, p, z), SC.drop(T, xs, lo1), Con{y, SC.append(T, a, SC.append(T, b, r))},
      Equal.trans(List<&2, T>, SC.drop(T, xs, lo1), Con{y, dd}, Con{y, SC.append(T, a, SC.append(T, b, r))}, drop_cons_g(T, xs, lo1, d, hlt),
        LL.cons_cong(T, y, dd, SC.append(T, a, SC.append(T, b, r)),
          Equal.trans(List<&2, T>, dd, SC.append(T, ks, r), SC.append(T, a, SC.append(T, b, r)), Equal.sym(List<&2, T>, SC.append(T, ks, r), dd, take_drop_app(T, dd, k)),
            Equal.trans(List<&2, T>, SC.append(T, ks, r), SC.append(T, SC.append(T, a, b), r), SC.append(T, a, SC.append(T, b, r)),
              Equal.cong(List<&2, T>, List<&2, T>, z => SC.append(T, z, r), ks, SC.append(T, a, b), Equal.sym(List<&2, T>, SC.append(T, a, b), ks, take_drop_app(T, ks, l))),
              LL.append_assoc(T, a, b, r)))))))
  +lenp = LL.sc_length_take(T, xs, lo1, hle)
  +hkd = le_cancel(1n+lo1, k, SC.length(T, dd), L.subst(Nat, z => {Nat.is_le(Nat.add(1n+lo1, k), z) == True{} : Bool}, SC.length(T, xs), Nat.add(1n+lo1, SC.length(T, dd)), Equal.sym(Nat, Nat.add(1n+lo1, SC.length(T, dd)), SC.length(T, xs), len_split(T, xs, 1n+lo1, h1)), hk))
  +lenks = LL.sc_length_take(T, dd, k, hkd)
  +lena = LL.sc_length_take(T, ks, l, L.subst(Nat, z => {Nat.is_le(l, z) == True{} : Bool}, k, SC.length(T, ks), Equal.sym(Nat, SC.length(T, ks), k, lenks), hl))
  +lenab = Equal.trans(Nat, Nat.add(SC.length(T, a), SC.length(T, b)), SC.length(T, ks), k,
    Equal.trans(Nat, Nat.add(SC.length(T, a), SC.length(T, b)), SC.length(T, SC.append(T, a, b)), SC.length(T, ks), Equal.sym(Nat, SC.length(T, SC.append(T, a, b)), Nat.add(SC.length(T, a), SC.length(T, b)), LL.length_append(T, a, b)),
      Equal.cong(List<&2, T>, Nat, z => SC.length(T, z), SC.append(T, a, b), ks, take_drop_app(T, ks, l))),
    lenks)
  +rz = SC.append(T, p, SC.append(T, a, Con{v, SC.append(T, b, r)}))
  +xz = SC.append(T, p, Con{y, SC.append(T, a, SC.append(T, b, r))})
  +z1 = L.subst(List<&2, T>, z => {SC.update(T, lsl(T, c, f, d, SC.length(T, a), z, SC.length(T, p)), Nat.add(SC.length(T, p), SC.length(T, a)), v) == rz : List<&2, T>}, xz, xs, Equal.sym(List<&2, T>, xs, xz, hxs), zl(T, c, f, d, a, p, y, SC.append(T, b, r), v))
  +z2 = L.subst(Nat, n => {SC.update(T, lsl(T, c, f, d, SC.length(T, a), xs, n), Nat.add(n, SC.length(T, a)), v) == rz : List<&2, T>}, SC.length(T, p), lo1, lenp, z1)
  +z3 = L.subst(Nat, n => {SC.update(T, lsl(T, c, f, d, n, xs, lo1), Nat.add(lo1, n), v) == rz : List<&2, T>}, SC.length(T, a), l, lena, z2)
  +w1 = L.subst(Nat, n => {SC.take(T, SC.drop(T, rz, n), 1n+Nat.add(SC.length(T, a), SC.length(T, b))) == SC.append(T, a, Con{v, b}) : List<&2, T>}, SC.length(T, p), lo1, lenp, wt(T, p, a, v, b, r))
  +w2 = L.subst(Nat, n => {SC.take(T, SC.drop(T, rz, lo1), 1n+n) == SC.append(T, a, Con{v, b}) : List<&2, T>}, Nat.add(SC.length(T, a), SC.length(T, b)), k, lenab, w1)
  L.subst(List<&2, T>, z => {SC.take(T, SC.drop(T, z, lo1), 1n+k) == SC.append(T, a, Con{v, b}) : List<&2, T>}, rz, SC.update(T, lsl(T, c, f, d, l, xs, lo1), Nat.add(lo1, l), v), Equal.sym(List<&2, T>, SC.update(T, lsl(T, c, f, d, l, xs, lo1), Nat.add(lo1, l), v), rz, z3), w2)

# Right shift of the last k - l window entries into the free slot lo + k,
# then the write at lo + l.
def ins_right_win(-T: Data, +c: Bool, +f: T, +d: T, +xs: List<&2, T>, +lo: Nat, +k: Nat, +l: Nat, +v: T, +hl: {Nat.is_le(l, k) == True{} : Bool}, +hk: {Nat.is_lt(Nat.add(lo, k), SC.length(T, xs)) == True{} : Bool}) -> {SC.take(T, SC.drop(T, SC.update(T, lsr(T, c, f, d, Nat.sub(k, l), xs, Nat.add(lo, k)), Nat.add(lo, l), v), lo), 1n+k) == SC.append(T, SC.take(T, SC.take(T, SC.drop(T, xs, lo), k), l), Con{v, SC.drop(T, SC.take(T, SC.drop(T, xs, lo), k), l)}) : List<&2, T>}:
  +t0 = SC.take(T, xs, lo)
  +dd = SC.drop(T, xs, lo)
  +ks = SC.take(T, dd, k)
  +a = SC.take(T, ks, l)
  +b = SC.drop(T, ks, l)
  +y = vget(T, d, dd, k)
  +r = SC.drop(T, dd, 1n+k)
  +pa = SC.append(T, t0, a)
  +hle = N.le_trans(lo, Nat.add(lo, k), SC.length(T, xs), N.le_add_right(lo, k), N.lt_le(Nat.add(lo, k), SC.length(T, xs), hk))
  +lent0 = LL.sc_length_take(T, xs, lo, hle)
  +hkd = lt_cancel(lo, k, SC.length(T, dd), L.subst(Nat, z => {Nat.is_lt(Nat.add(lo, k), z) == True{} : Bool}, SC.length(T, xs), Nat.add(lo, SC.length(T, dd)), Equal.sym(Nat, Nat.add(lo, SC.length(T, dd)), SC.length(T, xs), len_split(T, xs, lo, hle)), hk))
  +lenks = LL.sc_length_take(T, dd, k, N.lt_le(k, SC.length(T, dd), hkd))
  +lena = LL.sc_length_take(T, ks, l, L.subst(Nat, z => {Nat.is_le(l, z) == True{} : Bool}, k, SC.length(T, ks), Equal.sym(Nat, SC.length(T, ks), k, lenks), hl))
  +lenab = Equal.trans(Nat, Nat.add(SC.length(T, a), SC.length(T, b)), SC.length(T, ks), k,
    Equal.trans(Nat, Nat.add(SC.length(T, a), SC.length(T, b)), SC.length(T, SC.append(T, a, b)), SC.length(T, ks), Equal.sym(Nat, SC.length(T, SC.append(T, a, b)), Nat.add(SC.length(T, a), SC.length(T, b)), LL.length_append(T, a, b)),
      Equal.cong(List<&2, T>, Nat, z => SC.length(T, z), SC.append(T, a, b), ks, take_drop_app(T, ks, l))),
    lenks)
  +hxs = Equal.trans(List<&2, T>, xs, SC.append(T, t0, dd), SC.append(T, t0, SC.append(T, a, SC.append(T, b, Con{y, r}))),
    Equal.sym(List<&2, T>, SC.append(T, t0, dd), xs, take_drop_app(T, xs, lo)),
    Equal.cong(List<&2, T>, List<&2, T>, z => SC.append(T, t0, z), dd, SC.append(T, a, SC.append(T, b, Con{y, r})),
      Equal.trans(List<&2, T>, dd, SC.append(T, ks, SC.drop(T, dd, k)), SC.append(T, a, SC.append(T, b, Con{y, r})), Equal.sym(List<&2, T>, SC.append(T, ks, SC.drop(T, dd, k)), dd, take_drop_app(T, dd, k)),
        Equal.trans(List<&2, T>, SC.append(T, ks, SC.drop(T, dd, k)), SC.append(T, SC.append(T, a, b), Con{y, r}), SC.append(T, a, SC.append(T, b, Con{y, r})),
          Equal.trans(List<&2, T>, SC.append(T, ks, SC.drop(T, dd, k)), SC.append(T, ks, Con{y, r}), SC.append(T, SC.append(T, a, b), Con{y, r}),
            Equal.cong(List<&2, T>, List<&2, T>, z => SC.append(T, ks, z), SC.drop(T, dd, k), Con{y, r}, drop_cons_g(T, dd, k, d, hkd)),
            Equal.cong(List<&2, T>, List<&2, T>, z => SC.append(T, z, Con{y, r}), ks, SC.append(T, a, b), Equal.sym(List<&2, T>, SC.append(T, a, b), ks, take_drop_app(T, ks, l)))),
          LL.append_assoc(T, a, b, Con{y, r})))))
  +r1 = SC.append(T, pa, Con{v, SC.append(T, b, r)})
  +zr0 = zr(T, c, f, d, SC.reverse(T, b), pa, y, r, v)
  +zr1 = L.subst(List<&2, T>, z => {SC.update(T, lsr(T, c, f, d, SC.length(T, SC.reverse(T, b)), SC.append(T, pa, SC.append(T, z, Con{y, r})), Nat.add(SC.length(T, pa), SC.length(T, SC.reverse(T, b)))), SC.length(T, pa), v) == SC.append(T, pa, Con{v, SC.append(T, z, r)}) : List<&2, T>}, SC.reverse(T, SC.reverse(T, b)), b, LL.spec_rev_rev(T, b), zr0)
  +xpa = SC.append(T, pa, SC.append(T, b, Con{y, r}))
  +zr2 = L.subst(Nat, n => {SC.update(T, lsr(T, c, f, d, n, xpa, Nat.add(SC.length(T, pa), n)), SC.length(T, pa), v) == r1 : List<&2, T>}, SC.length(T, SC.reverse(T, b)), SC.length(T, b), LL.length_rev(T, b), zr1)
  +elpa = Equal.trans(Nat, SC.length(T, pa), Nat.add(SC.length(T, t0), SC.length(T, a)), Nat.add(lo, l), LL.length_append(T, t0, a),
    Equal.trans(Nat, Nat.add(SC.length(T, t0), SC.length(T, a)), Nat.add(lo, SC.length(T, a)), Nat.add(lo, l),
      Equal.cong(Nat, Nat, z => Nat.add(z, SC.length(T, a)), SC.length(T, t0), lo, lent0),
      Equal.cong(Nat, Nat, z => Nat.add(lo, z), SC.length(T, a), l, lena)))
  +zr3 = L.subst(Nat, n => {SC.update(T, lsr(T, c, f, d, SC.length(T, b), xpa, Nat.add(n, SC.length(T, b))), n, v) == r1 : List<&2, T>}, SC.length(T, pa), Nat.add(lo, l), elpa, zr2)
  +elk = L.subst(Nat, z => {Nat.add(z, SC.length(T, b)) == k : Nat}, SC.length(T, a), l, lena, lenab)
  +eb = Equal.sym(Nat, Nat.sub(k, l), SC.length(T, b), Equal.trans(Nat, Nat.sub(k, l), Nat.sub(Nat.add(l, SC.length(T, b)), l), SC.length(T, b), Equal.cong(Nat, Nat, z => Nat.sub(z, l), k, Nat.add(l, SC.length(T, b)), Equal.sym(Nat, Nat.add(l, SC.length(T, b)), k, elk)), N.add_sub_cancel(l, SC.length(T, b))))
  +zr4 = L.subst(Nat, n => {SC.update(T, lsr(T, c, f, d, n, xpa, Nat.add(Nat.add(lo, l), n)), Nat.add(lo, l), v) == r1 : List<&2, T>}, SC.length(T, b), Nat.sub(k, l), eb, zr3)
  +eix = Equal.trans(Nat, Nat.add(Nat.add(lo, l), Nat.sub(k, l)), Nat.add(lo, Nat.add(l, Nat.sub(k, l))), Nat.add(lo, k), N.add_assoc(lo, l, Nat.sub(k, l)), Equal.cong(Nat, Nat, z => Nat.add(lo, z), Nat.add(l, Nat.sub(k, l)), k, N.sub_add(k, l, hl)))
  +zr5 = L.subst(Nat, n => {SC.update(T, lsr(T, c, f, d, Nat.sub(k, l), xpa, n), Nat.add(lo, l), v) == r1 : List<&2, T>}, Nat.add(Nat.add(lo, l), Nat.sub(k, l)), Nat.add(lo, k), eix, zr4)
  +ex = Equal.trans(List<&2, T>, xpa, SC.append(T, t0, SC.append(T, a, SC.append(T, b, Con{y, r}))), xs, LL.append_assoc(T, t0, a, SC.append(T, b, Con{y, r})), Equal.sym(List<&2, T>, xs, SC.append(T, t0, SC.append(T, a, SC.append(T, b, Con{y, r}))), hxs))
  +zr6 = L.subst(List<&2, T>, z => {SC.update(T, lsr(T, c, f, d, Nat.sub(k, l), z, Nat.add(lo, k)), Nat.add(lo, l), v) == r1 : List<&2, T>}, xpa, xs, ex, zr5)
  +r2 = SC.append(T, t0, SC.append(T, a, Con{v, SC.append(T, b, r)}))
  +lhs = SC.update(T, lsr(T, c, f, d, Nat.sub(k, l), xs, Nat.add(lo, k)), Nat.add(lo, l), v)
  +e12 = Equal.trans(List<&2, T>, lhs, r1, r2, zr6, LL.append_assoc(T, t0, a, Con{v, SC.append(T, b, r)}))
  +w1 = L.subst(Nat, n => {SC.take(T, SC.drop(T, r2, n), 1n+Nat.add(SC.length(T, a), SC.length(T, b))) == SC.append(T, a, Con{v, b}) : List<&2, T>}, SC.length(T, t0), lo, lent0, wt(T, t0, a, v, b, r))
  +w2 = L.subst(Nat, n => {SC.take(T, SC.drop(T, r2, lo), 1n+n) == SC.append(T, a, Con{v, b}) : List<&2, T>}, Nat.add(SC.length(T, a), SC.length(T, b)), k, lenab, w1)
  L.subst(List<&2, T>, z => {SC.take(T, SC.drop(T, z, lo), 1n+k) == SC.append(T, a, Con{v, b}) : List<&2, T>}, r2, lhs, Equal.sym(List<&2, T>, lhs, r2, e12), w2)

# ---- updates outside a window ----

def upd_oob(-T: Data, +ys: List<&2, T>, +i: Nat, +x: T, +h: {Nat.is_le(SC.length(T, ys), i) == True{} : Bool}) -> {SC.update(T, ys, i, x) == ys : List<&2, T>}:
  match ys i:
    case Nil{} i0:
      {==}
    case Con{+hh, +t} 0n:
      Empty.absurd({SC.update(T, Con{hh, t}, 0n, x) == Con{hh, t} : List<&2, T>}, L.false_true(h))
    case Con{+hh, +t} 1n+p:
      LL.cons_cong(T, hh, SC.update(T, t, p, x), t, upd_oob(T, t, p, x, h))

def len_take_le(-T: Data, +xs: List<&2, T>, +n: Nat) -> {Nat.is_le(SC.length(T, SC.take(T, xs, n)), n) == True{} : Bool}:
  match xs n:
    case Nil{} n0:
      N.le_add_right(0n, n0)
    case Con{+hh, +t} 0n:
      {==}
    case Con{+hh, +t} 1n+p:
      len_take_le(T, t, p)

def take_upd_ge(-T: Data, +xs: List<&2, T>, +i: Nat, +x: T, +n: Nat, +h: {Nat.is_le(n, i) == True{} : Bool}) -> {SC.take(T, SC.update(T, xs, i, x), n) == SC.take(T, xs, n) : List<&2, T>}:
  Equal.trans(List<&2, T>, SC.take(T, SC.update(T, xs, i, x), n), SC.update(T, SC.take(T, xs, n), i, x), SC.take(T, xs, n),
    LL.sc_take_update(T, xs, i, x, n),
    upd_oob(T, SC.take(T, xs, n), i, x, N.le_trans(SC.length(T, SC.take(T, xs, n)), n, i, len_take_le(T, xs, n), h)))

def drop_upd(-T: Data, +xs: List<&2, T>, +lo: Nat, +j: Nat, +x: T) -> {SC.drop(T, SC.update(T, xs, Nat.add(lo, j), x), lo) == SC.update(T, SC.drop(T, xs, lo), j, x) : List<&2, T>}:
  match xs lo:
    case Nil{} l0:
      {==}
    case Con{+hh, +t} 0n:
      drop0(T, SC.update(T, Con{hh, t}, j, x))
    case Con{+hh, +t} 1n+p:
      drop_upd(T, t, p, j, x)

def win_upd_ge(-T: Data, +xs: List<&2, T>, +lo: Nat, +j: Nat, +x: T, +k: Nat, +h: {Nat.is_le(k, j) == True{} : Bool}) -> {SC.take(T, SC.drop(T, SC.update(T, xs, Nat.add(lo, j), x), lo), k) == SC.take(T, SC.drop(T, xs, lo), k) : List<&2, T>}:
  Equal.trans(List<&2, T>, SC.take(T, SC.drop(T, SC.update(T, xs, Nat.add(lo, j), x), lo), k), SC.take(T, SC.update(T, SC.drop(T, xs, lo), j, x), k), SC.take(T, SC.drop(T, xs, lo), k),
    Equal.cong(List<&2, T>, List<&2, T>, z => SC.take(T, z, k), SC.drop(T, SC.update(T, xs, Nat.add(lo, j), x), lo), SC.update(T, SC.drop(T, xs, lo), j, x), drop_upd(T, xs, lo, j, x)),
    take_upd_ge(T, SC.drop(T, xs, lo), j, x, k, h))

def DulIH(-T: Data, +t: List<&2, T>, +x: T, +p: Nat) -> Type:
  @+q: Nat -> @+hq: {Nat.is_lt(q, p) == True{} : Bool} -> {SC.drop(T, SC.update(T, t, q, x), p) == SC.drop(T, t, p) : List<&2, T>}

def drop_upd_lt_c(-T: Data, +hh: T, +t: List<&2, T>, +p: Nat, +i: Nat, +x: T, +h: {Nat.is_lt(i, 1n+p) == True{} : Bool}, ih: DulIH(T, t, x, p)) -> {SC.drop(T, SC.update(T, Con{hh, t}, i, x), 1n+p) == SC.drop(T, Con{hh, t}, 1n+p) : List<&2, T>}:
  match i:
    case 0n:
      {==}
    case 1n+q:
      ih(q, h)

def drop_upd_lt(-T: Data, +xs: List<&2, T>, +i: Nat, +x: T, +n: Nat, +h: {Nat.is_lt(i, n) == True{} : Bool}) -> {SC.drop(T, SC.update(T, xs, i, x), n) == SC.drop(T, xs, n) : List<&2, T>}:
  match xs n:
    case Nil{} n0:
      {==}
    case Con{+hh, +t} 0n:
      Empty.absurd({SC.drop(T, SC.update(T, Con{hh, t}, i, x), 0n) == SC.drop(T, Con{hh, t}, 0n) : List<&2, T>}, L.false_true(Equal.trans(Bool, False{}, Nat.is_lt(i, 0n), True{}, Equal.sym(Bool, Nat.is_lt(i, 0n), False{}, N.not_lt_zero(i)), h)))
    case Con{+hh, +t} 1n+p:
      drop_upd_lt_c(T, hh, t, p, i, x, h, q => hq => drop_upd_lt(T, t, q, x, p, hq))

def drop_app_len1(-T: Data, +p: List<&2, T>, +y: T, +w: List<&2, T>) -> {SC.drop(T, SC.append(T, p, Con{y, w}), 1n+SC.length(T, p)) == w : List<&2, T>}:
  match p:
    case Nil{}:
      drop0(T, w)
    case Con{+hh, +t}:
      drop_app_len1(T, t, y, w)

# ---- the window after a deletion by shifting ----

# The window [lo, lo + 1 + k1) split around position l.
def dsplit(-T: Data, +d: T, +xs: List<&2, T>, +lo: Nat, +k1: Nat, +l: Nat, +hl: {Nat.is_le(l, k1) == True{} : Bool}, +hk: {Nat.is_le(Nat.add(lo, 1n+k1), SC.length(T, xs)) == True{} : Bool}) -> {xs == SC.append(T, SC.take(T, xs, lo), SC.append(T, SC.take(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), l), Con{vget(T, d, SC.take(T, SC.drop(T, xs, lo), 1n+k1), l), SC.append(T, SC.drop(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), 1n+l), SC.drop(T, SC.drop(T, xs, lo), 1n+k1))})) : List<&2, T>}:
  +t0 = SC.take(T, xs, lo)
  +dd = SC.drop(T, xs, lo)
  +ks = SC.take(T, dd, 1n+k1)
  +e = SC.drop(T, dd, 1n+k1)
  +a = SC.take(T, ks, l)
  +b = SC.drop(T, ks, 1n+l)
  +y = vget(T, d, ks, l)
  +hle = N.le_trans(lo, Nat.add(lo, 1n+k1), SC.length(T, xs), N.le_add_right(lo, 1n+k1), hk)
  +hkd = le_cancel(lo, 1n+k1, SC.length(T, dd), L.subst(Nat, z => {Nat.is_le(Nat.add(lo, 1n+k1), z) == True{} : Bool}, SC.length(T, xs), Nat.add(lo, SC.length(T, dd)), Equal.sym(Nat, Nat.add(lo, SC.length(T, dd)), SC.length(T, xs), len_split(T, xs, lo, hle)), hk))
  +lenks = LL.sc_length_take(T, dd, 1n+k1, hkd)
  +hl1 = L.subst(Nat, z => {Nat.is_lt(l, z) == True{} : Bool}, 1n+k1, SC.length(T, ks), Equal.sym(Nat, SC.length(T, ks), 1n+k1, lenks), N.le_lt_trans(l, k1, 1n+k1, hl, N.lt_succ(k1)))
  Equal.trans(List<&2, T>, xs, SC.append(T, t0, dd), SC.append(T, t0, SC.append(T, a, Con{y, SC.append(T, b, e)})),
    Equal.sym(List<&2, T>, SC.append(T, t0, dd), xs, take_drop_app(T, xs, lo)),
    Equal.cong(List<&2, T>, List<&2, T>, z => SC.append(T, t0, z), dd, SC.append(T, a, Con{y, SC.append(T, b, e)}),
      Equal.trans(List<&2, T>, dd, SC.append(T, ks, e), SC.append(T, a, Con{y, SC.append(T, b, e)}),
        Equal.sym(List<&2, T>, SC.append(T, ks, e), dd, take_drop_app(T, dd, 1n+k1)),
        Equal.trans(List<&2, T>, SC.append(T, ks, e), SC.append(T, SC.append(T, a, Con{y, b}), e), SC.append(T, a, Con{y, SC.append(T, b, e)}),
          Equal.cong(List<&2, T>, List<&2, T>, z => SC.append(T, z, e), ks, SC.append(T, a, Con{y, b}),
            Equal.trans(List<&2, T>, ks, SC.append(T, a, SC.drop(T, ks, l)), SC.append(T, a, Con{y, b}),
              Equal.sym(List<&2, T>, SC.append(T, a, SC.drop(T, ks, l)), ks, take_drop_app(T, ks, l)),
              Equal.cong(List<&2, T>, List<&2, T>, z => SC.append(T, a, z), SC.drop(T, ks, l), Con{y, b}, drop_cons_g(T, ks, l, d, hl1)))),
          LL.append_assoc(T, a, Con{y, b}, e)))))

def dlens(-T: Data, +d: T, +xs: List<&2, T>, +lo: Nat, +k1: Nat, +l: Nat, +hl: {Nat.is_le(l, k1) == True{} : Bool}, +hk: {Nat.is_le(Nat.add(lo, 1n+k1), SC.length(T, xs)) == True{} : Bool}) -> {Nat.add(SC.length(T, SC.take(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), l)), SC.length(T, SC.drop(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), 1n+l))) == k1 : Nat}:
  +dd = SC.drop(T, xs, lo)
  +ks = SC.take(T, dd, 1n+k1)
  +a = SC.take(T, ks, l)
  +b = SC.drop(T, ks, 1n+l)
  +y = vget(T, d, ks, l)
  +hle = N.le_trans(lo, Nat.add(lo, 1n+k1), SC.length(T, xs), N.le_add_right(lo, 1n+k1), hk)
  +hkd = le_cancel(lo, 1n+k1, SC.length(T, dd), L.subst(Nat, z => {Nat.is_le(Nat.add(lo, 1n+k1), z) == True{} : Bool}, SC.length(T, xs), Nat.add(lo, SC.length(T, dd)), Equal.sym(Nat, Nat.add(lo, SC.length(T, dd)), SC.length(T, xs), len_split(T, xs, lo, hle)), hk))
  +lenks = LL.sc_length_take(T, dd, 1n+k1, hkd)
  +hl1 = L.subst(Nat, z => {Nat.is_lt(l, z) == True{} : Bool}, 1n+k1, SC.length(T, ks), Equal.sym(Nat, SC.length(T, ks), 1n+k1, lenks), N.le_lt_trans(l, k1, 1n+k1, hl, N.lt_succ(k1)))
  +eks = Equal.trans(List<&2, T>, ks, SC.append(T, a, SC.drop(T, ks, l)), SC.append(T, a, Con{y, b}), Equal.sym(List<&2, T>, SC.append(T, a, SC.drop(T, ks, l)), ks, take_drop_app(T, ks, l)), Equal.cong(List<&2, T>, List<&2, T>, z => SC.append(T, a, z), SC.drop(T, ks, l), Con{y, b}, drop_cons_g(T, ks, l, d, hl1)))
  +e1 = Equal.trans(Nat, 1n+Nat.add(SC.length(T, a), SC.length(T, b)), Nat.add(SC.length(T, a), 1n+SC.length(T, b)), 1n+k1,
    Equal.sym(Nat, Nat.add(SC.length(T, a), 1n+SC.length(T, b)), 1n+Nat.add(SC.length(T, a), SC.length(T, b)), N.add_succ(SC.length(T, a), SC.length(T, b))),
    Equal.trans(Nat, Nat.add(SC.length(T, a), 1n+SC.length(T, b)), SC.length(T, ks), 1n+k1,
      Equal.trans(Nat, Nat.add(SC.length(T, a), 1n+SC.length(T, b)), SC.length(T, SC.append(T, a, Con{y, b})), SC.length(T, ks), Equal.sym(Nat, SC.length(T, SC.append(T, a, Con{y, b})), Nat.add(SC.length(T, a), 1n+SC.length(T, b)), LL.length_append(T, a, Con{y, b})), Equal.cong(List<&2, T>, Nat, z => SC.length(T, z), SC.append(T, a, Con{y, b}), ks, Equal.sym(List<&2, T>, ks, SC.append(T, a, Con{y, b}), eks))),
      lenks))
  Equal.cong(Nat, Nat, z => N.pred(z), 1n+Nat.add(SC.length(T, a), SC.length(T, b)), 1n+k1, e1)

def dlena(-T: Data, +xs: List<&2, T>, +lo: Nat, +k1: Nat, +l: Nat, +hl: {Nat.is_le(l, k1) == True{} : Bool}, +hk: {Nat.is_le(Nat.add(lo, 1n+k1), SC.length(T, xs)) == True{} : Bool}) -> {SC.length(T, SC.take(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), l)) == l : Nat}:
  +dd = SC.drop(T, xs, lo)
  +hle = N.le_trans(lo, Nat.add(lo, 1n+k1), SC.length(T, xs), N.le_add_right(lo, 1n+k1), hk)
  +hkd = le_cancel(lo, 1n+k1, SC.length(T, dd), L.subst(Nat, z => {Nat.is_le(Nat.add(lo, 1n+k1), z) == True{} : Bool}, SC.length(T, xs), Nat.add(lo, SC.length(T, dd)), Equal.sym(Nat, Nat.add(lo, SC.length(T, dd)), SC.length(T, xs), len_split(T, xs, lo, hle)), hk))
  +lenks = LL.sc_length_take(T, dd, 1n+k1, hkd)
  LL.sc_length_take(T, SC.take(T, dd, 1n+k1), l, L.subst(Nat, z => {Nat.is_le(l, z) == True{} : Bool}, 1n+k1, SC.length(T, SC.take(T, dd, 1n+k1)), Equal.sym(Nat, SC.length(T, SC.take(T, dd, 1n+k1)), 1n+k1, lenks), N.le_trans(l, k1, 1n+k1, hl, N.le_succ(k1))))

# Head removal: shift the l entries before position l one slot right; the
# window then starts one later.
def del_right_win(-T: Data, +c: Bool, +f: T, +d: T, +xs: List<&2, T>, +lo: Nat, +k1: Nat, +l: Nat, +hl: {Nat.is_le(l, k1) == True{} : Bool}, +hk: {Nat.is_le(Nat.add(lo, 1n+k1), SC.length(T, xs)) == True{} : Bool}) -> {SC.take(T, SC.drop(T, lsr(T, c, f, d, l, xs, Nat.add(lo, l)), 1n+lo), k1) == SC.append(T, SC.take(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), l), SC.drop(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), 1n+l)) : List<&2, T>}:
  +t0 = SC.take(T, xs, lo)
  +y = vget(T, d, SC.take(T, SC.drop(T, xs, lo), 1n+k1), l)
  +e = SC.drop(T, SC.drop(T, xs, lo), 1n+k1)
  +r = SC.append(T, SC.drop(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), 1n+l), e)
  +hle = N.le_trans(lo, Nat.add(lo, 1n+k1), SC.length(T, xs), N.le_add_right(lo, 1n+k1), hk)
  +lent0 = LL.sc_length_take(T, xs, lo, hle)
  +lena = dlena(T, xs, lo, k1, l, hl, hk)
  +x0 = SC.append(T, t0, SC.append(T, SC.take(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), l), Con{y, r}))
  +r0 = SC.append(T, t0, Con{y, SC.append(T, SC.take(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), l), r)})
  +zr0 = zr(T, c, f, d, SC.reverse(T, SC.take(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), l)), t0, y, r, y)
  +zr1 = L.subst(List<&2, T>, z => {SC.update(T, lsr(T, c, f, d, SC.length(T, SC.reverse(T, SC.take(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), l))), SC.append(T, t0, SC.append(T, z, Con{y, r})), Nat.add(SC.length(T, t0), SC.length(T, SC.reverse(T, SC.take(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), l))))), SC.length(T, t0), y) == SC.append(T, t0, Con{y, SC.append(T, z, r)}) : List<&2, T>}, SC.reverse(T, SC.reverse(T, SC.take(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), l))), SC.take(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), l), LL.spec_rev_rev(T, SC.take(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), l)), zr0)
  +zr2 = L.subst(Nat, n => {SC.update(T, lsr(T, c, f, d, n, x0, Nat.add(SC.length(T, t0), n)), SC.length(T, t0), y) == r0 : List<&2, T>}, SC.length(T, SC.reverse(T, SC.take(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), l))), SC.length(T, SC.take(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), l)), LL.length_rev(T, SC.take(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), l)), zr1)
  +zr3 = L.subst(Nat, n => {SC.update(T, lsr(T, c, f, d, n, x0, Nat.add(SC.length(T, t0), n)), SC.length(T, t0), y) == r0 : List<&2, T>}, SC.length(T, SC.take(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), l)), l, lena, zr2)
  +zr4 = L.subst(Nat, m => {SC.update(T, lsr(T, c, f, d, l, x0, Nat.add(m, l)), m, y) == r0 : List<&2, T>}, SC.length(T, t0), lo, lent0, zr3)
  +zr5 = L.subst(List<&2, T>, z => {SC.update(T, lsr(T, c, f, d, l, z, Nat.add(lo, l)), lo, y) == r0 : List<&2, T>}, x0, xs, Equal.sym(List<&2, T>, xs, x0, dsplit(T, d, xs, lo, k1, l, hl, hk)), zr4)
  +xx = lsr(T, c, f, d, l, xs, Nat.add(lo, l))
  +ed = Equal.trans(List<&2, T>, SC.drop(T, xx, 1n+lo), SC.drop(T, SC.update(T, xx, lo, y), 1n+lo), SC.drop(T, r0, 1n+lo),
    Equal.sym(List<&2, T>, SC.drop(T, SC.update(T, xx, lo, y), 1n+lo), SC.drop(T, xx, 1n+lo), drop_upd_lt(T, xx, lo, y, 1n+lo, N.lt_succ(lo))),
    Equal.cong(List<&2, T>, List<&2, T>, z => SC.drop(T, z, 1n+lo), SC.update(T, xx, lo, y), r0, zr5))
  +ew = L.subst(Nat, m => {SC.drop(T, r0, 1n+m) == SC.append(T, SC.take(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), l), r) : List<&2, T>}, SC.length(T, t0), lo, lent0, drop_app_len1(T, t0, y, SC.append(T, SC.take(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), l), r)))
  +et = Equal.trans(List<&2, T>, SC.take(T, SC.append(T, SC.take(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), l), r), k1), SC.take(T, SC.append(T, SC.take(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), l), r), Nat.add(SC.length(T, SC.take(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), l)), SC.length(T, SC.drop(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), 1n+l)))), SC.append(T, SC.take(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), l), SC.drop(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), 1n+l)),
    Equal.cong(Nat, List<&2, T>, n => SC.take(T, SC.append(T, SC.take(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), l), r), n), k1, Nat.add(SC.length(T, SC.take(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), l)), SC.length(T, SC.drop(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), 1n+l))), Equal.sym(Nat, Nat.add(SC.length(T, SC.take(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), l)), SC.length(T, SC.drop(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), 1n+l))), k1, dlens(T, d, xs, lo, k1, l, hl, hk))),
    Equal.trans(List<&2, T>, SC.take(T, SC.append(T, SC.take(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), l), r), Nat.add(SC.length(T, SC.take(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), l)), SC.length(T, SC.drop(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), 1n+l)))), SC.append(T, SC.take(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), l), SC.take(T, r, SC.length(T, SC.drop(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), 1n+l)))), SC.append(T, SC.take(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), l), SC.drop(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), 1n+l)),
      take_app_len(T, SC.take(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), l), r, SC.length(T, SC.drop(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), 1n+l))),
      Equal.cong(List<&2, T>, List<&2, T>, z => SC.append(T, SC.take(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), l), z), SC.take(T, r, SC.length(T, SC.drop(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), 1n+l))), SC.drop(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), 1n+l), take_app_exact(T, SC.drop(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), 1n+l), e))))
  Equal.trans(List<&2, T>, SC.take(T, SC.drop(T, xx, 1n+lo), k1), SC.take(T, SC.append(T, SC.take(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), l), r), k1), SC.append(T, SC.take(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), l), SC.drop(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), 1n+l)),
    Equal.cong(List<&2, T>, List<&2, T>, z => SC.take(T, z, k1), SC.drop(T, xx, 1n+lo), SC.append(T, SC.take(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), l), r), Equal.trans(List<&2, T>, SC.drop(T, xx, 1n+lo), SC.drop(T, r0, 1n+lo), SC.append(T, SC.take(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), l), r), ed, ew)),
    et)

# Tail removal: shift the k1 - l entries after position l one slot left; the
# window then ends one earlier.
def del_left_win(-T: Data, +c: Bool, +f: T, +d: T, +xs: List<&2, T>, +lo: Nat, +k1: Nat, +l: Nat, +hl: {Nat.is_le(l, k1) == True{} : Bool}, +hk: {Nat.is_le(Nat.add(lo, 1n+k1), SC.length(T, xs)) == True{} : Bool}) -> {SC.take(T, SC.drop(T, lsl(T, c, f, d, Nat.sub(k1, l), xs, Nat.add(lo, l)), lo), k1) == SC.append(T, SC.take(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), l), SC.drop(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), 1n+l)) : List<&2, T>}:
  +t0 = SC.take(T, xs, lo)
  +p = SC.append(T, t0, SC.take(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), l))
  +y = vget(T, d, SC.take(T, SC.drop(T, xs, lo), 1n+k1), l)
  +e = SC.drop(T, SC.drop(T, xs, lo), 1n+k1)
  +hle = N.le_trans(lo, Nat.add(lo, 1n+k1), SC.length(T, xs), N.le_add_right(lo, 1n+k1), hk)
  +lent0 = LL.sc_length_take(T, xs, lo, hle)
  +lena = dlena(T, xs, lo, k1, l, hl, hk)
  +lab = dlens(T, d, xs, lo, k1, l, hl, hk)
  +elk = L.subst(Nat, z => {Nat.add(z, SC.length(T, SC.drop(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), 1n+l))) == k1 : Nat}, SC.length(T, SC.take(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), l)), l, lena, lab)
  +lenb = Equal.sym(Nat, Nat.sub(k1, l), SC.length(T, SC.drop(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), 1n+l)), Equal.trans(Nat, Nat.sub(k1, l), Nat.sub(Nat.add(l, SC.length(T, SC.drop(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), 1n+l))), l), SC.length(T, SC.drop(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), 1n+l)), Equal.cong(Nat, Nat, z => Nat.sub(z, l), k1, Nat.add(l, SC.length(T, SC.drop(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), 1n+l))), Equal.sym(Nat, Nat.add(l, SC.length(T, SC.drop(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), 1n+l))), k1, elk)), N.add_sub_cancel(l, SC.length(T, SC.drop(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), 1n+l)))))
  +lenp = Equal.trans(Nat, SC.length(T, p), Nat.add(SC.length(T, t0), SC.length(T, SC.take(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), l))), Nat.add(lo, l), LL.length_append(T, t0, SC.take(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), l)),
    Equal.trans(Nat, Nat.add(SC.length(T, t0), SC.length(T, SC.take(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), l))), Nat.add(lo, SC.length(T, SC.take(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), l))), Nat.add(lo, l), Equal.cong(Nat, Nat, z => Nat.add(z, SC.length(T, SC.take(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), l))), SC.length(T, t0), lo, lent0), Equal.cong(Nat, Nat, z => Nat.add(lo, z), SC.length(T, SC.take(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), l)), l, lena)))
  +x0 = SC.append(T, p, Con{y, SC.append(T, SC.drop(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), 1n+l), e)})
  +yy = SC.append(T, p, SC.append(T, SC.drop(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), 1n+l), Con{y, e}))
  +ex0 = Equal.trans(List<&2, T>, xs, SC.append(T, t0, SC.append(T, SC.take(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), l), Con{y, SC.append(T, SC.drop(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), 1n+l), e)})), x0, dsplit(T, d, xs, lo, k1, l, hl, hk), Equal.sym(List<&2, T>, x0, SC.append(T, t0, SC.append(T, SC.take(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), l), Con{y, SC.append(T, SC.drop(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), 1n+l), e)})), LL.append_assoc(T, t0, SC.take(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), l), Con{y, SC.append(T, SC.drop(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), 1n+l), e)})))
  +zl1 = L.subst(Nat, n => {SC.update(T, lsl(T, c, f, d, n, x0, SC.length(T, p)), Nat.add(SC.length(T, p), n), y) == yy : List<&2, T>}, SC.length(T, SC.drop(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), 1n+l)), Nat.sub(k1, l), lenb, zl(T, c, f, d, SC.drop(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), 1n+l), p, y, e, y))
  +zl2 = L.subst(Nat, m => {SC.update(T, lsl(T, c, f, d, Nat.sub(k1, l), x0, m), Nat.add(m, Nat.sub(k1, l)), y) == yy : List<&2, T>}, SC.length(T, p), Nat.add(lo, l), lenp, zl1)
  +zl3 = L.subst(List<&2, T>, z => {SC.update(T, lsl(T, c, f, d, Nat.sub(k1, l), z, Nat.add(lo, l)), Nat.add(Nat.add(lo, l), Nat.sub(k1, l)), y) == yy : List<&2, T>}, x0, xs, Equal.sym(List<&2, T>, xs, x0, ex0), zl2)
  +eix = Equal.trans(Nat, Nat.add(Nat.add(lo, l), Nat.sub(k1, l)), Nat.add(lo, Nat.add(l, Nat.sub(k1, l))), Nat.add(lo, k1), N.add_assoc(lo, l, Nat.sub(k1, l)), Equal.cong(Nat, Nat, z => Nat.add(lo, z), Nat.add(l, Nat.sub(k1, l)), k1, N.sub_add(k1, l, hl)))
  +zl4 = L.subst(Nat, n => {SC.update(T, lsl(T, c, f, d, Nat.sub(k1, l), xs, Nat.add(lo, l)), n, y) == yy : List<&2, T>}, Nat.add(Nat.add(lo, l), Nat.sub(k1, l)), Nat.add(lo, k1), eix, zl3)
  +xx = lsl(T, c, f, d, Nat.sub(k1, l), xs, Nat.add(lo, l))
  +w0 = SC.append(T, SC.take(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), l), SC.append(T, SC.drop(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), 1n+l), Con{y, e}))
  +ew = Equal.trans(List<&2, T>, SC.drop(T, yy, lo), SC.drop(T, SC.append(T, t0, w0), lo), w0,
    Equal.cong(List<&2, T>, List<&2, T>, z => SC.drop(T, z, lo), yy, SC.append(T, t0, w0), LL.append_assoc(T, t0, SC.take(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), l), SC.append(T, SC.drop(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), 1n+l), Con{y, e}))),
    L.subst(Nat, m => {SC.drop(T, SC.append(T, t0, w0), m) == w0 : List<&2, T>}, SC.length(T, t0), lo, lent0, drop_app_len(T, t0, w0)))
  +et = Equal.trans(List<&2, T>, SC.take(T, w0, k1), SC.take(T, w0, Nat.add(SC.length(T, SC.take(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), l)), SC.length(T, SC.drop(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), 1n+l)))), SC.append(T, SC.take(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), l), SC.drop(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), 1n+l)),
    Equal.cong(Nat, List<&2, T>, n => SC.take(T, w0, n), k1, Nat.add(SC.length(T, SC.take(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), l)), SC.length(T, SC.drop(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), 1n+l))), Equal.sym(Nat, Nat.add(SC.length(T, SC.take(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), l)), SC.length(T, SC.drop(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), 1n+l))), k1, lab)),
    Equal.trans(List<&2, T>, SC.take(T, w0, Nat.add(SC.length(T, SC.take(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), l)), SC.length(T, SC.drop(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), 1n+l)))), SC.append(T, SC.take(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), l), SC.take(T, SC.append(T, SC.drop(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), 1n+l), Con{y, e}), SC.length(T, SC.drop(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), 1n+l)))), SC.append(T, SC.take(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), l), SC.drop(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), 1n+l)),
      take_app_len(T, SC.take(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), l), SC.append(T, SC.drop(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), 1n+l), Con{y, e}), SC.length(T, SC.drop(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), 1n+l))),
      Equal.cong(List<&2, T>, List<&2, T>, z => SC.append(T, SC.take(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), l), z), SC.take(T, SC.append(T, SC.drop(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), 1n+l), Con{y, e}), SC.length(T, SC.drop(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), 1n+l))), SC.drop(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), 1n+l), take_app_exact(T, SC.drop(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), 1n+l), Con{y, e}))))
  Equal.trans(List<&2, T>, SC.take(T, SC.drop(T, xx, lo), k1), SC.take(T, SC.drop(T, SC.update(T, xx, Nat.add(lo, k1), y), lo), k1), SC.append(T, SC.take(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), l), SC.drop(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), 1n+l)),
    Equal.sym(List<&2, T>, SC.take(T, SC.drop(T, SC.update(T, xx, Nat.add(lo, k1), y), lo), k1), SC.take(T, SC.drop(T, xx, lo), k1), win_upd_ge(T, xx, lo, k1, y, k1, N.le_refl(k1))),
    Equal.trans(List<&2, T>, SC.take(T, SC.drop(T, SC.update(T, xx, Nat.add(lo, k1), y), lo), k1), SC.take(T, SC.drop(T, yy, lo), k1), SC.append(T, SC.take(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), l), SC.drop(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), 1n+l)),
      Equal.cong(List<&2, T>, List<&2, T>, z => SC.take(T, SC.drop(T, z, lo), k1), SC.update(T, xx, Nat.add(lo, k1), y), yy, zl4),
      Equal.trans(List<&2, T>, SC.take(T, SC.drop(T, yy, lo), k1), SC.take(T, w0, k1), SC.append(T, SC.take(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), l), SC.drop(T, SC.take(T, SC.drop(T, xs, lo), 1n+k1), 1n+l)),
        Equal.cong(List<&2, T>, List<&2, T>, z => SC.take(T, z, k1), SC.drop(T, yy, lo), w0, ew),
        et)))
