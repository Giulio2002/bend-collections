import Base
import ../../../src/math/u64.bend as W
import ../../../src/math/w64.bend as X
import ../../../src/math/random/rand.bend as R
import ../../../spec/math/random/rand.bend as SR
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../../lib/u32alg.bend as A

# Fisher-Yates on a list (src/math/random/rand.bend shuffle_list, the path of
# shuffle for 2^31 elements or more) returns a permutation of its input, for
# every source and every draw (the indices j need not be in range: an
# out-of-range swap is the identity):
# every swap keeps the number of elements related to any v (the multiset,
# for an equality), as in the Coq/Isabelle proofs that Fisher-Yates permutes.

def occ(~A: Data, ~V: Data, ~rel: A -> V -> Bool, +v: V, +xs: List<&2, A>) -> Nat:
  SR.occurrences(~A, ~V, ~rel, v, xs)

def some_or(-A: Data, m: Maybe<&2, A>, +d: A) -> A:
  match m:
    case None{}:
      d
    case Some{x}:
      x

def is_some(-A: Data, m: Maybe<&2, A>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{x}:
      True{}

def none_some(-A: Data, +y: A, e: {None{} == Some{y} : Maybe<&2, A>}) -> Empty:
  %Equal.sym(Maybe<&2, A>, None{}, Some{y}, e) : L.truth(is_some(A, _))
  Unit{}

def some_inj(-A: Data, +x: A, +y: A, e: {Some{x} == Some{y} : Maybe<&2, A>}) -> {x == y : A}:
  Equal.cong(Maybe<&2, A>, A, m => some_or(A, m, x), Some{x}, Some{y}, e)

# (a + c) + b == (b + c) + a
def swap_ends(+a: Nat, +b: Nat, +c: Nat) -> {Nat.add(Nat.add(a, c), b) == Nat.add(Nat.add(b, c), a) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.add(a, c), b), Nat.add(a, Nat.add(c, b)), Nat.add(Nat.add(b, c), a),
    N.add_assoc(a, c, b),
    Equal.trans(Nat, Nat.add(a, Nat.add(c, b)), Nat.add(a, Nat.add(b, c)), Nat.add(Nat.add(b, c), a),
      Equal.cong(Nat, Nat, t => Nat.add(a, t), Nat.add(c, b), Nat.add(b, c), N.add_comm(c, b)),
      N.add_comm(a, Nat.add(b, c))))

# (h + x) + y == h + (x + y), stated for the step of put_occ
def assoc3(+h: Nat, +x: Nat, +y: Nat, +z: Nat, +e: {Nat.add(x, y) == z : Nat}) -> {Nat.add(Nat.add(h, x), y) == Nat.add(h, z) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.add(h, x), y), Nat.add(h, Nat.add(x, y)), Nat.add(h, z), N.add_assoc(h, x, y),
    Equal.cong(Nat, Nat, t => Nat.add(h, t), Nat.add(x, y), z, e))

# writing x over the element y at i: occ + [y] == old occ + [x]
def put_occ(~A: Data, ~V: Data, ~rel: A -> V -> Bool, +v: V, +xs: List<&2, A>, +i: Nat, +x: A, +y: A, +h: {R.nth(A, xs, i) == Some{y} : Maybe<&2, A>}) -> {Nat.add(occ(~A, ~V, ~rel, v, R.put(A, xs, i, x)), SR.b2n(rel(y, v))) == Nat.add(occ(~A, ~V, ~rel, v, xs), SR.b2n(rel(x, v))) : Nat}:
  match xs i:
    case Nil{} _:
      Empty.absurd({Nat.add(0n, SR.b2n(rel(y, v))) == Nat.add(0n, SR.b2n(rel(x, v))) : Nat}, none_some(A, y, h))
    case Con{+hd, +t} 0n:
      %some_inj(A, hd, y, h) : {Nat.add(Nat.add(SR.b2n(rel(x, v)), occ(~A, ~V, ~rel, v, t)), SR.b2n(rel(_, v))) == Nat.add(Nat.add(SR.b2n(rel(hd, v)), occ(~A, ~V, ~rel, v, t)), SR.b2n(rel(x, v))) : Nat}
      swap_ends(SR.b2n(rel(x, v)), SR.b2n(rel(hd, v)), occ(~A, ~V, ~rel, v, t))
    case Con{+hd, +t} 1n+p:
      Equal.trans(Nat, Nat.add(Nat.add(SR.b2n(rel(hd, v)), occ(~A, ~V, ~rel, v, R.put(A, t, p, x))), SR.b2n(rel(y, v))), Nat.add(SR.b2n(rel(hd, v)), Nat.add(occ(~A, ~V, ~rel, v, t), SR.b2n(rel(x, v)))), Nat.add(Nat.add(SR.b2n(rel(hd, v)), occ(~A, ~V, ~rel, v, t)), SR.b2n(rel(x, v))),
        assoc3(SR.b2n(rel(hd, v)), occ(~A, ~V, ~rel, v, R.put(A, t, p, x)), SR.b2n(rel(y, v)), Nat.add(occ(~A, ~V, ~rel, v, t), SR.b2n(rel(x, v))), put_occ(~A, ~V, ~rel, v, t, p, x, y, h)),
        Equal.sym(Nat, Nat.add(Nat.add(SR.b2n(rel(hd, v)), occ(~A, ~V, ~rel, v, t)), SR.b2n(rel(x, v))), Nat.add(SR.b2n(rel(hd, v)), Nat.add(occ(~A, ~V, ~rel, v, t), SR.b2n(rel(x, v)))), N.add_assoc(SR.b2n(rel(hd, v)), occ(~A, ~V, ~rel, v, t), SR.b2n(rel(x, v)))))

# writing y at i keeps an element y at j
def nth_put(-A: Data, +xs: List<&2, A>, +i: Nat, +j: Nat, +y: A, +h: {R.nth(A, xs, j) == Some{y} : Maybe<&2, A>}) -> {R.nth(A, R.put(A, xs, i, y), j) == Some{y} : Maybe<&2, A>}:
  match xs i j:
    case Nil{} _ _:
      Empty.absurd({R.nth(A, R.put(A, Nil{}, i, y), j) == Some{y} : Maybe<&2, A>}, none_some(A, y, h))
    case Con{+hd, +t} 0n 0n:
      {==}
    case Con{+hd, +t} 0n 1n+q:
      h
    case Con{+hd, +t} 1n+r 0n:
      h
    case Con{+hd, +t} 1n+r 1n+q:
      nth_put(A, t, r, q, y, h)

def swap_some(~A: Data, ~V: Data, ~rel: A -> V -> Bool, +v: V, +xs: List<&2, A>, +i: Nat, +j: Nat, +x: A, +y: A, +hx: {R.nth(A, xs, i) == Some{x} : Maybe<&2, A>}, +hy: {R.nth(A, xs, j) == Some{y} : Maybe<&2, A>}) -> {occ(~A, ~V, ~rel, v, R.put(A, R.put(A, xs, i, y), j, x)) == occ(~A, ~V, ~rel, v, xs) : Nat}:
  +ys = R.put(A, xs, i, y)
  A.add_cancel_r(occ(~A, ~V, ~rel, v, R.put(A, ys, j, x)), occ(~A, ~V, ~rel, v, xs), SR.b2n(rel(y, v)),
    Equal.trans(Nat, Nat.add(occ(~A, ~V, ~rel, v, R.put(A, ys, j, x)), SR.b2n(rel(y, v))), Nat.add(occ(~A, ~V, ~rel, v, ys), SR.b2n(rel(x, v))), Nat.add(occ(~A, ~V, ~rel, v, xs), SR.b2n(rel(y, v))),
      put_occ(~A, ~V, ~rel, v, ys, j, x, y, nth_put(A, xs, i, j, y, hy)),
      put_occ(~A, ~V, ~rel, v, xs, i, y, x, hx)))

def swap_m_occ(~A: Data, ~V: Data, ~rel: A -> V -> Bool, +v: V, +xs: List<&2, A>, +i: Nat, +j: Nat, +a: Maybe<&2, A>, +b: Maybe<&2, A>, +ha: {R.nth(A, xs, i) == a : Maybe<&2, A>}, +hb: {R.nth(A, xs, j) == b : Maybe<&2, A>}) -> {occ(~A, ~V, ~rel, v, R.swap_m(A, xs, i, j, a, b)) == occ(~A, ~V, ~rel, v, xs) : Nat}:
  match a b:
    case Some{x} Some{y}:
      swap_some(~A, ~V, ~rel, v, xs, i, j, x, y, ha, hb)
    case None{} _:
      {==}
    case Some{x} None{}:
      {==}

# THEOREM: a swap keeps every count
def swap_occ(~A: Data, ~V: Data, ~rel: A -> V -> Bool, +v: V, +xs: List<&2, A>, +i: Nat, +j: Nat) -> {occ(~A, ~V, ~rel, v, R.swap(A, xs, i, j)) == occ(~A, ~V, ~rel, v, xs) : Nat}:
  swap_m_occ(~A, ~V, ~rel, v, xs, i, j, R.nth(A, xs, i), R.nth(A, xs, j), {==}, {==})

def swap_at_occ(~A: Data, ~V: Data, ~rel: A -> V -> Bool, -S: Data, +v: V, +xs: List<&2, A>, +i: Nat, r: W.U64 & S) -> {occ(~A, ~V, ~rel, v, R.fst(List<&2, A>, S, R.swap_at(A, S, xs, i, r))) == occ(~A, ~V, ~rel, v, xs) : Nat}:
  match r:
    case Tuple{+j, s}:
      swap_occ(~A, ~V, ~rel, v, xs, i, X.n48(j))

def go_occ(~A: Data, ~V: Data, ~rel: A -> V -> Bool, ~S: Data, ~next: S -> W.U64 & S, +v: V, +k: Nat, +n: W.U64, st: List<&2, A> & S) -> {occ(~A, ~V, ~rel, v, R.fst(List<&2, A>, S, R.shuffle_go(~A, ~S, ~next, k, n, st))) == occ(~A, ~V, ~rel, v, R.fst(List<&2, A>, S, st)) : Nat}:
  match k st:
    case 0n Tuple{+xs, +s}:
      {==}
    case 1n+p Tuple{+xs, +s}:
      Equal.trans(Nat, occ(~A, ~V, ~rel, v, R.fst(List<&2, A>, S, R.shuffle_go(~A, ~S, ~next, p, X.sub(n, W.U64{1, 0}), R.shuffle_step(~A, ~S, ~next, 1n+p, n, (xs, s))))), occ(~A, ~V, ~rel, v, R.fst(List<&2, A>, S, R.shuffle_step(~A, ~S, ~next, 1n+p, n, (xs, s)))), occ(~A, ~V, ~rel, v, xs),
        go_occ(~A, ~V, ~rel, ~S, ~next, v, p, X.sub(n, W.U64{1, 0}), R.shuffle_step(~A, ~S, ~next, 1n+p, n, (xs, s))),
        swap_at_occ(~A, ~V, ~rel, S, v, xs, 1n+p, R.uint64n(~S, ~next, s, n)))

# the list shuffle (R.shuffle_list, for 2^31 elements or more) permutes
def shuffle_list_perm(~A: Data, ~V: Data, ~rel: A -> V -> Bool, ~S: Data, ~next: S -> W.U64 & S, +s: S, +xs: List<&2, A>, +v: V) -> {SR.occurrences(~A, ~V, ~rel, v, R.fst(List<&2, A>, S, R.shuffle_list(~A, ~S, ~next, s, xs))) == SR.occurrences(~A, ~V, ~rel, v, xs) : Nat}:
  go_occ(~A, ~V, ~rel, ~S, ~next, v, Nat.sub(List.length(&2, A, xs), 1n), R.len64(A, xs), (xs, s))

# [p == v] + [v < p] == [v < p + 1]
def lt_succ_split(+v: Nat, +p: Nat) -> {Nat.add(SR.b2n(Nat.is_eq(p, v)), SR.b2n(Nat.is_lt(v, p))) == SR.b2n(Nat.is_lt(v, 1n+p)) : Nat}:
  match v p:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+u 0n:
      %Equal.sym(Bool, Nat.is_lt(u, 0n), False{}, N.not_lt_zero(u)) : {0n == SR.b2n(_) : Nat}
      {==}
    case 1n+u 1n+q:
      lt_succ_split(u, q)

# range_go(n, acc) = [0, 1, ..., n - 1] ++ acc holds v as often as acc,
# plus once when v < n
def range_occ(+n: Nat, +acc: List<&2, Nat>, +v: Nat) -> {SR.occurrences(~Nat, ~Nat, ~Nat.is_eq, v, R.range_go(n, acc)) == Nat.add(SR.occurrences(~Nat, ~Nat, ~Nat.is_eq, v, acc), SR.b2n(Nat.is_lt(v, n))) : Nat}:
  match n:
    case 0n:
      %Equal.sym(Bool, Nat.is_lt(v, 0n), False{}, N.not_lt_zero(v)) : {SR.occurrences(~Nat, ~Nat, ~Nat.is_eq, v, acc) == Nat.add(SR.occurrences(~Nat, ~Nat, ~Nat.is_eq, v, acc), SR.b2n(_)) : Nat}
      Equal.sym(Nat, Nat.add(SR.occurrences(~Nat, ~Nat, ~Nat.is_eq, v, acc), 0n), SR.occurrences(~Nat, ~Nat, ~Nat.is_eq, v, acc), N.add_zero(SR.occurrences(~Nat, ~Nat, ~Nat.is_eq, v, acc)))
    case 1n+p:
      +o = SR.occurrences(~Nat, ~Nat, ~Nat.is_eq, v, acc)
      +e = SR.b2n(Nat.is_eq(p, v))
      +l = SR.b2n(Nat.is_lt(v, p))
      Equal.trans(Nat, SR.occurrences(~Nat, ~Nat, ~Nat.is_eq, v, R.range_go(p, Con{p, acc})), Nat.add(Nat.add(e, o), l), Nat.add(o, SR.b2n(Nat.is_lt(v, 1n+p))),
        range_occ(p, Con{p, acc}, v),
        Equal.trans(Nat, Nat.add(Nat.add(e, o), l), Nat.add(o, Nat.add(e, l)), Nat.add(o, SR.b2n(Nat.is_lt(v, 1n+p))),
          Equal.trans(Nat, Nat.add(Nat.add(e, o), l), Nat.add(Nat.add(o, e), l), Nat.add(o, Nat.add(e, l)),
            Equal.cong(Nat, Nat, t => Nat.add(t, l), Nat.add(e, o), Nat.add(o, e), N.add_comm(e, o)),
            N.add_assoc(o, e, l)),
          Equal.cong(Nat, Nat, t => Nat.add(o, t), Nat.add(e, l), SR.b2n(Nat.is_lt(v, 1n+p)), lt_succ_split(v, p))))
