import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../../spec/common.bend as SC
import ../../src/union_find.bend as U

# The proof-level cell of src/union_find.bend.
#
# The runtime keeps three parallel arenas (representative, class size, member
# list), because a one-field slot is several times cheaper to read than a
# three-field record in the native backend. The mathematics is easier to
# state over one list of records, so this module defines that record and the
# zip that builds it from the three slot lists, together with the laws that
# let a write to one arena be read as a write to the zipped list.
#
# Nothing here is part of the runtime: `Cell` is a proof-level view.

type Cell is Data:
  Cell{root: Nat, size: Nat, members: List<&2, Nat>}

def croot(c: Cell) -> Nat:
  match c:
    case Cell{r, z, ms}:
      r

def csize(c: Cell) -> Nat:
  match c:
    case Cell{r, z, ms}:
      z

def cmembers(c: Cell) -> List<&2, Nat>:
  match c:
    case Cell{r, z, ms}:
      ms

def with_root(c: Cell, +r: Nat) -> Cell:
  match c:
    case Cell{q, z, ms}:
      Cell{r, z, ms}

def cell_of(m: Maybe<&2, Cell>, +x: Nat) -> Cell:
  match m:
    case Some{c}:
      c
    case None{}:
      Cell{x, 1n, Nil{}}

# ---- the three slot lists ----

def nmap(xs: List<&2, U.Nt>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      Con{U.nval(x), nmap(t)}

def mmap(xs: List<&2, U.Ms>) -> List<&2, List<&2, Nat>>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      Con{U.mval(x), mmap(t)}

# The zipped record list. Truncates to the shortest, which the invariant
# never allows to matter: all three arenas have the same depth.
def cells(rs: List<&2, Nat>, zs: List<&2, Nat>, ms: List<&2, List<&2, Nat>>) -> List<&2, Cell>:
  match rs zs ms:
    case Con{r, rt} Con{z, zt} Con{m, mt}:
      Con{Cell{r, z, m}, cells(rt, zt, mt)}
    case _ _ _:
      Nil{}

# ---- lengths ----

def nmap_length(xs: List<&2, U.Nt>) -> {SC.length(Nat, nmap(xs)) == SC.length(U.Nt, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +t}:
      N.succ_cong(SC.length(Nat, nmap(t)), SC.length(U.Nt, t), nmap_length(t))

def mmap_length(xs: List<&2, U.Ms>) -> {SC.length(List<&2, Nat>, mmap(xs)) == SC.length(U.Ms, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +t}:
      N.succ_cong(SC.length(List<&2, Nat>, mmap(t)), SC.length(U.Ms, t), mmap_length(t))

def cells_length(rs: List<&2, Nat>, zs: List<&2, Nat>, ms: List<&2, List<&2, Nat>>, +ez: {SC.length(Nat, zs) == SC.length(Nat, rs) : Nat}, +em: {SC.length(List<&2, Nat>, ms) == SC.length(Nat, rs) : Nat}) -> {SC.length(Cell, cells(rs, zs, ms)) == SC.length(Nat, rs) : Nat}:
  match rs zs ms:
    case Con{r, +rt} Con{z, +zt} Con{m, +mt}:
      N.succ_cong(SC.length(Cell, cells(rt, zt, mt)), SC.length(Nat, rt),
        cells_length(rt, zt, mt, N.succ_inj(SC.length(Nat, zt), SC.length(Nat, rt), ez), N.succ_inj(SC.length(List<&2, Nat>, mt), SC.length(Nat, rt), em)))
    case Nil{} _ _:
      {==}
    case Con{r, rt} Nil{} _:
      Empty.absurd({SC.length(Cell, Nil{}) == SC.length(Nat, Con{r, rt}) : Nat}, N.zero_succ(SC.length(Nat, rt), ez))
    case Con{r, rt} Con{z, zt} Nil{}:
      Empty.absurd({SC.length(Cell, Nil{}) == SC.length(Nat, Con{r, rt}) : Nat}, N.zero_succ(SC.length(Nat, rt), em))

# ---- nth ----

def cells_nth(rs: List<&2, Nat>, zs: List<&2, Nat>, ms: List<&2, List<&2, Nat>>, x: Nat, +r: Nat, +z: Nat, +m: List<&2, Nat>, +hr: {SC.nth(Nat, rs, x) == Some{r} : Maybe<&2, Nat>}, +hz: {SC.nth(Nat, zs, x) == Some{z} : Maybe<&2, Nat>}, +hm: {SC.nth(List<&2, Nat>, ms, x) == Some{m} : Maybe<&2, List<&2, Nat>>}) -> {SC.nth(Cell, cells(rs, zs, ms), x) == Some{Cell{r, z, m}} : Maybe<&2, Cell>}:
  match rs zs ms x:
    case Con{a, at} Con{b, bt} Con{c, ct} 0n:
      %Equal.sym(Nat, a, r, L.some_inj(Nat, a, r, hr)) : {Some{Cell{_, b, c}} == Some{Cell{r, z, m}} : Maybe<&2, Cell>}
      %Equal.sym(Nat, b, z, L.some_inj(Nat, b, z, hz)) : {Some{Cell{r, _, c}} == Some{Cell{r, z, m}} : Maybe<&2, Cell>}
      %Equal.sym(List<&2, Nat>, c, m, L.some_inj(List<&2, Nat>, c, m, hm)) : {Some{Cell{r, z, _}} == Some{Cell{r, z, m}} : Maybe<&2, Cell>}
      {==}
    case Con{a, at} Con{b, bt} Con{c, ct} 1n+p:
      cells_nth(at, bt, ct, p, r, z, m, hr, hz, hm)
    case Nil{} _ _ _:
      Empty.absurd({SC.nth(Cell, Nil{}, x) == Some{Cell{r, z, m}} : Maybe<&2, Cell>}, L.none_some(Nat, r, hr))
    case Con{a, at} Nil{} _ _:
      Empty.absurd({SC.nth(Cell, Nil{}, x) == Some{Cell{r, z, m}} : Maybe<&2, Cell>}, L.none_some(Nat, z, hz))
    case Con{a, at} Con{b, bt} Nil{} _:
      Empty.absurd({SC.nth(Cell, Nil{}, x) == Some{Cell{r, z, m}} : Maybe<&2, Cell>}, L.none_some(List<&2, Nat>, m, hm))

# ---- writing one component ----

# Replacing the representative of slot i in the roots arena is exactly
# `with_root` on the zipped list, provided slot i exists.
def cells_set_root(rs: List<&2, Nat>, zs: List<&2, Nat>, ms: List<&2, List<&2, Nat>>, i: Nat, +v: Nat, +j: Nat) -> {cells(SC.update(Nat, rs, i, v), zs, ms) == SC.update(Cell, cells(rs, zs, ms), i, with_root(cell_of(SC.nth(Cell, cells(rs, zs, ms), i), j), v)) : List<&2, Cell>}:
  match rs zs ms i:
    case Con{a, at} Con{b, bt} Con{c, ct} 0n:
      {==}
    case Con{a, +at} Con{b, +bt} Con{c, +ct} 1n+p:
      Equal.cong(List<&2, Cell>, List<&2, Cell>, w => Con{Cell{a, b, c}, w},
        cells(SC.update(Nat, at, p, v), bt, ct),
        SC.update(Cell, cells(at, bt, ct), p, with_root(cell_of(SC.nth(Cell, cells(at, bt, ct), p), j), v)),
        cells_set_root(at, bt, ct, p, v, j))
    case Nil{} _ _ _:
      {==}
    case Con{a, at} Nil{} _ 0n:
      {==}
    case Con{a, at} Nil{} _ 1n+p:
      {==}
    case Con{a, at} Con{b, bt} Nil{} 0n:
      {==}
    case Con{a, at} Con{b, bt} Nil{} 1n+p:
      {==}

# Replacing all three components of slot i.
def cells_set3(rs: List<&2, Nat>, zs: List<&2, Nat>, ms: List<&2, List<&2, Nat>>, i: Nat, +r: Nat, +z: Nat, +m: List<&2, Nat>) -> {cells(SC.update(Nat, rs, i, r), SC.update(Nat, zs, i, z), SC.update(List<&2, Nat>, ms, i, m)) == SC.update(Cell, cells(rs, zs, ms), i, Cell{r, z, m}) : List<&2, Cell>}:
  match rs zs ms i:
    case Con{a, at} Con{b, bt} Con{c, ct} 0n:
      {==}
    case Con{a, +at} Con{b, +bt} Con{c, +ct} 1n+p:
      Equal.cong(List<&2, Cell>, List<&2, Cell>, w => Con{Cell{a, b, c}, w},
        cells(SC.update(Nat, at, p, r), SC.update(Nat, bt, p, z), SC.update(List<&2, Nat>, ct, p, m)),
        SC.update(Cell, cells(at, bt, ct), p, Cell{r, z, m}),
        cells_set3(at, bt, ct, p, r, z, m))
    case Nil{} _ _ _:
      {==}
    case Con{a, at} Nil{} _ 0n:
      {==}
    case Con{a, at} Nil{} _ 1n+p:
      {==}
    case Con{a, at} Con{b, bt} Nil{} 0n:
      {==}
    case Con{a, at} Con{b, bt} Nil{} 1n+p:
      {==}

# Replacing the size and member components of slot i, leaving the
# representative alone.
def cells_set_sm(rs: List<&2, Nat>, zs: List<&2, Nat>, ms: List<&2, List<&2, Nat>>, i: Nat, +r: Nat, +z: Nat, +m: List<&2, Nat>, +hr: {SC.nth(Nat, rs, i) == Some{r} : Maybe<&2, Nat>}) -> {cells(rs, SC.update(Nat, zs, i, z), SC.update(List<&2, Nat>, ms, i, m)) == SC.update(Cell, cells(rs, zs, ms), i, Cell{r, z, m}) : List<&2, Cell>}:
  match rs zs ms i:
    case Con{a, at} Con{b, bt} Con{c, ct} 0n:
      %Equal.sym(Nat, a, r, L.some_inj(Nat, a, r, hr)) : {Con{Cell{_, z, m}, cells(at, bt, ct)} == Con{Cell{r, z, m}, cells(at, bt, ct)} : List<&2, Cell>}
      {==}
    case Con{a, +at} Con{b, +bt} Con{c, +ct} 1n+p:
      Equal.cong(List<&2, Cell>, List<&2, Cell>, w => Con{Cell{a, b, c}, w},
        cells(at, SC.update(Nat, bt, p, z), SC.update(List<&2, Nat>, ct, p, m)),
        SC.update(Cell, cells(at, bt, ct), p, Cell{r, z, m}),
        cells_set_sm(at, bt, ct, p, r, z, m, hr))
    case Nil{} _ _ _:
      Empty.absurd({cells(Nil{}, SC.update(Nat, zs, i, z), SC.update(List<&2, Nat>, ms, i, m)) == SC.update(Cell, cells(Nil{}, zs, ms), i, Cell{r, z, m}) : List<&2, Cell>}, L.none_some(Nat, r, hr))
    case Con{a, at} Nil{} _ 0n:
      {==}
    case Con{a, at} Nil{} _ 1n+p:
      {==}
    case Con{a, at} Con{b, bt} Nil{} 0n:
      {==}
    case Con{a, at} Con{b, bt} Nil{} 1n+p:
      {==}

# The relinking fold at the list level: every write stores `big`, so a slot
# that already holds `big` still holds it afterwards.
def rlr(ms: List<&2, Nat>, rs: List<&2, Nat>, +big: Nat) -> List<&2, Nat>:
  match ms:
    case Nil{}:
      rs
    case Con{+m, rest}:
      rlr(rest, SC.update(Nat, rs, m, big), big)

# Every slot that holds `big` still holds `big` after any relinking, because
# every write stores `big`.

def nth_in_range(+xs: List<&2, Nat>, y: Nat, +v: Nat, +h: {SC.nth(Nat, xs, y) == Some{v} : Maybe<&2, Nat>}) -> {Nat.is_lt(y, SC.length(Nat, xs)) == True{} : Bool}:
  match xs y:
    case Nil{} _:
      Empty.absurd({Nat.is_lt(y, 0n) == True{} : Bool}, L.none_some(Nat, v, h))
    case Con{a, t} 0n:
      {==}
    case Con{a, t} 1n+p:
      nth_in_range(t, p, v, h)

def rlr_step(+rs: List<&2, Nat>, +m: Nat, +big: Nat, +y: Nat, b: Bool, +eb: {Nat.is_eq(m, y) == b : Bool}, +h: {SC.nth(Nat, rs, y) == Some{big} : Maybe<&2, Nat>}) -> {SC.nth(Nat, SC.update(Nat, rs, m, big), y) == Some{big} : Maybe<&2, Nat>}:
  match b:
    case True{}:
      %Equal.sym(Nat, m, y, N.eq_from_is_eq(m, y, eb)) : {SC.nth(Nat, SC.update(Nat, rs, _, big), y) == Some{big} : Maybe<&2, Nat>}
      LL.nth_update_same(Nat, rs, y, big, nth_in_range(rs, y, big, h))
    case False{}:
      %Equal.sym(Maybe<&2, Nat>, SC.nth(Nat, SC.update(Nat, rs, m, big), y), SC.nth(Nat, rs, y), LL.nth_update_other(Nat, rs, m, y, big, eb)) : {_ == Some{big} : Maybe<&2, Nat>}
      h

def rlr_fix(ms: List<&2, Nat>, +rs: List<&2, Nat>, +big: Nat, +y: Nat, +h: {SC.nth(Nat, rs, y) == Some{big} : Maybe<&2, Nat>}) -> {SC.nth(Nat, rlr(ms, rs, big), y) == Some{big} : Maybe<&2, Nat>}:
  match ms:
    case Nil{}:
      h
    case Con{+m, rest}:
      rlr_fix(rest, SC.update(Nat, rs, m, big), big, y, rlr_step(rs, m, big, y, Nat.is_eq(m, y), {==}, h))
