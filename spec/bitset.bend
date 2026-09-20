import Base
import ./common.bend as C
import ../types/bitset.bend as E

# Independent model: a bitset of logical size n is a sequence of n Booleans
# (bit 0 first). Nothing here refers to words, shifts or masks.

def new(n: Nat) -> List<&2, Bool>:
  C.replicate(Bool, n, False{})

# Number of True bits.
def count(xs: List<&2, Bool>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{False{}, t}:
      count(t)
    case Con{True{}, t}:
      1n+count(t)

# Indices (offset by off) of True bits, ascending.
def members(xs: List<&2, Bool>, +off: Nat) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{False{}, t}:
      members(t, 1n+off)
    case Con{True{}, t}:
      Con{off, members(t, 1n+off)}

# Element-wise combination of two sequences (truncates to the shorter one).
def zip_or(xs: List<&2, Bool>, ys: List<&2, Bool>) -> List<&2, Bool>:
  match xs ys:
    case Con{a, s} Con{b, t}:
      Con{Bool.or(a, b), zip_or(s, t)}
    case _ _:
      Nil{}

def zip_and(xs: List<&2, Bool>, ys: List<&2, Bool>) -> List<&2, Bool>:
  match xs ys:
    case Con{a, s} Con{b, t}:
      Con{Bool.and(a, b), zip_and(s, t)}
    case _ _:
      Nil{}

def zip_diff(xs: List<&2, Bool>, ys: List<&2, Bool>) -> List<&2, Bool>:
  match xs ys:
    case Con{a, s} Con{b, t}:
      Con{Bool.and(a, Bool.not(b)), zip_diff(s, t)}
    case _ _:
      Nil{}

def zip_xor(xs: List<&2, Bool>, ys: List<&2, Bool>) -> List<&2, Bool>:
  match xs ys:
    case Con{a, s} Con{b, t}:
      Con{Bool.xor(a, b), zip_xor(s, t)}
    case _ _:
      Nil{}

def bit(x: Maybe<&2, Bool>) -> Result<&2, &2, E.Error, Bool>:
  match x:
    case None{}:
      Fail{E.IndexOutOfRange{}}
    case Some{b}:
      Done{b}

def get(xs: List<&2, Bool>, i: Nat) -> Result<&2, &2, E.Error, Bool>:
  bit(C.nth(Bool, xs, i))

# Assign bit i; out of range leaves the sequence unchanged and fails.
def assign_at(x: Maybe<&2, Bool>, +xs: List<&2, Bool>, i: Nat, v: Bool) -> List<&2, Bool> & E.Obs:
  match x:
    case None{}:
      (xs, E.OUnit{Fail{E.IndexOutOfRange{}}})
    case Some{b}:
      (C.update(Bool, xs, i, v), E.OUnit{Done{Unit{}}})

def assign(+xs: List<&2, Bool>, +i: Nat, v: Bool) -> List<&2, Bool> & E.Obs:
  assign_at(C.nth(Bool, xs, i), xs, i, v)

# Combine with an operand of the same logical size; a size mismatch leaves
# the sequence unchanged and fails.
def combine_if(same: Bool, xs: List<&2, Bool>, r: List<&2, Bool>) -> List<&2, Bool> & E.Obs:
  match same:
    case False{}:
      (xs, E.OUnit{Fail{E.LengthMismatch{}}})
    case True{}:
      (r, E.OUnit{Done{Unit{}}})

def combine(+xs: List<&2, Bool>, ys: List<&2, Bool>, r: List<&2, Bool>) -> List<&2, Bool> & E.Obs:
  combine_if(Nat.is_eq(C.length(Bool, xs), C.length(Bool, ys)), xs, r)

def step(+xs: List<&2, Bool>, op: E.Op) -> List<&2, Bool> & E.Obs:
  match op:
    case E.Length{}:
      (xs, E.ONat{C.length(Bool, xs)})
    case E.Get{+i}:
      (xs, E.OBit{get(xs, i)})
    case E.Set{+i}:
      assign(xs, i, True{})
    case E.Clear{+i}:
      assign(xs, i, False{})
    case E.Count{}:
      (xs, E.ONat{count(xs)})
    case E.Union{+ys}:
      combine(xs, ys, zip_or(xs, ys))
    case E.Intersection{+ys}:
      combine(xs, ys, zip_and(xs, ys))
    case E.Difference{+ys}:
      combine(xs, ys, zip_diff(xs, ys))
    case E.Xor{+ys}:
      combine(xs, ys, zip_xor(xs, ys))
    case E.ToList{}:
      (xs, E.OList{members(xs, 0n)})

def cons_obs(o: E.Obs, r: List<&2, Bool> & List<&2, E.Obs>) -> List<&2, Bool> & List<&2, E.Obs>:
  (m, os) = r
  (m, Con{o, os})

def run(ops: List<&2, E.Op>, +xs: List<&2, Bool>) -> List<&2, Bool> & List<&2, E.Obs>:
  match ops:
    case Nil{}:
      (xs, Nil{})
    case Con{+op, rest}:
      cons_obs(Pair.snd(List<&2, Bool>, E.Obs, step(xs, op)), run(rest, Pair.fst(List<&2, Bool>, E.Obs, step(xs, op))))
