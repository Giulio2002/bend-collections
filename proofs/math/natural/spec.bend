import Base

# Independent definitions the natural-number functions are proved
# against, as structural recursions in the shape of Lean 4 Mathlib:
#   factorial   Mathlib/Data/Nat/Factorial/Basic (Nat.factorial_succ)
#   desc        n.descFactorial k, (n - k) * n.descFactorial k at k + 1
#   choose      Mathlib/Data/Nat/Choose/Basic (Pascal's rule, Nat.choose_succ_succ)
#   lsum/lprod  List.sum and List.prod as right folds

def factorial(n: Nat) -> Nat:
  match n:
    case 0n:
      1n
    case 1n+ +p:
      Nat.mul(1n+p, factorial(p))

def desc(+n: Nat, k: Nat) -> Nat:
  match k:
    case 0n:
      1n
    case 1n+ +j:
      Nat.mul(Nat.sub(n, j), desc(n, j))

def choose(n: Nat, k: Nat) -> Nat:
  match n k:
    case 0n 0n:
      1n
    case 0n 1n+j:
      0n
    case 1n+m 0n:
      1n
    case 1n+ +m 1n+ +j:
      Nat.add(choose(m, j), choose(m, 1n+j))

def lsum(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{x, t}:
      Nat.add(x, lsum(t))

def lprod(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      1n
    case Con{x, t}:
      Nat.mul(x, lprod(t))
