import Base
import ../../lib/spec_common.bend as SC
import ../../../src/containers/queue.bend as Q

# The two-list queue QU{front, back, count} as a Data shadow: the two lists,
# with the count their total length.
#   model(sh) = front ++ reverse(back)   the elements, oldest first

type Shadow<-T: Data> is Data:
  Sh{front: List<&2, T>, back: List<&2, T>}

def initial(-T: Data) -> Shadow<T>:
  Sh{Nil{}, Nil{}}

def real(-T: Data, sh: Shadow<T>) -> Q.Queue<T>:
  match sh:
    case Sh{+f, +b}:
      Q.QU{f, b, Nat.add(SC.length(T, f), SC.length(T, b))}

def model(-T: Data, sh: Shadow<T>) -> List<&2, T>:
  match sh:
    case Sh{f, b}:
      SC.append(T, f, SC.reverse(T, b))

def unreal(-T: Data, q: Q.Queue<T>) -> Shadow<T>:
  Q.QU{f, b, n} = q
  Sh{f, b}

def unreal_real(-T: Data, +sh: Shadow<T>) -> {unreal(T, real(T, sh)) == sh : Shadow<T>}:
  match sh:
    case Sh{f, b}:
      {==}

# a queue determines its shadow
def real_inj(-T: Data, +a: Shadow<T>, +b: Shadow<T>, +e: {real(T, a) == real(T, b) : Q.Queue<T>}) -> {a == b : Shadow<T>}:
  Equal.trans(Shadow<T>, a, unreal(T, real(T, a)), b, Equal.sym(Shadow<T>, unreal(T, real(T, a)), a, unreal_real(T, a)),
    Equal.trans(Shadow<T>, unreal(T, real(T, a)), unreal(T, real(T, b)), b, Equal.cong(Q.Queue<T>, Shadow<T>, d => unreal(T, d), real(T, a), real(T, b), e), unreal_real(T, b)))
