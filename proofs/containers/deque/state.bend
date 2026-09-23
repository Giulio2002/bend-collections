import Base
import ../../lib/spec_common.bend as SC
import ../../../src/containers/deque.bend as DQ

# The two-list deque DE{front, back, nf, nb} as a Data shadow: the two
# lists, with the counts their lengths (so the count invariant holds by
# construction).
#   model(sh) = front ++ reverse(back)   the elements, front first

type Shadow<-T: Data> is Data:
  Sh{front: List<&2, T>, back: List<&2, T>}

def initial(-T: Data) -> Shadow<T>:
  Sh{Nil{}, Nil{}}

def real(-T: Data, sh: Shadow<T>) -> DQ.Deque<T>:
  match sh:
    case Sh{+f, +b}:
      DQ.DE{f, b, SC.length(T, f), SC.length(T, b)}

def model(-T: Data, sh: Shadow<T>) -> List<&2, T>:
  match sh:
    case Sh{f, b}:
      SC.append(T, f, SC.reverse(T, b))

def unreal(-T: Data, d: DQ.Deque<T>) -> Shadow<T>:
  DQ.DE{f, b, nf, nb} = d
  Sh{f, b}

def unreal_real(-T: Data, +sh: Shadow<T>) -> {unreal(T, real(T, sh)) == sh : Shadow<T>}:
  match sh:
    case Sh{f, b}:
      {==}

# a deque determines its shadow
def real_inj(-T: Data, +a: Shadow<T>, +b: Shadow<T>, +e: {real(T, a) == real(T, b) : DQ.Deque<T>}) -> {a == b : Shadow<T>}:
  Equal.trans(Shadow<T>, a, unreal(T, real(T, a)), b, Equal.sym(Shadow<T>, unreal(T, real(T, a)), a, unreal_real(T, a)),
    Equal.trans(Shadow<T>, unreal(T, real(T, a)), unreal(T, real(T, b)), b, Equal.cong(DQ.Deque<T>, Shadow<T>, d => unreal(T, d), real(T, a), real(T, b), e), unreal_real(T, b)))
