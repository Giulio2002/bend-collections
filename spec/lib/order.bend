import Base

# Total-order laws for a static comparator ~cmp : A -> A -> Cmp, the
# precondition every ordered container states its contract under.
#   flip:    cmp(b, a) = flip(cmp(a, b))
#   antisym: cmp(a, b) = EQ  implies  a == b
#   trans:   a <= b and b <= c  implies  a <= c     (<= is cmp in {LT, EQ})
# The lemmas and the U32 / String instances are in proofs/lib/order.bend.

def flipc(c: Cmp) -> Cmp:
  match c:
    case LT{}:
      GT{}
    case EQ{}:
      EQ{}
    case GT{}:
      LT{}

def Order(~A: Data, ~cmp: A -> A -> Cmp) -> Type:
  (@+a: A -> @+b: A -> {cmp(b, a) == flipc(cmp(a, b)) : Cmp}) & ((@+a: A -> @+b: A -> @+e: {cmp(a, b) == EQ{} : Cmp} -> {a == b : A}) & (@+a: A -> @+b: A -> @+c: A -> @+ab: {Cmp.is_le(cmp(a, b)) == True{} : Bool} -> @+bc: {Cmp.is_le(cmp(b, c)) == True{} : Bool} -> {Cmp.is_le(cmp(a, c)) == True{} : Bool}))
