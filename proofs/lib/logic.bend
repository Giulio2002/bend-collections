import Base

# Propositional helpers shared by every proof module.

def truth(b: Bool) -> Type:
  match b:
    case False{}:
      Empty
    case True{}:
      Unit

def false_true(e: {False{} == True{} : Bool}) -> Empty:
  %Equal.sym(Bool, False{}, True{}, e) : truth(_)
  Unit{}

def true_false(e: {True{} == False{} : Bool}) -> Empty:
  false_true(Equal.sym(Bool, True{}, False{}, e))

def and_left(a: Bool, b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, false_true(e))
    case True{}:
      {==}

def and_right(a: Bool, b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case False{}:
      Empty.absurd({b == True{} : Bool}, false_true(e))
    case True{}:
      e

def and_intro(a: Bool, b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ea) : {Bool.and(_, b) == True{} : Bool}
  eb

def not_true(b: Bool, e: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, false_true(e))

def not_false(b: Bool, e: {b == False{} : Bool}) -> {Bool.not(b) == True{} : Bool}:
  %Equal.sym(Bool, b, False{}, e) : {Bool.not(_) == True{} : Bool}
  {==}

def bool_cases(b: Bool) -> Or({b == True{} : Bool}, {b == False{} : Bool}):
  match b:
    case True{}:
      Inl{{==}}
    case False{}:
      Inr{{==}}

def true_not_false(b: Bool, t: {b == True{} : Bool}, f: {b == False{} : Bool}) -> Empty:
  false_true(Equal.trans(Bool, False{}, b, True{}, Equal.sym(Bool, b, False{}, f), t))

# Cmp discrimination.
def cmp_code(c: Cmp) -> Nat:
  match c:
    case LT{}:
      0n
    case EQ{}:
      1n
    case GT{}:
      2n

def cmp_lt_eq(e: {LT{} == EQ{} : Cmp}) -> Empty:
  %e : truth(Cmp.is_lt(_))
  Unit{}

def cmp_lt_gt(e: {LT{} == GT{} : Cmp}) -> Empty:
  %e : truth(Cmp.is_lt(_))
  Unit{}

def cmp_eq_gt(e: {EQ{} == GT{} : Cmp}) -> Empty:
  %e : truth(Cmp.is_eq(_))
  Unit{}

# Maybe discrimination.
def none_some(-A: Data, x: A, e: {None{} == Some{x} : Maybe<&2, A>}) -> Empty:
  %Equal.sym(Maybe<&2, A>, None{}, Some{x}, e) : truth(Maybe.is_some(&2, A, _))
  Unit{}

def some_value(-A: Data, m: Maybe<&2, A>, d: A) -> A:
  match m:
    case None{}:
      d
    case Some{x}:
      x

def some_inj(-A: Data, x: A, y: A, e: {Some{x} == Some{y} : Maybe<&2, A>}) -> {x == y : A}:
  Equal.cong(Maybe<&2, A>, A, m => some_value(A, m, x), Some{x}, Some{y}, e)

def pair_fst(-A: Type, -B: Type, a: A, b: B, c: A, d: B, e: {(a, b) == (c, d) : A & B}) -> {a == c : A}:
  Equal.cong(A & B, A, p => Pair.fst(A, B, p), (a, b), (c, d), e)

def pair_snd(-A: Type, -B: Type, a: A, b: B, c: A, d: B, e: {(a, b) == (c, d) : A & B}) -> {b == d : B}:
  Equal.cong(A & B, B, p => Pair.snd(A, B, p), (a, b), (c, d), e)

def pair_eq(-A: Type, -B: Type, a: A, b: B, c: A, d: B, ea: {a == c : A}, eb: {b == d : B}) -> {(a, b) == (c, d) : A & B}:
  %ea : {(a, b) == (_, d) : A & B}
  %eb : {(a, b) == (a, _) : A & B}
  {==}

# Transport a proof along an equation.
def subst(-A: Type, -P: A -> Type, -a: A, -b: A, e: {a == b : A}, pa: P(a)) -> P(b):
  %e : P(_)
  pa

# Dependent pair projections (call results cannot be destructured directly).
def sfst(-A: Type, -B: @-x: A -> Type, p: Sigma<&1, &1, A, B>) -> A:
  match p:
    case Tuple{a, b}:
      a

def ssnd(-A: Type, -B: @-x: A -> Type, p: Sigma<&1, &1, A, B>) -> B(sfst(A, B, p)):
  match p:
    case Tuple{a, b}:
      b

def pair_eta(-A: Type, -B: Type, p: A & B) -> {p == (Pair.fst(A, B, p), Pair.snd(A, B, p)) : A & B}:
  match p:
    case Tuple{a, b}:
      {==}
