import Base
import ../../lib/logic.bend as L

# Bit-level facts about zero tests on words, for any width, then at U32.
# A word is zero when it compares EQ with Word.zero; Word.cmp compares the
# tail first and settles ties with the head (Word.cmp.fin).

law and_true:
  for +b: Bool
  {Bool.and(b, True{}) == b : Bool}

def and_true(b):
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

law and_false:
  for +b: Bool
  {Bool.and(b, False{}) == False{} : Bool}

def and_false(b):
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

law and_assoc:
  for +a: Bool
  for +b: Bool
  for +c: Bool
  {Bool.and(Bool.and(a, b), c) == Bool.and(a, Bool.and(b, c)) : Bool}

def and_assoc(a, b, c):
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

# A comparison is EQ exactly when the tails compare EQ and the heads agree.
law fin_eq:
  for +ab: Bool
  for +bb: Bool
  for +t: Cmp
  {Cmp.is_eq(Word.cmp.fin(ab, bb, t)) == Bool.and(Cmp.is_eq(t), Cmp.is_eq(Bool.cmp(ab, bb))) : Bool}

def fin_eq(ab, bb, t):
  match t:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

law bits_or:
  for +a: Bool
  for +b: Bool
  for +x: Bool
  for +y: Bool
  {Bool.and(Bool.and(a, b), Cmp.is_eq(Bool.cmp(Bool.or(x, y), False{}))) ==
    Bool.and(Bool.and(a, Cmp.is_eq(Bool.cmp(x, False{}))), Bool.and(b, Cmp.is_eq(Bool.cmp(y, False{})))) : Bool}

def bits_or(a, b, x, y):
  match a b x y:
    case False{} _ _ _:
      {==}
    case True{} False{} False{} _:
      {==}
    case True{} False{} True{} _:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

law bits_xor:
  for +k: Bool
  for +x: Bool
  for +y: Bool
  {Bool.and(k, Cmp.is_eq(Bool.cmp(Bool.xor(x, y), False{}))) == Bool.and(k, Cmp.is_eq(Bool.cmp(x, y))) : Bool}

def bits_xor(k, x, y):
  match x y:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

law bit_eq:
  for +x: Bool
  for +y: Bool
  for +h: {Cmp.is_eq(Bool.cmp(x, y)) == True{} : Bool}
  {x == y : Bool}

def bit_eq(x, y, h):
  match x y:
    case False{} False{}:
      {==}
    case False{} True{}:
      Empty.absurd({False{} == True{} : Bool}, L.false_true(h))
    case True{} False{}:
      Empty.absurd({True{} == False{} : Bool}, L.false_true(h))
    case True{} True{}:
      {==}

law bit_refl:
  for +k: Bool
  for +x: Bool
  {Bool.and(k, Cmp.is_eq(Bool.cmp(x, x))) == k : Bool}

def bit_refl(k, x):
  match x:
    case False{}:
      and_true(k)
    case True{}:
      and_true(k)

# zero(x | y) == zero(x) && zero(y)
law or_zero:
  for +n: Nat
  for +x: Word(n)
  for +y: Word(n)
  {Cmp.is_eq(Word.cmp(n, Word.or(n, x, y), Word.zero(n))) ==
    Bool.and(Cmp.is_eq(Word.cmp(n, x, Word.zero(n))), Cmp.is_eq(Word.cmp(n, y, Word.zero(n)))) : Bool}

def or_zero(n, x, y):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match x y:
        case WCon{a, xt} WCon{b, yt}:
          +co = Word.cmp(p, Word.or(p, xt, yt), Word.zero(p))
          +cx = Word.cmp(p, xt, Word.zero(p))
          +cy = Word.cmp(p, yt, Word.zero(p))
          %Equal.sym(Bool, Cmp.is_eq(Word.cmp.fin(Bool.or(a, b), False{}, co)),
            Bool.and(Cmp.is_eq(co), Cmp.is_eq(Bool.cmp(Bool.or(a, b), False{}))),
            fin_eq(Bool.or(a, b), False{}, co)) :
            {_ == Bool.and(Cmp.is_eq(Word.cmp.fin(a, False{}, cx)), Cmp.is_eq(Word.cmp.fin(b, False{}, cy))) : Bool}
          %Equal.sym(Bool, Cmp.is_eq(Word.cmp.fin(a, False{}, cx)),
            Bool.and(Cmp.is_eq(cx), Cmp.is_eq(Bool.cmp(a, False{}))),
            fin_eq(a, False{}, cx)) :
            {Bool.and(Cmp.is_eq(co), Cmp.is_eq(Bool.cmp(Bool.or(a, b), False{}))) == Bool.and(_, Cmp.is_eq(Word.cmp.fin(b, False{}, cy))) : Bool}
          %Equal.sym(Bool, Cmp.is_eq(Word.cmp.fin(b, False{}, cy)),
            Bool.and(Cmp.is_eq(cy), Cmp.is_eq(Bool.cmp(b, False{}))),
            fin_eq(b, False{}, cy)) :
            {Bool.and(Cmp.is_eq(co), Cmp.is_eq(Bool.cmp(Bool.or(a, b), False{}))) == Bool.and(Bool.and(Cmp.is_eq(cx), Cmp.is_eq(Bool.cmp(a, False{}))), _) : Bool}
          %Equal.sym(Bool, Cmp.is_eq(co), Bool.and(Cmp.is_eq(cx), Cmp.is_eq(cy)), or_zero(p, xt, yt)) :
            {Bool.and(_, Cmp.is_eq(Bool.cmp(Bool.or(a, b), False{}))) == Bool.and(Bool.and(Cmp.is_eq(cx), Cmp.is_eq(Bool.cmp(a, False{}))), Bool.and(Cmp.is_eq(cy), Cmp.is_eq(Bool.cmp(b, False{})))) : Bool}
          bits_or(Cmp.is_eq(cx), Cmp.is_eq(cy), a, b)

# zero(x ^ y) == (x == y)
law xor_zero:
  for +n: Nat
  for +x: Word(n)
  for +y: Word(n)
  {Cmp.is_eq(Word.cmp(n, Word.xor(n, x, y), Word.zero(n))) == Cmp.is_eq(Word.cmp(n, x, y)) : Bool}

def xor_zero(n, x, y):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match x y:
        case WCon{a, xt} WCon{b, yt}:
          +co = Word.cmp(p, Word.xor(p, xt, yt), Word.zero(p))
          +c = Word.cmp(p, xt, yt)
          %Equal.sym(Bool, Cmp.is_eq(Word.cmp.fin(Bool.xor(a, b), False{}, co)),
            Bool.and(Cmp.is_eq(co), Cmp.is_eq(Bool.cmp(Bool.xor(a, b), False{}))),
            fin_eq(Bool.xor(a, b), False{}, co)) :
            {_ == Cmp.is_eq(Word.cmp.fin(a, b, c)) : Bool}
          %Equal.sym(Bool, Cmp.is_eq(Word.cmp.fin(a, b, c)),
            Bool.and(Cmp.is_eq(c), Cmp.is_eq(Bool.cmp(a, b))), fin_eq(a, b, c)) :
            {Bool.and(Cmp.is_eq(co), Cmp.is_eq(Bool.cmp(Bool.xor(a, b), False{}))) == _ : Bool}
          %Equal.sym(Bool, Cmp.is_eq(co), Cmp.is_eq(c), xor_zero(p, xt, yt)) :
            {Bool.and(_, Cmp.is_eq(Bool.cmp(Bool.xor(a, b), False{}))) == Bool.and(Cmp.is_eq(c), Cmp.is_eq(Bool.cmp(a, b))) : Bool}
          bits_xor(Cmp.is_eq(c), a, b)

law cmp_sound:
  for +n: Nat
  for +x: Word(n)
  for +y: Word(n)
  for +h: {Cmp.is_eq(Word.cmp(n, x, y)) == True{} : Bool}
  {x == y : Word(n)}

def cmp_sound(n, x, y, h):
  match n:
    case 0n:
      match x y:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match x y:
        case WCon{a, xt} WCon{b, yt}:
          +c = Word.cmp(p, xt, yt)
          +h2 = Equal.trans(Bool, Bool.and(Cmp.is_eq(c), Cmp.is_eq(Bool.cmp(a, b))),
            Cmp.is_eq(Word.cmp.fin(a, b, c)), True{},
            Equal.sym(Bool, Cmp.is_eq(Word.cmp.fin(a, b, c)),
              Bool.and(Cmp.is_eq(c), Cmp.is_eq(Bool.cmp(a, b))), fin_eq(a, b, c)), h)
          +et = cmp_sound(p, xt, yt, L.and_left(Cmp.is_eq(c), Cmp.is_eq(Bool.cmp(a, b)), h2))
          +eb = bit_eq(a, b, L.and_right(Cmp.is_eq(c), Cmp.is_eq(Bool.cmp(a, b)), h2))
          %et : {WCon{a, xt} == WCon{b, _} : Word(1n+p)}
          %eb : {WCon{a, xt} == WCon{_, xt} : Word(1n+p)}
          {==}

law cmp_refl:
  for +n: Nat
  for +x: Word(n)
  {Cmp.is_eq(Word.cmp(n, x, x)) == True{} : Bool}

def cmp_refl(n, x):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match x:
        case WCon{a, xt}:
          +c = Word.cmp(p, xt, xt)
          %Equal.sym(Bool, Cmp.is_eq(Word.cmp.fin(a, a, c)),
            Bool.and(Cmp.is_eq(c), Cmp.is_eq(Bool.cmp(a, a))), fin_eq(a, a, c)) :
            {_ == True{} : Bool}
          %Equal.sym(Bool, Bool.and(Cmp.is_eq(c), Cmp.is_eq(Bool.cmp(a, a))), Cmp.is_eq(c), bit_refl(Cmp.is_eq(c), a)) : {_ == True{} : Bool}
          cmp_refl(p, xt)

# ---- at U32

law u32_or_zero:
  for +x: U32
  for +y: U32
  {U32.is_eq(U32.or(x, y), 0) == Bool.and(U32.is_eq(x, 0), U32.is_eq(y, 0)) : Bool}

def u32_or_zero(x, y):
  match x y:
    case U32{a} U32{b}:
      or_zero(32n, a, b)

law u32_xor_zero:
  for +x: U32
  for +y: U32
  {U32.is_eq(U32.xor(x, y), 0) == U32.is_eq(x, y) : Bool}

def u32_xor_zero(x, y):
  match x y:
    case U32{a} U32{b}:
      xor_zero(32n, a, b)

law u32_sound:
  for +x: U32
  for +y: U32
  for +h: {U32.is_eq(x, y) == True{} : Bool}
  {x == y : U32}

def u32_sound(x, y, h):
  match x y:
    case U32{a} U32{b}:
      %cmp_sound(32n, a, b, h) : {U32{a} == U32{_} : U32}
      {==}

law u32_refl:
  for +x: U32
  {U32.is_eq(x, x) == True{} : Bool}

def u32_refl(x):
  match x:
    case U32{a}:
      cmp_refl(32n, a)
