import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/crypto/poly1305.bend as R
import ../../../src/crypto/poly1305/limbs.bend as Li
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/arith.bend as AR
import ../../lib/u32.bend as U3
import ../../lib/u32alg.bend as UA
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../../math/typed/width.bend as WW
import ../../math/typed/w64mul.bend as WM
import ../../math/typed/w64sh.bend as SH
import ../../math/typed/shrn.bend as SHN
import ../../math/typed/f64bits.bend as FB
import ../../math/natural/arith.bend as NR
import ./arith.bend as A
import ./value.bend as V
import ./step.bend as ST

# The last steps: freeze (the canonical value mod p, by a masked choice) and
# the 16 tag bytes (h + s mod 2^128, little-endian).

# ---- words ----

def wones(n: Nat) -> Word(n):
  match n:
    case 0n: WNil{}
    case 1n+p: WCon{True{}, wones(p)}

law wand0:
  for +n: Nat
  for +w: Word(n)
  {Word.and(n, Word.zero(n), w) == Word.zero(n) : Word(n)}

def wand0(n, w):
  match n:
    case 0n:
      match w:
        case WNil{}: {==}
    case 1n+p:
      match w:
        case WCon{b, t}: Equal.cong(Word(p), Word(1n+p), x => WCon{False{}, x}, Word.and(p, Word.zero(p), t), Word.zero(p), wand0(p, t))

law wand1:
  for +n: Nat
  for +w: Word(n)
  {Word.and(n, wones(n), w) == w : Word(n)}

def wand1(n, w):
  match n:
    case 0n:
      match w:
        case WNil{}: {==}
    case 1n+p:
      match w:
        case WCon{b, t}: Equal.cong(Word(p), Word(1n+p), x => WCon{b, x}, Word.and(p, wones(p), t), t, wand1(p, t))

law wxor0:
  for +n: Nat
  for +w: Word(n)
  {Word.xor(n, w, Word.zero(n)) == w : Word(n)}

def wxor0(n, w):
  match n:
    case 0n:
      match w:
        case WNil{}: {==}
    case 1n+p:
      match w:
        case WCon{b, t}:
          match b:
            case False{}: Equal.cong(Word(p), Word(1n+p), x => WCon{False{}, x}, Word.xor(p, t, Word.zero(p)), t, wxor0(p, t))
            case True{}: Equal.cong(Word(p), Word(1n+p), x => WCon{True{}, x}, Word.xor(p, t, Word.zero(p)), t, wxor0(p, t))

law wxor2:
  for +n: Nat
  for +x: Word(n)
  for +y: Word(n)
  {Word.xor(n, x, Word.xor(n, x, y)) == y : Word(n)}

def wxor2(n, x, y):
  match n:
    case 0n:
      match x y:
        case WNil{} WNil{}: {==}
    case 1n+p:
      match x y:
        case WCon{False{}, s} WCon{False{}, t}: Equal.cong(Word(p), Word(1n+p), z => WCon{False{}, z}, Word.xor(p, s, Word.xor(p, s, t)), t, wxor2(p, s, t))
        case WCon{False{}, s} WCon{True{}, t}: Equal.cong(Word(p), Word(1n+p), z => WCon{True{}, z}, Word.xor(p, s, Word.xor(p, s, t)), t, wxor2(p, s, t))
        case WCon{True{}, s} WCon{False{}, t}: Equal.cong(Word(p), Word(1n+p), z => WCon{False{}, z}, Word.xor(p, s, Word.xor(p, s, t)), t, wxor2(p, s, t))
        case WCon{True{}, s} WCon{True{}, t}: Equal.cong(Word(p), Word(1n+p), z => WCon{True{}, z}, Word.xor(p, s, Word.xor(p, s, t)), t, wxor2(p, s, t))

def pick0(+x: U32, +y: U32) -> {Li.pick(0, x, y) == x : U32}:
  match x y:
    case U32{a} U32{b}:
      Equal.trans(U32, U32{Word.xor(32n, a, Word.and(32n, Word.zero(32n), Word.xor(32n, a, b)))}, U32{Word.xor(32n, a, Word.zero(32n))}, U32{a},
        Equal.cong(Word(32n), U32, w => U32{Word.xor(32n, a, w)}, Word.and(32n, Word.zero(32n), Word.xor(32n, a, b)), Word.zero(32n), wand0(32n, Word.xor(32n, a, b))),
        Equal.cong(Word(32n), U32, w => U32{w}, Word.xor(32n, a, Word.zero(32n)), a, wxor0(32n, a)))

def pick1(+x: U32, +y: U32) -> {Li.pick(4294967295, x, y) == y : U32}:
  match x y:
    case U32{a} U32{b}:
      Equal.trans(U32, U32{Word.xor(32n, a, Word.and(32n, wones(32n), Word.xor(32n, a, b)))}, U32{Word.xor(32n, a, Word.xor(32n, a, b))}, U32{b},
        Equal.cong(Word(32n), U32, w => U32{Word.xor(32n, a, w)}, Word.and(32n, wones(32n), Word.xor(32n, a, b)), Word.xor(32n, a, b), wand1(32n, Word.xor(32n, a, b))),
        Equal.cong(Word(32n), U32, w => U32{w}, Word.xor(32n, a, Word.xor(32n, a, b)), b, wxor2(32n, a, b)))

law sel0:
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  for +h: {V.len(a) == V.len(b) : Nat}
  {Li.select(0, a, b) == a : List<&2, U32>}

def sel0(a, b, h):
  match a b:
    case Nil{} Nil{}: {==}
    case Nil{} y <> bt: Empty.absurd({Li.select(0, [], y <> bt) == [] : List<&2, U32>}, N.zero_succ(V.len(bt), h))
    case x <> at Nil{}: Empty.absurd({Li.select(0, x <> at, []) == x <> at : List<&2, U32>}, N.succ_zero(V.len(at), h))
    case x <> at y <> bt:
      Equal.trans(List<&2, U32>, Li.pick(0, x, y) <> Li.select(0, at, bt), x <> Li.select(0, at, bt), x <> at,
        Equal.cong(U32, List<&2, U32>, z => z <> Li.select(0, at, bt), Li.pick(0, x, y), x, pick0(x, y)),
        Equal.cong(List<&2, U32>, List<&2, U32>, z => x <> z, Li.select(0, at, bt), at, sel0(at, bt, N.succ_inj(V.len(at), V.len(bt), h))))

law sel1:
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  for +h: {V.len(a) == V.len(b) : Nat}
  {Li.select(4294967295, a, b) == b : List<&2, U32>}

def sel1(a, b, h):
  match a b:
    case Nil{} Nil{}: {==}
    case Nil{} y <> bt: Empty.absurd({Li.select(4294967295, [], y <> bt) == y <> bt : List<&2, U32>}, N.zero_succ(V.len(bt), h))
    case x <> at Nil{}: Empty.absurd({Li.select(4294967295, x <> at, []) == [] : List<&2, U32>}, N.succ_zero(V.len(at), h))
    case x <> at y <> bt:
      Equal.trans(List<&2, U32>, Li.pick(4294967295, x, y) <> Li.select(4294967295, at, bt), y <> Li.select(4294967295, at, bt), y <> bt,
        Equal.cong(U32, List<&2, U32>, z => z <> Li.select(4294967295, at, bt), Li.pick(4294967295, x, y), y, pick1(x, y)),
        Equal.cong(List<&2, U32>, List<&2, U32>, z => y <> z, Li.select(4294967295, at, bt), bt, sel1(at, bt, N.succ_inj(V.len(at), V.len(bt), h))))

law len_take_eq:
  for +n: Nat
  for +xs: List<&2, U32>
  for +h: {Nat.is_le(n, V.len(xs)) == True{} : Bool}
  {V.len(Li.take(n, xs)) == n : Nat}

def len_take_eq(n, xs, h):
  match n xs:
    case 0n _: {==}
    case 1n+k Nil{}: Empty.absurd({V.len(Li.take(1n+k, [])) == 1n+k : Nat}, L.false_true(h))
    case 1n+k x <> t: Equal.cong(Nat, Nat, z => 1n+z, V.len(Li.take(k, t)), k, len_take_eq(k, t, h))
