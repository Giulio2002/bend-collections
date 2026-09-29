import Base
import ../../../spec/crypto/aes/poly.bend as P
import ../../../spec/crypto/aes/aes.bend as S

# FIPS 197's inverse (spec/crypto/aes/aes.bend: the byte b with a * b = {01},
# searched among {01}..{ff}) is computed by the same search over the same
# field product, written so that no intermediate value is used twice: the
# reduction's multiplication by x takes the top coefficient and the shifted
# word from one pass (Base's Word.shl.out) instead of reading its argument
# twice. The BendTT kernel has no sharing, so the specification's form, fine
# for the proof checker, costs it exponentially many steps; this one is
# linear, and it is proved equal to the specification's for every input.

def sp(+n: Nat, +low: Word(n), pr: Bool & Word(n)) -> Word(n):
  (hi, sh) = pr
  Word.xor(n, P.wscale(n, hi, low), sh)

def txf(+n: Nat, +low: Word(n), r: Word(n)) -> Word(n):
  sp(n, low, Word.shl.out(n, False{}, r))

def redf(+n: Nat, +low: Word(n), p: List<&2, Bool>) -> Word(n):
  match p:
    case Nil{}: Word.zero(n)
    case c <> q: Word.xor(n, P.constant(n, c), txf(n, low, redf(n, low, q)))

def mulf(+a: U32, +b: U32) -> U32:
  S.byte(redf(8n, S.low(), P.mul(S.bits(a), S.bits(b))))

def searchf(n: Nat, +a: U32, +b: U32) -> U32:
  match n:
    case 0n: 0
    case 1n+p: Bool.pick(U32, U32.is_eq(mulf(a, b), 1), b, searchf(p, a, U32.inc(b)))

law tx_eq:
  for +r: Word(8n)
  {P.times_x(8n, S.low(), r) == txf(8n, S.low(), r) : Word(8n)}

def tx_eq(r):
  match r:
    case WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WNil{}}}}}}}}}: {==}

law red_eq:
  for +p: List<&2, Bool>
  {P.reduce(8n, S.low(), p) == redf(8n, S.low(), p) : Word(8n)}

def red_eq(p):
  match p:
    case Nil{}: {==}
    case c <> q:
      +L = S.low()
      Equal.trans(Word(8n), Word.xor(8n, P.constant(8n, c), P.times_x(8n, L, P.reduce(8n, L, q))), Word.xor(8n, P.constant(8n, c), P.times_x(8n, L, redf(8n, L, q))), Word.xor(8n, P.constant(8n, c), txf(8n, L, redf(8n, L, q))),
        Equal.cong(Word(8n), Word(8n), w => Word.xor(8n, P.constant(8n, c), P.times_x(8n, L, w)), P.reduce(8n, L, q), redf(8n, L, q), red_eq(q)),
        Equal.cong(Word(8n), Word(8n), w => Word.xor(8n, P.constant(8n, c), w), P.times_x(8n, L, redf(8n, L, q)), txf(8n, L, redf(8n, L, q)), tx_eq(redf(8n, L, q))))

law mul_eq:
  for +a: U32
  for +b: U32
  {S.mul(a, b) == mulf(a, b) : U32}

def mul_eq(a, b):
  +p = P.mul(S.bits(a), S.bits(b))
  Equal.cong(Word(8n), U32, w => S.byte(w), P.reduce(8n, S.low(), p), redf(8n, S.low(), p), red_eq(p))

law search_eq:
  for +n: Nat
  for +a: U32
  for +b: U32
  {S.search(n, a, b) == searchf(n, a, b) : U32}

def search_eq(n, a, b):
  match n:
    case 0n: {==}
    case 1n+p:
      Equal.trans(U32, Bool.pick(U32, U32.is_eq(S.mul(a, b), 1), b, S.search(p, a, U32.inc(b))), Bool.pick(U32, U32.is_eq(mulf(a, b), 1), b, S.search(p, a, U32.inc(b))), Bool.pick(U32, U32.is_eq(mulf(a, b), 1), b, searchf(p, a, U32.inc(b))),
        Equal.cong(U32, U32, m => Bool.pick(U32, U32.is_eq(m, 1), b, S.search(p, a, U32.inc(b))), S.mul(a, b), mulf(a, b), mul_eq(a, b)),
        Equal.cong(U32, U32, t => Bool.pick(U32, U32.is_eq(mulf(a, b), 1), b, t), S.search(p, a, U32.inc(b)), searchf(p, a, U32.inc(b)), search_eq(p, a, U32.inc(b))))

law inverse_eq:
  for +a: U32
  {S.inverse(a) == searchf(255n, a, 1) : U32}

def inverse_eq(a):
  search_eq(255n, a, 1)
