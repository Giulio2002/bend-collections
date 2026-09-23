import Base
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../../lib/list.bend as LL
import ../../lib/spec_common.bend as SC
import ./spec.bend as S
import ../../../src/containers/bitset.bend as B
import ./lists.bend as BL

# Bit-level meaning of the native U32 operations used by src/bitset.bend,
# derived from Base's Word definitions (U32 = U32{Word(32n)}, bit 0 first).

def wbits(n: Nat, w: Word(n)) -> List<&2, Bool>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      match w:
        case WCon{b, t}:
          Con{b, wbits(p, t)}

def ubits(x: U32) -> List<&2, Bool>:
  match x:
    case U32{w}:
      wbits(32n, w)

def len_wbits(+n: Nat, +w: Word(n)) -> {SC.length(Bool, wbits(n, w)) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{b, t}:
          N.succ_cong(SC.length(Bool, wbits(p, t)), p, len_wbits(p, t))

def ulen(+x: U32) -> {SC.length(Bool, ubits(x)) == 32n : Nat}:
  match x:
    case U32{w}:
      len_wbits(32n, w)

# ---- bitwise operations are element-wise ----

def w_or(+n: Nat, +a: Word(n), +b: Word(n)) -> {wbits(n, Word.or(n, a, b)) == BL.zipk(B.KOr{}, wbits(n, a), wbits(n, b)) : List<&2, Bool>}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match a b:
        case WCon{x, s} WCon{y, t}:
          LL.cons_cong(Bool, Bool.or(x, y), wbits(p, Word.or(p, s, t)), BL.zipk(B.KOr{}, wbits(p, s), wbits(p, t)), w_or(p, s, t))

def w_and(+n: Nat, +a: Word(n), +b: Word(n)) -> {wbits(n, Word.and(n, a, b)) == BL.zipk(B.KAnd{}, wbits(n, a), wbits(n, b)) : List<&2, Bool>}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match a b:
        case WCon{x, s} WCon{y, t}:
          LL.cons_cong(Bool, Bool.and(x, y), wbits(p, Word.and(p, s, t)), BL.zipk(B.KAnd{}, wbits(p, s), wbits(p, t)), w_and(p, s, t))

def w_diff(+n: Nat, +a: Word(n), +b: Word(n)) -> {wbits(n, Word.and(n, a, Word.not(n, b))) == BL.zipk(B.KDiff{}, wbits(n, a), wbits(n, b)) : List<&2, Bool>}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match a b:
        case WCon{x, s} WCon{y, t}:
          LL.cons_cong(Bool, Bool.and(x, Bool.not(y)), wbits(p, Word.and(p, s, Word.not(p, t))), BL.zipk(B.KDiff{}, wbits(p, s), wbits(p, t)), w_diff(p, s, t))

def w_xor(+n: Nat, +a: Word(n), +b: Word(n)) -> {wbits(n, Word.xor(n, a, b)) == BL.zipk(B.KXor{}, wbits(n, a), wbits(n, b)) : List<&2, Bool>}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match a b:
        case WCon{x, s} WCon{y, t}:
          LL.cons_cong(Bool, Bool.xor(x, y), wbits(p, Word.xor(p, s, t)), BL.zipk(B.KXor{}, wbits(p, s), wbits(p, t)), w_xor(p, s, t))

def u_op(+k: B.WordOp, +a: U32, +b: U32) -> {ubits(B.word_op(k, a, b)) == BL.zipk(k, ubits(a), ubits(b)) : List<&2, Bool>}:
  match k a b:
    case B.KOr{} U32{x} U32{y}:
      w_or(32n, x, y)
    case B.KAnd{} U32{x} U32{y}:
      w_and(32n, x, y)
    case B.KDiff{} U32{x} U32{y}:
      w_diff(32n, x, y)
    case B.KXor{} U32{x} U32{y}:
      w_xor(32n, x, y)

# ---- low bit ----

def and_zero(+n: Nat, +t: Word(n)) -> {Word.and(n, t, Word.zero(n)) == Word.zero(n) : Word(n)}:
  match n:
    case 0n:
      match t:
        case WNil{}:
          {==}
    case 1n+p:
      match t:
        case WCon{True{}, r}:
          %Equal.sym(Word(p), Word.and(p, r, Word.zero(p)), Word.zero(p), and_zero(p, r)) : {WCon{False{}, _} == WCon{False{}, Word.zero(p)} : Word(1n+p)}
          {==}
        case WCon{False{}, r}:
          %Equal.sym(Word(p), Word.and(p, r, Word.zero(p)), Word.zero(p), and_zero(p, r)) : {WCon{False{}, _} == WCon{False{}, Word.zero(p)} : Word(1n+p)}
          {==}

def low_word(+b: Bool, +t: Word(31n)) -> {B.low(U32{WCon{b, t}}) == b : Bool}:
  match b:
    case True{}:
      %Equal.sym(Word(31n), Word.and(31n, t, Word.zero(31n)), Word.zero(31n), and_zero(31n, t)) : {Bool.not(U32.is_eq(U32{WCon{True{}, _}}, 0)) == True{} : Bool}
      {==}
    case False{}:
      %Equal.sym(Word(31n), Word.and(31n, t, Word.zero(31n)), Word.zero(31n), and_zero(31n, t)) : {Bool.not(U32.is_eq(U32{WCon{False{}, _}}, 0)) == False{} : Bool}
      {==}

def low_nth(+x: U32) -> {SC.nth(Bool, ubits(x), 0n) == Some{B.low(x)} : Maybe<&2, Bool>}:
  match x:
    case U32{w}:
      match w:
        case WCon{b, t}:
          %Equal.sym(Bool, B.low(U32{WCon{b, t}}), b, low_word(b, t)) : {Some{b} == Some{_} : Maybe<&2, Bool>}
          {==}

# ---- shifts ----

def pad(+n: Nat, +w: Word(n)) -> {wbits(1n+n, Word.shr.pad(n, w)) == SC.snoc(Bool, wbits(n, w), False{}) : List<&2, Bool>}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{b, t}:
          LL.cons_cong(Bool, b, wbits(1n+p, Word.shr.pad(p, t)), SC.snoc(Bool, wbits(p, t), False{}), pad(p, t))

def u_shr(+b: Bool, +t: Word(31n)) -> {ubits(U32.shr(U32{WCon{b, t}})) == SC.snoc(Bool, wbits(31n, t), False{}) : List<&2, Bool>}:
  pad(31n, t)

def shr_nth(+x: U32, +j: Nat, +h: {Nat.is_lt(j, 31n) == True{} : Bool}) -> {SC.nth(Bool, ubits(U32.shr(x)), j) == SC.nth(Bool, ubits(x), 1n+j) : Maybe<&2, Bool>}:
  match x:
    case U32{w}:
      match w:
        case WCon{b, t}:
          %Equal.sym(List<&2, Bool>, ubits(U32.shr(U32{WCon{b, t}})), SC.snoc(Bool, wbits(31n, t), False{}), u_shr(b, t)) : {SC.nth(Bool, _, j) == SC.nth(Bool, wbits(31n, t), j) : Maybe<&2, Bool>}
          %Equal.sym(List<&2, Bool>, SC.snoc(Bool, wbits(31n, t), False{}), SC.append(Bool, wbits(31n, t), Con{False{}, Nil{}}), LL.snoc_append(Bool, wbits(31n, t), False{})) : {SC.nth(Bool, _, j) == SC.nth(Bool, wbits(31n, t), j) : Maybe<&2, Bool>}
          LL.nth_append_left(Bool, wbits(31n, t), Con{False{}, Nil{}}, j, L.subst(Nat, x => {Nat.is_lt(j, x) == True{} : Bool}, 31n, SC.length(Bool, wbits(31n, t)), Equal.sym(Nat, SC.length(Bool, wbits(31n, t)), 31n, len_wbits(31n, t)), h))

def shrn_nth(+k: Nat, +x: U32, +j: Nat, +h: {Nat.is_lt(Nat.add(j, k), 32n) == True{} : Bool}) -> {SC.nth(Bool, ubits(U32.shrn(x, k)), j) == SC.nth(Bool, ubits(x), Nat.add(j, k)) : Maybe<&2, Bool>}:
  match k:
    case 0n:
      %Equal.sym(Nat, Nat.add(j, 0n), j, N.add_zero(j)) : {SC.nth(Bool, ubits(x), j) == SC.nth(Bool, ubits(x), _) : Maybe<&2, Bool>}
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.add(j, 1n+p), 1n+Nat.add(j, p), N.add_succ(j, p)) : {SC.nth(Bool, ubits(U32.shr(U32.shrn(x, p))), j) == SC.nth(Bool, ubits(x), _) : Maybe<&2, Bool>}
      +h1 = L.subst(Nat, v => {Nat.is_lt(v, 32n) == True{} : Bool}, Nat.add(j, 1n+p), 1n+Nat.add(j, p), N.add_succ(j, p), h)
      Equal.trans(Maybe<&2, Bool>, SC.nth(Bool, ubits(U32.shr(U32.shrn(x, p))), j), SC.nth(Bool, ubits(U32.shrn(x, p)), 1n+j), SC.nth(Bool, ubits(x), 1n+Nat.add(j, p)),
        shr_nth(U32.shrn(x, p), j, N.le_lt_trans(j, Nat.add(j, p), 31n, N.le_add_right(j, p), h1)),
        shrn_nth(p, x, 1n+j, h1))

def word_get(+w: U32, +k: Nat, +h: {Nat.is_lt(k, 32n) == True{} : Bool}) -> {Some{B.word_get(w, k)} == SC.nth(Bool, ubits(w), k) : Maybe<&2, Bool>}:
  Equal.trans(Maybe<&2, Bool>, Some{B.low(U32.shrn(w, k))}, SC.nth(Bool, ubits(U32.shrn(w, k)), 0n), SC.nth(Bool, ubits(w), k),
    Equal.sym(Maybe<&2, Bool>, SC.nth(Bool, ubits(U32.shrn(w, k)), 0n), Some{B.low(U32.shrn(w, k))}, low_nth(U32.shrn(w, k))),
    shrn_nth(k, w, 0n, h))

def shl_put(+n: Nat, +c: Bool, +w: Word(n)) -> {wbits(n, Word.shl.put(n, c, w)) == SC.take(Bool, Con{c, wbits(n, w)}, n) : List<&2, Bool>}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{b, t}:
          LL.cons_cong(Bool, c, wbits(p, Word.shl.put(p, b, t)), SC.take(Bool, Con{b, wbits(p, t)}, p), shl_put(p, b, t))

def u_shl(+x: U32) -> {ubits(U32.shl(x)) == SC.take(Bool, Con{False{}, ubits(x)}, 32n) : List<&2, Bool>}:
  match x:
    case U32{w}:
      match w:
        case WCon{b, t}:
          LL.cons_cong(Bool, False{}, wbits(31n, Word.shl.put(31n, b, t)), SC.take(Bool, Con{b, wbits(31n, t)}, 31n), shl_put(31n, b, t))

# 1 << k is the one-hot mask for bit k.
def onehot(+k: Nat, +h: {Nat.is_lt(k, 32n) == True{} : Bool}) -> {ubits(U32.shln(1, k)) == SC.update(Bool, BL.rep(32n), k, True{}) : List<&2, Bool>}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      +hp = N.lt_trans(p, 1n+p, 32n, N.lt_succ(p), h)
      %Equal.sym(List<&2, Bool>, ubits(U32.shl(U32.shln(1, p))), SC.take(Bool, Con{False{}, ubits(U32.shln(1, p))}, 32n), u_shl(U32.shln(1, p))) : {_ == SC.update(Bool, BL.rep(32n), 1n+p, True{}) : List<&2, Bool>}
      %Equal.sym(List<&2, Bool>, ubits(U32.shln(1, p)), SC.update(Bool, BL.rep(32n), p, True{}), onehot(p, hp)) : {SC.take(Bool, Con{False{}, _}, 32n) == SC.update(Bool, BL.rep(32n), 1n+p, True{}) : List<&2, Bool>}
      LL.cons_cong(Bool, False{}, SC.take(Bool, SC.update(Bool, BL.rep(32n), p, True{}), 31n), SC.update(Bool, BL.rep(31n), p, True{}), BL.take_onehot(31n, p, h))

def word_put(+v: Bool, +w: U32, +k: Nat, +h: {Nat.is_lt(k, 32n) == True{} : Bool}) -> {ubits(B.word_put(v, w, k)) == SC.update(Bool, ubits(w), k, v) : List<&2, Bool>}:
  match v:
    case True{}:
      %Equal.sym(List<&2, Bool>, ubits(B.word_op(B.KOr{}, w, U32.shln(1, k))), BL.zipk(B.KOr{}, ubits(w), ubits(U32.shln(1, k))), u_op(B.KOr{}, w, U32.shln(1, k))) : {_ == SC.update(Bool, ubits(w), k, True{}) : List<&2, Bool>}
      %Equal.sym(List<&2, Bool>, ubits(U32.shln(1, k)), SC.update(Bool, BL.rep(32n), k, True{}), onehot(k, h)) : {BL.zipk(B.KOr{}, ubits(w), _) == SC.update(Bool, ubits(w), k, True{}) : List<&2, Bool>}
      %ulen(w) : {BL.zipk(B.KOr{}, ubits(w), SC.update(Bool, BL.rep(_), k, True{})) == SC.update(Bool, ubits(w), k, True{}) : List<&2, Bool>}
      BL.or_onehot(ubits(w), k)
    case False{}:
      %Equal.sym(List<&2, Bool>, ubits(B.word_op(B.KDiff{}, w, U32.shln(1, k))), BL.zipk(B.KDiff{}, ubits(w), ubits(U32.shln(1, k))), u_op(B.KDiff{}, w, U32.shln(1, k))) : {_ == SC.update(Bool, ubits(w), k, False{}) : List<&2, Bool>}
      %Equal.sym(List<&2, Bool>, ubits(U32.shln(1, k)), SC.update(Bool, BL.rep(32n), k, True{}), onehot(k, h)) : {BL.zipk(B.KDiff{}, ubits(w), _) == SC.update(Bool, ubits(w), k, False{}) : List<&2, Bool>}
      %ulen(w) : {BL.zipk(B.KDiff{}, ubits(w), SC.update(Bool, BL.rep(_), k, True{})) == SC.update(Bool, ubits(w), k, False{}) : List<&2, Bool>}
      BL.diff_onehot(ubits(w), k)

# ---- counting and enumeration by repeated shifting ----

def word_count(+m: Nat, +x: U32) -> {B.word_count(m, x) == S.count(SC.take(Bool, ubits(x), m)) : Nat}:
  match m x:
    case 0n U32{w}:
      match w:
        case WCon{b, t}:
          {==}
    case 1n+p U32{w}:
      match w:
        case WCon{True{}, t}:
          %Equal.sym(Bool, B.low(U32{WCon{True{}, t}}), True{}, low_word(True{}, t)) : {Nat.add(B.bit_value(_), B.word_count(p, U32.shr(U32{WCon{True{}, t}}))) == 1n+S.count(SC.take(Bool, wbits(31n, t), p)) : Nat}
          %Equal.sym(Nat, B.word_count(p, U32.shr(U32{WCon{True{}, t}})), S.count(SC.take(Bool, ubits(U32.shr(U32{WCon{True{}, t}})), p)), word_count(p, U32.shr(U32{WCon{True{}, t}}))) : {1n+_ == 1n+S.count(SC.take(Bool, wbits(31n, t), p)) : Nat}
          %Equal.sym(List<&2, Bool>, ubits(U32.shr(U32{WCon{True{}, t}})), SC.snoc(Bool, wbits(31n, t), False{}), u_shr(True{}, t)) : {1n+S.count(SC.take(Bool, _, p)) == 1n+S.count(SC.take(Bool, wbits(31n, t), p)) : Nat}
          N.succ_cong(S.count(SC.take(Bool, SC.snoc(Bool, wbits(31n, t), False{}), p)), S.count(SC.take(Bool, wbits(31n, t), p)), BL.count_take_snoc(wbits(31n, t), p))
        case WCon{False{}, t}:
          %Equal.sym(Bool, B.low(U32{WCon{False{}, t}}), False{}, low_word(False{}, t)) : {Nat.add(B.bit_value(_), B.word_count(p, U32.shr(U32{WCon{False{}, t}}))) == S.count(SC.take(Bool, wbits(31n, t), p)) : Nat}
          %Equal.sym(Nat, B.word_count(p, U32.shr(U32{WCon{False{}, t}})), S.count(SC.take(Bool, ubits(U32.shr(U32{WCon{False{}, t}})), p)), word_count(p, U32.shr(U32{WCon{False{}, t}}))) : {_ == S.count(SC.take(Bool, wbits(31n, t), p)) : Nat}
          %Equal.sym(List<&2, Bool>, ubits(U32.shr(U32{WCon{False{}, t}})), SC.snoc(Bool, wbits(31n, t), False{}), u_shr(False{}, t)) : {S.count(SC.take(Bool, _, p)) == S.count(SC.take(Bool, wbits(31n, t), p)) : Nat}
          BL.count_take_snoc(wbits(31n, t), p)

def word_members(+m: Nat, +x: U32, +off: Nat, +rest: List<&2, Nat>) -> {B.word_members(m, x, off, rest) == SC.append(Nat, S.members(SC.take(Bool, ubits(x), m), off), rest) : List<&2, Nat>}:
  match m x:
    case 0n U32{w}:
      match w:
        case WCon{b, t}:
          {==}
    case 1n+p U32{w}:
      match w:
        case WCon{True{}, t}:
          %Equal.sym(Bool, B.low(U32{WCon{True{}, t}}), True{}, low_word(True{}, t)) : {B.member_pick(_, off, B.word_members(p, U32.shr(U32{WCon{True{}, t}}), 1n+off, rest)) == Con{off, SC.append(Nat, S.members(SC.take(Bool, wbits(31n, t), p), 1n+off), rest)} : List<&2, Nat>}
          %Equal.sym(List<&2, Nat>, B.word_members(p, U32.shr(U32{WCon{True{}, t}}), 1n+off, rest), SC.append(Nat, S.members(SC.take(Bool, ubits(U32.shr(U32{WCon{True{}, t}})), p), 1n+off), rest), word_members(p, U32.shr(U32{WCon{True{}, t}}), 1n+off, rest)) : {Con{off, _} == Con{off, SC.append(Nat, S.members(SC.take(Bool, wbits(31n, t), p), 1n+off), rest)} : List<&2, Nat>}
          %Equal.sym(List<&2, Bool>, ubits(U32.shr(U32{WCon{True{}, t}})), SC.snoc(Bool, wbits(31n, t), False{}), u_shr(True{}, t)) : {Con{off, SC.append(Nat, S.members(SC.take(Bool, _, p), 1n+off), rest)} == Con{off, SC.append(Nat, S.members(SC.take(Bool, wbits(31n, t), p), 1n+off), rest)} : List<&2, Nat>}
          %Equal.sym(List<&2, Nat>, S.members(SC.take(Bool, SC.snoc(Bool, wbits(31n, t), False{}), p), 1n+off), S.members(SC.take(Bool, wbits(31n, t), p), 1n+off), BL.members_take_snoc(wbits(31n, t), p, 1n+off)) : {Con{off, SC.append(Nat, _, rest)} == Con{off, SC.append(Nat, S.members(SC.take(Bool, wbits(31n, t), p), 1n+off), rest)} : List<&2, Nat>}
          {==}
        case WCon{False{}, t}:
          %Equal.sym(Bool, B.low(U32{WCon{False{}, t}}), False{}, low_word(False{}, t)) : {B.member_pick(_, off, B.word_members(p, U32.shr(U32{WCon{False{}, t}}), 1n+off, rest)) == SC.append(Nat, S.members(SC.take(Bool, wbits(31n, t), p), 1n+off), rest) : List<&2, Nat>}
          %Equal.sym(List<&2, Nat>, B.word_members(p, U32.shr(U32{WCon{False{}, t}}), 1n+off, rest), SC.append(Nat, S.members(SC.take(Bool, ubits(U32.shr(U32{WCon{False{}, t}})), p), 1n+off), rest), word_members(p, U32.shr(U32{WCon{False{}, t}}), 1n+off, rest)) : {_ == SC.append(Nat, S.members(SC.take(Bool, wbits(31n, t), p), 1n+off), rest) : List<&2, Nat>}
          %Equal.sym(List<&2, Bool>, ubits(U32.shr(U32{WCon{False{}, t}})), SC.snoc(Bool, wbits(31n, t), False{}), u_shr(False{}, t)) : {SC.append(Nat, S.members(SC.take(Bool, _, p), 1n+off), rest) == SC.append(Nat, S.members(SC.take(Bool, wbits(31n, t), p), 1n+off), rest) : List<&2, Nat>}
          %Equal.sym(List<&2, Nat>, S.members(SC.take(Bool, SC.snoc(Bool, wbits(31n, t), False{}), p), 1n+off), S.members(SC.take(Bool, wbits(31n, t), p), 1n+off), BL.members_take_snoc(wbits(31n, t), p, 1n+off)) : {SC.append(Nat, _, rest) == SC.append(Nat, S.members(SC.take(Bool, wbits(31n, t), p), 1n+off), rest) : List<&2, Nat>}
          {==}
