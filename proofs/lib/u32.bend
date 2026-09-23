import Base
import ./logic.bend as L
import ./nat.bend as N
import ../spec/common.bend as SC
import ../lemmas/spec/numeric.bend as S
import ../lemmas/proofs/numeric.bend as RN
import ../lemmas/proofs/nat_algebra.bend as NA
import ../lemmas/proofs/modular_addition.bend as MA
import ../lemmas/proofs/word_value.bend as WV
import ../lemmas/proofs/word_shift.bend as WS
import ../lemmas/proofs/word_comparison.bend as WC
import ../lemmas/proofs/subtraction_bounds.bend as SB

# U32 facts needed by the new structures, derived from the retained LRU word
# interpretation lemmas (reused, not re-derived): unsigned interpretation,
# increment/shift/subtraction/comparison refinement and reconstruction.

def to_nat_word(+w: Word(32n)) -> {U32.to_nat(U32{w}) == S.unsigned(32n, w) : Nat}:
  RN.primitive_word_interpretation(32n, w)

def pow2_scale(+k: Nat) -> {SC.pow2(k) == S.scale_binary(k, 1n) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, Nat.double, SC.pow2(p), S.scale_binary(p, 1n), pow2_scale(p))

def double_pow(+x: Nat) -> {Nat.double(x) == Nat.add(x, Nat.add(x, 0n)) : Nat}:
  %Equal.sym(Nat, Nat.add(x, 0n), x, N.add_zero(x)) : {Nat.double(x) == Nat.add(x, _) : Nat}
  NA.double_self(x)

def pow2_pow(+k: Nat) -> {SC.pow2(k) == Nat.pow(2n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      %pow2_pow(p) : {Nat.double(SC.pow2(p)) == Nat.add(_, Nat.add(_, 0n)) : Nat}
      double_pow(SC.pow2(p))

# Every word is recovered from its unsigned interpretation (reconstruct at 0).
def word_from_unsigned(+w: Word(32n)) -> {S.from_nat(32n, S.unsigned(32n, w)) == w : Word(32n)}:
  %N.add_zero(S.unsigned(32n, w)) : {S.from_nat(32n, _) == w : Word(32n)}
  MA.reconstruct(32n, w, 0n)

def injective(+a: U32, +b: U32, +e: {U32.to_nat(a) == U32.to_nat(b) : Nat}) -> {a == b : U32}:
  match a b:
    case U32{+x} U32{+y}:
      Equal.cong(Word(32n), U32, w => U32{w}, x, y,
        Equal.trans(Word(32n), x, S.from_nat(32n, S.unsigned(32n, x)), y,
          Equal.sym(Word(32n), S.from_nat(32n, S.unsigned(32n, x)), x, word_from_unsigned(x)),
          Equal.trans(Word(32n), S.from_nat(32n, S.unsigned(32n, x)), S.from_nat(32n, S.unsigned(32n, y)), y,
            Equal.cong(Nat, Word(32n), v => S.from_nat(32n, v), S.unsigned(32n, x), S.unsigned(32n, y),
              Equal.trans(Nat, S.unsigned(32n, x), U32.to_nat(U32{x}), S.unsigned(32n, y),
                Equal.sym(Nat, U32.to_nat(U32{x}), S.unsigned(32n, x), to_nat_word(x)),
                Equal.trans(Nat, U32.to_nat(U32{x}), U32.to_nat(U32{y}), S.unsigned(32n, y), e, to_nat_word(y)))),
            word_from_unsigned(y))))

def pow2_le_pow(+n: Nat, +k: Nat, +hk: {Nat.is_le(k, n) == True{} : Bool}) -> {Nat.is_le(SC.pow2(k), Nat.pow(2n, n)) == True{} : Bool}:
  %pow2_pow(n) : {Nat.is_le(SC.pow2(k), _) == True{} : Bool}
  N.pow2_mono(k, n, hk)

def pow2_le_scale(+n: Nat, +k: Nat, +hk: {Nat.is_le(k, n) == True{} : Bool}) -> {Nat.is_le(SC.pow2(k), S.scale_binary(n, 1n)) == True{} : Bool}:
  %pow2_scale(n) : {Nat.is_le(SC.pow2(k), _) == True{} : Bool}
  N.pow2_mono(k, n, hk)

# Width-generic wrappers: bounds are 2^k with k <= n, never a closed 2^32.
def from_nat_value_k(+n: Nat, +k: Nat, +v: Nat, +hk: {Nat.is_le(k, n) == True{} : Bool}, +hv: {Nat.is_lt(v, SC.pow2(k)) == True{} : Bool}) -> {S.unsigned(n, S.from_nat(n, v)) == v : Nat}:
  WV.from_nat_value(n, v, N.lt_le_trans(v, SC.pow2(k), Nat.pow(2n, n), hv, pow2_le_pow(n, k, hk)))

def shl_exact_k(+n: Nat, +k: Nat, +w: Word(n), +hk: {Nat.is_le(k, n) == True{} : Bool}, +h: {Nat.is_lt(Nat.double(S.unsigned(n, w)), SC.pow2(k)) == True{} : Bool}) -> {S.unsigned(n, Word.shl(n, w)) == Nat.double(S.unsigned(n, w)) : Nat}:
  WS.exact(n, w, N.lt_le_trans(Nat.double(S.unsigned(n, w)), SC.pow2(k), S.scale_binary(n, 1n), h, pow2_le_scale(n, k, hk)))

def from_nat_word(+i: Nat, +k: Nat, +hk: {Nat.is_le(k, 32n) == True{} : Bool}, +h: {Nat.is_lt(i, SC.pow2(k)) == True{} : Bool}) -> {U32.from_nat(i) == U32{S.from_nat(32n, i)} : U32}:
  match i:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(U32, U32.from_nat(p), U32{S.from_nat(32n, p)}, from_nat_word(p, k, hk, N.lt_trans(p, 1n+p, SC.pow2(k), N.lt_succ(p), h))) : {U32.inc(_) == U32{S.from_nat(32n, 1n+p)} : U32}
      Equal.cong(Word(32n), U32, w => U32{w}, Word.inc(32n, S.from_nat(32n, p)), S.from_nat(32n, 1n+p),
        Equal.trans(Word(32n), Word.inc(32n, S.from_nat(32n, p)), S.from_nat(32n, 1n+S.unsigned(32n, S.from_nat(32n, p))), S.from_nat(32n, 1n+p),
          MA.increment_refines(32n, S.from_nat(32n, p)),
          Equal.cong(Nat, Word(32n), v => S.from_nat(32n, 1n+v), S.unsigned(32n, S.from_nat(32n, p)), p,
            from_nat_value_k(32n, k, p, hk, N.lt_trans(p, 1n+p, SC.pow2(k), N.lt_succ(p), h)))))

def to_nat_from_nat(+i: Nat, +k: Nat, +hk: {Nat.is_le(k, 32n) == True{} : Bool}, +h: {Nat.is_lt(i, SC.pow2(k)) == True{} : Bool}) -> {U32.to_nat(U32.from_nat(i)) == i : Nat}:
  %Equal.sym(U32, U32.from_nat(i), U32{S.from_nat(32n, i)}, from_nat_word(i, k, hk, h)) : {U32.to_nat(_) == i : Nat}
  Equal.trans(Nat, U32.to_nat(U32{S.from_nat(32n, i)}), S.unsigned(32n, S.from_nat(32n, i)), i, to_nat_word(S.from_nat(32n, i)), from_nat_value_k(32n, k, i, hk, h))

def is_lt_nat(+a: U32, +b: U32) -> {U32.is_lt(a, b) == Nat.is_lt(U32.to_nat(a), U32.to_nat(b)) : Bool}:
  WC.u32_lt(a, b)

def sub_nat(+a: U32, +b: U32, +e: {Nat.is_le(U32.to_nat(b), U32.to_nat(a)) == True{} : Bool}) -> {U32.to_nat(U32.sub(a, b)) == Nat.sub(U32.to_nat(a), U32.to_nat(b)) : Nat}:
  SB.u32_exact(a, b, e)

def WB_unsigned(+n: Nat, +w: Word(n)) -> {Nat.is_lt(S.unsigned(n, w), S.scale_binary(n, 1n)) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{b, t}:
          N.double_lt_bit(b, S.unsigned(p, t), S.scale_binary(p, 1n), WB_unsigned(p, t))

# ---- doubling (shl) and halving (shr) ----

def shl_bound(+w: Word(32n), +k: Nat, +h: {Nat.is_lt(Nat.double(U32.to_nat(U32{w})), SC.pow2(k)) == True{} : Bool}) -> {Nat.is_lt(Nat.double(S.unsigned(32n, w)), SC.pow2(k)) == True{} : Bool}:
  %to_nat_word(w) : {Nat.is_lt(Nat.double(_), SC.pow2(k)) == True{} : Bool}
  h

def shl_value(+x: U32, +k: Nat, +hk: {Nat.is_le(k, 32n) == True{} : Bool}, +h: {Nat.is_lt(Nat.double(U32.to_nat(x)), SC.pow2(k)) == True{} : Bool}) -> {U32.to_nat(U32.shl(x)) == Nat.double(U32.to_nat(x)) : Nat}:
  match x:
    case U32{+w}:
      %Equal.sym(Nat, U32.to_nat(U32{w}), S.unsigned(32n, w), to_nat_word(w)) : {U32.to_nat(U32{Word.shl(32n, w)}) == Nat.double(_) : Nat}
      Equal.trans(Nat, U32.to_nat(U32{Word.shl(32n, w)}), S.unsigned(32n, Word.shl(32n, w)), Nat.double(S.unsigned(32n, w)), to_nat_word(Word.shl(32n, w)),
        shl_exact_k(32n, k, w, hk, shl_bound(w, k, h)))

def pad_value(+n: Nat, +w: Word(n)) -> {S.unsigned(1n+n, Word.shr.pad(n, w)) == S.unsigned(n, w) : Nat}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{b, t}:
          Equal.cong(Nat, Nat, v => Nat.add(S.bit_value(b), Nat.double(v)), S.unsigned(1n+p, Word.shr.pad(p, t)), S.unsigned(p, t), pad_value(p, t))

def low_bit(x: U32) -> Bool:
  match x:
    case U32{w}:
      match w:
        case WCon{b, t}:
          b

def shr_split(+x: U32) -> {U32.to_nat(x) == Nat.add(S.bit_value(low_bit(x)), Nat.double(U32.to_nat(U32.shr(x)))) : Nat}:
  match x:
    case U32{w}:
      match w:
        case WCon{+b, +t}:
          %Equal.sym(Nat, U32.to_nat(U32{WCon{b, t}}), S.unsigned(32n, WCon{b, t}), to_nat_word(WCon{b, t})) : {_ == Nat.add(S.bit_value(b), Nat.double(U32.to_nat(U32{Word.shr.pad(31n, t)}))) : Nat}
          %Equal.sym(Nat, U32.to_nat(U32{Word.shr.pad(31n, t)}), S.unsigned(32n, Word.shr.pad(31n, t)), to_nat_word(Word.shr.pad(31n, t))) : {S.unsigned(32n, WCon{b, t}) == Nat.add(S.bit_value(b), Nat.double(_)) : Nat}
          %Equal.sym(Nat, S.unsigned(32n, Word.shr.pad(31n, t)), S.unsigned(31n, t), pad_value(31n, t)) : {S.unsigned(32n, WCon{b, t}) == Nat.add(S.bit_value(b), Nat.double(_)) : Nat}
          {==}

# 2^d as the U32 built by Base Array.size (1, then shl per level).
def pow2u(d: Nat) -> U32:
  match d:
    case 0n:
      1
    case 1n+p:
      U32.shl(pow2u(p))

def pow2u_shl_bound(+p: Nat, +ih: {U32.to_nat(pow2u(p)) == SC.pow2(p) : Nat}) -> {Nat.is_lt(Nat.double(U32.to_nat(pow2u(p))), SC.pow2(2n+p)) == True{} : Bool}:
  %Equal.sym(Nat, U32.to_nat(pow2u(p)), SC.pow2(p), ih) : {Nat.is_lt(Nat.double(_), SC.pow2(2n+p)) == True{} : Bool}
  N.pow2_lt_succ(1n+p)

def pow2u_value(+d: Nat, +h: {Nat.is_lt(d, 32n) == True{} : Bool}) -> {U32.to_nat(pow2u(d)) == SC.pow2(d) : Nat}:
  match d:
    case 0n:
      {==}
    case 1n+p:
      +ih = pow2u_value(p, N.lt_trans(p, 1n+p, 32n, N.lt_succ(p), h))
      Equal.trans(Nat, U32.to_nat(U32.shl(pow2u(p))), Nat.double(U32.to_nat(pow2u(p))), Nat.double(SC.pow2(p)),
        shl_value(pow2u(p), 2n+p, N.lt_succ_le_succ(1n+p, 32n, h), pow2u_shl_bound(p, ih)),
        Equal.cong(Nat, Nat, Nat.double, U32.to_nat(pow2u(p)), SC.pow2(p), ih))

def shr_pow2u(+p: Nat, +h: {Nat.is_lt(1n+p, 32n) == True{} : Bool}) -> {U32.shr(pow2u(1n+p)) == pow2u(p) : U32}:
  injective(U32.shr(pow2u(1n+p)), pow2u(p),
    Equal.trans(Nat, U32.to_nat(U32.shr(pow2u(1n+p))), SC.pow2(p), U32.to_nat(pow2u(p)),
      N.bit_split_val(low_bit(pow2u(1n+p)), False{}, U32.to_nat(U32.shr(pow2u(1n+p))), SC.pow2(p),
        Equal.trans(Nat, Nat.add(S.bit_value(low_bit(pow2u(1n+p))), Nat.double(U32.to_nat(U32.shr(pow2u(1n+p))))), U32.to_nat(pow2u(1n+p)), Nat.double(SC.pow2(p)),
          Equal.sym(Nat, U32.to_nat(pow2u(1n+p)), Nat.add(S.bit_value(low_bit(pow2u(1n+p))), Nat.double(U32.to_nat(U32.shr(pow2u(1n+p))))), shr_split(pow2u(1n+p))),
          pow2u_value(1n+p, h))),
      Equal.sym(Nat, U32.to_nat(pow2u(p)), SC.pow2(p), pow2u_value(p, N.lt_trans(p, 1n+p, 32n, N.lt_succ(p), h)))))

# ---- low-bit masks ----

def and_true(+b: Bool) -> {Bool.and(b, True{}) == b : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

def lt_one_zero(+v: Nat, +e: {Nat.is_lt(v, 1n) == True{} : Bool}) -> {v == 0n : Nat}:
  match v:
    case 0n:
      {==}
    case 1n+p:
      Empty.absurd({1n+p == 0n : Nat}, N.lt_zero_absurd(p, e))

def and_low_prev(d: Nat) -> Nat:
  match d:
    case 0n:
      0n
    case 1n+k:
      k

def and_low_hy(+m: Nat, +d: Nat, +yb: Bool, +yt: Word(m), +hy: {Nat.add(S.bit_value(yb), Nat.double(S.unsigned(m, yt))) == Nat.sub(SC.pow2(d), 1n) : Nat}) -> {S.unsigned(m, yt) == Nat.sub(SC.pow2(and_low_prev(d)), 1n) : Nat}:
  match d:
    case 0n:
      N.bit_split_val(yb, False{}, S.unsigned(m, yt), 0n, hy)
    case 1n+k:
      N.bit_split_val(yb, True{}, S.unsigned(m, yt), Nat.sub(SC.pow2(k), 1n), Equal.trans(Nat, Nat.add(S.bit_value(yb), Nat.double(S.unsigned(m, yt))), Nat.sub(Nat.double(SC.pow2(k)), 1n), 1n+Nat.double(Nat.sub(SC.pow2(k), 1n)), hy, N.pred_double(SC.pow2(k), N.pow2_pos(k))))

def and_low_hyb(+m: Nat, +d: Nat, +yb: Bool, +yt: Word(m), +hy: {Nat.add(S.bit_value(yb), Nat.double(S.unsigned(m, yt))) == Nat.sub(SC.pow2(d), 1n) : Nat}) -> {yb == Bool.not(N.is_zero(d)) : Bool}:
  match d:
    case 0n:
      N.bit_split_bit(yb, False{}, S.unsigned(m, yt), 0n, hy)
    case 1n+k:
      N.bit_split_bit(yb, True{}, S.unsigned(m, yt), Nat.sub(SC.pow2(k), 1n), Equal.trans(Nat, Nat.add(S.bit_value(yb), Nat.double(S.unsigned(m, yt))), Nat.sub(Nat.double(SC.pow2(k)), 1n), 1n+Nat.double(Nat.sub(SC.pow2(k), 1n)), hy, N.pred_double(SC.pow2(k), N.pow2_pos(k))))

def and_low_hx(+m: Nat, +d: Nat, +xb: Bool, +xt: Word(m), +hx: {Nat.is_lt(Nat.add(S.bit_value(xb), Nat.double(S.unsigned(m, xt))), SC.pow2(d)) == True{} : Bool}) -> {Nat.is_lt(S.unsigned(m, xt), SC.pow2(and_low_prev(d))) == True{} : Bool}:
  match d:
    case 0n:
      %Equal.sym(Nat, S.unsigned(m, xt), 0n, N.bit_split_val(xb, False{}, S.unsigned(m, xt), 0n, lt_one_zero(Nat.add(S.bit_value(xb), Nat.double(S.unsigned(m, xt))), hx))) : {Nat.is_lt(_, 1n) == True{} : Bool}
      {==}
    case 1n+k:
      N.bit_double_lt(xb, S.unsigned(m, xt), SC.pow2(k), hx)

def and_low_hxb(+m: Nat, +xb: Bool, +xt: Word(m), +hx: {Nat.is_lt(Nat.add(S.bit_value(xb), Nat.double(S.unsigned(m, xt))), 1n) == True{} : Bool}) -> {xb == False{} : Bool}:
  N.bit_split_bit(xb, False{}, S.unsigned(m, xt), 0n, lt_one_zero(Nat.add(S.bit_value(xb), Nat.double(S.unsigned(m, xt))), hx))

def and_low_step(+m: Nat, +d: Nat, +xb: Bool, +xt: Word(m), +yb: Bool, +yt: Word(m), +hy: {Nat.add(S.bit_value(yb), Nat.double(S.unsigned(m, yt))) == Nat.sub(SC.pow2(d), 1n) : Nat}, +hx: {Nat.is_lt(Nat.add(S.bit_value(xb), Nat.double(S.unsigned(m, xt))), SC.pow2(d)) == True{} : Bool}, +ih: {Word.and(m, xt, yt) == xt : Word(m)}) -> {WCon{Bool.and(xb, yb), Word.and(m, xt, yt)} == WCon{xb, xt} : Word(1n+m)}:
  match d:
    case 0n:
      %Equal.sym(Word(m), Word.and(m, xt, yt), xt, ih) : {WCon{Bool.and(xb, yb), _} == WCon{xb, xt} : Word(1n+m)}
      %Equal.sym(Bool, yb, False{}, and_low_hyb(m, 0n, yb, yt, hy)) : {WCon{Bool.and(xb, _), xt} == WCon{xb, xt} : Word(1n+m)}
      %Equal.sym(Bool, xb, False{}, and_low_hxb(m, xb, xt, hx)) : {WCon{Bool.and(_, False{}), xt} == WCon{_, xt} : Word(1n+m)}
      {==}
    case 1n+k:
      %Equal.sym(Word(m), Word.and(m, xt, yt), xt, ih) : {WCon{Bool.and(xb, yb), _} == WCon{xb, xt} : Word(1n+m)}
      %Equal.sym(Bool, yb, True{}, and_low_hyb(m, 1n+k, yb, yt, hy)) : {WCon{Bool.and(xb, _), xt} == WCon{xb, xt} : Word(1n+m)}
      %Equal.sym(Bool, Bool.and(xb, True{}), xb, and_true(xb)) : {WCon{_, xt} == WCon{xb, xt} : Word(1n+m)}
      {==}

def and_low(+n: Nat, +d: Nat, +x: Word(n), +y: Word(n), +hy: {S.unsigned(n, y) == Nat.sub(SC.pow2(d), 1n) : Nat}, +hx: {Nat.is_lt(S.unsigned(n, x), SC.pow2(d)) == True{} : Bool}) -> {Word.and(n, x, y) == x : Word(n)}:
  match n:
    case 0n:
      match x y:
        case WNil{} WNil{}:
          {==}
    case 1n+m:
      match x y:
        case WCon{+xb, +xt} WCon{+yb, +yt}:
          and_low_step(m, d, xb, xt, yb, yt, hy, hx, and_low(m, and_low_prev(d), xt, yt, and_low_hy(m, d, yb, yt, hy), and_low_hx(m, d, xb, xt, hx)))

def mask_hx(+wx: Word(32n), +d: Nat, +hx: {Nat.is_lt(U32.to_nat(U32{wx}), SC.pow2(d)) == True{} : Bool}) -> {Nat.is_lt(S.unsigned(32n, wx), SC.pow2(d)) == True{} : Bool}:
  %to_nat_word(wx) : {Nat.is_lt(_, SC.pow2(d)) == True{} : Bool}
  hx

def mask_word(+x: U32, +y: U32, +d: Nat, +hy: {U32.to_nat(y) == Nat.sub(SC.pow2(d), 1n) : Nat}, +hx: {Nat.is_lt(U32.to_nat(x), SC.pow2(d)) == True{} : Bool}) -> {U32.and(x, y) == x : U32}:
  match x y:
    case U32{+wx} U32{+wy}:
      Equal.cong(Word(32n), U32, w => U32{w}, Word.and(32n, wx, wy), wx,
        and_low(32n, d, wx, wy,
          Equal.trans(Nat, S.unsigned(32n, wy), U32.to_nat(U32{wy}), Nat.sub(SC.pow2(d), 1n), Equal.sym(Nat, U32.to_nat(U32{wy}), S.unsigned(32n, wy), to_nat_word(wy)), hy),
          mask_hx(wx, d, hx)))

# Base Array masks every index with size - 1; below the size this is the identity.
def one_le_pow2u(+d: Nat, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}) -> {Nat.is_le(U32.to_nat(1), U32.to_nat(pow2u(d))) == True{} : Bool}:
  %Equal.sym(Nat, U32.to_nat(pow2u(d)), SC.pow2(d), pow2u_value(d, hd)) : {Nat.is_le(1n, _) == True{} : Bool}
  N.pow2_pos(d)

def mask_pow2u(+x: U32, +d: Nat, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hx: {Nat.is_lt(U32.to_nat(x), SC.pow2(d)) == True{} : Bool}) -> {U32.and(x, U32.sub(pow2u(d), 1)) == x : U32}:
  mask_word(x, U32.sub(pow2u(d), 1), d,
    Equal.trans(Nat, U32.to_nat(U32.sub(pow2u(d), 1)), Nat.sub(U32.to_nat(pow2u(d)), 1n), Nat.sub(SC.pow2(d), 1n),
      sub_nat(pow2u(d), 1, one_le_pow2u(d, hd)),
      Equal.cong(Nat, Nat, v => Nat.sub(v, 1n), U32.to_nat(pow2u(d)), SC.pow2(d), pow2u_value(d, hd))),
    hx)

def u32_cmp(+a: U32, +b: U32) -> {U32.cmp(a, b) == Nat.cmp(U32.to_nat(a), U32.to_nat(b)) : Cmp}:
  WC.u32_refines(a, b)

def fin_refl(+c: Cmp, +b: Bool, +h: {Cmp.is_eq(c) == True{} : Bool}) -> {Cmp.is_eq(Word.cmp.fin(b, b, c)) == True{} : Bool}:
  match c b:
    case LT{} _:
      Empty.absurd({Cmp.is_eq(Word.cmp.fin(b, b, LT{})) == True{} : Bool}, L.false_true(h))
    case EQ{} True{}:
      {==}
    case EQ{} False{}:
      {==}
    case GT{} _:
      Empty.absurd({Cmp.is_eq(Word.cmp.fin(b, b, GT{})) == True{} : Bool}, L.false_true(h))

def cmp_refl_eq(+n: Nat, +w: Word(n)) -> {Cmp.is_eq(Word.cmp(n, w, w)) == True{} : Bool}:
  match n w:
    case 0n WNil{}:
      {==}
    case 1n+p WCon{b, t}:
      fin_refl(Word.cmp(p, t, t), b, cmp_refl_eq(p, t))

def u32_eq_refl(+x: U32) -> {U32.is_eq(x, x) == True{} : Bool}:
  match x:
    case U32{w}:
      cmp_refl_eq(32n, w)
