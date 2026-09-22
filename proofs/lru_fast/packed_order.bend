import Base
import ../../src/lru/fast.bend as F
import ../../src/lru/wide.bend as W
import ../../src/lru/time.bend as Time
import ./packed_zero.bend as Z

def order_zero(c: Cmp) -> {F.stamp_order(c, EQ{}) == c : Cmp}:
  match c:
    case LT{}: {==}
    case EQ{}: {==}
    case GT{}: {==}

def order_bit(+a: Bool, +b: Bool, high: Cmp, +low: Cmp) -> {Word.cmp.fin(a,b,F.stamp_order(high,low)) == F.stamp_order(high,Word.cmp.fin(a,b,low)) : Cmp}:
  match high:
    case LT{}: {==}
    case EQ{}: {==}
    case GT{}: {==}

def cmp_join(n: Nat, +m: Nat, a: Word(n), +ah: Word(m), b: Word(n), +bh: Word(m)) -> {Word.cmp(Nat.add(n,m),W.join(n,m,a,ah),W.join(n,m,b,bh)) == F.stamp_order(Word.cmp(m,ah,bh),Word.cmp(n,a,b)) : Cmp}:
  match n:
    case 0n:
      Equal.sym(Cmp,F.stamp_order(Word.cmp(m,ah,bh),EQ{}),Word.cmp(m,ah,bh),order_zero(Word.cmp(m,ah,bh)))
    case 1n+ +p:
      match a b:
        case WCon{+ab,+at} WCon{+bb,+bt}:
          Equal.trans(Cmp,Word.cmp.fin(ab,bb,Word.cmp(Nat.add(p,m),W.join(p,m,at,ah),W.join(p,m,bt,bh))),Word.cmp.fin(ab,bb,F.stamp_order(Word.cmp(m,ah,bh),Word.cmp(p,at,bt))),F.stamp_order(Word.cmp(m,ah,bh),Word.cmp.fin(ab,bb,Word.cmp(p,at,bt))),Equal.cong(Cmp,Cmp,x => Word.cmp.fin(ab,bb,x),Word.cmp(Nat.add(p,m),W.join(p,m,at,ah),W.join(p,m,bt,bh)),F.stamp_order(Word.cmp(m,ah,bh),Word.cmp(p,at,bt)),cmp_join(p,m,at,ah,bt,bh)),order_bit(ab,bb,Word.cmp(m,ah,bh),Word.cmp(p,at,bt)))

def sign_mask(n: Nat) -> Word(1n+n):
  match n:
    case 0n: WCon{True{},WNil{}}
    case 1n+p: WCon{False{},sign_mask(p)}

def ge_bit(a: Bool, c: Cmp) -> {Cmp.is_ge(Word.cmp.fin(a,False{},c)) == Cmp.is_ge(c) : Bool}:
  match a c:
    case False{} LT{}: {==}
    case False{} EQ{}: {==}
    case False{} GT{}: {==}
    case True{} LT{}: {==}
    case True{} EQ{}: {==}
    case True{} GT{}: {==}

def sign_word(n: Nat, w: Word(1n+n)) -> {Cmp.is_ge(Word.cmp(1n+n,w,sign_mask(n))) == W.last(1n+n,w) : Bool}:
  match n:
    case 0n:
      match w:
        case WCon{False{},WNil{}}: {==}
        case WCon{True{},WNil{}}: {==}
    case 1n+ +p:
      match w:
        case WCon{+b,+t}:
          Equal.trans(Bool,Cmp.is_ge(Word.cmp.fin(b,False{},Word.cmp(1n+p,t,sign_mask(p)))),Cmp.is_ge(Word.cmp(1n+p,t,sign_mask(p))),W.last(1n+p,t),ge_bit(b,Word.cmp(1n+p,t,sign_mask(p))),sign_word(p,t))

def word_pair(x: U32) -> Word(32n) & Unit:
  U32{w} = x
  (w,Unit{})

def sign_u32(+x: U32) -> {U32.is_ge(x,2147483648) == W.last(32n,Pair.fst(Word(32n),Unit,word_pair(x))) : Bool}:
  match x:
    case U32{w}:
      sign_word(31n,w)

def joined_sign(+lo: U32, +hi: U32) -> {W.last(64n,W.pack(lo,hi)) == W.last(32n,Pair.fst(Word(32n),Unit,word_pair(hi))) : Bool}:
  match lo hi:
    case U32{WCon{b0,WCon{b1,WCon{b2,WCon{b3,WCon{b4,WCon{b5,WCon{b6,WCon{b7,WCon{b8,WCon{b9,WCon{b10,WCon{b11,WCon{b12,WCon{b13,WCon{b14,WCon{b15,WCon{b16,WCon{b17,WCon{b18,WCon{b19,WCon{b20,WCon{b21,WCon{b22,WCon{b23,WCon{b24,WCon{b25,WCon{b26,WCon{b27,WCon{b28,WCon{b29,WCon{b30,WCon{b31,WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{bits}:
      {==}

def sign_pack(+lo: U32, +hi: U32) -> {U32.is_ge(hi,2147483648) == W.last(64n,W.pack(lo,hi)) : Bool}:
  Equal.trans(Bool,U32.is_ge(hi,2147483648),W.last(32n,Pair.fst(Word(32n),Unit,word_pair(hi))),W.last(64n,W.pack(lo,hi)),sign_u32(hi),Equal.sym(Bool,W.last(64n,W.pack(lo,hi)),W.last(32n,Pair.fst(Word(32n),Unit,word_pair(hi))),joined_sign(lo,hi)))

def order_pack(+al: U32, +ah: U32, +bl: U32, +bh: U32) -> {F.stamp_order(U32.cmp(ah,bh),U32.cmp(al,bl)) == Word.cmp(64n,W.pack(al,ah),W.pack(bl,bh)) : Cmp}:
  match al ah bl bh:
    case U32{+a} U32{+aa} U32{+b} U32{+bb}:
      Equal.sym(Cmp,Word.cmp(64n,W.join(32n,32n,a,aa),W.join(32n,32n,b,bb)),F.stamp_order(Word.cmp(32n,aa,bb),Word.cmp(32n,a,b)),cmp_join(32n,32n,a,aa,b,bb))

def signed_body(+al: U32, +ah: U32, +bl: U32, +bh: U32, +sa: Bool, +sb: Bool) -> {F.stamp_signed(al,ah,bl,bh,sa,sb) == W.signed_order(W.pack(al,ah),W.pack(bl,bh),sa,sb) : Bool}:
  match sa sb:
    case True{} False{}: {==}
    case False{} True{}: {==}
    case False{} False{}:
      Equal.cong(Cmp,Bool,x => Cmp.is_le(x),F.stamp_order(U32.cmp(ah,bh),U32.cmp(al,bl)),Word.cmp(64n,W.pack(al,ah),W.pack(bl,bh)),order_pack(al,ah,bl,bh))
    case True{} True{}:
      Equal.cong(Cmp,Bool,x => Cmp.is_le(x),F.stamp_order(U32.cmp(ah,bh),U32.cmp(al,bl)),Word.cmp(64n,W.pack(al,ah),W.pack(bl,bh)),order_pack(al,ah,bl,bh))

def le_ok(+a: F.Stamp, +b: F.Stamp) -> {F.stamp_le(a,b) == Time.le(F.stamp_int(a),F.stamp_int(b)) : Bool}:
  match a b:
    case F.ST{+al,+ah} F.ST{+bl,+bh}:
      Equal.trans(Bool,F.stamp_signed(al,ah,bl,bh,U32.is_ge(ah,2147483648),U32.is_ge(bh,2147483648)),W.signed_order(W.pack(al,ah),W.pack(bl,bh),U32.is_ge(ah,2147483648),U32.is_ge(bh,2147483648)),W.le(W.pack(al,ah),W.pack(bl,bh)),signed_body(al,ah,bl,bh,U32.is_ge(ah,2147483648),U32.is_ge(bh,2147483648)),
        Equal.trans(Bool,W.signed_order(W.pack(al,ah),W.pack(bl,bh),U32.is_ge(ah,2147483648),U32.is_ge(bh,2147483648)),W.signed_order(W.pack(al,ah),W.pack(bl,bh),W.last(64n,W.pack(al,ah)),U32.is_ge(bh,2147483648)),W.le(W.pack(al,ah),W.pack(bl,bh)),Equal.cong(Bool,Bool,x => W.signed_order(W.pack(al,ah),W.pack(bl,bh),x,U32.is_ge(bh,2147483648)),U32.is_ge(ah,2147483648),W.last(64n,W.pack(al,ah)),sign_pack(al,ah)),Equal.cong(Bool,Bool,x => W.signed_order(W.pack(al,ah),W.pack(bl,bh),W.last(64n,W.pack(al,ah)),x),U32.is_ge(bh,2147483648),W.last(64n,W.pack(bl,bh)),sign_pack(bl,bh))))

def expired_choose_ok(+deadline: F.Stamp, +now: F.Stamp, +immortal: Bool) -> {F.stamp_expired_choose(deadline,now,immortal) == Time.expired_choose(F.stamp_int(deadline),F.stamp_int(now),immortal) : Bool}:
  match immortal:
    case True{}: {==}
    case False{}: le_ok(deadline,now)

def expired_ok(+deadline: F.Stamp, +now: F.Stamp) -> {F.stamp_expired(deadline,now) == Time.expired(F.stamp_int(deadline),F.stamp_int(now)) : Bool}:
  Equal.trans(Bool,F.stamp_expired(deadline,now),Time.expired_choose(F.stamp_int(deadline),F.stamp_int(now),F.stamp_zero(deadline)),Time.expired(F.stamp_int(deadline),F.stamp_int(now)),expired_choose_ok(deadline,now,F.stamp_zero(deadline)),Equal.cong(Bool,Bool,x => Time.expired_choose(F.stamp_int(deadline),F.stamp_int(now),x),F.stamp_zero(deadline),Time.is_zero(F.stamp_int(deadline)),Z.zero_stamp(deadline)))

# These bridge the actual changed read/expiry helpers, not just a standalone comparator.
def old_read_slot(~V: Data, f: F.Fast<V>, +slot: U32, now: F.Stamp, +tracked: Bool, entry: F.Slot<V>) -> F.Fast<V> & Maybe<&2,V>:
  match entry:
    case F.Vacant{}: (F.count_read(~V,f,tracked,False{}),None{})
    case F.Live{v}: F.read_live(~V,f,slot,tracked,v)
    case F.Timed{v,d}: F.read_expiry(~V,f,slot,tracked,v,Time.expired(F.stamp_int(d),F.stamp_int(now)))

def read_slot_ok(~V: Data, f: F.Fast<V>, +slot: U32, +now: F.Stamp, +tracked: Bool, +entry: F.Slot<V>) -> {F.read_slot(~V,f,slot,now,tracked,entry) == old_read_slot(~V,f,slot,now,tracked,entry) : F.Fast<V> & Maybe<&2,V>}:
  match entry:
    case F.Vacant{}: {==}
    case F.Live{v}: {==}
    case F.Timed{v,+d}:
      Equal.cong(Bool,F.Fast<V> & Maybe<&2,V>, x => F.read_expiry(~V,f,slot,tracked,v,x),F.stamp_expired(d,now),Time.expired(F.stamp_int(d),F.stamp_int(now)),expired_ok(d,now))

def old_ex_slot(~V: Data, f: F.Fast<V>, +slot: U32, now: F.Stamp, entry: F.Slot<V>) -> F.Fast<V> & Bool:
  match entry:
    case F.Vacant{}: (f,False{})
    case F.Live{v}: (f,False{})
    case F.Timed{v,d}: F.ex_drop(~V,f,slot,Time.expired(F.stamp_int(d),F.stamp_int(now)))

def ex_slot_ok(~V: Data, f: F.Fast<V>, +slot: U32, +now: F.Stamp, +entry: F.Slot<V>) -> {F.ex_slot(~V,f,slot,now,entry) == old_ex_slot(~V,f,slot,now,entry) : F.Fast<V> & Bool}:
  match entry:
    case F.Vacant{}: {==}
    case F.Live{v}: {==}
    case F.Timed{v,+d}:
      Equal.cong(Bool,F.Fast<V> & Bool,x => F.ex_drop(~V,f,slot,x),F.stamp_expired(d,now),Time.expired(F.stamp_int(d),F.stamp_int(now)),expired_ok(d,now))

def read_u32(f: F.Fast<U32>, +slot: U32, +now: F.Stamp, +tracked: Bool, +entry: F.Slot<U32>) -> {F.read_slot(~U32,f,slot,now,tracked,entry) == old_read_slot(~U32,f,slot,now,tracked,entry) : F.Fast<U32> & Maybe<&2,U32>}:
  read_slot_ok(~U32,f,slot,now,tracked,entry)

def ex_u32(f: F.Fast<U32>, +slot: U32, +now: F.Stamp, +entry: F.Slot<U32>) -> {F.ex_slot(~U32,f,slot,now,entry) == old_ex_slot(~U32,f,slot,now,entry) : F.Fast<U32> & Bool}:
  ex_slot_ok(~U32,f,slot,now,entry)

def read_string(f: F.Fast<String>, +slot: U32, +now: F.Stamp, +tracked: Bool, +entry: F.Slot<String>) -> {F.read_slot(~String,f,slot,now,tracked,entry) == old_read_slot(~String,f,slot,now,tracked,entry) : F.Fast<String> & Maybe<&2,String>}:
  read_slot_ok(~String,f,slot,now,tracked,entry)

def ex_string(f: F.Fast<String>, +slot: U32, +now: F.Stamp, +entry: F.Slot<String>) -> {F.ex_slot(~String,f,slot,now,entry) == old_ex_slot(~String,f,slot,now,entry) : F.Fast<String> & Bool}:
  ex_slot_ok(~String,f,slot,now,entry)
