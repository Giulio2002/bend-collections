import Base
import ../../src/lru/fast.bend as F
import ../../src/lru/wide.bend as W
import ../../src/lru/time.bend as Time
import ../../types/lru_model.bend as T
import ./num/numeric.bend as N

def assoc(+a: Bool, +b: Bool, +c: Bool) -> {Bool.and(a, Bool.and(b, c)) == Bool.and(Bool.and(a, b), c) : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

def zero_join(n: Nat, +m: Nat, a: Word(n), +b: Word(m)) -> {W.is_zero(Nat.add(n,m), W.join(n,m,a,b)) == Bool.and(W.is_zero(n,a), W.is_zero(m,b)) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+ +p:
      match a:
        case WCon{+h, +tail}:
          Equal.trans(Bool, Bool.and(Bool.not(h), W.is_zero(Nat.add(p,m), W.join(p,m,tail,b))), Bool.and(Bool.not(h), Bool.and(W.is_zero(p,tail), W.is_zero(m,b))), Bool.and(Bool.and(Bool.not(h), W.is_zero(p,tail)), W.is_zero(m,b)), Equal.cong(Bool, Bool, x => Bool.and(Bool.not(h), x), W.is_zero(Nat.add(p,m), W.join(p,m,tail,b)), Bool.and(W.is_zero(p,tail), W.is_zero(m,b)), zero_join(p,m,tail,b)), assoc(Bool.not(h), W.is_zero(p,tail), W.is_zero(m,b)))

def zero_stamp(+s: F.Stamp) -> {F.stamp_zero(s) == Time.is_zero(F.stamp_int(s)) : Bool}:
  match s:
    case F.ST{U32{+lo}, U32{+hi}}:
      Equal.trans(Bool, Bool.and(U32.is_zero(U32{lo}), U32.is_zero(U32{hi})), Bool.and(W.is_zero(32n,lo), W.is_zero(32n,hi)), W.is_zero(64n,W.join(32n,32n,lo,hi)),
        Equal.trans(Bool, Bool.and(U32.is_zero(U32{lo}), U32.is_zero(U32{hi})), Bool.and(W.is_zero(32n,lo), U32.is_zero(U32{hi})), Bool.and(W.is_zero(32n,lo), W.is_zero(32n,hi)), Equal.cong(Bool,Bool,x => Bool.and(x,U32.is_zero(U32{hi})), U32.is_zero(U32{lo}), W.is_zero(32n,lo), N.zero_comparison_correspondence(32n,lo)), Equal.cong(Bool,Bool,x => Bool.and(W.is_zero(32n,lo),x), U32.is_zero(U32{hi}), W.is_zero(32n,hi), N.zero_comparison_correspondence(32n,hi))),
        Equal.sym(Bool,W.is_zero(64n,W.join(32n,32n,lo,hi)),Bool.and(W.is_zero(32n,lo),W.is_zero(32n,hi)),zero_join(32n,32n,lo,hi)))

def stamp_parts(parts: W.Parts<32n,32n>) -> {F.stamp_int(F.of_pair(W.limbs(parts))) == T.I64{N.rejoin(32n,32n,parts)} : T.Int64}:
  match parts:
    case W.Split{lo,hi}:
      {==}

def stamp_iso(t: T.Int64) -> {F.stamp_int(F.int_stamp(t)) == t : T.Int64}:
  match t:
    case T.I64{+w}:
      Equal.trans(T.Int64, F.stamp_int(F.of_pair(W.limbs(W.split(32n,32n,w)))), T.I64{N.rejoin(32n,32n,W.split(32n,32n,w))}, T.I64{w}, stamp_parts(W.split(32n,32n,w)), Equal.cong(Word(64n), T.Int64, x => T.I64{x}, N.rejoin(32n,32n,W.split(32n,32n,w)), w, N.join_split(32n,32n,w)))

def zero_int(+ns: T.Int64) -> {F.stamp_zero(F.int_stamp(ns)) == Time.is_zero(ns) : Bool}:
  Equal.trans(Bool, F.stamp_zero(F.int_stamp(ns)), Time.is_zero(F.stamp_int(F.int_stamp(ns))), Time.is_zero(ns), zero_stamp(F.int_stamp(ns)), Equal.cong(T.Int64, Bool, x => Time.is_zero(x), F.stamp_int(F.int_stamp(ns)), ns, stamp_iso(ns)))

def original(~V: Data, f: F.Fast<V>, +ns: T.Int64) -> F.Fast<V>:
  F.F{cap,n,fresh,size,depth,ttl,life,counts,table,kys,ents,ch} = f
  F.F{cap,n,fresh,size,depth,Bool.not(Time.is_zero(ns)),F.int_stamp(ns),counts,table,kys,ents,ch}

def lifetime_ok(~V: Data, f: F.Fast<V>, +ns: T.Int64) -> {F.set_lifetime(~V,f,ns) == original(~V,f,ns) : F.Fast<V>}:
  match f:
    case F.F{cap,n,fresh,size,depth,ttl,life,counts,table,kys,ents,ch}:
      Equal.cong(Bool, F.Fast<V>, x => F.F{cap,n,fresh,size,depth,Bool.not(x),F.int_stamp(ns),counts,table,kys,ents,ch}, F.stamp_zero(F.int_stamp(ns)), Time.is_zero(ns), zero_int(ns))

def lifetime_u32(f: F.Fast<U32>, +ns: T.Int64) -> {F.set_lifetime(~U32,f,ns) == original(~U32,f,ns) : F.Fast<U32>}:
  lifetime_ok(~U32,f,ns)

def lifetime_string(f: F.Fast<String>, +ns: T.Int64) -> {F.set_lifetime(~String,f,ns) == original(~String,f,ns) : F.Fast<String>}:
  lifetime_ok(~String,f,ns)
