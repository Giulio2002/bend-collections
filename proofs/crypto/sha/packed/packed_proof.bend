import Base
import ../../../../src/crypto/sha/packed/core.bend as Runtime
import ./legacy_model.bend as Legacy
import ./packed_array_proof.bend as A
import ../../../../src/crypto/sha/packed/packed.bend as P
import ../../../../spec/crypto/sha/packed.bend as R
import ./core_model.bend as C
import ../../../../spec/crypto/sha.bend as F
import ../../../../src/crypto/sha/state.bend as S
import ./conformance.bend as Conformance

law compress_correct:
  for +a: U32
  for +b: U32
  for +c: U32
  for +d: U32
  for +e: U32
  for +f: U32
  for +g: U32
  for +h: U32
  for +i: U32
  for +j: U32
  for +k: U32
  for +l: U32
  for +m: U32
  for +n: U32
  for +o: U32
  for +p: U32
  for +extra: Nat
  for +s: S.State
  {Runtime.fips_compress16(a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,extra,s) == R.compress([a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p],extra,s) : S.State}

def compress_correct(a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,extra,s):
  Equal.trans(S.State,Runtime.fips_compress16(a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,extra,s),C.window_compress16(a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,extra,C.round_constants(),s),R.compress([a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p],extra,s),Conformance.fips16_correct(a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,extra,s),Equal.trans(S.State,C.window_compress16(a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,extra,C.round_constants(),s),C.fused_compress([a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p],extra,C.round_constants(),s),R.compress([a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p],extra,s),Conformance.window_compress16_correct(a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,extra,C.round_constants(),s),Equal.trans(S.State,C.fused_compress([a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p],extra,C.round_constants(),s),C.compress(C.schedule(extra,[a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p]),C.round_constants(),s),R.compress([a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p],extra,s),Conformance.fused_compress_correct([a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p],extra,C.round_constants(),s),Equal.trans(S.State,C.compress(C.schedule(extra,[a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p]),C.round_constants(),s),F.compress(C.schedule(extra,[a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p]),F.constants(),s),R.compress([a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p],extra,s),Conformance.compression_correct(C.schedule(extra,[a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p]),C.round_constants(),s),Equal.cong(List<&2,U32>,S.State,ws => F.compress(ws,F.constants(),s),C.schedule(extra,[a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p]),F.schedule(extra,[a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p]),Conformance.schedule_correct(extra,[a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p]))))))

law read16_correct:
  for +extra: Nat
  for +index: U32
  for +s: S.State
  for +w0: U32
  for +w1: U32
  for +w2: U32
  for +w3: U32
  for +w4: U32
  for +w5: U32
  for +w6: U32
  for +w7: U32
  for +w8: U32
  for +w9: U32
  for +w10: U32
  for +w11: U32
  for +w12: U32
  for +w13: U32
  for +w14: U32
  for pair: Array<U32> & U32
  {P.read16(extra,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,pair) == R.gather(extra,0n,index,False{},0n,0n,s,[w14,w13,w12,w11,w10,w9,w8,w7,w6,w5,w4,w3,w2,w1,w0],pair) : Array<U32> & S.State}

def read16_correct(extra,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,pair):
  (a,w15) = pair
  Equal.cong(S.State,Array<U32> & S.State,x => (a,x),Runtime.fips_compress16(w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,extra,s),R.compress([w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15],extra,s),compress_correct(w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,extra,s))

law read15_correct:
  for +extra: Nat
  for +index: U32
  for +s: S.State
  for +w0: U32
  for +w1: U32
  for +w2: U32
  for +w3: U32
  for +w4: U32
  for +w5: U32
  for +w6: U32
  for +w7: U32
  for +w8: U32
  for +w9: U32
  for +w10: U32
  for +w11: U32
  for +w12: U32
  for +w13: U32
  for pair: Array<U32> & U32
  {P.read15(extra,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,pair) == R.gather(extra,1n,index,False{},0n,0n,s,[w13,w12,w11,w10,w9,w8,w7,w6,w5,w4,w3,w2,w1,w0],pair) : Array<U32> & S.State}

def read15_correct(extra,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,pair):
  (a,w14) = pair
  read16_correct(extra,U32.inc(index),s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,P.at(a,U32.inc(index)))

law read14_correct:
  for +extra: Nat
  for +index: U32
  for +s: S.State
  for +w0: U32
  for +w1: U32
  for +w2: U32
  for +w3: U32
  for +w4: U32
  for +w5: U32
  for +w6: U32
  for +w7: U32
  for +w8: U32
  for +w9: U32
  for +w10: U32
  for +w11: U32
  for +w12: U32
  for pair: Array<U32> & U32
  {P.read14(extra,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,pair) == R.gather(extra,2n,index,False{},0n,0n,s,[w12,w11,w10,w9,w8,w7,w6,w5,w4,w3,w2,w1,w0],pair) : Array<U32> & S.State}

def read14_correct(extra,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,pair):
  (a,w13) = pair
  read15_correct(extra,U32.inc(index),s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,P.at(a,U32.inc(index)))

law read13_correct:
  for +extra: Nat
  for +index: U32
  for +s: S.State
  for +w0: U32
  for +w1: U32
  for +w2: U32
  for +w3: U32
  for +w4: U32
  for +w5: U32
  for +w6: U32
  for +w7: U32
  for +w8: U32
  for +w9: U32
  for +w10: U32
  for +w11: U32
  for pair: Array<U32> & U32
  {P.read13(extra,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,pair) == R.gather(extra,3n,index,False{},0n,0n,s,[w11,w10,w9,w8,w7,w6,w5,w4,w3,w2,w1,w0],pair) : Array<U32> & S.State}

def read13_correct(extra,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,pair):
  (a,w12) = pair
  read14_correct(extra,U32.inc(index),s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,P.at(a,U32.inc(index)))

law read12_correct:
  for +extra: Nat
  for +index: U32
  for +s: S.State
  for +w0: U32
  for +w1: U32
  for +w2: U32
  for +w3: U32
  for +w4: U32
  for +w5: U32
  for +w6: U32
  for +w7: U32
  for +w8: U32
  for +w9: U32
  for +w10: U32
  for pair: Array<U32> & U32
  {P.read12(extra,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,pair) == R.gather(extra,4n,index,False{},0n,0n,s,[w10,w9,w8,w7,w6,w5,w4,w3,w2,w1,w0],pair) : Array<U32> & S.State}

def read12_correct(extra,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,pair):
  (a,w11) = pair
  read13_correct(extra,U32.inc(index),s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,P.at(a,U32.inc(index)))

law read11_correct:
  for +extra: Nat
  for +index: U32
  for +s: S.State
  for +w0: U32
  for +w1: U32
  for +w2: U32
  for +w3: U32
  for +w4: U32
  for +w5: U32
  for +w6: U32
  for +w7: U32
  for +w8: U32
  for +w9: U32
  for pair: Array<U32> & U32
  {P.read11(extra,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,pair) == R.gather(extra,5n,index,False{},0n,0n,s,[w9,w8,w7,w6,w5,w4,w3,w2,w1,w0],pair) : Array<U32> & S.State}

def read11_correct(extra,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,pair):
  (a,w10) = pair
  read12_correct(extra,U32.inc(index),s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,P.at(a,U32.inc(index)))

law read10_correct:
  for +extra: Nat
  for +index: U32
  for +s: S.State
  for +w0: U32
  for +w1: U32
  for +w2: U32
  for +w3: U32
  for +w4: U32
  for +w5: U32
  for +w6: U32
  for +w7: U32
  for +w8: U32
  for pair: Array<U32> & U32
  {P.read10(extra,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,pair) == R.gather(extra,6n,index,False{},0n,0n,s,[w8,w7,w6,w5,w4,w3,w2,w1,w0],pair) : Array<U32> & S.State}

def read10_correct(extra,index,s,w0,w1,w2,w3,w4,w5,w6,w7,w8,pair):
  (a,w9) = pair
  read11_correct(extra,U32.inc(index),s,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,P.at(a,U32.inc(index)))

law read9_correct:
  for +extra: Nat
  for +index: U32
  for +s: S.State
  for +w0: U32
  for +w1: U32
  for +w2: U32
  for +w3: U32
  for +w4: U32
  for +w5: U32
  for +w6: U32
  for +w7: U32
  for pair: Array<U32> & U32
  {P.read9(extra,index,s,w0,w1,w2,w3,w4,w5,w6,w7,pair) == R.gather(extra,7n,index,False{},0n,0n,s,[w7,w6,w5,w4,w3,w2,w1,w0],pair) : Array<U32> & S.State}

def read9_correct(extra,index,s,w0,w1,w2,w3,w4,w5,w6,w7,pair):
  (a,w8) = pair
  read10_correct(extra,U32.inc(index),s,w0,w1,w2,w3,w4,w5,w6,w7,w8,P.at(a,U32.inc(index)))

law read8_correct:
  for +extra: Nat
  for +index: U32
  for +s: S.State
  for +w0: U32
  for +w1: U32
  for +w2: U32
  for +w3: U32
  for +w4: U32
  for +w5: U32
  for +w6: U32
  for pair: Array<U32> & U32
  {P.read8(extra,index,s,w0,w1,w2,w3,w4,w5,w6,pair) == R.gather(extra,8n,index,False{},0n,0n,s,[w6,w5,w4,w3,w2,w1,w0],pair) : Array<U32> & S.State}

def read8_correct(extra,index,s,w0,w1,w2,w3,w4,w5,w6,pair):
  (a,w7) = pair
  read9_correct(extra,U32.inc(index),s,w0,w1,w2,w3,w4,w5,w6,w7,P.at(a,U32.inc(index)))

law read7_correct:
  for +extra: Nat
  for +index: U32
  for +s: S.State
  for +w0: U32
  for +w1: U32
  for +w2: U32
  for +w3: U32
  for +w4: U32
  for +w5: U32
  for pair: Array<U32> & U32
  {P.read7(extra,index,s,w0,w1,w2,w3,w4,w5,pair) == R.gather(extra,9n,index,False{},0n,0n,s,[w5,w4,w3,w2,w1,w0],pair) : Array<U32> & S.State}

def read7_correct(extra,index,s,w0,w1,w2,w3,w4,w5,pair):
  (a,w6) = pair
  read8_correct(extra,U32.inc(index),s,w0,w1,w2,w3,w4,w5,w6,P.at(a,U32.inc(index)))

law read6_correct:
  for +extra: Nat
  for +index: U32
  for +s: S.State
  for +w0: U32
  for +w1: U32
  for +w2: U32
  for +w3: U32
  for +w4: U32
  for pair: Array<U32> & U32
  {P.read6(extra,index,s,w0,w1,w2,w3,w4,pair) == R.gather(extra,10n,index,False{},0n,0n,s,[w4,w3,w2,w1,w0],pair) : Array<U32> & S.State}

def read6_correct(extra,index,s,w0,w1,w2,w3,w4,pair):
  (a,w5) = pair
  read7_correct(extra,U32.inc(index),s,w0,w1,w2,w3,w4,w5,P.at(a,U32.inc(index)))

law read5_correct:
  for +extra: Nat
  for +index: U32
  for +s: S.State
  for +w0: U32
  for +w1: U32
  for +w2: U32
  for +w3: U32
  for pair: Array<U32> & U32
  {P.read5(extra,index,s,w0,w1,w2,w3,pair) == R.gather(extra,11n,index,False{},0n,0n,s,[w3,w2,w1,w0],pair) : Array<U32> & S.State}

def read5_correct(extra,index,s,w0,w1,w2,w3,pair):
  (a,w4) = pair
  read6_correct(extra,U32.inc(index),s,w0,w1,w2,w3,w4,P.at(a,U32.inc(index)))

law read4_correct:
  for +extra: Nat
  for +index: U32
  for +s: S.State
  for +w0: U32
  for +w1: U32
  for +w2: U32
  for pair: Array<U32> & U32
  {P.read4(extra,index,s,w0,w1,w2,pair) == R.gather(extra,12n,index,False{},0n,0n,s,[w2,w1,w0],pair) : Array<U32> & S.State}

def read4_correct(extra,index,s,w0,w1,w2,pair):
  (a,w3) = pair
  read5_correct(extra,U32.inc(index),s,w0,w1,w2,w3,P.at(a,U32.inc(index)))

law read3_correct:
  for +extra: Nat
  for +index: U32
  for +s: S.State
  for +w0: U32
  for +w1: U32
  for pair: Array<U32> & U32
  {P.read3(extra,index,s,w0,w1,pair) == R.gather(extra,13n,index,False{},0n,0n,s,[w1,w0],pair) : Array<U32> & S.State}

def read3_correct(extra,index,s,w0,w1,pair):
  (a,w2) = pair
  read4_correct(extra,U32.inc(index),s,w0,w1,w2,P.at(a,U32.inc(index)))

law read2_correct:
  for +extra: Nat
  for +index: U32
  for +s: S.State
  for +w0: U32
  for pair: Array<U32> & U32
  {P.read2(extra,index,s,w0,pair) == R.gather(extra,14n,index,False{},0n,0n,s,[w0],pair) : Array<U32> & S.State}

def read2_correct(extra,index,s,w0,pair):
  (a,w1) = pair
  read3_correct(extra,U32.inc(index),s,w0,w1,P.at(a,U32.inc(index)))

law read1_correct:
  for +extra: Nat
  for +index: U32
  for +s: S.State
  for pair: Array<U32> & U32
  {P.read1(extra,index,s,pair) == R.gather(extra,15n,index,False{},0n,0n,s,Nil{},pair) : Array<U32> & S.State}

def read1_correct(extra,index,s,pair):
  (a,w0) = pair
  read2_correct(extra,U32.inc(index),s,w0,P.at(a,U32.inc(index)))

law partial_correct:
  for +w: U32
  for +delta: Nat
  {P.partial(w,delta) == R.partial(w,delta) : U32}
def partial_correct(w,delta):
  match delta:
    case 0n: {==}
    case 1n: {==}
    case 2n: {==}
    case 3n: {==}
    case 4n+p: {==}

law pad_choose_correct:
  for +c: Cmp
  for +w: U32
  for +delta: Nat
  {P.pad_choose(c,w,delta) == R.pad_choose(c,w,delta) : U32}
def pad_choose_correct(c,w,delta):
  match c:
    case GT{}: {==}
    case EQ{}: {==}
    case LT{}: partial_correct(w,delta)

law pad_word_correct:
  for +w: U32
  for +pos: Nat
  for +remain: Nat
  {P.pad_word(w,pos,remain) == R.pad_word(w,pos,remain) : U32}
def pad_word_correct(w,pos,remain):
  pad_choose_correct(Nat.cmp(pos,remain),w,Nat.sub(remain,pos))

law tail_word_correct:
  for +short: Bool
  for +w: U32
  for +pos: Nat
  for +remain: Nat
  for +length: U32
  {P.length_word(short,P.pad_word(w,pos,remain),length) == R.length_word(short,R.pad_word(w,pos,remain),length) : U32}
def tail_word_correct(short,w,pos,remain,length):
  match short:
    case True{}: {==}
    case False{}: pad_word_correct(w,pos,remain)

law padded_words_correct:
  for +w0: U32
  for +w1: U32
  for +w2: U32
  for +w3: U32
  for +w4: U32
  for +w5: U32
  for +w6: U32
  for +w7: U32
  for +w8: U32
  for +w9: U32
  for +w10: U32
  for +w11: U32
  for +w12: U32
  for +w13: U32
  for +w14: U32
  for +w15: U32
  for +remain: Nat
  for +total: Nat
  {[P.pad_word(w0,0n,remain),P.pad_word(w1,4n,remain),P.pad_word(w2,8n,remain),P.pad_word(w3,12n,remain),P.pad_word(w4,16n,remain),P.pad_word(w5,20n,remain),P.pad_word(w6,24n,remain),P.pad_word(w7,28n,remain),P.pad_word(w8,32n,remain),P.pad_word(w9,36n,remain),P.pad_word(w10,40n,remain),P.pad_word(w11,44n,remain),P.pad_word(w12,48n,remain),P.pad_word(w13,52n,remain),P.length_word(Nat.is_lt(remain,56n),P.pad_word(w14,56n,remain),Runtime.len_hi(total)),P.length_word(Nat.is_lt(remain,56n),P.pad_word(w15,60n,remain),Runtime.len_lo(total))] == R.padded_words([w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15],0n,remain,total) : List<&2,U32>}

def padded_words_correct(w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,remain,total):
  %pad_word_correct(w0,0n,remain) :
    {[P.pad_word(w0,0n,remain),P.pad_word(w1,4n,remain),P.pad_word(w2,8n,remain),P.pad_word(w3,12n,remain),P.pad_word(w4,16n,remain),P.pad_word(w5,20n,remain),P.pad_word(w6,24n,remain),P.pad_word(w7,28n,remain),P.pad_word(w8,32n,remain),P.pad_word(w9,36n,remain),P.pad_word(w10,40n,remain),P.pad_word(w11,44n,remain),P.pad_word(w12,48n,remain),P.pad_word(w13,52n,remain),P.length_word(Nat.is_lt(remain,56n),P.pad_word(w14,56n,remain),Runtime.len_hi(total)),P.length_word(Nat.is_lt(remain,56n),P.pad_word(w15,60n,remain),Runtime.len_lo(total))] == [_,R.pad_word(w1,4n,remain),R.pad_word(w2,8n,remain),R.pad_word(w3,12n,remain),R.pad_word(w4,16n,remain),R.pad_word(w5,20n,remain),R.pad_word(w6,24n,remain),R.pad_word(w7,28n,remain),R.pad_word(w8,32n,remain),R.pad_word(w9,36n,remain),R.pad_word(w10,40n,remain),R.pad_word(w11,44n,remain),R.pad_word(w12,48n,remain),R.pad_word(w13,52n,remain),R.length_word(Nat.is_lt(remain,56n),R.pad_word(w14,56n,remain),Runtime.len_hi(total)),R.length_word(Nat.is_lt(remain,56n),R.pad_word(w15,60n,remain),Runtime.len_lo(total))] : List<&2,U32>}
  %pad_word_correct(w1,4n,remain) :
    {[P.pad_word(w0,0n,remain),P.pad_word(w1,4n,remain),P.pad_word(w2,8n,remain),P.pad_word(w3,12n,remain),P.pad_word(w4,16n,remain),P.pad_word(w5,20n,remain),P.pad_word(w6,24n,remain),P.pad_word(w7,28n,remain),P.pad_word(w8,32n,remain),P.pad_word(w9,36n,remain),P.pad_word(w10,40n,remain),P.pad_word(w11,44n,remain),P.pad_word(w12,48n,remain),P.pad_word(w13,52n,remain),P.length_word(Nat.is_lt(remain,56n),P.pad_word(w14,56n,remain),Runtime.len_hi(total)),P.length_word(Nat.is_lt(remain,56n),P.pad_word(w15,60n,remain),Runtime.len_lo(total))] == [P.pad_word(w0,0n,remain),_,R.pad_word(w2,8n,remain),R.pad_word(w3,12n,remain),R.pad_word(w4,16n,remain),R.pad_word(w5,20n,remain),R.pad_word(w6,24n,remain),R.pad_word(w7,28n,remain),R.pad_word(w8,32n,remain),R.pad_word(w9,36n,remain),R.pad_word(w10,40n,remain),R.pad_word(w11,44n,remain),R.pad_word(w12,48n,remain),R.pad_word(w13,52n,remain),R.length_word(Nat.is_lt(remain,56n),R.pad_word(w14,56n,remain),Runtime.len_hi(total)),R.length_word(Nat.is_lt(remain,56n),R.pad_word(w15,60n,remain),Runtime.len_lo(total))] : List<&2,U32>}
  %pad_word_correct(w2,8n,remain) :
    {[P.pad_word(w0,0n,remain),P.pad_word(w1,4n,remain),P.pad_word(w2,8n,remain),P.pad_word(w3,12n,remain),P.pad_word(w4,16n,remain),P.pad_word(w5,20n,remain),P.pad_word(w6,24n,remain),P.pad_word(w7,28n,remain),P.pad_word(w8,32n,remain),P.pad_word(w9,36n,remain),P.pad_word(w10,40n,remain),P.pad_word(w11,44n,remain),P.pad_word(w12,48n,remain),P.pad_word(w13,52n,remain),P.length_word(Nat.is_lt(remain,56n),P.pad_word(w14,56n,remain),Runtime.len_hi(total)),P.length_word(Nat.is_lt(remain,56n),P.pad_word(w15,60n,remain),Runtime.len_lo(total))] == [P.pad_word(w0,0n,remain),P.pad_word(w1,4n,remain),_,R.pad_word(w3,12n,remain),R.pad_word(w4,16n,remain),R.pad_word(w5,20n,remain),R.pad_word(w6,24n,remain),R.pad_word(w7,28n,remain),R.pad_word(w8,32n,remain),R.pad_word(w9,36n,remain),R.pad_word(w10,40n,remain),R.pad_word(w11,44n,remain),R.pad_word(w12,48n,remain),R.pad_word(w13,52n,remain),R.length_word(Nat.is_lt(remain,56n),R.pad_word(w14,56n,remain),Runtime.len_hi(total)),R.length_word(Nat.is_lt(remain,56n),R.pad_word(w15,60n,remain),Runtime.len_lo(total))] : List<&2,U32>}
  %pad_word_correct(w3,12n,remain) :
    {[P.pad_word(w0,0n,remain),P.pad_word(w1,4n,remain),P.pad_word(w2,8n,remain),P.pad_word(w3,12n,remain),P.pad_word(w4,16n,remain),P.pad_word(w5,20n,remain),P.pad_word(w6,24n,remain),P.pad_word(w7,28n,remain),P.pad_word(w8,32n,remain),P.pad_word(w9,36n,remain),P.pad_word(w10,40n,remain),P.pad_word(w11,44n,remain),P.pad_word(w12,48n,remain),P.pad_word(w13,52n,remain),P.length_word(Nat.is_lt(remain,56n),P.pad_word(w14,56n,remain),Runtime.len_hi(total)),P.length_word(Nat.is_lt(remain,56n),P.pad_word(w15,60n,remain),Runtime.len_lo(total))] == [P.pad_word(w0,0n,remain),P.pad_word(w1,4n,remain),P.pad_word(w2,8n,remain),_,R.pad_word(w4,16n,remain),R.pad_word(w5,20n,remain),R.pad_word(w6,24n,remain),R.pad_word(w7,28n,remain),R.pad_word(w8,32n,remain),R.pad_word(w9,36n,remain),R.pad_word(w10,40n,remain),R.pad_word(w11,44n,remain),R.pad_word(w12,48n,remain),R.pad_word(w13,52n,remain),R.length_word(Nat.is_lt(remain,56n),R.pad_word(w14,56n,remain),Runtime.len_hi(total)),R.length_word(Nat.is_lt(remain,56n),R.pad_word(w15,60n,remain),Runtime.len_lo(total))] : List<&2,U32>}
  %pad_word_correct(w4,16n,remain) :
    {[P.pad_word(w0,0n,remain),P.pad_word(w1,4n,remain),P.pad_word(w2,8n,remain),P.pad_word(w3,12n,remain),P.pad_word(w4,16n,remain),P.pad_word(w5,20n,remain),P.pad_word(w6,24n,remain),P.pad_word(w7,28n,remain),P.pad_word(w8,32n,remain),P.pad_word(w9,36n,remain),P.pad_word(w10,40n,remain),P.pad_word(w11,44n,remain),P.pad_word(w12,48n,remain),P.pad_word(w13,52n,remain),P.length_word(Nat.is_lt(remain,56n),P.pad_word(w14,56n,remain),Runtime.len_hi(total)),P.length_word(Nat.is_lt(remain,56n),P.pad_word(w15,60n,remain),Runtime.len_lo(total))] == [P.pad_word(w0,0n,remain),P.pad_word(w1,4n,remain),P.pad_word(w2,8n,remain),P.pad_word(w3,12n,remain),_,R.pad_word(w5,20n,remain),R.pad_word(w6,24n,remain),R.pad_word(w7,28n,remain),R.pad_word(w8,32n,remain),R.pad_word(w9,36n,remain),R.pad_word(w10,40n,remain),R.pad_word(w11,44n,remain),R.pad_word(w12,48n,remain),R.pad_word(w13,52n,remain),R.length_word(Nat.is_lt(remain,56n),R.pad_word(w14,56n,remain),Runtime.len_hi(total)),R.length_word(Nat.is_lt(remain,56n),R.pad_word(w15,60n,remain),Runtime.len_lo(total))] : List<&2,U32>}
  %pad_word_correct(w5,20n,remain) :
    {[P.pad_word(w0,0n,remain),P.pad_word(w1,4n,remain),P.pad_word(w2,8n,remain),P.pad_word(w3,12n,remain),P.pad_word(w4,16n,remain),P.pad_word(w5,20n,remain),P.pad_word(w6,24n,remain),P.pad_word(w7,28n,remain),P.pad_word(w8,32n,remain),P.pad_word(w9,36n,remain),P.pad_word(w10,40n,remain),P.pad_word(w11,44n,remain),P.pad_word(w12,48n,remain),P.pad_word(w13,52n,remain),P.length_word(Nat.is_lt(remain,56n),P.pad_word(w14,56n,remain),Runtime.len_hi(total)),P.length_word(Nat.is_lt(remain,56n),P.pad_word(w15,60n,remain),Runtime.len_lo(total))] == [P.pad_word(w0,0n,remain),P.pad_word(w1,4n,remain),P.pad_word(w2,8n,remain),P.pad_word(w3,12n,remain),P.pad_word(w4,16n,remain),_,R.pad_word(w6,24n,remain),R.pad_word(w7,28n,remain),R.pad_word(w8,32n,remain),R.pad_word(w9,36n,remain),R.pad_word(w10,40n,remain),R.pad_word(w11,44n,remain),R.pad_word(w12,48n,remain),R.pad_word(w13,52n,remain),R.length_word(Nat.is_lt(remain,56n),R.pad_word(w14,56n,remain),Runtime.len_hi(total)),R.length_word(Nat.is_lt(remain,56n),R.pad_word(w15,60n,remain),Runtime.len_lo(total))] : List<&2,U32>}
  %pad_word_correct(w6,24n,remain) :
    {[P.pad_word(w0,0n,remain),P.pad_word(w1,4n,remain),P.pad_word(w2,8n,remain),P.pad_word(w3,12n,remain),P.pad_word(w4,16n,remain),P.pad_word(w5,20n,remain),P.pad_word(w6,24n,remain),P.pad_word(w7,28n,remain),P.pad_word(w8,32n,remain),P.pad_word(w9,36n,remain),P.pad_word(w10,40n,remain),P.pad_word(w11,44n,remain),P.pad_word(w12,48n,remain),P.pad_word(w13,52n,remain),P.length_word(Nat.is_lt(remain,56n),P.pad_word(w14,56n,remain),Runtime.len_hi(total)),P.length_word(Nat.is_lt(remain,56n),P.pad_word(w15,60n,remain),Runtime.len_lo(total))] == [P.pad_word(w0,0n,remain),P.pad_word(w1,4n,remain),P.pad_word(w2,8n,remain),P.pad_word(w3,12n,remain),P.pad_word(w4,16n,remain),P.pad_word(w5,20n,remain),_,R.pad_word(w7,28n,remain),R.pad_word(w8,32n,remain),R.pad_word(w9,36n,remain),R.pad_word(w10,40n,remain),R.pad_word(w11,44n,remain),R.pad_word(w12,48n,remain),R.pad_word(w13,52n,remain),R.length_word(Nat.is_lt(remain,56n),R.pad_word(w14,56n,remain),Runtime.len_hi(total)),R.length_word(Nat.is_lt(remain,56n),R.pad_word(w15,60n,remain),Runtime.len_lo(total))] : List<&2,U32>}
  %pad_word_correct(w7,28n,remain) :
    {[P.pad_word(w0,0n,remain),P.pad_word(w1,4n,remain),P.pad_word(w2,8n,remain),P.pad_word(w3,12n,remain),P.pad_word(w4,16n,remain),P.pad_word(w5,20n,remain),P.pad_word(w6,24n,remain),P.pad_word(w7,28n,remain),P.pad_word(w8,32n,remain),P.pad_word(w9,36n,remain),P.pad_word(w10,40n,remain),P.pad_word(w11,44n,remain),P.pad_word(w12,48n,remain),P.pad_word(w13,52n,remain),P.length_word(Nat.is_lt(remain,56n),P.pad_word(w14,56n,remain),Runtime.len_hi(total)),P.length_word(Nat.is_lt(remain,56n),P.pad_word(w15,60n,remain),Runtime.len_lo(total))] == [P.pad_word(w0,0n,remain),P.pad_word(w1,4n,remain),P.pad_word(w2,8n,remain),P.pad_word(w3,12n,remain),P.pad_word(w4,16n,remain),P.pad_word(w5,20n,remain),P.pad_word(w6,24n,remain),_,R.pad_word(w8,32n,remain),R.pad_word(w9,36n,remain),R.pad_word(w10,40n,remain),R.pad_word(w11,44n,remain),R.pad_word(w12,48n,remain),R.pad_word(w13,52n,remain),R.length_word(Nat.is_lt(remain,56n),R.pad_word(w14,56n,remain),Runtime.len_hi(total)),R.length_word(Nat.is_lt(remain,56n),R.pad_word(w15,60n,remain),Runtime.len_lo(total))] : List<&2,U32>}
  %pad_word_correct(w8,32n,remain) :
    {[P.pad_word(w0,0n,remain),P.pad_word(w1,4n,remain),P.pad_word(w2,8n,remain),P.pad_word(w3,12n,remain),P.pad_word(w4,16n,remain),P.pad_word(w5,20n,remain),P.pad_word(w6,24n,remain),P.pad_word(w7,28n,remain),P.pad_word(w8,32n,remain),P.pad_word(w9,36n,remain),P.pad_word(w10,40n,remain),P.pad_word(w11,44n,remain),P.pad_word(w12,48n,remain),P.pad_word(w13,52n,remain),P.length_word(Nat.is_lt(remain,56n),P.pad_word(w14,56n,remain),Runtime.len_hi(total)),P.length_word(Nat.is_lt(remain,56n),P.pad_word(w15,60n,remain),Runtime.len_lo(total))] == [P.pad_word(w0,0n,remain),P.pad_word(w1,4n,remain),P.pad_word(w2,8n,remain),P.pad_word(w3,12n,remain),P.pad_word(w4,16n,remain),P.pad_word(w5,20n,remain),P.pad_word(w6,24n,remain),P.pad_word(w7,28n,remain),_,R.pad_word(w9,36n,remain),R.pad_word(w10,40n,remain),R.pad_word(w11,44n,remain),R.pad_word(w12,48n,remain),R.pad_word(w13,52n,remain),R.length_word(Nat.is_lt(remain,56n),R.pad_word(w14,56n,remain),Runtime.len_hi(total)),R.length_word(Nat.is_lt(remain,56n),R.pad_word(w15,60n,remain),Runtime.len_lo(total))] : List<&2,U32>}
  %pad_word_correct(w9,36n,remain) :
    {[P.pad_word(w0,0n,remain),P.pad_word(w1,4n,remain),P.pad_word(w2,8n,remain),P.pad_word(w3,12n,remain),P.pad_word(w4,16n,remain),P.pad_word(w5,20n,remain),P.pad_word(w6,24n,remain),P.pad_word(w7,28n,remain),P.pad_word(w8,32n,remain),P.pad_word(w9,36n,remain),P.pad_word(w10,40n,remain),P.pad_word(w11,44n,remain),P.pad_word(w12,48n,remain),P.pad_word(w13,52n,remain),P.length_word(Nat.is_lt(remain,56n),P.pad_word(w14,56n,remain),Runtime.len_hi(total)),P.length_word(Nat.is_lt(remain,56n),P.pad_word(w15,60n,remain),Runtime.len_lo(total))] == [P.pad_word(w0,0n,remain),P.pad_word(w1,4n,remain),P.pad_word(w2,8n,remain),P.pad_word(w3,12n,remain),P.pad_word(w4,16n,remain),P.pad_word(w5,20n,remain),P.pad_word(w6,24n,remain),P.pad_word(w7,28n,remain),P.pad_word(w8,32n,remain),_,R.pad_word(w10,40n,remain),R.pad_word(w11,44n,remain),R.pad_word(w12,48n,remain),R.pad_word(w13,52n,remain),R.length_word(Nat.is_lt(remain,56n),R.pad_word(w14,56n,remain),Runtime.len_hi(total)),R.length_word(Nat.is_lt(remain,56n),R.pad_word(w15,60n,remain),Runtime.len_lo(total))] : List<&2,U32>}
  %pad_word_correct(w10,40n,remain) :
    {[P.pad_word(w0,0n,remain),P.pad_word(w1,4n,remain),P.pad_word(w2,8n,remain),P.pad_word(w3,12n,remain),P.pad_word(w4,16n,remain),P.pad_word(w5,20n,remain),P.pad_word(w6,24n,remain),P.pad_word(w7,28n,remain),P.pad_word(w8,32n,remain),P.pad_word(w9,36n,remain),P.pad_word(w10,40n,remain),P.pad_word(w11,44n,remain),P.pad_word(w12,48n,remain),P.pad_word(w13,52n,remain),P.length_word(Nat.is_lt(remain,56n),P.pad_word(w14,56n,remain),Runtime.len_hi(total)),P.length_word(Nat.is_lt(remain,56n),P.pad_word(w15,60n,remain),Runtime.len_lo(total))] == [P.pad_word(w0,0n,remain),P.pad_word(w1,4n,remain),P.pad_word(w2,8n,remain),P.pad_word(w3,12n,remain),P.pad_word(w4,16n,remain),P.pad_word(w5,20n,remain),P.pad_word(w6,24n,remain),P.pad_word(w7,28n,remain),P.pad_word(w8,32n,remain),P.pad_word(w9,36n,remain),_,R.pad_word(w11,44n,remain),R.pad_word(w12,48n,remain),R.pad_word(w13,52n,remain),R.length_word(Nat.is_lt(remain,56n),R.pad_word(w14,56n,remain),Runtime.len_hi(total)),R.length_word(Nat.is_lt(remain,56n),R.pad_word(w15,60n,remain),Runtime.len_lo(total))] : List<&2,U32>}
  %pad_word_correct(w11,44n,remain) :
    {[P.pad_word(w0,0n,remain),P.pad_word(w1,4n,remain),P.pad_word(w2,8n,remain),P.pad_word(w3,12n,remain),P.pad_word(w4,16n,remain),P.pad_word(w5,20n,remain),P.pad_word(w6,24n,remain),P.pad_word(w7,28n,remain),P.pad_word(w8,32n,remain),P.pad_word(w9,36n,remain),P.pad_word(w10,40n,remain),P.pad_word(w11,44n,remain),P.pad_word(w12,48n,remain),P.pad_word(w13,52n,remain),P.length_word(Nat.is_lt(remain,56n),P.pad_word(w14,56n,remain),Runtime.len_hi(total)),P.length_word(Nat.is_lt(remain,56n),P.pad_word(w15,60n,remain),Runtime.len_lo(total))] == [P.pad_word(w0,0n,remain),P.pad_word(w1,4n,remain),P.pad_word(w2,8n,remain),P.pad_word(w3,12n,remain),P.pad_word(w4,16n,remain),P.pad_word(w5,20n,remain),P.pad_word(w6,24n,remain),P.pad_word(w7,28n,remain),P.pad_word(w8,32n,remain),P.pad_word(w9,36n,remain),P.pad_word(w10,40n,remain),_,R.pad_word(w12,48n,remain),R.pad_word(w13,52n,remain),R.length_word(Nat.is_lt(remain,56n),R.pad_word(w14,56n,remain),Runtime.len_hi(total)),R.length_word(Nat.is_lt(remain,56n),R.pad_word(w15,60n,remain),Runtime.len_lo(total))] : List<&2,U32>}
  %pad_word_correct(w12,48n,remain) :
    {[P.pad_word(w0,0n,remain),P.pad_word(w1,4n,remain),P.pad_word(w2,8n,remain),P.pad_word(w3,12n,remain),P.pad_word(w4,16n,remain),P.pad_word(w5,20n,remain),P.pad_word(w6,24n,remain),P.pad_word(w7,28n,remain),P.pad_word(w8,32n,remain),P.pad_word(w9,36n,remain),P.pad_word(w10,40n,remain),P.pad_word(w11,44n,remain),P.pad_word(w12,48n,remain),P.pad_word(w13,52n,remain),P.length_word(Nat.is_lt(remain,56n),P.pad_word(w14,56n,remain),Runtime.len_hi(total)),P.length_word(Nat.is_lt(remain,56n),P.pad_word(w15,60n,remain),Runtime.len_lo(total))] == [P.pad_word(w0,0n,remain),P.pad_word(w1,4n,remain),P.pad_word(w2,8n,remain),P.pad_word(w3,12n,remain),P.pad_word(w4,16n,remain),P.pad_word(w5,20n,remain),P.pad_word(w6,24n,remain),P.pad_word(w7,28n,remain),P.pad_word(w8,32n,remain),P.pad_word(w9,36n,remain),P.pad_word(w10,40n,remain),P.pad_word(w11,44n,remain),_,R.pad_word(w13,52n,remain),R.length_word(Nat.is_lt(remain,56n),R.pad_word(w14,56n,remain),Runtime.len_hi(total)),R.length_word(Nat.is_lt(remain,56n),R.pad_word(w15,60n,remain),Runtime.len_lo(total))] : List<&2,U32>}
  %pad_word_correct(w13,52n,remain) :
    {[P.pad_word(w0,0n,remain),P.pad_word(w1,4n,remain),P.pad_word(w2,8n,remain),P.pad_word(w3,12n,remain),P.pad_word(w4,16n,remain),P.pad_word(w5,20n,remain),P.pad_word(w6,24n,remain),P.pad_word(w7,28n,remain),P.pad_word(w8,32n,remain),P.pad_word(w9,36n,remain),P.pad_word(w10,40n,remain),P.pad_word(w11,44n,remain),P.pad_word(w12,48n,remain),P.pad_word(w13,52n,remain),P.length_word(Nat.is_lt(remain,56n),P.pad_word(w14,56n,remain),Runtime.len_hi(total)),P.length_word(Nat.is_lt(remain,56n),P.pad_word(w15,60n,remain),Runtime.len_lo(total))] == [P.pad_word(w0,0n,remain),P.pad_word(w1,4n,remain),P.pad_word(w2,8n,remain),P.pad_word(w3,12n,remain),P.pad_word(w4,16n,remain),P.pad_word(w5,20n,remain),P.pad_word(w6,24n,remain),P.pad_word(w7,28n,remain),P.pad_word(w8,32n,remain),P.pad_word(w9,36n,remain),P.pad_word(w10,40n,remain),P.pad_word(w11,44n,remain),P.pad_word(w12,48n,remain),_,R.length_word(Nat.is_lt(remain,56n),R.pad_word(w14,56n,remain),Runtime.len_hi(total)),R.length_word(Nat.is_lt(remain,56n),R.pad_word(w15,60n,remain),Runtime.len_lo(total))] : List<&2,U32>}
  %tail_word_correct(Nat.is_lt(remain,56n),w14,56n,remain,Runtime.len_hi(total)) :
    {[P.pad_word(w0,0n,remain),P.pad_word(w1,4n,remain),P.pad_word(w2,8n,remain),P.pad_word(w3,12n,remain),P.pad_word(w4,16n,remain),P.pad_word(w5,20n,remain),P.pad_word(w6,24n,remain),P.pad_word(w7,28n,remain),P.pad_word(w8,32n,remain),P.pad_word(w9,36n,remain),P.pad_word(w10,40n,remain),P.pad_word(w11,44n,remain),P.pad_word(w12,48n,remain),P.pad_word(w13,52n,remain),P.length_word(Nat.is_lt(remain,56n),P.pad_word(w14,56n,remain),Runtime.len_hi(total)),P.length_word(Nat.is_lt(remain,56n),P.pad_word(w15,60n,remain),Runtime.len_lo(total))] == [P.pad_word(w0,0n,remain),P.pad_word(w1,4n,remain),P.pad_word(w2,8n,remain),P.pad_word(w3,12n,remain),P.pad_word(w4,16n,remain),P.pad_word(w5,20n,remain),P.pad_word(w6,24n,remain),P.pad_word(w7,28n,remain),P.pad_word(w8,32n,remain),P.pad_word(w9,36n,remain),P.pad_word(w10,40n,remain),P.pad_word(w11,44n,remain),P.pad_word(w12,48n,remain),P.pad_word(w13,52n,remain),_,R.length_word(Nat.is_lt(remain,56n),R.pad_word(w15,60n,remain),Runtime.len_lo(total))] : List<&2,U32>}
  %tail_word_correct(Nat.is_lt(remain,56n),w15,60n,remain,Runtime.len_lo(total)) :
    {[P.pad_word(w0,0n,remain),P.pad_word(w1,4n,remain),P.pad_word(w2,8n,remain),P.pad_word(w3,12n,remain),P.pad_word(w4,16n,remain),P.pad_word(w5,20n,remain),P.pad_word(w6,24n,remain),P.pad_word(w7,28n,remain),P.pad_word(w8,32n,remain),P.pad_word(w9,36n,remain),P.pad_word(w10,40n,remain),P.pad_word(w11,44n,remain),P.pad_word(w12,48n,remain),P.pad_word(w13,52n,remain),P.length_word(Nat.is_lt(remain,56n),P.pad_word(w14,56n,remain),Runtime.len_hi(total)),P.length_word(Nat.is_lt(remain,56n),P.pad_word(w15,60n,remain),Runtime.len_lo(total))] == [P.pad_word(w0,0n,remain),P.pad_word(w1,4n,remain),P.pad_word(w2,8n,remain),P.pad_word(w3,12n,remain),P.pad_word(w4,16n,remain),P.pad_word(w5,20n,remain),P.pad_word(w6,24n,remain),P.pad_word(w7,28n,remain),P.pad_word(w8,32n,remain),P.pad_word(w9,36n,remain),P.pad_word(w10,40n,remain),P.pad_word(w11,44n,remain),P.pad_word(w12,48n,remain),P.pad_word(w13,52n,remain),P.length_word(Nat.is_lt(remain,56n),P.pad_word(w14,56n,remain),Runtime.len_hi(total)),_] : List<&2,U32>}
  {==}

law pad16_correct:
  for +extra: Nat
  for +index: U32
  for +s: S.State
  for +remain: Nat
  for +total: Nat
  for +w0: U32
  for +w1: U32
  for +w2: U32
  for +w3: U32
  for +w4: U32
  for +w5: U32
  for +w6: U32
  for +w7: U32
  for +w8: U32
  for +w9: U32
  for +w10: U32
  for +w11: U32
  for +w12: U32
  for +w13: U32
  for +w14: U32
  for pair: Array<U32> & U32
  {P.pad16(extra,index,s,remain,total,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,pair) == R.gather(extra,0n,index,True{},remain,total,s,[w14,w13,w12,w11,w10,w9,w8,w7,w6,w5,w4,w3,w2,w1,w0],pair) : Array<U32> & S.State}

def pad16_correct(extra,index,s,remain,total,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,pair):
  (a,last) = pair
  +w15 = last
  Equal.trans(Array<U32> & S.State,
    (a,Runtime.fips_compress16(P.pad_word(w0,0n,remain),P.pad_word(w1,4n,remain),P.pad_word(w2,8n,remain),P.pad_word(w3,12n,remain),P.pad_word(w4,16n,remain),P.pad_word(w5,20n,remain),P.pad_word(w6,24n,remain),P.pad_word(w7,28n,remain),P.pad_word(w8,32n,remain),P.pad_word(w9,36n,remain),P.pad_word(w10,40n,remain),P.pad_word(w11,44n,remain),P.pad_word(w12,48n,remain),P.pad_word(w13,52n,remain),P.length_word(Nat.is_lt(remain,56n),P.pad_word(w14,56n,remain),Runtime.len_hi(total)),P.length_word(Nat.is_lt(remain,56n),P.pad_word(w15,60n,remain),Runtime.len_lo(total)),extra,s)),
    (a,R.compress([P.pad_word(w0,0n,remain),P.pad_word(w1,4n,remain),P.pad_word(w2,8n,remain),P.pad_word(w3,12n,remain),P.pad_word(w4,16n,remain),P.pad_word(w5,20n,remain),P.pad_word(w6,24n,remain),P.pad_word(w7,28n,remain),P.pad_word(w8,32n,remain),P.pad_word(w9,36n,remain),P.pad_word(w10,40n,remain),P.pad_word(w11,44n,remain),P.pad_word(w12,48n,remain),P.pad_word(w13,52n,remain),P.length_word(Nat.is_lt(remain,56n),P.pad_word(w14,56n,remain),Runtime.len_hi(total)),P.length_word(Nat.is_lt(remain,56n),P.pad_word(w15,60n,remain),Runtime.len_lo(total))],extra,s)),
    (a,R.compress(R.padded_words([w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15],0n,remain,total),extra,s)),
    Equal.cong(S.State,Array<U32> & S.State,x => (a,x),Runtime.fips_compress16(P.pad_word(w0,0n,remain),P.pad_word(w1,4n,remain),P.pad_word(w2,8n,remain),P.pad_word(w3,12n,remain),P.pad_word(w4,16n,remain),P.pad_word(w5,20n,remain),P.pad_word(w6,24n,remain),P.pad_word(w7,28n,remain),P.pad_word(w8,32n,remain),P.pad_word(w9,36n,remain),P.pad_word(w10,40n,remain),P.pad_word(w11,44n,remain),P.pad_word(w12,48n,remain),P.pad_word(w13,52n,remain),P.length_word(Nat.is_lt(remain,56n),P.pad_word(w14,56n,remain),Runtime.len_hi(total)),P.length_word(Nat.is_lt(remain,56n),P.pad_word(w15,60n,remain),Runtime.len_lo(total)),extra,s),R.compress([P.pad_word(w0,0n,remain),P.pad_word(w1,4n,remain),P.pad_word(w2,8n,remain),P.pad_word(w3,12n,remain),P.pad_word(w4,16n,remain),P.pad_word(w5,20n,remain),P.pad_word(w6,24n,remain),P.pad_word(w7,28n,remain),P.pad_word(w8,32n,remain),P.pad_word(w9,36n,remain),P.pad_word(w10,40n,remain),P.pad_word(w11,44n,remain),P.pad_word(w12,48n,remain),P.pad_word(w13,52n,remain),P.length_word(Nat.is_lt(remain,56n),P.pad_word(w14,56n,remain),Runtime.len_hi(total)),P.length_word(Nat.is_lt(remain,56n),P.pad_word(w15,60n,remain),Runtime.len_lo(total))],extra,s),compress_correct(P.pad_word(w0,0n,remain),P.pad_word(w1,4n,remain),P.pad_word(w2,8n,remain),P.pad_word(w3,12n,remain),P.pad_word(w4,16n,remain),P.pad_word(w5,20n,remain),P.pad_word(w6,24n,remain),P.pad_word(w7,28n,remain),P.pad_word(w8,32n,remain),P.pad_word(w9,36n,remain),P.pad_word(w10,40n,remain),P.pad_word(w11,44n,remain),P.pad_word(w12,48n,remain),P.pad_word(w13,52n,remain),P.length_word(Nat.is_lt(remain,56n),P.pad_word(w14,56n,remain),Runtime.len_hi(total)),P.length_word(Nat.is_lt(remain,56n),P.pad_word(w15,60n,remain),Runtime.len_lo(total)),extra,s)),
    Equal.cong(List<&2,U32>,Array<U32> & S.State,ws => (a,R.compress(ws,extra,s)),
      [P.pad_word(w0,0n,remain),P.pad_word(w1,4n,remain),P.pad_word(w2,8n,remain),P.pad_word(w3,12n,remain),P.pad_word(w4,16n,remain),P.pad_word(w5,20n,remain),P.pad_word(w6,24n,remain),P.pad_word(w7,28n,remain),P.pad_word(w8,32n,remain),P.pad_word(w9,36n,remain),P.pad_word(w10,40n,remain),P.pad_word(w11,44n,remain),P.pad_word(w12,48n,remain),P.pad_word(w13,52n,remain),P.length_word(Nat.is_lt(remain,56n),P.pad_word(w14,56n,remain),Runtime.len_hi(total)),P.length_word(Nat.is_lt(remain,56n),P.pad_word(w15,60n,remain),Runtime.len_lo(total))],R.padded_words([w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15],0n,remain,total),
      padded_words_correct(w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,remain,total)))

law pad15_correct:
  for +extra: Nat
  for +index: U32
  for +s: S.State
  for +remain: Nat
  for +total: Nat
  for +w0: U32
  for +w1: U32
  for +w2: U32
  for +w3: U32
  for +w4: U32
  for +w5: U32
  for +w6: U32
  for +w7: U32
  for +w8: U32
  for +w9: U32
  for +w10: U32
  for +w11: U32
  for +w12: U32
  for +w13: U32
  for pair: Array<U32> & U32
  {P.pad15(extra,index,s,remain,total,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,pair) == R.gather(extra,1n,index,True{},remain,total,s,[w13,w12,w11,w10,w9,w8,w7,w6,w5,w4,w3,w2,w1,w0],pair) : Array<U32> & S.State}

def pad15_correct(extra,index,s,remain,total,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,pair):
  (a,w14) = pair
  pad16_correct(extra,U32.inc(index),s,remain,total,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,P.at(a,U32.inc(index)))

law pad14_correct:
  for +extra: Nat
  for +index: U32
  for +s: S.State
  for +remain: Nat
  for +total: Nat
  for +w0: U32
  for +w1: U32
  for +w2: U32
  for +w3: U32
  for +w4: U32
  for +w5: U32
  for +w6: U32
  for +w7: U32
  for +w8: U32
  for +w9: U32
  for +w10: U32
  for +w11: U32
  for +w12: U32
  for pair: Array<U32> & U32
  {P.pad14(extra,index,s,remain,total,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,pair) == R.gather(extra,2n,index,True{},remain,total,s,[w12,w11,w10,w9,w8,w7,w6,w5,w4,w3,w2,w1,w0],pair) : Array<U32> & S.State}

def pad14_correct(extra,index,s,remain,total,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,pair):
  (a,w13) = pair
  pad15_correct(extra,U32.inc(index),s,remain,total,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,P.at(a,U32.inc(index)))

law pad13_correct:
  for +extra: Nat
  for +index: U32
  for +s: S.State
  for +remain: Nat
  for +total: Nat
  for +w0: U32
  for +w1: U32
  for +w2: U32
  for +w3: U32
  for +w4: U32
  for +w5: U32
  for +w6: U32
  for +w7: U32
  for +w8: U32
  for +w9: U32
  for +w10: U32
  for +w11: U32
  for pair: Array<U32> & U32
  {P.pad13(extra,index,s,remain,total,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,pair) == R.gather(extra,3n,index,True{},remain,total,s,[w11,w10,w9,w8,w7,w6,w5,w4,w3,w2,w1,w0],pair) : Array<U32> & S.State}

def pad13_correct(extra,index,s,remain,total,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,pair):
  (a,w12) = pair
  pad14_correct(extra,U32.inc(index),s,remain,total,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,P.at(a,U32.inc(index)))

law pad12_correct:
  for +extra: Nat
  for +index: U32
  for +s: S.State
  for +remain: Nat
  for +total: Nat
  for +w0: U32
  for +w1: U32
  for +w2: U32
  for +w3: U32
  for +w4: U32
  for +w5: U32
  for +w6: U32
  for +w7: U32
  for +w8: U32
  for +w9: U32
  for +w10: U32
  for pair: Array<U32> & U32
  {P.pad12(extra,index,s,remain,total,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,pair) == R.gather(extra,4n,index,True{},remain,total,s,[w10,w9,w8,w7,w6,w5,w4,w3,w2,w1,w0],pair) : Array<U32> & S.State}

def pad12_correct(extra,index,s,remain,total,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,pair):
  (a,w11) = pair
  pad13_correct(extra,U32.inc(index),s,remain,total,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,P.at(a,U32.inc(index)))

law pad11_correct:
  for +extra: Nat
  for +index: U32
  for +s: S.State
  for +remain: Nat
  for +total: Nat
  for +w0: U32
  for +w1: U32
  for +w2: U32
  for +w3: U32
  for +w4: U32
  for +w5: U32
  for +w6: U32
  for +w7: U32
  for +w8: U32
  for +w9: U32
  for pair: Array<U32> & U32
  {P.pad11(extra,index,s,remain,total,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,pair) == R.gather(extra,5n,index,True{},remain,total,s,[w9,w8,w7,w6,w5,w4,w3,w2,w1,w0],pair) : Array<U32> & S.State}

def pad11_correct(extra,index,s,remain,total,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,pair):
  (a,w10) = pair
  pad12_correct(extra,U32.inc(index),s,remain,total,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,P.at(a,U32.inc(index)))

law pad10_correct:
  for +extra: Nat
  for +index: U32
  for +s: S.State
  for +remain: Nat
  for +total: Nat
  for +w0: U32
  for +w1: U32
  for +w2: U32
  for +w3: U32
  for +w4: U32
  for +w5: U32
  for +w6: U32
  for +w7: U32
  for +w8: U32
  for pair: Array<U32> & U32
  {P.pad10(extra,index,s,remain,total,w0,w1,w2,w3,w4,w5,w6,w7,w8,pair) == R.gather(extra,6n,index,True{},remain,total,s,[w8,w7,w6,w5,w4,w3,w2,w1,w0],pair) : Array<U32> & S.State}

def pad10_correct(extra,index,s,remain,total,w0,w1,w2,w3,w4,w5,w6,w7,w8,pair):
  (a,w9) = pair
  pad11_correct(extra,U32.inc(index),s,remain,total,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,P.at(a,U32.inc(index)))

law pad9_correct:
  for +extra: Nat
  for +index: U32
  for +s: S.State
  for +remain: Nat
  for +total: Nat
  for +w0: U32
  for +w1: U32
  for +w2: U32
  for +w3: U32
  for +w4: U32
  for +w5: U32
  for +w6: U32
  for +w7: U32
  for pair: Array<U32> & U32
  {P.pad9(extra,index,s,remain,total,w0,w1,w2,w3,w4,w5,w6,w7,pair) == R.gather(extra,7n,index,True{},remain,total,s,[w7,w6,w5,w4,w3,w2,w1,w0],pair) : Array<U32> & S.State}

def pad9_correct(extra,index,s,remain,total,w0,w1,w2,w3,w4,w5,w6,w7,pair):
  (a,w8) = pair
  pad10_correct(extra,U32.inc(index),s,remain,total,w0,w1,w2,w3,w4,w5,w6,w7,w8,P.at(a,U32.inc(index)))

law pad8_correct:
  for +extra: Nat
  for +index: U32
  for +s: S.State
  for +remain: Nat
  for +total: Nat
  for +w0: U32
  for +w1: U32
  for +w2: U32
  for +w3: U32
  for +w4: U32
  for +w5: U32
  for +w6: U32
  for pair: Array<U32> & U32
  {P.pad8(extra,index,s,remain,total,w0,w1,w2,w3,w4,w5,w6,pair) == R.gather(extra,8n,index,True{},remain,total,s,[w6,w5,w4,w3,w2,w1,w0],pair) : Array<U32> & S.State}

def pad8_correct(extra,index,s,remain,total,w0,w1,w2,w3,w4,w5,w6,pair):
  (a,w7) = pair
  pad9_correct(extra,U32.inc(index),s,remain,total,w0,w1,w2,w3,w4,w5,w6,w7,P.at(a,U32.inc(index)))

law pad7_correct:
  for +extra: Nat
  for +index: U32
  for +s: S.State
  for +remain: Nat
  for +total: Nat
  for +w0: U32
  for +w1: U32
  for +w2: U32
  for +w3: U32
  for +w4: U32
  for +w5: U32
  for pair: Array<U32> & U32
  {P.pad7(extra,index,s,remain,total,w0,w1,w2,w3,w4,w5,pair) == R.gather(extra,9n,index,True{},remain,total,s,[w5,w4,w3,w2,w1,w0],pair) : Array<U32> & S.State}

def pad7_correct(extra,index,s,remain,total,w0,w1,w2,w3,w4,w5,pair):
  (a,w6) = pair
  pad8_correct(extra,U32.inc(index),s,remain,total,w0,w1,w2,w3,w4,w5,w6,P.at(a,U32.inc(index)))

law pad6_correct:
  for +extra: Nat
  for +index: U32
  for +s: S.State
  for +remain: Nat
  for +total: Nat
  for +w0: U32
  for +w1: U32
  for +w2: U32
  for +w3: U32
  for +w4: U32
  for pair: Array<U32> & U32
  {P.pad6(extra,index,s,remain,total,w0,w1,w2,w3,w4,pair) == R.gather(extra,10n,index,True{},remain,total,s,[w4,w3,w2,w1,w0],pair) : Array<U32> & S.State}

def pad6_correct(extra,index,s,remain,total,w0,w1,w2,w3,w4,pair):
  (a,w5) = pair
  pad7_correct(extra,U32.inc(index),s,remain,total,w0,w1,w2,w3,w4,w5,P.at(a,U32.inc(index)))

law pad5_correct:
  for +extra: Nat
  for +index: U32
  for +s: S.State
  for +remain: Nat
  for +total: Nat
  for +w0: U32
  for +w1: U32
  for +w2: U32
  for +w3: U32
  for pair: Array<U32> & U32
  {P.pad5(extra,index,s,remain,total,w0,w1,w2,w3,pair) == R.gather(extra,11n,index,True{},remain,total,s,[w3,w2,w1,w0],pair) : Array<U32> & S.State}

def pad5_correct(extra,index,s,remain,total,w0,w1,w2,w3,pair):
  (a,w4) = pair
  pad6_correct(extra,U32.inc(index),s,remain,total,w0,w1,w2,w3,w4,P.at(a,U32.inc(index)))

law pad4_correct:
  for +extra: Nat
  for +index: U32
  for +s: S.State
  for +remain: Nat
  for +total: Nat
  for +w0: U32
  for +w1: U32
  for +w2: U32
  for pair: Array<U32> & U32
  {P.pad4(extra,index,s,remain,total,w0,w1,w2,pair) == R.gather(extra,12n,index,True{},remain,total,s,[w2,w1,w0],pair) : Array<U32> & S.State}

def pad4_correct(extra,index,s,remain,total,w0,w1,w2,pair):
  (a,w3) = pair
  pad5_correct(extra,U32.inc(index),s,remain,total,w0,w1,w2,w3,P.at(a,U32.inc(index)))

law pad3_correct:
  for +extra: Nat
  for +index: U32
  for +s: S.State
  for +remain: Nat
  for +total: Nat
  for +w0: U32
  for +w1: U32
  for pair: Array<U32> & U32
  {P.pad3(extra,index,s,remain,total,w0,w1,pair) == R.gather(extra,13n,index,True{},remain,total,s,[w1,w0],pair) : Array<U32> & S.State}

def pad3_correct(extra,index,s,remain,total,w0,w1,pair):
  (a,w2) = pair
  pad4_correct(extra,U32.inc(index),s,remain,total,w0,w1,w2,P.at(a,U32.inc(index)))

law pad2_correct:
  for +extra: Nat
  for +index: U32
  for +s: S.State
  for +remain: Nat
  for +total: Nat
  for +w0: U32
  for pair: Array<U32> & U32
  {P.pad2(extra,index,s,remain,total,w0,pair) == R.gather(extra,14n,index,True{},remain,total,s,[w0],pair) : Array<U32> & S.State}

def pad2_correct(extra,index,s,remain,total,w0,pair):
  (a,w1) = pair
  pad3_correct(extra,U32.inc(index),s,remain,total,w0,w1,P.at(a,U32.inc(index)))

law pad1_correct:
  for +extra: Nat
  for +index: U32
  for +s: S.State
  for +remain: Nat
  for +total: Nat
  for pair: Array<U32> & U32
  {P.pad1(extra,index,s,remain,total,pair) == R.gather(extra,15n,index,True{},remain,total,s,Nil{},pair) : Array<U32> & S.State}

def pad1_correct(extra,index,s,remain,total,pair):
  (a,w0) = pair
  pad2_correct(extra,U32.inc(index),s,remain,total,w0,P.at(a,U32.inc(index)))

law final_extra_correct:
  for +extra: Nat
  for +more: Bool
  for +total: Nat
  for pair: Array<U32> & S.State
  {P.final_extra(extra,more,total,pair) == R.final_extra(extra,more,total,pair) : Array<U32> & S.State}

def final_extra_correct(extra,more,total,pair):
  match more pair:
    case False{} Tuple{a,s}: {==}
    case True{} Tuple{a,s}:
      Equal.cong(S.State,Array<U32> & S.State,x => (a,x),
        Runtime.fips_compress16(0,0,0,0,0,0,0,0,0,0,0,0,0,0,Runtime.len_hi(total),Runtime.len_lo(total),extra,s),
        R.compress([0,0,0,0,0,0,0,0,0,0,0,0,0,0,Runtime.len_hi(total),Runtime.len_lo(total)],extra,s),
        compress_correct(0,0,0,0,0,0,0,0,0,0,0,0,0,0,Runtime.len_hi(total),Runtime.len_lo(total),extra,s))

law blocks_correct:
  for +extra: Nat
  for +n: Nat
  for +index: U32
  for +remain: Nat
  for +total: Nat
  for pair: Array<U32> & S.State
  {P.blocks(extra,n,index,remain,total,pair) == R.blocks(extra,n,index,remain,total,pair) : Array<U32> & S.State}

law blocks_zero_reified:
  for +extra: Nat
  for +index: U32
  for +remain: Nat
  for +total: Nat
  for -a: Array<U32>
  for +s: S.State
  for view: Sigma<&2,&1,A.Tree,t => {a == A.thaw(t) : Array<U32>}>
  {P.blocks(extra,0n,index,remain,total,(a,s)) == R.blocks(extra,0n,index,remain,total,(a,s)) : Array<U32> & S.State}

def blocks_zero_reified(extra,index,remain,total,a,s,view):
  match view:
    case Tuple{+tree,pf}:
      %Equal.sym(Array<U32>,a,A.thaw(tree),pf) : {P.blocks(extra,0n,index,remain,total,(_,s)) == R.blocks(extra,0n,index,remain,total,(_,s)) : Array<U32> & S.State}
      Equal.trans(Array<U32> & S.State,
        P.final_extra(extra,Nat.is_ge(remain,56n),total,P.pad1(extra,index,s,remain,total,P.at(A.thaw(tree),index))),
        R.final_extra(extra,Nat.is_ge(remain,56n),total,P.pad1(extra,index,s,remain,total,P.at(A.thaw(tree),index))),
        R.final_extra(extra,Nat.is_ge(remain,56n),total,R.gather(extra,15n,index,True{},remain,total,s,Nil{},P.at(A.thaw(tree),index))),
        final_extra_correct(extra,Nat.is_ge(remain,56n),total,P.pad1(extra,index,s,remain,total,P.at(A.thaw(tree),index))),
        Equal.cong(Array<U32> & S.State,Array<U32> & S.State,
          pair => R.final_extra(extra,Nat.is_ge(remain,56n),total,pair),
          P.pad1(extra,index,s,remain,total,P.at(A.thaw(tree),index)),R.gather(extra,15n,index,True{},remain,total,s,Nil{},P.at(A.thaw(tree),index)),
          pad1_correct(extra,index,s,remain,total,P.at(A.thaw(tree),index))))

law blocks_step_reified:
  for +p: Nat
  for +extra: Nat
  for +index: U32
  for +remain: Nat
  for +total: Nat
  for -a: Array<U32>
  for +s: S.State
  for view: Sigma<&2,&1,A.Tree,t => {a == A.thaw(t) : Array<U32>}>
  for recurse: @pair: (Array<U32> & S.State) -> {P.blocks(extra,p,U32.add(index,16),remain,total,pair) == R.blocks(extra,p,U32.add(index,16),remain,total,pair) : Array<U32> & S.State}
  {P.blocks(extra,1n+p,index,remain,total,(a,s)) == R.blocks(extra,1n+p,index,remain,total,(a,s)) : Array<U32> & S.State}

def blocks_step_reified(p,extra,index,remain,total,a,s,view,recurse):
  match view:
    case Tuple{+tree,pf}:
      %Equal.sym(Array<U32>,a,A.thaw(tree),pf) : {P.blocks(extra,1n+p,index,remain,total,(_,s)) == R.blocks(extra,1n+p,index,remain,total,(_,s)) : Array<U32> & S.State}
      Equal.trans(Array<U32> & S.State,
        P.blocks(extra,p,U32.add(index,16),remain,total,P.read1(extra,index,s,P.at(A.thaw(tree),index))),
        R.blocks(extra,p,U32.add(index,16),remain,total,P.read1(extra,index,s,P.at(A.thaw(tree),index))),
        R.blocks(extra,p,U32.add(index,16),remain,total,R.gather(extra,15n,index,False{},0n,0n,s,Nil{},P.at(A.thaw(tree),index))),
        recurse(P.read1(extra,index,s,P.at(A.thaw(tree),index))),
        Equal.cong(Array<U32> & S.State,Array<U32> & S.State,
          pair => R.blocks(extra,p,U32.add(index,16),remain,total,pair),
          P.read1(extra,index,s,P.at(A.thaw(tree),index)),R.gather(extra,15n,index,False{},0n,0n,s,Nil{},P.at(A.thaw(tree),index)),
          read1_correct(extra,index,s,P.at(A.thaw(tree),index))))

def blocks_correct(extra,n,index,remain,total,pair):
  match n pair:
    case 0n Tuple{a,s}:
      blocks_zero_reified(extra,index,remain,total,a,s,A.reify(a))
    case 1n+p Tuple{a,s}:
      blocks_step_reified(p,extra,index,remain,total,a,s,A.reify(a),
        pair => blocks_correct(extra,p,U32.add(index,16),remain,total,pair))

law hash_unchecked_correct:
  for a: Array<U32>
  for +length: Nat
  {P.hash_unchecked(a,length) == R.hash_unchecked(a,length) : S.State}

def hash_unchecked_correct(a,length):
  Equal.cong(Array<U32> & S.State,S.State,pair => P.take_state(pair),
    P.blocks(48n,Nat.div(length,64n),0,Nat.mod(length,64n),length,(a,Runtime.initial())),
    R.blocks(48n,Nat.div(length,64n),0,Nat.mod(length,64n),length,(a,Runtime.initial())),
    blocks_correct(48n,Nat.div(length,64n),0,Nat.mod(length,64n),length,(a,Runtime.initial())))

law checked_correct:
  for +valid: Bool
  for a: Array<U32>
  for +length: Nat
  {P.checked(valid,a,length) == R.checked(valid,a,length) : Maybe<&2,S.State>}

def checked_correct(valid,a,length):
  match valid:
    case False{}: {==}
    case True{}:
      Equal.cong(S.State,Maybe<&2,S.State>,s => Some{s},
        P.hash_unchecked(a,length),R.hash_unchecked(a,length),hash_unchecked_correct(a,length))

law sized_correct:
  for +length: Nat
  for pair: Array<U32> & U32
  {P.sized(length,pair) == R.sized(length,pair) : Maybe<&2,S.State>}

def sized_correct(length,pair):
  (a,capacity) = pair
  checked_correct(Nat.is_le(length,Nat.mul(4n,U32.to_nat(capacity))),a,length)

law hash_correct:
  for a: Array<U32>
  for +length: Nat
  {P.hash(a,length) == R.hash(a,length) : Maybe<&2,S.State>}

def hash_correct(a,length):
  sized_correct(length,Array.size(U32,a))

law digest_result_correct:
  for +r: Maybe<&2,S.State>
  {Legacy.packed_digest(r) == R.digest_result(r) : Maybe<&2,List<&2,U32>>}

def digest_result_correct(r):
  match r:
    case None{}: {==}
    case Some{s}:
      Equal.cong(List<&2,U32>,Maybe<&2,List<&2,U32>>,ws => Some{ws},
        C.digest(s),F.digest(s),Conformance.digest_correct(s))

law sha256_correct:
  for a: Array<U32>
  for +length: Nat
  {Legacy.sha256_packed(a,length) == R.sha256(a,length) : Maybe<&2,List<&2,U32>>}

law sha256_reified:
  for -a: Array<U32>
  for +length: Nat
  for view: Sigma<&2,&1,A.Tree,t => {a == A.thaw(t) : Array<U32>}>
  {Legacy.sha256_packed(a,length) == R.sha256(a,length) : Maybe<&2,List<&2,U32>>}
def sha256_reified(a,length,view):
  match view:
    case Tuple{+tree,pf}:
      %Equal.sym(Array<U32>,a,A.thaw(tree),pf) : {Legacy.sha256_packed(_,length) == R.sha256(_,length) : Maybe<&2,List<&2,U32>>}
      Equal.trans(Maybe<&2,List<&2,U32>>,
        Legacy.packed_digest(P.hash(A.thaw(tree),length)),R.digest_result(P.hash(A.thaw(tree),length)),R.digest_result(R.hash(A.thaw(tree),length)),
        digest_result_correct(P.hash(A.thaw(tree),length)),
        Equal.cong(Maybe<&2,S.State>,Maybe<&2,List<&2,U32>>,r => R.digest_result(r),
          P.hash(A.thaw(tree),length),R.hash(A.thaw(tree),length),hash_correct(A.thaw(tree),length)))

def sha256_correct(a,length):
  sha256_reified(a,length,A.reify(a))
