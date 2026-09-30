import Base
import ../../../src/math/u64.bend as W
import ../../../src/math/random/chacha8.bend as C8
import ../../../src/crypto/random.bend as CR
import ../../../spec/math/random/source.bend as SRC
import ../../../spec/crypto/random.bend as SCR
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/u32.bend as U
import ../../../spec/math/random/rand.bend as SR
import ../../math/random/bits.bend as BI
import ../../math/random/below.bend as BL

# bytes(g, n) (Go's ChaCha8.Read) returns the pending bytes, then the
# little-endian bytes of the next outputs: its accumulator, read back, is
# always the prefix of that byte stream.

def rev(xs: List<&2, U32>) -> List<&2, U32>:
  List.reverse(&2, U32, xs)

def app_nil(+xs: List<&2, U32>) -> {SCR.append(xs, []) == xs : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      Equal.cong(List<&2, U32>, List<&2, U32>, l => Con{x, l}, SCR.append(rest, []), rest, app_nil(rest))

def app_assoc(+xs: List<&2, U32>, +ys: List<&2, U32>, +zs: List<&2, U32>) -> {SCR.append(SCR.append(xs, ys), zs) == SCR.append(xs, SCR.append(ys, zs)) : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      Equal.cong(List<&2, U32>, List<&2, U32>, l => Con{x, l}, SCR.append(SCR.append(rest, ys), zs), SCR.append(rest, SCR.append(ys, zs)), app_assoc(rest, ys, zs))

# reverse.go(xs, ys) = reverse(xs) ++ ys
def rgo(+xs: List<&2, U32>, +ys: List<&2, U32>) -> {List.reverse.go(&2, U32, xs, ys) == SCR.append(rev(xs), ys) : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      Equal.trans(List<&2, U32>, List.reverse.go(&2, U32, t, Con{h, ys}), SCR.append(rev(t), Con{h, ys}), SCR.append(List.reverse.go(&2, U32, t, [h]), ys),
        rgo(t, Con{h, ys}),
        Equal.trans(List<&2, U32>, SCR.append(rev(t), Con{h, ys}), SCR.append(SCR.append(rev(t), [h]), ys), SCR.append(List.reverse.go(&2, U32, t, [h]), ys),
          Equal.sym(List<&2, U32>, SCR.append(SCR.append(rev(t), [h]), ys), SCR.append(rev(t), SCR.append([h], ys)), app_assoc(rev(t), [h], ys)),
          Equal.cong(List<&2, U32>, List<&2, U32>, l => SCR.append(l, ys), SCR.append(rev(t), [h]), List.reverse.go(&2, U32, t, [h]), Equal.sym(List<&2, U32>, List.reverse.go(&2, U32, t, [h]), SCR.append(rev(t), [h]), rgo(t, [h])))))

# rev(b :: acc) ++ ts = rev(acc) ++ (b :: ts)
def rev_cons(+b: U32, +acc: List<&2, U32>, +ts: List<&2, U32>) -> {SCR.append(rev(Con{b, acc}), ts) == SCR.append(rev(acc), Con{b, ts}) : List<&2, U32>}:
  Equal.trans(List<&2, U32>, SCR.append(List.reverse.go(&2, U32, acc, [b]), ts), SCR.append(SCR.append(rev(acc), [b]), ts), SCR.append(rev(acc), Con{b, ts}),
    Equal.cong(List<&2, U32>, List<&2, U32>, l => SCR.append(l, ts), List.reverse.go(&2, U32, acc, [b]), SCR.append(rev(acc), [b]), rgo(acc, [b])),
    app_assoc(rev(acc), [b], ts))

# the eight bytes of a word, split at the first
def b0(x: W.U64) -> U32:
  match x:
    case W.U64{+l, +h}:
      SCR.byte_of(l, 0n)

def b7(x: W.U64) -> List<&2, U32>:
  match x:
    case W.U64{+l, +h}:
      [SCR.byte_of(l, 8n), SCR.byte_of(l, 16n), SCR.byte_of(l, 24n), SCR.byte_of(h, 0n), SCR.byte_of(h, 8n), SCR.byte_of(h, 16n), SCR.byte_of(h, 24n)]

def le_split(+x: W.U64) -> {SCR.le_bytes(x) == Con{b0(x), b7(x)} : List<&2, U32>}:
  match x:
    case W.U64{+l, +h}:
      {==}

def outs(+k: Nat, +c: C8.ChaCha8) -> List<&2, W.U64>:
  SRC.outputs(~C8.ChaCha8, ~C8.next, k, c)

# taking j bytes never looks past the first j outputs
def prefix(+j: Nat, +r: List<&2, U32>, +c: C8.ChaCha8, +d: Nat) -> {SCR.take(j, SCR.append(r, SCR.flat(outs(Nat.add(j, d), c)))) == SCR.take(j, SCR.append(r, SCR.flat(outs(j, c)))) : List<&2, U32>}:
  match j r:
    case 0n _:
      {==}
    case 1n+i Con{+b, +rest}:
      Equal.cong(List<&2, U32>, List<&2, U32>, l => Con{b, l}, SCR.take(i, SCR.append(rest, SCR.flat(outs(1n+Nat.add(i, d), c)))), SCR.take(i, SCR.append(rest, SCR.flat(outs(1n+i, c)))),
        Equal.trans(List<&2, U32>, SCR.take(i, SCR.append(rest, SCR.flat(outs(1n+Nat.add(i, d), c)))), SCR.take(i, SCR.append(rest, SCR.flat(outs(i, c)))), SCR.take(i, SCR.append(rest, SCR.flat(outs(1n+i, c)))),
          %N.add_succ(i, d) : {SCR.take(i, SCR.append(rest, SCR.flat(outs(_, c)))) == SCR.take(i, SCR.append(rest, SCR.flat(outs(i, c)))) : List<&2, U32>}
          prefix(i, rest, c, 1n+d),
          Equal.sym(List<&2, U32>, SCR.take(i, SCR.append(rest, SCR.flat(outs(1n+i, c)))), SCR.take(i, SCR.append(rest, SCR.flat(outs(i, c)))),
            %Equal.trans(Nat, Nat.add(i, 1n), 1n+Nat.add(i, 0n), 1n+i, N.add_succ(i, 0n), Equal.cong(Nat, Nat, z => 1n+z, Nat.add(i, 0n), i, N.add_zero(i))) : {SCR.take(i, SCR.append(rest, SCR.flat(outs(_, c)))) == SCR.take(i, SCR.append(rest, SCR.flat(outs(i, c)))) : List<&2, U32>}
            prefix(i, rest, c, 1n))))
    case 1n+i Nil{}:
      +x = SRC.fst64(C8.ChaCha8, C8.next(c))
      +c1 = SRC.snd64(C8.ChaCha8, C8.next(c))
      %Equal.sym(List<&2, U32>, SCR.le_bytes(x), Con{b0(x), b7(x)}, le_split(x)) : {SCR.take(1n+i, SCR.append(_, SCR.flat(outs(Nat.add(i, d), c1)))) == SCR.take(1n+i, SCR.append(_, SCR.flat(outs(i, c1)))) : List<&2, U32>}
      Equal.cong(List<&2, U32>, List<&2, U32>, l => Con{b0(x), l}, SCR.take(i, SCR.append(b7(x), SCR.flat(outs(Nat.add(i, d), c1)))), SCR.take(i, SCR.append(b7(x), SCR.flat(outs(i, c1)))), prefix(i, b7(x), c1, d))

# ---- the fill loop ----

def facc(f: CR.Fill) -> List<&2, U32>:
  match f:
    case CR.FS{a, c, p}:
      a

def fsrc(f: CR.Fill) -> C8.ChaCha8:
  match f:
    case CR.FS{a, c, p}:
      c

def fpend(f: CR.Fill) -> List<&2, U32>:
  match f:
    case CR.FS{a, c, p}:
      p

def step_nil(+j: Nat, +acc: List<&2, U32>, q: W.U64 & C8.ChaCha8) -> {SCR.append(rev(facc(CR.split(acc, q))), SCR.take(j, SCR.append(fpend(CR.split(acc, q)), SCR.flat(outs(j, fsrc(CR.split(acc, q))))))) == SCR.append(rev(acc), SCR.take(1n+j, SCR.flat(Con{SRC.fst64(C8.ChaCha8, q), outs(j, SRC.snd64(C8.ChaCha8, q))}))) : List<&2, U32>}:
  match q:
    case Tuple{x, +c1}:
      match x:
        case W.U64{+l, +h}:
          +r7 = {[U32.and(U32.shrn(l, 8n), 255), U32.and(U32.shrn(l, 16n), 255), U32.and(U32.shrn(l, 24n), 255), U32.and(h, 255), U32.and(U32.shrn(h, 8n), 255), U32.and(U32.shrn(h, 16n), 255), U32.and(U32.shrn(h, 24n), 255)] : List<&2, U32>}
          rev_cons(U32.and(l, 255), acc, SCR.take(j, SCR.append(r7, SCR.flat(outs(j, c1)))))

# one byte of the loop against the byte stream
def step(+j: Nat, +f: CR.Fill) -> {SCR.append(rev(facc(CR.take1(f))), SCR.take(j, SCR.append(fpend(CR.take1(f)), SCR.flat(outs(j, fsrc(CR.take1(f))))))) == SCR.append(rev(facc(f)), SCR.take(1n+j, SCR.append(fpend(f), SCR.flat(outs(1n+j, fsrc(f)))))) : List<&2, U32>}:
  match f:
    case CR.FS{+acc, +c, +p}:
      match p:
        case Con{+b, +rest}:
          Equal.trans(List<&2, U32>, SCR.append(rev(Con{b, acc}), SCR.take(j, SCR.append(rest, SCR.flat(outs(j, c))))), SCR.append(rev(acc), Con{b, SCR.take(j, SCR.append(rest, SCR.flat(outs(j, c))))}), SCR.append(rev(acc), Con{b, SCR.take(j, SCR.append(rest, SCR.flat(outs(1n+j, c))))}),
            rev_cons(b, acc, SCR.take(j, SCR.append(rest, SCR.flat(outs(j, c))))),
            Equal.cong(List<&2, U32>, List<&2, U32>, z => SCR.append(rev(acc), Con{b, z}), SCR.take(j, SCR.append(rest, SCR.flat(outs(j, c)))), SCR.take(j, SCR.append(rest, SCR.flat(outs(1n+j, c)))),
              Equal.sym(List<&2, U32>, SCR.take(j, SCR.append(rest, SCR.flat(outs(1n+j, c)))), SCR.take(j, SCR.append(rest, SCR.flat(outs(j, c)))),
                %Equal.trans(Nat, Nat.add(j, 1n), 1n+Nat.add(j, 0n), 1n+j, N.add_succ(j, 0n), Equal.cong(Nat, Nat, z => 1n+z, Nat.add(j, 0n), j, N.add_zero(j))) : {SCR.take(j, SCR.append(rest, SCR.flat(outs(_, c)))) == SCR.take(j, SCR.append(rest, SCR.flat(outs(j, c)))) : List<&2, U32>}
                prefix(j, rest, c, 1n))))
        case Nil{}:
          step_nil(j, acc, C8.next(c))

# THEOREM: after k bytes the accumulator, read back, is the old one followed
# by the first k bytes of the pending bytes and the stream
def fill_inv(+k: Nat, +f: CR.Fill) -> {rev(facc(CR.fill(k, f))) == SCR.append(rev(facc(f)), SCR.take(k, SCR.append(fpend(f), SCR.flat(outs(k, fsrc(f)))))) : List<&2, U32>}:
  match k:
    case 0n:
      Equal.sym(List<&2, U32>, SCR.append(rev(facc(f)), []), rev(facc(f)), app_nil(rev(facc(f))))
    case 1n+j:
      Equal.trans(List<&2, U32>, rev(facc(CR.fill(j, CR.take1(f)))), SCR.append(rev(facc(CR.take1(f))), SCR.take(j, SCR.append(fpend(CR.take1(f)), SCR.flat(outs(j, fsrc(CR.take1(f))))))), SCR.append(rev(facc(f)), SCR.take(1n+j, SCR.append(fpend(f), SCR.flat(outs(1n+j, fsrc(f)))))),
        fill_inv(j, CR.take1(f)),
        step(j, f))

def done_bytes(+f: CR.Fill) -> {SCR.fst_bytes(CR.Gen, CR.done(f)) == rev(facc(f)) : List<&2, U32>}:
  match f:
    case CR.FS{a, c, p}:
      {==}

# a word at a time: the eight bytes split and seven take1 give
def word_eq(+acc: List<&2, U32>, q: W.U64 & C8.ChaCha8) -> {CR.word(acc, q) == CR.fill(7n, CR.split(acc, q)) : CR.Fill}:
  match q:
    case Tuple{+x, +c}:
      {==}

# fill_fast is fill
def fast_eq(+n: Nat, +f: CR.Fill) -> {CR.fill_fast(n, f) == CR.fill(n, f) : CR.Fill}:
  match n f:
    case 8n+k CR.FS{+acc, +c, Nil{}}:
      Equal.trans(CR.Fill, CR.fill_fast(k, CR.word(acc, C8.next(c))), CR.fill(k, CR.word(acc, C8.next(c))), CR.fill(k, CR.fill(7n, CR.split(acc, C8.next(c)))),
        fast_eq(k, CR.word(acc, C8.next(c))),
        Equal.cong(CR.Fill, CR.Fill, z => CR.fill(k, z), CR.word(acc, C8.next(c)), CR.fill(7n, CR.split(acc, C8.next(c))), word_eq(acc, C8.next(c))))
    case 8n+k CR.FS{+acc, +c, Con{+b, +rest}}:
      fast_eq(7n+k, CR.FS{Con{b, acc}, c, rest})
    case 7n +g:
      fast_eq(6n, CR.take1(g))
    case 6n +g:
      fast_eq(5n, CR.take1(g))
    case 5n +g:
      fast_eq(4n, CR.take1(g))
    case 4n +g:
      fast_eq(3n, CR.take1(g))
    case 3n +g:
      fast_eq(2n, CR.take1(g))
    case 2n +g:
      fast_eq(1n, CR.take1(g))
    case 1n +g:
      fast_eq(0n, CR.take1(g))
    case 0n +g:
      {==}

# THEOREM (Random.bytes)
def bytes(+n: Nat, +c: C8.ChaCha8, +p: List<&2, U32>) -> SCR.Random.bytes(n, c, p):
  Equal.trans(List<&2, U32>, SCR.fst_bytes(CR.Gen, CR.done(CR.fill_fast(n, CR.FS{[], c, p}))), SCR.fst_bytes(CR.Gen, CR.done(CR.fill(n, CR.FS{[], c, p}))), SCR.take(n, SCR.append(p, SCR.flat(outs(n, c)))),
    Equal.cong(CR.Fill, List<&2, U32>, z => SCR.fst_bytes(CR.Gen, CR.done(z)), CR.fill_fast(n, CR.FS{[], c, p}), CR.fill(n, CR.FS{[], c, p}), fast_eq(n, CR.FS{[], c, p})),
    Equal.trans(List<&2, U32>, SCR.fst_bytes(CR.Gen, CR.done(CR.fill(n, CR.FS{[], c, p}))), rev(facc(CR.fill(n, CR.FS{[], c, p}))), SCR.take(n, SCR.append(p, SCR.flat(outs(n, c)))),
      done_bytes(CR.fill(n, CR.FS{[], c, p})),
      fill_inv(n, CR.FS{[], c, p})))

# ---- every byte is below 256 ----

def and_true_r(+b: Bool) -> {Bool.and(b, True{}) == b : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def below_take(+n: Nat, +xs: List<&2, U32>, +h: {SCR.below256(xs) == True{} : Bool}) -> {SCR.below256(SCR.take(n, xs)) == True{} : Bool}:
  match n xs:
    case 0n _:
      {==}
    case 1n+p Nil{}:
      {==}
    case 1n+p Con{+x, +rest}:
      %Equal.sym(Bool, U32.is_lt(x, 256), True{}, L.and_left(U32.is_lt(x, 256), SCR.below256(rest), h)) : {Bool.and(_, SCR.below256(SCR.take(p, rest))) == True{} : Bool}
      below_take(p, rest, L.and_right(U32.is_lt(x, 256), SCR.below256(rest), h))

def below_app(+xs: List<&2, U32>, +ys: List<&2, U32>, +hx: {SCR.below256(xs) == True{} : Bool}, +hy: {SCR.below256(ys) == True{} : Bool}) -> {SCR.below256(SCR.append(xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      hy
    case Con{+x, +rest}:
      %Equal.sym(Bool, U32.is_lt(x, 256), True{}, L.and_left(U32.is_lt(x, 256), SCR.below256(rest), hx)) : {Bool.and(_, SCR.below256(SCR.append(rest, ys))) == True{} : Bool}
      below_app(rest, ys, L.and_right(U32.is_lt(x, 256), SCR.below256(rest), hx), hy)

# y & 255 < 256
def byte_lt(+y: U32) -> {U32.is_lt(U32.and(y, 255), 256) == True{} : Bool}:
  Equal.trans(Bool, U32.is_lt(U32.and(y, 255), 256), Nat.is_lt(U32.to_nat(U32.and(y, 255)), 256n), True{},
    U.is_lt_nat(U32.and(y, 255), 256),
    %Equal.sym(Nat, U32.to_nat(U32.and(y, 255)), SR.and_bits(32n, U32.to_nat(y), 255n), BI.uand(y, 255)) : {Nat.is_lt(_, 256n) == True{} : Bool}
    N.le_lt_succ(SR.and_bits(32n, U32.to_nat(y), 255n), 255n, BL.and_le(32n, U32.to_nat(y), 255n)))

def byte_of_lt(+w: U32, +k: Nat) -> {U32.is_lt(SCR.byte_of(w, k), 256) == True{} : Bool}:
  byte_lt(U32.shrn(w, k))

def le_below(+x: W.U64) -> {SCR.below256(SCR.le_bytes(x)) == True{} : Bool}:
  match x:
    case W.U64{+l, +h}:
      %Equal.sym(Bool, U32.is_lt(SCR.byte_of(l, 0n), 256), True{}, byte_of_lt(l, 0n)) : {Bool.and(_, SCR.below256([SCR.byte_of(l, 8n), SCR.byte_of(l, 16n), SCR.byte_of(l, 24n), SCR.byte_of(h, 0n), SCR.byte_of(h, 8n), SCR.byte_of(h, 16n), SCR.byte_of(h, 24n)])) == True{} : Bool}
      %Equal.sym(Bool, U32.is_lt(SCR.byte_of(l, 8n), 256), True{}, byte_of_lt(l, 8n)) : {Bool.and(_, SCR.below256([SCR.byte_of(l, 16n), SCR.byte_of(l, 24n), SCR.byte_of(h, 0n), SCR.byte_of(h, 8n), SCR.byte_of(h, 16n), SCR.byte_of(h, 24n)])) == True{} : Bool}
      %Equal.sym(Bool, U32.is_lt(SCR.byte_of(l, 16n), 256), True{}, byte_of_lt(l, 16n)) : {Bool.and(_, SCR.below256([SCR.byte_of(l, 24n), SCR.byte_of(h, 0n), SCR.byte_of(h, 8n), SCR.byte_of(h, 16n), SCR.byte_of(h, 24n)])) == True{} : Bool}
      %Equal.sym(Bool, U32.is_lt(SCR.byte_of(l, 24n), 256), True{}, byte_of_lt(l, 24n)) : {Bool.and(_, SCR.below256([SCR.byte_of(h, 0n), SCR.byte_of(h, 8n), SCR.byte_of(h, 16n), SCR.byte_of(h, 24n)])) == True{} : Bool}
      %Equal.sym(Bool, U32.is_lt(SCR.byte_of(h, 0n), 256), True{}, byte_of_lt(h, 0n)) : {Bool.and(_, SCR.below256([SCR.byte_of(h, 8n), SCR.byte_of(h, 16n), SCR.byte_of(h, 24n)])) == True{} : Bool}
      %Equal.sym(Bool, U32.is_lt(SCR.byte_of(h, 8n), 256), True{}, byte_of_lt(h, 8n)) : {Bool.and(_, SCR.below256([SCR.byte_of(h, 16n), SCR.byte_of(h, 24n)])) == True{} : Bool}
      %Equal.sym(Bool, U32.is_lt(SCR.byte_of(h, 16n), 256), True{}, byte_of_lt(h, 16n)) : {Bool.and(_, SCR.below256([SCR.byte_of(h, 24n)])) == True{} : Bool}
      %Equal.sym(Bool, U32.is_lt(SCR.byte_of(h, 24n), 256), True{}, byte_of_lt(h, 24n)) : {Bool.and(_, True{}) == True{} : Bool}
      {==}

def flat_below(+os: List<&2, W.U64>) -> {SCR.below256(SCR.flat(os)) == True{} : Bool}:
  match os:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      below_app(SCR.le_bytes(x), SCR.flat(rest), le_below(x), flat_below(rest))

# THEOREM (Random.bytes_lt)
def bytes_lt(+n: Nat, +c: C8.ChaCha8, +p: List<&2, U32>, +hp: {SCR.below256(p) == True{} : Bool}) -> SCR.Random.bytes_lt(n, c, p, hp):
  %Equal.sym(List<&2, U32>, SCR.fst_bytes(CR.Gen, CR.bytes(CR.G{c, p}, n)), SCR.take(n, SCR.append(p, SCR.flat(outs(n, c)))), bytes(n, c, p)) : {SCR.below256(_) == True{} : Bool}
  below_take(n, SCR.append(p, SCR.flat(outs(n, c))), below_app(p, SCR.flat(outs(n, c)), hp, flat_below(outs(n, c))))
