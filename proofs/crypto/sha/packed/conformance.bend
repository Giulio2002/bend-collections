import Base
import ../../../../src/crypto/sha/packed/core.bend as Runtime
import ../../../../src/crypto/sha/state.bend as S
import ./core_model.bend as C
import ../../../../spec/crypto/sha.bend as F
import ../list_proofs.bend as L
import ../padding.bend as Padding

law octets_correct:
  for +width: Nat
  for +n: Nat
  for +acc: List<&2, U32>
  {C.length_octets(width, n, acc) == List.append(&2, U32, F.octets(width, n), acc) : List<&2, U32>}

def octets_correct(width, n, acc):
  match width:
    case 0n:
      {==}
    case 1n+p:
      %L.append_assoc_reverse(U32, F.octets(p, Nat.div(n, 256n)),
        [U32.from_nat(Nat.mod(n, 256n))], acc) :
        {C.length_octets(p, Nat.div(n, 256n), U32.from_nat(Nat.mod(n, 256n)) <> acc) == _ : List<&2, U32>}
      octets_correct(p, Nat.div(n, 256n), U32.from_nat(Nat.mod(n, 256n)) <> acc)

law length_correct:
  for +n: Nat
  {C.bit_length(n) == F.length_field(n) : List<&2, U32>}

def length_correct(n):
  octets_correct(7n, Nat.div(n, 32n), [U32.shln(U32.from_nat(Nat.mod(n, 32n)), 3n)])

law nth_correct:
  for xs: List<&2, U32>
  for n: Nat
  {C.get(xs, n) == F.nth(xs, n) : U32}

def nth_correct(xs, n):
  match xs n:
    case Nil{} _:
      {==}
    case h <> t 0n:
      {==}
    case h <> t 1n+p:
      nth_correct(t, p)

law next_correct:
  for +hs: List<&2, U32>
  {C.next_word(hs) == F.recurrence(hs) : U32}

def next_correct(hs):
  match hs:
    case a <> b <> c <> d <> e <> f <> g <> h <> i <> j <> k <> l <> m <> n <> o <> (p <> rest):
      {==}
    case Nil{}:
      {==}
    case a <> Nil{}:
      {==}
    case a <> b <> Nil{}:
      {==}
    case a <> b <> c <> Nil{}:
      {==}
    case a <> b <> c <> d <> Nil{}:
      {==}
    case a <> b <> c <> d <> e <> Nil{}:
      {==}
    case a <> b <> c <> d <> e <> f <> Nil{}:
      {==}
    case a <> b <> c <> d <> e <> f <> g <> Nil{}:
      {==}
    case a <> b <> c <> d <> e <> f <> g <> h <> Nil{}:
      {==}
    case a <> b <> c <> d <> e <> f <> g <> h <> i <> Nil{}:
      {==}
    case a <> b <> c <> d <> e <> f <> g <> h <> i <> j <> Nil{}:
      {==}
    case a <> b <> c <> d <> e <> f <> g <> h <> i <> j <> k <> Nil{}:
      {==}
    case a <> b <> c <> d <> e <> f <> g <> h <> i <> j <> k <> l <> Nil{}:
      {==}
    case a <> b <> c <> d <> e <> f <> g <> h <> i <> j <> k <> l <> m <> Nil{}:
      {==}
    case a <> b <> c <> d <> e <> f <> g <> h <> i <> j <> k <> l <> m <> n <> Nil{}:
      {==}
    case a <> b <> c <> d <> e <> f <> g <> h <> i <> j <> k <> l <> m <> n <> o <> Nil{}:
      {==}

law extension_correct:
  for +n: Nat
  for +hs: List<&2, U32>
  {C.expand(n, hs) == F.extension(n, hs) : List<&2, U32>}

def extension_correct(n, hs):
  match n:
    case 0n:
      {==}
    case 1n+p:
      %next_correct(hs) : {C.expand(1n+p, hs) == _ <> F.extension(p, _ <> hs) : List<&2, U32>}
      %extension_correct(p, C.next_word(hs) <> hs) :
        {C.expand(1n+p, hs) == C.next_word(hs) <> _ : List<&2, U32>}
      {==}

law schedule_correct:
  for +extra: Nat
  for +block: List<&2, U32>
  {C.schedule(extra, block) == F.schedule(extra, block) : List<&2, U32>}

def schedule_correct(extra, block):
  Equal.cong(List<&2, U32>, List<&2, U32>, ext => List.append(&2, U32, block, ext),
    C.expand(extra, List.reverse(&2, U32, block)), F.extension(extra, List.reverse(&2, U32, block)),
    extension_correct(extra, List.reverse(&2, U32, block)))

law step_correct:
  for s: S.State
  for k: U32
  for w: U32
  {Runtime.step(s, k, w) == F.step(s, k, w) : S.State}

def step_correct(s, k, w):
  match s:
    case S.H{a, b, c, d, e, f, g, h}:
      {==}

law rounds_correct:
  for +ks: List<&2, U32>
  for +ws: List<&2, U32>
  for +s: S.State
  {C.rounds(ks, ws, s) == F.rounds(ks, ws)(s) : S.State}

def rounds_correct(ks, ws, s):
  match ks ws:
    case Nil{} _:
      {==}
    case k <> kt Nil{}:
      {==}
    case k <> kt w <> wt:
      %step_correct(s, k, w) :
        {C.rounds(kt, wt, Runtime.step(s, k, w)) == F.rounds(kt, wt)(_) : S.State}
      rounds_correct(kt, wt, Runtime.step(s, k, w))

law feedforward_correct:
  for x: S.State
  for y: S.State
  {Runtime.feedforward(x, y) == F.feedforward(x, y) : S.State}

def feedforward_correct(x, y):
  match x y:
    case S.H{a, b, c, d, e, f, g, h} S.H{i, j, k, l, m, n, o, p}:
      {==}

law compression_correct:
  for +ws: List<&2, U32>
  for +ks: List<&2, U32>
  for +s: S.State
  {C.compress(ws, ks, s) == F.compress(ws, ks, s) : S.State}

def compression_correct(ws, ks, s):
  %feedforward_correct(s, F.rounds(ks, ws)(s)) : {C.compress(ws, ks, s) == _ : S.State}
  Equal.cong(S.State, S.State, r => Runtime.feedforward(s, r),
    C.rounds(ks, ws, s), F.rounds(ks, ws)(s), rounds_correct(ks, ws, s))

law expanded_rounds_correct:
  for +n: Nat
  for +history: List<&2, U32>
  for +ks: List<&2, U32>
  for +s: S.State
  {C.expanded_rounds(n, history, ks, s) == C.rounds(ks, C.expand(n, history), s) : S.State}

def expanded_rounds_correct(n, history, ks, s):
  match n ks:
    case 0n Nil{}:
      {==}
    case 0n k <> kt:
      {==}
    case 1n+p Nil{}:
      {==}
    case 1n+p k <> kt:
      expanded_rounds_correct(p, C.next_word(history) <> history, kt,
        Runtime.step(s, k, C.next_word(history)))

law schedule_rounds_correct:
  for +ws: List<&2, U32>
  for +extra: Nat
  for +history: List<&2, U32>
  for +ks: List<&2, U32>
  for +s: S.State
  {C.schedule_rounds(ws, extra, history, ks, s) ==
    C.rounds(ks, List.append(&2, U32, ws, C.expand(extra, history)), s) : S.State}

def schedule_rounds_correct(ws, extra, history, ks, s):
  match ws ks:
    case Nil{} _:
      expanded_rounds_correct(extra, history, ks, s)
    case w <> wt Nil{}:
      {==}
    case w <> wt k <> kt:
      schedule_rounds_correct(wt, extra, history, kt, Runtime.step(s, k, w))

law fused_compress_correct:
  for +block: List<&2, U32>
  for +extra: Nat
  for +ks: List<&2, U32>
  for +s: S.State
  {C.fused_compress(block, extra, ks, s) == C.compress(C.schedule(extra, block), ks, s) : S.State}

law fused_compress_slow_correct:
  for +block: List<&2, U32>
  for +extra: Nat
  for +ks: List<&2, U32>
  for +s: S.State
  {C.fused_compress_slow(block, extra, ks, s) == C.compress(C.schedule(extra, block), ks, s) : S.State}

def fused_compress_slow_correct(block, extra, ks, s):
  Equal.cong(S.State, S.State, r => Runtime.feedforward(s, r),
    C.schedule_rounds(block, extra, List.reverse(&2, U32, block), ks, s),
    C.rounds(ks, List.append(&2, U32, block,
      C.expand(extra, List.reverse(&2, U32, block))), s),
    schedule_rounds_correct(block, extra, List.reverse(&2, U32, block), ks, s))

law window_rounds_correct:
  for +q: Nat
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
  for +rest: List<&2, U32>
  for +ks: List<&2, U32>
  for +s: S.State
  {C.window_rounds(q, Runtime.W{a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p}, ks, s) ==
    C.expanded_rounds(q, a <> b <> c <> d <> e <> f <> g <> h <> i <> j <> k <> l <> m <> n <> o <> p <> rest, ks, s) : S.State}

def window_rounds_correct(q, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, rest, ks, s):
  match q ks:
    case 0n Nil{}:
      {==}
    case 0n x <> xt:
      {==}
    case 1n+r Nil{}:
      {==}
    case 1n+r x <> xt:
      window_rounds_correct(r,
        (Runtime.small1(b) + g + Runtime.small0(o) + p : U32),
        a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p <> rest, xt,
        Runtime.step(s, x, (Runtime.small1(b) + g + Runtime.small0(o) + p : U32)))

law window_schedule_rounds_correct:
  for +ws: List<&2, U32>
  for +extra: Nat
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
  for +rest: List<&2, U32>
  for +ks: List<&2, U32>
  for +s: S.State
  {C.window_schedule_rounds(ws, extra, Runtime.W{a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p}, ks, s) ==
    C.schedule_rounds(ws, extra, a <> b <> c <> d <> e <> f <> g <> h <> i <> j <> k <> l <> m <> n <> o <> p <> rest, ks, s) : S.State}

def window_schedule_rounds_correct(ws, extra, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, rest, ks, s):
  match ws ks:
    case Nil{} _:
      window_rounds_correct(extra, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, rest, ks, s)
    case w <> wt Nil{}:
      {==}
    case w <> wt x <> xt:
      window_schedule_rounds_correct(wt, extra, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p,
        rest, xt, Runtime.step(s, x, w))

def fused_compress_correct(block, extra, ks, s):
  match block:
    case a <> b <> c <> d <> e <> f <> g <> h <> i <> j <> k <> l <> m <> n <> o <> p <> Nil{}:
      Equal.trans(S.State,
        Runtime.feedforward(s, C.window_schedule_rounds(
          [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p], extra,
          Runtime.W{p, o, n, m, l, k, j, i, h, g, f, e, d, c, b, a}, ks, s)),
        Runtime.feedforward(s, C.schedule_rounds(
          [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p], extra,
          [p, o, n, m, l, k, j, i, h, g, f, e, d, c, b, a], ks, s)),
        Runtime.feedforward(s, C.rounds(ks, List.append(&2, U32,
          [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p],
          C.expand(extra, [p, o, n, m, l, k, j, i, h, g, f, e, d, c, b, a])), s)),
        Equal.cong(S.State, S.State, r => Runtime.feedforward(s, r),
          C.window_schedule_rounds(
            [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p], extra,
            Runtime.W{p, o, n, m, l, k, j, i, h, g, f, e, d, c, b, a}, ks, s),
          C.schedule_rounds(
            [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p], extra,
            [p, o, n, m, l, k, j, i, h, g, f, e, d, c, b, a], ks, s),
          window_schedule_rounds_correct(
            [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p], extra,
            p, o, n, m, l, k, j, i, h, g, f, e, d, c, b, a, Nil{}, ks, s)),
        Equal.cong(S.State, S.State, r => Runtime.feedforward(s, r),
          C.schedule_rounds(
            [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p], extra,
            [p, o, n, m, l, k, j, i, h, g, f, e, d, c, b, a], ks, s),
          C.rounds(ks, List.append(&2, U32,
            [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p],
            C.expand(extra, [p, o, n, m, l, k, j, i, h, g, f, e, d, c, b, a])), s),
          schedule_rounds_correct(
            [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p], extra,
            [p, o, n, m, l, k, j, i, h, g, f, e, d, c, b, a], ks, s)))
    case a <> b <> c <> d <> e <> f <> g <> h <> i <> j <> k <> l <> m <> n <> o <> p <> q <> rest:
      fused_compress_slow_correct(a <> b <> c <> d <> e <> f <> g <> h <> i <> j <> k <> l <> m <> n <> o <> p <> q <> rest, extra, ks, s)
    case Nil{}:
      fused_compress_slow_correct(Nil{}, extra, ks, s)
    case a <> Nil{}:
      fused_compress_slow_correct(a <> Nil{}, extra, ks, s)
    case a <> b <> Nil{}:
      fused_compress_slow_correct(a <> b <> Nil{}, extra, ks, s)
    case a <> b <> c <> Nil{}:
      fused_compress_slow_correct(a <> b <> c <> Nil{}, extra, ks, s)
    case a <> b <> c <> d <> Nil{}:
      fused_compress_slow_correct(a <> b <> c <> d <> Nil{}, extra, ks, s)
    case a <> b <> c <> d <> e <> Nil{}:
      fused_compress_slow_correct(a <> b <> c <> d <> e <> Nil{}, extra, ks, s)
    case a <> b <> c <> d <> e <> f <> Nil{}:
      fused_compress_slow_correct(a <> b <> c <> d <> e <> f <> Nil{}, extra, ks, s)
    case a <> b <> c <> d <> e <> f <> g <> Nil{}:
      fused_compress_slow_correct(a <> b <> c <> d <> e <> f <> g <> Nil{}, extra, ks, s)
    case a <> b <> c <> d <> e <> f <> g <> h <> Nil{}:
      fused_compress_slow_correct(a <> b <> c <> d <> e <> f <> g <> h <> Nil{}, extra, ks, s)
    case a <> b <> c <> d <> e <> f <> g <> h <> i <> Nil{}:
      fused_compress_slow_correct(a <> b <> c <> d <> e <> f <> g <> h <> i <> Nil{}, extra, ks, s)
    case a <> b <> c <> d <> e <> f <> g <> h <> i <> j <> Nil{}:
      fused_compress_slow_correct(a <> b <> c <> d <> e <> f <> g <> h <> i <> j <> Nil{}, extra, ks, s)
    case a <> b <> c <> d <> e <> f <> g <> h <> i <> j <> k <> Nil{}:
      fused_compress_slow_correct(a <> b <> c <> d <> e <> f <> g <> h <> i <> j <> k <> Nil{}, extra, ks, s)
    case a <> b <> c <> d <> e <> f <> g <> h <> i <> j <> k <> l <> Nil{}:
      fused_compress_slow_correct(a <> b <> c <> d <> e <> f <> g <> h <> i <> j <> k <> l <> Nil{}, extra, ks, s)
    case a <> b <> c <> d <> e <> f <> g <> h <> i <> j <> k <> l <> m <> Nil{}:
      fused_compress_slow_correct(a <> b <> c <> d <> e <> f <> g <> h <> i <> j <> k <> l <> m <> Nil{}, extra, ks, s)
    case a <> b <> c <> d <> e <> f <> g <> h <> i <> j <> k <> l <> m <> n <> Nil{}:
      fused_compress_slow_correct(a <> b <> c <> d <> e <> f <> g <> h <> i <> j <> k <> l <> m <> n <> Nil{}, extra, ks, s)
    case a <> b <> c <> d <> e <> f <> g <> h <> i <> j <> k <> l <> m <> n <> o <> Nil{}:
      fused_compress_slow_correct(a <> b <> c <> d <> e <> f <> g <> h <> i <> j <> k <> l <> m <> n <> o <> Nil{}, extra, ks, s)

law window_compress16_correct:
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
  for +ks: List<&2, U32>
  for +s: S.State
  {C.window_compress16(a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, extra, ks, s) ==
    C.fused_compress([a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p], extra, ks, s) : S.State}

def window_compress16_correct(a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, extra, ks, s):
  match ks:
    case k0 <> k1 <> k2 <> k3 <> k4 <> k5 <> k6 <> k7 <> k8 <> k9 <> k10 <> k11 <> k12 <> k13 <> k14 <> k15 <> kt:
      {==}
    case Nil{}:
      {==}
    case k0 <> Nil{}:
      {==}
    case k0 <> k1 <> Nil{}:
      {==}
    case k0 <> k1 <> k2 <> Nil{}:
      {==}
    case k0 <> k1 <> k2 <> k3 <> Nil{}:
      {==}
    case k0 <> k1 <> k2 <> k3 <> k4 <> Nil{}:
      {==}
    case k0 <> k1 <> k2 <> k3 <> k4 <> k5 <> Nil{}:
      {==}
    case k0 <> k1 <> k2 <> k3 <> k4 <> k5 <> k6 <> Nil{}:
      {==}
    case k0 <> k1 <> k2 <> k3 <> k4 <> k5 <> k6 <> k7 <> Nil{}:
      {==}
    case k0 <> k1 <> k2 <> k3 <> k4 <> k5 <> k6 <> k7 <> k8 <> Nil{}:
      {==}
    case k0 <> k1 <> k2 <> k3 <> k4 <> k5 <> k6 <> k7 <> k8 <> k9 <> Nil{}:
      {==}
    case k0 <> k1 <> k2 <> k3 <> k4 <> k5 <> k6 <> k7 <> k8 <> k9 <> k10 <> Nil{}:
      {==}
    case k0 <> k1 <> k2 <> k3 <> k4 <> k5 <> k6 <> k7 <> k8 <> k9 <> k10 <> k11 <> Nil{}:
      {==}
    case k0 <> k1 <> k2 <> k3 <> k4 <> k5 <> k6 <> k7 <> k8 <> k9 <> k10 <> k11 <> k12 <> Nil{}:
      {==}
    case k0 <> k1 <> k2 <> k3 <> k4 <> k5 <> k6 <> k7 <> k8 <> k9 <> k10 <> k11 <> k12 <> k13 <> Nil{}:
      {==}
    case k0 <> k1 <> k2 <> k3 <> k4 <> k5 <> k6 <> k7 <> k8 <> k9 <> k10 <> k11 <> k12 <> k13 <> k14 <> Nil{}:
      {==}

law digest_correct:
  for s: S.State
  {C.digest(s) == F.digest(s) : List<&2, U32>}

def digest_correct(s):
  match s:
    case S.H{a, b, c, d, e, f, g, h}:
      {==}

law block_bytes_correct:
  for +bytes: List<&2, U32>
  for +extra: Nat
  for +ks: List<&2, U32>
  for +s: S.State
  {C.block_bytes(bytes, extra, ks, s) == F.blocks(F.schedules(F.words(bytes), extra), ks)(s) : S.State}

def block_bytes_correct(bytes, extra, ks, s):
  match bytes:
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> b59 <> b60 <> b61 <> b62 <> b63 <> rest:
      +block = {[
        Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15),
        Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31),
        Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, b38, b39), Runtime.pack(b40, b41, b42, b43), Runtime.pack(b44, b45, b46, b47),
        Runtime.pack(b48, b49, b50, b51), Runtime.pack(b52, b53, b54, b55), Runtime.pack(b56, b57, b58, b59), Runtime.pack(b60, b61, b62, b63)
      ] : List<&2, U32>}
      +fast = C.window_compress16(
        Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15),
        Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31),
        Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, b38, b39), Runtime.pack(b40, b41, b42, b43), Runtime.pack(b44, b45, b46, b47),
        Runtime.pack(b48, b49, b50, b51), Runtime.pack(b52, b53, b54, b55), Runtime.pack(b56, b57, b58, b59), Runtime.pack(b60, b61, b62, b63),
        extra, ks, s)
      %schedule_correct(extra, block) :
        {C.block_bytes(rest, extra, ks, fast) == F.blocks(F.schedules(F.words(rest), extra), ks)(F.compress(_, ks, s)) : S.State}
      %compression_correct(C.schedule(extra, block), ks, s) :
        {C.block_bytes(rest, extra, ks, fast) == F.blocks(F.schedules(F.words(rest), extra), ks)(_) : S.State}
      %fused_compress_correct(block, extra, ks, s) :
        {C.block_bytes(rest, extra, ks, fast) == F.blocks(F.schedules(F.words(rest), extra), ks)(_) : S.State}
      %window_compress16_correct(
        Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15),
        Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31),
        Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, b38, b39), Runtime.pack(b40, b41, b42, b43), Runtime.pack(b44, b45, b46, b47),
        Runtime.pack(b48, b49, b50, b51), Runtime.pack(b52, b53, b54, b55), Runtime.pack(b56, b57, b58, b59), Runtime.pack(b60, b61, b62, b63),
        extra, ks, s) :
        {C.block_bytes(rest, extra, ks, fast) == F.blocks(F.schedules(F.words(rest), extra), ks)(_) : S.State}
      block_bytes_correct(rest, extra, ks, fast)
    case Nil{}:
      {==}
    case b0 <> Nil{}:
      {==}
    case b0 <> b1 <> Nil{}:
      {==}
    case b0 <> b1 <> b2 <> Nil{}:
      {==}
    case b0 <> b1 <> b2 <> b3 <> Nil{}:
      {==}
    case b0 <> b1 <> b2 <> b3 <> b4 <> Nil{}:
      {==}
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> Nil{}:
      {==}
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> Nil{}:
      {==}
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> Nil{}:
      {==}
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> Nil{}:
      {==}
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> Nil{}:
      {==}
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> Nil{}:
      {==}
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> Nil{}:
      {==}
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> Nil{}:
      {==}
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> Nil{}:
      {==}
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> Nil{}:
      {==}
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> Nil{}:
      {==}
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> Nil{}:
      {==}
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> Nil{}:
      {==}
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> Nil{}:
      {==}
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> Nil{}:
      {==}
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> Nil{}:
      {==}
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> Nil{}:
      {==}
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> Nil{}:
      {==}
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> Nil{}:
      {==}
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> Nil{}:
      {==}
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> Nil{}:
      {==}
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> Nil{}:
      {==}
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> Nil{}:
      {==}
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> Nil{}:
      {==}
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> Nil{}:
      {==}
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> Nil{}:
      {==}
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> Nil{}:
      {==}
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> Nil{}:
      {==}
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> Nil{}:
      {==}
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> Nil{}:
      {==}
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> Nil{}:
      {==}
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> Nil{}:
      {==}
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> Nil{}:
      {==}
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> Nil{}:
      {==}
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> Nil{}:
      {==}
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> Nil{}:
      {==}
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> Nil{}:
      {==}
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> Nil{}:
      {==}
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> Nil{}:
      {==}
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> Nil{}:
      {==}
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> Nil{}:
      {==}
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> Nil{}:
      {==}
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> Nil{}:
      {==}
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> Nil{}:
      {==}
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> Nil{}:
      {==}
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> Nil{}:
      {==}
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> Nil{}:
      {==}
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> Nil{}:
      {==}
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> Nil{}:
      {==}
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> Nil{}:
      {==}
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> Nil{}:
      {==}
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> Nil{}:
      {==}
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> Nil{}:
      {==}
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> Nil{}:
      {==}
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> b59 <> Nil{}:
      {==}
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> b59 <> b60 <> Nil{}:
      {==}
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> b59 <> b60 <> b61 <> Nil{}:
      {==}
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> b59 <> b60 <> b61 <> b62 <> Nil{}:
      {==}

law suffix_correct:
  for +n: Nat
  {C.suffix(n) == F.padding_suffix(n) : List<&2, U32>}

def suffix_correct(n):
  %Padding.zeros_correct(Nat.mod(n, 64n)) :
    {C.suffix(n) == 128 <> List.append(&2, U32, List.replicate(U32, _, 0), F.length_field(n)) : List<&2, U32>}
  %length_correct(n) :
    {C.suffix(n) == 128 <> List.append(&2, U32,
      List.replicate(U32, Nat.mod(Nat.sub(119n, Nat.mod(n, 64n)), 64n), 0), _) : List<&2, U32>}
  {==}

# Byte counts of whole blocks: 64 * k, built the way stream accumulates them.
def mul64(k: Nat) -> Nat:
  match k:
    case 0n:
      0n
    case 1n+p:
      Nat.add(64n, mul64(p))

# The quotient accumulator never affects the remainder computed by divmod.
law mod_quotient:
  for +x: Nat
  for +m: Nat
  for +d: Nat
  for +e: Nat
  for +r: Nat
  {Nat.mod.fin(Nat.divmod.go(x, m, d, r)) == Nat.mod.fin(Nat.divmod.go(x, m, e, r)) : Nat}

def mod_quotient(x, m, d, e, r):
  match x m:
    case 0n _:
      {==}
    case 1n+p 0n:
      mod_quotient(p, r, 1n+d, 1n+e, 0n)
    case 1n+p 1n+q:
      mod_quotient(p, q, d, e, 1n+r)

# Sixty-four divmod steps return to the initial counter state with a larger quotient.
law mod_shift:
  for +x: Nat
  {Nat.mod(Nat.add(64n, x), 64n) == Nat.mod(x, 64n) : Nat}

def mod_shift(x):
  mod_quotient(x, 63n, 1n, 0n, 0n)

law mod_tail:
  for +x: Nat
  for +k: Nat
  {Nat.mod(Nat.add(x, mul64(k)), 64n) == Nat.mod(x, 64n) : Nat}

def mod_tail(x, k):
  match k:
    case 0n:
      %L.add_zero(x) : {Nat.mod(Nat.add(x, 0n), 64n) == Nat.mod(_, 64n) : Nat}
      {==}
    case 1n+p:
      Equal.trans(Nat, Nat.mod(Nat.add(x, Nat.add(64n, mul64(p))), 64n),
        Nat.mod(Nat.add(64n, Nat.add(x, mul64(p))), 64n), Nat.mod(x, 64n),
        Equal.cong(Nat, Nat, y => Nat.mod(y, 64n),
          Nat.add(x, Nat.add(64n, mul64(p))), Nat.add(64n, Nat.add(x, mul64(p))),
          L.add_swap(x, 64n, mul64(p))),
        Equal.trans(Nat, Nat.mod(Nat.add(64n, Nat.add(x, mul64(p))), 64n),
          Nat.mod(Nat.add(x, mul64(p)), 64n), Nat.mod(x, 64n),
          mod_shift(Nat.add(x, mul64(p))), mod_tail(x, p)))

# Each literal-constant round refines one step of window_rounds over the
# remaining FIPS constants; the window variables stay abstract, so every proof
# is one unfolding followed by the next round's lemma.
law kr64_correct:
  for +q: Nat
  for +win: Runtime.ShaWindow
  for +s: S.State
  {Runtime.kr64(q, win, s) == C.window_rounds(q, win, Nil{}, s) : S.State}

def kr64_correct(q, win, s):
  match q win:
    case 0n _:
      {==}
    case 1n+z Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}:
      {==}

law kr63_correct:
  for +q: Nat
  for +x0: U32
  for +x1: U32
  for +x2: U32
  for +x3: U32
  for +x4: U32
  for +x5: U32
  for +x6: U32
  for +x7: U32
  for +x8: U32
  for +x9: U32
  for +x10: U32
  for +x11: U32
  for +x12: U32
  for +x13: U32
  for +x14: U32
  for +x15: U32
  for +s: S.State
  {Runtime.kr63(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, s) ==
    C.window_rounds(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, [3329325298], s) : S.State}

def kr63_correct(q, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, s):
  match q:
    case 0n:
      {==}
    case 1n+z:
      kr64_correct(z, Runtime.W{(Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32), x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14},
        Runtime.step(s, 3329325298, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32)))

law kr62_correct:
  for +q: Nat
  for +x0: U32
  for +x1: U32
  for +x2: U32
  for +x3: U32
  for +x4: U32
  for +x5: U32
  for +x6: U32
  for +x7: U32
  for +x8: U32
  for +x9: U32
  for +x10: U32
  for +x11: U32
  for +x12: U32
  for +x13: U32
  for +x14: U32
  for +x15: U32
  for +s: S.State
  {Runtime.kr62(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, s) ==
    C.window_rounds(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, [3204031479, 3329325298], s) : S.State}

def kr62_correct(q, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, s):
  match q:
    case 0n:
      {==}
    case 1n+z:
      kr63_correct(z, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32), x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14,
        Runtime.step(s, 3204031479, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32)))

law kr61_correct:
  for +q: Nat
  for +x0: U32
  for +x1: U32
  for +x2: U32
  for +x3: U32
  for +x4: U32
  for +x5: U32
  for +x6: U32
  for +x7: U32
  for +x8: U32
  for +x9: U32
  for +x10: U32
  for +x11: U32
  for +x12: U32
  for +x13: U32
  for +x14: U32
  for +x15: U32
  for +s: S.State
  {Runtime.kr61(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, s) ==
    C.window_rounds(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, [2756734187, 3204031479, 3329325298], s) : S.State}

def kr61_correct(q, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, s):
  match q:
    case 0n:
      {==}
    case 1n+z:
      kr62_correct(z, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32), x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14,
        Runtime.step(s, 2756734187, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32)))

law kr60_correct:
  for +q: Nat
  for +x0: U32
  for +x1: U32
  for +x2: U32
  for +x3: U32
  for +x4: U32
  for +x5: U32
  for +x6: U32
  for +x7: U32
  for +x8: U32
  for +x9: U32
  for +x10: U32
  for +x11: U32
  for +x12: U32
  for +x13: U32
  for +x14: U32
  for +x15: U32
  for +s: S.State
  {Runtime.kr60(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, s) ==
    C.window_rounds(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, [2428436474, 2756734187, 3204031479, 3329325298], s) : S.State}

def kr60_correct(q, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, s):
  match q:
    case 0n:
      {==}
    case 1n+z:
      kr61_correct(z, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32), x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14,
        Runtime.step(s, 2428436474, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32)))

law kr59_correct:
  for +q: Nat
  for +x0: U32
  for +x1: U32
  for +x2: U32
  for +x3: U32
  for +x4: U32
  for +x5: U32
  for +x6: U32
  for +x7: U32
  for +x8: U32
  for +x9: U32
  for +x10: U32
  for +x11: U32
  for +x12: U32
  for +x13: U32
  for +x14: U32
  for +x15: U32
  for +s: S.State
  {Runtime.kr59(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, s) ==
    C.window_rounds(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, [2361852424, 2428436474, 2756734187, 3204031479, 3329325298], s) : S.State}

def kr59_correct(q, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, s):
  match q:
    case 0n:
      {==}
    case 1n+z:
      kr60_correct(z, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32), x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14,
        Runtime.step(s, 2361852424, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32)))

law kr58_correct:
  for +q: Nat
  for +x0: U32
  for +x1: U32
  for +x2: U32
  for +x3: U32
  for +x4: U32
  for +x5: U32
  for +x6: U32
  for +x7: U32
  for +x8: U32
  for +x9: U32
  for +x10: U32
  for +x11: U32
  for +x12: U32
  for +x13: U32
  for +x14: U32
  for +x15: U32
  for +s: S.State
  {Runtime.kr58(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, s) ==
    C.window_rounds(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, [2227730452, 2361852424, 2428436474, 2756734187, 3204031479, 3329325298], s) : S.State}

def kr58_correct(q, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, s):
  match q:
    case 0n:
      {==}
    case 1n+z:
      kr59_correct(z, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32), x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14,
        Runtime.step(s, 2227730452, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32)))

law kr57_correct:
  for +q: Nat
  for +x0: U32
  for +x1: U32
  for +x2: U32
  for +x3: U32
  for +x4: U32
  for +x5: U32
  for +x6: U32
  for +x7: U32
  for +x8: U32
  for +x9: U32
  for +x10: U32
  for +x11: U32
  for +x12: U32
  for +x13: U32
  for +x14: U32
  for +x15: U32
  for +s: S.State
  {Runtime.kr57(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, s) ==
    C.window_rounds(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, [2024104815, 2227730452, 2361852424, 2428436474, 2756734187, 3204031479, 3329325298], s) : S.State}

def kr57_correct(q, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, s):
  match q:
    case 0n:
      {==}
    case 1n+z:
      kr58_correct(z, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32), x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14,
        Runtime.step(s, 2024104815, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32)))

law kr56_correct:
  for +q: Nat
  for +x0: U32
  for +x1: U32
  for +x2: U32
  for +x3: U32
  for +x4: U32
  for +x5: U32
  for +x6: U32
  for +x7: U32
  for +x8: U32
  for +x9: U32
  for +x10: U32
  for +x11: U32
  for +x12: U32
  for +x13: U32
  for +x14: U32
  for +x15: U32
  for +s: S.State
  {Runtime.kr56(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, s) ==
    C.window_rounds(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, [1955562222, 2024104815, 2227730452, 2361852424, 2428436474, 2756734187, 3204031479, 3329325298], s) : S.State}

def kr56_correct(q, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, s):
  match q:
    case 0n:
      {==}
    case 1n+z:
      kr57_correct(z, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32), x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14,
        Runtime.step(s, 1955562222, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32)))

law kr55_correct:
  for +q: Nat
  for +x0: U32
  for +x1: U32
  for +x2: U32
  for +x3: U32
  for +x4: U32
  for +x5: U32
  for +x6: U32
  for +x7: U32
  for +x8: U32
  for +x9: U32
  for +x10: U32
  for +x11: U32
  for +x12: U32
  for +x13: U32
  for +x14: U32
  for +x15: U32
  for +s: S.State
  {Runtime.kr55(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, s) ==
    C.window_rounds(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, [1747873779, 1955562222, 2024104815, 2227730452, 2361852424, 2428436474, 2756734187, 3204031479, 3329325298], s) : S.State}

def kr55_correct(q, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, s):
  match q:
    case 0n:
      {==}
    case 1n+z:
      kr56_correct(z, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32), x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14,
        Runtime.step(s, 1747873779, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32)))

law kr54_correct:
  for +q: Nat
  for +x0: U32
  for +x1: U32
  for +x2: U32
  for +x3: U32
  for +x4: U32
  for +x5: U32
  for +x6: U32
  for +x7: U32
  for +x8: U32
  for +x9: U32
  for +x10: U32
  for +x11: U32
  for +x12: U32
  for +x13: U32
  for +x14: U32
  for +x15: U32
  for +s: S.State
  {Runtime.kr54(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, s) ==
    C.window_rounds(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, [1537002063, 1747873779, 1955562222, 2024104815, 2227730452, 2361852424, 2428436474, 2756734187, 3204031479, 3329325298], s) : S.State}

def kr54_correct(q, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, s):
  match q:
    case 0n:
      {==}
    case 1n+z:
      kr55_correct(z, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32), x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14,
        Runtime.step(s, 1537002063, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32)))

law kr53_correct:
  for +q: Nat
  for +x0: U32
  for +x1: U32
  for +x2: U32
  for +x3: U32
  for +x4: U32
  for +x5: U32
  for +x6: U32
  for +x7: U32
  for +x8: U32
  for +x9: U32
  for +x10: U32
  for +x11: U32
  for +x12: U32
  for +x13: U32
  for +x14: U32
  for +x15: U32
  for +s: S.State
  {Runtime.kr53(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, s) ==
    C.window_rounds(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, [1322822218, 1537002063, 1747873779, 1955562222, 2024104815, 2227730452, 2361852424, 2428436474, 2756734187, 3204031479, 3329325298], s) : S.State}

def kr53_correct(q, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, s):
  match q:
    case 0n:
      {==}
    case 1n+z:
      kr54_correct(z, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32), x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14,
        Runtime.step(s, 1322822218, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32)))

law kr52_correct:
  for +q: Nat
  for +x0: U32
  for +x1: U32
  for +x2: U32
  for +x3: U32
  for +x4: U32
  for +x5: U32
  for +x6: U32
  for +x7: U32
  for +x8: U32
  for +x9: U32
  for +x10: U32
  for +x11: U32
  for +x12: U32
  for +x13: U32
  for +x14: U32
  for +x15: U32
  for +s: S.State
  {Runtime.kr52(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, s) ==
    C.window_rounds(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, [958139571, 1322822218, 1537002063, 1747873779, 1955562222, 2024104815, 2227730452, 2361852424, 2428436474, 2756734187, 3204031479, 3329325298], s) : S.State}

def kr52_correct(q, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, s):
  match q:
    case 0n:
      {==}
    case 1n+z:
      kr53_correct(z, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32), x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14,
        Runtime.step(s, 958139571, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32)))

law kr51_correct:
  for +q: Nat
  for +x0: U32
  for +x1: U32
  for +x2: U32
  for +x3: U32
  for +x4: U32
  for +x5: U32
  for +x6: U32
  for +x7: U32
  for +x8: U32
  for +x9: U32
  for +x10: U32
  for +x11: U32
  for +x12: U32
  for +x13: U32
  for +x14: U32
  for +x15: U32
  for +s: S.State
  {Runtime.kr51(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, s) ==
    C.window_rounds(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, [883997877, 958139571, 1322822218, 1537002063, 1747873779, 1955562222, 2024104815, 2227730452, 2361852424, 2428436474, 2756734187, 3204031479, 3329325298], s) : S.State}

def kr51_correct(q, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, s):
  match q:
    case 0n:
      {==}
    case 1n+z:
      kr52_correct(z, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32), x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14,
        Runtime.step(s, 883997877, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32)))

law kr50_correct:
  for +q: Nat
  for +x0: U32
  for +x1: U32
  for +x2: U32
  for +x3: U32
  for +x4: U32
  for +x5: U32
  for +x6: U32
  for +x7: U32
  for +x8: U32
  for +x9: U32
  for +x10: U32
  for +x11: U32
  for +x12: U32
  for +x13: U32
  for +x14: U32
  for +x15: U32
  for +s: S.State
  {Runtime.kr50(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, s) ==
    C.window_rounds(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, [659060556, 883997877, 958139571, 1322822218, 1537002063, 1747873779, 1955562222, 2024104815, 2227730452, 2361852424, 2428436474, 2756734187, 3204031479, 3329325298], s) : S.State}

def kr50_correct(q, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, s):
  match q:
    case 0n:
      {==}
    case 1n+z:
      kr51_correct(z, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32), x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14,
        Runtime.step(s, 659060556, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32)))

law kr49_correct:
  for +q: Nat
  for +x0: U32
  for +x1: U32
  for +x2: U32
  for +x3: U32
  for +x4: U32
  for +x5: U32
  for +x6: U32
  for +x7: U32
  for +x8: U32
  for +x9: U32
  for +x10: U32
  for +x11: U32
  for +x12: U32
  for +x13: U32
  for +x14: U32
  for +x15: U32
  for +s: S.State
  {Runtime.kr49(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, s) ==
    C.window_rounds(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, [506948616, 659060556, 883997877, 958139571, 1322822218, 1537002063, 1747873779, 1955562222, 2024104815, 2227730452, 2361852424, 2428436474, 2756734187, 3204031479, 3329325298], s) : S.State}

def kr49_correct(q, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, s):
  match q:
    case 0n:
      {==}
    case 1n+z:
      kr50_correct(z, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32), x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14,
        Runtime.step(s, 506948616, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32)))

law kr48_correct:
  for +q: Nat
  for +x0: U32
  for +x1: U32
  for +x2: U32
  for +x3: U32
  for +x4: U32
  for +x5: U32
  for +x6: U32
  for +x7: U32
  for +x8: U32
  for +x9: U32
  for +x10: U32
  for +x11: U32
  for +x12: U32
  for +x13: U32
  for +x14: U32
  for +x15: U32
  for +s: S.State
  {Runtime.kr48(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, s) ==
    C.window_rounds(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, [430227734, 506948616, 659060556, 883997877, 958139571, 1322822218, 1537002063, 1747873779, 1955562222, 2024104815, 2227730452, 2361852424, 2428436474, 2756734187, 3204031479, 3329325298], s) : S.State}

def kr48_correct(q, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, s):
  match q:
    case 0n:
      {==}
    case 1n+z:
      kr49_correct(z, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32), x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14,
        Runtime.step(s, 430227734, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32)))

law kr47_correct:
  for +q: Nat
  for +x0: U32
  for +x1: U32
  for +x2: U32
  for +x3: U32
  for +x4: U32
  for +x5: U32
  for +x6: U32
  for +x7: U32
  for +x8: U32
  for +x9: U32
  for +x10: U32
  for +x11: U32
  for +x12: U32
  for +x13: U32
  for +x14: U32
  for +x15: U32
  for +s: S.State
  {Runtime.kr47(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, s) ==
    C.window_rounds(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, [275423344, 430227734, 506948616, 659060556, 883997877, 958139571, 1322822218, 1537002063, 1747873779, 1955562222, 2024104815, 2227730452, 2361852424, 2428436474, 2756734187, 3204031479, 3329325298], s) : S.State}

def kr47_correct(q, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, s):
  match q:
    case 0n:
      {==}
    case 1n+z:
      kr48_correct(z, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32), x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14,
        Runtime.step(s, 275423344, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32)))

law kr46_correct:
  for +q: Nat
  for +x0: U32
  for +x1: U32
  for +x2: U32
  for +x3: U32
  for +x4: U32
  for +x5: U32
  for +x6: U32
  for +x7: U32
  for +x8: U32
  for +x9: U32
  for +x10: U32
  for +x11: U32
  for +x12: U32
  for +x13: U32
  for +x14: U32
  for +x15: U32
  for +s: S.State
  {Runtime.kr46(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, s) ==
    C.window_rounds(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, [4094571909, 275423344, 430227734, 506948616, 659060556, 883997877, 958139571, 1322822218, 1537002063, 1747873779, 1955562222, 2024104815, 2227730452, 2361852424, 2428436474, 2756734187, 3204031479, 3329325298], s) : S.State}

def kr46_correct(q, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, s):
  match q:
    case 0n:
      {==}
    case 1n+z:
      kr47_correct(z, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32), x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14,
        Runtime.step(s, 4094571909, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32)))

law kr45_correct:
  for +q: Nat
  for +x0: U32
  for +x1: U32
  for +x2: U32
  for +x3: U32
  for +x4: U32
  for +x5: U32
  for +x6: U32
  for +x7: U32
  for +x8: U32
  for +x9: U32
  for +x10: U32
  for +x11: U32
  for +x12: U32
  for +x13: U32
  for +x14: U32
  for +x15: U32
  for +s: S.State
  {Runtime.kr45(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, s) ==
    C.window_rounds(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, [3600352804, 4094571909, 275423344, 430227734, 506948616, 659060556, 883997877, 958139571, 1322822218, 1537002063, 1747873779, 1955562222, 2024104815, 2227730452, 2361852424, 2428436474, 2756734187, 3204031479, 3329325298], s) : S.State}

def kr45_correct(q, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, s):
  match q:
    case 0n:
      {==}
    case 1n+z:
      kr46_correct(z, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32), x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14,
        Runtime.step(s, 3600352804, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32)))

law kr44_correct:
  for +q: Nat
  for +x0: U32
  for +x1: U32
  for +x2: U32
  for +x3: U32
  for +x4: U32
  for +x5: U32
  for +x6: U32
  for +x7: U32
  for +x8: U32
  for +x9: U32
  for +x10: U32
  for +x11: U32
  for +x12: U32
  for +x13: U32
  for +x14: U32
  for +x15: U32
  for +s: S.State
  {Runtime.kr44(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, s) ==
    C.window_rounds(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, [3516065817, 3600352804, 4094571909, 275423344, 430227734, 506948616, 659060556, 883997877, 958139571, 1322822218, 1537002063, 1747873779, 1955562222, 2024104815, 2227730452, 2361852424, 2428436474, 2756734187, 3204031479, 3329325298], s) : S.State}

def kr44_correct(q, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, s):
  match q:
    case 0n:
      {==}
    case 1n+z:
      kr45_correct(z, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32), x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14,
        Runtime.step(s, 3516065817, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32)))

law kr43_correct:
  for +q: Nat
  for +x0: U32
  for +x1: U32
  for +x2: U32
  for +x3: U32
  for +x4: U32
  for +x5: U32
  for +x6: U32
  for +x7: U32
  for +x8: U32
  for +x9: U32
  for +x10: U32
  for +x11: U32
  for +x12: U32
  for +x13: U32
  for +x14: U32
  for +x15: U32
  for +s: S.State
  {Runtime.kr43(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, s) ==
    C.window_rounds(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, [3345764771, 3516065817, 3600352804, 4094571909, 275423344, 430227734, 506948616, 659060556, 883997877, 958139571, 1322822218, 1537002063, 1747873779, 1955562222, 2024104815, 2227730452, 2361852424, 2428436474, 2756734187, 3204031479, 3329325298], s) : S.State}

def kr43_correct(q, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, s):
  match q:
    case 0n:
      {==}
    case 1n+z:
      kr44_correct(z, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32), x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14,
        Runtime.step(s, 3345764771, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32)))

law kr42_correct:
  for +q: Nat
  for +x0: U32
  for +x1: U32
  for +x2: U32
  for +x3: U32
  for +x4: U32
  for +x5: U32
  for +x6: U32
  for +x7: U32
  for +x8: U32
  for +x9: U32
  for +x10: U32
  for +x11: U32
  for +x12: U32
  for +x13: U32
  for +x14: U32
  for +x15: U32
  for +s: S.State
  {Runtime.kr42(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, s) ==
    C.window_rounds(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, [3259730800, 3345764771, 3516065817, 3600352804, 4094571909, 275423344, 430227734, 506948616, 659060556, 883997877, 958139571, 1322822218, 1537002063, 1747873779, 1955562222, 2024104815, 2227730452, 2361852424, 2428436474, 2756734187, 3204031479, 3329325298], s) : S.State}

def kr42_correct(q, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, s):
  match q:
    case 0n:
      {==}
    case 1n+z:
      kr43_correct(z, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32), x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14,
        Runtime.step(s, 3259730800, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32)))

law kr41_correct:
  for +q: Nat
  for +x0: U32
  for +x1: U32
  for +x2: U32
  for +x3: U32
  for +x4: U32
  for +x5: U32
  for +x6: U32
  for +x7: U32
  for +x8: U32
  for +x9: U32
  for +x10: U32
  for +x11: U32
  for +x12: U32
  for +x13: U32
  for +x14: U32
  for +x15: U32
  for +s: S.State
  {Runtime.kr41(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, s) ==
    C.window_rounds(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, [2820302411, 3259730800, 3345764771, 3516065817, 3600352804, 4094571909, 275423344, 430227734, 506948616, 659060556, 883997877, 958139571, 1322822218, 1537002063, 1747873779, 1955562222, 2024104815, 2227730452, 2361852424, 2428436474, 2756734187, 3204031479, 3329325298], s) : S.State}

def kr41_correct(q, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, s):
  match q:
    case 0n:
      {==}
    case 1n+z:
      kr42_correct(z, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32), x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14,
        Runtime.step(s, 2820302411, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32)))

law kr40_correct:
  for +q: Nat
  for +x0: U32
  for +x1: U32
  for +x2: U32
  for +x3: U32
  for +x4: U32
  for +x5: U32
  for +x6: U32
  for +x7: U32
  for +x8: U32
  for +x9: U32
  for +x10: U32
  for +x11: U32
  for +x12: U32
  for +x13: U32
  for +x14: U32
  for +x15: U32
  for +s: S.State
  {Runtime.kr40(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, s) ==
    C.window_rounds(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, [2730485921, 2820302411, 3259730800, 3345764771, 3516065817, 3600352804, 4094571909, 275423344, 430227734, 506948616, 659060556, 883997877, 958139571, 1322822218, 1537002063, 1747873779, 1955562222, 2024104815, 2227730452, 2361852424, 2428436474, 2756734187, 3204031479, 3329325298], s) : S.State}

def kr40_correct(q, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, s):
  match q:
    case 0n:
      {==}
    case 1n+z:
      kr41_correct(z, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32), x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14,
        Runtime.step(s, 2730485921, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32)))

law kr39_correct:
  for +q: Nat
  for +x0: U32
  for +x1: U32
  for +x2: U32
  for +x3: U32
  for +x4: U32
  for +x5: U32
  for +x6: U32
  for +x7: U32
  for +x8: U32
  for +x9: U32
  for +x10: U32
  for +x11: U32
  for +x12: U32
  for +x13: U32
  for +x14: U32
  for +x15: U32
  for +s: S.State
  {Runtime.kr39(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, s) ==
    C.window_rounds(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, [2456956037, 2730485921, 2820302411, 3259730800, 3345764771, 3516065817, 3600352804, 4094571909, 275423344, 430227734, 506948616, 659060556, 883997877, 958139571, 1322822218, 1537002063, 1747873779, 1955562222, 2024104815, 2227730452, 2361852424, 2428436474, 2756734187, 3204031479, 3329325298], s) : S.State}

def kr39_correct(q, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, s):
  match q:
    case 0n:
      {==}
    case 1n+z:
      kr40_correct(z, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32), x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14,
        Runtime.step(s, 2456956037, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32)))

law kr38_correct:
  for +q: Nat
  for +x0: U32
  for +x1: U32
  for +x2: U32
  for +x3: U32
  for +x4: U32
  for +x5: U32
  for +x6: U32
  for +x7: U32
  for +x8: U32
  for +x9: U32
  for +x10: U32
  for +x11: U32
  for +x12: U32
  for +x13: U32
  for +x14: U32
  for +x15: U32
  for +s: S.State
  {Runtime.kr38(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, s) ==
    C.window_rounds(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, [2177026350, 2456956037, 2730485921, 2820302411, 3259730800, 3345764771, 3516065817, 3600352804, 4094571909, 275423344, 430227734, 506948616, 659060556, 883997877, 958139571, 1322822218, 1537002063, 1747873779, 1955562222, 2024104815, 2227730452, 2361852424, 2428436474, 2756734187, 3204031479, 3329325298], s) : S.State}

def kr38_correct(q, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, s):
  match q:
    case 0n:
      {==}
    case 1n+z:
      kr39_correct(z, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32), x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14,
        Runtime.step(s, 2177026350, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32)))

law kr37_correct:
  for +q: Nat
  for +x0: U32
  for +x1: U32
  for +x2: U32
  for +x3: U32
  for +x4: U32
  for +x5: U32
  for +x6: U32
  for +x7: U32
  for +x8: U32
  for +x9: U32
  for +x10: U32
  for +x11: U32
  for +x12: U32
  for +x13: U32
  for +x14: U32
  for +x15: U32
  for +s: S.State
  {Runtime.kr37(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, s) ==
    C.window_rounds(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, [1986661051, 2177026350, 2456956037, 2730485921, 2820302411, 3259730800, 3345764771, 3516065817, 3600352804, 4094571909, 275423344, 430227734, 506948616, 659060556, 883997877, 958139571, 1322822218, 1537002063, 1747873779, 1955562222, 2024104815, 2227730452, 2361852424, 2428436474, 2756734187, 3204031479, 3329325298], s) : S.State}

def kr37_correct(q, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, s):
  match q:
    case 0n:
      {==}
    case 1n+z:
      kr38_correct(z, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32), x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14,
        Runtime.step(s, 1986661051, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32)))

law kr36_correct:
  for +q: Nat
  for +x0: U32
  for +x1: U32
  for +x2: U32
  for +x3: U32
  for +x4: U32
  for +x5: U32
  for +x6: U32
  for +x7: U32
  for +x8: U32
  for +x9: U32
  for +x10: U32
  for +x11: U32
  for +x12: U32
  for +x13: U32
  for +x14: U32
  for +x15: U32
  for +s: S.State
  {Runtime.kr36(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, s) ==
    C.window_rounds(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, [1695183700, 1986661051, 2177026350, 2456956037, 2730485921, 2820302411, 3259730800, 3345764771, 3516065817, 3600352804, 4094571909, 275423344, 430227734, 506948616, 659060556, 883997877, 958139571, 1322822218, 1537002063, 1747873779, 1955562222, 2024104815, 2227730452, 2361852424, 2428436474, 2756734187, 3204031479, 3329325298], s) : S.State}

def kr36_correct(q, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, s):
  match q:
    case 0n:
      {==}
    case 1n+z:
      kr37_correct(z, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32), x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14,
        Runtime.step(s, 1695183700, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32)))

law kr35_correct:
  for +q: Nat
  for +x0: U32
  for +x1: U32
  for +x2: U32
  for +x3: U32
  for +x4: U32
  for +x5: U32
  for +x6: U32
  for +x7: U32
  for +x8: U32
  for +x9: U32
  for +x10: U32
  for +x11: U32
  for +x12: U32
  for +x13: U32
  for +x14: U32
  for +x15: U32
  for +s: S.State
  {Runtime.kr35(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, s) ==
    C.window_rounds(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, [1396182291, 1695183700, 1986661051, 2177026350, 2456956037, 2730485921, 2820302411, 3259730800, 3345764771, 3516065817, 3600352804, 4094571909, 275423344, 430227734, 506948616, 659060556, 883997877, 958139571, 1322822218, 1537002063, 1747873779, 1955562222, 2024104815, 2227730452, 2361852424, 2428436474, 2756734187, 3204031479, 3329325298], s) : S.State}

def kr35_correct(q, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, s):
  match q:
    case 0n:
      {==}
    case 1n+z:
      kr36_correct(z, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32), x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14,
        Runtime.step(s, 1396182291, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32)))

law kr34_correct:
  for +q: Nat
  for +x0: U32
  for +x1: U32
  for +x2: U32
  for +x3: U32
  for +x4: U32
  for +x5: U32
  for +x6: U32
  for +x7: U32
  for +x8: U32
  for +x9: U32
  for +x10: U32
  for +x11: U32
  for +x12: U32
  for +x13: U32
  for +x14: U32
  for +x15: U32
  for +s: S.State
  {Runtime.kr34(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, s) ==
    C.window_rounds(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, [1294757372, 1396182291, 1695183700, 1986661051, 2177026350, 2456956037, 2730485921, 2820302411, 3259730800, 3345764771, 3516065817, 3600352804, 4094571909, 275423344, 430227734, 506948616, 659060556, 883997877, 958139571, 1322822218, 1537002063, 1747873779, 1955562222, 2024104815, 2227730452, 2361852424, 2428436474, 2756734187, 3204031479, 3329325298], s) : S.State}

def kr34_correct(q, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, s):
  match q:
    case 0n:
      {==}
    case 1n+z:
      kr35_correct(z, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32), x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14,
        Runtime.step(s, 1294757372, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32)))

law kr33_correct:
  for +q: Nat
  for +x0: U32
  for +x1: U32
  for +x2: U32
  for +x3: U32
  for +x4: U32
  for +x5: U32
  for +x6: U32
  for +x7: U32
  for +x8: U32
  for +x9: U32
  for +x10: U32
  for +x11: U32
  for +x12: U32
  for +x13: U32
  for +x14: U32
  for +x15: U32
  for +s: S.State
  {Runtime.kr33(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, s) ==
    C.window_rounds(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, [773529912, 1294757372, 1396182291, 1695183700, 1986661051, 2177026350, 2456956037, 2730485921, 2820302411, 3259730800, 3345764771, 3516065817, 3600352804, 4094571909, 275423344, 430227734, 506948616, 659060556, 883997877, 958139571, 1322822218, 1537002063, 1747873779, 1955562222, 2024104815, 2227730452, 2361852424, 2428436474, 2756734187, 3204031479, 3329325298], s) : S.State}

def kr33_correct(q, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, s):
  match q:
    case 0n:
      {==}
    case 1n+z:
      kr34_correct(z, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32), x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14,
        Runtime.step(s, 773529912, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32)))

law kr32_correct:
  for +q: Nat
  for +x0: U32
  for +x1: U32
  for +x2: U32
  for +x3: U32
  for +x4: U32
  for +x5: U32
  for +x6: U32
  for +x7: U32
  for +x8: U32
  for +x9: U32
  for +x10: U32
  for +x11: U32
  for +x12: U32
  for +x13: U32
  for +x14: U32
  for +x15: U32
  for +s: S.State
  {Runtime.kr32(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, s) ==
    C.window_rounds(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, [666307205, 773529912, 1294757372, 1396182291, 1695183700, 1986661051, 2177026350, 2456956037, 2730485921, 2820302411, 3259730800, 3345764771, 3516065817, 3600352804, 4094571909, 275423344, 430227734, 506948616, 659060556, 883997877, 958139571, 1322822218, 1537002063, 1747873779, 1955562222, 2024104815, 2227730452, 2361852424, 2428436474, 2756734187, 3204031479, 3329325298], s) : S.State}

def kr32_correct(q, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, s):
  match q:
    case 0n:
      {==}
    case 1n+z:
      kr33_correct(z, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32), x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14,
        Runtime.step(s, 666307205, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32)))

law kr31_correct:
  for +q: Nat
  for +x0: U32
  for +x1: U32
  for +x2: U32
  for +x3: U32
  for +x4: U32
  for +x5: U32
  for +x6: U32
  for +x7: U32
  for +x8: U32
  for +x9: U32
  for +x10: U32
  for +x11: U32
  for +x12: U32
  for +x13: U32
  for +x14: U32
  for +x15: U32
  for +s: S.State
  {Runtime.kr31(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, s) ==
    C.window_rounds(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, [338241895, 666307205, 773529912, 1294757372, 1396182291, 1695183700, 1986661051, 2177026350, 2456956037, 2730485921, 2820302411, 3259730800, 3345764771, 3516065817, 3600352804, 4094571909, 275423344, 430227734, 506948616, 659060556, 883997877, 958139571, 1322822218, 1537002063, 1747873779, 1955562222, 2024104815, 2227730452, 2361852424, 2428436474, 2756734187, 3204031479, 3329325298], s) : S.State}

def kr31_correct(q, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, s):
  match q:
    case 0n:
      {==}
    case 1n+z:
      kr32_correct(z, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32), x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14,
        Runtime.step(s, 338241895, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32)))

law kr30_correct:
  for +q: Nat
  for +x0: U32
  for +x1: U32
  for +x2: U32
  for +x3: U32
  for +x4: U32
  for +x5: U32
  for +x6: U32
  for +x7: U32
  for +x8: U32
  for +x9: U32
  for +x10: U32
  for +x11: U32
  for +x12: U32
  for +x13: U32
  for +x14: U32
  for +x15: U32
  for +s: S.State
  {Runtime.kr30(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, s) ==
    C.window_rounds(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, [113926993, 338241895, 666307205, 773529912, 1294757372, 1396182291, 1695183700, 1986661051, 2177026350, 2456956037, 2730485921, 2820302411, 3259730800, 3345764771, 3516065817, 3600352804, 4094571909, 275423344, 430227734, 506948616, 659060556, 883997877, 958139571, 1322822218, 1537002063, 1747873779, 1955562222, 2024104815, 2227730452, 2361852424, 2428436474, 2756734187, 3204031479, 3329325298], s) : S.State}

def kr30_correct(q, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, s):
  match q:
    case 0n:
      {==}
    case 1n+z:
      kr31_correct(z, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32), x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14,
        Runtime.step(s, 113926993, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32)))

law kr29_correct:
  for +q: Nat
  for +x0: U32
  for +x1: U32
  for +x2: U32
  for +x3: U32
  for +x4: U32
  for +x5: U32
  for +x6: U32
  for +x7: U32
  for +x8: U32
  for +x9: U32
  for +x10: U32
  for +x11: U32
  for +x12: U32
  for +x13: U32
  for +x14: U32
  for +x15: U32
  for +s: S.State
  {Runtime.kr29(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, s) ==
    C.window_rounds(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, [3584528711, 113926993, 338241895, 666307205, 773529912, 1294757372, 1396182291, 1695183700, 1986661051, 2177026350, 2456956037, 2730485921, 2820302411, 3259730800, 3345764771, 3516065817, 3600352804, 4094571909, 275423344, 430227734, 506948616, 659060556, 883997877, 958139571, 1322822218, 1537002063, 1747873779, 1955562222, 2024104815, 2227730452, 2361852424, 2428436474, 2756734187, 3204031479, 3329325298], s) : S.State}

def kr29_correct(q, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, s):
  match q:
    case 0n:
      {==}
    case 1n+z:
      kr30_correct(z, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32), x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14,
        Runtime.step(s, 3584528711, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32)))

law kr28_correct:
  for +q: Nat
  for +x0: U32
  for +x1: U32
  for +x2: U32
  for +x3: U32
  for +x4: U32
  for +x5: U32
  for +x6: U32
  for +x7: U32
  for +x8: U32
  for +x9: U32
  for +x10: U32
  for +x11: U32
  for +x12: U32
  for +x13: U32
  for +x14: U32
  for +x15: U32
  for +s: S.State
  {Runtime.kr28(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, s) ==
    C.window_rounds(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, [3336571891, 3584528711, 113926993, 338241895, 666307205, 773529912, 1294757372, 1396182291, 1695183700, 1986661051, 2177026350, 2456956037, 2730485921, 2820302411, 3259730800, 3345764771, 3516065817, 3600352804, 4094571909, 275423344, 430227734, 506948616, 659060556, 883997877, 958139571, 1322822218, 1537002063, 1747873779, 1955562222, 2024104815, 2227730452, 2361852424, 2428436474, 2756734187, 3204031479, 3329325298], s) : S.State}

def kr28_correct(q, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, s):
  match q:
    case 0n:
      {==}
    case 1n+z:
      kr29_correct(z, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32), x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14,
        Runtime.step(s, 3336571891, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32)))

law kr27_correct:
  for +q: Nat
  for +x0: U32
  for +x1: U32
  for +x2: U32
  for +x3: U32
  for +x4: U32
  for +x5: U32
  for +x6: U32
  for +x7: U32
  for +x8: U32
  for +x9: U32
  for +x10: U32
  for +x11: U32
  for +x12: U32
  for +x13: U32
  for +x14: U32
  for +x15: U32
  for +s: S.State
  {Runtime.kr27(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, s) ==
    C.window_rounds(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, [3210313671, 3336571891, 3584528711, 113926993, 338241895, 666307205, 773529912, 1294757372, 1396182291, 1695183700, 1986661051, 2177026350, 2456956037, 2730485921, 2820302411, 3259730800, 3345764771, 3516065817, 3600352804, 4094571909, 275423344, 430227734, 506948616, 659060556, 883997877, 958139571, 1322822218, 1537002063, 1747873779, 1955562222, 2024104815, 2227730452, 2361852424, 2428436474, 2756734187, 3204031479, 3329325298], s) : S.State}

def kr27_correct(q, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, s):
  match q:
    case 0n:
      {==}
    case 1n+z:
      kr28_correct(z, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32), x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14,
        Runtime.step(s, 3210313671, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32)))

law kr26_correct:
  for +q: Nat
  for +x0: U32
  for +x1: U32
  for +x2: U32
  for +x3: U32
  for +x4: U32
  for +x5: U32
  for +x6: U32
  for +x7: U32
  for +x8: U32
  for +x9: U32
  for +x10: U32
  for +x11: U32
  for +x12: U32
  for +x13: U32
  for +x14: U32
  for +x15: U32
  for +s: S.State
  {Runtime.kr26(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, s) ==
    C.window_rounds(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, [2952996808, 3210313671, 3336571891, 3584528711, 113926993, 338241895, 666307205, 773529912, 1294757372, 1396182291, 1695183700, 1986661051, 2177026350, 2456956037, 2730485921, 2820302411, 3259730800, 3345764771, 3516065817, 3600352804, 4094571909, 275423344, 430227734, 506948616, 659060556, 883997877, 958139571, 1322822218, 1537002063, 1747873779, 1955562222, 2024104815, 2227730452, 2361852424, 2428436474, 2756734187, 3204031479, 3329325298], s) : S.State}

def kr26_correct(q, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, s):
  match q:
    case 0n:
      {==}
    case 1n+z:
      kr27_correct(z, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32), x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14,
        Runtime.step(s, 2952996808, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32)))

law kr25_correct:
  for +q: Nat
  for +x0: U32
  for +x1: U32
  for +x2: U32
  for +x3: U32
  for +x4: U32
  for +x5: U32
  for +x6: U32
  for +x7: U32
  for +x8: U32
  for +x9: U32
  for +x10: U32
  for +x11: U32
  for +x12: U32
  for +x13: U32
  for +x14: U32
  for +x15: U32
  for +s: S.State
  {Runtime.kr25(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, s) ==
    C.window_rounds(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, [2821834349, 2952996808, 3210313671, 3336571891, 3584528711, 113926993, 338241895, 666307205, 773529912, 1294757372, 1396182291, 1695183700, 1986661051, 2177026350, 2456956037, 2730485921, 2820302411, 3259730800, 3345764771, 3516065817, 3600352804, 4094571909, 275423344, 430227734, 506948616, 659060556, 883997877, 958139571, 1322822218, 1537002063, 1747873779, 1955562222, 2024104815, 2227730452, 2361852424, 2428436474, 2756734187, 3204031479, 3329325298], s) : S.State}

def kr25_correct(q, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, s):
  match q:
    case 0n:
      {==}
    case 1n+z:
      kr26_correct(z, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32), x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14,
        Runtime.step(s, 2821834349, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32)))

law kr24_correct:
  for +q: Nat
  for +x0: U32
  for +x1: U32
  for +x2: U32
  for +x3: U32
  for +x4: U32
  for +x5: U32
  for +x6: U32
  for +x7: U32
  for +x8: U32
  for +x9: U32
  for +x10: U32
  for +x11: U32
  for +x12: U32
  for +x13: U32
  for +x14: U32
  for +x15: U32
  for +s: S.State
  {Runtime.kr24(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, s) ==
    C.window_rounds(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, [2554220882, 2821834349, 2952996808, 3210313671, 3336571891, 3584528711, 113926993, 338241895, 666307205, 773529912, 1294757372, 1396182291, 1695183700, 1986661051, 2177026350, 2456956037, 2730485921, 2820302411, 3259730800, 3345764771, 3516065817, 3600352804, 4094571909, 275423344, 430227734, 506948616, 659060556, 883997877, 958139571, 1322822218, 1537002063, 1747873779, 1955562222, 2024104815, 2227730452, 2361852424, 2428436474, 2756734187, 3204031479, 3329325298], s) : S.State}

def kr24_correct(q, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, s):
  match q:
    case 0n:
      {==}
    case 1n+z:
      kr25_correct(z, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32), x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14,
        Runtime.step(s, 2554220882, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32)))

law kr23_correct:
  for +q: Nat
  for +x0: U32
  for +x1: U32
  for +x2: U32
  for +x3: U32
  for +x4: U32
  for +x5: U32
  for +x6: U32
  for +x7: U32
  for +x8: U32
  for +x9: U32
  for +x10: U32
  for +x11: U32
  for +x12: U32
  for +x13: U32
  for +x14: U32
  for +x15: U32
  for +s: S.State
  {Runtime.kr23(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, s) ==
    C.window_rounds(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, [1996064986, 2554220882, 2821834349, 2952996808, 3210313671, 3336571891, 3584528711, 113926993, 338241895, 666307205, 773529912, 1294757372, 1396182291, 1695183700, 1986661051, 2177026350, 2456956037, 2730485921, 2820302411, 3259730800, 3345764771, 3516065817, 3600352804, 4094571909, 275423344, 430227734, 506948616, 659060556, 883997877, 958139571, 1322822218, 1537002063, 1747873779, 1955562222, 2024104815, 2227730452, 2361852424, 2428436474, 2756734187, 3204031479, 3329325298], s) : S.State}

def kr23_correct(q, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, s):
  match q:
    case 0n:
      {==}
    case 1n+z:
      kr24_correct(z, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32), x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14,
        Runtime.step(s, 1996064986, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32)))

law kr22_correct:
  for +q: Nat
  for +x0: U32
  for +x1: U32
  for +x2: U32
  for +x3: U32
  for +x4: U32
  for +x5: U32
  for +x6: U32
  for +x7: U32
  for +x8: U32
  for +x9: U32
  for +x10: U32
  for +x11: U32
  for +x12: U32
  for +x13: U32
  for +x14: U32
  for +x15: U32
  for +s: S.State
  {Runtime.kr22(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, s) ==
    C.window_rounds(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, [1555081692, 1996064986, 2554220882, 2821834349, 2952996808, 3210313671, 3336571891, 3584528711, 113926993, 338241895, 666307205, 773529912, 1294757372, 1396182291, 1695183700, 1986661051, 2177026350, 2456956037, 2730485921, 2820302411, 3259730800, 3345764771, 3516065817, 3600352804, 4094571909, 275423344, 430227734, 506948616, 659060556, 883997877, 958139571, 1322822218, 1537002063, 1747873779, 1955562222, 2024104815, 2227730452, 2361852424, 2428436474, 2756734187, 3204031479, 3329325298], s) : S.State}

def kr22_correct(q, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, s):
  match q:
    case 0n:
      {==}
    case 1n+z:
      kr23_correct(z, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32), x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14,
        Runtime.step(s, 1555081692, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32)))

law kr21_correct:
  for +q: Nat
  for +x0: U32
  for +x1: U32
  for +x2: U32
  for +x3: U32
  for +x4: U32
  for +x5: U32
  for +x6: U32
  for +x7: U32
  for +x8: U32
  for +x9: U32
  for +x10: U32
  for +x11: U32
  for +x12: U32
  for +x13: U32
  for +x14: U32
  for +x15: U32
  for +s: S.State
  {Runtime.kr21(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, s) ==
    C.window_rounds(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, [1249150122, 1555081692, 1996064986, 2554220882, 2821834349, 2952996808, 3210313671, 3336571891, 3584528711, 113926993, 338241895, 666307205, 773529912, 1294757372, 1396182291, 1695183700, 1986661051, 2177026350, 2456956037, 2730485921, 2820302411, 3259730800, 3345764771, 3516065817, 3600352804, 4094571909, 275423344, 430227734, 506948616, 659060556, 883997877, 958139571, 1322822218, 1537002063, 1747873779, 1955562222, 2024104815, 2227730452, 2361852424, 2428436474, 2756734187, 3204031479, 3329325298], s) : S.State}

def kr21_correct(q, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, s):
  match q:
    case 0n:
      {==}
    case 1n+z:
      kr22_correct(z, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32), x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14,
        Runtime.step(s, 1249150122, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32)))

law kr20_correct:
  for +q: Nat
  for +x0: U32
  for +x1: U32
  for +x2: U32
  for +x3: U32
  for +x4: U32
  for +x5: U32
  for +x6: U32
  for +x7: U32
  for +x8: U32
  for +x9: U32
  for +x10: U32
  for +x11: U32
  for +x12: U32
  for +x13: U32
  for +x14: U32
  for +x15: U32
  for +s: S.State
  {Runtime.kr20(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, s) ==
    C.window_rounds(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, [770255983, 1249150122, 1555081692, 1996064986, 2554220882, 2821834349, 2952996808, 3210313671, 3336571891, 3584528711, 113926993, 338241895, 666307205, 773529912, 1294757372, 1396182291, 1695183700, 1986661051, 2177026350, 2456956037, 2730485921, 2820302411, 3259730800, 3345764771, 3516065817, 3600352804, 4094571909, 275423344, 430227734, 506948616, 659060556, 883997877, 958139571, 1322822218, 1537002063, 1747873779, 1955562222, 2024104815, 2227730452, 2361852424, 2428436474, 2756734187, 3204031479, 3329325298], s) : S.State}

def kr20_correct(q, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, s):
  match q:
    case 0n:
      {==}
    case 1n+z:
      kr21_correct(z, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32), x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14,
        Runtime.step(s, 770255983, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32)))

law kr19_correct:
  for +q: Nat
  for +x0: U32
  for +x1: U32
  for +x2: U32
  for +x3: U32
  for +x4: U32
  for +x5: U32
  for +x6: U32
  for +x7: U32
  for +x8: U32
  for +x9: U32
  for +x10: U32
  for +x11: U32
  for +x12: U32
  for +x13: U32
  for +x14: U32
  for +x15: U32
  for +s: S.State
  {Runtime.kr19(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, s) ==
    C.window_rounds(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, [604807628, 770255983, 1249150122, 1555081692, 1996064986, 2554220882, 2821834349, 2952996808, 3210313671, 3336571891, 3584528711, 113926993, 338241895, 666307205, 773529912, 1294757372, 1396182291, 1695183700, 1986661051, 2177026350, 2456956037, 2730485921, 2820302411, 3259730800, 3345764771, 3516065817, 3600352804, 4094571909, 275423344, 430227734, 506948616, 659060556, 883997877, 958139571, 1322822218, 1537002063, 1747873779, 1955562222, 2024104815, 2227730452, 2361852424, 2428436474, 2756734187, 3204031479, 3329325298], s) : S.State}

def kr19_correct(q, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, s):
  match q:
    case 0n:
      {==}
    case 1n+z:
      kr20_correct(z, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32), x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14,
        Runtime.step(s, 604807628, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32)))

law kr18_correct:
  for +q: Nat
  for +x0: U32
  for +x1: U32
  for +x2: U32
  for +x3: U32
  for +x4: U32
  for +x5: U32
  for +x6: U32
  for +x7: U32
  for +x8: U32
  for +x9: U32
  for +x10: U32
  for +x11: U32
  for +x12: U32
  for +x13: U32
  for +x14: U32
  for +x15: U32
  for +s: S.State
  {Runtime.kr18(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, s) ==
    C.window_rounds(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, [264347078, 604807628, 770255983, 1249150122, 1555081692, 1996064986, 2554220882, 2821834349, 2952996808, 3210313671, 3336571891, 3584528711, 113926993, 338241895, 666307205, 773529912, 1294757372, 1396182291, 1695183700, 1986661051, 2177026350, 2456956037, 2730485921, 2820302411, 3259730800, 3345764771, 3516065817, 3600352804, 4094571909, 275423344, 430227734, 506948616, 659060556, 883997877, 958139571, 1322822218, 1537002063, 1747873779, 1955562222, 2024104815, 2227730452, 2361852424, 2428436474, 2756734187, 3204031479, 3329325298], s) : S.State}

def kr18_correct(q, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, s):
  match q:
    case 0n:
      {==}
    case 1n+z:
      kr19_correct(z, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32), x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14,
        Runtime.step(s, 264347078, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32)))

law kr17_correct:
  for +q: Nat
  for +x0: U32
  for +x1: U32
  for +x2: U32
  for +x3: U32
  for +x4: U32
  for +x5: U32
  for +x6: U32
  for +x7: U32
  for +x8: U32
  for +x9: U32
  for +x10: U32
  for +x11: U32
  for +x12: U32
  for +x13: U32
  for +x14: U32
  for +x15: U32
  for +s: S.State
  {Runtime.kr17(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, s) ==
    C.window_rounds(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, [4022224774, 264347078, 604807628, 770255983, 1249150122, 1555081692, 1996064986, 2554220882, 2821834349, 2952996808, 3210313671, 3336571891, 3584528711, 113926993, 338241895, 666307205, 773529912, 1294757372, 1396182291, 1695183700, 1986661051, 2177026350, 2456956037, 2730485921, 2820302411, 3259730800, 3345764771, 3516065817, 3600352804, 4094571909, 275423344, 430227734, 506948616, 659060556, 883997877, 958139571, 1322822218, 1537002063, 1747873779, 1955562222, 2024104815, 2227730452, 2361852424, 2428436474, 2756734187, 3204031479, 3329325298], s) : S.State}

def kr17_correct(q, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, s):
  match q:
    case 0n:
      {==}
    case 1n+z:
      kr18_correct(z, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32), x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14,
        Runtime.step(s, 4022224774, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32)))

law kr16_correct:
  for +q: Nat
  for +x0: U32
  for +x1: U32
  for +x2: U32
  for +x3: U32
  for +x4: U32
  for +x5: U32
  for +x6: U32
  for +x7: U32
  for +x8: U32
  for +x9: U32
  for +x10: U32
  for +x11: U32
  for +x12: U32
  for +x13: U32
  for +x14: U32
  for +x15: U32
  for +s: S.State
  {Runtime.kr16(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, s) ==
    C.window_rounds(q, Runtime.W{x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, [3835390401, 4022224774, 264347078, 604807628, 770255983, 1249150122, 1555081692, 1996064986, 2554220882, 2821834349, 2952996808, 3210313671, 3336571891, 3584528711, 113926993, 338241895, 666307205, 773529912, 1294757372, 1396182291, 1695183700, 1986661051, 2177026350, 2456956037, 2730485921, 2820302411, 3259730800, 3345764771, 3516065817, 3600352804, 4094571909, 275423344, 430227734, 506948616, 659060556, 883997877, 958139571, 1322822218, 1537002063, 1747873779, 1955562222, 2024104815, 2227730452, 2361852424, 2428436474, 2756734187, 3204031479, 3329325298], s) : S.State}

def kr16_correct(q, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, s):
  match q:
    case 0n:
      {==}
    case 1n+z:
      kr17_correct(z, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32), x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14,
        Runtime.step(s, 3835390401, (Runtime.small1(x1) + x6 + Runtime.small0(x14) + x15 : U32)))

law fips16_correct:
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
  for +q: Nat
  for +s: S.State
  {Runtime.fips_compress16(a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, s) ==
    C.window_compress16(a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, C.round_constants(), s) : S.State}

def fips16_correct(a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, s):
  +s16 = Runtime.step(Runtime.step(Runtime.step(Runtime.step(Runtime.step(Runtime.step(Runtime.step(Runtime.step(Runtime.step(Runtime.step(Runtime.step(Runtime.step(Runtime.step(Runtime.step(Runtime.step(Runtime.step(s, 1116352408, a), 1899447441, b), 3049323471, c), 3921009573, d), 961987163, e), 1508970993, f), 2453635748, g), 2870763221, h), 3624381080, i), 310598401, j), 607225278, k), 1426881987, l), 1925078388, m), 2162078206, n), 2614888103, o), 3248222580, p)
  Equal.cong(S.State, S.State, y => Runtime.feedforward(s, y),
    Runtime.kr16(q, Runtime.W{p, o, n, m, l, k, j, i, h, g, f, e, d, c, b, a}, s16),
    C.window_rounds(q, Runtime.W{p, o, n, m, l, k, j, i, h, g, f, e, d, c, b, a}, [3835390401, 4022224774, 264347078, 604807628, 770255983, 1249150122, 1555081692, 1996064986, 2554220882, 2821834349, 2952996808, 3210313671, 3336571891, 3584528711, 113926993, 338241895, 666307205, 773529912, 1294757372, 1396182291, 1695183700, 1986661051, 2177026350, 2456956037, 2730485921, 2820302411, 3259730800, 3345764771, 3516065817, 3600352804, 4094571909, 275423344, 430227734, 506948616, 659060556, 883997877, 958139571, 1322822218, 1537002063, 1747873779, 1955562222, 2024104815, 2227730452, 2361852424, 2428436474, 2756734187, 3204031479, 3329325298], s16),
    kr16_correct(q, p, o, n, m, l, k, j, i, h, g, f, e, d, c, b, a, s16))

# Streaming refines the generic block decoder, instantiated with the FIPS
# table, applied to the padded message. After a complete block the count grows
# by 64 exactly as the remaining length shrinks. For a short tail, count = 64k
# fixes n mod 64 to the tail length, so the modular zero count is concrete and
# finish_go packs the same 64 or 128 bytes that block_bytes decodes.
law stream_correct:
  for +bytes: List<&2, U32>
  for +k: Nat
  for +extra: Nat
  for +s: S.State
  {C.stream(bytes, mul64(k), extra, s) == C.block_bytes(List.append(&2, U32, bytes,
    C.suffix(Nat.add(List.length(&2, U32, bytes), mul64(k)))), extra, C.round_constants(), s) : S.State}

def stream_correct(bytes, k, extra, s):
  match bytes:
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> b59 <> b60 <> b61 <> b62 <> b63 <> rest:
      +fast = Runtime.fips_compress16(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, b38, b39), Runtime.pack(b40, b41, b42, b43), Runtime.pack(b44, b45, b46, b47), Runtime.pack(b48, b49, b50, b51), Runtime.pack(b52, b53, b54, b55), Runtime.pack(b56, b57, b58, b59), Runtime.pack(b60, b61, b62, b63), extra, s)
      %fips16_correct(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, b38, b39), Runtime.pack(b40, b41, b42, b43), Runtime.pack(b44, b45, b46, b47), Runtime.pack(b48, b49, b50, b51), Runtime.pack(b52, b53, b54, b55), Runtime.pack(b56, b57, b58, b59), Runtime.pack(b60, b61, b62, b63), extra, s) :
        {C.stream(rest, mul64(1n+k), extra, fast) == C.block_bytes(List.append(&2, U32, rest,
          C.suffix(Nat.add(64n, Nat.add(List.length(&2, U32, rest), mul64(k))))), extra, C.round_constants(), _) : S.State}
      %L.add_swap(List.length(&2, U32, rest), 64n, mul64(k)) :
        {C.stream(rest, mul64(1n+k), extra, fast) == C.block_bytes(List.append(&2, U32, rest,
          C.suffix(_)), extra, C.round_constants(), fast) : S.State}
      stream_correct(rest, 1n+k, extra, fast)
    case Nil{}:
      %Equal.sym(Nat, Nat.mod(Nat.add(List.length(&2, U32, Nil{}), mul64(k)), 64n),
        Nat.mod(List.length(&2, U32, Nil{}), 64n),
        mod_tail(List.length(&2, U32, Nil{}), k)) :
        {C.stream(Nil{}, mul64(k), extra, s) == C.block_bytes(List.append(&2, U32, Nil{},
          128 <> List.append(&2, U32, List.replicate(U32, Nat.mod(Nat.sub(119n, _), 64n), 0),
            C.bit_length(Nat.add(List.length(&2, U32, Nil{}), mul64(k))))), extra, C.round_constants(), s) : S.State}
      fips16_correct(Runtime.pack(128, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, Nil{}), mul64(k))), extra, s)
    case b0 <> Nil{}:
      %Equal.sym(Nat, Nat.mod(Nat.add(List.length(&2, U32, b0 <> Nil{}), mul64(k)), 64n),
        Nat.mod(List.length(&2, U32, b0 <> Nil{}), 64n),
        mod_tail(List.length(&2, U32, b0 <> Nil{}), k)) :
        {C.stream(b0 <> Nil{}, mul64(k), extra, s) == C.block_bytes(List.append(&2, U32, b0 <> Nil{},
          128 <> List.append(&2, U32, List.replicate(U32, Nat.mod(Nat.sub(119n, _), 64n), 0),
            C.bit_length(Nat.add(List.length(&2, U32, b0 <> Nil{}), mul64(k))))), extra, C.round_constants(), s) : S.State}
      fips16_correct(Runtime.pack(b0, 128, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> Nil{}), mul64(k))), extra, s)
    case b0 <> b1 <> Nil{}:
      %Equal.sym(Nat, Nat.mod(Nat.add(List.length(&2, U32, b0 <> b1 <> Nil{}), mul64(k)), 64n),
        Nat.mod(List.length(&2, U32, b0 <> b1 <> Nil{}), 64n),
        mod_tail(List.length(&2, U32, b0 <> b1 <> Nil{}), k)) :
        {C.stream(b0 <> b1 <> Nil{}, mul64(k), extra, s) == C.block_bytes(List.append(&2, U32, b0 <> b1 <> Nil{},
          128 <> List.append(&2, U32, List.replicate(U32, Nat.mod(Nat.sub(119n, _), 64n), 0),
            C.bit_length(Nat.add(List.length(&2, U32, b0 <> b1 <> Nil{}), mul64(k))))), extra, C.round_constants(), s) : S.State}
      fips16_correct(Runtime.pack(b0, b1, 128, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> Nil{}), mul64(k))), extra, s)
    case b0 <> b1 <> b2 <> Nil{}:
      %Equal.sym(Nat, Nat.mod(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> Nil{}), mul64(k)), 64n),
        Nat.mod(List.length(&2, U32, b0 <> b1 <> b2 <> Nil{}), 64n),
        mod_tail(List.length(&2, U32, b0 <> b1 <> b2 <> Nil{}), k)) :
        {C.stream(b0 <> b1 <> b2 <> Nil{}, mul64(k), extra, s) == C.block_bytes(List.append(&2, U32, b0 <> b1 <> b2 <> Nil{},
          128 <> List.append(&2, U32, List.replicate(U32, Nat.mod(Nat.sub(119n, _), 64n), 0),
            C.bit_length(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> Nil{}), mul64(k))))), extra, C.round_constants(), s) : S.State}
      fips16_correct(Runtime.pack(b0, b1, b2, 128), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> Nil{}), mul64(k))), extra, s)
    case b0 <> b1 <> b2 <> b3 <> Nil{}:
      %Equal.sym(Nat, Nat.mod(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> Nil{}), mul64(k)), 64n),
        Nat.mod(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> Nil{}), 64n),
        mod_tail(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> Nil{}), k)) :
        {C.stream(b0 <> b1 <> b2 <> b3 <> Nil{}, mul64(k), extra, s) == C.block_bytes(List.append(&2, U32, b0 <> b1 <> b2 <> b3 <> Nil{},
          128 <> List.append(&2, U32, List.replicate(U32, Nat.mod(Nat.sub(119n, _), 64n), 0),
            C.bit_length(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> Nil{}), mul64(k))))), extra, C.round_constants(), s) : S.State}
      fips16_correct(Runtime.pack(b0, b1, b2, b3), Runtime.pack(128, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> Nil{}), mul64(k))), extra, s)
    case b0 <> b1 <> b2 <> b3 <> b4 <> Nil{}:
      %Equal.sym(Nat, Nat.mod(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> Nil{}), mul64(k)), 64n),
        Nat.mod(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> Nil{}), 64n),
        mod_tail(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> Nil{}), k)) :
        {C.stream(b0 <> b1 <> b2 <> b3 <> b4 <> Nil{}, mul64(k), extra, s) == C.block_bytes(List.append(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> Nil{},
          128 <> List.append(&2, U32, List.replicate(U32, Nat.mod(Nat.sub(119n, _), 64n), 0),
            C.bit_length(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> Nil{}), mul64(k))))), extra, C.round_constants(), s) : S.State}
      fips16_correct(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, 128, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> Nil{}), mul64(k))), extra, s)
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> Nil{}:
      %Equal.sym(Nat, Nat.mod(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> Nil{}), mul64(k)), 64n),
        Nat.mod(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> Nil{}), 64n),
        mod_tail(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> Nil{}), k)) :
        {C.stream(b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> Nil{}, mul64(k), extra, s) == C.block_bytes(List.append(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> Nil{},
          128 <> List.append(&2, U32, List.replicate(U32, Nat.mod(Nat.sub(119n, _), 64n), 0),
            C.bit_length(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> Nil{}), mul64(k))))), extra, C.round_constants(), s) : S.State}
      fips16_correct(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, 128, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> Nil{}), mul64(k))), extra, s)
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> Nil{}:
      %Equal.sym(Nat, Nat.mod(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> Nil{}), mul64(k)), 64n),
        Nat.mod(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> Nil{}), 64n),
        mod_tail(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> Nil{}), k)) :
        {C.stream(b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> Nil{}, mul64(k), extra, s) == C.block_bytes(List.append(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> Nil{},
          128 <> List.append(&2, U32, List.replicate(U32, Nat.mod(Nat.sub(119n, _), 64n), 0),
            C.bit_length(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> Nil{}), mul64(k))))), extra, C.round_constants(), s) : S.State}
      fips16_correct(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, 128), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> Nil{}), mul64(k))), extra, s)
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> Nil{}:
      %Equal.sym(Nat, Nat.mod(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> Nil{}), mul64(k)), 64n),
        Nat.mod(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> Nil{}), 64n),
        mod_tail(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> Nil{}), k)) :
        {C.stream(b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> Nil{}, mul64(k), extra, s) == C.block_bytes(List.append(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> Nil{},
          128 <> List.append(&2, U32, List.replicate(U32, Nat.mod(Nat.sub(119n, _), 64n), 0),
            C.bit_length(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> Nil{}), mul64(k))))), extra, C.round_constants(), s) : S.State}
      fips16_correct(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(128, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> Nil{}), mul64(k))), extra, s)
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> Nil{}:
      %Equal.sym(Nat, Nat.mod(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> Nil{}), mul64(k)), 64n),
        Nat.mod(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> Nil{}), 64n),
        mod_tail(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> Nil{}), k)) :
        {C.stream(b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> Nil{}, mul64(k), extra, s) == C.block_bytes(List.append(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> Nil{},
          128 <> List.append(&2, U32, List.replicate(U32, Nat.mod(Nat.sub(119n, _), 64n), 0),
            C.bit_length(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> Nil{}), mul64(k))))), extra, C.round_constants(), s) : S.State}
      fips16_correct(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, 128, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> Nil{}), mul64(k))), extra, s)
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> Nil{}:
      %Equal.sym(Nat, Nat.mod(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> Nil{}), mul64(k)), 64n),
        Nat.mod(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> Nil{}), 64n),
        mod_tail(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> Nil{}), k)) :
        {C.stream(b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> Nil{}, mul64(k), extra, s) == C.block_bytes(List.append(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> Nil{},
          128 <> List.append(&2, U32, List.replicate(U32, Nat.mod(Nat.sub(119n, _), 64n), 0),
            C.bit_length(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> Nil{}), mul64(k))))), extra, C.round_constants(), s) : S.State}
      fips16_correct(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, 128, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> Nil{}), mul64(k))), extra, s)
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> Nil{}:
      %Equal.sym(Nat, Nat.mod(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> Nil{}), mul64(k)), 64n),
        Nat.mod(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> Nil{}), 64n),
        mod_tail(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> Nil{}), k)) :
        {C.stream(b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> Nil{}, mul64(k), extra, s) == C.block_bytes(List.append(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> Nil{},
          128 <> List.append(&2, U32, List.replicate(U32, Nat.mod(Nat.sub(119n, _), 64n), 0),
            C.bit_length(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> Nil{}), mul64(k))))), extra, C.round_constants(), s) : S.State}
      fips16_correct(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, 128), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> Nil{}), mul64(k))), extra, s)
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> Nil{}:
      %Equal.sym(Nat, Nat.mod(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> Nil{}), mul64(k)), 64n),
        Nat.mod(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> Nil{}), 64n),
        mod_tail(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> Nil{}), k)) :
        {C.stream(b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> Nil{}, mul64(k), extra, s) == C.block_bytes(List.append(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> Nil{},
          128 <> List.append(&2, U32, List.replicate(U32, Nat.mod(Nat.sub(119n, _), 64n), 0),
            C.bit_length(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> Nil{}), mul64(k))))), extra, C.round_constants(), s) : S.State}
      fips16_correct(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(128, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> Nil{}), mul64(k))), extra, s)
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> Nil{}:
      %Equal.sym(Nat, Nat.mod(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> Nil{}), mul64(k)), 64n),
        Nat.mod(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> Nil{}), 64n),
        mod_tail(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> Nil{}), k)) :
        {C.stream(b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> Nil{}, mul64(k), extra, s) == C.block_bytes(List.append(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> Nil{},
          128 <> List.append(&2, U32, List.replicate(U32, Nat.mod(Nat.sub(119n, _), 64n), 0),
            C.bit_length(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> Nil{}), mul64(k))))), extra, C.round_constants(), s) : S.State}
      fips16_correct(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, 128, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> Nil{}), mul64(k))), extra, s)
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> Nil{}:
      %Equal.sym(Nat, Nat.mod(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> Nil{}), mul64(k)), 64n),
        Nat.mod(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> Nil{}), 64n),
        mod_tail(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> Nil{}), k)) :
        {C.stream(b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> Nil{}, mul64(k), extra, s) == C.block_bytes(List.append(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> Nil{},
          128 <> List.append(&2, U32, List.replicate(U32, Nat.mod(Nat.sub(119n, _), 64n), 0),
            C.bit_length(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> Nil{}), mul64(k))))), extra, C.round_constants(), s) : S.State}
      fips16_correct(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, 128, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> Nil{}), mul64(k))), extra, s)
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> Nil{}:
      %Equal.sym(Nat, Nat.mod(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> Nil{}), mul64(k)), 64n),
        Nat.mod(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> Nil{}), 64n),
        mod_tail(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> Nil{}), k)) :
        {C.stream(b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> Nil{}, mul64(k), extra, s) == C.block_bytes(List.append(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> Nil{},
          128 <> List.append(&2, U32, List.replicate(U32, Nat.mod(Nat.sub(119n, _), 64n), 0),
            C.bit_length(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> Nil{}), mul64(k))))), extra, C.round_constants(), s) : S.State}
      fips16_correct(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, 128), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> Nil{}), mul64(k))), extra, s)
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> Nil{}:
      %Equal.sym(Nat, Nat.mod(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> Nil{}), mul64(k)), 64n),
        Nat.mod(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> Nil{}), 64n),
        mod_tail(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> Nil{}), k)) :
        {C.stream(b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> Nil{}, mul64(k), extra, s) == C.block_bytes(List.append(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> Nil{},
          128 <> List.append(&2, U32, List.replicate(U32, Nat.mod(Nat.sub(119n, _), 64n), 0),
            C.bit_length(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> Nil{}), mul64(k))))), extra, C.round_constants(), s) : S.State}
      fips16_correct(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(128, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> Nil{}), mul64(k))), extra, s)
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> Nil{}:
      %Equal.sym(Nat, Nat.mod(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> Nil{}), mul64(k)), 64n),
        Nat.mod(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> Nil{}), 64n),
        mod_tail(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> Nil{}), k)) :
        {C.stream(b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> Nil{}, mul64(k), extra, s) == C.block_bytes(List.append(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> Nil{},
          128 <> List.append(&2, U32, List.replicate(U32, Nat.mod(Nat.sub(119n, _), 64n), 0),
            C.bit_length(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> Nil{}), mul64(k))))), extra, C.round_constants(), s) : S.State}
      fips16_correct(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, 128, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> Nil{}), mul64(k))), extra, s)
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> Nil{}:
      %Equal.sym(Nat, Nat.mod(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> Nil{}), mul64(k)), 64n),
        Nat.mod(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> Nil{}), 64n),
        mod_tail(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> Nil{}), k)) :
        {C.stream(b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> Nil{}, mul64(k), extra, s) == C.block_bytes(List.append(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> Nil{},
          128 <> List.append(&2, U32, List.replicate(U32, Nat.mod(Nat.sub(119n, _), 64n), 0),
            C.bit_length(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> Nil{}), mul64(k))))), extra, C.round_constants(), s) : S.State}
      fips16_correct(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, 128, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> Nil{}), mul64(k))), extra, s)
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> Nil{}:
      %Equal.sym(Nat, Nat.mod(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> Nil{}), mul64(k)), 64n),
        Nat.mod(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> Nil{}), 64n),
        mod_tail(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> Nil{}), k)) :
        {C.stream(b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> Nil{}, mul64(k), extra, s) == C.block_bytes(List.append(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> Nil{},
          128 <> List.append(&2, U32, List.replicate(U32, Nat.mod(Nat.sub(119n, _), 64n), 0),
            C.bit_length(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> Nil{}), mul64(k))))), extra, C.round_constants(), s) : S.State}
      fips16_correct(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, 128), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> Nil{}), mul64(k))), extra, s)
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> Nil{}:
      %Equal.sym(Nat, Nat.mod(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> Nil{}), mul64(k)), 64n),
        Nat.mod(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> Nil{}), 64n),
        mod_tail(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> Nil{}), k)) :
        {C.stream(b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> Nil{}, mul64(k), extra, s) == C.block_bytes(List.append(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> Nil{},
          128 <> List.append(&2, U32, List.replicate(U32, Nat.mod(Nat.sub(119n, _), 64n), 0),
            C.bit_length(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> Nil{}), mul64(k))))), extra, C.round_constants(), s) : S.State}
      fips16_correct(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(128, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> Nil{}), mul64(k))), extra, s)
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> Nil{}:
      %Equal.sym(Nat, Nat.mod(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> Nil{}), mul64(k)), 64n),
        Nat.mod(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> Nil{}), 64n),
        mod_tail(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> Nil{}), k)) :
        {C.stream(b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> Nil{}, mul64(k), extra, s) == C.block_bytes(List.append(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> Nil{},
          128 <> List.append(&2, U32, List.replicate(U32, Nat.mod(Nat.sub(119n, _), 64n), 0),
            C.bit_length(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> Nil{}), mul64(k))))), extra, C.round_constants(), s) : S.State}
      fips16_correct(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, 128, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> Nil{}), mul64(k))), extra, s)
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> Nil{}:
      %Equal.sym(Nat, Nat.mod(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> Nil{}), mul64(k)), 64n),
        Nat.mod(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> Nil{}), 64n),
        mod_tail(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> Nil{}), k)) :
        {C.stream(b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> Nil{}, mul64(k), extra, s) == C.block_bytes(List.append(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> Nil{},
          128 <> List.append(&2, U32, List.replicate(U32, Nat.mod(Nat.sub(119n, _), 64n), 0),
            C.bit_length(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> Nil{}), mul64(k))))), extra, C.round_constants(), s) : S.State}
      fips16_correct(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, 128, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> Nil{}), mul64(k))), extra, s)
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> Nil{}:
      %Equal.sym(Nat, Nat.mod(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> Nil{}), mul64(k)), 64n),
        Nat.mod(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> Nil{}), 64n),
        mod_tail(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> Nil{}), k)) :
        {C.stream(b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> Nil{}, mul64(k), extra, s) == C.block_bytes(List.append(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> Nil{},
          128 <> List.append(&2, U32, List.replicate(U32, Nat.mod(Nat.sub(119n, _), 64n), 0),
            C.bit_length(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> Nil{}), mul64(k))))), extra, C.round_constants(), s) : S.State}
      fips16_correct(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, 128), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> Nil{}), mul64(k))), extra, s)
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> Nil{}:
      %Equal.sym(Nat, Nat.mod(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> Nil{}), mul64(k)), 64n),
        Nat.mod(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> Nil{}), 64n),
        mod_tail(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> Nil{}), k)) :
        {C.stream(b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> Nil{}, mul64(k), extra, s) == C.block_bytes(List.append(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> Nil{},
          128 <> List.append(&2, U32, List.replicate(U32, Nat.mod(Nat.sub(119n, _), 64n), 0),
            C.bit_length(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> Nil{}), mul64(k))))), extra, C.round_constants(), s) : S.State}
      fips16_correct(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(128, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> Nil{}), mul64(k))), extra, s)
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> Nil{}:
      %Equal.sym(Nat, Nat.mod(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> Nil{}), mul64(k)), 64n),
        Nat.mod(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> Nil{}), 64n),
        mod_tail(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> Nil{}), k)) :
        {C.stream(b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> Nil{}, mul64(k), extra, s) == C.block_bytes(List.append(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> Nil{},
          128 <> List.append(&2, U32, List.replicate(U32, Nat.mod(Nat.sub(119n, _), 64n), 0),
            C.bit_length(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> Nil{}), mul64(k))))), extra, C.round_constants(), s) : S.State}
      fips16_correct(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, 128, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> Nil{}), mul64(k))), extra, s)
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> Nil{}:
      %Equal.sym(Nat, Nat.mod(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> Nil{}), mul64(k)), 64n),
        Nat.mod(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> Nil{}), 64n),
        mod_tail(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> Nil{}), k)) :
        {C.stream(b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> Nil{}, mul64(k), extra, s) == C.block_bytes(List.append(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> Nil{},
          128 <> List.append(&2, U32, List.replicate(U32, Nat.mod(Nat.sub(119n, _), 64n), 0),
            C.bit_length(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> Nil{}), mul64(k))))), extra, C.round_constants(), s) : S.State}
      fips16_correct(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, 128, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> Nil{}), mul64(k))), extra, s)
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> Nil{}:
      %Equal.sym(Nat, Nat.mod(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> Nil{}), mul64(k)), 64n),
        Nat.mod(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> Nil{}), 64n),
        mod_tail(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> Nil{}), k)) :
        {C.stream(b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> Nil{}, mul64(k), extra, s) == C.block_bytes(List.append(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> Nil{},
          128 <> List.append(&2, U32, List.replicate(U32, Nat.mod(Nat.sub(119n, _), 64n), 0),
            C.bit_length(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> Nil{}), mul64(k))))), extra, C.round_constants(), s) : S.State}
      fips16_correct(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, 128), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> Nil{}), mul64(k))), extra, s)
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> Nil{}:
      %Equal.sym(Nat, Nat.mod(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> Nil{}), mul64(k)), 64n),
        Nat.mod(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> Nil{}), 64n),
        mod_tail(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> Nil{}), k)) :
        {C.stream(b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> Nil{}, mul64(k), extra, s) == C.block_bytes(List.append(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> Nil{},
          128 <> List.append(&2, U32, List.replicate(U32, Nat.mod(Nat.sub(119n, _), 64n), 0),
            C.bit_length(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> Nil{}), mul64(k))))), extra, C.round_constants(), s) : S.State}
      fips16_correct(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(128, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> Nil{}), mul64(k))), extra, s)
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> Nil{}:
      %Equal.sym(Nat, Nat.mod(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> Nil{}), mul64(k)), 64n),
        Nat.mod(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> Nil{}), 64n),
        mod_tail(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> Nil{}), k)) :
        {C.stream(b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> Nil{}, mul64(k), extra, s) == C.block_bytes(List.append(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> Nil{},
          128 <> List.append(&2, U32, List.replicate(U32, Nat.mod(Nat.sub(119n, _), 64n), 0),
            C.bit_length(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> Nil{}), mul64(k))))), extra, C.round_constants(), s) : S.State}
      fips16_correct(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, 128, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> Nil{}), mul64(k))), extra, s)
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> Nil{}:
      %Equal.sym(Nat, Nat.mod(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> Nil{}), mul64(k)), 64n),
        Nat.mod(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> Nil{}), 64n),
        mod_tail(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> Nil{}), k)) :
        {C.stream(b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> Nil{}, mul64(k), extra, s) == C.block_bytes(List.append(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> Nil{},
          128 <> List.append(&2, U32, List.replicate(U32, Nat.mod(Nat.sub(119n, _), 64n), 0),
            C.bit_length(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> Nil{}), mul64(k))))), extra, C.round_constants(), s) : S.State}
      fips16_correct(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, 128, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> Nil{}), mul64(k))), extra, s)
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> Nil{}:
      %Equal.sym(Nat, Nat.mod(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> Nil{}), mul64(k)), 64n),
        Nat.mod(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> Nil{}), 64n),
        mod_tail(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> Nil{}), k)) :
        {C.stream(b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> Nil{}, mul64(k), extra, s) == C.block_bytes(List.append(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> Nil{},
          128 <> List.append(&2, U32, List.replicate(U32, Nat.mod(Nat.sub(119n, _), 64n), 0),
            C.bit_length(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> Nil{}), mul64(k))))), extra, C.round_constants(), s) : S.State}
      fips16_correct(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, 128), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> Nil{}), mul64(k))), extra, s)
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> Nil{}:
      %Equal.sym(Nat, Nat.mod(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> Nil{}), mul64(k)), 64n),
        Nat.mod(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> Nil{}), 64n),
        mod_tail(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> Nil{}), k)) :
        {C.stream(b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> Nil{}, mul64(k), extra, s) == C.block_bytes(List.append(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> Nil{},
          128 <> List.append(&2, U32, List.replicate(U32, Nat.mod(Nat.sub(119n, _), 64n), 0),
            C.bit_length(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> Nil{}), mul64(k))))), extra, C.round_constants(), s) : S.State}
      fips16_correct(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(128, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> Nil{}), mul64(k))), extra, s)
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> Nil{}:
      %Equal.sym(Nat, Nat.mod(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> Nil{}), mul64(k)), 64n),
        Nat.mod(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> Nil{}), 64n),
        mod_tail(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> Nil{}), k)) :
        {C.stream(b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> Nil{}, mul64(k), extra, s) == C.block_bytes(List.append(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> Nil{},
          128 <> List.append(&2, U32, List.replicate(U32, Nat.mod(Nat.sub(119n, _), 64n), 0),
            C.bit_length(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> Nil{}), mul64(k))))), extra, C.round_constants(), s) : S.State}
      fips16_correct(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, 128, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> Nil{}), mul64(k))), extra, s)
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> Nil{}:
      %Equal.sym(Nat, Nat.mod(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> Nil{}), mul64(k)), 64n),
        Nat.mod(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> Nil{}), 64n),
        mod_tail(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> Nil{}), k)) :
        {C.stream(b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> Nil{}, mul64(k), extra, s) == C.block_bytes(List.append(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> Nil{},
          128 <> List.append(&2, U32, List.replicate(U32, Nat.mod(Nat.sub(119n, _), 64n), 0),
            C.bit_length(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> Nil{}), mul64(k))))), extra, C.round_constants(), s) : S.State}
      fips16_correct(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, b33, 128, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> Nil{}), mul64(k))), extra, s)
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> Nil{}:
      %Equal.sym(Nat, Nat.mod(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> Nil{}), mul64(k)), 64n),
        Nat.mod(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> Nil{}), 64n),
        mod_tail(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> Nil{}), k)) :
        {C.stream(b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> Nil{}, mul64(k), extra, s) == C.block_bytes(List.append(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> Nil{},
          128 <> List.append(&2, U32, List.replicate(U32, Nat.mod(Nat.sub(119n, _), 64n), 0),
            C.bit_length(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> Nil{}), mul64(k))))), extra, C.round_constants(), s) : S.State}
      fips16_correct(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, b33, b34, 128), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> Nil{}), mul64(k))), extra, s)
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> Nil{}:
      %Equal.sym(Nat, Nat.mod(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> Nil{}), mul64(k)), 64n),
        Nat.mod(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> Nil{}), 64n),
        mod_tail(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> Nil{}), k)) :
        {C.stream(b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> Nil{}, mul64(k), extra, s) == C.block_bytes(List.append(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> Nil{},
          128 <> List.append(&2, U32, List.replicate(U32, Nat.mod(Nat.sub(119n, _), 64n), 0),
            C.bit_length(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> Nil{}), mul64(k))))), extra, C.round_constants(), s) : S.State}
      fips16_correct(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, b33, b34, b35), Runtime.pack(128, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> Nil{}), mul64(k))), extra, s)
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> Nil{}:
      %Equal.sym(Nat, Nat.mod(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> Nil{}), mul64(k)), 64n),
        Nat.mod(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> Nil{}), 64n),
        mod_tail(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> Nil{}), k)) :
        {C.stream(b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> Nil{}, mul64(k), extra, s) == C.block_bytes(List.append(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> Nil{},
          128 <> List.append(&2, U32, List.replicate(U32, Nat.mod(Nat.sub(119n, _), 64n), 0),
            C.bit_length(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> Nil{}), mul64(k))))), extra, C.round_constants(), s) : S.State}
      fips16_correct(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, 128, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> Nil{}), mul64(k))), extra, s)
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> Nil{}:
      %Equal.sym(Nat, Nat.mod(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> Nil{}), mul64(k)), 64n),
        Nat.mod(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> Nil{}), 64n),
        mod_tail(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> Nil{}), k)) :
        {C.stream(b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> Nil{}, mul64(k), extra, s) == C.block_bytes(List.append(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> Nil{},
          128 <> List.append(&2, U32, List.replicate(U32, Nat.mod(Nat.sub(119n, _), 64n), 0),
            C.bit_length(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> Nil{}), mul64(k))))), extra, C.round_constants(), s) : S.State}
      fips16_correct(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, 128, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> Nil{}), mul64(k))), extra, s)
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> Nil{}:
      %Equal.sym(Nat, Nat.mod(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> Nil{}), mul64(k)), 64n),
        Nat.mod(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> Nil{}), 64n),
        mod_tail(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> Nil{}), k)) :
        {C.stream(b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> Nil{}, mul64(k), extra, s) == C.block_bytes(List.append(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> Nil{},
          128 <> List.append(&2, U32, List.replicate(U32, Nat.mod(Nat.sub(119n, _), 64n), 0),
            C.bit_length(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> Nil{}), mul64(k))))), extra, C.round_constants(), s) : S.State}
      fips16_correct(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, b38, 128), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> Nil{}), mul64(k))), extra, s)
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> Nil{}:
      %Equal.sym(Nat, Nat.mod(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> Nil{}), mul64(k)), 64n),
        Nat.mod(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> Nil{}), 64n),
        mod_tail(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> Nil{}), k)) :
        {C.stream(b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> Nil{}, mul64(k), extra, s) == C.block_bytes(List.append(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> Nil{},
          128 <> List.append(&2, U32, List.replicate(U32, Nat.mod(Nat.sub(119n, _), 64n), 0),
            C.bit_length(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> Nil{}), mul64(k))))), extra, C.round_constants(), s) : S.State}
      fips16_correct(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, b38, b39), Runtime.pack(128, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> Nil{}), mul64(k))), extra, s)
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> Nil{}:
      %Equal.sym(Nat, Nat.mod(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> Nil{}), mul64(k)), 64n),
        Nat.mod(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> Nil{}), 64n),
        mod_tail(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> Nil{}), k)) :
        {C.stream(b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> Nil{}, mul64(k), extra, s) == C.block_bytes(List.append(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> Nil{},
          128 <> List.append(&2, U32, List.replicate(U32, Nat.mod(Nat.sub(119n, _), 64n), 0),
            C.bit_length(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> Nil{}), mul64(k))))), extra, C.round_constants(), s) : S.State}
      fips16_correct(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, b38, b39), Runtime.pack(b40, 128, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> Nil{}), mul64(k))), extra, s)
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> Nil{}:
      %Equal.sym(Nat, Nat.mod(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> Nil{}), mul64(k)), 64n),
        Nat.mod(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> Nil{}), 64n),
        mod_tail(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> Nil{}), k)) :
        {C.stream(b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> Nil{}, mul64(k), extra, s) == C.block_bytes(List.append(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> Nil{},
          128 <> List.append(&2, U32, List.replicate(U32, Nat.mod(Nat.sub(119n, _), 64n), 0),
            C.bit_length(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> Nil{}), mul64(k))))), extra, C.round_constants(), s) : S.State}
      fips16_correct(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, b38, b39), Runtime.pack(b40, b41, 128, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> Nil{}), mul64(k))), extra, s)
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> Nil{}:
      %Equal.sym(Nat, Nat.mod(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> Nil{}), mul64(k)), 64n),
        Nat.mod(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> Nil{}), 64n),
        mod_tail(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> Nil{}), k)) :
        {C.stream(b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> Nil{}, mul64(k), extra, s) == C.block_bytes(List.append(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> Nil{},
          128 <> List.append(&2, U32, List.replicate(U32, Nat.mod(Nat.sub(119n, _), 64n), 0),
            C.bit_length(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> Nil{}), mul64(k))))), extra, C.round_constants(), s) : S.State}
      fips16_correct(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, b38, b39), Runtime.pack(b40, b41, b42, 128), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> Nil{}), mul64(k))), extra, s)
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> Nil{}:
      %Equal.sym(Nat, Nat.mod(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> Nil{}), mul64(k)), 64n),
        Nat.mod(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> Nil{}), 64n),
        mod_tail(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> Nil{}), k)) :
        {C.stream(b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> Nil{}, mul64(k), extra, s) == C.block_bytes(List.append(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> Nil{},
          128 <> List.append(&2, U32, List.replicate(U32, Nat.mod(Nat.sub(119n, _), 64n), 0),
            C.bit_length(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> Nil{}), mul64(k))))), extra, C.round_constants(), s) : S.State}
      fips16_correct(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, b38, b39), Runtime.pack(b40, b41, b42, b43), Runtime.pack(128, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> Nil{}), mul64(k))), extra, s)
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> Nil{}:
      %Equal.sym(Nat, Nat.mod(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> Nil{}), mul64(k)), 64n),
        Nat.mod(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> Nil{}), 64n),
        mod_tail(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> Nil{}), k)) :
        {C.stream(b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> Nil{}, mul64(k), extra, s) == C.block_bytes(List.append(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> Nil{},
          128 <> List.append(&2, U32, List.replicate(U32, Nat.mod(Nat.sub(119n, _), 64n), 0),
            C.bit_length(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> Nil{}), mul64(k))))), extra, C.round_constants(), s) : S.State}
      fips16_correct(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, b38, b39), Runtime.pack(b40, b41, b42, b43), Runtime.pack(b44, 128, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> Nil{}), mul64(k))), extra, s)
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> Nil{}:
      %Equal.sym(Nat, Nat.mod(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> Nil{}), mul64(k)), 64n),
        Nat.mod(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> Nil{}), 64n),
        mod_tail(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> Nil{}), k)) :
        {C.stream(b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> Nil{}, mul64(k), extra, s) == C.block_bytes(List.append(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> Nil{},
          128 <> List.append(&2, U32, List.replicate(U32, Nat.mod(Nat.sub(119n, _), 64n), 0),
            C.bit_length(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> Nil{}), mul64(k))))), extra, C.round_constants(), s) : S.State}
      fips16_correct(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, b38, b39), Runtime.pack(b40, b41, b42, b43), Runtime.pack(b44, b45, 128, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> Nil{}), mul64(k))), extra, s)
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> Nil{}:
      %Equal.sym(Nat, Nat.mod(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> Nil{}), mul64(k)), 64n),
        Nat.mod(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> Nil{}), 64n),
        mod_tail(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> Nil{}), k)) :
        {C.stream(b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> Nil{}, mul64(k), extra, s) == C.block_bytes(List.append(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> Nil{},
          128 <> List.append(&2, U32, List.replicate(U32, Nat.mod(Nat.sub(119n, _), 64n), 0),
            C.bit_length(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> Nil{}), mul64(k))))), extra, C.round_constants(), s) : S.State}
      fips16_correct(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, b38, b39), Runtime.pack(b40, b41, b42, b43), Runtime.pack(b44, b45, b46, 128), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> Nil{}), mul64(k))), extra, s)
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> Nil{}:
      %Equal.sym(Nat, Nat.mod(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> Nil{}), mul64(k)), 64n),
        Nat.mod(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> Nil{}), 64n),
        mod_tail(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> Nil{}), k)) :
        {C.stream(b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> Nil{}, mul64(k), extra, s) == C.block_bytes(List.append(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> Nil{},
          128 <> List.append(&2, U32, List.replicate(U32, Nat.mod(Nat.sub(119n, _), 64n), 0),
            C.bit_length(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> Nil{}), mul64(k))))), extra, C.round_constants(), s) : S.State}
      fips16_correct(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, b38, b39), Runtime.pack(b40, b41, b42, b43), Runtime.pack(b44, b45, b46, b47), Runtime.pack(128, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> Nil{}), mul64(k))), extra, s)
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> Nil{}:
      %Equal.sym(Nat, Nat.mod(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> Nil{}), mul64(k)), 64n),
        Nat.mod(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> Nil{}), 64n),
        mod_tail(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> Nil{}), k)) :
        {C.stream(b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> Nil{}, mul64(k), extra, s) == C.block_bytes(List.append(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> Nil{},
          128 <> List.append(&2, U32, List.replicate(U32, Nat.mod(Nat.sub(119n, _), 64n), 0),
            C.bit_length(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> Nil{}), mul64(k))))), extra, C.round_constants(), s) : S.State}
      fips16_correct(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, b38, b39), Runtime.pack(b40, b41, b42, b43), Runtime.pack(b44, b45, b46, b47), Runtime.pack(b48, 128, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> Nil{}), mul64(k))), extra, s)
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> Nil{}:
      %Equal.sym(Nat, Nat.mod(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> Nil{}), mul64(k)), 64n),
        Nat.mod(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> Nil{}), 64n),
        mod_tail(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> Nil{}), k)) :
        {C.stream(b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> Nil{}, mul64(k), extra, s) == C.block_bytes(List.append(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> Nil{},
          128 <> List.append(&2, U32, List.replicate(U32, Nat.mod(Nat.sub(119n, _), 64n), 0),
            C.bit_length(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> Nil{}), mul64(k))))), extra, C.round_constants(), s) : S.State}
      fips16_correct(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, b38, b39), Runtime.pack(b40, b41, b42, b43), Runtime.pack(b44, b45, b46, b47), Runtime.pack(b48, b49, 128, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> Nil{}), mul64(k))), extra, s)
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> Nil{}:
      %Equal.sym(Nat, Nat.mod(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> Nil{}), mul64(k)), 64n),
        Nat.mod(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> Nil{}), 64n),
        mod_tail(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> Nil{}), k)) :
        {C.stream(b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> Nil{}, mul64(k), extra, s) == C.block_bytes(List.append(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> Nil{},
          128 <> List.append(&2, U32, List.replicate(U32, Nat.mod(Nat.sub(119n, _), 64n), 0),
            C.bit_length(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> Nil{}), mul64(k))))), extra, C.round_constants(), s) : S.State}
      fips16_correct(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, b38, b39), Runtime.pack(b40, b41, b42, b43), Runtime.pack(b44, b45, b46, b47), Runtime.pack(b48, b49, b50, 128), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> Nil{}), mul64(k))), extra, s)
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> Nil{}:
      %Equal.sym(Nat, Nat.mod(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> Nil{}), mul64(k)), 64n),
        Nat.mod(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> Nil{}), 64n),
        mod_tail(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> Nil{}), k)) :
        {C.stream(b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> Nil{}, mul64(k), extra, s) == C.block_bytes(List.append(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> Nil{},
          128 <> List.append(&2, U32, List.replicate(U32, Nat.mod(Nat.sub(119n, _), 64n), 0),
            C.bit_length(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> Nil{}), mul64(k))))), extra, C.round_constants(), s) : S.State}
      fips16_correct(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, b38, b39), Runtime.pack(b40, b41, b42, b43), Runtime.pack(b44, b45, b46, b47), Runtime.pack(b48, b49, b50, b51), Runtime.pack(128, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> Nil{}), mul64(k))), extra, s)
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> Nil{}:
      %Equal.sym(Nat, Nat.mod(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> Nil{}), mul64(k)), 64n),
        Nat.mod(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> Nil{}), 64n),
        mod_tail(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> Nil{}), k)) :
        {C.stream(b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> Nil{}, mul64(k), extra, s) == C.block_bytes(List.append(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> Nil{},
          128 <> List.append(&2, U32, List.replicate(U32, Nat.mod(Nat.sub(119n, _), 64n), 0),
            C.bit_length(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> Nil{}), mul64(k))))), extra, C.round_constants(), s) : S.State}
      fips16_correct(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, b38, b39), Runtime.pack(b40, b41, b42, b43), Runtime.pack(b44, b45, b46, b47), Runtime.pack(b48, b49, b50, b51), Runtime.pack(b52, 128, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> Nil{}), mul64(k))), extra, s)
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> Nil{}:
      %Equal.sym(Nat, Nat.mod(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> Nil{}), mul64(k)), 64n),
        Nat.mod(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> Nil{}), 64n),
        mod_tail(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> Nil{}), k)) :
        {C.stream(b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> Nil{}, mul64(k), extra, s) == C.block_bytes(List.append(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> Nil{},
          128 <> List.append(&2, U32, List.replicate(U32, Nat.mod(Nat.sub(119n, _), 64n), 0),
            C.bit_length(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> Nil{}), mul64(k))))), extra, C.round_constants(), s) : S.State}
      fips16_correct(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, b38, b39), Runtime.pack(b40, b41, b42, b43), Runtime.pack(b44, b45, b46, b47), Runtime.pack(b48, b49, b50, b51), Runtime.pack(b52, b53, 128, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> Nil{}), mul64(k))), extra, s)
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> Nil{}:
      %Equal.sym(Nat, Nat.mod(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> Nil{}), mul64(k)), 64n),
        Nat.mod(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> Nil{}), 64n),
        mod_tail(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> Nil{}), k)) :
        {C.stream(b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> Nil{}, mul64(k), extra, s) == C.block_bytes(List.append(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> Nil{},
          128 <> List.append(&2, U32, List.replicate(U32, Nat.mod(Nat.sub(119n, _), 64n), 0),
            C.bit_length(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> Nil{}), mul64(k))))), extra, C.round_constants(), s) : S.State}
      fips16_correct(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, b38, b39), Runtime.pack(b40, b41, b42, b43), Runtime.pack(b44, b45, b46, b47), Runtime.pack(b48, b49, b50, b51), Runtime.pack(b52, b53, b54, 128), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> Nil{}), mul64(k))), extra, s)
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> Nil{}:
      %Equal.sym(Nat, Nat.mod(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> Nil{}), mul64(k)), 64n),
        Nat.mod(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> Nil{}), 64n),
        mod_tail(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> Nil{}), k)) :
        {C.stream(b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> Nil{}, mul64(k), extra, s) == C.block_bytes(List.append(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> Nil{},
          128 <> List.append(&2, U32, List.replicate(U32, Nat.mod(Nat.sub(119n, _), 64n), 0),
            C.bit_length(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> Nil{}), mul64(k))))), extra, C.round_constants(), s) : S.State}
      Equal.trans(S.State,
        Runtime.fips_compress16(Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> Nil{}), mul64(k))), extra, Runtime.fips_compress16(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, b38, b39), Runtime.pack(b40, b41, b42, b43), Runtime.pack(b44, b45, b46, b47), Runtime.pack(b48, b49, b50, b51), Runtime.pack(b52, b53, b54, b55), Runtime.pack(128, 0, 0, 0), Runtime.pack(0, 0, 0, 0), extra, s)),
        C.window_compress16(Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> Nil{}), mul64(k))), extra, C.round_constants(), Runtime.fips_compress16(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, b38, b39), Runtime.pack(b40, b41, b42, b43), Runtime.pack(b44, b45, b46, b47), Runtime.pack(b48, b49, b50, b51), Runtime.pack(b52, b53, b54, b55), Runtime.pack(128, 0, 0, 0), Runtime.pack(0, 0, 0, 0), extra, s)),
        C.window_compress16(Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> Nil{}), mul64(k))), extra, C.round_constants(), C.window_compress16(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, b38, b39), Runtime.pack(b40, b41, b42, b43), Runtime.pack(b44, b45, b46, b47), Runtime.pack(b48, b49, b50, b51), Runtime.pack(b52, b53, b54, b55), Runtime.pack(128, 0, 0, 0), Runtime.pack(0, 0, 0, 0), extra, C.round_constants(), s)),
        fips16_correct(Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> Nil{}), mul64(k))), extra, Runtime.fips_compress16(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, b38, b39), Runtime.pack(b40, b41, b42, b43), Runtime.pack(b44, b45, b46, b47), Runtime.pack(b48, b49, b50, b51), Runtime.pack(b52, b53, b54, b55), Runtime.pack(128, 0, 0, 0), Runtime.pack(0, 0, 0, 0), extra, s)),
        Equal.cong(S.State, S.State, y => C.window_compress16(Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> Nil{}), mul64(k))), extra, C.round_constants(), y),
          Runtime.fips_compress16(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, b38, b39), Runtime.pack(b40, b41, b42, b43), Runtime.pack(b44, b45, b46, b47), Runtime.pack(b48, b49, b50, b51), Runtime.pack(b52, b53, b54, b55), Runtime.pack(128, 0, 0, 0), Runtime.pack(0, 0, 0, 0), extra, s), C.window_compress16(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, b38, b39), Runtime.pack(b40, b41, b42, b43), Runtime.pack(b44, b45, b46, b47), Runtime.pack(b48, b49, b50, b51), Runtime.pack(b52, b53, b54, b55), Runtime.pack(128, 0, 0, 0), Runtime.pack(0, 0, 0, 0), extra, C.round_constants(), s),
          fips16_correct(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, b38, b39), Runtime.pack(b40, b41, b42, b43), Runtime.pack(b44, b45, b46, b47), Runtime.pack(b48, b49, b50, b51), Runtime.pack(b52, b53, b54, b55), Runtime.pack(128, 0, 0, 0), Runtime.pack(0, 0, 0, 0), extra, s)))
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> Nil{}:
      %Equal.sym(Nat, Nat.mod(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> Nil{}), mul64(k)), 64n),
        Nat.mod(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> Nil{}), 64n),
        mod_tail(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> Nil{}), k)) :
        {C.stream(b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> Nil{}, mul64(k), extra, s) == C.block_bytes(List.append(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> Nil{},
          128 <> List.append(&2, U32, List.replicate(U32, Nat.mod(Nat.sub(119n, _), 64n), 0),
            C.bit_length(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> Nil{}), mul64(k))))), extra, C.round_constants(), s) : S.State}
      Equal.trans(S.State,
        Runtime.fips_compress16(Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> Nil{}), mul64(k))), extra, Runtime.fips_compress16(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, b38, b39), Runtime.pack(b40, b41, b42, b43), Runtime.pack(b44, b45, b46, b47), Runtime.pack(b48, b49, b50, b51), Runtime.pack(b52, b53, b54, b55), Runtime.pack(b56, 128, 0, 0), Runtime.pack(0, 0, 0, 0), extra, s)),
        C.window_compress16(Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> Nil{}), mul64(k))), extra, C.round_constants(), Runtime.fips_compress16(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, b38, b39), Runtime.pack(b40, b41, b42, b43), Runtime.pack(b44, b45, b46, b47), Runtime.pack(b48, b49, b50, b51), Runtime.pack(b52, b53, b54, b55), Runtime.pack(b56, 128, 0, 0), Runtime.pack(0, 0, 0, 0), extra, s)),
        C.window_compress16(Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> Nil{}), mul64(k))), extra, C.round_constants(), C.window_compress16(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, b38, b39), Runtime.pack(b40, b41, b42, b43), Runtime.pack(b44, b45, b46, b47), Runtime.pack(b48, b49, b50, b51), Runtime.pack(b52, b53, b54, b55), Runtime.pack(b56, 128, 0, 0), Runtime.pack(0, 0, 0, 0), extra, C.round_constants(), s)),
        fips16_correct(Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> Nil{}), mul64(k))), extra, Runtime.fips_compress16(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, b38, b39), Runtime.pack(b40, b41, b42, b43), Runtime.pack(b44, b45, b46, b47), Runtime.pack(b48, b49, b50, b51), Runtime.pack(b52, b53, b54, b55), Runtime.pack(b56, 128, 0, 0), Runtime.pack(0, 0, 0, 0), extra, s)),
        Equal.cong(S.State, S.State, y => C.window_compress16(Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> Nil{}), mul64(k))), extra, C.round_constants(), y),
          Runtime.fips_compress16(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, b38, b39), Runtime.pack(b40, b41, b42, b43), Runtime.pack(b44, b45, b46, b47), Runtime.pack(b48, b49, b50, b51), Runtime.pack(b52, b53, b54, b55), Runtime.pack(b56, 128, 0, 0), Runtime.pack(0, 0, 0, 0), extra, s), C.window_compress16(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, b38, b39), Runtime.pack(b40, b41, b42, b43), Runtime.pack(b44, b45, b46, b47), Runtime.pack(b48, b49, b50, b51), Runtime.pack(b52, b53, b54, b55), Runtime.pack(b56, 128, 0, 0), Runtime.pack(0, 0, 0, 0), extra, C.round_constants(), s),
          fips16_correct(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, b38, b39), Runtime.pack(b40, b41, b42, b43), Runtime.pack(b44, b45, b46, b47), Runtime.pack(b48, b49, b50, b51), Runtime.pack(b52, b53, b54, b55), Runtime.pack(b56, 128, 0, 0), Runtime.pack(0, 0, 0, 0), extra, s)))
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> Nil{}:
      %Equal.sym(Nat, Nat.mod(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> Nil{}), mul64(k)), 64n),
        Nat.mod(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> Nil{}), 64n),
        mod_tail(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> Nil{}), k)) :
        {C.stream(b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> Nil{}, mul64(k), extra, s) == C.block_bytes(List.append(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> Nil{},
          128 <> List.append(&2, U32, List.replicate(U32, Nat.mod(Nat.sub(119n, _), 64n), 0),
            C.bit_length(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> Nil{}), mul64(k))))), extra, C.round_constants(), s) : S.State}
      Equal.trans(S.State,
        Runtime.fips_compress16(Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> Nil{}), mul64(k))), extra, Runtime.fips_compress16(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, b38, b39), Runtime.pack(b40, b41, b42, b43), Runtime.pack(b44, b45, b46, b47), Runtime.pack(b48, b49, b50, b51), Runtime.pack(b52, b53, b54, b55), Runtime.pack(b56, b57, 128, 0), Runtime.pack(0, 0, 0, 0), extra, s)),
        C.window_compress16(Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> Nil{}), mul64(k))), extra, C.round_constants(), Runtime.fips_compress16(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, b38, b39), Runtime.pack(b40, b41, b42, b43), Runtime.pack(b44, b45, b46, b47), Runtime.pack(b48, b49, b50, b51), Runtime.pack(b52, b53, b54, b55), Runtime.pack(b56, b57, 128, 0), Runtime.pack(0, 0, 0, 0), extra, s)),
        C.window_compress16(Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> Nil{}), mul64(k))), extra, C.round_constants(), C.window_compress16(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, b38, b39), Runtime.pack(b40, b41, b42, b43), Runtime.pack(b44, b45, b46, b47), Runtime.pack(b48, b49, b50, b51), Runtime.pack(b52, b53, b54, b55), Runtime.pack(b56, b57, 128, 0), Runtime.pack(0, 0, 0, 0), extra, C.round_constants(), s)),
        fips16_correct(Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> Nil{}), mul64(k))), extra, Runtime.fips_compress16(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, b38, b39), Runtime.pack(b40, b41, b42, b43), Runtime.pack(b44, b45, b46, b47), Runtime.pack(b48, b49, b50, b51), Runtime.pack(b52, b53, b54, b55), Runtime.pack(b56, b57, 128, 0), Runtime.pack(0, 0, 0, 0), extra, s)),
        Equal.cong(S.State, S.State, y => C.window_compress16(Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> Nil{}), mul64(k))), extra, C.round_constants(), y),
          Runtime.fips_compress16(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, b38, b39), Runtime.pack(b40, b41, b42, b43), Runtime.pack(b44, b45, b46, b47), Runtime.pack(b48, b49, b50, b51), Runtime.pack(b52, b53, b54, b55), Runtime.pack(b56, b57, 128, 0), Runtime.pack(0, 0, 0, 0), extra, s), C.window_compress16(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, b38, b39), Runtime.pack(b40, b41, b42, b43), Runtime.pack(b44, b45, b46, b47), Runtime.pack(b48, b49, b50, b51), Runtime.pack(b52, b53, b54, b55), Runtime.pack(b56, b57, 128, 0), Runtime.pack(0, 0, 0, 0), extra, C.round_constants(), s),
          fips16_correct(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, b38, b39), Runtime.pack(b40, b41, b42, b43), Runtime.pack(b44, b45, b46, b47), Runtime.pack(b48, b49, b50, b51), Runtime.pack(b52, b53, b54, b55), Runtime.pack(b56, b57, 128, 0), Runtime.pack(0, 0, 0, 0), extra, s)))
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> Nil{}:
      %Equal.sym(Nat, Nat.mod(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> Nil{}), mul64(k)), 64n),
        Nat.mod(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> Nil{}), 64n),
        mod_tail(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> Nil{}), k)) :
        {C.stream(b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> Nil{}, mul64(k), extra, s) == C.block_bytes(List.append(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> Nil{},
          128 <> List.append(&2, U32, List.replicate(U32, Nat.mod(Nat.sub(119n, _), 64n), 0),
            C.bit_length(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> Nil{}), mul64(k))))), extra, C.round_constants(), s) : S.State}
      Equal.trans(S.State,
        Runtime.fips_compress16(Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> Nil{}), mul64(k))), extra, Runtime.fips_compress16(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, b38, b39), Runtime.pack(b40, b41, b42, b43), Runtime.pack(b44, b45, b46, b47), Runtime.pack(b48, b49, b50, b51), Runtime.pack(b52, b53, b54, b55), Runtime.pack(b56, b57, b58, 128), Runtime.pack(0, 0, 0, 0), extra, s)),
        C.window_compress16(Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> Nil{}), mul64(k))), extra, C.round_constants(), Runtime.fips_compress16(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, b38, b39), Runtime.pack(b40, b41, b42, b43), Runtime.pack(b44, b45, b46, b47), Runtime.pack(b48, b49, b50, b51), Runtime.pack(b52, b53, b54, b55), Runtime.pack(b56, b57, b58, 128), Runtime.pack(0, 0, 0, 0), extra, s)),
        C.window_compress16(Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> Nil{}), mul64(k))), extra, C.round_constants(), C.window_compress16(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, b38, b39), Runtime.pack(b40, b41, b42, b43), Runtime.pack(b44, b45, b46, b47), Runtime.pack(b48, b49, b50, b51), Runtime.pack(b52, b53, b54, b55), Runtime.pack(b56, b57, b58, 128), Runtime.pack(0, 0, 0, 0), extra, C.round_constants(), s)),
        fips16_correct(Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> Nil{}), mul64(k))), extra, Runtime.fips_compress16(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, b38, b39), Runtime.pack(b40, b41, b42, b43), Runtime.pack(b44, b45, b46, b47), Runtime.pack(b48, b49, b50, b51), Runtime.pack(b52, b53, b54, b55), Runtime.pack(b56, b57, b58, 128), Runtime.pack(0, 0, 0, 0), extra, s)),
        Equal.cong(S.State, S.State, y => C.window_compress16(Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> Nil{}), mul64(k))), extra, C.round_constants(), y),
          Runtime.fips_compress16(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, b38, b39), Runtime.pack(b40, b41, b42, b43), Runtime.pack(b44, b45, b46, b47), Runtime.pack(b48, b49, b50, b51), Runtime.pack(b52, b53, b54, b55), Runtime.pack(b56, b57, b58, 128), Runtime.pack(0, 0, 0, 0), extra, s), C.window_compress16(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, b38, b39), Runtime.pack(b40, b41, b42, b43), Runtime.pack(b44, b45, b46, b47), Runtime.pack(b48, b49, b50, b51), Runtime.pack(b52, b53, b54, b55), Runtime.pack(b56, b57, b58, 128), Runtime.pack(0, 0, 0, 0), extra, C.round_constants(), s),
          fips16_correct(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, b38, b39), Runtime.pack(b40, b41, b42, b43), Runtime.pack(b44, b45, b46, b47), Runtime.pack(b48, b49, b50, b51), Runtime.pack(b52, b53, b54, b55), Runtime.pack(b56, b57, b58, 128), Runtime.pack(0, 0, 0, 0), extra, s)))
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> b59 <> Nil{}:
      %Equal.sym(Nat, Nat.mod(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> b59 <> Nil{}), mul64(k)), 64n),
        Nat.mod(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> b59 <> Nil{}), 64n),
        mod_tail(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> b59 <> Nil{}), k)) :
        {C.stream(b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> b59 <> Nil{}, mul64(k), extra, s) == C.block_bytes(List.append(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> b59 <> Nil{},
          128 <> List.append(&2, U32, List.replicate(U32, Nat.mod(Nat.sub(119n, _), 64n), 0),
            C.bit_length(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> b59 <> Nil{}), mul64(k))))), extra, C.round_constants(), s) : S.State}
      Equal.trans(S.State,
        Runtime.fips_compress16(Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> b59 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> b59 <> Nil{}), mul64(k))), extra, Runtime.fips_compress16(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, b38, b39), Runtime.pack(b40, b41, b42, b43), Runtime.pack(b44, b45, b46, b47), Runtime.pack(b48, b49, b50, b51), Runtime.pack(b52, b53, b54, b55), Runtime.pack(b56, b57, b58, b59), Runtime.pack(128, 0, 0, 0), extra, s)),
        C.window_compress16(Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> b59 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> b59 <> Nil{}), mul64(k))), extra, C.round_constants(), Runtime.fips_compress16(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, b38, b39), Runtime.pack(b40, b41, b42, b43), Runtime.pack(b44, b45, b46, b47), Runtime.pack(b48, b49, b50, b51), Runtime.pack(b52, b53, b54, b55), Runtime.pack(b56, b57, b58, b59), Runtime.pack(128, 0, 0, 0), extra, s)),
        C.window_compress16(Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> b59 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> b59 <> Nil{}), mul64(k))), extra, C.round_constants(), C.window_compress16(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, b38, b39), Runtime.pack(b40, b41, b42, b43), Runtime.pack(b44, b45, b46, b47), Runtime.pack(b48, b49, b50, b51), Runtime.pack(b52, b53, b54, b55), Runtime.pack(b56, b57, b58, b59), Runtime.pack(128, 0, 0, 0), extra, C.round_constants(), s)),
        fips16_correct(Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> b59 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> b59 <> Nil{}), mul64(k))), extra, Runtime.fips_compress16(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, b38, b39), Runtime.pack(b40, b41, b42, b43), Runtime.pack(b44, b45, b46, b47), Runtime.pack(b48, b49, b50, b51), Runtime.pack(b52, b53, b54, b55), Runtime.pack(b56, b57, b58, b59), Runtime.pack(128, 0, 0, 0), extra, s)),
        Equal.cong(S.State, S.State, y => C.window_compress16(Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> b59 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> b59 <> Nil{}), mul64(k))), extra, C.round_constants(), y),
          Runtime.fips_compress16(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, b38, b39), Runtime.pack(b40, b41, b42, b43), Runtime.pack(b44, b45, b46, b47), Runtime.pack(b48, b49, b50, b51), Runtime.pack(b52, b53, b54, b55), Runtime.pack(b56, b57, b58, b59), Runtime.pack(128, 0, 0, 0), extra, s), C.window_compress16(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, b38, b39), Runtime.pack(b40, b41, b42, b43), Runtime.pack(b44, b45, b46, b47), Runtime.pack(b48, b49, b50, b51), Runtime.pack(b52, b53, b54, b55), Runtime.pack(b56, b57, b58, b59), Runtime.pack(128, 0, 0, 0), extra, C.round_constants(), s),
          fips16_correct(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, b38, b39), Runtime.pack(b40, b41, b42, b43), Runtime.pack(b44, b45, b46, b47), Runtime.pack(b48, b49, b50, b51), Runtime.pack(b52, b53, b54, b55), Runtime.pack(b56, b57, b58, b59), Runtime.pack(128, 0, 0, 0), extra, s)))
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> b59 <> b60 <> Nil{}:
      %Equal.sym(Nat, Nat.mod(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> b59 <> b60 <> Nil{}), mul64(k)), 64n),
        Nat.mod(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> b59 <> b60 <> Nil{}), 64n),
        mod_tail(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> b59 <> b60 <> Nil{}), k)) :
        {C.stream(b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> b59 <> b60 <> Nil{}, mul64(k), extra, s) == C.block_bytes(List.append(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> b59 <> b60 <> Nil{},
          128 <> List.append(&2, U32, List.replicate(U32, Nat.mod(Nat.sub(119n, _), 64n), 0),
            C.bit_length(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> b59 <> b60 <> Nil{}), mul64(k))))), extra, C.round_constants(), s) : S.State}
      Equal.trans(S.State,
        Runtime.fips_compress16(Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> b59 <> b60 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> b59 <> b60 <> Nil{}), mul64(k))), extra, Runtime.fips_compress16(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, b38, b39), Runtime.pack(b40, b41, b42, b43), Runtime.pack(b44, b45, b46, b47), Runtime.pack(b48, b49, b50, b51), Runtime.pack(b52, b53, b54, b55), Runtime.pack(b56, b57, b58, b59), Runtime.pack(b60, 128, 0, 0), extra, s)),
        C.window_compress16(Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> b59 <> b60 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> b59 <> b60 <> Nil{}), mul64(k))), extra, C.round_constants(), Runtime.fips_compress16(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, b38, b39), Runtime.pack(b40, b41, b42, b43), Runtime.pack(b44, b45, b46, b47), Runtime.pack(b48, b49, b50, b51), Runtime.pack(b52, b53, b54, b55), Runtime.pack(b56, b57, b58, b59), Runtime.pack(b60, 128, 0, 0), extra, s)),
        C.window_compress16(Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> b59 <> b60 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> b59 <> b60 <> Nil{}), mul64(k))), extra, C.round_constants(), C.window_compress16(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, b38, b39), Runtime.pack(b40, b41, b42, b43), Runtime.pack(b44, b45, b46, b47), Runtime.pack(b48, b49, b50, b51), Runtime.pack(b52, b53, b54, b55), Runtime.pack(b56, b57, b58, b59), Runtime.pack(b60, 128, 0, 0), extra, C.round_constants(), s)),
        fips16_correct(Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> b59 <> b60 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> b59 <> b60 <> Nil{}), mul64(k))), extra, Runtime.fips_compress16(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, b38, b39), Runtime.pack(b40, b41, b42, b43), Runtime.pack(b44, b45, b46, b47), Runtime.pack(b48, b49, b50, b51), Runtime.pack(b52, b53, b54, b55), Runtime.pack(b56, b57, b58, b59), Runtime.pack(b60, 128, 0, 0), extra, s)),
        Equal.cong(S.State, S.State, y => C.window_compress16(Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> b59 <> b60 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> b59 <> b60 <> Nil{}), mul64(k))), extra, C.round_constants(), y),
          Runtime.fips_compress16(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, b38, b39), Runtime.pack(b40, b41, b42, b43), Runtime.pack(b44, b45, b46, b47), Runtime.pack(b48, b49, b50, b51), Runtime.pack(b52, b53, b54, b55), Runtime.pack(b56, b57, b58, b59), Runtime.pack(b60, 128, 0, 0), extra, s), C.window_compress16(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, b38, b39), Runtime.pack(b40, b41, b42, b43), Runtime.pack(b44, b45, b46, b47), Runtime.pack(b48, b49, b50, b51), Runtime.pack(b52, b53, b54, b55), Runtime.pack(b56, b57, b58, b59), Runtime.pack(b60, 128, 0, 0), extra, C.round_constants(), s),
          fips16_correct(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, b38, b39), Runtime.pack(b40, b41, b42, b43), Runtime.pack(b44, b45, b46, b47), Runtime.pack(b48, b49, b50, b51), Runtime.pack(b52, b53, b54, b55), Runtime.pack(b56, b57, b58, b59), Runtime.pack(b60, 128, 0, 0), extra, s)))
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> b59 <> b60 <> b61 <> Nil{}:
      %Equal.sym(Nat, Nat.mod(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> b59 <> b60 <> b61 <> Nil{}), mul64(k)), 64n),
        Nat.mod(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> b59 <> b60 <> b61 <> Nil{}), 64n),
        mod_tail(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> b59 <> b60 <> b61 <> Nil{}), k)) :
        {C.stream(b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> b59 <> b60 <> b61 <> Nil{}, mul64(k), extra, s) == C.block_bytes(List.append(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> b59 <> b60 <> b61 <> Nil{},
          128 <> List.append(&2, U32, List.replicate(U32, Nat.mod(Nat.sub(119n, _), 64n), 0),
            C.bit_length(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> b59 <> b60 <> b61 <> Nil{}), mul64(k))))), extra, C.round_constants(), s) : S.State}
      Equal.trans(S.State,
        Runtime.fips_compress16(Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> b59 <> b60 <> b61 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> b59 <> b60 <> b61 <> Nil{}), mul64(k))), extra, Runtime.fips_compress16(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, b38, b39), Runtime.pack(b40, b41, b42, b43), Runtime.pack(b44, b45, b46, b47), Runtime.pack(b48, b49, b50, b51), Runtime.pack(b52, b53, b54, b55), Runtime.pack(b56, b57, b58, b59), Runtime.pack(b60, b61, 128, 0), extra, s)),
        C.window_compress16(Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> b59 <> b60 <> b61 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> b59 <> b60 <> b61 <> Nil{}), mul64(k))), extra, C.round_constants(), Runtime.fips_compress16(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, b38, b39), Runtime.pack(b40, b41, b42, b43), Runtime.pack(b44, b45, b46, b47), Runtime.pack(b48, b49, b50, b51), Runtime.pack(b52, b53, b54, b55), Runtime.pack(b56, b57, b58, b59), Runtime.pack(b60, b61, 128, 0), extra, s)),
        C.window_compress16(Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> b59 <> b60 <> b61 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> b59 <> b60 <> b61 <> Nil{}), mul64(k))), extra, C.round_constants(), C.window_compress16(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, b38, b39), Runtime.pack(b40, b41, b42, b43), Runtime.pack(b44, b45, b46, b47), Runtime.pack(b48, b49, b50, b51), Runtime.pack(b52, b53, b54, b55), Runtime.pack(b56, b57, b58, b59), Runtime.pack(b60, b61, 128, 0), extra, C.round_constants(), s)),
        fips16_correct(Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> b59 <> b60 <> b61 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> b59 <> b60 <> b61 <> Nil{}), mul64(k))), extra, Runtime.fips_compress16(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, b38, b39), Runtime.pack(b40, b41, b42, b43), Runtime.pack(b44, b45, b46, b47), Runtime.pack(b48, b49, b50, b51), Runtime.pack(b52, b53, b54, b55), Runtime.pack(b56, b57, b58, b59), Runtime.pack(b60, b61, 128, 0), extra, s)),
        Equal.cong(S.State, S.State, y => C.window_compress16(Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> b59 <> b60 <> b61 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> b59 <> b60 <> b61 <> Nil{}), mul64(k))), extra, C.round_constants(), y),
          Runtime.fips_compress16(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, b38, b39), Runtime.pack(b40, b41, b42, b43), Runtime.pack(b44, b45, b46, b47), Runtime.pack(b48, b49, b50, b51), Runtime.pack(b52, b53, b54, b55), Runtime.pack(b56, b57, b58, b59), Runtime.pack(b60, b61, 128, 0), extra, s), C.window_compress16(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, b38, b39), Runtime.pack(b40, b41, b42, b43), Runtime.pack(b44, b45, b46, b47), Runtime.pack(b48, b49, b50, b51), Runtime.pack(b52, b53, b54, b55), Runtime.pack(b56, b57, b58, b59), Runtime.pack(b60, b61, 128, 0), extra, C.round_constants(), s),
          fips16_correct(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, b38, b39), Runtime.pack(b40, b41, b42, b43), Runtime.pack(b44, b45, b46, b47), Runtime.pack(b48, b49, b50, b51), Runtime.pack(b52, b53, b54, b55), Runtime.pack(b56, b57, b58, b59), Runtime.pack(b60, b61, 128, 0), extra, s)))
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> b59 <> b60 <> b61 <> b62 <> Nil{}:
      %Equal.sym(Nat, Nat.mod(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> b59 <> b60 <> b61 <> b62 <> Nil{}), mul64(k)), 64n),
        Nat.mod(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> b59 <> b60 <> b61 <> b62 <> Nil{}), 64n),
        mod_tail(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> b59 <> b60 <> b61 <> b62 <> Nil{}), k)) :
        {C.stream(b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> b59 <> b60 <> b61 <> b62 <> Nil{}, mul64(k), extra, s) == C.block_bytes(List.append(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> b59 <> b60 <> b61 <> b62 <> Nil{},
          128 <> List.append(&2, U32, List.replicate(U32, Nat.mod(Nat.sub(119n, _), 64n), 0),
            C.bit_length(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> b59 <> b60 <> b61 <> b62 <> Nil{}), mul64(k))))), extra, C.round_constants(), s) : S.State}
      Equal.trans(S.State,
        Runtime.fips_compress16(Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> b59 <> b60 <> b61 <> b62 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> b59 <> b60 <> b61 <> b62 <> Nil{}), mul64(k))), extra, Runtime.fips_compress16(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, b38, b39), Runtime.pack(b40, b41, b42, b43), Runtime.pack(b44, b45, b46, b47), Runtime.pack(b48, b49, b50, b51), Runtime.pack(b52, b53, b54, b55), Runtime.pack(b56, b57, b58, b59), Runtime.pack(b60, b61, b62, 128), extra, s)),
        C.window_compress16(Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> b59 <> b60 <> b61 <> b62 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> b59 <> b60 <> b61 <> b62 <> Nil{}), mul64(k))), extra, C.round_constants(), Runtime.fips_compress16(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, b38, b39), Runtime.pack(b40, b41, b42, b43), Runtime.pack(b44, b45, b46, b47), Runtime.pack(b48, b49, b50, b51), Runtime.pack(b52, b53, b54, b55), Runtime.pack(b56, b57, b58, b59), Runtime.pack(b60, b61, b62, 128), extra, s)),
        C.window_compress16(Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> b59 <> b60 <> b61 <> b62 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> b59 <> b60 <> b61 <> b62 <> Nil{}), mul64(k))), extra, C.round_constants(), C.window_compress16(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, b38, b39), Runtime.pack(b40, b41, b42, b43), Runtime.pack(b44, b45, b46, b47), Runtime.pack(b48, b49, b50, b51), Runtime.pack(b52, b53, b54, b55), Runtime.pack(b56, b57, b58, b59), Runtime.pack(b60, b61, b62, 128), extra, C.round_constants(), s)),
        fips16_correct(Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> b59 <> b60 <> b61 <> b62 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> b59 <> b60 <> b61 <> b62 <> Nil{}), mul64(k))), extra, Runtime.fips_compress16(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, b38, b39), Runtime.pack(b40, b41, b42, b43), Runtime.pack(b44, b45, b46, b47), Runtime.pack(b48, b49, b50, b51), Runtime.pack(b52, b53, b54, b55), Runtime.pack(b56, b57, b58, b59), Runtime.pack(b60, b61, b62, 128), extra, s)),
        Equal.cong(S.State, S.State, y => C.window_compress16(Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> b59 <> b60 <> b61 <> b62 <> Nil{}), mul64(k))), Runtime.len_lo(Nat.add(List.length(&2, U32, b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> b59 <> b60 <> b61 <> b62 <> Nil{}), mul64(k))), extra, C.round_constants(), y),
          Runtime.fips_compress16(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, b38, b39), Runtime.pack(b40, b41, b42, b43), Runtime.pack(b44, b45, b46, b47), Runtime.pack(b48, b49, b50, b51), Runtime.pack(b52, b53, b54, b55), Runtime.pack(b56, b57, b58, b59), Runtime.pack(b60, b61, b62, 128), extra, s), C.window_compress16(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, b38, b39), Runtime.pack(b40, b41, b42, b43), Runtime.pack(b44, b45, b46, b47), Runtime.pack(b48, b49, b50, b51), Runtime.pack(b52, b53, b54, b55), Runtime.pack(b56, b57, b58, b59), Runtime.pack(b60, b61, b62, 128), extra, C.round_constants(), s),
          fips16_correct(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, b38, b39), Runtime.pack(b40, b41, b42, b43), Runtime.pack(b44, b45, b46, b47), Runtime.pack(b48, b49, b50, b51), Runtime.pack(b52, b53, b54, b55), Runtime.pack(b56, b57, b58, b59), Runtime.pack(b60, b61, b62, 128), extra, s)))

# Unlike the old theorem, there is NO arbitrary preprocessing parameter.
# This proves the actual implementation pipeline against the independent one.
law sha256_correct:
  for +bytes: List<&2, U32>
  {C.sha256(bytes) == F.hash(bytes, 48n, C.round_constants()) : List<&2, U32>}

def sha256_correct(bytes):
  %suffix_correct(List.length(&2, U32, bytes)) :
    {C.sha256(bytes) == F.digest(F.blocks(F.schedules(F.words(
      List.append(&2, U32, bytes, _)), 48n), C.round_constants())(F.initial())) : List<&2, U32>}
  %L.add_zero(List.length(&2, U32, bytes)) :
    {C.sha256(bytes) == F.digest(F.blocks(F.schedules(F.words(
      List.append(&2, U32, bytes, C.suffix(_))), 48n), C.round_constants())(F.initial())) : List<&2, U32>}
  +padded = List.append(&2, U32, bytes, C.suffix(Nat.add(List.length(&2, U32, bytes), 0n)))
  %digest_correct(F.blocks(F.schedules(F.words(padded), 48n), C.round_constants())(F.initial())) :
    {C.sha256(bytes) == _ : List<&2, U32>}
  Equal.cong(S.State, List<&2, U32>, s => C.digest(s),
    C.stream(bytes, 0n, 48n, Runtime.initial()),
    F.blocks(F.schedules(F.words(padded), 48n), C.round_constants())(Runtime.initial()),
    Equal.trans(S.State, C.stream(bytes, 0n, 48n, Runtime.initial()),
      C.block_bytes(padded, 48n, C.round_constants(), Runtime.initial()),
      F.blocks(F.schedules(F.words(padded), 48n), C.round_constants())(Runtime.initial()),
      stream_correct(bytes, 0n, 48n, Runtime.initial()),
      block_bytes_correct(padded, 48n, C.round_constants(), Runtime.initial())))
