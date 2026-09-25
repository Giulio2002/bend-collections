import Base
import ../state.bend as S

type ShaWindow is Data:
  W{a: U32, b: U32, c: U32, d: U32, e: U32, f: U32, g: U32, h: U32,
    i: U32, j: U32, k: U32, l: U32, m: U32, n: U32, o: U32, p: U32}

# SHA-256 for byte sequences. Each input U32 contributes its low 8 bits.
# SHA-256 arithmetic is native U32, hence addition wraps modulo 2^32.
def initial() -> S.State:
  S.H{1779033703, 3144134277, 1013904242, 2773480762,
    1359893119, 2600822924, 528734635, 1541459225}

def big0(+x: U32) -> U32:
  ((U32.shrn(x, 2n) .|. U32.shln(x, 30n))
    .^. (U32.shrn(x, 13n) .|. U32.shln(x, 19n))
    .^. (U32.shrn(x, 22n) .|. U32.shln(x, 10n)) : U32)

def big1(+x: U32) -> U32:
  ((U32.shrn(x, 6n) .|. U32.shln(x, 26n))
    .^. (U32.shrn(x, 11n) .|. U32.shln(x, 21n))
    .^. (U32.shrn(x, 25n) .|. U32.shln(x, 7n)) : U32)

def small0(+x: U32) -> U32:
  ((U32.shrn(x, 7n) .|. U32.shln(x, 25n))
    .^. (U32.shrn(x, 18n) .|. U32.shln(x, 14n))
    .^. U32.shrn(x, 3n) : U32)

def small1(+x: U32) -> U32:
  ((U32.shrn(x, 17n) .|. U32.shln(x, 15n))
    .^. (U32.shrn(x, 19n) .|. U32.shln(x, 13n))
    .^. U32.shrn(x, 10n) : U32)

def choose(+x: U32, y: U32, z: U32) -> U32:
  ((x .&. y) .^. (U32.not(x) .&. z) : U32)

def majority(+x: U32, +y: U32, +z: U32) -> U32:
  ((x .&. y) .^. (x .&. z) .^. (y .&. z) : U32)

def step(s: S.State, k: U32, w: U32) -> S.State:
  S.H{+a, +b, +c, d, +e, +f, +g, h} = s
  +t1 = (h + big1(e) + choose(e, f, g) + k + w : U32)
  t2 = (big0(a) + majority(a, b, c) : U32)
  S.H{(t1 + t2 : U32), a, b, c, (d + t1 : U32), e, f, g}

def feedforward(x: S.State, y: S.State) -> S.State:
  S.H{a, b, c, d, e, f, g, h} = x
  S.H{i, j, k, l, m, n, o, p} = y
  S.H{(a + i : U32), (b + j : U32), (c + k : U32), (d + l : U32),
    (e + m : U32), (f + n : U32), (g + o : U32), (h + p : U32)}

def pack(a: U32, b: U32, c: U32, d: U32) -> U32:
  (U32.shln((a .&. 255 : U32), 24n)
    .|. U32.shln((b .&. 255 : U32), 16n)
    .|. U32.shln((c .&. 255 : U32), 8n) .|. (d .&. 255) : U32)

def kr64(q: Nat, win: ShaWindow, s: S.State) -> S.State:
  s

def kr63(q: Nat, win: ShaWindow, s: S.State) -> S.State:
  match q win:
    case 0n _:
      s
    case 1n+z W{a, +b, c, d, e, f, +g, h, i, j, l, m, o, r, +t, +u}:
      +w = (small1(b) + g + small0(t) + u : U32)
      kr64(z, W{w, a, b, c, d, e, f, g, h, i, j, l, m, o, r, t}, step(s, 3329325298, w))

def kr62(q: Nat, win: ShaWindow, s: S.State) -> S.State:
  match q win:
    case 0n _:
      s
    case 1n+z W{a, +b, c, d, e, f, +g, h, i, j, l, m, o, r, +t, +u}:
      +w = (small1(b) + g + small0(t) + u : U32)
      kr63(z, W{w, a, b, c, d, e, f, g, h, i, j, l, m, o, r, t}, step(s, 3204031479, w))

def kr61(q: Nat, win: ShaWindow, s: S.State) -> S.State:
  match q win:
    case 0n _:
      s
    case 1n+z W{a, +b, c, d, e, f, +g, h, i, j, l, m, o, r, +t, +u}:
      +w = (small1(b) + g + small0(t) + u : U32)
      kr62(z, W{w, a, b, c, d, e, f, g, h, i, j, l, m, o, r, t}, step(s, 2756734187, w))

def kr60(q: Nat, win: ShaWindow, s: S.State) -> S.State:
  match q win:
    case 0n _:
      s
    case 1n+z W{a, +b, c, d, e, f, +g, h, i, j, l, m, o, r, +t, +u}:
      +w = (small1(b) + g + small0(t) + u : U32)
      kr61(z, W{w, a, b, c, d, e, f, g, h, i, j, l, m, o, r, t}, step(s, 2428436474, w))

def kr59(q: Nat, win: ShaWindow, s: S.State) -> S.State:
  match q win:
    case 0n _:
      s
    case 1n+z W{a, +b, c, d, e, f, +g, h, i, j, l, m, o, r, +t, +u}:
      +w = (small1(b) + g + small0(t) + u : U32)
      kr60(z, W{w, a, b, c, d, e, f, g, h, i, j, l, m, o, r, t}, step(s, 2361852424, w))

def kr58(q: Nat, win: ShaWindow, s: S.State) -> S.State:
  match q win:
    case 0n _:
      s
    case 1n+z W{a, +b, c, d, e, f, +g, h, i, j, l, m, o, r, +t, +u}:
      +w = (small1(b) + g + small0(t) + u : U32)
      kr59(z, W{w, a, b, c, d, e, f, g, h, i, j, l, m, o, r, t}, step(s, 2227730452, w))

def kr57(q: Nat, win: ShaWindow, s: S.State) -> S.State:
  match q win:
    case 0n _:
      s
    case 1n+z W{a, +b, c, d, e, f, +g, h, i, j, l, m, o, r, +t, +u}:
      +w = (small1(b) + g + small0(t) + u : U32)
      kr58(z, W{w, a, b, c, d, e, f, g, h, i, j, l, m, o, r, t}, step(s, 2024104815, w))

def kr56(q: Nat, win: ShaWindow, s: S.State) -> S.State:
  match q win:
    case 0n _:
      s
    case 1n+z W{a, +b, c, d, e, f, +g, h, i, j, l, m, o, r, +t, +u}:
      +w = (small1(b) + g + small0(t) + u : U32)
      kr57(z, W{w, a, b, c, d, e, f, g, h, i, j, l, m, o, r, t}, step(s, 1955562222, w))

def kr55(q: Nat, win: ShaWindow, s: S.State) -> S.State:
  match q win:
    case 0n _:
      s
    case 1n+z W{a, +b, c, d, e, f, +g, h, i, j, l, m, o, r, +t, +u}:
      +w = (small1(b) + g + small0(t) + u : U32)
      kr56(z, W{w, a, b, c, d, e, f, g, h, i, j, l, m, o, r, t}, step(s, 1747873779, w))

def kr54(q: Nat, win: ShaWindow, s: S.State) -> S.State:
  match q win:
    case 0n _:
      s
    case 1n+z W{a, +b, c, d, e, f, +g, h, i, j, l, m, o, r, +t, +u}:
      +w = (small1(b) + g + small0(t) + u : U32)
      kr55(z, W{w, a, b, c, d, e, f, g, h, i, j, l, m, o, r, t}, step(s, 1537002063, w))

def kr53(q: Nat, win: ShaWindow, s: S.State) -> S.State:
  match q win:
    case 0n _:
      s
    case 1n+z W{a, +b, c, d, e, f, +g, h, i, j, l, m, o, r, +t, +u}:
      +w = (small1(b) + g + small0(t) + u : U32)
      kr54(z, W{w, a, b, c, d, e, f, g, h, i, j, l, m, o, r, t}, step(s, 1322822218, w))

def kr52(q: Nat, win: ShaWindow, s: S.State) -> S.State:
  match q win:
    case 0n _:
      s
    case 1n+z W{a, +b, c, d, e, f, +g, h, i, j, l, m, o, r, +t, +u}:
      +w = (small1(b) + g + small0(t) + u : U32)
      kr53(z, W{w, a, b, c, d, e, f, g, h, i, j, l, m, o, r, t}, step(s, 958139571, w))

def kr51(q: Nat, win: ShaWindow, s: S.State) -> S.State:
  match q win:
    case 0n _:
      s
    case 1n+z W{a, +b, c, d, e, f, +g, h, i, j, l, m, o, r, +t, +u}:
      +w = (small1(b) + g + small0(t) + u : U32)
      kr52(z, W{w, a, b, c, d, e, f, g, h, i, j, l, m, o, r, t}, step(s, 883997877, w))

def kr50(q: Nat, win: ShaWindow, s: S.State) -> S.State:
  match q win:
    case 0n _:
      s
    case 1n+z W{a, +b, c, d, e, f, +g, h, i, j, l, m, o, r, +t, +u}:
      +w = (small1(b) + g + small0(t) + u : U32)
      kr51(z, W{w, a, b, c, d, e, f, g, h, i, j, l, m, o, r, t}, step(s, 659060556, w))

def kr49(q: Nat, win: ShaWindow, s: S.State) -> S.State:
  match q win:
    case 0n _:
      s
    case 1n+z W{a, +b, c, d, e, f, +g, h, i, j, l, m, o, r, +t, +u}:
      +w = (small1(b) + g + small0(t) + u : U32)
      kr50(z, W{w, a, b, c, d, e, f, g, h, i, j, l, m, o, r, t}, step(s, 506948616, w))

def kr48(q: Nat, win: ShaWindow, s: S.State) -> S.State:
  match q win:
    case 0n _:
      s
    case 1n+z W{a, +b, c, d, e, f, +g, h, i, j, l, m, o, r, +t, +u}:
      +w = (small1(b) + g + small0(t) + u : U32)
      kr49(z, W{w, a, b, c, d, e, f, g, h, i, j, l, m, o, r, t}, step(s, 430227734, w))

def kr47(q: Nat, win: ShaWindow, s: S.State) -> S.State:
  match q win:
    case 0n _:
      s
    case 1n+z W{a, +b, c, d, e, f, +g, h, i, j, l, m, o, r, +t, +u}:
      +w = (small1(b) + g + small0(t) + u : U32)
      kr48(z, W{w, a, b, c, d, e, f, g, h, i, j, l, m, o, r, t}, step(s, 275423344, w))

def kr46(q: Nat, win: ShaWindow, s: S.State) -> S.State:
  match q win:
    case 0n _:
      s
    case 1n+z W{a, +b, c, d, e, f, +g, h, i, j, l, m, o, r, +t, +u}:
      +w = (small1(b) + g + small0(t) + u : U32)
      kr47(z, W{w, a, b, c, d, e, f, g, h, i, j, l, m, o, r, t}, step(s, 4094571909, w))

def kr45(q: Nat, win: ShaWindow, s: S.State) -> S.State:
  match q win:
    case 0n _:
      s
    case 1n+z W{a, +b, c, d, e, f, +g, h, i, j, l, m, o, r, +t, +u}:
      +w = (small1(b) + g + small0(t) + u : U32)
      kr46(z, W{w, a, b, c, d, e, f, g, h, i, j, l, m, o, r, t}, step(s, 3600352804, w))

def kr44(q: Nat, win: ShaWindow, s: S.State) -> S.State:
  match q win:
    case 0n _:
      s
    case 1n+z W{a, +b, c, d, e, f, +g, h, i, j, l, m, o, r, +t, +u}:
      +w = (small1(b) + g + small0(t) + u : U32)
      kr45(z, W{w, a, b, c, d, e, f, g, h, i, j, l, m, o, r, t}, step(s, 3516065817, w))

def kr43(q: Nat, win: ShaWindow, s: S.State) -> S.State:
  match q win:
    case 0n _:
      s
    case 1n+z W{a, +b, c, d, e, f, +g, h, i, j, l, m, o, r, +t, +u}:
      +w = (small1(b) + g + small0(t) + u : U32)
      kr44(z, W{w, a, b, c, d, e, f, g, h, i, j, l, m, o, r, t}, step(s, 3345764771, w))

def kr42(q: Nat, win: ShaWindow, s: S.State) -> S.State:
  match q win:
    case 0n _:
      s
    case 1n+z W{a, +b, c, d, e, f, +g, h, i, j, l, m, o, r, +t, +u}:
      +w = (small1(b) + g + small0(t) + u : U32)
      kr43(z, W{w, a, b, c, d, e, f, g, h, i, j, l, m, o, r, t}, step(s, 3259730800, w))

def kr41(q: Nat, win: ShaWindow, s: S.State) -> S.State:
  match q win:
    case 0n _:
      s
    case 1n+z W{a, +b, c, d, e, f, +g, h, i, j, l, m, o, r, +t, +u}:
      +w = (small1(b) + g + small0(t) + u : U32)
      kr42(z, W{w, a, b, c, d, e, f, g, h, i, j, l, m, o, r, t}, step(s, 2820302411, w))

def kr40(q: Nat, win: ShaWindow, s: S.State) -> S.State:
  match q win:
    case 0n _:
      s
    case 1n+z W{a, +b, c, d, e, f, +g, h, i, j, l, m, o, r, +t, +u}:
      +w = (small1(b) + g + small0(t) + u : U32)
      kr41(z, W{w, a, b, c, d, e, f, g, h, i, j, l, m, o, r, t}, step(s, 2730485921, w))

def kr39(q: Nat, win: ShaWindow, s: S.State) -> S.State:
  match q win:
    case 0n _:
      s
    case 1n+z W{a, +b, c, d, e, f, +g, h, i, j, l, m, o, r, +t, +u}:
      +w = (small1(b) + g + small0(t) + u : U32)
      kr40(z, W{w, a, b, c, d, e, f, g, h, i, j, l, m, o, r, t}, step(s, 2456956037, w))

def kr38(q: Nat, win: ShaWindow, s: S.State) -> S.State:
  match q win:
    case 0n _:
      s
    case 1n+z W{a, +b, c, d, e, f, +g, h, i, j, l, m, o, r, +t, +u}:
      +w = (small1(b) + g + small0(t) + u : U32)
      kr39(z, W{w, a, b, c, d, e, f, g, h, i, j, l, m, o, r, t}, step(s, 2177026350, w))

def kr37(q: Nat, win: ShaWindow, s: S.State) -> S.State:
  match q win:
    case 0n _:
      s
    case 1n+z W{a, +b, c, d, e, f, +g, h, i, j, l, m, o, r, +t, +u}:
      +w = (small1(b) + g + small0(t) + u : U32)
      kr38(z, W{w, a, b, c, d, e, f, g, h, i, j, l, m, o, r, t}, step(s, 1986661051, w))

def kr36(q: Nat, win: ShaWindow, s: S.State) -> S.State:
  match q win:
    case 0n _:
      s
    case 1n+z W{a, +b, c, d, e, f, +g, h, i, j, l, m, o, r, +t, +u}:
      +w = (small1(b) + g + small0(t) + u : U32)
      kr37(z, W{w, a, b, c, d, e, f, g, h, i, j, l, m, o, r, t}, step(s, 1695183700, w))

def kr35(q: Nat, win: ShaWindow, s: S.State) -> S.State:
  match q win:
    case 0n _:
      s
    case 1n+z W{a, +b, c, d, e, f, +g, h, i, j, l, m, o, r, +t, +u}:
      +w = (small1(b) + g + small0(t) + u : U32)
      kr36(z, W{w, a, b, c, d, e, f, g, h, i, j, l, m, o, r, t}, step(s, 1396182291, w))

def kr34(q: Nat, win: ShaWindow, s: S.State) -> S.State:
  match q win:
    case 0n _:
      s
    case 1n+z W{a, +b, c, d, e, f, +g, h, i, j, l, m, o, r, +t, +u}:
      +w = (small1(b) + g + small0(t) + u : U32)
      kr35(z, W{w, a, b, c, d, e, f, g, h, i, j, l, m, o, r, t}, step(s, 1294757372, w))

def kr33(q: Nat, win: ShaWindow, s: S.State) -> S.State:
  match q win:
    case 0n _:
      s
    case 1n+z W{a, +b, c, d, e, f, +g, h, i, j, l, m, o, r, +t, +u}:
      +w = (small1(b) + g + small0(t) + u : U32)
      kr34(z, W{w, a, b, c, d, e, f, g, h, i, j, l, m, o, r, t}, step(s, 773529912, w))

def kr32(q: Nat, win: ShaWindow, s: S.State) -> S.State:
  match q win:
    case 0n _:
      s
    case 1n+z W{a, +b, c, d, e, f, +g, h, i, j, l, m, o, r, +t, +u}:
      +w = (small1(b) + g + small0(t) + u : U32)
      kr33(z, W{w, a, b, c, d, e, f, g, h, i, j, l, m, o, r, t}, step(s, 666307205, w))

def kr31(q: Nat, win: ShaWindow, s: S.State) -> S.State:
  match q win:
    case 0n _:
      s
    case 1n+z W{a, +b, c, d, e, f, +g, h, i, j, l, m, o, r, +t, +u}:
      +w = (small1(b) + g + small0(t) + u : U32)
      kr32(z, W{w, a, b, c, d, e, f, g, h, i, j, l, m, o, r, t}, step(s, 338241895, w))

def kr30(q: Nat, win: ShaWindow, s: S.State) -> S.State:
  match q win:
    case 0n _:
      s
    case 1n+z W{a, +b, c, d, e, f, +g, h, i, j, l, m, o, r, +t, +u}:
      +w = (small1(b) + g + small0(t) + u : U32)
      kr31(z, W{w, a, b, c, d, e, f, g, h, i, j, l, m, o, r, t}, step(s, 113926993, w))

def kr29(q: Nat, win: ShaWindow, s: S.State) -> S.State:
  match q win:
    case 0n _:
      s
    case 1n+z W{a, +b, c, d, e, f, +g, h, i, j, l, m, o, r, +t, +u}:
      +w = (small1(b) + g + small0(t) + u : U32)
      kr30(z, W{w, a, b, c, d, e, f, g, h, i, j, l, m, o, r, t}, step(s, 3584528711, w))

def kr28(q: Nat, win: ShaWindow, s: S.State) -> S.State:
  match q win:
    case 0n _:
      s
    case 1n+z W{a, +b, c, d, e, f, +g, h, i, j, l, m, o, r, +t, +u}:
      +w = (small1(b) + g + small0(t) + u : U32)
      kr29(z, W{w, a, b, c, d, e, f, g, h, i, j, l, m, o, r, t}, step(s, 3336571891, w))

def kr27(q: Nat, win: ShaWindow, s: S.State) -> S.State:
  match q win:
    case 0n _:
      s
    case 1n+z W{a, +b, c, d, e, f, +g, h, i, j, l, m, o, r, +t, +u}:
      +w = (small1(b) + g + small0(t) + u : U32)
      kr28(z, W{w, a, b, c, d, e, f, g, h, i, j, l, m, o, r, t}, step(s, 3210313671, w))

def kr26(q: Nat, win: ShaWindow, s: S.State) -> S.State:
  match q win:
    case 0n _:
      s
    case 1n+z W{a, +b, c, d, e, f, +g, h, i, j, l, m, o, r, +t, +u}:
      +w = (small1(b) + g + small0(t) + u : U32)
      kr27(z, W{w, a, b, c, d, e, f, g, h, i, j, l, m, o, r, t}, step(s, 2952996808, w))

def kr25(q: Nat, win: ShaWindow, s: S.State) -> S.State:
  match q win:
    case 0n _:
      s
    case 1n+z W{a, +b, c, d, e, f, +g, h, i, j, l, m, o, r, +t, +u}:
      +w = (small1(b) + g + small0(t) + u : U32)
      kr26(z, W{w, a, b, c, d, e, f, g, h, i, j, l, m, o, r, t}, step(s, 2821834349, w))

def kr24(q: Nat, win: ShaWindow, s: S.State) -> S.State:
  match q win:
    case 0n _:
      s
    case 1n+z W{a, +b, c, d, e, f, +g, h, i, j, l, m, o, r, +t, +u}:
      +w = (small1(b) + g + small0(t) + u : U32)
      kr25(z, W{w, a, b, c, d, e, f, g, h, i, j, l, m, o, r, t}, step(s, 2554220882, w))

def kr23(q: Nat, win: ShaWindow, s: S.State) -> S.State:
  match q win:
    case 0n _:
      s
    case 1n+z W{a, +b, c, d, e, f, +g, h, i, j, l, m, o, r, +t, +u}:
      +w = (small1(b) + g + small0(t) + u : U32)
      kr24(z, W{w, a, b, c, d, e, f, g, h, i, j, l, m, o, r, t}, step(s, 1996064986, w))

def kr22(q: Nat, win: ShaWindow, s: S.State) -> S.State:
  match q win:
    case 0n _:
      s
    case 1n+z W{a, +b, c, d, e, f, +g, h, i, j, l, m, o, r, +t, +u}:
      +w = (small1(b) + g + small0(t) + u : U32)
      kr23(z, W{w, a, b, c, d, e, f, g, h, i, j, l, m, o, r, t}, step(s, 1555081692, w))

def kr21(q: Nat, win: ShaWindow, s: S.State) -> S.State:
  match q win:
    case 0n _:
      s
    case 1n+z W{a, +b, c, d, e, f, +g, h, i, j, l, m, o, r, +t, +u}:
      +w = (small1(b) + g + small0(t) + u : U32)
      kr22(z, W{w, a, b, c, d, e, f, g, h, i, j, l, m, o, r, t}, step(s, 1249150122, w))

def kr20(q: Nat, win: ShaWindow, s: S.State) -> S.State:
  match q win:
    case 0n _:
      s
    case 1n+z W{a, +b, c, d, e, f, +g, h, i, j, l, m, o, r, +t, +u}:
      +w = (small1(b) + g + small0(t) + u : U32)
      kr21(z, W{w, a, b, c, d, e, f, g, h, i, j, l, m, o, r, t}, step(s, 770255983, w))

def kr19(q: Nat, win: ShaWindow, s: S.State) -> S.State:
  match q win:
    case 0n _:
      s
    case 1n+z W{a, +b, c, d, e, f, +g, h, i, j, l, m, o, r, +t, +u}:
      +w = (small1(b) + g + small0(t) + u : U32)
      kr20(z, W{w, a, b, c, d, e, f, g, h, i, j, l, m, o, r, t}, step(s, 604807628, w))

def kr18(q: Nat, win: ShaWindow, s: S.State) -> S.State:
  match q win:
    case 0n _:
      s
    case 1n+z W{a, +b, c, d, e, f, +g, h, i, j, l, m, o, r, +t, +u}:
      +w = (small1(b) + g + small0(t) + u : U32)
      kr19(z, W{w, a, b, c, d, e, f, g, h, i, j, l, m, o, r, t}, step(s, 264347078, w))

def kr17(q: Nat, win: ShaWindow, s: S.State) -> S.State:
  match q win:
    case 0n _:
      s
    case 1n+z W{a, +b, c, d, e, f, +g, h, i, j, l, m, o, r, +t, +u}:
      +w = (small1(b) + g + small0(t) + u : U32)
      kr18(z, W{w, a, b, c, d, e, f, g, h, i, j, l, m, o, r, t}, step(s, 4022224774, w))

def kr16(q: Nat, win: ShaWindow, s: S.State) -> S.State:
  match q win:
    case 0n _:
      s
    case 1n+z W{a, +b, c, d, e, f, +g, h, i, j, l, m, o, r, +t, +u}:
      +w = (small1(b) + g + small0(t) + u : U32)
      kr17(z, W{w, a, b, c, d, e, f, g, h, i, j, l, m, o, r, t}, step(s, 3835390401, w))

# window_compress16 specialized to the FIPS table: no constant list is walked.
def fips_compress16(+a: U32, +b: U32, +c: U32, +d: U32,
  +e: U32, +f: U32, +g: U32, +h: U32,
  +i: U32, +j: U32, +k: U32, +l: U32,
  +m: U32, +n: U32, +o: U32, +p: U32, +q: Nat, +s: S.State) -> S.State:
  s1 = step(s, 1116352408, a)
  s2 = step(s1, 1899447441, b)
  s3 = step(s2, 3049323471, c)
  s4 = step(s3, 3921009573, d)
  s5 = step(s4, 961987163, e)
  s6 = step(s5, 1508970993, f)
  s7 = step(s6, 2453635748, g)
  s8 = step(s7, 2870763221, h)
  s9 = step(s8, 3624381080, i)
  s10 = step(s9, 310598401, j)
  s11 = step(s10, 607225278, k)
  s12 = step(s11, 1426881987, l)
  s13 = step(s12, 1925078388, m)
  s14 = step(s13, 2162078206, n)
  s15 = step(s14, 2614888103, o)
  s16 = step(s15, 3248222580, p)
  feedforward(s, kr16(q, W{p, o, n, m, l, k, j, i, h, g, f, e, d, c, b, a}, s16))

# FIPS padding suffix for a message of n bytes, computed with modular
# arithmetic. The proofs state the streaming hash in terms of it.
def len_hi(+n: Nat) -> U32:
  +d0 = Nat.div(n, 32n)
  +d1 = Nat.div(d0, 256n)
  +d2 = Nat.div(d1, 256n)
  +d3 = Nat.div(d2, 256n)
  +d4 = Nat.div(d3, 256n)
  +d5 = Nat.div(d4, 256n)
  +d6 = Nat.div(d5, 256n)
  pack(U32.from_nat(Nat.mod(d6, 256n)), U32.from_nat(Nat.mod(d5, 256n)),
    U32.from_nat(Nat.mod(d4, 256n)), U32.from_nat(Nat.mod(d3, 256n)))

def len_lo(+n: Nat) -> U32:
  +d0 = Nat.div(n, 32n)
  +d1 = Nat.div(d0, 256n)
  +d2 = Nat.div(d1, 256n)
  pack(U32.from_nat(Nat.mod(d2, 256n)), U32.from_nat(Nat.mod(d1, 256n)),
    U32.from_nat(Nat.mod(d0, 256n)), U32.shln(U32.from_nat(Nat.mod(n, 32n)), 3n))

# Final block(s) for an n-byte message ending in r = 0..63 tail bytes. Each
# tail length has its own padded layout: the tail bytes, the 0x80 marker, the
# zero fill and the big-endian bit length are packed straight into schedule
# words, so no padded list is built.
