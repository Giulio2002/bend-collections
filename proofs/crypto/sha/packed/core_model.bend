# Proof-only historical implementation model; not a production dependency.
import Base
import ../../../../src/crypto/sha/packed/core.bend as Runtime
import ../../../../src/crypto/sha/state.bend as S

def rotr(+x: U32, +n: Nat) -> U32:
  (U32.shrn(x, n) .|. U32.shln(x, Nat.sub(32n, n)) : U32)

def get(xs: List<&2, U32>, n: Nat) -> U32:
  match xs n:
    case Nil{} _:
      0
    case h <> t 0n:
      h
    case h <> t 1n+p:
      get(t, p)

# Reverse history: at round t, index j contains Runtime.W[t-1-j].
def next_word_slow(+history: List<&2, U32>) -> U32:
  (Runtime.small1(get(history, 1n)) + get(history, 6n)
    + Runtime.small0(get(history, 14n)) + get(history, 15n) : U32)

# Schedule histories always contain at least 16 words. Destructuring that prefix
# avoids four independent linked-list walks for every expanded word; the fallback
# preserves the total behavior used by the universal refinement theorem.
def next_word(+history: List<&2, U32>) -> U32:
  match history:
    case a <> b <> c <> d <> e <> f <> g <> h <> i <> j <> k <> l <> m <> n <> o <> (p <> rest):
      (Runtime.small1(b) + g + Runtime.small0(o) + p : U32)
    case _:
      next_word_slow(history)

def expand(n: Nat, +history: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      +w = next_word(history)
      w <> expand(p, w <> history)

def schedule(extra: Nat, +block: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, block,
    expand(extra, List.reverse(&2, U32, block)))

def rounds(ks: List<&2, U32>, ws: List<&2, U32>, s: S.State) -> S.State:
  match ks ws:
    case Nil{} _:
      s
    case k <> kt Nil{}:
      s
    case k <> kt w <> wt:
      rounds(kt, wt, Runtime.step(s, k, w))

# Compression consumes an already expanded 64-word schedule.
def compress(ws: List<&2, U32>, ks: List<&2, U32>, +s: S.State) -> S.State:
  Runtime.feedforward(s, rounds(ks, ws, s))

# Generate each derived schedule word immediately before its round. The reverse
# history is still retained for the recurrence, but the chronological 48-word
# extension is never materialized.
def expanded_rounds(n: Nat, +history: List<&2, U32>, ks: List<&2, U32>, s: S.State) -> S.State:
  match n ks:
    case 0n _:
      s
    case 1n+p Nil{}:
      s
    case 1n+p k <> kt:
      +w = next_word(history)
      expanded_rounds(p, w <> history, kt, Runtime.step(s, k, w))

# Consume the original block words, then continue directly with its expansion.
def schedule_rounds(ws: List<&2, U32>, +extra: Nat, +history: List<&2, U32>, ks: List<&2, U32>, s: S.State) -> S.State:
  match ws ks:
    case Nil{} _:
      expanded_rounds(extra, history, ks, s)
    case w <> wt Nil{}:
      s
    case w <> wt k <> kt:
      schedule_rounds(wt, extra, history, kt, Runtime.step(s, k, w))

# A fixed rolling window drops schedule words as soon as they are older than 16
# rounds. This avoids growing and reference-counting the reverse history list.
def window_rounds(n: Nat, win: Runtime.ShaWindow, ks: List<&2, U32>, s: S.State) -> S.State:
  match n win ks:
    case 0n _ _:
      s
    case 1n+q _ Nil{}:
      s
    case 1n+q Runtime.W{a, +b, c, d, e, f, +g, h, i, j, l, m, o, r, +t, +u} k <> kt:
      +w = (Runtime.small1(b) + g + Runtime.small0(t) + u : U32)
      window_rounds(q, Runtime.W{w, a, b, c, d, e, f, g, h, i, j, l, m, o, r, t}, kt,
        Runtime.step(s, k, w))

def window_schedule_rounds(ws: List<&2, U32>, +extra: Nat, win: Runtime.ShaWindow, ks: List<&2, U32>, s: S.State) -> S.State:
  match ws ks:
    case Nil{} _:
      window_rounds(extra, win, ks, s)
    case w <> wt Nil{}:
      s
    case w <> wt k <> kt:
      window_schedule_rounds(wt, extra, win, kt, Runtime.step(s, k, w))

def fused_compress_slow(+block: List<&2, U32>, +extra: Nat, +ks: List<&2, U32>, +s: S.State) -> S.State:
  Runtime.feedforward(s, schedule_rounds(block, extra, List.reverse(&2, U32, block), ks, s))

def fused_compress(+block: List<&2, U32>, +extra: Nat, +ks: List<&2, U32>, +s: S.State) -> S.State:
  match block:
    case a <> b <> c <> d <> e <> f <> g <> h <> i <> j <> k <> l <> m <> n <> o <> p <> Nil{}:
      Runtime.feedforward(s, window_schedule_rounds(
        [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p], extra,
        Runtime.W{p, o, n, m, l, k, j, i, h, g, f, e, d, c, b, a}, ks, s))
    case _:
      fused_compress_slow(block, extra, ks, s)

# Fast path for the 16-word blocks produced by block_bytes. It executes the
# seed rounds directly and constructs only the fixed rolling window.
def window_compress16(+a: U32, +b: U32, +c: U32, +d: U32,
  +e: U32, +f: U32, +g: U32, +h: U32,
  +i: U32, +j: U32, +k: U32, +l: U32,
  +m: U32, +n: U32, +o: U32, +p: U32,
  +extra: Nat, +ks: List<&2, U32>, +s: S.State) -> S.State:
  match ks:
    case k0 <> k1 <> k2 <> k3 <> k4 <> k5 <> k6 <> k7 <>
      k8 <> k9 <> k10 <> k11 <> k12 <> k13 <> k14 <> k15 <> kt:
      s1 = Runtime.step(s, k0, a)
      s2 = Runtime.step(s1, k1, b)
      s3 = Runtime.step(s2, k2, c)
      s4 = Runtime.step(s3, k3, d)
      s5 = Runtime.step(s4, k4, e)
      s6 = Runtime.step(s5, k5, f)
      s7 = Runtime.step(s6, k6, g)
      s8 = Runtime.step(s7, k7, h)
      s9 = Runtime.step(s8, k8, i)
      s10 = Runtime.step(s9, k9, j)
      s11 = Runtime.step(s10, k10, k)
      s12 = Runtime.step(s11, k11, l)
      s13 = Runtime.step(s12, k12, m)
      s14 = Runtime.step(s13, k13, n)
      s15 = Runtime.step(s14, k14, o)
      s16 = Runtime.step(s15, k15, p)
      Runtime.feedforward(s, window_rounds(extra,
        Runtime.W{p, o, n, m, l, k, j, i, h, g, f, e, d, c, b, a}, kt, s16))
    case _:
      fused_compress([a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p], extra, ks, s)

def be32(+x: U32) -> List<&2, U32>:
  [U32.shrn(x, 24n), (U32.shrn(x, 16n) .&. 255 : U32),
   (U32.shrn(x, 8n) .&. 255 : U32), (x .&. 255 : U32)]

def length_octets(count: Nat, +n: Nat, acc: List<&2, U32>) -> List<&2, U32>:
  match count:
    case 0n:
      acc
    case 1n+p:
      length_octets(p, Nat.div(n, 256n), U32.from_nat(Nat.mod(n, 256n)) <> acc)

def bit_length(+n: Nat) -> List<&2, U32>:
  length_octets(7n, Nat.div(n, 32n),
    [U32.shln(U32.from_nat(Nat.mod(n, 32n)), 3n)])

def digest(s: S.State) -> List<&2, U32>:
  S.H{a, b, c, d, e, f, g, h} = s
  [a, b, c, d, e, f, g, h]

# Generic block decoder over a padded byte list and any constant table. The
# fast path below is proved equal to it with the FIPS table.
def block_bytes(bytes: List<&2, U32>, +extra: Nat, +ks: List<&2, U32>, s: S.State) -> S.State:
  match bytes:
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> b59 <> b60 <> b61 <> b62 <> b63 <> rest:
      block_bytes(rest, extra, ks, window_compress16(
        Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15),
        Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31),
        Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, b38, b39), Runtime.pack(b40, b41, b42, b43), Runtime.pack(b44, b45, b46, b47),
        Runtime.pack(b48, b49, b50, b51), Runtime.pack(b52, b53, b54, b55), Runtime.pack(b56, b57, b58, b59), Runtime.pack(b60, b61, b62, b63),
        extra, ks, s))
    case _:
      s

# FIPS 180-4 round constants, the table the specialized rounds below inline.
def round_constants() -> List<&2, U32>:
  [1116352408, 1899447441, 3049323471, 3921009573,
   961987163, 1508970993, 2453635748, 2870763221,
   3624381080, 310598401, 607225278, 1426881987,
   1925078388, 2162078206, 2614888103, 3248222580,
   3835390401, 4022224774, 264347078, 604807628,
   770255983, 1249150122, 1555081692, 1996064986,
   2554220882, 2821834349, 2952996808, 3210313671,
   3336571891, 3584528711, 113926993, 338241895,
   666307205, 773529912, 1294757372, 1396182291,
   1695183700, 1986661051, 2177026350, 2456956037,
   2730485921, 2820302411, 3259730800, 3345764771,
   3516065817, 3600352804, 4094571909, 275423344,
   430227734, 506948616, 659060556, 883997877,
   958139571, 1322822218, 1537002063, 1747873779,
   1955562222, 2024104815, 2227730452, 2361852424,
   2428436474, 2756734187, 3204031479, 3329325298]

# SHA-256 round t (16 <= t < 64) with its constant as a literal. Like
# window_rounds, q bounds the remaining rounds (48 for SHA-256) and each round
# derives its schedule word from the rolling window before continuing with
# round t+1. Defined last-to-first because names must precede use.
def suffix(+n: Nat) -> List<&2, U32>:
  128 <> List.append(&2, U32,
    List.replicate(U32, Nat.mod(Nat.sub(119n, Nat.mod(n, 64n)), 64n), 0), bit_length(n))

# Big-endian words of the 64-bit message bit length 8n, computed from n with
# exactly the digit expressions bit_length produces, but without building and
# matching an eight-element list. bit_length(n) is [o(d6), .., o(d0), low]
# where d0 = n / 32, d(k+1) = dk / 256 and o(x) = x mod 256.
def fin0(+n: Nat, +extra: Nat, s: S.State) -> S.State:
  Runtime.fips_compress16(Runtime.pack(128, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(n), Runtime.len_lo(n),
    extra, s)

def fin1(+t0: U32, +n: Nat, +extra: Nat, s: S.State) -> S.State:
  Runtime.fips_compress16(Runtime.pack(t0, 128, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(n), Runtime.len_lo(n),
    extra, s)

def fin2(+t0: U32, +t1: U32, +n: Nat, +extra: Nat, s: S.State) -> S.State:
  Runtime.fips_compress16(Runtime.pack(t0, t1, 128, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(n), Runtime.len_lo(n),
    extra, s)

def fin3(+t0: U32, +t1: U32, +t2: U32, +n: Nat, +extra: Nat, s: S.State) -> S.State:
  Runtime.fips_compress16(Runtime.pack(t0, t1, t2, 128), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(n), Runtime.len_lo(n),
    extra, s)

def fin4(+t0: U32, +t1: U32, +t2: U32, +t3: U32, +n: Nat, +extra: Nat, s: S.State) -> S.State:
  Runtime.fips_compress16(Runtime.pack(t0, t1, t2, t3), Runtime.pack(128, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(n), Runtime.len_lo(n),
    extra, s)

def fin5(+t0: U32, +t1: U32, +t2: U32, +t3: U32, +t4: U32, +n: Nat, +extra: Nat, s: S.State) -> S.State:
  Runtime.fips_compress16(Runtime.pack(t0, t1, t2, t3), Runtime.pack(t4, 128, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(n), Runtime.len_lo(n),
    extra, s)

def fin6(+t0: U32, +t1: U32, +t2: U32, +t3: U32, +t4: U32, +t5: U32, +n: Nat, +extra: Nat, s: S.State) -> S.State:
  Runtime.fips_compress16(Runtime.pack(t0, t1, t2, t3), Runtime.pack(t4, t5, 128, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(n), Runtime.len_lo(n),
    extra, s)

def fin7(+t0: U32, +t1: U32, +t2: U32, +t3: U32, +t4: U32, +t5: U32, +t6: U32, +n: Nat, +extra: Nat, s: S.State) -> S.State:
  Runtime.fips_compress16(Runtime.pack(t0, t1, t2, t3), Runtime.pack(t4, t5, t6, 128), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(n), Runtime.len_lo(n),
    extra, s)

def fin8(+t0: U32, +t1: U32, +t2: U32, +t3: U32, +t4: U32, +t5: U32, +t6: U32, +t7: U32, +n: Nat, +extra: Nat, s: S.State) -> S.State:
  Runtime.fips_compress16(Runtime.pack(t0, t1, t2, t3), Runtime.pack(t4, t5, t6, t7), Runtime.pack(128, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(n), Runtime.len_lo(n),
    extra, s)

def fin9(+t0: U32, +t1: U32, +t2: U32, +t3: U32, +t4: U32, +t5: U32, +t6: U32, +t7: U32, +t8: U32, +n: Nat, +extra: Nat, s: S.State) -> S.State:
  Runtime.fips_compress16(Runtime.pack(t0, t1, t2, t3), Runtime.pack(t4, t5, t6, t7), Runtime.pack(t8, 128, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(n), Runtime.len_lo(n),
    extra, s)

def fin10(+t0: U32, +t1: U32, +t2: U32, +t3: U32, +t4: U32, +t5: U32, +t6: U32, +t7: U32, +t8: U32, +t9: U32, +n: Nat, +extra: Nat, s: S.State) -> S.State:
  Runtime.fips_compress16(Runtime.pack(t0, t1, t2, t3), Runtime.pack(t4, t5, t6, t7), Runtime.pack(t8, t9, 128, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(n), Runtime.len_lo(n),
    extra, s)

def fin11(+t0: U32, +t1: U32, +t2: U32, +t3: U32, +t4: U32, +t5: U32, +t6: U32, +t7: U32, +t8: U32, +t9: U32, +t10: U32, +n: Nat, +extra: Nat, s: S.State) -> S.State:
  Runtime.fips_compress16(Runtime.pack(t0, t1, t2, t3), Runtime.pack(t4, t5, t6, t7), Runtime.pack(t8, t9, t10, 128), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(n), Runtime.len_lo(n),
    extra, s)

def fin12(+t0: U32, +t1: U32, +t2: U32, +t3: U32, +t4: U32, +t5: U32, +t6: U32, +t7: U32, +t8: U32, +t9: U32, +t10: U32, +t11: U32, +n: Nat, +extra: Nat, s: S.State) -> S.State:
  Runtime.fips_compress16(Runtime.pack(t0, t1, t2, t3), Runtime.pack(t4, t5, t6, t7), Runtime.pack(t8, t9, t10, t11), Runtime.pack(128, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(n), Runtime.len_lo(n),
    extra, s)

def fin13(+t0: U32, +t1: U32, +t2: U32, +t3: U32, +t4: U32, +t5: U32, +t6: U32, +t7: U32, +t8: U32, +t9: U32, +t10: U32, +t11: U32, +t12: U32, +n: Nat, +extra: Nat, s: S.State) -> S.State:
  Runtime.fips_compress16(Runtime.pack(t0, t1, t2, t3), Runtime.pack(t4, t5, t6, t7), Runtime.pack(t8, t9, t10, t11), Runtime.pack(t12, 128, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(n), Runtime.len_lo(n),
    extra, s)

def fin14(+t0: U32, +t1: U32, +t2: U32, +t3: U32, +t4: U32, +t5: U32, +t6: U32, +t7: U32, +t8: U32, +t9: U32, +t10: U32, +t11: U32, +t12: U32, +t13: U32, +n: Nat, +extra: Nat, s: S.State) -> S.State:
  Runtime.fips_compress16(Runtime.pack(t0, t1, t2, t3), Runtime.pack(t4, t5, t6, t7), Runtime.pack(t8, t9, t10, t11), Runtime.pack(t12, t13, 128, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(n), Runtime.len_lo(n),
    extra, s)

def fin15(+t0: U32, +t1: U32, +t2: U32, +t3: U32, +t4: U32, +t5: U32, +t6: U32, +t7: U32, +t8: U32, +t9: U32, +t10: U32, +t11: U32, +t12: U32, +t13: U32, +t14: U32, +n: Nat, +extra: Nat, s: S.State) -> S.State:
  Runtime.fips_compress16(Runtime.pack(t0, t1, t2, t3), Runtime.pack(t4, t5, t6, t7), Runtime.pack(t8, t9, t10, t11), Runtime.pack(t12, t13, t14, 128), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(n), Runtime.len_lo(n),
    extra, s)

def fin16(+t0: U32, +t1: U32, +t2: U32, +t3: U32, +t4: U32, +t5: U32, +t6: U32, +t7: U32, +t8: U32, +t9: U32, +t10: U32, +t11: U32, +t12: U32, +t13: U32, +t14: U32, +t15: U32, +n: Nat, +extra: Nat, s: S.State) -> S.State:
  Runtime.fips_compress16(Runtime.pack(t0, t1, t2, t3), Runtime.pack(t4, t5, t6, t7), Runtime.pack(t8, t9, t10, t11), Runtime.pack(t12, t13, t14, t15), Runtime.pack(128, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(n), Runtime.len_lo(n),
    extra, s)

def fin17(+t0: U32, +t1: U32, +t2: U32, +t3: U32, +t4: U32, +t5: U32, +t6: U32, +t7: U32, +t8: U32, +t9: U32, +t10: U32, +t11: U32, +t12: U32, +t13: U32, +t14: U32, +t15: U32, +t16: U32, +n: Nat, +extra: Nat, s: S.State) -> S.State:
  Runtime.fips_compress16(Runtime.pack(t0, t1, t2, t3), Runtime.pack(t4, t5, t6, t7), Runtime.pack(t8, t9, t10, t11), Runtime.pack(t12, t13, t14, t15), Runtime.pack(t16, 128, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(n), Runtime.len_lo(n),
    extra, s)

def fin18(+t0: U32, +t1: U32, +t2: U32, +t3: U32, +t4: U32, +t5: U32, +t6: U32, +t7: U32, +t8: U32, +t9: U32, +t10: U32, +t11: U32, +t12: U32, +t13: U32, +t14: U32, +t15: U32, +t16: U32, +t17: U32, +n: Nat, +extra: Nat, s: S.State) -> S.State:
  Runtime.fips_compress16(Runtime.pack(t0, t1, t2, t3), Runtime.pack(t4, t5, t6, t7), Runtime.pack(t8, t9, t10, t11), Runtime.pack(t12, t13, t14, t15), Runtime.pack(t16, t17, 128, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(n), Runtime.len_lo(n),
    extra, s)

def fin19(+t0: U32, +t1: U32, +t2: U32, +t3: U32, +t4: U32, +t5: U32, +t6: U32, +t7: U32, +t8: U32, +t9: U32, +t10: U32, +t11: U32, +t12: U32, +t13: U32, +t14: U32, +t15: U32, +t16: U32, +t17: U32, +t18: U32, +n: Nat, +extra: Nat, s: S.State) -> S.State:
  Runtime.fips_compress16(Runtime.pack(t0, t1, t2, t3), Runtime.pack(t4, t5, t6, t7), Runtime.pack(t8, t9, t10, t11), Runtime.pack(t12, t13, t14, t15), Runtime.pack(t16, t17, t18, 128), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(n), Runtime.len_lo(n),
    extra, s)

def fin20(+t0: U32, +t1: U32, +t2: U32, +t3: U32, +t4: U32, +t5: U32, +t6: U32, +t7: U32, +t8: U32, +t9: U32, +t10: U32, +t11: U32, +t12: U32, +t13: U32, +t14: U32, +t15: U32, +t16: U32, +t17: U32, +t18: U32, +t19: U32, +n: Nat, +extra: Nat, s: S.State) -> S.State:
  Runtime.fips_compress16(Runtime.pack(t0, t1, t2, t3), Runtime.pack(t4, t5, t6, t7), Runtime.pack(t8, t9, t10, t11), Runtime.pack(t12, t13, t14, t15), Runtime.pack(t16, t17, t18, t19), Runtime.pack(128, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(n), Runtime.len_lo(n),
    extra, s)

def fin21(+t0: U32, +t1: U32, +t2: U32, +t3: U32, +t4: U32, +t5: U32, +t6: U32, +t7: U32, +t8: U32, +t9: U32, +t10: U32, +t11: U32, +t12: U32, +t13: U32, +t14: U32, +t15: U32, +t16: U32, +t17: U32, +t18: U32, +t19: U32, +t20: U32, +n: Nat, +extra: Nat, s: S.State) -> S.State:
  Runtime.fips_compress16(Runtime.pack(t0, t1, t2, t3), Runtime.pack(t4, t5, t6, t7), Runtime.pack(t8, t9, t10, t11), Runtime.pack(t12, t13, t14, t15), Runtime.pack(t16, t17, t18, t19), Runtime.pack(t20, 128, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(n), Runtime.len_lo(n),
    extra, s)

def fin22(+t0: U32, +t1: U32, +t2: U32, +t3: U32, +t4: U32, +t5: U32, +t6: U32, +t7: U32, +t8: U32, +t9: U32, +t10: U32, +t11: U32, +t12: U32, +t13: U32, +t14: U32, +t15: U32, +t16: U32, +t17: U32, +t18: U32, +t19: U32, +t20: U32, +t21: U32, +n: Nat, +extra: Nat, s: S.State) -> S.State:
  Runtime.fips_compress16(Runtime.pack(t0, t1, t2, t3), Runtime.pack(t4, t5, t6, t7), Runtime.pack(t8, t9, t10, t11), Runtime.pack(t12, t13, t14, t15), Runtime.pack(t16, t17, t18, t19), Runtime.pack(t20, t21, 128, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(n), Runtime.len_lo(n),
    extra, s)

def fin23(+t0: U32, +t1: U32, +t2: U32, +t3: U32, +t4: U32, +t5: U32, +t6: U32, +t7: U32, +t8: U32, +t9: U32, +t10: U32, +t11: U32, +t12: U32, +t13: U32, +t14: U32, +t15: U32, +t16: U32, +t17: U32, +t18: U32, +t19: U32, +t20: U32, +t21: U32, +t22: U32, +n: Nat, +extra: Nat, s: S.State) -> S.State:
  Runtime.fips_compress16(Runtime.pack(t0, t1, t2, t3), Runtime.pack(t4, t5, t6, t7), Runtime.pack(t8, t9, t10, t11), Runtime.pack(t12, t13, t14, t15), Runtime.pack(t16, t17, t18, t19), Runtime.pack(t20, t21, t22, 128), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(n), Runtime.len_lo(n),
    extra, s)

def fin24(+t0: U32, +t1: U32, +t2: U32, +t3: U32, +t4: U32, +t5: U32, +t6: U32, +t7: U32, +t8: U32, +t9: U32, +t10: U32, +t11: U32, +t12: U32, +t13: U32, +t14: U32, +t15: U32, +t16: U32, +t17: U32, +t18: U32, +t19: U32, +t20: U32, +t21: U32, +t22: U32, +t23: U32, +n: Nat, +extra: Nat, s: S.State) -> S.State:
  Runtime.fips_compress16(Runtime.pack(t0, t1, t2, t3), Runtime.pack(t4, t5, t6, t7), Runtime.pack(t8, t9, t10, t11), Runtime.pack(t12, t13, t14, t15), Runtime.pack(t16, t17, t18, t19), Runtime.pack(t20, t21, t22, t23), Runtime.pack(128, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(n), Runtime.len_lo(n),
    extra, s)

def fin25(+t0: U32, +t1: U32, +t2: U32, +t3: U32, +t4: U32, +t5: U32, +t6: U32, +t7: U32, +t8: U32, +t9: U32, +t10: U32, +t11: U32, +t12: U32, +t13: U32, +t14: U32, +t15: U32, +t16: U32, +t17: U32, +t18: U32, +t19: U32, +t20: U32, +t21: U32, +t22: U32, +t23: U32, +t24: U32, +n: Nat, +extra: Nat, s: S.State) -> S.State:
  Runtime.fips_compress16(Runtime.pack(t0, t1, t2, t3), Runtime.pack(t4, t5, t6, t7), Runtime.pack(t8, t9, t10, t11), Runtime.pack(t12, t13, t14, t15), Runtime.pack(t16, t17, t18, t19), Runtime.pack(t20, t21, t22, t23), Runtime.pack(t24, 128, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(n), Runtime.len_lo(n),
    extra, s)

def fin26(+t0: U32, +t1: U32, +t2: U32, +t3: U32, +t4: U32, +t5: U32, +t6: U32, +t7: U32, +t8: U32, +t9: U32, +t10: U32, +t11: U32, +t12: U32, +t13: U32, +t14: U32, +t15: U32, +t16: U32, +t17: U32, +t18: U32, +t19: U32, +t20: U32, +t21: U32, +t22: U32, +t23: U32, +t24: U32, +t25: U32, +n: Nat, +extra: Nat, s: S.State) -> S.State:
  Runtime.fips_compress16(Runtime.pack(t0, t1, t2, t3), Runtime.pack(t4, t5, t6, t7), Runtime.pack(t8, t9, t10, t11), Runtime.pack(t12, t13, t14, t15), Runtime.pack(t16, t17, t18, t19), Runtime.pack(t20, t21, t22, t23), Runtime.pack(t24, t25, 128, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(n), Runtime.len_lo(n),
    extra, s)

def fin27(+t0: U32, +t1: U32, +t2: U32, +t3: U32, +t4: U32, +t5: U32, +t6: U32, +t7: U32, +t8: U32, +t9: U32, +t10: U32, +t11: U32, +t12: U32, +t13: U32, +t14: U32, +t15: U32, +t16: U32, +t17: U32, +t18: U32, +t19: U32, +t20: U32, +t21: U32, +t22: U32, +t23: U32, +t24: U32, +t25: U32, +t26: U32, +n: Nat, +extra: Nat, s: S.State) -> S.State:
  Runtime.fips_compress16(Runtime.pack(t0, t1, t2, t3), Runtime.pack(t4, t5, t6, t7), Runtime.pack(t8, t9, t10, t11), Runtime.pack(t12, t13, t14, t15), Runtime.pack(t16, t17, t18, t19), Runtime.pack(t20, t21, t22, t23), Runtime.pack(t24, t25, t26, 128), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(n), Runtime.len_lo(n),
    extra, s)

def fin28(+t0: U32, +t1: U32, +t2: U32, +t3: U32, +t4: U32, +t5: U32, +t6: U32, +t7: U32, +t8: U32, +t9: U32, +t10: U32, +t11: U32, +t12: U32, +t13: U32, +t14: U32, +t15: U32, +t16: U32, +t17: U32, +t18: U32, +t19: U32, +t20: U32, +t21: U32, +t22: U32, +t23: U32, +t24: U32, +t25: U32, +t26: U32, +t27: U32, +n: Nat, +extra: Nat, s: S.State) -> S.State:
  Runtime.fips_compress16(Runtime.pack(t0, t1, t2, t3), Runtime.pack(t4, t5, t6, t7), Runtime.pack(t8, t9, t10, t11), Runtime.pack(t12, t13, t14, t15), Runtime.pack(t16, t17, t18, t19), Runtime.pack(t20, t21, t22, t23), Runtime.pack(t24, t25, t26, t27), Runtime.pack(128, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(n), Runtime.len_lo(n),
    extra, s)

def fin29(+t0: U32, +t1: U32, +t2: U32, +t3: U32, +t4: U32, +t5: U32, +t6: U32, +t7: U32, +t8: U32, +t9: U32, +t10: U32, +t11: U32, +t12: U32, +t13: U32, +t14: U32, +t15: U32, +t16: U32, +t17: U32, +t18: U32, +t19: U32, +t20: U32, +t21: U32, +t22: U32, +t23: U32, +t24: U32, +t25: U32, +t26: U32, +t27: U32, +t28: U32, +n: Nat, +extra: Nat, s: S.State) -> S.State:
  Runtime.fips_compress16(Runtime.pack(t0, t1, t2, t3), Runtime.pack(t4, t5, t6, t7), Runtime.pack(t8, t9, t10, t11), Runtime.pack(t12, t13, t14, t15), Runtime.pack(t16, t17, t18, t19), Runtime.pack(t20, t21, t22, t23), Runtime.pack(t24, t25, t26, t27), Runtime.pack(t28, 128, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(n), Runtime.len_lo(n),
    extra, s)

def fin30(+t0: U32, +t1: U32, +t2: U32, +t3: U32, +t4: U32, +t5: U32, +t6: U32, +t7: U32, +t8: U32, +t9: U32, +t10: U32, +t11: U32, +t12: U32, +t13: U32, +t14: U32, +t15: U32, +t16: U32, +t17: U32, +t18: U32, +t19: U32, +t20: U32, +t21: U32, +t22: U32, +t23: U32, +t24: U32, +t25: U32, +t26: U32, +t27: U32, +t28: U32, +t29: U32, +n: Nat, +extra: Nat, s: S.State) -> S.State:
  Runtime.fips_compress16(Runtime.pack(t0, t1, t2, t3), Runtime.pack(t4, t5, t6, t7), Runtime.pack(t8, t9, t10, t11), Runtime.pack(t12, t13, t14, t15), Runtime.pack(t16, t17, t18, t19), Runtime.pack(t20, t21, t22, t23), Runtime.pack(t24, t25, t26, t27), Runtime.pack(t28, t29, 128, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(n), Runtime.len_lo(n),
    extra, s)

def fin31(+t0: U32, +t1: U32, +t2: U32, +t3: U32, +t4: U32, +t5: U32, +t6: U32, +t7: U32, +t8: U32, +t9: U32, +t10: U32, +t11: U32, +t12: U32, +t13: U32, +t14: U32, +t15: U32, +t16: U32, +t17: U32, +t18: U32, +t19: U32, +t20: U32, +t21: U32, +t22: U32, +t23: U32, +t24: U32, +t25: U32, +t26: U32, +t27: U32, +t28: U32, +t29: U32, +t30: U32, +n: Nat, +extra: Nat, s: S.State) -> S.State:
  Runtime.fips_compress16(Runtime.pack(t0, t1, t2, t3), Runtime.pack(t4, t5, t6, t7), Runtime.pack(t8, t9, t10, t11), Runtime.pack(t12, t13, t14, t15), Runtime.pack(t16, t17, t18, t19), Runtime.pack(t20, t21, t22, t23), Runtime.pack(t24, t25, t26, t27), Runtime.pack(t28, t29, t30, 128), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(n), Runtime.len_lo(n),
    extra, s)

def fin32(+t0: U32, +t1: U32, +t2: U32, +t3: U32, +t4: U32, +t5: U32, +t6: U32, +t7: U32, +t8: U32, +t9: U32, +t10: U32, +t11: U32, +t12: U32, +t13: U32, +t14: U32, +t15: U32, +t16: U32, +t17: U32, +t18: U32, +t19: U32, +t20: U32, +t21: U32, +t22: U32, +t23: U32, +t24: U32, +t25: U32, +t26: U32, +t27: U32, +t28: U32, +t29: U32, +t30: U32, +t31: U32, +n: Nat, +extra: Nat, s: S.State) -> S.State:
  Runtime.fips_compress16(Runtime.pack(t0, t1, t2, t3), Runtime.pack(t4, t5, t6, t7), Runtime.pack(t8, t9, t10, t11), Runtime.pack(t12, t13, t14, t15), Runtime.pack(t16, t17, t18, t19), Runtime.pack(t20, t21, t22, t23), Runtime.pack(t24, t25, t26, t27), Runtime.pack(t28, t29, t30, t31), Runtime.pack(128, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(n), Runtime.len_lo(n),
    extra, s)

def fin33(+t0: U32, +t1: U32, +t2: U32, +t3: U32, +t4: U32, +t5: U32, +t6: U32, +t7: U32, +t8: U32, +t9: U32, +t10: U32, +t11: U32, +t12: U32, +t13: U32, +t14: U32, +t15: U32, +t16: U32, +t17: U32, +t18: U32, +t19: U32, +t20: U32, +t21: U32, +t22: U32, +t23: U32, +t24: U32, +t25: U32, +t26: U32, +t27: U32, +t28: U32, +t29: U32, +t30: U32, +t31: U32, +t32: U32, +n: Nat, +extra: Nat, s: S.State) -> S.State:
  Runtime.fips_compress16(Runtime.pack(t0, t1, t2, t3), Runtime.pack(t4, t5, t6, t7), Runtime.pack(t8, t9, t10, t11), Runtime.pack(t12, t13, t14, t15), Runtime.pack(t16, t17, t18, t19), Runtime.pack(t20, t21, t22, t23), Runtime.pack(t24, t25, t26, t27), Runtime.pack(t28, t29, t30, t31), Runtime.pack(t32, 128, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(n), Runtime.len_lo(n),
    extra, s)

def fin34(+t0: U32, +t1: U32, +t2: U32, +t3: U32, +t4: U32, +t5: U32, +t6: U32, +t7: U32, +t8: U32, +t9: U32, +t10: U32, +t11: U32, +t12: U32, +t13: U32, +t14: U32, +t15: U32, +t16: U32, +t17: U32, +t18: U32, +t19: U32, +t20: U32, +t21: U32, +t22: U32, +t23: U32, +t24: U32, +t25: U32, +t26: U32, +t27: U32, +t28: U32, +t29: U32, +t30: U32, +t31: U32, +t32: U32, +t33: U32, +n: Nat, +extra: Nat, s: S.State) -> S.State:
  Runtime.fips_compress16(Runtime.pack(t0, t1, t2, t3), Runtime.pack(t4, t5, t6, t7), Runtime.pack(t8, t9, t10, t11), Runtime.pack(t12, t13, t14, t15), Runtime.pack(t16, t17, t18, t19), Runtime.pack(t20, t21, t22, t23), Runtime.pack(t24, t25, t26, t27), Runtime.pack(t28, t29, t30, t31), Runtime.pack(t32, t33, 128, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(n), Runtime.len_lo(n),
    extra, s)

def fin35(+t0: U32, +t1: U32, +t2: U32, +t3: U32, +t4: U32, +t5: U32, +t6: U32, +t7: U32, +t8: U32, +t9: U32, +t10: U32, +t11: U32, +t12: U32, +t13: U32, +t14: U32, +t15: U32, +t16: U32, +t17: U32, +t18: U32, +t19: U32, +t20: U32, +t21: U32, +t22: U32, +t23: U32, +t24: U32, +t25: U32, +t26: U32, +t27: U32, +t28: U32, +t29: U32, +t30: U32, +t31: U32, +t32: U32, +t33: U32, +t34: U32, +n: Nat, +extra: Nat, s: S.State) -> S.State:
  Runtime.fips_compress16(Runtime.pack(t0, t1, t2, t3), Runtime.pack(t4, t5, t6, t7), Runtime.pack(t8, t9, t10, t11), Runtime.pack(t12, t13, t14, t15), Runtime.pack(t16, t17, t18, t19), Runtime.pack(t20, t21, t22, t23), Runtime.pack(t24, t25, t26, t27), Runtime.pack(t28, t29, t30, t31), Runtime.pack(t32, t33, t34, 128), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(n), Runtime.len_lo(n),
    extra, s)

def fin36(+t0: U32, +t1: U32, +t2: U32, +t3: U32, +t4: U32, +t5: U32, +t6: U32, +t7: U32, +t8: U32, +t9: U32, +t10: U32, +t11: U32, +t12: U32, +t13: U32, +t14: U32, +t15: U32, +t16: U32, +t17: U32, +t18: U32, +t19: U32, +t20: U32, +t21: U32, +t22: U32, +t23: U32, +t24: U32, +t25: U32, +t26: U32, +t27: U32, +t28: U32, +t29: U32, +t30: U32, +t31: U32, +t32: U32, +t33: U32, +t34: U32, +t35: U32, +n: Nat, +extra: Nat, s: S.State) -> S.State:
  Runtime.fips_compress16(Runtime.pack(t0, t1, t2, t3), Runtime.pack(t4, t5, t6, t7), Runtime.pack(t8, t9, t10, t11), Runtime.pack(t12, t13, t14, t15), Runtime.pack(t16, t17, t18, t19), Runtime.pack(t20, t21, t22, t23), Runtime.pack(t24, t25, t26, t27), Runtime.pack(t28, t29, t30, t31), Runtime.pack(t32, t33, t34, t35), Runtime.pack(128, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(n), Runtime.len_lo(n),
    extra, s)

def fin37(+t0: U32, +t1: U32, +t2: U32, +t3: U32, +t4: U32, +t5: U32, +t6: U32, +t7: U32, +t8: U32, +t9: U32, +t10: U32, +t11: U32, +t12: U32, +t13: U32, +t14: U32, +t15: U32, +t16: U32, +t17: U32, +t18: U32, +t19: U32, +t20: U32, +t21: U32, +t22: U32, +t23: U32, +t24: U32, +t25: U32, +t26: U32, +t27: U32, +t28: U32, +t29: U32, +t30: U32, +t31: U32, +t32: U32, +t33: U32, +t34: U32, +t35: U32, +t36: U32, +n: Nat, +extra: Nat, s: S.State) -> S.State:
  Runtime.fips_compress16(Runtime.pack(t0, t1, t2, t3), Runtime.pack(t4, t5, t6, t7), Runtime.pack(t8, t9, t10, t11), Runtime.pack(t12, t13, t14, t15), Runtime.pack(t16, t17, t18, t19), Runtime.pack(t20, t21, t22, t23), Runtime.pack(t24, t25, t26, t27), Runtime.pack(t28, t29, t30, t31), Runtime.pack(t32, t33, t34, t35), Runtime.pack(t36, 128, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(n), Runtime.len_lo(n),
    extra, s)

def fin38(+t0: U32, +t1: U32, +t2: U32, +t3: U32, +t4: U32, +t5: U32, +t6: U32, +t7: U32, +t8: U32, +t9: U32, +t10: U32, +t11: U32, +t12: U32, +t13: U32, +t14: U32, +t15: U32, +t16: U32, +t17: U32, +t18: U32, +t19: U32, +t20: U32, +t21: U32, +t22: U32, +t23: U32, +t24: U32, +t25: U32, +t26: U32, +t27: U32, +t28: U32, +t29: U32, +t30: U32, +t31: U32, +t32: U32, +t33: U32, +t34: U32, +t35: U32, +t36: U32, +t37: U32, +n: Nat, +extra: Nat, s: S.State) -> S.State:
  Runtime.fips_compress16(Runtime.pack(t0, t1, t2, t3), Runtime.pack(t4, t5, t6, t7), Runtime.pack(t8, t9, t10, t11), Runtime.pack(t12, t13, t14, t15), Runtime.pack(t16, t17, t18, t19), Runtime.pack(t20, t21, t22, t23), Runtime.pack(t24, t25, t26, t27), Runtime.pack(t28, t29, t30, t31), Runtime.pack(t32, t33, t34, t35), Runtime.pack(t36, t37, 128, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(n), Runtime.len_lo(n),
    extra, s)

def fin39(+t0: U32, +t1: U32, +t2: U32, +t3: U32, +t4: U32, +t5: U32, +t6: U32, +t7: U32, +t8: U32, +t9: U32, +t10: U32, +t11: U32, +t12: U32, +t13: U32, +t14: U32, +t15: U32, +t16: U32, +t17: U32, +t18: U32, +t19: U32, +t20: U32, +t21: U32, +t22: U32, +t23: U32, +t24: U32, +t25: U32, +t26: U32, +t27: U32, +t28: U32, +t29: U32, +t30: U32, +t31: U32, +t32: U32, +t33: U32, +t34: U32, +t35: U32, +t36: U32, +t37: U32, +t38: U32, +n: Nat, +extra: Nat, s: S.State) -> S.State:
  Runtime.fips_compress16(Runtime.pack(t0, t1, t2, t3), Runtime.pack(t4, t5, t6, t7), Runtime.pack(t8, t9, t10, t11), Runtime.pack(t12, t13, t14, t15), Runtime.pack(t16, t17, t18, t19), Runtime.pack(t20, t21, t22, t23), Runtime.pack(t24, t25, t26, t27), Runtime.pack(t28, t29, t30, t31), Runtime.pack(t32, t33, t34, t35), Runtime.pack(t36, t37, t38, 128), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(n), Runtime.len_lo(n),
    extra, s)

def fin40(+t0: U32, +t1: U32, +t2: U32, +t3: U32, +t4: U32, +t5: U32, +t6: U32, +t7: U32, +t8: U32, +t9: U32, +t10: U32, +t11: U32, +t12: U32, +t13: U32, +t14: U32, +t15: U32, +t16: U32, +t17: U32, +t18: U32, +t19: U32, +t20: U32, +t21: U32, +t22: U32, +t23: U32, +t24: U32, +t25: U32, +t26: U32, +t27: U32, +t28: U32, +t29: U32, +t30: U32, +t31: U32, +t32: U32, +t33: U32, +t34: U32, +t35: U32, +t36: U32, +t37: U32, +t38: U32, +t39: U32, +n: Nat, +extra: Nat, s: S.State) -> S.State:
  Runtime.fips_compress16(Runtime.pack(t0, t1, t2, t3), Runtime.pack(t4, t5, t6, t7), Runtime.pack(t8, t9, t10, t11), Runtime.pack(t12, t13, t14, t15), Runtime.pack(t16, t17, t18, t19), Runtime.pack(t20, t21, t22, t23), Runtime.pack(t24, t25, t26, t27), Runtime.pack(t28, t29, t30, t31), Runtime.pack(t32, t33, t34, t35), Runtime.pack(t36, t37, t38, t39), Runtime.pack(128, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(n), Runtime.len_lo(n),
    extra, s)

def fin41(+t0: U32, +t1: U32, +t2: U32, +t3: U32, +t4: U32, +t5: U32, +t6: U32, +t7: U32, +t8: U32, +t9: U32, +t10: U32, +t11: U32, +t12: U32, +t13: U32, +t14: U32, +t15: U32, +t16: U32, +t17: U32, +t18: U32, +t19: U32, +t20: U32, +t21: U32, +t22: U32, +t23: U32, +t24: U32, +t25: U32, +t26: U32, +t27: U32, +t28: U32, +t29: U32, +t30: U32, +t31: U32, +t32: U32, +t33: U32, +t34: U32, +t35: U32, +t36: U32, +t37: U32, +t38: U32, +t39: U32, +t40: U32, +n: Nat, +extra: Nat, s: S.State) -> S.State:
  Runtime.fips_compress16(Runtime.pack(t0, t1, t2, t3), Runtime.pack(t4, t5, t6, t7), Runtime.pack(t8, t9, t10, t11), Runtime.pack(t12, t13, t14, t15), Runtime.pack(t16, t17, t18, t19), Runtime.pack(t20, t21, t22, t23), Runtime.pack(t24, t25, t26, t27), Runtime.pack(t28, t29, t30, t31), Runtime.pack(t32, t33, t34, t35), Runtime.pack(t36, t37, t38, t39), Runtime.pack(t40, 128, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(n), Runtime.len_lo(n),
    extra, s)

def fin42(+t0: U32, +t1: U32, +t2: U32, +t3: U32, +t4: U32, +t5: U32, +t6: U32, +t7: U32, +t8: U32, +t9: U32, +t10: U32, +t11: U32, +t12: U32, +t13: U32, +t14: U32, +t15: U32, +t16: U32, +t17: U32, +t18: U32, +t19: U32, +t20: U32, +t21: U32, +t22: U32, +t23: U32, +t24: U32, +t25: U32, +t26: U32, +t27: U32, +t28: U32, +t29: U32, +t30: U32, +t31: U32, +t32: U32, +t33: U32, +t34: U32, +t35: U32, +t36: U32, +t37: U32, +t38: U32, +t39: U32, +t40: U32, +t41: U32, +n: Nat, +extra: Nat, s: S.State) -> S.State:
  Runtime.fips_compress16(Runtime.pack(t0, t1, t2, t3), Runtime.pack(t4, t5, t6, t7), Runtime.pack(t8, t9, t10, t11), Runtime.pack(t12, t13, t14, t15), Runtime.pack(t16, t17, t18, t19), Runtime.pack(t20, t21, t22, t23), Runtime.pack(t24, t25, t26, t27), Runtime.pack(t28, t29, t30, t31), Runtime.pack(t32, t33, t34, t35), Runtime.pack(t36, t37, t38, t39), Runtime.pack(t40, t41, 128, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(n), Runtime.len_lo(n),
    extra, s)

def fin43(+t0: U32, +t1: U32, +t2: U32, +t3: U32, +t4: U32, +t5: U32, +t6: U32, +t7: U32, +t8: U32, +t9: U32, +t10: U32, +t11: U32, +t12: U32, +t13: U32, +t14: U32, +t15: U32, +t16: U32, +t17: U32, +t18: U32, +t19: U32, +t20: U32, +t21: U32, +t22: U32, +t23: U32, +t24: U32, +t25: U32, +t26: U32, +t27: U32, +t28: U32, +t29: U32, +t30: U32, +t31: U32, +t32: U32, +t33: U32, +t34: U32, +t35: U32, +t36: U32, +t37: U32, +t38: U32, +t39: U32, +t40: U32, +t41: U32, +t42: U32, +n: Nat, +extra: Nat, s: S.State) -> S.State:
  Runtime.fips_compress16(Runtime.pack(t0, t1, t2, t3), Runtime.pack(t4, t5, t6, t7), Runtime.pack(t8, t9, t10, t11), Runtime.pack(t12, t13, t14, t15), Runtime.pack(t16, t17, t18, t19), Runtime.pack(t20, t21, t22, t23), Runtime.pack(t24, t25, t26, t27), Runtime.pack(t28, t29, t30, t31), Runtime.pack(t32, t33, t34, t35), Runtime.pack(t36, t37, t38, t39), Runtime.pack(t40, t41, t42, 128), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(n), Runtime.len_lo(n),
    extra, s)

def fin44(+t0: U32, +t1: U32, +t2: U32, +t3: U32, +t4: U32, +t5: U32, +t6: U32, +t7: U32, +t8: U32, +t9: U32, +t10: U32, +t11: U32, +t12: U32, +t13: U32, +t14: U32, +t15: U32, +t16: U32, +t17: U32, +t18: U32, +t19: U32, +t20: U32, +t21: U32, +t22: U32, +t23: U32, +t24: U32, +t25: U32, +t26: U32, +t27: U32, +t28: U32, +t29: U32, +t30: U32, +t31: U32, +t32: U32, +t33: U32, +t34: U32, +t35: U32, +t36: U32, +t37: U32, +t38: U32, +t39: U32, +t40: U32, +t41: U32, +t42: U32, +t43: U32, +n: Nat, +extra: Nat, s: S.State) -> S.State:
  Runtime.fips_compress16(Runtime.pack(t0, t1, t2, t3), Runtime.pack(t4, t5, t6, t7), Runtime.pack(t8, t9, t10, t11), Runtime.pack(t12, t13, t14, t15), Runtime.pack(t16, t17, t18, t19), Runtime.pack(t20, t21, t22, t23), Runtime.pack(t24, t25, t26, t27), Runtime.pack(t28, t29, t30, t31), Runtime.pack(t32, t33, t34, t35), Runtime.pack(t36, t37, t38, t39), Runtime.pack(t40, t41, t42, t43), Runtime.pack(128, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(n), Runtime.len_lo(n),
    extra, s)

def fin45(+t0: U32, +t1: U32, +t2: U32, +t3: U32, +t4: U32, +t5: U32, +t6: U32, +t7: U32, +t8: U32, +t9: U32, +t10: U32, +t11: U32, +t12: U32, +t13: U32, +t14: U32, +t15: U32, +t16: U32, +t17: U32, +t18: U32, +t19: U32, +t20: U32, +t21: U32, +t22: U32, +t23: U32, +t24: U32, +t25: U32, +t26: U32, +t27: U32, +t28: U32, +t29: U32, +t30: U32, +t31: U32, +t32: U32, +t33: U32, +t34: U32, +t35: U32, +t36: U32, +t37: U32, +t38: U32, +t39: U32, +t40: U32, +t41: U32, +t42: U32, +t43: U32, +t44: U32, +n: Nat, +extra: Nat, s: S.State) -> S.State:
  Runtime.fips_compress16(Runtime.pack(t0, t1, t2, t3), Runtime.pack(t4, t5, t6, t7), Runtime.pack(t8, t9, t10, t11), Runtime.pack(t12, t13, t14, t15), Runtime.pack(t16, t17, t18, t19), Runtime.pack(t20, t21, t22, t23), Runtime.pack(t24, t25, t26, t27), Runtime.pack(t28, t29, t30, t31), Runtime.pack(t32, t33, t34, t35), Runtime.pack(t36, t37, t38, t39), Runtime.pack(t40, t41, t42, t43), Runtime.pack(t44, 128, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(n), Runtime.len_lo(n),
    extra, s)

def fin46(+t0: U32, +t1: U32, +t2: U32, +t3: U32, +t4: U32, +t5: U32, +t6: U32, +t7: U32, +t8: U32, +t9: U32, +t10: U32, +t11: U32, +t12: U32, +t13: U32, +t14: U32, +t15: U32, +t16: U32, +t17: U32, +t18: U32, +t19: U32, +t20: U32, +t21: U32, +t22: U32, +t23: U32, +t24: U32, +t25: U32, +t26: U32, +t27: U32, +t28: U32, +t29: U32, +t30: U32, +t31: U32, +t32: U32, +t33: U32, +t34: U32, +t35: U32, +t36: U32, +t37: U32, +t38: U32, +t39: U32, +t40: U32, +t41: U32, +t42: U32, +t43: U32, +t44: U32, +t45: U32, +n: Nat, +extra: Nat, s: S.State) -> S.State:
  Runtime.fips_compress16(Runtime.pack(t0, t1, t2, t3), Runtime.pack(t4, t5, t6, t7), Runtime.pack(t8, t9, t10, t11), Runtime.pack(t12, t13, t14, t15), Runtime.pack(t16, t17, t18, t19), Runtime.pack(t20, t21, t22, t23), Runtime.pack(t24, t25, t26, t27), Runtime.pack(t28, t29, t30, t31), Runtime.pack(t32, t33, t34, t35), Runtime.pack(t36, t37, t38, t39), Runtime.pack(t40, t41, t42, t43), Runtime.pack(t44, t45, 128, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(n), Runtime.len_lo(n),
    extra, s)

def fin47(+t0: U32, +t1: U32, +t2: U32, +t3: U32, +t4: U32, +t5: U32, +t6: U32, +t7: U32, +t8: U32, +t9: U32, +t10: U32, +t11: U32, +t12: U32, +t13: U32, +t14: U32, +t15: U32, +t16: U32, +t17: U32, +t18: U32, +t19: U32, +t20: U32, +t21: U32, +t22: U32, +t23: U32, +t24: U32, +t25: U32, +t26: U32, +t27: U32, +t28: U32, +t29: U32, +t30: U32, +t31: U32, +t32: U32, +t33: U32, +t34: U32, +t35: U32, +t36: U32, +t37: U32, +t38: U32, +t39: U32, +t40: U32, +t41: U32, +t42: U32, +t43: U32, +t44: U32, +t45: U32, +t46: U32, +n: Nat, +extra: Nat, s: S.State) -> S.State:
  Runtime.fips_compress16(Runtime.pack(t0, t1, t2, t3), Runtime.pack(t4, t5, t6, t7), Runtime.pack(t8, t9, t10, t11), Runtime.pack(t12, t13, t14, t15), Runtime.pack(t16, t17, t18, t19), Runtime.pack(t20, t21, t22, t23), Runtime.pack(t24, t25, t26, t27), Runtime.pack(t28, t29, t30, t31), Runtime.pack(t32, t33, t34, t35), Runtime.pack(t36, t37, t38, t39), Runtime.pack(t40, t41, t42, t43), Runtime.pack(t44, t45, t46, 128), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(n), Runtime.len_lo(n),
    extra, s)

def fin48(+t0: U32, +t1: U32, +t2: U32, +t3: U32, +t4: U32, +t5: U32, +t6: U32, +t7: U32, +t8: U32, +t9: U32, +t10: U32, +t11: U32, +t12: U32, +t13: U32, +t14: U32, +t15: U32, +t16: U32, +t17: U32, +t18: U32, +t19: U32, +t20: U32, +t21: U32, +t22: U32, +t23: U32, +t24: U32, +t25: U32, +t26: U32, +t27: U32, +t28: U32, +t29: U32, +t30: U32, +t31: U32, +t32: U32, +t33: U32, +t34: U32, +t35: U32, +t36: U32, +t37: U32, +t38: U32, +t39: U32, +t40: U32, +t41: U32, +t42: U32, +t43: U32, +t44: U32, +t45: U32, +t46: U32, +t47: U32, +n: Nat, +extra: Nat, s: S.State) -> S.State:
  Runtime.fips_compress16(Runtime.pack(t0, t1, t2, t3), Runtime.pack(t4, t5, t6, t7), Runtime.pack(t8, t9, t10, t11), Runtime.pack(t12, t13, t14, t15), Runtime.pack(t16, t17, t18, t19), Runtime.pack(t20, t21, t22, t23), Runtime.pack(t24, t25, t26, t27), Runtime.pack(t28, t29, t30, t31), Runtime.pack(t32, t33, t34, t35), Runtime.pack(t36, t37, t38, t39), Runtime.pack(t40, t41, t42, t43), Runtime.pack(t44, t45, t46, t47), Runtime.pack(128, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(n), Runtime.len_lo(n),
    extra, s)

def fin49(+t0: U32, +t1: U32, +t2: U32, +t3: U32, +t4: U32, +t5: U32, +t6: U32, +t7: U32, +t8: U32, +t9: U32, +t10: U32, +t11: U32, +t12: U32, +t13: U32, +t14: U32, +t15: U32, +t16: U32, +t17: U32, +t18: U32, +t19: U32, +t20: U32, +t21: U32, +t22: U32, +t23: U32, +t24: U32, +t25: U32, +t26: U32, +t27: U32, +t28: U32, +t29: U32, +t30: U32, +t31: U32, +t32: U32, +t33: U32, +t34: U32, +t35: U32, +t36: U32, +t37: U32, +t38: U32, +t39: U32, +t40: U32, +t41: U32, +t42: U32, +t43: U32, +t44: U32, +t45: U32, +t46: U32, +t47: U32, +t48: U32, +n: Nat, +extra: Nat, s: S.State) -> S.State:
  Runtime.fips_compress16(Runtime.pack(t0, t1, t2, t3), Runtime.pack(t4, t5, t6, t7), Runtime.pack(t8, t9, t10, t11), Runtime.pack(t12, t13, t14, t15), Runtime.pack(t16, t17, t18, t19), Runtime.pack(t20, t21, t22, t23), Runtime.pack(t24, t25, t26, t27), Runtime.pack(t28, t29, t30, t31), Runtime.pack(t32, t33, t34, t35), Runtime.pack(t36, t37, t38, t39), Runtime.pack(t40, t41, t42, t43), Runtime.pack(t44, t45, t46, t47), Runtime.pack(t48, 128, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(n), Runtime.len_lo(n),
    extra, s)

def fin50(+t0: U32, +t1: U32, +t2: U32, +t3: U32, +t4: U32, +t5: U32, +t6: U32, +t7: U32, +t8: U32, +t9: U32, +t10: U32, +t11: U32, +t12: U32, +t13: U32, +t14: U32, +t15: U32, +t16: U32, +t17: U32, +t18: U32, +t19: U32, +t20: U32, +t21: U32, +t22: U32, +t23: U32, +t24: U32, +t25: U32, +t26: U32, +t27: U32, +t28: U32, +t29: U32, +t30: U32, +t31: U32, +t32: U32, +t33: U32, +t34: U32, +t35: U32, +t36: U32, +t37: U32, +t38: U32, +t39: U32, +t40: U32, +t41: U32, +t42: U32, +t43: U32, +t44: U32, +t45: U32, +t46: U32, +t47: U32, +t48: U32, +t49: U32, +n: Nat, +extra: Nat, s: S.State) -> S.State:
  Runtime.fips_compress16(Runtime.pack(t0, t1, t2, t3), Runtime.pack(t4, t5, t6, t7), Runtime.pack(t8, t9, t10, t11), Runtime.pack(t12, t13, t14, t15), Runtime.pack(t16, t17, t18, t19), Runtime.pack(t20, t21, t22, t23), Runtime.pack(t24, t25, t26, t27), Runtime.pack(t28, t29, t30, t31), Runtime.pack(t32, t33, t34, t35), Runtime.pack(t36, t37, t38, t39), Runtime.pack(t40, t41, t42, t43), Runtime.pack(t44, t45, t46, t47), Runtime.pack(t48, t49, 128, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(n), Runtime.len_lo(n),
    extra, s)

def fin51(+t0: U32, +t1: U32, +t2: U32, +t3: U32, +t4: U32, +t5: U32, +t6: U32, +t7: U32, +t8: U32, +t9: U32, +t10: U32, +t11: U32, +t12: U32, +t13: U32, +t14: U32, +t15: U32, +t16: U32, +t17: U32, +t18: U32, +t19: U32, +t20: U32, +t21: U32, +t22: U32, +t23: U32, +t24: U32, +t25: U32, +t26: U32, +t27: U32, +t28: U32, +t29: U32, +t30: U32, +t31: U32, +t32: U32, +t33: U32, +t34: U32, +t35: U32, +t36: U32, +t37: U32, +t38: U32, +t39: U32, +t40: U32, +t41: U32, +t42: U32, +t43: U32, +t44: U32, +t45: U32, +t46: U32, +t47: U32, +t48: U32, +t49: U32, +t50: U32, +n: Nat, +extra: Nat, s: S.State) -> S.State:
  Runtime.fips_compress16(Runtime.pack(t0, t1, t2, t3), Runtime.pack(t4, t5, t6, t7), Runtime.pack(t8, t9, t10, t11), Runtime.pack(t12, t13, t14, t15), Runtime.pack(t16, t17, t18, t19), Runtime.pack(t20, t21, t22, t23), Runtime.pack(t24, t25, t26, t27), Runtime.pack(t28, t29, t30, t31), Runtime.pack(t32, t33, t34, t35), Runtime.pack(t36, t37, t38, t39), Runtime.pack(t40, t41, t42, t43), Runtime.pack(t44, t45, t46, t47), Runtime.pack(t48, t49, t50, 128), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(n), Runtime.len_lo(n),
    extra, s)

def fin52(+t0: U32, +t1: U32, +t2: U32, +t3: U32, +t4: U32, +t5: U32, +t6: U32, +t7: U32, +t8: U32, +t9: U32, +t10: U32, +t11: U32, +t12: U32, +t13: U32, +t14: U32, +t15: U32, +t16: U32, +t17: U32, +t18: U32, +t19: U32, +t20: U32, +t21: U32, +t22: U32, +t23: U32, +t24: U32, +t25: U32, +t26: U32, +t27: U32, +t28: U32, +t29: U32, +t30: U32, +t31: U32, +t32: U32, +t33: U32, +t34: U32, +t35: U32, +t36: U32, +t37: U32, +t38: U32, +t39: U32, +t40: U32, +t41: U32, +t42: U32, +t43: U32, +t44: U32, +t45: U32, +t46: U32, +t47: U32, +t48: U32, +t49: U32, +t50: U32, +t51: U32, +n: Nat, +extra: Nat, s: S.State) -> S.State:
  Runtime.fips_compress16(Runtime.pack(t0, t1, t2, t3), Runtime.pack(t4, t5, t6, t7), Runtime.pack(t8, t9, t10, t11), Runtime.pack(t12, t13, t14, t15), Runtime.pack(t16, t17, t18, t19), Runtime.pack(t20, t21, t22, t23), Runtime.pack(t24, t25, t26, t27), Runtime.pack(t28, t29, t30, t31), Runtime.pack(t32, t33, t34, t35), Runtime.pack(t36, t37, t38, t39), Runtime.pack(t40, t41, t42, t43), Runtime.pack(t44, t45, t46, t47), Runtime.pack(t48, t49, t50, t51), Runtime.pack(128, 0, 0, 0), Runtime.len_hi(n), Runtime.len_lo(n),
    extra, s)

def fin53(+t0: U32, +t1: U32, +t2: U32, +t3: U32, +t4: U32, +t5: U32, +t6: U32, +t7: U32, +t8: U32, +t9: U32, +t10: U32, +t11: U32, +t12: U32, +t13: U32, +t14: U32, +t15: U32, +t16: U32, +t17: U32, +t18: U32, +t19: U32, +t20: U32, +t21: U32, +t22: U32, +t23: U32, +t24: U32, +t25: U32, +t26: U32, +t27: U32, +t28: U32, +t29: U32, +t30: U32, +t31: U32, +t32: U32, +t33: U32, +t34: U32, +t35: U32, +t36: U32, +t37: U32, +t38: U32, +t39: U32, +t40: U32, +t41: U32, +t42: U32, +t43: U32, +t44: U32, +t45: U32, +t46: U32, +t47: U32, +t48: U32, +t49: U32, +t50: U32, +t51: U32, +t52: U32, +n: Nat, +extra: Nat, s: S.State) -> S.State:
  Runtime.fips_compress16(Runtime.pack(t0, t1, t2, t3), Runtime.pack(t4, t5, t6, t7), Runtime.pack(t8, t9, t10, t11), Runtime.pack(t12, t13, t14, t15), Runtime.pack(t16, t17, t18, t19), Runtime.pack(t20, t21, t22, t23), Runtime.pack(t24, t25, t26, t27), Runtime.pack(t28, t29, t30, t31), Runtime.pack(t32, t33, t34, t35), Runtime.pack(t36, t37, t38, t39), Runtime.pack(t40, t41, t42, t43), Runtime.pack(t44, t45, t46, t47), Runtime.pack(t48, t49, t50, t51), Runtime.pack(t52, 128, 0, 0), Runtime.len_hi(n), Runtime.len_lo(n),
    extra, s)

def fin54(+t0: U32, +t1: U32, +t2: U32, +t3: U32, +t4: U32, +t5: U32, +t6: U32, +t7: U32, +t8: U32, +t9: U32, +t10: U32, +t11: U32, +t12: U32, +t13: U32, +t14: U32, +t15: U32, +t16: U32, +t17: U32, +t18: U32, +t19: U32, +t20: U32, +t21: U32, +t22: U32, +t23: U32, +t24: U32, +t25: U32, +t26: U32, +t27: U32, +t28: U32, +t29: U32, +t30: U32, +t31: U32, +t32: U32, +t33: U32, +t34: U32, +t35: U32, +t36: U32, +t37: U32, +t38: U32, +t39: U32, +t40: U32, +t41: U32, +t42: U32, +t43: U32, +t44: U32, +t45: U32, +t46: U32, +t47: U32, +t48: U32, +t49: U32, +t50: U32, +t51: U32, +t52: U32, +t53: U32, +n: Nat, +extra: Nat, s: S.State) -> S.State:
  Runtime.fips_compress16(Runtime.pack(t0, t1, t2, t3), Runtime.pack(t4, t5, t6, t7), Runtime.pack(t8, t9, t10, t11), Runtime.pack(t12, t13, t14, t15), Runtime.pack(t16, t17, t18, t19), Runtime.pack(t20, t21, t22, t23), Runtime.pack(t24, t25, t26, t27), Runtime.pack(t28, t29, t30, t31), Runtime.pack(t32, t33, t34, t35), Runtime.pack(t36, t37, t38, t39), Runtime.pack(t40, t41, t42, t43), Runtime.pack(t44, t45, t46, t47), Runtime.pack(t48, t49, t50, t51), Runtime.pack(t52, t53, 128, 0), Runtime.len_hi(n), Runtime.len_lo(n),
    extra, s)

def fin55(+t0: U32, +t1: U32, +t2: U32, +t3: U32, +t4: U32, +t5: U32, +t6: U32, +t7: U32, +t8: U32, +t9: U32, +t10: U32, +t11: U32, +t12: U32, +t13: U32, +t14: U32, +t15: U32, +t16: U32, +t17: U32, +t18: U32, +t19: U32, +t20: U32, +t21: U32, +t22: U32, +t23: U32, +t24: U32, +t25: U32, +t26: U32, +t27: U32, +t28: U32, +t29: U32, +t30: U32, +t31: U32, +t32: U32, +t33: U32, +t34: U32, +t35: U32, +t36: U32, +t37: U32, +t38: U32, +t39: U32, +t40: U32, +t41: U32, +t42: U32, +t43: U32, +t44: U32, +t45: U32, +t46: U32, +t47: U32, +t48: U32, +t49: U32, +t50: U32, +t51: U32, +t52: U32, +t53: U32, +t54: U32, +n: Nat, +extra: Nat, s: S.State) -> S.State:
  Runtime.fips_compress16(Runtime.pack(t0, t1, t2, t3), Runtime.pack(t4, t5, t6, t7), Runtime.pack(t8, t9, t10, t11), Runtime.pack(t12, t13, t14, t15), Runtime.pack(t16, t17, t18, t19), Runtime.pack(t20, t21, t22, t23), Runtime.pack(t24, t25, t26, t27), Runtime.pack(t28, t29, t30, t31), Runtime.pack(t32, t33, t34, t35), Runtime.pack(t36, t37, t38, t39), Runtime.pack(t40, t41, t42, t43), Runtime.pack(t44, t45, t46, t47), Runtime.pack(t48, t49, t50, t51), Runtime.pack(t52, t53, t54, 128), Runtime.len_hi(n), Runtime.len_lo(n),
    extra, s)

def fin56(+t0: U32, +t1: U32, +t2: U32, +t3: U32, +t4: U32, +t5: U32, +t6: U32, +t7: U32, +t8: U32, +t9: U32, +t10: U32, +t11: U32, +t12: U32, +t13: U32, +t14: U32, +t15: U32, +t16: U32, +t17: U32, +t18: U32, +t19: U32, +t20: U32, +t21: U32, +t22: U32, +t23: U32, +t24: U32, +t25: U32, +t26: U32, +t27: U32, +t28: U32, +t29: U32, +t30: U32, +t31: U32, +t32: U32, +t33: U32, +t34: U32, +t35: U32, +t36: U32, +t37: U32, +t38: U32, +t39: U32, +t40: U32, +t41: U32, +t42: U32, +t43: U32, +t44: U32, +t45: U32, +t46: U32, +t47: U32, +t48: U32, +t49: U32, +t50: U32, +t51: U32, +t52: U32, +t53: U32, +t54: U32, +t55: U32, +n: Nat, +extra: Nat, s: S.State) -> S.State:
  Runtime.fips_compress16(Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(n), Runtime.len_lo(n),
    extra, Runtime.fips_compress16(Runtime.pack(t0, t1, t2, t3), Runtime.pack(t4, t5, t6, t7), Runtime.pack(t8, t9, t10, t11), Runtime.pack(t12, t13, t14, t15), Runtime.pack(t16, t17, t18, t19), Runtime.pack(t20, t21, t22, t23), Runtime.pack(t24, t25, t26, t27), Runtime.pack(t28, t29, t30, t31), Runtime.pack(t32, t33, t34, t35), Runtime.pack(t36, t37, t38, t39), Runtime.pack(t40, t41, t42, t43), Runtime.pack(t44, t45, t46, t47), Runtime.pack(t48, t49, t50, t51), Runtime.pack(t52, t53, t54, t55), Runtime.pack(128, 0, 0, 0), Runtime.pack(0, 0, 0, 0),
    extra, s))

def fin57(+t0: U32, +t1: U32, +t2: U32, +t3: U32, +t4: U32, +t5: U32, +t6: U32, +t7: U32, +t8: U32, +t9: U32, +t10: U32, +t11: U32, +t12: U32, +t13: U32, +t14: U32, +t15: U32, +t16: U32, +t17: U32, +t18: U32, +t19: U32, +t20: U32, +t21: U32, +t22: U32, +t23: U32, +t24: U32, +t25: U32, +t26: U32, +t27: U32, +t28: U32, +t29: U32, +t30: U32, +t31: U32, +t32: U32, +t33: U32, +t34: U32, +t35: U32, +t36: U32, +t37: U32, +t38: U32, +t39: U32, +t40: U32, +t41: U32, +t42: U32, +t43: U32, +t44: U32, +t45: U32, +t46: U32, +t47: U32, +t48: U32, +t49: U32, +t50: U32, +t51: U32, +t52: U32, +t53: U32, +t54: U32, +t55: U32, +t56: U32, +n: Nat, +extra: Nat, s: S.State) -> S.State:
  Runtime.fips_compress16(Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(n), Runtime.len_lo(n),
    extra, Runtime.fips_compress16(Runtime.pack(t0, t1, t2, t3), Runtime.pack(t4, t5, t6, t7), Runtime.pack(t8, t9, t10, t11), Runtime.pack(t12, t13, t14, t15), Runtime.pack(t16, t17, t18, t19), Runtime.pack(t20, t21, t22, t23), Runtime.pack(t24, t25, t26, t27), Runtime.pack(t28, t29, t30, t31), Runtime.pack(t32, t33, t34, t35), Runtime.pack(t36, t37, t38, t39), Runtime.pack(t40, t41, t42, t43), Runtime.pack(t44, t45, t46, t47), Runtime.pack(t48, t49, t50, t51), Runtime.pack(t52, t53, t54, t55), Runtime.pack(t56, 128, 0, 0), Runtime.pack(0, 0, 0, 0),
    extra, s))

def fin58(+t0: U32, +t1: U32, +t2: U32, +t3: U32, +t4: U32, +t5: U32, +t6: U32, +t7: U32, +t8: U32, +t9: U32, +t10: U32, +t11: U32, +t12: U32, +t13: U32, +t14: U32, +t15: U32, +t16: U32, +t17: U32, +t18: U32, +t19: U32, +t20: U32, +t21: U32, +t22: U32, +t23: U32, +t24: U32, +t25: U32, +t26: U32, +t27: U32, +t28: U32, +t29: U32, +t30: U32, +t31: U32, +t32: U32, +t33: U32, +t34: U32, +t35: U32, +t36: U32, +t37: U32, +t38: U32, +t39: U32, +t40: U32, +t41: U32, +t42: U32, +t43: U32, +t44: U32, +t45: U32, +t46: U32, +t47: U32, +t48: U32, +t49: U32, +t50: U32, +t51: U32, +t52: U32, +t53: U32, +t54: U32, +t55: U32, +t56: U32, +t57: U32, +n: Nat, +extra: Nat, s: S.State) -> S.State:
  Runtime.fips_compress16(Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(n), Runtime.len_lo(n),
    extra, Runtime.fips_compress16(Runtime.pack(t0, t1, t2, t3), Runtime.pack(t4, t5, t6, t7), Runtime.pack(t8, t9, t10, t11), Runtime.pack(t12, t13, t14, t15), Runtime.pack(t16, t17, t18, t19), Runtime.pack(t20, t21, t22, t23), Runtime.pack(t24, t25, t26, t27), Runtime.pack(t28, t29, t30, t31), Runtime.pack(t32, t33, t34, t35), Runtime.pack(t36, t37, t38, t39), Runtime.pack(t40, t41, t42, t43), Runtime.pack(t44, t45, t46, t47), Runtime.pack(t48, t49, t50, t51), Runtime.pack(t52, t53, t54, t55), Runtime.pack(t56, t57, 128, 0), Runtime.pack(0, 0, 0, 0),
    extra, s))

def fin59(+t0: U32, +t1: U32, +t2: U32, +t3: U32, +t4: U32, +t5: U32, +t6: U32, +t7: U32, +t8: U32, +t9: U32, +t10: U32, +t11: U32, +t12: U32, +t13: U32, +t14: U32, +t15: U32, +t16: U32, +t17: U32, +t18: U32, +t19: U32, +t20: U32, +t21: U32, +t22: U32, +t23: U32, +t24: U32, +t25: U32, +t26: U32, +t27: U32, +t28: U32, +t29: U32, +t30: U32, +t31: U32, +t32: U32, +t33: U32, +t34: U32, +t35: U32, +t36: U32, +t37: U32, +t38: U32, +t39: U32, +t40: U32, +t41: U32, +t42: U32, +t43: U32, +t44: U32, +t45: U32, +t46: U32, +t47: U32, +t48: U32, +t49: U32, +t50: U32, +t51: U32, +t52: U32, +t53: U32, +t54: U32, +t55: U32, +t56: U32, +t57: U32, +t58: U32, +n: Nat, +extra: Nat, s: S.State) -> S.State:
  Runtime.fips_compress16(Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(n), Runtime.len_lo(n),
    extra, Runtime.fips_compress16(Runtime.pack(t0, t1, t2, t3), Runtime.pack(t4, t5, t6, t7), Runtime.pack(t8, t9, t10, t11), Runtime.pack(t12, t13, t14, t15), Runtime.pack(t16, t17, t18, t19), Runtime.pack(t20, t21, t22, t23), Runtime.pack(t24, t25, t26, t27), Runtime.pack(t28, t29, t30, t31), Runtime.pack(t32, t33, t34, t35), Runtime.pack(t36, t37, t38, t39), Runtime.pack(t40, t41, t42, t43), Runtime.pack(t44, t45, t46, t47), Runtime.pack(t48, t49, t50, t51), Runtime.pack(t52, t53, t54, t55), Runtime.pack(t56, t57, t58, 128), Runtime.pack(0, 0, 0, 0),
    extra, s))

def fin60(+t0: U32, +t1: U32, +t2: U32, +t3: U32, +t4: U32, +t5: U32, +t6: U32, +t7: U32, +t8: U32, +t9: U32, +t10: U32, +t11: U32, +t12: U32, +t13: U32, +t14: U32, +t15: U32, +t16: U32, +t17: U32, +t18: U32, +t19: U32, +t20: U32, +t21: U32, +t22: U32, +t23: U32, +t24: U32, +t25: U32, +t26: U32, +t27: U32, +t28: U32, +t29: U32, +t30: U32, +t31: U32, +t32: U32, +t33: U32, +t34: U32, +t35: U32, +t36: U32, +t37: U32, +t38: U32, +t39: U32, +t40: U32, +t41: U32, +t42: U32, +t43: U32, +t44: U32, +t45: U32, +t46: U32, +t47: U32, +t48: U32, +t49: U32, +t50: U32, +t51: U32, +t52: U32, +t53: U32, +t54: U32, +t55: U32, +t56: U32, +t57: U32, +t58: U32, +t59: U32, +n: Nat, +extra: Nat, s: S.State) -> S.State:
  Runtime.fips_compress16(Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(n), Runtime.len_lo(n),
    extra, Runtime.fips_compress16(Runtime.pack(t0, t1, t2, t3), Runtime.pack(t4, t5, t6, t7), Runtime.pack(t8, t9, t10, t11), Runtime.pack(t12, t13, t14, t15), Runtime.pack(t16, t17, t18, t19), Runtime.pack(t20, t21, t22, t23), Runtime.pack(t24, t25, t26, t27), Runtime.pack(t28, t29, t30, t31), Runtime.pack(t32, t33, t34, t35), Runtime.pack(t36, t37, t38, t39), Runtime.pack(t40, t41, t42, t43), Runtime.pack(t44, t45, t46, t47), Runtime.pack(t48, t49, t50, t51), Runtime.pack(t52, t53, t54, t55), Runtime.pack(t56, t57, t58, t59), Runtime.pack(128, 0, 0, 0),
    extra, s))

def fin61(+t0: U32, +t1: U32, +t2: U32, +t3: U32, +t4: U32, +t5: U32, +t6: U32, +t7: U32, +t8: U32, +t9: U32, +t10: U32, +t11: U32, +t12: U32, +t13: U32, +t14: U32, +t15: U32, +t16: U32, +t17: U32, +t18: U32, +t19: U32, +t20: U32, +t21: U32, +t22: U32, +t23: U32, +t24: U32, +t25: U32, +t26: U32, +t27: U32, +t28: U32, +t29: U32, +t30: U32, +t31: U32, +t32: U32, +t33: U32, +t34: U32, +t35: U32, +t36: U32, +t37: U32, +t38: U32, +t39: U32, +t40: U32, +t41: U32, +t42: U32, +t43: U32, +t44: U32, +t45: U32, +t46: U32, +t47: U32, +t48: U32, +t49: U32, +t50: U32, +t51: U32, +t52: U32, +t53: U32, +t54: U32, +t55: U32, +t56: U32, +t57: U32, +t58: U32, +t59: U32, +t60: U32, +n: Nat, +extra: Nat, s: S.State) -> S.State:
  Runtime.fips_compress16(Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(n), Runtime.len_lo(n),
    extra, Runtime.fips_compress16(Runtime.pack(t0, t1, t2, t3), Runtime.pack(t4, t5, t6, t7), Runtime.pack(t8, t9, t10, t11), Runtime.pack(t12, t13, t14, t15), Runtime.pack(t16, t17, t18, t19), Runtime.pack(t20, t21, t22, t23), Runtime.pack(t24, t25, t26, t27), Runtime.pack(t28, t29, t30, t31), Runtime.pack(t32, t33, t34, t35), Runtime.pack(t36, t37, t38, t39), Runtime.pack(t40, t41, t42, t43), Runtime.pack(t44, t45, t46, t47), Runtime.pack(t48, t49, t50, t51), Runtime.pack(t52, t53, t54, t55), Runtime.pack(t56, t57, t58, t59), Runtime.pack(t60, 128, 0, 0),
    extra, s))

def fin62(+t0: U32, +t1: U32, +t2: U32, +t3: U32, +t4: U32, +t5: U32, +t6: U32, +t7: U32, +t8: U32, +t9: U32, +t10: U32, +t11: U32, +t12: U32, +t13: U32, +t14: U32, +t15: U32, +t16: U32, +t17: U32, +t18: U32, +t19: U32, +t20: U32, +t21: U32, +t22: U32, +t23: U32, +t24: U32, +t25: U32, +t26: U32, +t27: U32, +t28: U32, +t29: U32, +t30: U32, +t31: U32, +t32: U32, +t33: U32, +t34: U32, +t35: U32, +t36: U32, +t37: U32, +t38: U32, +t39: U32, +t40: U32, +t41: U32, +t42: U32, +t43: U32, +t44: U32, +t45: U32, +t46: U32, +t47: U32, +t48: U32, +t49: U32, +t50: U32, +t51: U32, +t52: U32, +t53: U32, +t54: U32, +t55: U32, +t56: U32, +t57: U32, +t58: U32, +t59: U32, +t60: U32, +t61: U32, +n: Nat, +extra: Nat, s: S.State) -> S.State:
  Runtime.fips_compress16(Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(n), Runtime.len_lo(n),
    extra, Runtime.fips_compress16(Runtime.pack(t0, t1, t2, t3), Runtime.pack(t4, t5, t6, t7), Runtime.pack(t8, t9, t10, t11), Runtime.pack(t12, t13, t14, t15), Runtime.pack(t16, t17, t18, t19), Runtime.pack(t20, t21, t22, t23), Runtime.pack(t24, t25, t26, t27), Runtime.pack(t28, t29, t30, t31), Runtime.pack(t32, t33, t34, t35), Runtime.pack(t36, t37, t38, t39), Runtime.pack(t40, t41, t42, t43), Runtime.pack(t44, t45, t46, t47), Runtime.pack(t48, t49, t50, t51), Runtime.pack(t52, t53, t54, t55), Runtime.pack(t56, t57, t58, t59), Runtime.pack(t60, t61, 128, 0),
    extra, s))

def fin63(+t0: U32, +t1: U32, +t2: U32, +t3: U32, +t4: U32, +t5: U32, +t6: U32, +t7: U32, +t8: U32, +t9: U32, +t10: U32, +t11: U32, +t12: U32, +t13: U32, +t14: U32, +t15: U32, +t16: U32, +t17: U32, +t18: U32, +t19: U32, +t20: U32, +t21: U32, +t22: U32, +t23: U32, +t24: U32, +t25: U32, +t26: U32, +t27: U32, +t28: U32, +t29: U32, +t30: U32, +t31: U32, +t32: U32, +t33: U32, +t34: U32, +t35: U32, +t36: U32, +t37: U32, +t38: U32, +t39: U32, +t40: U32, +t41: U32, +t42: U32, +t43: U32, +t44: U32, +t45: U32, +t46: U32, +t47: U32, +t48: U32, +t49: U32, +t50: U32, +t51: U32, +t52: U32, +t53: U32, +t54: U32, +t55: U32, +t56: U32, +t57: U32, +t58: U32, +t59: U32, +t60: U32, +t61: U32, +t62: U32, +n: Nat, +extra: Nat, s: S.State) -> S.State:
  Runtime.fips_compress16(Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.pack(0, 0, 0, 0), Runtime.len_hi(n), Runtime.len_lo(n),
    extra, Runtime.fips_compress16(Runtime.pack(t0, t1, t2, t3), Runtime.pack(t4, t5, t6, t7), Runtime.pack(t8, t9, t10, t11), Runtime.pack(t12, t13, t14, t15), Runtime.pack(t16, t17, t18, t19), Runtime.pack(t20, t21, t22, t23), Runtime.pack(t24, t25, t26, t27), Runtime.pack(t28, t29, t30, t31), Runtime.pack(t32, t33, t34, t35), Runtime.pack(t36, t37, t38, t39), Runtime.pack(t40, t41, t42, t43), Runtime.pack(t44, t45, t46, t47), Runtime.pack(t48, t49, t50, t51), Runtime.pack(t52, t53, t54, t55), Runtime.pack(t56, t57, t58, t59), Runtime.pack(t60, t61, t62, 128),
    extra, s))

# Tail-recursive block loop over an already padded byte list.
def fips_blocks(bytes: List<&2, U32>, +extra: Nat, s: S.State) -> S.State:
  match bytes:
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> b59 <> b60 <> b61 <> b62 <> b63 <> rest:
      fips_blocks(rest, extra, Runtime.fips_compress16(Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15), Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31), Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, b38, b39), Runtime.pack(b40, b41, b42, b43), Runtime.pack(b44, b45, b46, b47), Runtime.pack(b48, b49, b50, b51), Runtime.pack(b52, b53, b54, b55), Runtime.pack(b56, b57, b58, b59), Runtime.pack(b60, b61, b62, b63), extra, s))
    case _:
      s

def zeros_onto(z: Nat, acc: List<&2, U32>) -> List<&2, U32>:
  match z:
    case 0n:
      acc
    case 1n+p:
      zeros_onto(p, 0 <> acc)

# The padding suffix built only with tail-recursive loops.
def padding(+n: Nat) -> List<&2, U32>:
  128 <> zeros_onto(Nat.mod(Nat.sub(119n, Nat.mod(n, 64n)), 64n), bit_length(n))

def byte_count(bytes: List<&2, U32>, acc: Nat) -> Nat:
  match bytes:
    case Nil{}:
      acc
    case h <> t:
      byte_count(t, 1n+acc)

# Final block(s) of an n-byte message whose tail has fewer than 64 bytes.
# stream never passes 64 or more bytes; that case pads with tail-recursive
# loops. The match is exhaustive: a default case would make Bend rebuild the
# consumed cells at every depth. Length words are computed directly from n; note
# that sharing any List<U32> would make Bend reference-count every list match,
# including the input loop in stream.
def finish_n(+tail: List<&2, U32>, +n: Nat, +extra: Nat, s: S.State) -> S.State:
  match tail:
    case Nil{}:
      fin0(n, extra, s)
    case t0 <> Nil{}:
      fin1(t0, n, extra, s)
    case t0 <> t1 <> Nil{}:
      fin2(t0, t1, n, extra, s)
    case t0 <> t1 <> t2 <> Nil{}:
      fin3(t0, t1, t2, n, extra, s)
    case t0 <> t1 <> t2 <> t3 <> Nil{}:
      fin4(t0, t1, t2, t3, n, extra, s)
    case t0 <> t1 <> t2 <> t3 <> t4 <> Nil{}:
      fin5(t0, t1, t2, t3, t4, n, extra, s)
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> Nil{}:
      fin6(t0, t1, t2, t3, t4, t5, n, extra, s)
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> Nil{}:
      fin7(t0, t1, t2, t3, t4, t5, t6, n, extra, s)
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> t7 <> Nil{}:
      fin8(t0, t1, t2, t3, t4, t5, t6, t7, n, extra, s)
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> t7 <> t8 <> Nil{}:
      fin9(t0, t1, t2, t3, t4, t5, t6, t7, t8, n, extra, s)
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> t7 <> t8 <> t9 <> Nil{}:
      fin10(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, n, extra, s)
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> t7 <> t8 <> t9 <> t10 <> Nil{}:
      fin11(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, n, extra, s)
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> t7 <> t8 <> t9 <> t10 <> t11 <> Nil{}:
      fin12(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, n, extra, s)
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> t7 <> t8 <> t9 <> t10 <> t11 <> t12 <> Nil{}:
      fin13(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, n, extra, s)
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> t7 <> t8 <> t9 <> t10 <> t11 <> t12 <> t13 <> Nil{}:
      fin14(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, n, extra, s)
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> t7 <> t8 <> t9 <> t10 <> t11 <> t12 <> t13 <> t14 <> Nil{}:
      fin15(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, n, extra, s)
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> t7 <> t8 <> t9 <> t10 <> t11 <> t12 <> t13 <> t14 <> t15 <> Nil{}:
      fin16(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, n, extra, s)
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> t7 <> t8 <> t9 <> t10 <> t11 <> t12 <> t13 <> t14 <> t15 <> t16 <> Nil{}:
      fin17(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, n, extra, s)
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> t7 <> t8 <> t9 <> t10 <> t11 <> t12 <> t13 <> t14 <> t15 <> t16 <> t17 <> Nil{}:
      fin18(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, n, extra, s)
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> t7 <> t8 <> t9 <> t10 <> t11 <> t12 <> t13 <> t14 <> t15 <> t16 <> t17 <> t18 <> Nil{}:
      fin19(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, n, extra, s)
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> t7 <> t8 <> t9 <> t10 <> t11 <> t12 <> t13 <> t14 <> t15 <> t16 <> t17 <> t18 <> t19 <> Nil{}:
      fin20(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, n, extra, s)
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> t7 <> t8 <> t9 <> t10 <> t11 <> t12 <> t13 <> t14 <> t15 <> t16 <> t17 <> t18 <> t19 <> t20 <> Nil{}:
      fin21(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, n, extra, s)
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> t7 <> t8 <> t9 <> t10 <> t11 <> t12 <> t13 <> t14 <> t15 <> t16 <> t17 <> t18 <> t19 <> t20 <> t21 <> Nil{}:
      fin22(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, n, extra, s)
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> t7 <> t8 <> t9 <> t10 <> t11 <> t12 <> t13 <> t14 <> t15 <> t16 <> t17 <> t18 <> t19 <> t20 <> t21 <> t22 <> Nil{}:
      fin23(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, n, extra, s)
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> t7 <> t8 <> t9 <> t10 <> t11 <> t12 <> t13 <> t14 <> t15 <> t16 <> t17 <> t18 <> t19 <> t20 <> t21 <> t22 <> t23 <> Nil{}:
      fin24(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, n, extra, s)
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> t7 <> t8 <> t9 <> t10 <> t11 <> t12 <> t13 <> t14 <> t15 <> t16 <> t17 <> t18 <> t19 <> t20 <> t21 <> t22 <> t23 <> t24 <> Nil{}:
      fin25(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, n, extra, s)
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> t7 <> t8 <> t9 <> t10 <> t11 <> t12 <> t13 <> t14 <> t15 <> t16 <> t17 <> t18 <> t19 <> t20 <> t21 <> t22 <> t23 <> t24 <> t25 <> Nil{}:
      fin26(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, n, extra, s)
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> t7 <> t8 <> t9 <> t10 <> t11 <> t12 <> t13 <> t14 <> t15 <> t16 <> t17 <> t18 <> t19 <> t20 <> t21 <> t22 <> t23 <> t24 <> t25 <> t26 <> Nil{}:
      fin27(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26, n, extra, s)
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> t7 <> t8 <> t9 <> t10 <> t11 <> t12 <> t13 <> t14 <> t15 <> t16 <> t17 <> t18 <> t19 <> t20 <> t21 <> t22 <> t23 <> t24 <> t25 <> t26 <> t27 <> Nil{}:
      fin28(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26, t27, n, extra, s)
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> t7 <> t8 <> t9 <> t10 <> t11 <> t12 <> t13 <> t14 <> t15 <> t16 <> t17 <> t18 <> t19 <> t20 <> t21 <> t22 <> t23 <> t24 <> t25 <> t26 <> t27 <> t28 <> Nil{}:
      fin29(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26, t27, t28, n, extra, s)
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> t7 <> t8 <> t9 <> t10 <> t11 <> t12 <> t13 <> t14 <> t15 <> t16 <> t17 <> t18 <> t19 <> t20 <> t21 <> t22 <> t23 <> t24 <> t25 <> t26 <> t27 <> t28 <> t29 <> Nil{}:
      fin30(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26, t27, t28, t29, n, extra, s)
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> t7 <> t8 <> t9 <> t10 <> t11 <> t12 <> t13 <> t14 <> t15 <> t16 <> t17 <> t18 <> t19 <> t20 <> t21 <> t22 <> t23 <> t24 <> t25 <> t26 <> t27 <> t28 <> t29 <> t30 <> Nil{}:
      fin31(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26, t27, t28, t29, t30, n, extra, s)
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> t7 <> t8 <> t9 <> t10 <> t11 <> t12 <> t13 <> t14 <> t15 <> t16 <> t17 <> t18 <> t19 <> t20 <> t21 <> t22 <> t23 <> t24 <> t25 <> t26 <> t27 <> t28 <> t29 <> t30 <> t31 <> Nil{}:
      fin32(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26, t27, t28, t29, t30, t31, n, extra, s)
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> t7 <> t8 <> t9 <> t10 <> t11 <> t12 <> t13 <> t14 <> t15 <> t16 <> t17 <> t18 <> t19 <> t20 <> t21 <> t22 <> t23 <> t24 <> t25 <> t26 <> t27 <> t28 <> t29 <> t30 <> t31 <> t32 <> Nil{}:
      fin33(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26, t27, t28, t29, t30, t31, t32, n, extra, s)
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> t7 <> t8 <> t9 <> t10 <> t11 <> t12 <> t13 <> t14 <> t15 <> t16 <> t17 <> t18 <> t19 <> t20 <> t21 <> t22 <> t23 <> t24 <> t25 <> t26 <> t27 <> t28 <> t29 <> t30 <> t31 <> t32 <> t33 <> Nil{}:
      fin34(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26, t27, t28, t29, t30, t31, t32, t33, n, extra, s)
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> t7 <> t8 <> t9 <> t10 <> t11 <> t12 <> t13 <> t14 <> t15 <> t16 <> t17 <> t18 <> t19 <> t20 <> t21 <> t22 <> t23 <> t24 <> t25 <> t26 <> t27 <> t28 <> t29 <> t30 <> t31 <> t32 <> t33 <> t34 <> Nil{}:
      fin35(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26, t27, t28, t29, t30, t31, t32, t33, t34, n, extra, s)
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> t7 <> t8 <> t9 <> t10 <> t11 <> t12 <> t13 <> t14 <> t15 <> t16 <> t17 <> t18 <> t19 <> t20 <> t21 <> t22 <> t23 <> t24 <> t25 <> t26 <> t27 <> t28 <> t29 <> t30 <> t31 <> t32 <> t33 <> t34 <> t35 <> Nil{}:
      fin36(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26, t27, t28, t29, t30, t31, t32, t33, t34, t35, n, extra, s)
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> t7 <> t8 <> t9 <> t10 <> t11 <> t12 <> t13 <> t14 <> t15 <> t16 <> t17 <> t18 <> t19 <> t20 <> t21 <> t22 <> t23 <> t24 <> t25 <> t26 <> t27 <> t28 <> t29 <> t30 <> t31 <> t32 <> t33 <> t34 <> t35 <> t36 <> Nil{}:
      fin37(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26, t27, t28, t29, t30, t31, t32, t33, t34, t35, t36, n, extra, s)
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> t7 <> t8 <> t9 <> t10 <> t11 <> t12 <> t13 <> t14 <> t15 <> t16 <> t17 <> t18 <> t19 <> t20 <> t21 <> t22 <> t23 <> t24 <> t25 <> t26 <> t27 <> t28 <> t29 <> t30 <> t31 <> t32 <> t33 <> t34 <> t35 <> t36 <> t37 <> Nil{}:
      fin38(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26, t27, t28, t29, t30, t31, t32, t33, t34, t35, t36, t37, n, extra, s)
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> t7 <> t8 <> t9 <> t10 <> t11 <> t12 <> t13 <> t14 <> t15 <> t16 <> t17 <> t18 <> t19 <> t20 <> t21 <> t22 <> t23 <> t24 <> t25 <> t26 <> t27 <> t28 <> t29 <> t30 <> t31 <> t32 <> t33 <> t34 <> t35 <> t36 <> t37 <> t38 <> Nil{}:
      fin39(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26, t27, t28, t29, t30, t31, t32, t33, t34, t35, t36, t37, t38, n, extra, s)
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> t7 <> t8 <> t9 <> t10 <> t11 <> t12 <> t13 <> t14 <> t15 <> t16 <> t17 <> t18 <> t19 <> t20 <> t21 <> t22 <> t23 <> t24 <> t25 <> t26 <> t27 <> t28 <> t29 <> t30 <> t31 <> t32 <> t33 <> t34 <> t35 <> t36 <> t37 <> t38 <> t39 <> Nil{}:
      fin40(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26, t27, t28, t29, t30, t31, t32, t33, t34, t35, t36, t37, t38, t39, n, extra, s)
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> t7 <> t8 <> t9 <> t10 <> t11 <> t12 <> t13 <> t14 <> t15 <> t16 <> t17 <> t18 <> t19 <> t20 <> t21 <> t22 <> t23 <> t24 <> t25 <> t26 <> t27 <> t28 <> t29 <> t30 <> t31 <> t32 <> t33 <> t34 <> t35 <> t36 <> t37 <> t38 <> t39 <> t40 <> Nil{}:
      fin41(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26, t27, t28, t29, t30, t31, t32, t33, t34, t35, t36, t37, t38, t39, t40, n, extra, s)
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> t7 <> t8 <> t9 <> t10 <> t11 <> t12 <> t13 <> t14 <> t15 <> t16 <> t17 <> t18 <> t19 <> t20 <> t21 <> t22 <> t23 <> t24 <> t25 <> t26 <> t27 <> t28 <> t29 <> t30 <> t31 <> t32 <> t33 <> t34 <> t35 <> t36 <> t37 <> t38 <> t39 <> t40 <> t41 <> Nil{}:
      fin42(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26, t27, t28, t29, t30, t31, t32, t33, t34, t35, t36, t37, t38, t39, t40, t41, n, extra, s)
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> t7 <> t8 <> t9 <> t10 <> t11 <> t12 <> t13 <> t14 <> t15 <> t16 <> t17 <> t18 <> t19 <> t20 <> t21 <> t22 <> t23 <> t24 <> t25 <> t26 <> t27 <> t28 <> t29 <> t30 <> t31 <> t32 <> t33 <> t34 <> t35 <> t36 <> t37 <> t38 <> t39 <> t40 <> t41 <> t42 <> Nil{}:
      fin43(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26, t27, t28, t29, t30, t31, t32, t33, t34, t35, t36, t37, t38, t39, t40, t41, t42, n, extra, s)
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> t7 <> t8 <> t9 <> t10 <> t11 <> t12 <> t13 <> t14 <> t15 <> t16 <> t17 <> t18 <> t19 <> t20 <> t21 <> t22 <> t23 <> t24 <> t25 <> t26 <> t27 <> t28 <> t29 <> t30 <> t31 <> t32 <> t33 <> t34 <> t35 <> t36 <> t37 <> t38 <> t39 <> t40 <> t41 <> t42 <> t43 <> Nil{}:
      fin44(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26, t27, t28, t29, t30, t31, t32, t33, t34, t35, t36, t37, t38, t39, t40, t41, t42, t43, n, extra, s)
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> t7 <> t8 <> t9 <> t10 <> t11 <> t12 <> t13 <> t14 <> t15 <> t16 <> t17 <> t18 <> t19 <> t20 <> t21 <> t22 <> t23 <> t24 <> t25 <> t26 <> t27 <> t28 <> t29 <> t30 <> t31 <> t32 <> t33 <> t34 <> t35 <> t36 <> t37 <> t38 <> t39 <> t40 <> t41 <> t42 <> t43 <> t44 <> Nil{}:
      fin45(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26, t27, t28, t29, t30, t31, t32, t33, t34, t35, t36, t37, t38, t39, t40, t41, t42, t43, t44, n, extra, s)
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> t7 <> t8 <> t9 <> t10 <> t11 <> t12 <> t13 <> t14 <> t15 <> t16 <> t17 <> t18 <> t19 <> t20 <> t21 <> t22 <> t23 <> t24 <> t25 <> t26 <> t27 <> t28 <> t29 <> t30 <> t31 <> t32 <> t33 <> t34 <> t35 <> t36 <> t37 <> t38 <> t39 <> t40 <> t41 <> t42 <> t43 <> t44 <> t45 <> Nil{}:
      fin46(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26, t27, t28, t29, t30, t31, t32, t33, t34, t35, t36, t37, t38, t39, t40, t41, t42, t43, t44, t45, n, extra, s)
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> t7 <> t8 <> t9 <> t10 <> t11 <> t12 <> t13 <> t14 <> t15 <> t16 <> t17 <> t18 <> t19 <> t20 <> t21 <> t22 <> t23 <> t24 <> t25 <> t26 <> t27 <> t28 <> t29 <> t30 <> t31 <> t32 <> t33 <> t34 <> t35 <> t36 <> t37 <> t38 <> t39 <> t40 <> t41 <> t42 <> t43 <> t44 <> t45 <> t46 <> Nil{}:
      fin47(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26, t27, t28, t29, t30, t31, t32, t33, t34, t35, t36, t37, t38, t39, t40, t41, t42, t43, t44, t45, t46, n, extra, s)
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> t7 <> t8 <> t9 <> t10 <> t11 <> t12 <> t13 <> t14 <> t15 <> t16 <> t17 <> t18 <> t19 <> t20 <> t21 <> t22 <> t23 <> t24 <> t25 <> t26 <> t27 <> t28 <> t29 <> t30 <> t31 <> t32 <> t33 <> t34 <> t35 <> t36 <> t37 <> t38 <> t39 <> t40 <> t41 <> t42 <> t43 <> t44 <> t45 <> t46 <> t47 <> Nil{}:
      fin48(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26, t27, t28, t29, t30, t31, t32, t33, t34, t35, t36, t37, t38, t39, t40, t41, t42, t43, t44, t45, t46, t47, n, extra, s)
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> t7 <> t8 <> t9 <> t10 <> t11 <> t12 <> t13 <> t14 <> t15 <> t16 <> t17 <> t18 <> t19 <> t20 <> t21 <> t22 <> t23 <> t24 <> t25 <> t26 <> t27 <> t28 <> t29 <> t30 <> t31 <> t32 <> t33 <> t34 <> t35 <> t36 <> t37 <> t38 <> t39 <> t40 <> t41 <> t42 <> t43 <> t44 <> t45 <> t46 <> t47 <> t48 <> Nil{}:
      fin49(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26, t27, t28, t29, t30, t31, t32, t33, t34, t35, t36, t37, t38, t39, t40, t41, t42, t43, t44, t45, t46, t47, t48, n, extra, s)
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> t7 <> t8 <> t9 <> t10 <> t11 <> t12 <> t13 <> t14 <> t15 <> t16 <> t17 <> t18 <> t19 <> t20 <> t21 <> t22 <> t23 <> t24 <> t25 <> t26 <> t27 <> t28 <> t29 <> t30 <> t31 <> t32 <> t33 <> t34 <> t35 <> t36 <> t37 <> t38 <> t39 <> t40 <> t41 <> t42 <> t43 <> t44 <> t45 <> t46 <> t47 <> t48 <> t49 <> Nil{}:
      fin50(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26, t27, t28, t29, t30, t31, t32, t33, t34, t35, t36, t37, t38, t39, t40, t41, t42, t43, t44, t45, t46, t47, t48, t49, n, extra, s)
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> t7 <> t8 <> t9 <> t10 <> t11 <> t12 <> t13 <> t14 <> t15 <> t16 <> t17 <> t18 <> t19 <> t20 <> t21 <> t22 <> t23 <> t24 <> t25 <> t26 <> t27 <> t28 <> t29 <> t30 <> t31 <> t32 <> t33 <> t34 <> t35 <> t36 <> t37 <> t38 <> t39 <> t40 <> t41 <> t42 <> t43 <> t44 <> t45 <> t46 <> t47 <> t48 <> t49 <> t50 <> Nil{}:
      fin51(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26, t27, t28, t29, t30, t31, t32, t33, t34, t35, t36, t37, t38, t39, t40, t41, t42, t43, t44, t45, t46, t47, t48, t49, t50, n, extra, s)
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> t7 <> t8 <> t9 <> t10 <> t11 <> t12 <> t13 <> t14 <> t15 <> t16 <> t17 <> t18 <> t19 <> t20 <> t21 <> t22 <> t23 <> t24 <> t25 <> t26 <> t27 <> t28 <> t29 <> t30 <> t31 <> t32 <> t33 <> t34 <> t35 <> t36 <> t37 <> t38 <> t39 <> t40 <> t41 <> t42 <> t43 <> t44 <> t45 <> t46 <> t47 <> t48 <> t49 <> t50 <> t51 <> Nil{}:
      fin52(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26, t27, t28, t29, t30, t31, t32, t33, t34, t35, t36, t37, t38, t39, t40, t41, t42, t43, t44, t45, t46, t47, t48, t49, t50, t51, n, extra, s)
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> t7 <> t8 <> t9 <> t10 <> t11 <> t12 <> t13 <> t14 <> t15 <> t16 <> t17 <> t18 <> t19 <> t20 <> t21 <> t22 <> t23 <> t24 <> t25 <> t26 <> t27 <> t28 <> t29 <> t30 <> t31 <> t32 <> t33 <> t34 <> t35 <> t36 <> t37 <> t38 <> t39 <> t40 <> t41 <> t42 <> t43 <> t44 <> t45 <> t46 <> t47 <> t48 <> t49 <> t50 <> t51 <> t52 <> Nil{}:
      fin53(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26, t27, t28, t29, t30, t31, t32, t33, t34, t35, t36, t37, t38, t39, t40, t41, t42, t43, t44, t45, t46, t47, t48, t49, t50, t51, t52, n, extra, s)
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> t7 <> t8 <> t9 <> t10 <> t11 <> t12 <> t13 <> t14 <> t15 <> t16 <> t17 <> t18 <> t19 <> t20 <> t21 <> t22 <> t23 <> t24 <> t25 <> t26 <> t27 <> t28 <> t29 <> t30 <> t31 <> t32 <> t33 <> t34 <> t35 <> t36 <> t37 <> t38 <> t39 <> t40 <> t41 <> t42 <> t43 <> t44 <> t45 <> t46 <> t47 <> t48 <> t49 <> t50 <> t51 <> t52 <> t53 <> Nil{}:
      fin54(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26, t27, t28, t29, t30, t31, t32, t33, t34, t35, t36, t37, t38, t39, t40, t41, t42, t43, t44, t45, t46, t47, t48, t49, t50, t51, t52, t53, n, extra, s)
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> t7 <> t8 <> t9 <> t10 <> t11 <> t12 <> t13 <> t14 <> t15 <> t16 <> t17 <> t18 <> t19 <> t20 <> t21 <> t22 <> t23 <> t24 <> t25 <> t26 <> t27 <> t28 <> t29 <> t30 <> t31 <> t32 <> t33 <> t34 <> t35 <> t36 <> t37 <> t38 <> t39 <> t40 <> t41 <> t42 <> t43 <> t44 <> t45 <> t46 <> t47 <> t48 <> t49 <> t50 <> t51 <> t52 <> t53 <> t54 <> Nil{}:
      fin55(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26, t27, t28, t29, t30, t31, t32, t33, t34, t35, t36, t37, t38, t39, t40, t41, t42, t43, t44, t45, t46, t47, t48, t49, t50, t51, t52, t53, t54, n, extra, s)
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> t7 <> t8 <> t9 <> t10 <> t11 <> t12 <> t13 <> t14 <> t15 <> t16 <> t17 <> t18 <> t19 <> t20 <> t21 <> t22 <> t23 <> t24 <> t25 <> t26 <> t27 <> t28 <> t29 <> t30 <> t31 <> t32 <> t33 <> t34 <> t35 <> t36 <> t37 <> t38 <> t39 <> t40 <> t41 <> t42 <> t43 <> t44 <> t45 <> t46 <> t47 <> t48 <> t49 <> t50 <> t51 <> t52 <> t53 <> t54 <> t55 <> Nil{}:
      fin56(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26, t27, t28, t29, t30, t31, t32, t33, t34, t35, t36, t37, t38, t39, t40, t41, t42, t43, t44, t45, t46, t47, t48, t49, t50, t51, t52, t53, t54, t55, n, extra, s)
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> t7 <> t8 <> t9 <> t10 <> t11 <> t12 <> t13 <> t14 <> t15 <> t16 <> t17 <> t18 <> t19 <> t20 <> t21 <> t22 <> t23 <> t24 <> t25 <> t26 <> t27 <> t28 <> t29 <> t30 <> t31 <> t32 <> t33 <> t34 <> t35 <> t36 <> t37 <> t38 <> t39 <> t40 <> t41 <> t42 <> t43 <> t44 <> t45 <> t46 <> t47 <> t48 <> t49 <> t50 <> t51 <> t52 <> t53 <> t54 <> t55 <> t56 <> Nil{}:
      fin57(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26, t27, t28, t29, t30, t31, t32, t33, t34, t35, t36, t37, t38, t39, t40, t41, t42, t43, t44, t45, t46, t47, t48, t49, t50, t51, t52, t53, t54, t55, t56, n, extra, s)
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> t7 <> t8 <> t9 <> t10 <> t11 <> t12 <> t13 <> t14 <> t15 <> t16 <> t17 <> t18 <> t19 <> t20 <> t21 <> t22 <> t23 <> t24 <> t25 <> t26 <> t27 <> t28 <> t29 <> t30 <> t31 <> t32 <> t33 <> t34 <> t35 <> t36 <> t37 <> t38 <> t39 <> t40 <> t41 <> t42 <> t43 <> t44 <> t45 <> t46 <> t47 <> t48 <> t49 <> t50 <> t51 <> t52 <> t53 <> t54 <> t55 <> t56 <> t57 <> Nil{}:
      fin58(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26, t27, t28, t29, t30, t31, t32, t33, t34, t35, t36, t37, t38, t39, t40, t41, t42, t43, t44, t45, t46, t47, t48, t49, t50, t51, t52, t53, t54, t55, t56, t57, n, extra, s)
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> t7 <> t8 <> t9 <> t10 <> t11 <> t12 <> t13 <> t14 <> t15 <> t16 <> t17 <> t18 <> t19 <> t20 <> t21 <> t22 <> t23 <> t24 <> t25 <> t26 <> t27 <> t28 <> t29 <> t30 <> t31 <> t32 <> t33 <> t34 <> t35 <> t36 <> t37 <> t38 <> t39 <> t40 <> t41 <> t42 <> t43 <> t44 <> t45 <> t46 <> t47 <> t48 <> t49 <> t50 <> t51 <> t52 <> t53 <> t54 <> t55 <> t56 <> t57 <> t58 <> Nil{}:
      fin59(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26, t27, t28, t29, t30, t31, t32, t33, t34, t35, t36, t37, t38, t39, t40, t41, t42, t43, t44, t45, t46, t47, t48, t49, t50, t51, t52, t53, t54, t55, t56, t57, t58, n, extra, s)
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> t7 <> t8 <> t9 <> t10 <> t11 <> t12 <> t13 <> t14 <> t15 <> t16 <> t17 <> t18 <> t19 <> t20 <> t21 <> t22 <> t23 <> t24 <> t25 <> t26 <> t27 <> t28 <> t29 <> t30 <> t31 <> t32 <> t33 <> t34 <> t35 <> t36 <> t37 <> t38 <> t39 <> t40 <> t41 <> t42 <> t43 <> t44 <> t45 <> t46 <> t47 <> t48 <> t49 <> t50 <> t51 <> t52 <> t53 <> t54 <> t55 <> t56 <> t57 <> t58 <> t59 <> Nil{}:
      fin60(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26, t27, t28, t29, t30, t31, t32, t33, t34, t35, t36, t37, t38, t39, t40, t41, t42, t43, t44, t45, t46, t47, t48, t49, t50, t51, t52, t53, t54, t55, t56, t57, t58, t59, n, extra, s)
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> t7 <> t8 <> t9 <> t10 <> t11 <> t12 <> t13 <> t14 <> t15 <> t16 <> t17 <> t18 <> t19 <> t20 <> t21 <> t22 <> t23 <> t24 <> t25 <> t26 <> t27 <> t28 <> t29 <> t30 <> t31 <> t32 <> t33 <> t34 <> t35 <> t36 <> t37 <> t38 <> t39 <> t40 <> t41 <> t42 <> t43 <> t44 <> t45 <> t46 <> t47 <> t48 <> t49 <> t50 <> t51 <> t52 <> t53 <> t54 <> t55 <> t56 <> t57 <> t58 <> t59 <> t60 <> Nil{}:
      fin61(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26, t27, t28, t29, t30, t31, t32, t33, t34, t35, t36, t37, t38, t39, t40, t41, t42, t43, t44, t45, t46, t47, t48, t49, t50, t51, t52, t53, t54, t55, t56, t57, t58, t59, t60, n, extra, s)
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> t7 <> t8 <> t9 <> t10 <> t11 <> t12 <> t13 <> t14 <> t15 <> t16 <> t17 <> t18 <> t19 <> t20 <> t21 <> t22 <> t23 <> t24 <> t25 <> t26 <> t27 <> t28 <> t29 <> t30 <> t31 <> t32 <> t33 <> t34 <> t35 <> t36 <> t37 <> t38 <> t39 <> t40 <> t41 <> t42 <> t43 <> t44 <> t45 <> t46 <> t47 <> t48 <> t49 <> t50 <> t51 <> t52 <> t53 <> t54 <> t55 <> t56 <> t57 <> t58 <> t59 <> t60 <> t61 <> Nil{}:
      fin62(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26, t27, t28, t29, t30, t31, t32, t33, t34, t35, t36, t37, t38, t39, t40, t41, t42, t43, t44, t45, t46, t47, t48, t49, t50, t51, t52, t53, t54, t55, t56, t57, t58, t59, t60, t61, n, extra, s)
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> t7 <> t8 <> t9 <> t10 <> t11 <> t12 <> t13 <> t14 <> t15 <> t16 <> t17 <> t18 <> t19 <> t20 <> t21 <> t22 <> t23 <> t24 <> t25 <> t26 <> t27 <> t28 <> t29 <> t30 <> t31 <> t32 <> t33 <> t34 <> t35 <> t36 <> t37 <> t38 <> t39 <> t40 <> t41 <> t42 <> t43 <> t44 <> t45 <> t46 <> t47 <> t48 <> t49 <> t50 <> t51 <> t52 <> t53 <> t54 <> t55 <> t56 <> t57 <> t58 <> t59 <> t60 <> t61 <> t62 <> Nil{}:
      fin63(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26, t27, t28, t29, t30, t31, t32, t33, t34, t35, t36, t37, t38, t39, t40, t41, t42, t43, t44, t45, t46, t47, t48, t49, t50, t51, t52, t53, t54, t55, t56, t57, t58, t59, t60, t61, t62, n, extra, s)
    case t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> t7 <> t8 <> t9 <> t10 <> t11 <> t12 <> t13 <> t14 <> t15 <> t16 <> t17 <> t18 <> t19 <> t20 <> t21 <> t22 <> t23 <> t24 <> t25 <> t26 <> t27 <> t28 <> t29 <> t30 <> t31 <> t32 <> t33 <> t34 <> t35 <> t36 <> t37 <> t38 <> t39 <> t40 <> t41 <> t42 <> t43 <> t44 <> t45 <> t46 <> t47 <> t48 <> t49 <> t50 <> t51 <> t52 <> t53 <> t54 <> t55 <> t56 <> t57 <> t58 <> t59 <> t60 <> t61 <> t62 <> t63 <> rest:
      fips_blocks(List.reverse.go(&2, U32, List.reverse(&2, U32, t0 <> t1 <> t2 <> t3 <> t4 <> t5 <> t6 <> t7 <> t8 <> t9 <> t10 <> t11 <> t12 <> t13 <> t14 <> t15 <> t16 <> t17 <> t18 <> t19 <> t20 <> t21 <> t22 <> t23 <> t24 <> t25 <> t26 <> t27 <> t28 <> t29 <> t30 <> t31 <> t32 <> t33 <> t34 <> t35 <> t36 <> t37 <> t38 <> t39 <> t40 <> t41 <> t42 <> t43 <> t44 <> t45 <> t46 <> t47 <> t48 <> t49 <> t50 <> t51 <> t52 <> t53 <> t54 <> t55 <> t56 <> t57 <> t58 <> t59 <> t60 <> t61 <> t62 <> t63 <> rest), padding(n)), extra, s)

# count is the number of bytes already hashed, always a multiple of 64.
def finish(+tail: List<&2, U32>, count: Nat, +extra: Nat, s: S.State) -> S.State:
  finish_n(tail, byte_count(tail, count), extra, s)

# Compress complete 64-byte blocks straight from the input list, so the
# message is never copied, counted or reversed. count is the number of bytes
# already hashed and extra the number of derived schedule words (48).
def stream(+bytes: List<&2, U32>, count: Nat, +extra: Nat, s: S.State) -> S.State:
  match bytes:
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> b8 <> b9 <> b10 <> b11 <> b12 <> b13 <> b14 <> b15 <> b16 <> b17 <> b18 <> b19 <> b20 <> b21 <> b22 <> b23 <> b24 <> b25 <> b26 <> b27 <> b28 <> b29 <> b30 <> b31 <> b32 <> b33 <> b34 <> b35 <> b36 <> b37 <> b38 <> b39 <> b40 <> b41 <> b42 <> b43 <> b44 <> b45 <> b46 <> b47 <> b48 <> b49 <> b50 <> b51 <> b52 <> b53 <> b54 <> b55 <> b56 <> b57 <> b58 <> b59 <> b60 <> b61 <> b62 <> b63 <> rest:
      stream(rest, Nat.add(64n, count), extra, Runtime.fips_compress16(
        Runtime.pack(b0, b1, b2, b3), Runtime.pack(b4, b5, b6, b7), Runtime.pack(b8, b9, b10, b11), Runtime.pack(b12, b13, b14, b15),
        Runtime.pack(b16, b17, b18, b19), Runtime.pack(b20, b21, b22, b23), Runtime.pack(b24, b25, b26, b27), Runtime.pack(b28, b29, b30, b31),
        Runtime.pack(b32, b33, b34, b35), Runtime.pack(b36, b37, b38, b39), Runtime.pack(b40, b41, b42, b43), Runtime.pack(b44, b45, b46, b47),
        Runtime.pack(b48, b49, b50, b51), Runtime.pack(b52, b53, b54, b55), Runtime.pack(b56, b57, b58, b59), Runtime.pack(b60, b61, b62, b63),
        extra, s))
    case _:
      finish(bytes, count, extra, s)

# ASCII convenience only; binary inputs use sha256 directly.
def ascii(s: String) -> List<&2, U32>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{Chr{c}, t}:
      c <> ascii(t)

def hex_digit_if(x: U32, small: Bool) -> Char:
  match small:
    case True{}:
      Chr{(48 + x : U32)}
    case False{}:
      Chr{(87 + x : U32)}

def hex_digit(+x: U32) -> Char:
  hex_digit_if(x, U32.is_lt(x, 10))

def hex_word_go(n: Nat, +x: U32, acc: String) -> String:
  match n:
    case 0n:
      acc
    case 1n+p:
      hex_word_go(p, U32.shrn(x, 4n), SCon{hex_digit((x .&. 15 : U32)), acc})

def hex_word(x: U32) -> String:
  hex_word_go(8n, x, "")

def hex(ws: List<&2, U32>) -> String:
  match ws:
    case Nil{}:
      ""
    case w <> t:
      hex_word(w) ++ hex(t)

def sha256(bytes: List<&2, U32>) -> List<&2, U32>:
  digest(stream(bytes, 0n, 48n, Runtime.initial()))
