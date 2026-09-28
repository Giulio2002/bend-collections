import Base
import ./types.bend as T
import ./sbox.bend as B

# AES (FIPS 197) block encryption for 128-, 192- and 256-bit keys. The
# state is four columns of four bytes (U32 values below 256); the S-box and
# the field doublings are the constant-time circuits of sbox.bend. The key
# schedule is expanded once into the list of round keys.

def sub_word(w: T.Quad) -> T.Quad:
  match w:
    case T.W{a, b, c, d}:
      T.W{B.sbox(a), B.sbox(b), B.sbox(c), B.sbox(d)}

def sub_bytes(s: T.State) -> T.State:
  match s:
    case T.S{c0, c1, c2, c3}:
      T.S{sub_word(c0), sub_word(c1), sub_word(c2), sub_word(c3)}

# Row r moves r columns to the left.
def shift_rows(s: T.State) -> T.State:
  match s:
    case T.S{T.W{a0, a1, a2, a3}, T.W{b0, b1, b2, b3}, T.W{c0, c1, c2, c3}, T.W{d0, d1, d2, d3}}:
      T.S{T.W{a0, b1, c2, d3}, T.W{b0, c1, d2, a3}, T.W{c0, d1, a2, b3}, T.W{d0, a1, b2, c3}}

def mix_column(w: T.Quad) -> T.Quad:
  match w:
    case T.W{+a, +b, +c, +d}:
      T.W{U32.xor(U32.xor(U32.xor(B.xtime(a), B.mul3(b)), c), d),
        U32.xor(U32.xor(U32.xor(a, B.xtime(b)), B.mul3(c)), d),
        U32.xor(U32.xor(U32.xor(a, b), B.xtime(c)), B.mul3(d)),
        U32.xor(U32.xor(U32.xor(B.mul3(a), b), c), B.xtime(d))}

def mix_columns(s: T.State) -> T.State:
  match s:
    case T.S{c0, c1, c2, c3}:
      T.S{mix_column(c0), mix_column(c1), mix_column(c2), mix_column(c3)}

def xor_word(a: T.Quad, b: T.Quad) -> T.Quad:
  match a b:
    case T.W{a0, a1, a2, a3} T.W{b0, b1, b2, b3}:
      T.W{U32.xor(a0, b0), U32.xor(a1, b1), U32.xor(a2, b2), U32.xor(a3, b3)}

def add_round_key(s: T.State, k: T.State) -> T.State:
  match s k:
    case T.S{c0, c1, c2, c3} T.S{k0, k1, k2, k3}:
      T.S{xor_word(c0, k0), xor_word(c1, k1), xor_word(c2, k2), xor_word(c3, k3)}

def round(s: T.State, k: T.State) -> T.State:
  add_round_key(mix_columns(shift_rows(sub_bytes(s))), k)

def last_round(s: T.State, k: T.State) -> T.State:
  add_round_key(shift_rows(sub_bytes(s)), k)

# n full rounds, then the final round.
def rounds(n: Nat, s: T.State, ks: List<&2, T.State>) -> T.State:
  match n ks:
    case 0n k <> rest:
      last_round(s, k)
    case 1n+p k <> rest:
      rounds(p, round(s, k), rest)
    case _ _:
      s

def cipher(+nr: Nat, s: T.State, ks: List<&2, T.State>) -> T.State:
  match ks:
    case k <> rest:
      rounds(Nat.sub(nr, 1n), add_round_key(s, k), rest)
    case Nil{}:
      s

# ---- key schedule ----

def rot_word(w: T.Quad) -> T.Quad:
  match w:
    case T.W{a, b, c, d}:
      T.W{b, c, d, a}

# x^n in GF(2^8), by doubling.
def xpow(n: Nat) -> U32:
  match n:
    case 0n:
      1
    case 1n+p:
      B.xtime(xpow(p))

def rcon(j: Nat) -> T.Quad:
  T.W{xpow(Nat.sub(j, 1n)), 0, 0, 0}

def key_words(key: List<&2, U32>) -> List<&2, T.Quad>:
  match key:
    case a <> b <> c <> d <> rest:
      T.W{a, b, c, d} <> key_words(rest)
    case _:
      Nil{}

def get_word(ws: List<&2, T.Quad>, n: Nat) -> T.Quad:
  match ws n:
    case Nil{} _:
      T.W{0, 0, 0, 0}
    case w <> rest 0n:
      w
    case w <> rest 1n+p:
      get_word(rest, p)

def schedule_core(k: Nat, big: Bool, +q: Nat, temp: T.Quad) -> T.Quad:
  match k:
    case 0n:
      xor_word(sub_word(rot_word(temp)), rcon(q))
    case 1n:
      temp
    case 2n:
      temp
    case 3n:
      temp
    case 4n:
      match big:
        case True{}:
          sub_word(temp)
        case False{}:
          temp
    case 5n+p:
      temp

# history is the words so far, the newest first.
def next_word(+nk: Nat, +i: Nat, +history: List<&2, T.Quad>) -> T.Quad:
  xor_word(get_word(history, Nat.sub(nk, 1n)),
    schedule_core(Nat.mod(i, nk), Nat.is_lt(6n, nk), Nat.div(i, nk), get_word(history, 0n)))

def grow(n: Nat, +nk: Nat, +i: Nat, +history: List<&2, T.Quad>) -> List<&2, T.Quad>:
  match n:
    case 0n:
      history
    case 1n+p:
      grow(p, nk, 1n+i, next_word(nk, i, history) <> history)

# Four consecutive words make a round key.
def round_keys(ws: List<&2, T.Quad>) -> List<&2, T.State>:
  match ws:
    case w0 <> w1 <> w2 <> w3 <> rest:
      T.S{w0, w1, w2, w3} <> round_keys(rest)
    case _:
      Nil{}

def expand(+nk: Nat, +nr: Nat, key: List<&2, U32>) -> List<&2, T.State>:
  round_keys(List.reverse(&2, T.Quad, grow(Nat.sub(Nat.mul(4n, 1n+nr), nk), nk, nk,
    List.reverse(&2, T.Quad, key_words(key)))))

def encrypt(+nk: Nat, +nr: Nat, key: List<&2, U32>, block: T.State) -> T.State:
  cipher(nr, block, expand(nk, nr, key))

# ---- byte API ----

# An expanded key: the number of rounds and the round keys.
type Schedule is Data:
  Schedule{rounds: Nat, keys: List<&2, T.State>}

def schedule_for(+n: Nat, +key: List<&2, U32>) -> Maybe<&2, Schedule>:
  match n:
    case 16n:
      Some{Schedule{10n, expand(4n, 10n, key)}}
    case 24n:
      Some{Schedule{12n, expand(6n, 12n, key)}}
    case 32n:
      Some{Schedule{14n, expand(8n, 14n, key)}}
    case _:
      None{}

# A 16-, 24- or 32-byte key (AES-128, AES-192, AES-256); None otherwise.
def expand_key(+key: List<&2, U32>) -> Maybe<&2, Schedule>:
  schedule_for(List.length(&2, U32, key), key)

def encrypt_state(sched: Schedule, s: T.State) -> T.State:
  match sched:
    case Schedule{nr, ks}:
      cipher(nr, s, ks)

def state_of(bytes: List<&2, U32>) -> Maybe<&2, T.State>:
  match bytes:
    case a0 <> a1 <> a2 <> a3 <> b0 <> b1 <> b2 <> b3 <> c0 <> c1 <> c2 <> c3 <> d0 <> d1 <> d2 <> d3 <> Nil{}:
      Some{T.S{T.W{a0, a1, a2, a3}, T.W{b0, b1, b2, b3}, T.W{c0, c1, c2, c3}, T.W{d0, d1, d2, d3}}}
    case _:
      None{}

def bytes_of(s: T.State) -> List<&2, U32>:
  match s:
    case T.S{T.W{a0, a1, a2, a3}, T.W{b0, b1, b2, b3}, T.W{c0, c1, c2, c3}, T.W{d0, d1, d2, d3}}:
      [a0, a1, a2, a3, b0, b1, b2, b3, c0, c1, c2, c3, d0, d1, d2, d3]

def encrypt_bytes(sched: Schedule, m: Maybe<&2, T.State>) -> Maybe<&2, List<&2, U32>>:
  match m:
    case None{}:
      None{}
    case Some{s}:
      Some{bytes_of(encrypt_state(sched, s))}

# Encrypts one 16-byte block; None for another length.
def encrypt_block(sched: Schedule, block: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  encrypt_bytes(sched, state_of(block))

def hex_digit_if(x: U32, small: Bool) -> Char:
  match small:
    case True{}:
      Chr{U32.add(48, x)}
    case False{}:
      Chr{U32.add(87, x)}

def hex_digit(+x: U32) -> Char:
  hex_digit_if(x, U32.is_lt(x, 10))

# Lowercase hexadecimal of a byte list.
def hex(bytes: List<&2, U32>) -> String:
  match bytes:
    case Nil{}:
      ""
    case +b <> rest:
      SCon{hex_digit(U32.and(15, U32.shrn(b, 4n))), SCon{hex_digit(U32.and(15, b)), hex(rest)}}
