import Base

# The PHC string format of an Argon2id hash:
#
#   $argon2id$v=19$m=<m>,t=<t>,p=<p>$<salt>$<hash>
#
# with m, t, p in decimal and the salt and hash in standard base64 (RFC 4648
# section 4 alphabet) without padding, as the reference implementation and
# argon2-cffi write it. parse accepts exactly the strings format writes, up to
# leading zeros in the numbers; base64 must be canonical (unused low bits zero).
#
# Bytes are U32 values below 256. Base64 is computed through 2-bit crumbs: a
# byte is four crumbs (high first), a base64 digit three, so encoding and
# decoding only regroup crumbs.

type Phc is Data:
  Phc{m: Nat, t: Nat, p: Nat, salt: List<&2, U32>, hash: List<&2, U32>}

# A number read and the rest of the string.
type Got is Data:
  Got{value: Nat, rest: String}

# A string cut at a '$': before and after it.
type Cut is Data:
  Cut{before: String, after: String}

# ---------------------------------------------------------------- crumbs

# The crumbs of a byte n, high first: n = ((c3 * 4 + c2) * 4 + c1) * 4 + c0.
def c0(+b: U32) -> U32:
  U32.from_nat(Nat.mod(U32.to_nat(b), 4n))

def c1(+b: U32) -> U32:
  U32.from_nat(Nat.mod(Nat.div(U32.to_nat(b), 4n), 4n))

def c2(+b: U32) -> U32:
  U32.from_nat(Nat.mod(Nat.div(Nat.div(U32.to_nat(b), 4n), 4n), 4n))

def c3(+b: U32) -> U32:
  U32.from_nat(Nat.div(Nat.div(Nat.div(U32.to_nat(b), 4n), 4n), 4n))

# The byte of four crumbs, high first.
def byte_of(+w: U32, +x: U32, +y: U32, +z: U32) -> U32:
  U32.from_nat(Nat.add(Nat.mul(Nat.add(Nat.mul(Nat.add(Nat.mul(U32.to_nat(w), 4n), U32.to_nat(x)), 4n), U32.to_nat(y)), 4n), U32.to_nat(z)))

# The base64 digit value of three crumbs, high first, and back.
def sext(+x: U32, +y: U32, +z: U32) -> U32:
  U32.or(U32.shln(x, 4n), U32.or(U32.shln(y, 2n), z))

def su(+s: U32) -> U32:
  U32.shrn(s, 4n)

def sv(+s: U32) -> U32:
  U32.and(U32.shrn(s, 2n), 3)

def sw(+s: U32) -> U32:
  U32.and(s, 3)

def digit_last(+s: U32, is62: Bool) -> U32:
  match is62:
    case True{}:
      43
    case False{}:
      47

# ---------------------------------------------------------------- base64 digits

def digit_hi(+s: U32, lt62: Bool) -> U32:
  match lt62:
    case True{}:
      U32.sub(s, 4)
    case False{}:
      digit_last(s, U32.is_eq(s, 62))

def digit_mid(+s: U32, lt52: Bool) -> U32:
  match lt52:
    case True{}:
      U32.add(s, 71)
    case False{}:
      digit_hi(s, U32.is_lt(s, 62))

def digit_code(+s: U32, lt26: Bool) -> U32:
  match lt26:
    case True{}:
      U32.add(s, 65)
    case False{}:
      digit_mid(s, U32.is_lt(s, 52))

# The character of digit value s < 64: A-Z, a-z, 0-9, +, /.
def digit(+s: U32) -> Char:
  Chr{digit_code(s, U32.is_lt(s, 26))}

def in_range(+x: U32, +lo: U32, +hi: U32) -> Bool:
  Bool.and(U32.is_le(lo, x), U32.is_le(x, hi))

def value_slash(slash: Bool) -> Maybe<&2, U32>:
  match slash:
    case True{}:
      Some{63}
    case False{}:
      None{}

def value_sym(+x: U32, plus: Bool) -> Maybe<&2, U32>:
  match plus:
    case True{}:
      Some{62}
    case False{}:
      value_slash(U32.is_eq(x, 47))

def value_num(+x: U32, num: Bool) -> Maybe<&2, U32>:
  match num:
    case True{}:
      Some{U32.add(x, 4)}
    case False{}:
      value_sym(x, U32.is_eq(x, 43))

def value_low(+x: U32, low: Bool) -> Maybe<&2, U32>:
  match low:
    case True{}:
      Some{U32.sub(x, 71)}
    case False{}:
      value_num(x, in_range(x, 48, 57))

def value_code(+x: U32, up: Bool) -> Maybe<&2, U32>:
  match up:
    case True{}:
      Some{U32.sub(x, 65)}
    case False{}:
      value_low(x, in_range(x, 97, 122))

# The value of a base64 character, or None.
def value(c: Char) -> Maybe<&2, U32>:
  match c:
    case Chr{+x}:
      value_code(x, in_range(x, 65, 90))

# ---------------------------------------------------------------- base64

def enc1(+a: U32) -> String:
  SCon{digit(sext(c3(a), c2(a), c1(a))), SCon{digit(sext(c0(a), 0, 0)), SNil{}}}

def enc2(+a: U32, +b: U32) -> String:
  SCon{digit(sext(c3(a), c2(a), c1(a))), SCon{digit(sext(c0(a), c3(b), c2(b))), SCon{digit(sext(c1(b), c0(b), 0)), SNil{}}}}

def enc3(+a: U32, +b: U32, +c: U32, rest: String) -> String:
  SCon{digit(sext(c3(a), c2(a), c1(a))), SCon{digit(sext(c0(a), c3(b), c2(b))), SCon{digit(sext(c1(b), c0(b), c3(c))), SCon{digit(sext(c2(c), c1(c), c0(c))), rest}}}}

# Standard base64 without padding.
def b64(bs: List<&2, U32>) -> String:
  match bs:
    case Nil{}:
      SNil{}
    case a <> Nil{}:
      enc1(a)
    case a <> b <> Nil{}:
      enc2(a, b)
    case a <> b <> c <> rest:
      enc3(a, b, c, b64(rest))

def dec2_fin(+x: U32, ok: Bool) -> Maybe<&2, List<&2, U32>>:
  match ok:
    case True{}:
      Some{[x]}
    case False{}:
      None{}

def dec2(ma: Maybe<&2, U32>, mb: Maybe<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match ma mb:
    case Some{+a} Some{+b}:
      dec2_fin(byte_of(su(a), sv(a), sw(a), su(b)), Bool.and(U32.is_eq(sv(b), 0), U32.is_eq(sw(b), 0)))
    case _ _:
      None{}

def dec3_fin(+x: U32, +y: U32, ok: Bool) -> Maybe<&2, List<&2, U32>>:
  match ok:
    case True{}:
      Some{[x, y]}
    case False{}:
      None{}

def dec3(ma: Maybe<&2, U32>, mb: Maybe<&2, U32>, mc: Maybe<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match ma mb mc:
    case Some{+a} Some{+b} Some{+c}:
      dec3_fin(byte_of(su(a), sv(a), sw(a), su(b)), byte_of(sv(b), sw(b), su(c), sv(c)), U32.is_eq(sw(c), 0))
    case _ _ _:
      None{}

def dec4(ma: Maybe<&2, U32>, mb: Maybe<&2, U32>, mc: Maybe<&2, U32>, md: Maybe<&2, U32>, mr: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match ma mb mc md mr:
    case Some{+a} Some{+b} Some{+c} Some{+d} Some{rest}:
      Some{byte_of(su(a), sv(a), sw(a), su(b)) <> byte_of(sv(b), sw(b), su(c), sv(c)) <> byte_of(sw(c), su(d), sv(d), sw(d)) <> rest}
    case _ _ _ _ _:
      None{}

# The bytes of canonical unpadded base64, or None.
def unb64(s: String) -> Maybe<&2, List<&2, U32>>:
  match s:
    case SNil{}:
      Some{Nil{}}
    case SCon{a, SNil{}}:
      None{}
    case SCon{a, SCon{b, SNil{}}}:
      dec2(value(a), value(b))
    case SCon{a, SCon{b, SCon{c, SNil{}}}}:
      dec3(value(a), value(b), value(c))
    case SCon{a, SCon{b, SCon{c, SCon{d, rest}}}}:
      dec4(value(a), value(b), value(c), value(d), unb64(rest))

# ---------------------------------------------------------------- decimal

def dchar(+d: Nat) -> Char:
  Chr{U32.add(48, U32.from_nat(d))}

# The decimal digits of n before acc; fuel bounds the number of digits and
# last says n < 10.
def dec_go(fuel: Nat, +n: Nat, acc: String, last: Bool) -> String:
  match fuel last:
    case 0n _:
      acc
    case 1n+f True{}:
      SCon{dchar(n), acc}
    case 1n+f False{}:
      +q = Nat.div(n, 10n)
      dec_go(f, q, SCon{dchar(Nat.mod(n, 10n)), acc}, Nat.is_lt(q, 10n))

# n in decimal, without leading zeros.
def decimal(+n: Nat) -> String:
  dec_go(1n+n, n, SNil{}, Nat.is_lt(n, 10n))

def is_digit(+x: U32) -> Bool:
  in_range(x, 48, 57)

def starts_digit(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{Chr{+x}, rest}:
      is_digit(x)

# Digits from s on top of v (d says s starts with a digit); the value and the rest.
def read_go(s: String, +v: Nat, d: Bool) -> Got:
  match s d:
    case SNil{} _:
      Got{v, SNil{}}
    case SCon{Chr{+x}, +rest} True{}:
      read_go(rest, Nat.add(Nat.mul(v, 10n), U32.to_nat(U32.sub(x, 48))), starts_digit(rest))
    case SCon{c, rest} False{}:
      Got{v, SCon{c, rest}}

def read_check(s: String, first: Bool) -> Maybe<&2, Got>:
  match first:
    case True{}:
      Some{read_go(s, 0n, True{})}
    case False{}:
      None{}

# A decimal number (at least one digit) and the rest.
def read(+s: String) -> Maybe<&2, Got>:
  read_check(s, starts_digit(s))

# ---------------------------------------------------------------- the string

def same_char(a: Char, b: Char) -> Bool:
  match a b:
    case Chr{x} Chr{y}:
      U32.is_eq(x, y)

def heads(+lit: String, +s: String) -> Bool:
  match lit s:
    case SCon{a, lt} SCon{b, st}:
      same_char(a, b)
    case _ _:
      False{}

# s without the prefix lit, or None (same says the first characters agree).
def strip_go(lit: String, s: String, same: Bool) -> Maybe<&2, String>:
  match lit s same:
    case SNil{} _ _:
      Some{s}
    case SCon{a, lt} SNil{} _:
      None{}
    case SCon{a, +lt} SCon{b, +st} True{}:
      strip_go(lt, st, heads(lt, st))
    case SCon{a, lt} SCon{b, st} False{}:
      None{}

def strip(+lit: String, +s: String) -> Maybe<&2, String>:
  strip_go(lit, s, heads(lit, s))

def dollar(s: String) -> Bool:
  match s:
    case SCon{Chr{+x}, rest}:
      U32.is_eq(x, 36)
    case SNil{}:
      False{}

def field_cons(+x: U32, r: Maybe<&2, Cut>) -> Maybe<&2, Cut>:
  match r:
    case None{}:
      None{}
    case Some{Cut{a, b}}:
      Some{Cut{SCon{Chr{x}, a}, b}}

# The characters before the first '$' and what follows it, or None (d says s starts with '$').
def field_go(s: String, d: Bool) -> Maybe<&2, Cut>:
  match s d:
    case SNil{} _:
      None{}
    case SCon{c, rest} True{}:
      Some{Cut{SNil{}, rest}}
    case SCon{Chr{+x}, +rest} False{}:
      field_cons(x, field_go(rest, dollar(rest)))

def field(+s: String) -> Maybe<&2, Cut>:
  field_go(s, dollar(s))

def format(x: Phc) -> String:
  match x:
    case Phc{m, t, p, salt, hash}:
      String.concat(["$argon2id$v=19$m=", decimal(m), ",t=", decimal(t), ",p=", decimal(p), "$", b64(salt), "$", b64(hash)])

def parse_hash(+m: Nat, +t: Nat, +p: Nat, salt: Maybe<&2, List<&2, U32>>, hash: Maybe<&2, List<&2, U32>>) -> Maybe<&2, Phc>:
  match salt hash:
    case Some{s} Some{h}:
      Some{Phc{m, t, p, s, h}}
    case _ _:
      None{}

def parse_salt(+m: Nat, +t: Nat, +p: Nat, r: Maybe<&2, Cut>) -> Maybe<&2, Phc>:
  match r:
    case None{}:
      None{}
    case Some{Cut{s, h}}:
      parse_hash(m, t, p, unb64(s), unb64(h))

def parse_p2(+m: Nat, +t: Nat, +p: Nat, r: Maybe<&2, String>) -> Maybe<&2, Phc>:
  match r:
    case None{}:
      None{}
    case Some{rest}:
      parse_salt(m, t, p, field(rest))

def parse_p(+m: Nat, +t: Nat, r: Maybe<&2, Got>) -> Maybe<&2, Phc>:
  match r:
    case None{}:
      None{}
    case Some{Got{+p, rest}}:
      parse_p2(m, t, p, strip("$", rest))

def parse_t2(+m: Nat, +t: Nat, r: Maybe<&2, String>) -> Maybe<&2, Phc>:
  match r:
    case None{}:
      None{}
    case Some{rest}:
      parse_p(m, t, read(rest))

def parse_t(+m: Nat, r: Maybe<&2, Got>) -> Maybe<&2, Phc>:
  match r:
    case None{}:
      None{}
    case Some{Got{+t, rest}}:
      parse_t2(m, t, strip(",p=", rest))

def parse_m2(+m: Nat, r: Maybe<&2, String>) -> Maybe<&2, Phc>:
  match r:
    case None{}:
      None{}
    case Some{rest}:
      parse_t(m, read(rest))

def parse_m(r: Maybe<&2, Got>) -> Maybe<&2, Phc>:
  match r:
    case None{}:
      None{}
    case Some{Got{+m, rest}}:
      parse_m2(m, strip(",t=", rest))

def parse_head(r: Maybe<&2, String>) -> Maybe<&2, Phc>:
  match r:
    case None{}:
      None{}
    case Some{rest}:
      parse_m(read(rest))

# The fields of an Argon2id version 19 PHC string, or None.
def parse(s: String) -> Maybe<&2, Phc>:
  parse_head(strip("$argon2id$v=19$m=", s))
