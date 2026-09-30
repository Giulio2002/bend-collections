import Base
import ./argon2/argon2.bend as A2
import ./argon2/phc.bend as PHC
import ./subtle.bend as Subtle

# Password hashing with Argon2id (RFC 9106, version 0x13), stored as PHC
# strings:
#
#   hash_password(pw, salt, params)   Some{"$argon2id$v=19$m=..,t=..,p=..$salt$hash"},
#                                     None when a parameter is out of range
#   hash_password_os(pw, params)      the same with a fresh random salt of
#                                     params' salt length (IO.random_u32)
#   verify_password(pw, encoded)      the password hashes to the encoded tag
#                                     (constant-time comparison, subtle.eq)
#   needs_rehash(encoded, params)     the string is not Argon2id v=19 with
#                                     exactly these parameters
#
# Passwords and salts are byte lists (U32 values below 256). Parameters are
# m (memory, KiB), t (passes), p (lanes), the tag length and the salt length
# in bytes. owasp() is OWASP's Argon2id recommendation (m = 19 MiB, t = 2,
# p = 1); rfc9106() is RFC 9106 section 4's second recommended option
# (m = 64 MiB, t = 3, p = 4); both with 16-byte salts and 32-byte tags.

type Params is Data:
  Params{m: Nat, t: Nat, p: Nat, tag: Nat, salt: Nat}

def owasp() -> Params:
  Params{19456n, 2n, 1n, 32n, 16n}

def rfc9106() -> Params:
  Params{65536n, 3n, 4n, 32n, 16n}

def len(xs: List<&2, U32>) -> Nat:
  List.length(&2, U32, xs)

def encode(+m: Nat, +t: Nat, +p: Nat, +salt: List<&2, U32>, r: Maybe<&2, List<&2, U32>>) -> Maybe<&2, String>:
  match r:
    case None{}:
      None{}
    case Some{h}:
      Some{PHC.format(PHC.Phc{m, t, p, salt, h})}

# The PHC string of Argon2id(pw, salt) with the parameters, or None when they
# are out of the RFC 9106 ranges (or m > 2^23 KiB, this implementation's limit).
def hash_password(+pw: List<&2, U32>, +salt: List<&2, U32>, params: Params) -> Maybe<&2, String>:
  match params:
    case Params{+m, +t, +p, +tag, s}:
      encode(m, t, p, salt, A2.argon2id(pw, salt, Nil{}, Nil{}, t, m, p, tag))

def verify_tag(+hash: List<&2, U32>, r: Maybe<&2, List<&2, U32>>) -> Bool:
  match r:
    case None{}:
      False{}
    case Some{tag}:
      Subtle.eq(tag, hash)

def verify_phc(+pw: List<&2, U32>, x: PHC.Phc) -> Bool:
  match x:
    case PHC.Phc{+m, +t, +p, +salt, +hash}:
      verify_tag(hash, A2.argon2id(pw, salt, Nil{}, Nil{}, t, m, p, len(hash)))

def verify_parsed(+pw: List<&2, U32>, r: Maybe<&2, PHC.Phc>) -> Bool:
  match r:
    case None{}:
      False{}
    case Some{x}:
      verify_phc(pw, x)

# The password matches the encoded Argon2id hash.
def verify_password(+pw: List<&2, U32>, encoded: String) -> Bool:
  verify_parsed(pw, PHC.parse(encoded))

def same(+x: PHC.Phc, params: Params) -> Bool:
  match x params:
    case PHC.Phc{+m, +t, +p, +salt, +hash} Params{+pm, +pt, +pp, +ptag, +psalt}:
      Bool.and(Bool.and(Nat.is_eq(m, pm), Bool.and(Nat.is_eq(t, pt), Nat.is_eq(p, pp))), Bool.and(Nat.is_eq(len(hash), ptag), Nat.is_eq(len(salt), psalt)))

def rehash_parsed(r: Maybe<&2, PHC.Phc>, params: Params) -> Bool:
  match r:
    case None{}:
      True{}
    case Some{x}:
      Bool.not(same(x, params))

# The encoded hash should be recomputed: it is not an Argon2id v=19 PHC string
# with exactly these memory, passes, lanes, tag and salt lengths.
def needs_rehash(encoded: String, params: Params) -> Bool:
  rehash_parsed(PHC.parse(encoded), params)

# n bytes from the operating system's generator.
def random_bytes(n: Nat) -> IO(List<&2, U32>):
  match n:
    case 0n:
      IO.pure(List<&2, U32>, Nil{})
    case 1n+k:
      do IO<List<&2, U32>>:
        w : U32 <- IO.try(U32, IO.random_u32())
        rest : List<&2, U32> <- random_bytes(k)
        return U32.and(w, 255) <> rest

def salt_len(+params: Params) -> Nat:
  match params:
    case Params{m, t, p, tag, s}:
      s

# hash_password with a fresh salt of params' salt length from IO.random_u32.
def hash_password_os(+pw: List<&2, U32>, +params: Params) -> IO(Maybe<&2, String>):
  do IO<Maybe<&2, String>>:
    salt : List<&2, U32> <- random_bytes(salt_len(params))
    return hash_password(pw, salt, params)
