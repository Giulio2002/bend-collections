import Base
import ../../../src/crypto/sha/state.bend as State
import ../../../src/crypto/sha/sha256.bend as SHA
import ./spec.bend as FIPS
import ./conformance.bend as Conformance
import ./laws.bend as Laws

# This gate contains NO concrete-message test vectors.
def Laws.constants_correct():
  {==}

def Laws.sha256_correct(bytes):
  Conformance.sha256_correct(bytes)

law digest_octets_length:
  for s: State.State
  {List.length(&2, U32, FIPS.digest_octets(FIPS.digest(s))) == 32n : Nat}

def digest_octets_length(s):
  match s:
    case State.H{a, b, c, d, e, f, g, h}:
      {==}

def Laws.digest_bytes_correct(ws):
  match ws:
    case Nil{}:
      {==}
    case w <> tail:
      %Laws.digest_bytes_correct(tail) :
        {SHA.digest_bytes(w <> tail) == List.append(&2, U32, FIPS.word_octets(w), _) : List<&2, U32>}
      {==}

def Laws.sha256_bytes_correct(bytes):
  %Laws.sha256_correct(bytes) :
    {SHA.sha256_bytes(bytes) == FIPS.digest_octets(_) : List<&2, U32>}
  Laws.digest_bytes_correct(SHA.sha256(bytes))

def Laws.sha256_bytes_length(bytes):
  %Equal.sym(List<&2, U32>, SHA.sha256_bytes(bytes), FIPS.sha256_bytes(bytes), Laws.sha256_bytes_correct(bytes)) :
    {List.length(&2, U32, _) == 32n : Nat}
  digest_octets_length(FIPS.blocks(FIPS.prepare(bytes, 48n), FIPS.constants())(FIPS.initial()))
