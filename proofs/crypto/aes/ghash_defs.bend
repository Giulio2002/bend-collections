import Base
import ../../../src/crypto/aes/gcm.bend as I
import ../../../spec/crypto/aes/gcm.bend as G
import ./gf.bend as GF

# The relation between the implementation's GHASH state and the
# specification's field elements.

# The field element of an implementation block (its 16 bytes, as SP 800-38D
# reads them).
def R(z: I.Block) -> Word(128n):
  G.block(I.unpack(z))

# The U32 the implementation reads for a coefficient c.
def bit(c: Bool) -> U32:
  U32{WCon{c, Word.zero(31n)}}

# Algorithm 1 continued from an implementation accumulator (Z, V) over the
# coefficients cs.
def F(acc: I.Acc, cs: List<&2, Bool>) -> Word(128n):
  match acc:
    case I.Acc{z, v}:
      GF.sa(128n, G.low(), cs, R(z), R(v))

# The implementation's steps over a list of coefficients.
def steps(cs: List<&2, Bool>, acc: I.Acc) -> I.Acc:
  match cs:
    case Nil{}:
      acc
    case c <> r:
      steps(r, I.step(bit(c), acc))
