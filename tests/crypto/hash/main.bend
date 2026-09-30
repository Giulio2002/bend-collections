import Base
import ../../../src/crypto/hash.bend as Hash
import ../../../src/crypto/sha512/sha512.bend as SHA

# The facade on "abc": one-shot, then incremental as "a" + "" + "bc", for
# SHA-256, SHA-512 and SHA3-256 (each pair of lines must agree).
def split(h: Hash.Hasher) -> List<&2, U32>:
  Hash.digest(Hash.update(Hash.update(Hash.update(h, [97]), []), [98, 99]))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(SHA.hex(Hash.sha256([97, 98, 99])))
    IO.print(SHA.hex(split(Hash.new_sha256())))
    IO.print(SHA.hex(Hash.sha512([97, 98, 99])))
    IO.print(SHA.hex(split(Hash.new_sha512())))
    IO.print(SHA.hex(Hash.sha3_256([97, 98, 99])))
    IO.print(SHA.hex(split(Hash.new_sha3_256())))
