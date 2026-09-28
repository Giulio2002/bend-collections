import Base
import ../../../src/crypto/sha3/sha3_256.bend as SHA3
import ../../../src/crypto/sha512/sha512.bend as SHA

# FIPS 202 examples: SHA3-256 of "", "abc" and the 448-bit and 896-bit messages.
def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(SHA.hex(SHA3.sha3_256([])))
    IO.print(SHA.hex(SHA3.sha3_256(SHA.ascii("abc"))))
    IO.print(SHA.hex(SHA3.sha3_256(SHA.ascii("abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"))))
    IO.print(SHA.hex(SHA3.sha3_256(SHA.ascii("abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu"))))
