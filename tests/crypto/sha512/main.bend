import Base
import ../../../src/crypto/sha512/sha512.bend as SHA

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(SHA.hex(SHA.sha512([])))
    IO.print(SHA.hex(SHA.sha512(SHA.ascii("abc"))))
    IO.print(SHA.hex(SHA.sha512(SHA.ascii("abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu"))))
