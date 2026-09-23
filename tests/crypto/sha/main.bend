import Base
import ../../../src/crypto/sha/sha256.bend as SHA

def main() -> IO(Unit):
  IO.print(SHA.hex(SHA.sha256(SHA.ascii("abc"))))
