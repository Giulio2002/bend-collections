import Base

# docs/BACKEND_BUGS.md, "nan-bits". The bit pattern of an F32 NaN depends on
# the execution path (the sign and the payload are whatever the host produced).
# Bend 2.0.34 on x86-64 Linux, one line per path:
#
#   bend nan_bits.bend   4290772992 4290772992 2143289344 4290772992 4290772992
#   native               2143289344 4290772992 4290772992 2143289344 2143289344
#   node (JavaScript)    2143289344 4290772992 2145386496 4290772992 2145386496
#
# (2143289344 = 0x7FC00000, 4290772992 = 0xFFC00000, 2145386496 = 0x7FE00000.)

def bits(x: F32) -> String:
  U32.show(F32.bits(x))

def main() -> IO(Unit):
  IO.print(String.join([bits(F32.div(0.0, 0.0)), bits(F32.sqrt(F32.neg(1.0))), bits(F32.log(F32.neg(1.0))), bits(F32.sub(F32.div(1.0, 0.0), F32.div(1.0, 0.0))), bits(F32.pow(F32.neg(2.0), 0.5))], " "))
