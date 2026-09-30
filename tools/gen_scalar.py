#!/usr/bin/env python3
"""Write src/crypto/ed25519/step.bend and proofs/crypto/ed25519/stepb.bend.

step15 is the Horner step of src/crypto/ed25519/scalar.bend (step: one
17-bit digit into a scalar below L) evaluated on 15 symbolic limbs, the way
tools/gen_fe.py writes the field operations: the generated body is, after
its lets are substituted, the normal form the proof checker computes for
the list form, and stepb.bend checks that with one evaluation.

  python3 tools/gen_scalar.py            rewrite both files
  python3 tools/gen_scalar.py --check    fail if either is out of date
"""
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
from gen_fe import V, lit, op, emit, carry, scal, N

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'src/crypto/ed25519/step.bend'
BRIDGE = ROOT / 'proofs/crypto/ed25519/stepb.bend'


# mirrors of src/crypto/ed25519/scalar.bend and limbs.bend
def subb(R, xs, ys, b):
    if not xs or not ys:
        return [], b
    d = op('Nat.sub', op('Nat.add', xs[0], R), op('Nat.add', ys[0], b))
    rest, out = subb(R, xs[1:], ys[1:], op('Nat.sub', lit('1n'), op('Nat.div', d, R)))
    return [op('Nat.mod', d, R)] + rest, out


def sel(s, xs, ys):
    return [op('Nat.add', op('Nat.mul', x, op('Nat.sub', lit('1n'), s)), op('Nat.mul', y, s)) for x, y in zip(xs, ys)]


def step(R, l, acc, d):
    x = op('Nat.add', acc[13], op('Nat.mul', acc[14], R))
    m = op('Nat.sub', op('Nat.div', x, op('Nat.div', R, lit('8n'))), lit('1n'))
    ml, mo = carry(R, scal(m, l), lit('0n'))
    u, _ = subb(R, [d] + acc, ml + [mo], lit('0n'))
    w, wo = subb(R, u, l + [lit('0n')], lit('0n'))
    return sel(wo, w, u)[:15]


A = [V('a%d' % i) for i in range(N)]
Lm = [V('l%d' % i) for i in range(N)]
R = V('R')

HEADER = '''import Base
import ../curve25519/fe.bend as FE

# The Horner step of scalar.bend on 15 limbs, as straight-line code
# (written by tools/gen_scalar.py from scalar.bend's list form `step`; do
# not edit by hand). l holds L in 15 limbs of 17 bits, a a scalar below L
# the same way, d a 17-bit digit: the result is (d + 2^17 a) mod L. The
# 15-limb container is the field element type (only its shape is used).

'''


def generate():
    lines, res = emit(step(R, Lm, A, V('d')), 'w')
    body = ['def step15(+R: Nat, l: FE.Fe, a: FE.Fe, +d: Nat) -> FE.Fe:',
            '  match l a:',
            '    case FE.Fe{' + ', '.join('+' + x[1] for x in Lm) + '} FE.Fe{' + ', '.join('+' + x[1] for x in A) + '}:']
    body += ['      ' + l for l in lines]
    body.append('      FE.Fe{' + ', '.join(res) + '}')
    return HEADER + '\n'.join(body) + '\n'


def bridge():
    fl = 'FE.Fe{' + ', '.join('l%d' % i for i in range(N)) + '}'
    fa = 'FE.Fe{' + ', '.join('a%d' % i for i in range(N)) + '}'
    return '''import Base
import ../../../src/crypto/curve25519/fe.bend as FE
import ../../../src/crypto/ed25519/scalar.bend as ESC
import ../../../src/crypto/ed25519/step.bend as ST

# The straight-line Horner step is the list form on the limbs: one
# evaluation on symbolic limbs (written by tools/gen_scalar.py together
# with src/crypto/ed25519/step.bend).

def step_b(+R: Nat, +l: FE.Fe, +a: FE.Fe, +d: Nat) -> {FE.to_list(ST.step15(R, l, a, d)) == ESC.step(R, FE.to_list(l), FE.to_list(a), d) : List<&2, Nat>}:
  match l a:
    case %s %s:
      {==}
''' % (fl, fa)


def main():
    text, btext = generate(), bridge()
    if '--check' in sys.argv:
        if OUT.read_text() != text or BRIDGE.read_text() != btext:
            print('step.bend or stepb.bend is out of date: run python3 tools/gen_scalar.py')
            return 1
        return 0
    OUT.write_text(text)
    BRIDGE.write_text(btext)
    return 0


if __name__ == '__main__':
    sys.exit(main())
