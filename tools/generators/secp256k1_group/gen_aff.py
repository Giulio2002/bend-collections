#!/usr/bin/env python3
"""Identity instances for the affine group law (group/aff_id*.bend), written
with gen_ids.py's machinery: nothing here is trusted, each instance is
checked by reflection (see gen_ids.py).

  python3 tools/generators/secp256k1_group/gen_aff.py
"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen_ids as g
from gen_ids import Ctx, cube, padd


def rule_aff(c, ix, iy, ib, h):
    """hypothesis h: (x, y, 1) is on the projective curve (F.OnC(mp, x, y, 1n)); the rule x^3 -> y^2 - b"""
    y, b, one = c.var(iy), c.var(ib), c.const(1)
    F = c.sub(c.mul(c.mul(y, y), one), c.mul(b, cube(c, one)))
    x = c.vals[ix]
    rel = 'I.cur_rel(mp, %s, %s, E.eP(%s, %s), E.eN(%s, %s), %s, %s)' % (x, F.spec, F.poly, c.env, F.poly, c.env, h, F.rel)
    return (ix, 2, F.poly, rel, '+%s: {FS.mmul(%s, FS.mmul(%s, %s, %s), %s) == %s : Nat}' % (h, g.M, g.M, x, x, x, F.spec))


def gen_chord():
    c = Ctx(['u1', 'v1', 'u2', 'v2', 'w'], ['7n'])
    u1, v1, u2, v2, w, b7 = [c.var(i) for i in range(6)]
    b3 = c.cmul(3, 5, 21)
    cv = [rule_aff(c, 0, 1, 5, 'h1'), rule_aff(c, 2, 3, 5, 'h2')]
    one = c.const(1)
    z = one
    s = padd(c, [u1, v1, z], [u2, v2, z], b3)
    d, dv = c.sub(u2, u1), c.sub(v2, v1)
    dw = c.mul(d, w)
    lam = c.mul(dv, w)
    x3 = c.sub(c.sub(c.mul(lam, lam), u1), u2)
    y3 = c.sub(c.mul(lam, c.sub(u1, x3)), v1)
    c.conseq('ch_x', c.mul(c.mul(d, d), c.sub(s[0], c.mul(x3, s[2]))),
             [(one, dw, c.mul(s[2], c.mul(c.mul(dv, dv), c.add(one, dw))))], cv,
             'chord: d^2 (X - x3 Z) == 0 for d = u2 - u1, d w == 1, (X : Y : Z) = (u1, v1, 1) + (u2, v2, 1)')
    c.conseq('ch_y', c.mul(c.mul(c.mul(d, d), d), c.sub(s[1], c.mul(y3, s[2]))),
             [(one, dw, c.mul(s[2], c.sub(c.mul(c.mul(dv, c.add(c.add(u1, u1), u2)), c.mul(d, d)),
                                           c.mul(cube(c, dv), c.add(c.add(c.mul(dw, dw), dw), one)))))], cv,
             'chord: d^3 (Y - y3 Z) == 0')
    c.write('aff_id1.bend', '# The chord: the complete addition of two affine points with x1 != x2.\n')


def gen_tangent():
    c = Ctx(['u', 'v', 'w'], ['7n'])
    u, v, w, b7 = [c.var(i) for i in range(4)]
    b3 = c.cmul(3, 3, 21)
    cv = [rule_aff(c, 0, 1, 3, 'h')]
    one = c.const(1)
    z = one
    s = padd(c, [u, v, z], [u, v, z], b3)
    d = c.mul(c.const(2), v)
    dw = c.mul(d, w)
    uu = c.mul(u, u)
    lam = c.mul(c.mul(c.const(3), uu), w)
    x3 = c.sub(c.sub(c.mul(lam, lam), u), u)
    y3 = c.sub(c.mul(lam, c.sub(u, x3)), v)
    c.conseq('tg_x', c.mul(c.mul(d, d), c.sub(s[0], c.mul(x3, s[2]))),
             [(one, dw, c.mul(s[2], c.mul(c.mul(c.const(9), c.mul(uu, uu)), c.add(one, dw))))], cv,
             'tangent: d^2 (X - x3 Z) == 0 for d = 2 v, d w == 1, (X : Y : Z) = (u, v, 1) + (u, v, 1)')
    c.conseq('tg_y', c.mul(c.mul(c.mul(d, d), d), c.sub(s[1], c.mul(y3, s[2]))),
             [(one, dw, c.mul(s[2], c.sub(c.mul(c.mul(c.const(9), c.mul(uu, u)), c.mul(d, d)),
                                           c.mul(c.mul(c.const(27), c.mul(c.mul(uu, uu), uu)), c.add(c.add(c.mul(dw, dw), dw), one)))))], cv,
             'tangent: d^3 (Y - y3 Z) == 0')
    c.write('aff_id2.bend', '# The tangent: the complete addition of an affine point to itself.\n')


def gen_alg():
    c = Ctx(['u1', 'v1', 'u2', 'v2'])
    u1, v1, u2, v2 = [c.var(i) for i in range(4)]
    one = c.const(1)
    nv2 = c.sub(c.zero(), v2)
    c.conseq('ne_x', c.mul(c.sub(u1, u2), v1), [(c.mul(u1, nv2), c.mul(u2, v1), one), (c.mul(one, v1), c.mul(one, nv2), u1)], (),
             '(u1, v1, 1) equiv -(u2, v2, 1) gives (u1 - u2) v1 == 0')
    c.write('aff_id3.bend', '# Small consequences for the affine law (1).\n')
    c = Ctx(['v'])
    v = c.var(0)
    one = c.const(1)
    c.conseq('two_v', c.mul(c.const(2), v), [(c.mul(one, v), c.mul(one, c.sub(c.zero(), v)), one)], (), '1 v == 1 (-v) gives 2 v == 0')
    c.write('aff_id4.bend', '# Small consequences for the affine law (2).\n')
    c = Ctx(['u', 'v1', 'v2'], ['1n', '7n'])
    u, v1, v2, z, b7 = [c.var(i) for i in range(5)]
    f1 = c.sub(c.mul(c.mul(v1, v1), z), c.mul(b7, cube(c, z)))
    f2 = c.sub(c.mul(c.mul(v2, v2), z), c.mul(b7, cube(c, z)))
    c.conseq('sq_v', c.mul(c.mul(c.sub(v1, v2), c.add(v1, v2)), z), [(f1, f2, c.const(1))], (), 'two points with the same x: (v1 - v2)(v1 + v2) == 0')
    c.write('aff_id5.bend', '# Small consequences for the affine law (3).\n')
    c = Ctx(['x', 'y', 'z', 'i'], ['7n'])
    x, y, z, i, b7 = [c.var(k) for k in range(5)]
    one = c.const(1)
    zi, yi = c.mul(z, i), c.mul(y, i)
    c.conseq('nrm_z', c.sub(c.mul(z, yi), c.mul(one, y)), [(zi, one, y)], (), 'z i == 1: z (y i) == 1 y')
    c.ident('nrm_x', c.mul(x, yi), c.mul(c.mul(x, i), y), (), 'x (y i) == (x i) y')
    c.conseq('nrm_c', c.sub(cube(c, c.mul(x, i)), c.sub(c.mul(c.mul(yi, yi), one), c.mul(b7, cube(c, one)))),
             [(zi, one, c.sub(c.mul(yi, yi), c.mul(b7, c.add(c.add(c.mul(zi, zi), zi), one))))], [c.rule_curve(0, 1, 2, 4, 'h')],
             '(x, y, z) on the curve, z i == 1: (x i, y i, 1) is on the curve')
    c.ident('neg_y', c.mul(c.sub(c.zero(), y), i), c.sub(c.zero(), c.mul(y, i)), (), '(-y) i == -(y i)')
    c.write('aff_id6.bend', '# The affine normalization (x / z, y / z, 1).\n')
    c = Ctx(['x1', 'z1', 'i1', 'x2', 'z2', 'i2'])
    x1, z1, i1, x2, z2, i2 = [c.var(k) for k in range(6)]
    one = c.const(1)
    c.conseq('div_x', c.sub(c.mul(x1, i1), c.mul(x2, i2)),
             [(one, c.mul(z2, i2), c.mul(x1, i1)), (c.mul(x1, z2), c.mul(x2, z1), c.mul(i1, i2)), (c.mul(z1, i1), one, c.mul(x2, i2))], (),
             'x1 z2 == x2 z1 with inverses i1, i2 of z1, z2: x1 i1 == x2 i2')
    c.write('aff_id7.bend', '# Equal quotients.\n')
    c = Ctx(['x1', 'y1', 'z1', 'x2', 'y2', 'z2'], ['7n'])
    x1, y1, z1, x2, y2, z2, b7 = [c.var(k) for k in range(7)]
    c.conseq('xz_eq', c.mul(c.sub(c.mul(x1, z2), c.mul(x2, z1)), c.mul(y1, y2)),
             [(c.mul(x1, y2), c.mul(x2, y1), c.mul(z2, y1)), (c.mul(z2, y1), c.mul(z1, y2), c.mul(x2, y1))], (),
             'equiv points: (x1 z2 - x2 z1) y1 y2 == 0')
    a, b = c.mul(x1, z2), c.mul(x2, z1)
    p, q = c.mul(y1, z2), c.mul(y2, z1)
    c.conseq('same_x', c.mul(c.mul(c.sub(p, q), c.add(p, q)), c.mul(z1, z2)),
             [(a, b, c.add(c.add(c.mul(a, a), c.mul(a, b)), c.mul(b, b)))], [c.rule_curve(0, 1, 2, 6, 'h1'), c.rule_curve(3, 4, 5, 6, 'h2')],
             'x1 z2 == x2 z1 on the curve: (y1 z2 - y2 z1)(y1 z2 + y2 z1) z1 z2 == 0')
    c.write('aff_id8.bend', '# Points with proportional x and z.\n')
    c = Ctx(['x', 'y'])
    x, y = c.var(0), c.var(1)
    one, c7 = c.const(1), c.const(7)
    proj = c.sub(c.mul(c.mul(y, y), one), c.mul(c7, cube(c, one)))
    c.conseq('on_a2p', c.sub(cube(c, x), proj), [(c.add(cube(c, x), c7), c.mul(y, y), one)], (), 'y^2 == x^3 + 7 gives (x, y, 1) on the projective curve')
    c.conseq('on_p2a', c.sub(c.mul(y, y), c.add(cube(c, x), c7)), [(proj, cube(c, x), one)], (), 'and conversely')
    c.write('aff_id9.bend', '# The affine and the projective curve equation at z = 1.\n')


if __name__ == '__main__':
    gen_chord()
    gen_tangent()
    gen_alg()
