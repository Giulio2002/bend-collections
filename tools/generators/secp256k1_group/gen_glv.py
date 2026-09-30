#!/usr/bin/env python3
"""Identity instances for the GLV endomorphism phi(X : Y : Z) = (beta X : Y : Z)
(proofs/crypto/secp256k1/group/id_glv.bend), by the reflection of gen_ids.py
with the rule b1^3 -> 1 (hypothesis: beta^3 == 1 as residues).

  python3 tools/generators/secp256k1_group/gen_glv.py
"""
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import gen_ids as g

M = '1n+mp'


def rule_beta(c, ib, h):
    """hypothesis h: b1^3 == 1 (as residues); the rule b1^3 -> 1"""
    b = c.vals[ib]
    one = c.const(1)
    rel = 'I.cur_rel(mp, %s, 1n, E.eP(%s, %s), E.eN(%s, %s), %s, %s)' % (b, one.poly, c.env, one.poly, c.env, h, one.rel)
    return (ib, 2, one.poly, rel, '+%s: {FS.mmul(%s, FS.mmul(%s, %s, %s), %s) == 1n : Nat}' % (h, M, M, b, b, b))


def main():
    c = g.Ctx(['x1', 'y1', 'z1', 'x2', 'y2', 'z2', 'b1', 'w'])
    p, q, b1, w = g.point(c, 0), g.point(c, 1), c.var(6), c.var(7)
    rb = [rule_beta(c, 6, 'hb')]
    s = g.padd(c, p, q, w)
    t = g.padd(c, [c.mul(b1, p[0]), p[1], p[2]], [c.mul(b1, q[0]), q[1], q[2]], w)
    c.ident('phi_x', t[0], c.mul(b1, s[0]), rb, 'phi(P) + phi(Q) and phi(P + Q), coordinate X (beta^3 == 1)')
    c.ident('phi_y', t[1], s[1], rb, 'coordinate Y')
    c.ident('phi_z', t[2], s[2], rb, 'coordinate Z')
    c.write('id_glv.bend', '# The GLV endomorphism phi(X : Y : Z) = (beta X : Y : Z), beta^3 == 1, is a\n# homomorphism for the complete addition, coordinate by coordinate.\n')
    c = g.Ctx(['x', 'y', 'z', 'b1'], ['7n'])
    x, y, z, b1, b7 = c.var(0), c.var(1), c.var(2), c.var(3), c.var(4)
    cv = [c.rule_curve(0, 1, 2, 4, 'h'), rule_beta(c, 3, 'hb')]
    c.ident('phi_curve', g.cube(c, c.mul(b1, x)), c.sub(c.mul(c.mul(y, y), z), c.mul(b7, g.cube(c, z))), cv, 'phi(P) is on the curve when P is')
    c.write('id_glv2.bend', '# phi maps the curve to itself.\n')


if __name__ == '__main__':
    main()
