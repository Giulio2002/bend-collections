#!/usr/bin/env python3
"""Identity instances for the SEC 1 encoding proofs (group/id_enc.bend),
written with gen_ids' reflection combinators.

  python3 tools/generators/secp256k1_group/gen_enc.py
"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen_ids as g


def gen():
    out = []
    c = g.Ctx(['r', 'y'])
    r, y = c.var(0), c.var(1)
    c.conseq('sq_diff', c.mul(c.sub(r, y), c.add(r, y)), [(c.mul(r, r), c.mul(y, y), c.const(1))], (),
             'r^2 == y^2 gives (r - y) (r + y) == 0')
    ny = c.sub(c.zero(), r)
    c.ident('neg_sq', c.mul(ny, ny), c.mul(r, r), (), '(-r)^2 == r^2')
    out += c.defs
    c = g.Ctx(['x', 'y'])
    x, y = c.var(0), c.var(1)
    one = c.const(1)
    c.conseq('proj1', c.sub(c.mul(c.mul(y, y), one), c.add(g.cube(c, x), c.mul(c.const(7), g.cube(c, one)))),
             [(c.mul(y, y), c.add(g.cube(c, x), c.const(7)), c.const(1))], (),
             'y^2 == x^3 + 7 gives the projective equation of (x : y : 1)')
    out += c.defs
    c = g.Ctx(['x', 'y', 'z', 'w'])
    x, y, z, w = [c.var(i) for i in range(4)]
    xa, ya, gg = c.mul(x, w), c.mul(y, w), c.mul(z, w)
    c.conseq('aff_curve', c.sub(c.mul(ya, ya), c.add(g.cube(c, xa), c.const(7))),
             [(c.mul(c.mul(y, y), z), c.add(g.cube(c, x), c.mul(c.const(7), g.cube(c, z))), g.cube(c, w)),
              (c.const(1), gg, c.sub(c.mul(c.mul(y, y), c.mul(w, w)), c.mul(c.const(7), c.add(c.add(c.const(1), gg), c.mul(gg, gg)))))], (),
             'Y^2 Z == X^3 + 7 Z^3 and Z w == 1 give (Y w)^2 == (X w)^3 + 7')
    out += c.defs
    with open(os.path.join(g.OUT, 'id_enc.bend'), 'w') as f:
        f.write(g.HEAD.replace('gen_ids.py', 'gen_enc.py') + '\n# The identities behind the SEC 1 encoding round trips.\n\n' + '\n'.join(out))


if __name__ == '__main__':
    gen()
