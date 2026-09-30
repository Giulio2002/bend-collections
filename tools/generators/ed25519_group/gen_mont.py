#!/usr/bin/env python3
"""Identities of the Montgomery ladder (RFC 7748) through the twisted Edwards
group (proofs/crypto/ed25519/group/id_m*.bend), by reflection: see idlib.py.

  python3 tools/generators/ed25519_group/gen_mont.py

u = (1 + y) / (1 - y) maps the Edwards curve to the Montgomery curve of
X25519. A ladder register (x : z) stands for the point with
x == h (1 + y), z == h (1 - y), h = (x + z) / 2 != 0 (rules x -> h (1 + y),
z -> h (1 - y)). a24 = c with d c + d + c == 0 (d = -a24 / (a24 + 1)).
"""
from idlib import Ctx
from gen_ids import parts, lhs, rhs, curve_rule, de_rule, neg, lin_rule


def consts(c, d, e, a):
    """the rules d e -> 1, d c -> -c - d, e c -> -c - 1"""
    one = c.const(1)
    return [de_rule(c, d, e, 'hde'), c.rule(c.mul(d, a), c.sub(neg(c, a), d), 'hdc'), c.rule(c.mul(e, a), c.sub(neg(c, a), one), 'hec')]


def reg(c, x, z, h, y, nx, nz):
    one = c.const(1)
    return [lin_rule(c, x, c.mul(h, c.add(one, y)), nx), lin_rule(c, z, c.mul(h, c.sub(one, y)), nz)]


def step(c, x1, x2, z2, x3, z3, a24):
    a = c.add(x2, z2)
    aa = c.mul(a, a)
    b = c.sub(x2, z2)
    bb = c.mul(b, b)
    e = c.sub(aa, bb)
    cc = c.add(x3, z3)
    dd = c.sub(x3, z3)
    da = c.mul(dd, a)
    cb = c.mul(cc, b)
    s = c.add(da, cb)
    t = c.sub(da, cb)
    return (c.mul(aa, bb), c.mul(e, c.add(aa, c.mul(e, a24))), c.mul(s, s), c.mul(x1, c.mul(t, t)), s, t)


def gen_dbl():
    c = Ctx(['x2', 'z2', 'h', 'xf', 'yf', 'd', 'e', 'a', 'yd'])
    x2, z2, h, xf, yf, d, e, a, yd = c.vars('x2', 'z2', 'h', 'xf', 'yf', 'd', 'e', 'a', 'yd')
    one = c.const(1)
    F = (xf, yf)
    rules = reg(c, x2, z2, h, yf, 'hx', 'hz') + [curve_rule(c, F, e, 'hf')] + consts(c, d, e, a)
    n2, z2n, _, _, _, _ = step(c, c.zero(), x2, z2, c.zero(), c.zero(), a)
    n2 = c.specdef('mx', n2)
    z2n = c.specdef('mz', z2n)
    nx, dx, ny, dy = parts(c, F, F, d)
    c.conseq('dbl_rel', c.mul(c.sub(c.mul(n2, c.sub(one, yd)), c.mul(z2n, c.add(one, yd))), dy), [(c.mul(yd, dy), ny, neg(c, c.add(n2, z2n)))], rules,
             'yd dy == ny (yd the y of F + F): (x2\' (1 - yd) - z2\' (1 + yd)) dy == 0')
    v = c.add(c.mul(d, c.sq(yf)), one)
    two = c.const(2)
    h2 = c.sq(c.mul(two, h))
    c.ident('dbl_nz', c.mul(c.add(n2, z2n), c.add(one, d)), c.mul(c.sq(h2), c.mul(dy, v)), rules, "(x2' + z2') (1 + d) == (2 h)^4 (dy (d yf^2 + 1))")
    c.write('id_mdbl.bend', '# The ladder\'s doubling is the Edwards doubling.\n')


def gen_add():
    c = Ctx(['x2', 'z2', 'x3', 'z3', 'h', 'k', 'xf', 'yf', 'xr', 'yr', 'd', 'e', 'x1', 'ys', 'yp'])
    x2, z2, x3, z3, h, k, xf, yf, xr, yr, d, e, x1, ys, yp = c.vars('x2', 'z2', 'x3', 'z3', 'h', 'k', 'xf', 'yf', 'xr', 'yr', 'd', 'e', 'x1', 'ys', 'yp')
    one = c.const(1)
    F, R = (xf, yf), (xr, yr)
    regs = reg(c, x2, z2, h, yf, 'hx2', 'hz2') + reg(c, x3, z3, k, yr, 'hx3', 'hz3')
    rules = regs + [curve_rule(c, F, e, 'hf'), curve_rule(c, R, e, 'hr'), de_rule(c, d, e, 'hde')]
    _, _, n3, z3n, s, t = step(c, x1, x2, z2, x3, z3, c.zero())
    n3 = c.specdef('ax', n3)
    z3n = c.specdef('az', z3n)
    s = c.specdef('as', s)
    t = c.specdef('at', t)
    nx, dx, ny, dy = parts(c, F, R, d)
    nn = c.sub(c.mul(yr, yf), c.mul(xr, xf))          # numerator of the y of R - F; its denominator is dx
    u = c.sub(dx, nn)
    w = c.add(dx, nn)
    # (x3' (1 - ys) - z3' (1 + ys)) dy (dx - nn) == 0
    a = c.mul(c.sub(c.mul(n3, c.sub(one, ys)), c.mul(z3n, c.add(one, ys))), c.mul(dy, u))
    c.conseq('add_rel', a, [(c.mul(ys, dy), ny, neg(c, c.mul(u, c.add(n3, z3n)))), (c.mul(x1, u), w, neg(c, c.mul(c.sq(t), c.add(dy, ny))))], rules,
             'ys dy == ny (ys the y of F + R) and x1 (dx - nn) == dx + nn (x1 the u of R - F): (x3\' (1 - ys) - z3\' (1 + ys)) (dy (dx - nn)) == 0')
    two = c.const(2)
    hk = c.mul(c.mul(two, h), c.mul(two, k))
    c.ident('add_s', s, c.mul(hk, c.add(yr, yf)), regs, 'DA + CB == (2 h) (2 k) (yr + yf)')
    c.ident('add_t', t, c.mul(hk, c.sub(yr, yf)), regs, 'DA - CB == (2 h) (2 k) (yr - yf)')
    c.conseq('add_2x', c.mul(two, n3), [(c.mul(n3, c.sub(one, ys)), c.mul(z3n, c.add(one, ys)), one), (c.add(n3, z3n), c.zero(), c.add(one, ys))], (), "x3' (1 - ys) == z3' (1 + ys) and x3' + z3' == 0: 2 x3' == 0")
    c.conseq('add_2y', c.mul(two, yf), [(c.add(yr, yf), c.zero(), one), (c.sub(yr, yf), c.zero(), neg(c, one))], (), 'yr + yf == 0 and yr - yf == 0: 2 yf == 0')
    c.conseq('add_yr', yr, [(c.add(yr, yf), c.zero(), one), (yf, c.zero(), neg(c, one))], (), 'yr + yf == 0 and yf == 0: yr == 0')
    # yf == yr == 0: (1 - yp) (1 + yp) dx^2 == 0
    zr = [lin_rule(c, yf, c.zero(), 'hyf'), lin_rule(c, yr, c.zero(), 'hyr')]
    ypd = c.mul(yp, dx)
    c.conseq('add_deg', c.mul(c.mul(c.sub(one, yp), c.add(one, yp)), c.mul(dx, dx)),
             [(lhs(c, F), rhs(c, F, d), c.sq(xr)), (lhs(c, R), rhs(c, R, d), neg(c, one)), (ypd, nn, neg(c, c.add(ypd, nn)))], zr,
             'yf == yr == 0, F and R on the curve, yp dx == nn: (1 - yp) (1 + yp) dx^2 == 0')
    # x1 (dx - nn) == dx + nn from x1 (1 - yp) == 1 + yp and yp dx == nn
    c.conseq('add_x1', c.sub(c.mul(x1, u), w), [(c.mul(x1, c.sub(one, yp)), c.add(one, yp), dx), (ypd, nn, c.add(x1, one))], (),
             'x1 (1 - yp) == 1 + yp and yp dx == nn: x1 (dx - nn) == dx + nn')
    c.conseq('add_u', c.sub(u, c.mul(dx, c.sub(one, yp))), [(ypd, nn, one)], (), 'yp dx == nn: dx - nn == dx (1 - yp)')
    c.write('id_madd.bend', '# The ladder\'s differential addition is the Edwards addition.\n')


def gen_pu():
    c = Ctx(['x', 'z', 'y', 'i2'])
    x, z, y, i2 = c.vars('x', 'z', 'y', 'i2')
    one = c.const(1)
    two = c.const(2)
    hh = c.mul(c.add(x, z), i2)
    rel = (c.mul(x, c.sub(one, y)), c.mul(z, c.add(one, y)))
    inv = (c.mul(two, i2), one)
    c.conseq('pu_x', c.sub(x, c.mul(hh, c.add(one, y))), [(rel[0], rel[1], i2), (inv[0], inv[1], neg(c, x))], (), 'x (1 - y) == z (1 + y), 2 i2 == 1: x == ((x + z) i2) (1 + y)')
    c.conseq('pu_z', c.sub(z, c.mul(hh, c.sub(one, y))), [(rel[0], rel[1], neg(c, i2)), (inv[0], inv[1], neg(c, z))], (), 'the same: z == ((x + z) i2) (1 - y)')
    c.write('id_mpu.bend', '# A register (x : z) of the point with coordinate y.\n')


if __name__ == '__main__':
    for g in (gen_pu, gen_dbl, gen_add):
        print(g.__name__, g())
