#!/usr/bin/env python3
"""Generator of the identities of the twisted Edwards group law
(proofs/crypto/ed25519/group/id_*.bend), by reflection: see idlib.py.

  python3 tools/generators/ed25519_group/gen_ids.py [names...]

The curve is -x^2 + y^2 = 1 + d x^2 y^2 over Z/mZ (no primality is used
here), with e an inverse of d: the curve equation is used as the rule
x^2 y^2 -> e (y^2 - x^2 - 1), and d e -> 1; the leading monomials are
coprime, so the rules are a Groebner basis and the zero test is complete.
The sum of (x1, y1) and (x2, y2) is (nx / dx, ny / dy) with
  t = d ((x1 x2) (y1 y2)),  nx = x1 y2 + y1 x2,  dx = 1 + t,
                            ny = y1 y2 + x1 x2,  dy = 1 - t,
the expressions of spec/crypto/ed25519_group.bend's aadd.
"""
import sys
from idlib import Ctx


def tt(c, p, q, d):
    return c.mul(d, c.mul(c.mul(p[0], q[0]), c.mul(p[1], q[1])))


def parts(c, p, q, d):
    """nx, dx, ny, dy of p + q"""
    t = tt(c, p, q, d)
    return (c.add(c.mul(p[0], q[1]), c.mul(p[1], q[0])), c.add(c.const(1), t),
            c.add(c.mul(p[1], q[1]), c.mul(p[0], q[0])), c.sub(c.const(1), t))


def lhs(c, p):
    return c.sub(c.sq(p[1]), c.sq(p[0]))


def rhs(c, p, d):
    return c.add(c.const(1), c.mul(d, c.mul(c.sq(p[0]), c.sq(p[1]))))


def curve_rule(c, p, e, h):
    """x^2 y^2 -> e (y^2 - x^2 - 1), from the hypothesis h"""
    return c.rule(c.mul(c.sq(p[0]), c.sq(p[1])), c.mul(e, c.sub(c.sub(c.sq(p[1]), c.sq(p[0])), c.const(1))), h)


def de_rule(c, d, e, h):
    return c.rule(c.mul(d, e), c.const(1), h)


def neg(c, v):
    return c.sub(c.zero(), v)


def gen_rule():
    c = Ctx(['x', 'y', 'd', 'e'])
    x, y, d, e = c.vars('x', 'y', 'd', 'e')
    mono = c.mul(c.sq(x), c.sq(y))
    F = c.mul(e, c.sub(c.sub(c.sq(y), c.sq(x)), c.const(1)))
    c.conseq('curve_rule', c.sub(mono, F), [(lhs(c, (x, y)), rhs(c, (x, y), d), neg(c, e)), (c.mul(d, e), c.const(1), neg(c, mono))], (),
             'y^2 - x^2 == 1 + d x^2 y^2 and d e == 1 give x^2 y^2 == e (y^2 - x^2 - 1)')
    c.write('id_rule.bend', '# The curve equation as a rewriting rule.\n')


def gen_comm():
    c = Ctx(['x1', 'y1', 'x2', 'y2', 'd'])
    x1, y1, x2, y2, d = c.vars('x1', 'y1', 'x2', 'y2', 'd')
    p, q = (x1, y1), (x2, y2)
    a, b = parts(c, p, q, d), parts(c, q, p, d)
    c.ident('comm_nx', a[0], b[0], (), 'x1 y2 + y1 x2 == x2 y1 + y2 x1')
    c.ident('comm_ny', a[2], b[2], (), 'y1 y2 + x1 x2 == y2 y1 + x2 x1')
    c.ident('comm_t', tt(c, p, q, d), tt(c, q, p, d), (), 'd ((x1 x2) (y1 y2)) == d ((x2 x1) (y2 y1))')
    c.write('id_comm.bend', '# The addition is commutative: numerators and denominators.\n')


def gen_unit():
    c = Ctx(['x', 'y', 'd'])
    x, y, d = c.vars('x', 'y', 'd')
    p, o = (x, y), (c.zero(), c.const(1))
    nx, dx, ny, dy = parts(c, p, o, d)
    c.ident('unit_x', nx, c.mul(x, dx), (), 'P + (0, 1): nx == x dx')
    c.ident('unit_y', ny, c.mul(y, dy), (), 'P + (0, 1): ny == y dy')
    c.ident('zero_curve', lhs(c, o), rhs(c, o, d), (), '(0, 1) is on the curve')
    c.write('id_unit.bend', '# (0, 1) is the identity.\n')
    c = Ctx(['x', 'y', 'd', 'e'])
    x, y, d, e = c.vars('x', 'y', 'd', 'e')
    p, m = (x, y), (neg(c, x), y)
    cv = [curve_rule(c, p, e, 'h'), de_rule(c, d, e, 'hde')]
    nx, dx, ny, dy = parts(c, p, m, d)
    c.ident('neg_x', nx, c.mul(c.zero(), dx), (), 'P + (-x, y): nx == 0 dx')
    c.ident('neg_y', ny, c.mul(c.const(1), dy), cv, 'P + (-x, y): ny == 1 dy, for P on the curve')
    c.ident('neg_l', lhs(c, m), lhs(c, p), (), 'the curve equation at (-x, y): left side')
    c.ident('neg_r', rhs(c, m, d), rhs(c, p, d), (), 'the curve equation at (-x, y): right side')
    c.write('id_neg.bend', '# (-x, y) is the inverse of (x, y).\n')


def gen_closure():
    c = Ctx(['x1', 'y1', 'x2', 'y2', 'd', 'e', 'xs', 'ys'])
    x1, y1, x2, y2, d, e, X, Y = c.vars('x1', 'y1', 'x2', 'y2', 'd', 'e', 'xs', 'ys')
    p, q = (x1, y1), (x2, y2)
    cv = [curve_rule(c, p, e, 'h1'), curve_rule(c, q, e, 'h2'), de_rule(c, d, e, 'hde')]
    nx, dx, ny, dy = parts(c, p, q, d)
    U, W = c.mul(X, dx), c.mul(Y, dy)
    a = c.mul(c.sub(lhs(c, (X, Y)), rhs(c, (X, Y), d)), c.mul(c.sq(dx), c.sq(dy)))
    c.conseq('add_curve', a,
             [(W, ny, c.mul(c.add(W, ny), c.sub(c.sq(dx), c.mul(d, c.sq(U))))),
              (U, nx, neg(c, c.mul(c.add(U, nx), c.add(c.sq(dy), c.mul(d, c.sq(ny))))))], cv,
             'xs dx == nx and ys dy == ny (the sum (xs, ys) of two points of the curve): (ys^2 - xs^2 - (1 + d xs^2 ys^2)) dx^2 dy^2 == 0')
    c.write('id_closure.bend', '# The sum of two points of the curve is on the curve.\n')


def gen_compl():
    c = Ctx(['x1', 'y1', 'x2', 'y2', 'd', 'e', 'i'])
    x1, y1, x2, y2, d, e, i = c.vars('x1', 'y1', 'x2', 'y2', 'd', 'e', 'i')
    p, q = (x1, y1), (x2, y2)
    cv = [curve_rule(c, p, e, 'h1'), curve_rule(c, q, e, 'h2'), de_rule(c, d, e, 'hde')]
    t = tt(c, p, q, d)
    dx, dy = c.add(c.const(1), t), c.sub(c.const(1), t)
    i2 = c.add(c.sq(i), c.const(1))
    k1 = c.sub(c.sq(x1), c.mul(d, c.mul(c.mul(c.sq(x1), c.sq(y1)), c.sq(x2))))
    ixy = c.mul(c.const(2), c.mul(i, c.mul(x1, y1)))
    for nm, den, other, sg, tg in (('cy_p', dy, dx, 1, 1), ('cy_m', dy, dx, -1, -1), ('cx_p', dx, dy, 1, -1), ('cx_m', dx, dy, -1, 1)):
        ix1 = c.mul(i, x1)
        v = c.add(ix1, y1) if sg > 0 else c.sub(ix1, y1)
        ix2 = c.mul(i, x2)
        u = c.mul(c.mul(x1, y1), c.add(ix2, y2) if tg > 0 else c.sub(ix2, y2))
        cof = c.add(other, ixy) if sg > 0 else c.sub(other, ixy)
        c.conseq(nm, c.sub(c.sq(v), c.mul(d, c.sq(u))), [(i2, c.zero(), k1), (den, c.zero(), cof)], cv,
                 '%s == 0 and i^2 + 1 == 0: (i x1 %s y1)^2 == d (x1 y1 (i x2 %s y2))^2' % ('1 - t' if den is dy else '1 + t', '+' if sg > 0 else '-', '+' if tg > 0 else '-'))
    c.write('id_compl.bend', '# Completeness: a vanishing denominator makes d a square (Bernstein and Lange).\n')


def gen_assoc(which):
    c = Ctx(['x1', 'y1', 'x2', 'y2', 'x3', 'y3', 'd', 'e', 'xa', 'ya', 'xb', 'yb'])
    x1, y1, x2, y2, x3, y3, d, e, Xa, Ya, Xb, Yb = c.vars('x1', 'y1', 'x2', 'y2', 'x3', 'y3', 'd', 'e', 'xa', 'ya', 'xb', 'yb')
    p, q, r = (x1, y1), (x2, y2), (x3, y3)
    cv = [curve_rule(c, p, e, 'h1'), curve_rule(c, q, e, 'h2'), curve_rule(c, r, e, 'h3'), de_rule(c, d, e, 'hde')]
    nxa, dxa, nya, dya = parts(c, p, q, d)       # a = p + q
    nxb, dxb, nyb, dyb = parts(c, q, r, d)       # b = q + r
    Lx, Ldx, Ly, Ldy = parts(c, (Xa, Ya), r, d)  # a + r
    Rx, Rdx, Ry, Rdy = parts(c, p, (Xb, Yb), d)  # p + b
    u = [(c.mul(Xa, dxa), nxa), (c.mul(Ya, dya), nya), (c.mul(Xb, dxb), nxb), (c.mul(Yb, dyb), nyb)]
    Wa, Wb = c.mul(dxa, dya), c.mul(dxb, dyb)
    dxy3, dxy1 = c.mul(d, c.mul(x3, y3)), c.mul(d, c.mul(x1, y1))
    z = c.zero()
    if which == 'x':
        NL, DL, NR, DR = Lx, Ldx, Rx, Rdx
        # A = NL Wa, A' = nxa dya y3 + nya dxa x3; A - A' = u1 dya y3 + u2 dxa x3
        A1 = c.add(c.mul(c.mul(nxa, dya), y3), c.mul(c.mul(nya, dxa), x3))
        da = [c.mul(dya, y3), c.mul(dxa, x3), z, z]
        # C = NR Wb, C' = x1 nyb dxb + y1 nxb dyb; C - C' = u4 x1 dxb + u3 y1 dyb
        C1 = c.add(c.mul(x1, c.mul(nyb, dxb)), c.mul(y1, c.mul(nxb, dyb)))
        dc = [z, z, c.mul(y1, dyb), c.mul(x1, dxb)]
        sg = 1
    else:
        NL, DL, NR, DR = Ly, Ldy, Ry, Rdy
        A1 = c.add(c.mul(c.mul(nya, dxa), y3), c.mul(c.mul(nxa, dya), x3))
        da = [c.mul(dya, x3), c.mul(dxa, y3), z, z]
        C1 = c.add(c.mul(y1, c.mul(nyb, dxb)), c.mul(x1, c.mul(nxb, dyb)))
        dc = [z, z, c.mul(x1, dyb), c.mul(y1, dxb)]
        sg = -1
    # G = DL Wa = Wa +- d x3 y3 (Xa dxa)(Ya dya); G - G' = +- d x3 y3 (u1 Ya dya + nxa u2)
    # B = DR Wb = Wb +- d x1 y1 (Xb dxb)(Yb dyb); B - B' = +- d x1 y1 (u3 Yb dyb + nxb u4)
    dg = [c.mul(dxy3, c.mul(Ya, dya)), c.mul(dxy3, nxa), z, z]
    db = [z, z, c.mul(dxy1, c.mul(Yb, dyb)), c.mul(dxy1, nxb)]
    if sg < 0:
        dg = [neg(c, v) if v is not z else z for v in dg]
        db = [neg(c, v) if v is not z else z for v in db]
    G, B = c.mul(DL, Wa), c.mul(DR, Wb)
    # E W - (A' B' - C' G') = (A - A') B + A' (B - B') - (C - C') G - C' (G - G')
    combos = []
    for k in range(4):
        cof = None
        for s, t in ((1, c.mul(da[k], B) if da[k] is not z else None), (1, c.mul(A1, db[k]) if db[k] is not z else None),
                     (-1, c.mul(dc[k], G) if dc[k] is not z else None), (-1, c.mul(C1, dg[k]) if dg[k] is not z else None)):
            if t is None:
                continue
            if cof is None:
                cof = t if s > 0 else neg(c, t)
            else:
                cof = c.add(cof, t) if s > 0 else c.sub(cof, t)
        combos.append((u[k][0], u[k][1], cof))
    a = c.mul(c.sub(c.mul(NL, DR), c.mul(NR, DL)), c.mul(Wa, Wb))
    np = c.conseq('assoc_' + which, a, combos, cv,
                  '(xa, ya) = P1 + P2 and (xb, yb) = P2 + P3 (as xa dxa == nxa, ...), the three points on the curve: (N_L D_R - N_R D_L) (dxa dya dxb dyb) == 0 for the %s coordinates N_L / D_L of (P1 + P2) + P3 and N_R / D_R of P1 + (P2 + P3)' % which)
    c.write('id_assoc_%s.bend' % which, '# Associativity of the addition, coordinate %s.\n' % which)
    return np


GENS = {'rule': gen_rule, 'comm': gen_comm, 'unit': gen_unit, 'closure': gen_closure, 'compl': gen_compl,
        'assoc_x': lambda: gen_assoc('x'), 'assoc_y': lambda: gen_assoc('y')}

if __name__ == '__main__':
    for nm in (sys.argv[1:] or list(GENS)):
        print(nm, GENS[nm]())
