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
    return c.call('G.ct(1n+mp, %s, %s, %s, %s, %s)' % (d.spec, p[0].spec, p[1].spec, q[0].spec, q[1].spec),
                  c.mul(d, c.mul(c.mul(p[0], q[0]), c.mul(p[1], q[1]))))


def parts(c, p, q, d):
    """nx, dx, ny, dy of p + q"""
    t = tt(c, p, q, d)
    a4 = '%s, %s, %s, %s' % (p[0].spec, p[1].spec, q[0].spec, q[1].spec)
    return (c.call('G.nx(1n+mp, %s)' % a4, c.add(c.mul(p[0], q[1]), c.mul(p[1], q[0]))),
            c.call('G.dx(1n+mp, %s, %s)' % (d.spec, a4), c.add(c.const(1), t)),
            c.call('G.ny(1n+mp, %s)' % a4, c.add(c.mul(p[1], q[1]), c.mul(p[0], q[0]))),
            c.call('G.dy(1n+mp, %s, %s)' % (d.spec, a4), c.sub(c.const(1), t)))


def lhs(c, p):
    return c.call('G.lhs(1n+mp, %s, %s)' % (p[0].spec, p[1].spec), c.sub(c.sq(p[1]), c.sq(p[0])))


def rhs(c, p, d):
    return c.call('G.rhs(1n+mp, %s, %s, %s)' % (d.spec, p[0].spec, p[1].spec), c.add(c.const(1), c.mul(d, c.mul(c.sq(p[0]), c.sq(p[1])))))


def curve_rule(c, p, e, h):
    """x^2 y^2 -> e (y^2 - x^2 - 1), from the hypothesis h"""
    return c.rule(c.mul(c.sq(p[0]), c.sq(p[1])), c.mul(e, c.sub(c.sub(c.sq(p[1]), c.sq(p[0])), c.const(1))), h,
                  'IM.Rule(mp, %s, %s, %s)' % (e.spec, p[0].spec, p[1].spec))


def de_rule(c, d, e, h):
    return c.rule(c.mul(d, e), c.const(1), h, 'IM.Inv(mp, %s, %s)' % (d.spec, e.spec))


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
    up = c.specdef('up', c.mul(c.mul(x1, y1), c.add(c.mul(i, x2), y2)))
    um = c.specdef('um', c.mul(c.mul(x1, y1), c.sub(c.mul(i, x2), y2)))
    vp = c.specdef('vp', c.add(c.mul(i, x1), y1))
    vm = c.specdef('vm', c.sub(c.mul(i, x1), y1))
    for nm, den, other, sg, tg in (('cy_p', dy, dx, 1, 1), ('cy_m', dy, dx, -1, -1), ('cx_p', dx, dy, 1, -1), ('cx_m', dx, dy, -1, 1)):
        v = vp if sg > 0 else vm
        u = up if tg > 0 else um
        cof = c.add(other, ixy) if sg > 0 else c.sub(other, ixy)
        c.conseq(nm, c.sub(c.sq(v), c.mul(d, c.sq(u))), [(i2, c.zero(), k1), (den, c.zero(), cof)], cv,
                 '%s == 0 and i^2 + 1 == 0: (i x1 %s y1)^2 == d (x1 y1 (i x2 %s y2))^2' % ('1 - t' if den is dy else '1 + t', '+' if sg > 0 else '-', '+' if tg > 0 else '-'))
    dx2 = c.mul(d, x2)
    c.conseq('two_y', c.const(2), [(dy, c.zero(), c.const(2)), (up, c.zero(), dx2), (um, c.zero(), neg(c, dx2))], (),
             '1 - t == 0 and x1 y1 (i x2 + y2) == 0 and x1 y1 (i x2 - y2) == 0: 2 == 0')
    c.conseq('two_x', c.const(2), [(dx, c.zero(), c.const(2)), (up, c.zero(), neg(c, dx2)), (um, c.zero(), dx2)], (),
             '1 + t == 0 and x1 y1 (i x2 + y2) == 0 and x1 y1 (i x2 - y2) == 0: 2 == 0')
    c.write('id_compl.bend', '# Completeness: a vanishing denominator makes d a square (Bernstein and Lange).\n')


def gen_assoc(which):
    c = Ctx(['x1', 'y1', 'x2', 'y2', 'x3', 'y3', 'd', 'e', 'xa', 'ya', 'xb', 'yb'])
    x1, y1, x2, y2, x3, y3, d, e, Xa, Ya, Xb, Yb = c.vars('x1', 'y1', 'x2', 'y2', 'x3', 'y3', 'd', 'e', 'xa', 'ya', 'xb', 'yb')
    p, q, r = (x1, y1), (x2, y2), (x3, y3)
    cv = [curve_rule(c, p, e, 'h1'), curve_rule(c, q, e, 'h2'), curve_rule(c, r, e, 'h3'), de_rule(c, d, e, 'hde')]
    sh = c.share
    nxa, dxa, nya, dya = [sh(v) for v in parts(c, p, q, d)]       # a = p + q
    nxb, dxb, nyb, dyb = [sh(v) for v in parts(c, q, r, d)]       # b = q + r
    Lx, Ldx, Ly, Ldy = [sh(v) for v in parts(c, (Xa, Ya), r, d)]  # a + r
    Rx, Rdx, Ry, Rdy = [sh(v) for v in parts(c, p, (Xb, Yb), d)]  # p + b
    u = [(sh(c.mul(Xa, dxa)), nxa), (sh(c.mul(Ya, dya)), nya), (sh(c.mul(Xb, dxb)), nxb), (sh(c.mul(Yb, dyb)), nyb)]
    Wa, Wb = sh(c.mul(dxa, dya)), sh(c.mul(dxb, dyb))
    dxy3, dxy1 = sh(c.mul(d, c.mul(x3, y3))), sh(c.mul(d, c.mul(x1, y1)))
    z = c.zero()
    if which == 'x':
        NL, DL, NR, DR = Lx, Ldx, Rx, Rdx
        # A = NL Wa, A' = nxa dya y3 + nya dxa x3; A - A' = u1 dya y3 + u2 dxa x3
        A1 = sh(c.add(c.mul(c.mul(nxa, dya), y3), c.mul(c.mul(nya, dxa), x3)))
        da = [c.mul(dya, y3), c.mul(dxa, x3), z, z]
        # C = NR Wb, C' = x1 nyb dxb + y1 nxb dyb; C - C' = u4 x1 dxb + u3 y1 dyb
        C1 = sh(c.add(c.mul(x1, c.mul(nyb, dxb)), c.mul(y1, c.mul(nxb, dyb))))
        dc = [z, z, c.mul(y1, dyb), c.mul(x1, dxb)]
        sg = 1
    else:
        NL, DL, NR, DR = Ly, Ldy, Ry, Rdy
        A1 = sh(c.add(c.mul(c.mul(nya, dxa), y3), c.mul(c.mul(nxa, dya), x3)))
        da = [c.mul(dya, x3), c.mul(dxa, y3), z, z]
        C1 = sh(c.add(c.mul(y1, c.mul(nyb, dxb)), c.mul(x1, c.mul(nxb, dyb))))
        dc = [z, z, c.mul(x1, dyb), c.mul(y1, dxb)]
        sg = -1
    # G = DL Wa = Wa +- d x3 y3 (Xa dxa)(Ya dya); G - G' = +- d x3 y3 (u1 Ya dya + nxa u2)
    # B = DR Wb = Wb +- d x1 y1 (Xb dxb)(Yb dyb); B - B' = +- d x1 y1 (u3 Yb dyb + nxb u4)
    dg = [c.mul(dxy3, c.mul(Ya, dya)), c.mul(dxy3, nxa), z, z]
    db = [z, z, c.mul(dxy1, c.mul(Yb, dyb)), c.mul(dxy1, nxb)]
    if sg < 0:
        dg = [neg(c, v) if v is not z else z for v in dg]
        db = [neg(c, v) if v is not z else z for v in db]
    G, B = sh(c.mul(DL, Wa)), sh(c.mul(DR, Wb))
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
        combos.append((u[k][0], u[k][1], sh(cof)))
    a = c.mul(c.sub(c.mul(NL, DR), c.mul(NR, DL)), c.mul(Wa, Wb))
    np = c.conseq('assoc_' + which, a, combos, cv,
                  '(xa, ya) = P1 + P2 and (xb, yb) = P2 + P3 (as xa dxa == nxa, ...), the three points on the curve: (N_L D_R - N_R D_L) (dxa dya dxb dyb) == 0 for the %s coordinates N_L / D_L of (P1 + P2) + P3 and N_R / D_R of P1 + (P2 + P3)' % which)
    c.write('id_assoc_%s.bend' % which, '# Associativity of the addition, coordinate %s.\n' % which)
    return np


def gen_fracs():
    c = Ctx(['n', 'dn', 'iv', 'x'])
    n, dn, iv, x = c.vars('n', 'dn', 'iv', 'x')
    one = c.const(1)
    c.conseq('frac_mul', c.sub(c.mul(c.mul(n, iv), dn), n), [(c.mul(dn, iv), one, n)], (), 'dn iv == 1: (n iv) dn == n')
    c.conseq('frac_val', c.sub(c.mul(n, iv), x), [(n, c.mul(x, dn), iv), (c.mul(dn, iv), one, x)], (), 'n == x dn and dn iv == 1: n iv == x')
    c.write('id_frac.bend', '# Fractions n / dn = n iv with dn iv == 1.\n')
    c = Ctx(['n1', 'd1', 'i1', 'n2', 'd2', 'i2'])
    n1, d1, i1, n2, d2, i2 = c.vars('n1', 'd1', 'i1', 'n2', 'd2', 'i2')
    one = c.const(1)
    c.conseq('frac_eq', c.sub(c.mul(n1, i1), c.mul(n2, i2)),
             [(c.mul(n1, d2), c.mul(n2, d1), c.mul(i1, i2)), (c.mul(d2, i2), one, neg(c, c.mul(n1, i1))), (c.mul(d1, i1), one, c.mul(n2, i2))], (),
             'n1 d2 == n2 d1, d1 i1 == 1 and d2 i2 == 1: n1 i1 == n2 i2')
    c.write('id_frac2.bend', '# Equal fractions.\n')
    c = Ctx(['a', 'b', 'k'])
    a, b, k = c.vars('a', 'b', 'k')
    one = c.const(1)
    aa, bb = c.mul(a, a), c.mul(b, b)
    c.conseq('ns_alg', c.sub(k, one), [(aa, one, one), (aa, c.mul(k, bb), neg(c, one)), (bb, one, neg(c, k))], (),
             'a a == 1, a a == k (b b) and b b == 1: k == 1')
    c.write('id_ns.bend', '# Euler\'s criterion, the algebra: a = v^h, b = u^h, k = d^h.\n')


def lin_rule(c, v, F, h):
    """v -> F (a variable that is a product of others), from h : v == F (mod m)"""
    return c.rule(v, F, h)


def gen_ext():
    # T == (x y) Z from T Z == X Y, X == x Z, Y == y Z (then cancel Z)
    c = Ctx(['xx', 'yy', 'zz', 'tt', 'x', 'y'])
    X, Y, Z, T, x, y = c.vars('xx', 'yy', 'zz', 'tt', 'x', 'y')
    c.conseq('t_rule', c.mul(c.sub(T, c.mul(c.mul(x, y), Z)), Z),
             [(c.mul(T, Z), c.mul(X, Y), c.const(1)), (X, c.mul(x, Z), Y), (Y, c.mul(y, Z), c.mul(x, Z))], (),
             'T Z == X Y, X == x Z and Y == y Z: (T - (x y) Z) Z == 0')
    c.write('id_ext_t.bend', '# The T coordinate of a valid extended point.\n')
    # RFC 8032 addition
    c = Ctx(['x1', 'y1', 'z1', 't1', 'x2', 'y2', 'z2', 't2', 'd', 'u1', 'v1', 'u2', 'v2'])
    X1, Y1, Z1, T1, X2, Y2, Z2, T2, d, x1, y1, x2, y2 = c.vars('x1', 'y1', 'z1', 't1', 'x2', 'y2', 'z2', 't2', 'd', 'u1', 'v1', 'u2', 'v2')
    rules = [lin_rule(c, X1, c.mul(x1, Z1), 'hx1'), lin_rule(c, Y1, c.mul(y1, Z1), 'hy1'), lin_rule(c, T1, c.mul(c.mul(x1, y1), Z1), 'ht1'),
             lin_rule(c, X2, c.mul(x2, Z2), 'hx2'), lin_rule(c, Y2, c.mul(y2, Z2), 'hy2'), lin_rule(c, T2, c.mul(c.mul(x2, y2), Z2), 'ht2')]
    ea = c.mul(c.sub(Y1, X1), c.sub(Y2, X2))
    eb = c.mul(c.add(Y1, X1), c.add(Y2, X2))
    ec = c.mul(c.mul(T1, c.add(d, d)), T2)
    ed = c.mul(c.add(Z1, Z1), Z2)
    ee, ef, eg, eh = c.sub(eb, ea), c.sub(ed, ec), c.add(ed, ec), c.add(eb, ea)
    aX, aY, aZ, aT = c.specdef('ax', c.mul(ee, ef)), c.specdef('ay', c.mul(eg, eh)), c.specdef('az', c.mul(ef, eg)), c.specdef('at', c.mul(ee, eh))
    nx, dx, ny, dy = parts(c, (x1, y1), (x2, y2), d)
    c.ident('add_x', c.mul(aX, dx), c.mul(nx, aZ), rules, 'X3 dx == nx Z3 (X3 / Z3 is the x of the affine sum)')
    c.ident('add_y', c.mul(aY, dy), c.mul(ny, aZ), rules, 'Y3 dy == ny Z3')
    zz = c.mul(Z1, Z2)
    c.ident('add_z', aZ, c.mul(c.mul(c.mul(c.const(2), c.const(2)), c.mul(zz, zz)), c.mul(dx, dy)), rules, 'Z3 == 4 (Z1 Z2)^2 (dx dy)')
    c.ident('add_t', c.mul(aT, aZ), c.mul(aX, aY), (), 'T3 Z3 == X3 Y3')
    c.write('id_ext_add.bend', '# RFC 8032 point addition in extended coordinates is the affine addition.\n')
    # RFC 8032 doubling
    c = Ctx(['x1', 'y1', 'z1', 'd', 'e', 'u', 'v'])
    X1, Y1, Z1, d, e, x, y = c.vars('x1', 'y1', 'z1', 'd', 'e', 'u', 'v')
    rules = [lin_rule(c, X1, c.mul(x, Z1), 'hx1'), lin_rule(c, Y1, c.mul(y, Z1), 'hy1'), curve_rule(c, (x, y), e, 'h'), de_rule(c, d, e, 'hde')]
    ea, eb = c.mul(X1, X1), c.mul(Y1, Y1)
    z2 = c.mul(Z1, Z1)
    ec = c.add(z2, z2)
    eh = c.add(ea, eb)
    xy = c.add(X1, Y1)
    ee = c.sub(eh, c.mul(xy, xy))
    eg = c.sub(ea, eb)
    ef = c.add(ec, eg)
    dX, dY, dZ, dT = c.specdef('dbx', c.mul(ee, ef)), c.specdef('dby', c.mul(eg, eh)), c.specdef('dbz', c.mul(ef, eg)), c.specdef('dbt', c.mul(ee, eh))
    nx, dx, ny, dy = parts(c, (x, y), (x, y), d)
    c.ident('dbl_x', c.mul(dX, dx), c.mul(nx, dZ), rules, 'X3 dx == nx Z3 for the doubling (P on the curve)')
    c.ident('dbl_y', c.mul(dY, dy), c.mul(ny, dZ), rules, 'Y3 dy == ny Z3')
    c.ident('dbl_z', c.sub(c.zero(), dZ), c.mul(c.mul(z2, z2), c.mul(dx, dy)), rules, '-Z3 == Z1^4 (dx dy)')
    c.ident('dbl_t', c.mul(dT, dZ), c.mul(dX, dY), (), 'T3 Z3 == X3 Y3')
    c.write('id_ext_dbl.bend', '# RFC 8032 point doubling in extended coordinates is the affine doubling.\n')


def gen_dec():
    # x recovery (RFC 8032 section 5.1.3): u = y^2 - 1, v = d y^2 + 1
    c = Ctx(['x', 'y', 'd', 'w', 'r'])
    x, y, d, w, r = c.vars('x', 'y', 'd', 'w', 'r')
    one = c.const(1)
    u = c.specdef('du', c.sub(c.sq(y), one))
    v = c.specdef('dv', c.add(c.mul(d, c.sq(y)), one))
    c.conseq('dec_uv', c.sub(u, c.mul(v, c.sq(x))), [(lhs(c, (x, y)), rhs(c, (x, y), d), one)], (), '(x, y) on the curve: u == v x^2')
    rw = [lin_rule(c, w, one, 'hw')]
    c.conseq('dec_on', c.sub(lhs(c, (c.mul(r, w), c.mul(y, w))), rhs(c, (c.mul(r, w), c.mul(y, w)), d)), [(c.mul(v, c.sq(r)), u, neg(c, one))], rw,
             'v r^2 == u and w == 1: (r w, y w) is on the curve')
    c.ident('dec_negsq', c.mul(v, c.sq(neg(c, r))), c.mul(v, c.sq(r)), (), 'v (-r)^2 == v r^2')
    c.ident('dec_t', c.mul(c.mul(r, y), one), c.mul(r, y), (), '(r y) 1 == r y')
    c.ident('dec_nn', neg(c, neg(c, x)), x, (), '-(-x) == x')
    c.conseq('dec_pm', c.mul(c.mul(c.sub(r, x), c.add(r, x)), v), [(c.mul(v, c.sq(r)), u, one), (u, c.mul(v, c.sq(x)), one)], (), 'v r^2 == u == v x^2: (r - x) (r + x) v == 0')
    c.conseq('dec_x0', neg(c, x), [(x, c.zero(), neg(c, one))], (), 'x == 0: -x == 0')
    c.conseq('dec_r0', x, [(r, c.zero(), one), (c.sub(r, x), c.zero(), neg(c, one))], (), 'r == 0 and r - x == 0: x == 0')
    c.conseq('dec_r0n', x, [(r, c.zero(), neg(c, one)), (c.add(r, x), c.zero(), one)], (), 'r == 0 and r + x == 0: x == 0')
    c.write('id_dec.bend', '# Point decoding: the recovered x is on the curve.\n')
    # the candidate root xc = (u v^3) g with g = (u v^7)^((p - 5) / 8)
    c = Ctx(['u', 'v', 'g', 'x', 'i', 'ww', 'xc'])
    u, v, g, x, i, W, xc = c.vars('u', 'v', 'g', 'x', 'i', 'ww', 'xc')
    one = c.const(1)
    v3 = c.mul(c.mul(v, v), v)
    v7 = c.mul(c.mul(v3, v3), v)
    b = c.specdef('db', c.mul(u, v7))
    a = c.specdef('da', c.mul(x, c.mul(c.mul(v, v), c.mul(v, v))))
    cand = c.specdef('dc', c.mul(c.mul(u, v3), g))
    c.conseq('dec_b', c.sub(b, c.sq(a)), [(u, c.mul(v, c.sq(x)), v7)], (), 'u == v x^2: u v^7 == (x v^4)^2')
    c.conseq('dec_vxx', c.sub(c.mul(v, c.sq(cand)), c.mul(u, W)), [(c.mul(b, c.mul(g, g)), W, u)], (), '(u v^7) g^2 == W: v xc^2 == u W')
    c.conseq('dec_w2', c.mul(c.sub(W, one), c.add(W, one)), [(c.mul(W, W), one, one)], (), 'W^2 == 1: (W - 1) (W + 1) == 0')
    c.conseq('dec_wp', c.sub(c.mul(u, W), u), [(c.sub(W, one), c.zero(), u)], (), 'W - 1 == 0: u W == u')
    c.conseq('dec_wm', c.sub(c.mul(u, W), neg(c, u)), [(c.add(W, one), c.zero(), u)], (), 'W + 1 == 0: u W == -u')
    c.conseq('dec_r2', c.sub(c.mul(v, c.sq(c.mul(xc, i))), u), [(c.add(c.sq(i), one), c.zero(), c.mul(v, c.sq(xc))), (c.mul(v, c.sq(xc)), neg(c, u), neg(c, one))], (),
             'i^2 + 1 == 0 and v xc^2 == -u: v (xc i)^2 == u')
    c.conseq('dec_c0', cand, [(u, c.zero(), c.mul(v3, g))], (), 'u == 0: xc == 0')
    c.conseq('dec_u0', u, [(u, c.mul(v, c.sq(x)), one), (x, c.zero(), c.mul(v, x))], (), 'u == v x^2 and x == 0: u == 0')
    c.conseq('dec_a0', x, [(a, c.zero(), one)], (), 'placeholder')  if False else None
    c.write('id_dec2.bend', '# Point decoding: the candidate square root.\n')


GENS = {'dec': gen_dec, 'ext': gen_ext, 'frac': gen_fracs, 'rule': gen_rule, 'comm': gen_comm, 'unit': gen_unit, 'closure': gen_closure, 'compl': gen_compl,
        'assoc_x': lambda: gen_assoc('x'), 'assoc_y': lambda: gen_assoc('y')}

if __name__ == '__main__':
    for nm in (sys.argv[1:] or list(GENS)):
        print(nm, GENS[nm]())
