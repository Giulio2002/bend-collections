"""Reference arithmetic and literals for the point computations (gen_pt.py)."""
P = 2**256 - 2**32 - 977
N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
GX = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
GY = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8
BETA = 0x7ae96a2b657c07106e64479eac3434e99cf0497512f58995c1396c28719501ee
LAM = 0x5363ad4cc05c30e0a5261c028812645a122e22ea20816678df02967c1b23bd72
ADD = [('M',0,3),('M',1,4),('M',2,5),('A',0,1),('A',3,4),('M',10,11),('A',7,8),('S',12,13),('A',1,2),('A',4,5),('M',15,16),('A',8,9),('S',17,18),('A',0,2),('A',3,5),('M',20,21),('A',7,9),('S',22,23),('A',7,7),('A',25,7),('M',6,9),('A',8,27),('S',8,27),('M',6,24),('M',19,30),('M',14,29),('S',32,31),('M',30,26),('M',29,28),('A',35,34),('M',26,14),('M',28,19),('A',38,37)]
DBL = [('M',1,1),('A',4,4),('A',5,5),('A',6,6),('M',1,2),('M',2,2),('M',3,9),('M',10,7),('A',4,10),('M',8,7),('A',10,10),('A',14,10),('S',4,15),('M',16,12),('A',11,17),('M',0,1),('M',16,19),('A',20,20)]


def run(prog, regs):
    regs = list(regs)
    for op, i, j in prog:
        a, b = regs[i], regs[j]
        regs.append((a + b) % P if op == 'A' else (a - b) % P if op == 'S' else a * b % P)
    return regs


def padd(a, b):
    r = run(ADD, list(a) + list(b) + [21])
    return (r[33], r[36], r[39])


def pdbl(a):
    r = run(DBL, list(a) + [21])
    return (r[21], r[18], r[13])


def lmul(bits, g, r):
    for b in bits:
        r = pdbl(r)
        if b:
            r = padd(r, g)
    return r


def bits_of(k, n):
    return [(k >> i) & 1 for i in range(n - 1, -1, -1)]


def lit(v, pre='B.'):
    s = pre + 'BZ{}'
    bs = []
    while v:
        bs.append(v & 1)
        v >>= 1
    for b in reversed(bs):
        s = (pre + 'B1{%s}' if b else pre + 'B0{%s}') % s
    return s


def bp(pt, pre='B.', m='M.'):
    return '%sBP{%s, %s, %s}' % (m, lit(pt[0], pre), lit(pt[1], pre), lit(pt[2], pre))
