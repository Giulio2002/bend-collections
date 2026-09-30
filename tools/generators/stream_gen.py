#!/usr/bin/env python3
"""Generate the streaming hash cores src/crypto/{sha,sha512,sha3}/stream.bend
and their proofs (proofs/crypto/{sha512,sha3}/stream.bend,
proofs/crypto/hash/stream256.bend, proofs/crypto/hash/incremental.bend).

  python3 tools/generators/stream_gen.py [outdir]

A stream state holds the chaining value, the words read but not yet
compressed (fewer than one block), the bytes of an unfinished word (fewer
than a word) and the number of bytes already compressed. update reads the
new bytes once, a word at a time, into a word list that ends with the
unfinished bytes (Words: WC{w, rest} | WE{rem}), prepends the pending words,
and compresses every whole block; finish pads the pending words and bytes
with the total length and runs the algorithm's block loop on them.
"""
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]

# ---------------------------------------------------------------- padding lanes

LZ = {
    'sha256': dict(LWf='lanes', ZERO='0', ZO='N.zeros_onto', ZOc='zeros_onto', LWp='N.lanes(%s)',
                   tail='lzp(List.append(&2, U32, rem, [128]), Nat.mod(Nat.sub(119n, Nat.mod(len, 64n)), 64n), C.bit_length(len))'),
    'sha512': dict(LWf='C.lanes', ZERO='T.W{0, 0}', ZO='C.zeros_onto', ZOc='C.zeros_onto', LWp='C.lanes(%s)',
                   tail='lzp(List.append(&2, U32, rem, [128]), C.zeros(Nat.mod(len, 128n)), C.base256_onto(15n, Nat.div(len, 32n), [U32.shln(U32.from_nat(Nat.mod(len, 32n)), 3n)]))'),
    'sha3': dict(LWf='C.lanes', ZERO='T.W{0, 0}', ZO='N.zeros_onto', ZOc='zeros_onto', LWp='C.lanes(%s)',
                 tail='tl(Nat.sub(136n, Nat.mod(len, 136n)), rem)'),
}


def lzp_code(name, a):
    z = LZ[name]
    u = a['u']
    b = ['b%d' % i for i in range(u)]
    ks = ''.join('    case %dn:\n      %s(%s(%dn, sfx))\n' % (c, z['LWf'], z['ZOc'], c) for c in range(u))
    rows = ''
    for m in range(1, u):
        rows += '    case %s <> Nil{} %dn+j:\n      %s <> lz0(j, sfx)\n' % (' <> '.join(b[:m]), u - m, a['pack'](b[:m] + ['0'] * (u - m)))
    out = '''
# lanes(k zero bytes ++ sfx), a whole zero word at a time.
def lz0(k: Nat, sfx: List<&2, U32>) -> List<&2, %(W)s>:
  match k:
%(ks)s    case %(u)dn+j:
      %(ZERO)s <> lz0(j, sfx)

# lanes(prefix ++ k zeros ++ sfx), the words of a padding, without building
# the zero bytes: the prefix's word completed with zeros, then lz0.
def lzp(prefix: List<&2, U32>, k: Nat, sfx: List<&2, U32>) -> List<&2, %(W)s>:
  match prefix k:
    case Nil{} k2:
      lz0(k2, sfx)
    case %(bpat)s <> Nil{} k2:
      %(pack)s <> lz0(k2, sfx)
%(rows)s    case p k2:
      %(LWf)s(List.append(&2, U32, p, %(ZOc)s(k2, sfx)))
''' % dict(W=a['W'], ks=ks, u=u, ZERO=z['ZERO'], bpat=' <> '.join(b), pack=a['pack'](b), rows=rows,
           LWf=z['LWf'], ZOc=z['ZOc'])
    if name == 'sha3':
        out += '''
# lanes(rem ++ tail_fast(q)).
def tl(q: Nat, rem: List<&2, U32>) -> List<&2, T.Lane>:
  match q:
    case 0n:
      C.lanes(rem)
    case 1n:
      C.lanes(List.append(&2, U32, rem, [134]))
    case 2n+k:
      lzp(List.append(&2, U32, rem, [6]), k, [128])
'''
    out += '''
# The words of rem followed by the padding for a message of len bytes.
def tail_lanes(rem: List<&2, U32>, +len: Nat) -> List<&2, %(W)s>:
  %(tail)s
''' % dict(W=a['W'], tail=z['tail'])
    return out


def lzp_proofs(name, a):
    z = LZ[name]
    u = a['u']
    W = a['W']
    b = ['b%d' % i for i in range(u)]
    LW = lambda x: z['LWp'] % x
    ZO = z['ZO']
    zk = ''.join('    case %dn:\n      {==}\n' % c for c in range(u))
    rows = ''
    for m in range(1, u):
        P = ' <> '.join(b[:m] + ['Nil{}'])
        for c in range(u - m):
            rows += '    case %s %dn:\n      {==}\n' % (P, c)
        rows += '''    case %(P)s %(r)dn+j:
      %%lz0_correct(j, sfx) : {N.lzp(%(P)s, %(r)dn+j, sfx) == %(pk)s <> _ : List<&2, %(W)s>}
      {==}
''' % dict(P=P, r=u - m, pk=a['pack'](b[:m] + ['0'] * (u - m)), W=W)
    out = '''
law lz0_correct:
  for +k: Nat
  for +sfx: List<&2, U32>
  {N.lz0(k, sfx) == %(LZ)s : List<&2, %(W)s>}

def lz0_correct(k, sfx):
  match k:
%(zk)s    case %(u)dn+j:
      %%lz0_correct(j, sfx) : {N.lz0(%(u)dn+j, sfx) == %(ZERO)s <> _ : List<&2, %(W)s>}
      {==}

law lzp_correct:
  for +prefix: List<&2, U32>
  for +k: Nat
  for +sfx: List<&2, U32>
  {N.lzp(prefix, k, sfx) == %(LG)s : List<&2, %(W)s>}

def lzp_correct(prefix, k, sfx):
  match prefix k:
    case Nil{} k2:
      lz0_correct(k2, sfx)
    case %(bpat)s <> Nil{} k2:
      %%lz0_correct(k2, sfx) : {N.lzp(%(bpat)s <> Nil{}, k2, sfx) == %(pack)s <> _ : List<&2, %(W)s>}
      {==}
%(rows)s    case %(bpat)s <> bx <> rest k2:
      {==}
''' % dict(LZ=LW('%s(k, sfx)' % ZO), W=W, zk=zk, u=u, ZERO=z['ZERO'],
           LG=LW('List.append(&2, U32, prefix, %s(k, sfx))' % ZO), bpat=' <> '.join(b),
           pack=a['pack'](b), rows=rows)
    if name == 'sha3':
        out += '''
law tl_correct:
  for +q: Nat
  for +rem: List<&2, U32>
  {N.tl(q, rem) == C.lanes(List.append(&2, U32, rem, N.tail_fast(q))) : List<&2, T.Lane>}

def tl_correct(q, rem):
  match q:
    case 0n:
      %Equal.sym(List<&2, U32>, List.append(&2, U32, rem, Nil{}), rem, L.append_nil(rem)) : {N.tl(0n, rem) == C.lanes(_) : List<&2, T.Lane>}
      {==}
    case 1n:
      {==}
    case 2n+k:
      Equal.trans(List<&2, T.Lane>, N.lzp(List.append(&2, U32, rem, [6]), k, [128]),
        C.lanes(List.append(&2, U32, List.append(&2, U32, rem, [6]), N.zeros_onto(k, [128]))),
        C.lanes(List.append(&2, U32, rem, 6 <> N.zeros_onto(k, [128]))),
        lzp_correct(List.append(&2, U32, rem, [6]), k, [128]),
        Equal.cong(List<&2, U32>, List<&2, T.Lane>, t => C.lanes(t),
          List.append(&2, U32, List.append(&2, U32, rem, [6]), N.zeros_onto(k, [128])),
          List.append(&2, U32, rem, 6 <> N.zeros_onto(k, [128])),
          L.append_assoc(rem, [6], N.zeros_onto(k, [128]))))

law tail_lanes_correct:
  for +rem: List<&2, U32>
  for +n: Nat
  {N.tail_lanes(rem, n) == C.lanes(List.append(&2, U32, rem, N.suffix_fast(n))) : List<&2, T.Lane>}

def tail_lanes_correct(rem, n):
  tl_correct(Nat.sub(136n, Nat.mod(n, 136n)), rem)
'''
    else:
        if name == 'sha512':
            zc, sfx, SUFF = 'C.zeros(Nat.mod(n, 128n))', 'C.base256_onto(15n, Nat.div(n, 32n), [U32.shln(U32.from_nat(Nat.mod(n, 32n)), 3n)])', 'C.suffix_fast(n)'
        else:
            zc, sfx, SUFF = 'Nat.mod(Nat.sub(119n, Nat.mod(n, 64n)), 64n)', 'C.bit_length(n)', 'N.suffix_fast(n)'
        out += '''
law tail_lanes_correct:
  for +rem: List<&2, U32>
  for +n: Nat
  {N.tail_lanes(rem, n) == %(R)s : List<&2, %(W)s>}

def tail_lanes_correct(rem, n):
  +zc = %(zc)s
  +sf = {%(sfx)s : List<&2, U32>}
  Equal.trans(List<&2, %(W)s>, N.lzp(List.append(&2, U32, rem, [128]), zc, sf),
    %(M)s, %(R)s,
    lzp_correct(List.append(&2, U32, rem, [128]), zc, sf),
    Equal.cong(List<&2, U32>, List<&2, %(W)s>, t => %(Lt)s,
      List.append(&2, U32, List.append(&2, U32, rem, [128]), %(ZO)s(zc, sf)),
      List.append(&2, U32, rem, 128 <> %(ZO)s(zc, sf)),
      L.append_assoc(rem, [128], %(ZO)s(zc, sf))))
''' % dict(W=W, zc=zc, sfx=sfx, ZO=ZO, R=LW('List.append(&2, U32, rem, %s)' % SUFF),
           M=LW('List.append(&2, U32, List.append(&2, U32, rem, [128]), %s(zc, sf))' % ZO), Lt=LW('t'))
    return out


ZEROS = '''
# k zero bytes onto acc.
def zeros_onto(k: Nat, acc: List<&2, U32>) -> List<&2, U32>:
  match k:
    case 0n:
      acc
    case 1n+p:
      0 <> zeros_onto(p, acc)
'''

ALGS = {
    'sha256': dict(
        dir='sha', imports='import ./state.bend as T\nimport ./core.bend as C\nimport ./sha256.bend as SHA\n',
        W='U32', S='T.State', u=4, n=16, B=64, Q='48n',
        pack=lambda b: 'C.pack(%s)' % ', '.join(b),
        compress=lambda ws: 'C.fips_compress16(%s, q, s)' % ', '.join(ws),
        init='C.initial()',
        finish='SHA.digest_bytes(C.digest(blocks(List.append(&2, U32, pend, tail_lanes(rem, len)), q, s)))',
        extra=ZEROS + '''
# C.suffix(n) (0x80, zeros, the 64-bit bit length), with no list appended.
def suffix_fast(+n: Nat) -> List<&2, U32>:
  128 <> zeros_onto(Nat.mod(Nat.sub(119n, Nat.mod(n, 64n)), 64n), C.bit_length(n))

# The words of a byte list (a trailing partial word dropped), and the block
# loop over words: the finishing path (at most two blocks).
def lanes(bytes: List<&2, U32>) -> List<&2, U32>:
  match bytes:
    case a <> b <> c <> d <> rest:
      C.pack(a, b, c, d) <> lanes(rest)
    case _:
      Nil{}

def blocks(ws: List<&2, U32>, +q: Nat, s: T.State) -> T.State:
  match ws:
    case %(W16)s <> rest:
      blocks(rest, q, C.fips_compress16(%(A16)s, q, s))
    case _:
      s
''' % dict(W16=' <> '.join('w%d' % i for i in range(16)), A16=', '.join('w%d' % i for i in range(16))),
        doc='SHA-256 (FIPS 180-4)'),
    'sha512': dict(
        dir='sha512', imports='import ./types.bend as T\nimport ./core.bend as C\n',
        W='T.Lane', S='T.State', u=8, n=16, B=128, Q='64n',
        pack=lambda b: 'T.W{C.pack(%s), C.pack(%s)}' % (', '.join(b[:4]), ', '.join(b[4:])),
        compress=lambda ws: 'C.fips16(%s, q, s)' % ', '.join(ws),
        init='C.initial()',
        finish='C.digest_bytes(blocks(List.append(&2, T.Lane, pend, tail_lanes(rem, len)), q, s))',
        extra='''
# The block loop with the FIPS-specialized compression: the finishing path.
def blocks(ws: List<&2, T.Lane>, +q: Nat, s: T.State) -> T.State:
  match ws:
    case %(W16)s <> rest:
      blocks(rest, q, C.fips16(%(A16)s, q, s))
    case _:
      s
''' % dict(W16=' <> '.join('w%d' % i for i in range(16)), A16=', '.join('w%d' % i for i in range(16))),
        doc='SHA-512 (FIPS 180-4)'),
    'sha3': dict(
        dir='sha3', imports='import ../keccak/types.bend as T\nimport ../keccak/permutation.bend as P\nimport ./core.bend as C\n',
        W='T.Lane', S='T.State', u=8, n=17, B=136, Q='24n',
        pack=lambda b: 'T.W{C.pack(%s), C.pack(%s)}' % (', '.join(b[:4]), ', '.join(b[4:])),
        compress=lambda ws: 'P.rounds(q, 0n, C.inject(s, %s))' % ', '.join(ws),
        init='C.zero()',
        finish='C.digest_bytes(C.absorb(List.append(&2, T.Lane, pend, tail_lanes(rem, len)), q, s))',
        extra=ZEROS + '''
# C.suffix(n) (0x06, zeros, 0x80 to the end of the block), with no list appended.
def tail_fast(q: Nat) -> List<&2, U32>:
  match q:
    case 0n:
      Nil{}
    case 1n:
      [134]
    case 2n+k:
      6 <> zeros_onto(k, [128])

def suffix_fast(+n: Nat) -> List<&2, U32>:
  tail_fast(Nat.sub(136n, Nat.mod(n, 136n)))
''',
        doc='SHA3-256 (FIPS 202)'),
}


def stream(name, a):
    u, n, W = a['u'], a['n'], a['W']
    b = ['b%d' % i for i in range(u)]
    ws = ['w%d' % i for i in range(n)]
    nest = ''
    for w in ws:
        nest += 'WC{%s, ' % w
    nest += 'rest' + '}' * n
    return '''# Generated by tools/generators/stream_gen.py; do not edit by hand.
import Base
%(imports)s
# %(doc)s over a stream of byte chunks (see tools/generators/stream_gen.py).

# The words of a byte list, then the bytes of its unfinished word.
type Words is Data:
  WC{w: %(W)s, t: Words}
  WE{rem: List<&2, U32>}

# Chaining value, pending words (< %(n)d), unfinished word's bytes (< %(u)d),
# bytes already compressed.
type St is Data:
  St{s: %(S)s, pend: List<&2, %(W)s>, rem: List<&2, U32>, done: Nat}

def words(bytes: List<&2, U32>) -> Words:
  match bytes:
    case %(bpat)s <> rest:
      WC{%(pack)s, words(rest)}
    case _:
      WE{bytes}

def pre(ws: List<&2, %(W)s>, wl: Words) -> Words:
  match ws:
    case Nil{}:
      wl
    case w <> t:
      WC{w, pre(t, wl)}

def pend_of(wl: Words) -> List<&2, %(W)s>:
  match wl:
    case WC{w, t}:
      w <> pend_of(t)
    case WE{r}:
      Nil{}

def rem_of(wl: Words) -> List<&2, U32>:
  match wl:
    case WC{w, t}:
      rem_of(t)
    case WE{r}:
      r

def stop(+wl: Words, s: %(S)s, done: Nat) -> St:
  St{s, pend_of(wl), rem_of(wl), done}

# Compress every whole block of %(n)d words.
def run(wl: Words, +q: Nat, s: %(S)s, +done: Nat) -> St:
  match wl:
    case %(nest)s:
      run(rest, q, %(compress)s, Nat.add(%(B)dn, done))
    case _:
      stop(wl, s, done)

%(extra)s%(lzp)s
def new() -> St:
  St{%(init)s, Nil{}, Nil{}, 0n}

# q is the algorithm's round parameter (%(Q)s), a variable for the proofs.
def update(st: St, xs: List<&2, U32>, +q: Nat) -> St:
  match st:
    case St{s, pend, rem, done}:
      run(pre(pend, words(List.append(&2, U32, rem, xs))), q, s, done)

def word_bytes(ws: List<&2, %(W)s>) -> Nat:
  match ws:
    case Nil{}:
      0n
    case w <> t:
      Nat.add(%(u)dn, word_bytes(t))

def finish(st: St, +q: Nat) -> List<&2, U32>:
  match st:
    case St{s, +pend, +rem, done}:
      +len = Nat.add(done, Nat.add(word_bytes(pend), List.length(&2, U32, rem)))
      %(finish)s

def hash(bytes: List<&2, U32>) -> List<&2, U32>:
  finish(update(new(), bytes, %(Q)s), %(Q)s)
''' % dict(a, extra=a.get('extra', ''), lzp=lzp_code(name, a), bpat=' <> '.join(b), pack=a['pack'](b), nest=nest, compress=a['compress'](ws))


# ---------------------------------------------------------------- proofs

PROOF = {
    'sha512': dict(
        out='proofs/crypto/sha512/stream.bend',
        imports='''import ../../../src/crypto/sha512/types.bend as T
import ../../../src/crypto/sha512/core.bend as C
import ../../../src/crypto/sha512/stream.bend as N
import ./fast.bend as FP
import ../hash/lists.bend as L
''',
        LW='C.lanes(%s)', Gw='C.blocks(%s, %s, C.round_constants(), %s)',
        brw='FP.fips16_correct(%s, q, s)',
        NB='N.blocks(%s, %s, %s)', DIG='C.digest_bytes(%s)',
        SUFF='C.suffix_fast(%s)', SUF='C.suffix(%s)', sufeq='FP.suffix_fast_correct(%s)',
        INIT='C.initial()', Fone='C.sha512(%s)'),
    'sha3': dict(
        out='proofs/crypto/sha3/stream.bend',
        imports='''import ../../../src/crypto/keccak/types.bend as T
import ../../../src/crypto/keccak/permutation.bend as P
import ../../../src/crypto/sha3/core.bend as C
import ../../../src/crypto/sha3/stream.bend as N
import ../hash/lists.bend as L
''',
        LW='C.lanes(%s)', Gw='C.absorb(%s, %s, %s)', brw=None,
        NB=None, DIG='C.digest_bytes(%s)',
        SUFF='N.suffix_fast(%s)', SUF='C.suffix(%s)', sufeq='suffix_fast_correct(%s)',
        INIT='C.zero()', Fone='C.keccak(%s, 24n)'),
    'sha256': dict(
        out='proofs/crypto/hash/stream256.bend',
        imports='''import ../../../src/crypto/sha/state.bend as T
import ../../../src/crypto/sha/core.bend as C
import ../../../src/crypto/sha/sha256.bend as SHA
import ../../../src/crypto/sha/stream.bend as N
import ./lists.bend as L
''',
        LW='N.lanes(%s)', Gw='N.blocks(%s, %s, %s)', brw=None,
        NB=None, DIG='SHA.digest_bytes(C.digest(%s))',
        SUFF='N.suffix_fast(%s)', SUF='C.suffix(%s)', sufeq='suffix_fast_correct(%s)',
        INIT='C.initial()', Fone=None),
}


def app(u, v):
    return 'List.append(&2, U32, %s, %s)' % (u, v)


def wapp(W, u, v):
    return 'List.append(&2, %s, %s, %s)' % (W, u, v)


def stream_proofs(name, a, p):
    u, n, W, B, Q = a['u'], a['n'], a['W'], a['B'], a['Q']
    S = a['S']
    LW = lambda x: p['LW'] % x
    Gw = lambda ws, q, s: p['Gw'] % (ws, q, s)
    DIG = lambda x: p['DIG'] % x
    b = ['b%d' % i for i in range(u)]
    ws = ['w%d' % i for i in range(n)]
    pack = a['pack'](b).replace('C.', 'C.') if name != 'sha256' else a['pack'](b)
    nest = ''.join('N.WC{%s, ' % w for w in ws) + 'rest' + '}' * n
    short_bytes = ''.join('    case %s:\n      {==}\n' % (' <> '.join(b[:k] + ['Nil{}'])) for k in range(u))
    short_wl = ''.join('    case %s:\n      {==}\n' % (''.join('N.WC{%s, ' % w for w in ws[:k]) + 'N.WE{r}' + '}' * k) for k in range(n))
    short_blocks = ''.join('    case %s:\n      {==}\n' % (' <> '.join(ws[:k] + ['Nil{}'])) for k in range(n))
    fast = a['compress'](ws)
    Rp = 'N.run(rest, q, %s, Nat.add(%dn, done))' % (fast, B)
    NBf = (lambda x, q, sv: p['NB'] % (x, q, sv)) if p['NB'] else Gw
    fin_expr = DIG(NBf(wapp(W, 'ppend(st)', 'N.tail_lanes(prem(st), lenof(st))'), 'q', 'sv(st)'))
    view = lambda st, z: Gw(wapp(W, 'ppend(%s)' % st, LW(app('prem(%s)' % st, z))), 'q', 'sv(%s)' % st)
    out = ['''# Generated by tools/generators/stream_gen.py; do not edit by hand.
import Base
%(imports)s
# The streaming %(doc)s of src/crypto/%(dir)s/stream.bend computes the
# block loop G over the whole input: with G(ws, s) the algorithm's block loop
# on a word list, a stream state (s, pend, rem) after the bytes so far
# satisfies, for every continuation z (the invariant of HACL*'s
# Hacl.Streaming.Functor),
#
#   G(words(bytes so far ++ z), initial) == G(pend ++ words(rem ++ z), s)
#
# and done + |pend| words + |rem| is the number of bytes so far. The round
# parameter q stays a variable in every lemma that unfolds a block.

def sv(st: N.St) -> %(S)s:
  match st:
    case N.St{s, pend, rem, done}:
      s

def ppend(st: N.St) -> List<&2, %(W)s>:
  match st:
    case N.St{s, pend, rem, done}:
      pend

def prem(st: N.St) -> List<&2, U32>:
  match st:
    case N.St{s, pend, rem, done}:
      rem

def lenof(st: N.St) -> Nat:
  match st:
    case N.St{s, +pend, +rem, done}:
      Nat.add(done, Nat.add(N.word_bytes(pend), List.length(&2, U32, rem)))

# The words a Words value stands for, followed by those of rem ++ z.
def wl_app(wl: N.Words, z: List<&2, U32>) -> List<&2, %(W)s>:
  match wl:
    case N.WC{w, t}:
      w <> wl_app(t, z)
    case N.WE{r}:
      %(LWrz)s

# The number of bytes a Words value stands for.
def wlen(wl: N.Words) -> Nat:
  match wl:
    case N.WC{w, t}:
      Nat.add(%(u)dn, wlen(t))
    case N.WE{r}:
      List.length(&2, U32, r)

law words_app:
  for +bytes: List<&2, U32>
  for +z: List<&2, U32>
  {%(LWbz)s == wl_app(N.words(bytes), z) : List<&2, %(W)s>}

def words_app(bytes, z):
  match bytes:
    case %(bpat)s <> rest:
      %%words_app(rest, z) :
        {%(LWbpz)s == %(pack)s <> _ : List<&2, %(W)s>}
      {==}
%(short_bytes)s
law words_len:
  for +bytes: List<&2, U32>
  {List.length(&2, U32, bytes) == wlen(N.words(bytes)) : Nat}

def words_len(bytes):
  match bytes:
    case %(bpat)s <> rest:
      %%words_len(rest) :
        {List.length(&2, U32, %(bpat)s <> rest) == Nat.add(%(u)dn, _) : Nat}
      {==}
%(short_bytes)s
law pre_app:
  for +ws: List<&2, %(W)s>
  for +wl: N.Words
  for +z: List<&2, U32>
  {wl_app(N.pre(ws, wl), z) == List.append(&2, %(W)s, ws, wl_app(wl, z)) : List<&2, %(W)s>}

def pre_app(ws, wl, z):
  match ws:
    case Nil{}:
      {==}
    case w <> t:
      %%pre_app(t, wl, z) : {wl_app(N.pre(w <> t, wl), z) == w <> _ : List<&2, %(W)s>}
      {==}

law pre_len:
  for +ws: List<&2, %(W)s>
  for +wl: N.Words
  {wlen(N.pre(ws, wl)) == Nat.add(N.word_bytes(ws), wlen(wl)) : Nat}

def pre_len(ws, wl):
  match ws:
    case Nil{}:
      {==}
    case w <> t:
      %%pre_len(t, wl) : {wlen(N.pre(w <> t, wl)) == Nat.add(%(u)dn, _) : Nat}
      {==}

law run_app:
  for +wl: N.Words
  for +q: Nat
  for +s: %(S)s
  for +done: Nat
  for +z: List<&2, U32>
  {%(Gwz)s == %(runview)s : %(S)s}

def run_app(wl, q, s, done, z):
  match wl:
    case %(nest)s:
%(runblock)s
%(short_wl)s
law run_len:
  for +wl: N.Words
  for +q: Nat
  for +s: %(S)s
  for +done: Nat
  {Nat.add(done, wlen(wl)) == lenof(N.run(wl, q, s, done)) : Nat}

def run_len(wl, q, s, done):
  match wl:
    case %(nest)s:
      Equal.trans(Nat, Nat.add(done, wlen(%(nest)s)),
        Nat.add(%(B)dn, Nat.add(done, wlen(rest))), lenof(%(Rp)s),
        L.add_swap(done, %(B)dn, wlen(rest)),
        run_len(rest, q, %(fast)s, Nat.add(%(B)dn, done)))
%(short_wl)s
# The stream state after each chunk in turn.
def fold_st(cs: List<&2, List<&2, U32>>, +q: Nat, st: N.St) -> N.St:
  match cs:
    case Nil{}:
      st
    case c <> ct:
      fold_st(ct, q, N.update(st, c, q))

law fold_inv:
  for +cs: List<&2, List<&2, U32>>
  for +q: Nat
  for +st: N.St
  for +z: List<&2, U32>
  {%(finv_l)s == %(finv_r)s : %(S)s}

def fold_inv(cs, q, st, z):
  match cs st:
    case Nil{} N.St{s, pend, rem, done}:
      {==}
    case c <> ct N.St{s, pend, rem, done}:
      +m = List.concat(&2, U32, ct)
      +mz = List.append(&2, U32, m, z)
      +rc = List.append(&2, U32, rem, c)
      +wd = N.words(rc)
      +r1 = N.run(N.pre(pend, wd), q, s, done)
      +x0 = %(x0)s
      +x1 = %(x1)s
      +x2 = %(x2)s
      +x3 = %(x3)s
      +x4 = %(x4)s
      +x5 = %(x5)s
      Equal.trans(%(S)s, x0, x1, x5,
        Equal.cong(List<&2, U32>, %(S)s, t => %(Gt1)s,
          %(l0)s, %(l2)s,
          Equal.trans(List<&2, U32>, %(l0)s, %(l1)s, %(l2)s,
            Equal.cong(List<&2, U32>, List<&2, U32>, t => List.append(&2, U32, rem, t),
              List.append(&2, U32, List.append(&2, U32, c, m), z), List.append(&2, U32, c, mz),
              L.append_assoc(c, m, z)),
            L.append_assoc_rev(rem, c, mz))),
        Equal.trans(%(S)s, x1, x2, x5,
          Equal.cong(List<&2, %(W)s>, %(S)s, t => %(Gt2)s, %(LWrcmz)s, wl_app(wd, mz), words_app(rc, mz)),
          Equal.trans(%(S)s, x2, x3, x5,
            Equal.cong(List<&2, %(W)s>, %(S)s, t => %(Gt3)s,
              List.append(&2, %(W)s, pend, wl_app(wd, mz)), wl_app(N.pre(pend, wd), mz),
              Equal.sym(List<&2, %(W)s>, wl_app(N.pre(pend, wd), mz), List.append(&2, %(W)s, pend, wl_app(wd, mz)), pre_app(pend, wd, mz))),
            Equal.trans(%(S)s, x3, x4, x5,
              run_app(N.pre(pend, wd), q, s, done, mz),
              fold_inv(ct, q, r1, z)))))

law fold_len:
  for +cs: List<&2, List<&2, U32>>
  for +q: Nat
  for +st: N.St
  {Nat.add(lenof(st), List.length(&2, U32, List.concat(&2, U32, cs))) == lenof(fold_st(cs, q, st)) : Nat}

def fold_len(cs, q, st):
  match cs st:
    case Nil{} N.St{s, pend, rem, done}:
      L.add_zero(lenof(N.St{s, pend, rem, done}))
    case c <> ct N.St{s, pend, rem, done}:
      +m = List.concat(&2, U32, ct)
      +rc = List.append(&2, U32, rem, c)
      +wd = N.words(rc)
      +r1 = N.run(N.pre(pend, wd), q, s, done)
      +wb = N.word_bytes(pend)
      +lr = List.length(&2, U32, rem)
      +lc = List.length(&2, U32, c)
      +lm = List.length(&2, U32, m)
      +k1 = Equal.trans(Nat, lenof(r1), Nat.add(done, wlen(N.pre(pend, wd))), Nat.add(done, Nat.add(wb, Nat.add(lr, lc))),
        Equal.sym(Nat, Nat.add(done, wlen(N.pre(pend, wd))), lenof(r1), run_len(N.pre(pend, wd), q, s, done)),
        Equal.trans(Nat, Nat.add(done, wlen(N.pre(pend, wd))), Nat.add(done, Nat.add(wb, wlen(wd))), Nat.add(done, Nat.add(wb, Nat.add(lr, lc))),
          Equal.cong(Nat, Nat, t => Nat.add(done, t), wlen(N.pre(pend, wd)), Nat.add(wb, wlen(wd)), pre_len(pend, wd)),
          Equal.trans(Nat, Nat.add(done, Nat.add(wb, wlen(wd))), Nat.add(done, Nat.add(wb, List.length(&2, U32, rc))), Nat.add(done, Nat.add(wb, Nat.add(lr, lc))),
            Equal.cong(Nat, Nat, t => Nat.add(done, Nat.add(wb, t)), wlen(wd), List.length(&2, U32, rc),
              Equal.sym(Nat, List.length(&2, U32, rc), wlen(wd), words_len(rc))),
            Equal.cong(Nat, Nat, t => Nat.add(done, Nat.add(wb, t)), List.length(&2, U32, rc), Nat.add(lr, lc),
              L.length_append(rem, c)))))
      +e = Equal.trans(Nat, Nat.add(Nat.add(done, Nat.add(wb, lr)), List.length(&2, U32, List.append(&2, U32, c, m))),
        Nat.add(Nat.add(done, Nat.add(wb, lr)), Nat.add(lc, lm)), Nat.add(lenof(r1), lm),
        Equal.cong(Nat, Nat, t => Nat.add(Nat.add(done, Nat.add(wb, lr)), t), List.length(&2, U32, List.append(&2, U32, c, m)), Nat.add(lc, lm),
          L.length_append(c, m)),
        Equal.trans(Nat, Nat.add(Nat.add(done, Nat.add(wb, lr)), Nat.add(lc, lm)), Nat.add(Nat.add(done, Nat.add(wb, Nat.add(lr, lc))), lm), Nat.add(lenof(r1), lm),
          L.add_regroup(done, wb, lr, lc, lm),
          Equal.cong(Nat, Nat, t => Nat.add(t, lm), Nat.add(done, Nat.add(wb, Nat.add(lr, lc))), lenof(r1),
            Equal.sym(Nat, lenof(r1), Nat.add(done, Nat.add(wb, Nat.add(lr, lc))), k1))))
      Equal.trans(Nat, Nat.add(Nat.add(done, Nat.add(wb, lr)), List.length(&2, U32, List.append(&2, U32, c, m))),
        Nat.add(lenof(r1), lm), lenof(fold_st(ct, q, r1)), e, fold_len(ct, q, r1))
%(extra)s
law finish_eta:
  for +st: N.St
  for +q: Nat
  {N.finish(st, q) == %(fin)s : List<&2, U32>}

def finish_eta(st, q):
  match st:
    case N.St{s, pend, rem, done}:
      {==}

''' % dict(
        imports=p['imports'], doc=a['doc'], dir=a['dir'], S=S, W=W, u=u, B=B, Q=Q,
        LWrz=LW(app('r', 'z')), LWbz=LW(app('bytes', 'z')), bpat=' <> '.join(b),
        LWbpz=LW(app(' <> '.join(b) + ' <> rest', 'z')), pack=pack, short_bytes=short_bytes,
        Gwz=Gw('wl_app(wl, z)', 'q', 's'), runview=view('N.run(wl, q, s, done)', 'z'),
        nest=nest, short_wl=short_wl, Rp=Rp, fast=fast,
        runblock=(('      %%%s :\n        {%s == %s : %s}\n' % (
            p['brw'] % ', '.join(ws), Gw('wl_app(rest, z)', 'q', '_'), view(Rp, 'z'), S)) if p['brw'] else '') +
                 '      run_app(rest, q, %s, Nat.add(%dn, done), z)' % (fast, B),
        finv_l=Gw(wapp(W, 'ppend(st)', LW(app('prem(st)', app('List.concat(&2, U32, cs)', 'z')))), 'q', 'sv(st)'),
        finv_r=view('fold_st(cs, q, st)', 'z'),
        x0=Gw(wapp(W, 'pend', LW(app('rem', app(app('c', 'm'), 'z')))), 'q', 's'),
        x1=Gw(wapp(W, 'pend', LW(app('rc', 'mz'))), 'q', 's'),
        x2=Gw(wapp(W, 'pend', 'wl_app(wd, mz)'), 'q', 's'),
        x3=Gw('wl_app(N.pre(pend, wd), mz)', 'q', 's'),
        x4=view('r1', 'mz'),
        x5=view('fold_st(ct, q, r1)', 'z'),
        Gt1=Gw(wapp(W, 'pend', LW('t')), 'q', 's'),
        l0=app('rem', app(app('c', 'm'), 'z')), l1=app('rem', app('c', 'mz')), l2=app('rc', 'mz'),
        Gt2=Gw(wapp(W, 'pend', 't'), 'q', 's'), LWrcmz=LW(app('rc', 'mz')),
        Gt3=Gw('t', 'q', 's'),
        extra=extra_text(name, a, p, W) + lzp_proofs(name, a),
        fin=fin_expr)]
    out.append(tail(name, a, p, W, Q, LW, Gw, DIG))
    return ''.join(out)


def fone(name, m, LW, Gw, DIG, p, Q):
    if name == 'sha512':
        return 'C.sha512(%s)' % m
    if name == 'sha3':
        return 'C.keccak(%s, 24n)' % m
    return DIG(Gw(LW(app(m, p['SUF'] % ('List.length(&2, U32, %s)' % m))), Q, p['INIT']))


def tail(name, a, p, W, Q, LW, Gw, DIG):
    SUFF = lambda x: p['SUFF'] % x
    SUF = lambda x: p['SUF'] % x
    NB = (lambda x, q, sv: p['NB'] % (x, q, sv)) if p['NB'] else Gw
    Xf = wapp(W, 'ppend(st)', LW(app('prem(st)', SUFF('lenof(st)'))))
    Xs = wapp(W, 'ppend(st)', LW(app('prem(st)', SUF('lenof(st)'))))
    Xm = wapp(W, 'ppend(st)', LW(app('prem(st)', 'z')))
    Xi = LW(app('m', 'z'))
    Fm = fone(name, 'm', LW, Gw, DIG, p, Q)
    terms, proofs = [], []
    Xt = wapp(W, 'ppend(st)', 'N.tail_lanes(prem(st), lenof(st))')
    terms.append(DIG(NB(Xt, Q, 'sv(st)')))
    proofs.append('finish_eta(st, %s)' % Q)
    terms.append(DIG(NB(Xf, Q, 'sv(st)')))
    proofs.append('Equal.cong(List<&2, %s>, List<&2, U32>, t => %s, %s, %s, tail_lanes_correct(prem(st), lenof(st)))' % (
        W, DIG(NB(wapp(W, 'ppend(st)', 't'), Q, 'sv(st)')), 'N.tail_lanes(prem(st), lenof(st))',
        LW(app('prem(st)', SUFF('lenof(st)')))))
    if p['NB']:
        terms.append(DIG(Gw(Xf, Q, 'sv(st)')))
        proofs.append('Equal.cong(%s, List<&2, U32>, t => %s, %s, %s, sblocks(%s, %s, sv(st)))' % (
            a['S'], DIG('t'), NB(Xf, Q, 'sv(st)'), Gw(Xf, Q, 'sv(st)'), Xf, Q))
    terms.append(DIG(Gw(Xs, Q, 'sv(st)')))
    proofs.append('Equal.cong(List<&2, U32>, List<&2, U32>, t => %s, %s, %s, %s)' % (
        DIG(Gw(wapp(W, 'ppend(st)', LW(app('prem(st)', 't'))), Q, 'sv(st)')), SUFF('lenof(st)'), SUF('lenof(st)'),
        p['sufeq'] % 'lenof(st)'))
    terms.append(DIG(Gw(Xm, Q, 'sv(st)')))
    proofs.append('Equal.cong(Nat, List<&2, U32>, t => %s, lenof(st), List.length(&2, U32, m), Equal.sym(Nat, Nat.add(lenof(N.new()), List.length(&2, U32, m)), lenof(st), fold_len(cs, %s, N.new())))' % (
        DIG(Gw(wapp(W, 'ppend(st)', LW(app('prem(st)', SUF('t')))), Q, 'sv(st)')), Q))
    terms.append(Fm)
    proofs.append('Equal.cong(%s, List<&2, U32>, t => %s, %s, %s, Equal.sym(%s, %s, %s, fold_inv(cs, %s, N.new(), z)))' % (
        a['S'], DIG('t'), Gw(Xm, Q, 'sv(st)'), Gw(Xi, Q, p['INIT']), a['S'],
        Gw(wapp(W, 'ppend(N.new())', LW(app('prem(N.new())', app('m', 'z')))), Q, 'sv(N.new())'), Gw(Xm, Q, 'sv(st)'), Q))
    # fold into nested trans from the goal's left side N.finish(st, Q)
    left = 'N.finish(st, %s)' % Q
    chain = None
    seq = [left] + terms
    def build(i):
        if i == len(proofs) - 1:
            return proofs[i]
        return 'Equal.trans(List<&2, U32>, %s, %s, %s,\n    %s,\n    %s)' % (seq[i], seq[i + 1], Fm, proofs[i], build(i + 1))
    return """
# The stream over every chunk, finished, is the padded block loop over their
# concatenation: the implementation's one-shot hash.
law stream_correct:
  for +cs: List<&2, List<&2, U32>>
  {N.finish(fold_st(cs, %(Q)s, N.new()), %(Q)s) == %(Fcs)s : List<&2, U32>}

def stream_correct(cs):
  +m = List.concat(&2, U32, cs)
  +st = fold_st(cs, %(Q)s, N.new())
  +z = %(z)s
  %(body)s

law hash_correct:
  for +bytes: List<&2, U32>
  {N.hash(bytes) == %(Fb)s : List<&2, U32>}

def hash_correct(bytes):
  %%L.append_nil(bytes) : {N.hash(bytes) == %(Fu)s : List<&2, U32>}
  stream_correct([bytes])
""" % dict(Q=Q, Fcs=fone(name, 'List.concat(&2, U32, cs)', LW, Gw, DIG, p, Q), z=SUF('List.length(&2, U32, m)'),
           body=build(0), Fb=fone(name, 'bytes', LW, Gw, DIG, p, Q), Fu=fone(name, '_', LW, Gw, DIG, p, Q))


def extra_text(name, a, p, W):
    if name == 'sha512':
        ws = ['w%d' % i for i in range(16)]
        shorts = ''.join('    case %s:\n      {==}\n' % (' <> '.join(ws[:k] + ['Nil{}'])) for k in range(16))
        return """
law sblocks:
  for +ws: List<&2, T.Lane>
  for +q: Nat
  for +s: T.State
  {N.blocks(ws, q, s) == C.blocks(ws, q, C.round_constants(), s) : T.State}

def sblocks(ws, q, s):
  match ws:
    case %(pat)s <> rest:
      %%FP.fips16_correct(%(A)s, q, s) :
        {N.blocks(%(pat)s <> rest, q, s) == C.blocks(rest, q, C.round_constants(), _) : T.State}
      sblocks(rest, q, C.fips16(%(A)s, q, s))
%(shorts)s""" % dict(pat=' <> '.join(ws), A=', '.join(ws), shorts=shorts)
    zo = """
law zeros_onto_correct:
  for +k: Nat
  for +acc: List<&2, U32>
  {N.zeros_onto(k, acc) == List.append(&2, U32, List.replicate(U32, k, 0), acc) : List<&2, U32>}

def zeros_onto_correct(k, acc):
  match k:
    case 0n:
      {==}
    case 1n+p:
      %zeros_onto_correct(p, acc) : {N.zeros_onto(1n+p, acc) == 0 <> _ : List<&2, U32>}
      {==}
"""
    if name == 'sha3':
        return zo + """
law tail_fast_correct:
  for +q: Nat
  {N.tail_fast(q) == C.tail(q) : List<&2, U32>}

def tail_fast_correct(q):
  match q:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n+k:
      %zeros_onto_correct(k, [128]) : {N.tail_fast(2n+k) == 6 <> _ : List<&2, U32>}
      {==}

law suffix_fast_correct:
  for +n: Nat
  {N.suffix_fast(n) == C.suffix(n) : List<&2, U32>}

def suffix_fast_correct(n):
  tail_fast_correct(Nat.sub(136n, Nat.mod(n, 136n)))
"""
    return zo + """
law suffix_fast_correct:
  for +n: Nat
  {N.suffix_fast(n) == C.suffix(n) : List<&2, U32>}

def suffix_fast_correct(n):
  %zeros_onto_correct(Nat.mod(Nat.sub(119n, Nat.mod(n, 64n)), 64n), C.bit_length(n)) :
    {N.suffix_fast(n) == 128 <> _ : List<&2, U32>}
  {==}
"""


def incremental():
    b = ['b%d' % i for i in range(64)]
    packs = ', '.join('C256.pack(%s)' % ', '.join(b[i:i + 4]) for i in range(0, 64, 4))
    shorts = ''.join('    case %s:\n      {==}\n' % (' <> '.join(b[:k] + ['Nil{}'])) for k in range(64))
    out = ['''# Generated by tools/generators/stream_gen.py; do not edit by hand.
import Base
import ../../../src/crypto/sha/state.bend as S256
import ../../../src/crypto/sha/core.bend as C256
import ../../../src/crypto/sha/stream.bend as N256
import ../../../src/crypto/sha512/stream.bend as N512
import ../../../src/crypto/sha3/stream.bend as N3
import ../../../src/crypto/hash.bend as H
import ../sha/conformance.bend as SC
import ./stream256.bend as P256
import ../sha512/stream.bend as P512
import ../sha3/stream.bend as P3

# The Hasher of src/crypto/hash.bend folds each algorithm's stream state
# (stateX: H.fold over chunks is the stream proofs' fold_st), and SHA-256's
# word-level block loop is its byte-level one (block_loop: the FIPS
# compression is the table-driven one, proofs/crypto/sha/conformance.bend).

law block_loop:
  for +bytes: List<&2, U32>
  for +q: Nat
  for +s: S256.State
  {N256.blocks(N256.lanes(bytes), q, s) == C256.block_bytes(bytes, q, C256.round_constants(), s) : S256.State}

def block_loop(bytes, q, s):
  match bytes:
    case %(pat)s <> rest:
      %%SC.fips16_correct(%(packs)s, q, s) :
        {N256.blocks(N256.lanes(%(pat)s <> rest), q, s) == C256.block_bytes(rest, q, C256.round_constants(), _) : S256.State}
      block_loop(rest, q, C256.fips_compress16(%(packs)s, q, s))
%(shorts)s''' % dict(pat=' <> '.join(b), packs=packs, shorts=shorts)]
    for x, ctor, P, N, Q in (('256', 'Sha256H', 'P256', 'N256', '48n'), ('512', 'Sha512H', 'P512', 'N512', '64n'), ('3', 'Sha3H', 'P3', 'N3', '24n')):
        out.append('''
law state%(x)s:
  for +cs: List<&2, List<&2, U32>>
  for +st: %(N)s.St
  {H.fold(cs, H.%(ctor)s{st}) == H.%(ctor)s{%(P)s.fold_st(cs, %(Q)s, st)} : H.Hasher}

def state%(x)s(cs, st):
  match cs:
    case Nil{}:
      {==}
    case c <> ct:
      state%(x)s(ct, %(N)s.update(st, c, %(Q)s))
''' % dict(x=x, ctor=ctor, P=P, N=N, Q=Q))
    return ''.join(out)


def main():
    out = Path(sys.argv[1]) if len(sys.argv) > 1 else None
    for name, a in ALGS.items():
        dst = (out / ('stream_%s.bend' % name)) if out else (ROOT / 'src/crypto' / a['dir'] / 'stream.bend')
        dst.write_text(stream(name, a))
        if not out:
            (ROOT / PROOF[name]['out']).write_text(stream_proofs(name, a, PROOF[name]))
    if not out:
        (ROOT / 'proofs/crypto/hash/incremental.bend').write_text(incremental())


if __name__ == '__main__':
    main()
