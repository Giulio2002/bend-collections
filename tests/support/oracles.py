"""Independent Python oracles for the Bend test drivers (tests/<id>/main.bend).

Each oracle takes the same argv as the driver and returns the lines the driver
must print. They are written from the documented semantics (docs/API.md and the
spec/ models), in plain Python data structures, never from the Bend sources.
Expected answers are computed here only; the Bend binaries receive operation
tokens and nothing else.
"""
U32 = 1 << 32

def fields(tok):
    return tok.split(':')

def field(p, i):
    return p[i] if i < len(p) else ''

def nat_of(s):
    return int(s) if s.isdigit() else 0

def u32_of(s):
    if s.isdigit() and int(s) < U32:
        return int(s)
    return 0

def join(xs):
    return ','.join((str(x) for x in xs))

def dynamic_array(args):
    conv = u32_of if args[0] == 'u32' else nat_of
    limit = min(nat_of(args[1]), 31)
    (depth, items, out) = (0, [], [])
    for tok in args[2:]:
        p = fields(tok)
        n = p[0]
        if n == 'len':
            out.append('N %d' % len(items))
        elif n == 'cap':
            out.append('N %d' % (1 << depth))
        elif n == 'get':
            i = nat_of(field(p, 1))
            out.append('OK %d' % items[i] if i < len(items) else 'ERR IndexOutOfRange')
        elif n == 'set':
            (i, v) = (nat_of(field(p, 1)), conv(field(p, 2)))
            if i < len(items):
                items[i] = v
                out.append('OK')
            else:
                out.append('ERR IndexOutOfRange')
        elif n == 'push':
            v = conv(field(p, 1))
            if len(items) < 1 << depth:
                items.append(v)
                out.append('OK')
            elif depth < limit:
                depth += 1
                items.append(v)
                out.append('OK')
            else:
                out.append('ERR CapacityExceeded')
        elif n == 'pop':
            out.append('OK %d' % items.pop() if items else 'ERR EmptyArray')
        elif n == 'reserve':
            w = nat_of(field(p, 1))
            if w <= 1 << depth:
                out.append('OK')
            elif w <= 1 << limit:
                while 1 << depth < w:
                    depth += 1
                out.append('OK')
            else:
                out.append('ERR CapacityExceeded')
        elif n == 'clear':
            items = []
            out.append('OK')
        else:
            out.append('LIST ' + join(items))
    return out

def deque(args):
    (xs, out) = ([], [])
    for tok in args:
        p = fields(tok)
        n = p[0]
        if n == 'len':
            out.append('N %d' % len(xs))
        elif n == 'pf':
            xs.insert(0, nat_of(field(p, 1)))
            out.append('OK')
        elif n == 'pb':
            xs.append(nat_of(field(p, 1)))
            out.append('OK')
        elif n == 'popf':
            out.append('OK %d' % xs.pop(0) if xs else 'ERR EmptyDeque')
        elif n == 'popb':
            out.append('OK %d' % xs.pop() if xs else 'ERR EmptyDeque')
        elif n == 'peekf':
            out.append('OK %d' % xs[0] if xs else 'ERR EmptyDeque')
        elif n == 'peekb':
            out.append('OK %d' % xs[-1] if xs else 'ERR EmptyDeque')
        else:
            out.append('LIST ' + join(xs))
    return out

def queue(args):
    (xs, out) = ([], [])
    for tok in args:
        p = fields(tok)
        n = p[0]
        if n == 'len':
            out.append('N %d' % len(xs))
        elif n == 'enq':
            xs.append(nat_of(field(p, 1)))
            out.append('OK')
        elif n == 'deq':
            out.append('OK %d' % xs.pop(0) if xs else 'ERR EmptyQueue')
        elif n == 'peek':
            out.append('OK %d' % xs[0] if xs else 'ERR EmptyQueue')
        else:
            out.append('LIST ' + join(xs))
    return out

def stack(args):
    (items, out) = ([], [])
    for token in args:
        p = fields(token)
        op = p[0]
        if op == 'push':
            items.insert(0, nat_of(field(p, 1)))
            out.append('OK')
        elif op == 'pop':
            out.append('OK %d' % items.pop(0) if items else 'ERR EmptyStack')
        elif op == 'peek':
            out.append('OK %d' % items[0] if items else 'ERR EmptyStack')
        elif op == 'len':
            out.append('N %d' % len(items))
        else:
            out.append('LIST ' + join(items))
    return out

def doubly_linked_list(args):
    tag = u32_of(args[0])
    values = {}
    generations = {}
    order = []
    free = []
    fresh = 0
    out = []

    def handle(i):
        return 'H %d:%d:%d' % (tag, i, generations[i])

    def insert(at, value):
        nonlocal fresh
        if free:
            i = free.pop()
        else:
            i = fresh
            fresh += 1
            generations[i] = 0
        values[i] = value
        order.insert(at, i)
        return handle(i)
    for token in args[1:]:
        p = fields(token)
        op = p[0]
        if op == 'len':
            out.append('N %d' % len(order))
            continue
        if op in ['pf', 'pb']:
            out.append(insert(0 if op == 'pf' else len(order), nat_of(field(p, 1))))
            continue
        if op not in ['ib', 'ia', 'rm', 'get', 'set', 'nx', 'pv']:
            out.append('LIST ' + join([values[i] for i in order]))
            continue
        (owner, i, generation) = [u32_of(field(p, j)) for j in [1, 2, 3]]
        if owner != tag:
            out.append('ERR ForeignHandle')
            continue
        if i not in values or generations[i] != generation:
            out.append('ERR StaleHandle')
            continue
        at = order.index(i)
        if op == 'get':
            out.append('OK %d' % values[i])
        elif op == 'set':
            values[i] = nat_of(field(p, 4))
            out.append('OK')
        elif op == 'rm':
            out.append('OK %d' % values.pop(i))
            order.pop(at)
            if generation != 4294967295:
                generations[i] += 1
                free.append(i)
        elif op in ['ia', 'ib']:
            out.append('OK ' + insert(at + (op == 'ia'), nat_of(field(p, 4))))
        else:
            j = at + (1 if op == 'nx' else -1)
            out.append('OK ' + handle(order[j]) if 0 <= j < len(order) else 'OK none')
    return out

def binary_heap(args):
    kind = args[0]
    conv = u32_of if kind == 'u32' else lambda s: s
    (xs, out) = ([], [])
    for tok in args[1:]:
        p = fields(tok)
        n = p[0]
        if n == 'push':
            xs.append(conv(field(p, 1)))
            xs.sort()
            out.append('OK')
        elif n == 'peek':
            out.append('OK %s' % xs[0] if xs else 'ERR EmptyHeap')
        elif n == 'pop':
            out.append('OK %s' % xs.pop(0) if xs else 'ERR EmptyHeap')
        elif n == 'from':
            xs = sorted((conv(s) for s in field(p, 1).split(',')))
            out.append('OK')
        elif n == 'sorted':
            out.append('LIST ' + join(xs))
        else:
            out.append('N %d' % len(xs))
    return out

def balanced_search_tree(args):
    kind = args[0]
    rb = kind.startswith('rb')
    numeric = kind in ('u32', 'rb32')
    conv = u32_of if numeric else lambda s: s
    (m, out) = ({}, [])

    def ent(k):
        return '%s=%d' % (k, m[k])
    for tok in args[1:]:
        p = fields(tok)
        n = p[0]
        if n == 'ins':
            m[conv(field(p, 1))] = nat_of(field(p, 2))
            out.append('OK')
        elif n == 'rm':
            k = conv(field(p, 1))
            out.append('OK %d' % m.pop(k) if k in m else 'ERR KeyNotFound')
        elif n == 'get':
            k = conv(field(p, 1))
            out.append('OK %d' % m[k] if k in m else 'ERR KeyNotFound')
        elif n == 'has':
            out.append('OK true' if conv(field(p, 1)) in m else 'OK false')
        elif n == 'min':
            out.append('OK ' + ent(min(m)) if m else 'ERR EmptyTree')
        elif n == 'max':
            out.append('OK ' + ent(max(m)) if m else 'ERR EmptyTree')
        elif n == 'lb':
            k = conv(field(p, 1))
            c = [x for x in m if x >= k]
            out.append('OK ' + ent(min(c)) if c else 'ERR KeyNotFound')
        elif n == 'range':
            (lo, hi) = (conv(field(p, 1)), conv(field(p, 2)))
            out.append('LIST ' + ','.join((ent(k) for k in sorted(m) if lo <= k < hi)))
        elif n == 'list':
            out.append('LIST ' + ','.join((ent(k) for k in sorted(m))))
        else:
            out.append('N %d' % len(m))
        if rb:
            out[-1] = 'RB root=1 nrr=1 bh=1 ord=1 sz=1 n=%d' % len(m)
    return out

def bitset(args):
    (xs, out) = ([False] * nat_of(args[0]), [])
    for tok in args[1:]:
        p = fields(tok)
        n = p[0]
        if n in ('get', 'set', 'clear'):
            i = nat_of(field(p, 1))
            if i >= len(xs):
                out.append('ERR IndexOutOfRange')
            elif n == 'get':
                out.append('OK 1' if xs[i] else 'OK 0')
            else:
                xs[i] = n == 'set'
                out.append('OK')
        elif n == 'count':
            out.append('N %d' % sum(xs))
        elif n in ('or', 'and', 'diff', 'xor'):
            ys = [c == '1' for c in field(p, 1)]
            if len(ys) != len(xs):
                out.append('ERR LengthMismatch')
            else:
                f = {'or': lambda a, b: a or b, 'and': lambda a, b: a and b, 'diff': lambda a, b: a and (not b), 'xor': lambda a, b: a != b}[n]
                xs = [f(a, b) for (a, b) in zip(xs, ys)]
                out.append('OK')
        elif n == 'list':
            out.append('LIST ' + join((i for (i, b) in enumerate(xs) if b)))
        else:
            out.append('N %d' % len(xs))
    return out

def _init_u32(s):
    p = fields(s)
    if field(p, 0) == 'list':
        return [u32_of(x) for x in field(p, 1).split(',')]
    return [0] * nat_of(field(p, 1))

def lru(args):
    cap = u32_of(args[0])
    if cap == 0:
        return None
    (d, out) = ({}, [])
    for tok in args[1:]:
        p = fields(tok)
        n = p[0]
        k = field(p, 1)
        if n == 'add':
            ev = False
            if k in d:
                del d[k]
            elif len(d) >= cap:
                del d[next(iter(d))]
                ev = True
            d[k] = nat_of(field(p, 2))
            out.append('BOOL true' if ev else 'BOOL false')
        elif n == 'get':
            if k in d:
                v = d.pop(k)
                d[k] = v
                out.append('VAL %d' % v)
            else:
                out.append('MISS')
        elif n == 'peek':
            out.append('VAL %d' % d[k] if k in d else 'MISS')
        elif n == 'has':
            out.append('BOOL true' if k in d else 'BOOL false')
        elif n == 'rm':
            out.append('BOOL true' if d.pop(k, None) is not None else 'BOOL false')
        elif n == 'keys':
            out.append('KEYS ' + ','.join(d))
        elif n in ('oldest', 'rmold'):
            if d:
                k0 = next(iter(d))
                out.append('OLD %s=%d' % (k0, d[k0]))
                if n == 'rmold':
                    del d[k0]
            else:
                out.append('NONE')
        else:
            out.append('LEN %d' % len(d))
    return out
ORACLES = {'dynamic_array': dynamic_array, 'deque': deque, 'queue': queue, 'doubly_linked_list': doubly_linked_list, 'binary_heap': binary_heap, 'balanced_search_tree': balanced_search_tree, 'bitset': bitset, 'lru': lru}
