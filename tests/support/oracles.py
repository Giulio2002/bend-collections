"""Independent Python oracles for the Bend test drivers (tests/<id>/main.bend).

Each oracle takes the same argv as the driver and returns the lines the driver
must print. They are written from the documented semantics (docs/API.md and the
spec/ models), in plain Python data structures, never from the Bend sources.
Expected answers are computed here only; the Bend binaries receive operation
tokens and nothing else.
"""

U32 = 1 << 32


# ---- argv transport (mirrors tests/support/text.bend) ----

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
    return ','.join(str(x) for x in xs)


# ---- dynamic_array ----

def dynamic_array(args):
    # argv = [kind, limit, tokens...]; kind selects the element type.
    conv = u32_of if args[0] == 'u32' else nat_of
    limit = min(nat_of(args[1]), 31)
    depth, items, out = 0, [], []
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
            i, v = nat_of(field(p, 1)), conv(field(p, 2))
            if i < len(items):
                items[i] = v
                out.append('OK')
            else:
                out.append('ERR IndexOutOfRange')
        elif n == 'push':
            v = conv(field(p, 1))
            if len(items) < (1 << depth):
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
            if w <= (1 << depth):
                out.append('OK')
            elif w <= (1 << limit):
                while (1 << depth) < w:
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


# ---- deque / queue ----

def deque(args):
    xs, out = [], []
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
    xs, out = [], []
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


# ---- doubly_linked_list: (id, value) sequence, fresh ids never reused ----

def doubly_linked_list(args):
    tag = nat_of(args[0])
    items, fresh, out = [], 0, []

    def pos(i):
        for k, (j, _) in enumerate(items):
            if j == i:
                return k
        return None

    def check(l, i):
        if l != tag:
            return 'ERR ForeignHandle'
        if pos(i) is None:
            return 'ERR StaleHandle'
        return None

    def h(i):
        return 'H %d:%d' % (tag, i)

    for tok in args[1:]:
        p = fields(tok)
        n = p[0]
        if n == 'len':
            out.append('N %d' % len(items))
        elif n in ('pf', 'pb'):
            x = nat_of(field(p, 1))
            if n == 'pf':
                items.insert(0, (fresh, x))
            else:
                items.append((fresh, x))
            out.append(h(fresh))
            fresh += 1
        elif n in ('ib', 'ia', 'rm', 'get', 'set', 'nx', 'pv'):
            l, i = nat_of(field(p, 1)), nat_of(field(p, 2))
            e = check(l, i)
            if e:
                out.append(e)
                continue
            k = pos(i)
            if n in ('ib', 'ia'):
                x = nat_of(field(p, 3))
                items.insert(k if n == 'ib' else k + 1, (fresh, x))
                out.append('OK ' + h(fresh))
                fresh += 1
            elif n == 'rm':
                out.append('OK %d' % items.pop(k)[1])
            elif n == 'get':
                out.append('OK %d' % items[k][1])
            elif n == 'set':
                items[k] = (i, nat_of(field(p, 3)))
                out.append('OK')
            elif n == 'nx':
                out.append('OK ' + h(items[k + 1][0]) if k + 1 < len(items) else 'OK none')
            else:
                out.append('OK ' + h(items[k - 1][0]) if k > 0 else 'OK none')
        else:
            out.append('LIST ' + join(v for _, v in items))
    return out


# ---- binary_heap: sorted multiset ----

def binary_heap(args):
    kind = args[0]
    conv = u32_of if kind == 'u32' else (lambda s: s)
    xs, out = [], []
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
            xs = sorted(conv(s) for s in field(p, 1).split(','))
            out.append('OK')
        elif n == 'sorted':
            out.append('LIST ' + join(xs))
        else:
            out.append('N %d' % len(xs))
    return out


# ---- balanced_search_tree: ordered map (keys U32 or String by code point) ----

def balanced_search_tree(args):
    kind = args[0]
    # kinds "rb32"/"rbstr" ask the driver for a red-black structure report
    # after every operation instead of the operation's observation; the
    # expected report is "all five structural properties hold", with the
    # entry count this model predicts.
    rb = kind.startswith('rb')
    numeric = kind in ('u32', 'rb32')
    conv = u32_of if numeric else (lambda s: s)
    m, out = {}, []

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
            lo, hi = conv(field(p, 1)), conv(field(p, 2))
            out.append('LIST ' + ','.join(ent(k) for k in sorted(m) if lo <= k < hi))
        elif n == 'list':
            out.append('LIST ' + ','.join(ent(k) for k in sorted(m)))
        else:
            out.append('N %d' % len(m))
        if rb:
            out[-1] = 'RB root=1 nrr=1 bh=1 ord=1 sz=1 n=%d' % len(m)
    return out


# ---- bitset ----

def bitset(args):
    xs, out = [False] * nat_of(args[0]), []
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
                xs[i] = (n == 'set')
                out.append('OK')
        elif n == 'count':
            out.append('N %d' % sum(xs))
        elif n in ('or', 'and', 'diff', 'xor'):
            ys = [c == '1' for c in field(p, 1)]
            if len(ys) != len(xs):
                out.append('ERR LengthMismatch')
            else:
                f = {'or': lambda a, b: a or b, 'and': lambda a, b: a and b,
                     'diff': lambda a, b: a and not b, 'xor': lambda a, b: a != b}[n]
                xs = [f(a, b) for a, b in zip(xs, ys)]
                out.append('OK')
        elif n == 'list':
            out.append('LIST ' + join(i for i, b in enumerate(xs) if b))
        else:
            out.append('N %d' % len(xs))
    return out


# ---- union_find: labelled partition; larger class keeps its label ----

def union_find(args):
    size = nat_of(args[0])
    lab, out = list(range(size)), []
    for tok in args[1:]:
        p = fields(tok)
        n = p[0]
        if n == 'find':
            x = nat_of(field(p, 1))
            out.append('OK %d' % lab[x] if x < size else 'ERR OutOfRange')
        elif n in ('union', 'conn'):
            a, b = nat_of(field(p, 1)), nat_of(field(p, 2))
            if a >= size or b >= size:
                out.append('ERR OutOfRange')
                continue
            la, lb = lab[a], lab[b]
            if n == 'conn':
                out.append('OK true' if la == lb else 'OK false')
            elif la == lb:
                out.append('OK false')
            else:
                keep, drop = (la, lb) if lab.count(lb) <= lab.count(la) else (lb, la)
                lab = [keep if v == drop else v for v in lab]
                out.append('OK true')
        elif n == 'size':
            x = nat_of(field(p, 1))
            out.append('OK %d' % lab.count(lab[x]) if x < size else 'ERR OutOfRange')
        else:
            out.append('N %d' % sum(1 for i, v in enumerate(lab) if v == i))
    return out


# ---- fenwick_tree / segment_tree: U32 sequences, sums mod 2^32 ----

def _init_u32(s):
    p = fields(s)
    if field(p, 0) == 'list':
        return [u32_of(x) for x in field(p, 1).split(',')]
    return [0] * nat_of(field(p, 1))


def fenwick_tree(args):
    xs, out = _init_u32(args[0]), []
    for tok in args[1:]:
        p = fields(tok)
        n = p[0]
        if n == 'add':
            i, v = nat_of(field(p, 1)), u32_of(field(p, 2))
            if i < len(xs):
                xs[i] = (xs[i] + v) % U32
                out.append('OK')
            else:
                out.append('ERR IndexOutOfRange')
        elif n == 'prefix':
            e = nat_of(field(p, 1))
            out.append('OK %d' % (sum(xs[:e]) % U32) if e <= len(xs) else 'ERR InvalidRange')
        elif n == 'range':
            l, r = nat_of(field(p, 1)), nat_of(field(p, 2))
            out.append('OK %d' % (sum(xs[l:r]) % U32) if l <= r <= len(xs) else 'ERR InvalidRange')
        else:
            out.append('N %d' % len(xs))
    return out


def segment_tree(args):
    xs, out = _init_u32(args[0]), []
    for tok in args[1:]:
        p = fields(tok)
        n = p[0]
        if n == 'get':
            i = nat_of(field(p, 1))
            out.append('OK %d' % xs[i] if i < len(xs) else 'ERR IndexOutOfRange')
        elif n == 'set':
            i, v = nat_of(field(p, 1)), u32_of(field(p, 2))
            if i < len(xs):
                xs[i] = v
                out.append('OK')
            else:
                out.append('ERR IndexOutOfRange')
        elif n == 'query':
            l, r = nat_of(field(p, 1)), nat_of(field(p, 2))
            out.append('OK %d' % (sum(xs[l:r]) % U32) if l <= r <= len(xs) else 'ERR InvalidRange')
        elif n == 'add':
            l, r, v = nat_of(field(p, 1)), nat_of(field(p, 2)), u32_of(field(p, 3))
            if l <= r <= len(xs):
                for k in range(l, r):
                    xs[k] = (xs[k] + v) % U32
                out.append('OK')
            else:
                out.append('ERR InvalidRange')
        else:
            out.append('N %d' % len(xs))
    return out


# ---- prefix_trie: String -> Nat map; enumeration in code-point order ----

def prefix_trie(args):
    m, out = {}, []

    def ent(k):
        return '%s=%d' % (k, m[k])

    for tok in args:
        p = fields(tok)
        n = p[0]
        k = field(p, 1)
        if n == 'ins':
            m[k] = nat_of(field(p, 2))
            out.append('OK')
        elif n == 'get':
            out.append('OK %d' % m[k] if k in m else 'ERR KeyNotFound')
        elif n == 'rm':
            out.append('OK %d' % m.pop(k) if k in m else 'ERR KeyNotFound')
        elif n == 'pre':
            out.append('LIST ' + ','.join(ent(x) for x in sorted(m) if x.startswith(k)))
        elif n == 'lp':
            c = [x for x in m if k.startswith(x)]
            out.append('OK ' + ent(max(c, key=len)) if c else 'ERR KeyNotFound')
        else:
            out.append('OK true' if k in m else 'OK false')
    return out


# ---- graph: vertex -> neighbour set; undirected stores both directions ----

def graph(args):
    directed = args[0] == 'dir'
    adj, out = {}, []
    for tok in args[1:]:
        p = fields(tok)
        n = p[0]
        u, v = u32_of(field(p, 1)), u32_of(field(p, 2))
        if n == 'av':
            if u in adj:
                out.append('ERR VertexExists')
            else:
                adj[u] = set()
                out.append('OK')
        elif n == 'rv':
            if u not in adj:
                out.append('ERR VertexNotFound')
            else:
                del adj[u]
                for s in adj.values():
                    s.discard(u)
                out.append('OK')
        elif n == 'ae':
            if u not in adj or v not in adj:
                out.append('ERR VertexNotFound')
            elif u == v:
                out.append('ERR SelfLoop')
            else:
                adj[u].add(v)
                if not directed:
                    adj[v].add(u)
                out.append('OK')
        elif n == 're':
            if u not in adj or v not in adj:
                out.append('ERR VertexNotFound')
            elif v not in adj[u]:
                out.append('ERR EdgeNotFound')
            else:
                adj[u].discard(v)
                if not directed:
                    adj[v].discard(u)
                out.append('OK')
        elif n == 'hv':
            out.append('BOOL true' if u in adj else 'BOOL false')
        elif n == 'he':
            if u not in adj or v not in adj:
                out.append('ERR VertexNotFound')
            else:
                out.append('OK true' if v in adj[u] else 'OK false')
        elif n == 'nb':
            out.append('LIST ' + join(sorted(adj[u])) if u in adj else 'ERR VertexNotFound')
        elif n == 'vs' or n == 'vb':
            # `vs` reads the vertices through the List enumeration and `vb`
            # through the public block enumeration: the same ordered sequence
            out.append('LIST ' + join(sorted(adj)))
        else:
            es = [(a, b) for a in sorted(adj) for b in sorted(adj[a]) if directed or a < b]
            out.append('EDGES ' + ','.join('%d-%d' % e for e in es))
    return out


# ---- lru (smoke): capacity-bounded recency order, oldest first ----

def lru(args):
    cap = u32_of(args[0])
    if cap == 0:
        return None  # constructor error; checked separately (line starts with CTOR)
    d, out = {}, []
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


ORACLES = {
    'dynamic_array': dynamic_array, 'deque': deque, 'queue': queue,
    'doubly_linked_list': doubly_linked_list, 'binary_heap': binary_heap,
    'balanced_search_tree': balanced_search_tree, 'bitset': bitset,
    'union_find': union_find, 'fenwick_tree': fenwick_tree,
    'segment_tree': segment_tree, 'prefix_trie': prefix_trie, 'graph': graph,
    'lru': lru,
}
