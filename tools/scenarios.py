"""Deterministic scenario tables for tools/validate.py.

Every scenario is a full argv for tests/<id>/main.bend. The same argv is handed
to the independent Python oracle in tests/support/oracles.py; the Bend side
never sees an expected answer.

  functional  - covers every inventoried operation on non-trivial states
  boundary    - empty structures, out-of-range indices, invalid ranges, foreign
                and stale handles, capacity limits; each one is followed by an
                observation of the whole state so that state preservation after
                a rejected operation is checked, not just the error value
  seeds       - seeds for the deterministic differential histories

`OPS` maps each inventoried operation name to the argv token that exercises it
("" means the operation is exercised by the constructor arguments).
"""
import random
OPS = {'dynamic_array': {'new': '', 'length': 'len', 'capacity': 'cap', 'get': 'get', 'set': 'set', 'push': 'push', 'pop': 'pop', 'reserve': 'reserve', 'clear': 'clear', 'to_list': 'to_list'}, 'deque': {'new': '', 'length': 'len', 'push_front': 'pf', 'push_back': 'pb', 'pop_front': 'popf', 'pop_back': 'popb', 'peek_front': 'peekf', 'peek_back': 'peekb', 'to_list': 'to_list'}, 'queue': {'new': '', 'length': 'len', 'enqueue': 'enq', 'dequeue': 'deq', 'peek': 'peek', 'to_list': 'to_list'}, 'doubly_linked_list': {'new': '', 'length': 'len', 'push_front': 'pf', 'push_back': 'pb', 'insert_before': 'ib', 'insert_after': 'ia', 'remove': 'rm', 'get': 'get', 'set': 'set', 'next': 'nx', 'prev': 'pv', 'to_list': 'to_list'}, 'binary_heap': {'new': '', 'length': 'len', 'push': 'push', 'peek': 'peek', 'pop': 'pop', 'from_list': 'from', 'to_sorted_list': 'sorted'}, 'balanced_search_tree': {'new': '', 'length': 'len', 'insert': 'ins', 'remove': 'rm', 'lookup': 'get', 'contains': 'has', 'min': 'min', 'max': 'max', 'lower_bound': 'lb', 'range': 'range', 'to_list': 'list'}, 'bitset': {'new': '', 'length': 'len', 'get': 'get', 'set': 'set', 'clear': 'clear', 'count': 'count', 'union': 'or', 'intersection': 'and', 'difference': 'diff', 'xor': 'xor', 'to_list': 'list'}, 'union_find': {'new': '', 'find': 'find', 'union': 'union', 'connected': 'conn', 'component_size': 'size', 'component_count': 'count'}, 'segment_tree': {'new': '', 'from_list': '', 'length': 'len', 'get': 'get', 'set': 'set', 'range_query': 'query', 'range_add': 'add'}}
CTOR_OPS = {'dynamic_array': {'new': lambda a: True}, 'deque': {'new': lambda a: True}, 'queue': {'new': lambda a: True}, 'doubly_linked_list': {'new': lambda a: True}, 'binary_heap': {'new': lambda a: True}, 'balanced_search_tree': {'new': lambda a: True}, 'bitset': {'new': lambda a: True}, 'union_find': {'new': lambda a: True}, 'segment_tree': {'new': lambda a: a[0].startswith('new'), 'from_list': lambda a: a[0].startswith('list')}}
FUNCTIONAL = {'dynamic_array': [['nat', '10', 'len', 'cap', 'push:5', 'push:7', 'push:9', 'len', 'cap', 'get:0', 'get:2', 'set:1:42', 'to_list', 'pop', 'to_list', 'len', 'reserve:100', 'cap', 'to_list', 'clear', 'len', 'cap', 'to_list'], ['u32', '10', 'push:4294967295', 'push:0', 'push:1', 'get:0', 'get:1', 'set:2:123456789', 'to_list', 'len', 'cap', 'pop', 'to_list', 'reserve:64', 'cap', 'clear', 'to_list', 'len'], ['u32', '5', 'reserve:17', 'cap', 'len', 'push:1', 'to_list', 'clear', 'cap', 'len', 'to_list']], 'deque': [['len', 'pf:1', 'pb:2', 'pf:3', 'pb:4', 'to_list', 'len', 'peekf', 'peekb', 'popf', 'to_list', 'popb', 'to_list', 'peekf', 'peekb', 'popf', 'popb', 'len', 'to_list'], ['pb:1', 'pb:2', 'pb:3', 'pb:4', 'pb:5', 'popf', 'popf', 'to_list', 'pf:9', 'peekf', 'peekb', 'popb', 'popb', 'to_list', 'len']], 'queue': [['len', 'enq:1', 'enq:2', 'enq:3', 'to_list', 'len', 'peek', 'deq', 'to_list', 'deq', 'peek', 'deq', 'len', 'to_list'], ['enq:7', 'deq', 'enq:8', 'enq:9', 'peek', 'to_list', 'deq', 'deq', 'len', 'to_list']], 'doubly_linked_list': [['1', 'len', 'pf:10', 'pb:20', 'pb:30', 'to_list', 'len', 'get:1:0', 'get:1:1', 'set:1:1:21', 'to_list', 'ib:1:2:15', 'to_list', 'ia:1:0:11', 'to_list', 'nx:1:0', 'pv:1:0', 'nx:1:2', 'pv:1:2', 'rm:1:0', 'to_list', 'len', 'rm:1:1', 'rm:1:2', 'to_list', 'len'], ['7', 'pb:1', 'pb:2', 'pb:3', 'nx:7:1', 'pv:7:1', 'ia:7:2:99', 'to_list', 'ib:7:0:88', 'to_list', 'get:7:3', 'set:7:3:77', 'to_list', 'rm:7:3', 'to_list', 'len']], 'binary_heap': [['u32', 'len', 'push:5', 'push:3', 'push:9', 'push:1', 'len', 'peek', 'sorted', 'pop', 'sorted', 'pop', 'peek', 'len', 'from:8,2,6,4,10,1', 'len', 'sorted', 'peek', 'pop', 'sorted'], ['str', 'push:pear', 'push:apple', 'push:fig', 'peek', 'sorted', 'pop', 'sorted', 'len', 'from:kiwi,banana,date', 'sorted', 'peek', 'pop', 'len'], ['u32', 'push:7', 'push:7', 'push:7', 'sorted', 'len', 'pop', 'sorted', 'peek'], ['u32', 'push:10', 'push:9', 'push:8', 'push:7', 'push:6', 'push:5', 'push:4', 'push:3', 'push:2', 'push:1', 'len', 'peek', 'sorted', 'pop', 'peek', 'pop', 'sorted', 'len'], ['u32', 'push:1', 'push:2', 'push:3', 'push:4', 'push:5', 'push:6', 'push:7', 'push:8', 'push:9', 'pop', 'peek', 'pop', 'pop', 'sorted', 'push:0', 'peek', 'sorted', 'len']], 'balanced_search_tree': [['u32', 'len', 'ins:5:50', 'ins:2:20', 'ins:8:80', 'ins:1:10', 'ins:9:90', 'len', 'list', 'get:2', 'get:7', 'has:8', 'has:7', 'min', 'max', 'lb:3', 'lb:9', 'lb:10', 'range:2:9', 'range:0:100', 'range:5:5', 'ins:5:55', 'get:5', 'len', 'rm:2', 'list', 'rm:2', 'len', 'list'], ['str', 'ins:pear:1', 'ins:apple:2', 'ins:fig:3', 'list', 'min', 'max', 'get:fig', 'has:plum', 'lb:b', 'range:apple:fig', 'rm:apple', 'list', 'len'], ['u32', 'min', 'max', 'get:1', 'rm:1', 'lb:1', 'list', 'len', 'range:0:1']], 'bitset': [['12', 'len', 'count', 'list', 'set:0', 'set:5', 'set:11', 'count', 'list', 'get:5', 'get:6', 'clear:5', 'count', 'list', 'or:000000000011', 'list', 'and:100000000001', 'list', 'diff:100000000000', 'list', 'xor:111111111111', 'list', 'count', 'len'], ['40', 'set:0', 'set:31', 'set:32', 'set:39', 'count', 'list', 'get:32', 'clear:32', 'list', 'count', 'len'], ['1', 'len', 'count', 'set:0', 'list', 'count', 'xor:1', 'list', 'count'], ['65', 'set:0', 'set:31', 'set:32', 'set:63', 'set:64', 'count', 'list', 'get:64', 'get:65', 'set:65', 'clear:64', 'count', 'list', 'xor:' + '1' * 65, 'count', 'list', 'len']], 'union_find': [['8', 'count', 'find:0', 'find:7', 'conn:0:1', 'union:0:1', 'conn:0:1', 'count', 'size:0', 'union:2:3', 'union:0:2', 'count', 'size:0', 'size:3', 'find:3', 'union:0:1', 'conn:1:3', 'size:7', 'count'], ['5', 'union:0:1', 'union:1:2', 'union:3:4', 'count', 'size:2', 'size:4', 'union:2:4', 'count', 'size:0', 'find:4', 'conn:0:4']], 'segment_tree': [['new:8', 'len', 'get:0', 'set:2:9', 'get:2', 'query:0:8', 'query:2:3', 'add:1:5:4', 'get:1', 'get:4', 'query:0:8', 'query:1:5', 'set:1:0', 'query:0:8', 'len'], ['list:1,2,3,4', 'len', 'query:0:4', 'get:3', 'add:0:4:10', 'query:0:4', 'get:0', 'set:3:0', 'query:2:4', 'query:4:4'], ['list:4294967295,1', 'query:0:2', 'add:0:2:2', 'get:0', 'get:1', 'query:0:2'], ['new:8', 'add:2:8:5', 'query:0:8', 'query:4:6', 'query:5:8', 'get:5', 'add:1:7:3', 'query:0:8', 'query:2:6', 'set:3:100', 'query:0:8', 'add:0:8:1', 'query:0:8', 'query:3:7', 'len']]}
BOUNDARY = {'dynamic_array': [['nat', '10', 'pop', 'len', 'to_list', 'get:0', 'set:0:1', 'len', 'to_list', 'cap'], ['u32', '2', 'push:1', 'push:2', 'push:3', 'push:4', 'push:5', 'to_list', 'len', 'cap', 'reserve:5', 'to_list', 'len', 'cap'], ['nat', '3', 'push:1', 'get:1', 'set:9:9', 'to_list', 'len', 'reserve:9999', 'to_list', 'len', 'cap'], ['nat', '0', 'push:1', 'push:2', 'to_list', 'len', 'cap']], 'deque': [['popf', 'popb', 'peekf', 'peekb', 'len', 'to_list'], ['pf:1', 'popf', 'popf', 'peekb', 'len', 'to_list']], 'queue': [['deq', 'peek', 'len', 'to_list'], ['enq:1', 'deq', 'deq', 'peek', 'len', 'to_list']], 'doubly_linked_list': [['1', 'get:1:0', 'rm:1:0', 'len', 'to_list'], ['1', 'pb:5', 'get:2:0', 'to_list', 'len', 'set:2:0:9', 'to_list', 'rm:2:0', 'to_list', 'nx:2:0', 'pv:2:0', 'ib:2:0:1', 'to_list'], ['1', 'pb:5', 'rm:1:0', 'get:1:0', 'to_list', 'len', 'set:1:0:9', 'to_list', 'rm:1:0', 'nx:1:0', 'pv:1:0', 'ia:1:0:7', 'to_list', 'len']], 'binary_heap': [['u32', 'peek', 'pop', 'len', 'sorted'], ['str', 'pop', 'peek', 'len', 'sorted']], 'balanced_search_tree': [['u32', 'get:1', 'rm:1', 'min', 'max', 'lb:0', 'len', 'list'], ['u32', 'ins:5:1', 'rm:6', 'list', 'len', 'get:6', 'lb:6', 'range:9:2', 'range:5:5', 'list']], 'bitset': [['0', 'len', 'count', 'list', 'get:0', 'set:0', 'clear:0', 'list', 'count'], ['4', 'get:4', 'set:4', 'clear:4', 'list', 'count', 'or:11111', 'list', 'and:1', 'list', 'count', 'len'], ['65', 'or:' + '1' * 64, 'count', 'or:' + '1' * 66, 'count', 'and:' + '1' * 65, 'count', 'len']], 'union_find': [['0', 'count', 'find:0', 'union:0:0', 'size:0', 'conn:0:0'], ['3', 'find:3', 'union:0:3', 'union:3:0', 'conn:0:3', 'size:3', 'count', 'union:1:1', 'conn:1:1', 'size:1', 'count']], 'segment_tree': [['new:0', 'len', 'query:0:0', 'get:0', 'set:0:1', 'add:0:0:1', 'query:0:1', 'len'], ['new:4', 'get:4', 'set:4:1', 'query:0:5', 'query:3:1', 'add:0:5:1', 'add:3:1:1', 'query:0:4', 'len']]}

def _asc(lo, hi):
    return ['ins:%d:%d' % (i, i) for i in range(lo, hi)]

def _desc(hi, lo):
    return ['ins:%d:%d' % (i, i) for i in range(hi, lo, -1)]

def _adversarial():
    """Interleaved deletes and inserts that drive every fixup case: delete
    from an ascending build (left-heavy deficiencies), from a descending
    build (right-heavy), and alternately from both ends."""
    ops = _asc(1, 33)
    for i in range(1, 17):
        ops.append('rm:%d' % i)
    ops += _desc(64, 48)
    for i in range(32, 16, -1):
        ops.append('rm:%d' % i)
    for i in range(49, 65):
        ops.append('rm:%d' % i)
        ops.append('ins:%d:%d' % (i + 100, i))
    for i in range(149, 165):
        ops.append('rm:%d' % i)
        ops.append('rm:%d' % (313 - i))
    ops += ['len', 'list']
    return ops
STRUCTURAL = {'balanced_search_tree': [['rb32', 'len', 'list', 'min', 'max', 'get:1', 'rm:1', 'lb:0', 'range:0:9'], ['rb32', 'ins:7:70', 'len', 'list', 'min', 'max', 'rm:7', 'len', 'list'], ['rb32', 'ins:4:1', 'ins:4:2', 'ins:4:3', 'len', 'get:4', 'ins:9:1', 'ins:9:2', 'ins:4:4', 'len', 'rm:4', 'len', 'rm:4'], ['rb32', 'ins:1:1', 'ins:2:2', 'ins:3:3', 'rm:99', 'rm:0', 'rm:2', 'rm:2', 'list', 'len'], ['rb32', 'ins:1:1', 'ins:2:2', 'ins:3:3', 'rm:2', 'list', 'rm:1', 'rm:3', 'len'], ['rb32'] + _asc(1, 41) + ['len'] + ['rm:%d' % i for i in range(1, 41)] + ['len', 'list'], ['rb32'] + _desc(40, 0) + ['len'] + ['rm:%d' % i for i in range(40, 0, -1)] + ['len', 'list'], ['rb32'] + _adversarial(), ['rbstr', 'ins:pear:1', 'ins:apple:2', 'ins:fig:3', 'ins:apple:4', 'ins:kiwi:5', 'ins:date:6', 'ins:banana:7', 'ins:plum:8', 'len', 'rm:fig', 'rm:fig', 'rm:apple', 'list', 'rm:zzz', 'len']]}
for _k in OPS:
    STRUCTURAL.setdefault(_k, [])
SEEDS = [11, 23, 37, 59, 101]

def _da(rng, u32):
    n = rng.randrange(20, 60)
    lim = rng.choice([4, 5, 6])
    hi = 4294967295 if u32 else 999
    ops = ['u32' if u32 else 'nat', str(lim)]
    for _ in range(n):
        c = rng.random()
        if c < 0.35:
            ops.append('push:%d' % rng.randrange(hi))
        elif c < 0.45:
            ops.append('pop')
        elif c < 0.55:
            ops.append('get:%d' % rng.randrange(0, 40))
        elif c < 0.65:
            ops.append('set:%d:%d' % (rng.randrange(0, 40), rng.randrange(hi)))
        elif c < 0.72:
            ops.append('reserve:%d' % rng.randrange(0, 80))
        elif c < 0.77:
            ops.append('clear')
        elif c < 0.85:
            ops.append('cap')
        elif c < 0.93:
            ops.append('len')
        else:
            ops.append('to_list')
    return ops

def _deque(rng):
    ops = []
    for _ in range(rng.randrange(25, 70)):
        c = rng.random()
        if c < 0.22:
            ops.append('pf:%d' % rng.randrange(100))
        elif c < 0.44:
            ops.append('pb:%d' % rng.randrange(100))
        elif c < 0.58:
            ops.append('popf')
        elif c < 0.72:
            ops.append('popb')
        elif c < 0.79:
            ops.append('peekf')
        elif c < 0.86:
            ops.append('peekb')
        elif c < 0.93:
            ops.append('len')
        else:
            ops.append('to_list')
    return ops

def _queue(rng):
    ops = []
    for _ in range(rng.randrange(25, 70)):
        c = rng.random()
        if c < 0.45:
            ops.append('enq:%d' % rng.randrange(100))
        elif c < 0.7:
            ops.append('deq')
        elif c < 0.82:
            ops.append('peek')
        elif c < 0.92:
            ops.append('len')
        else:
            ops.append('to_list')
    return ops

def _dll(rng):
    tag = rng.choice([1, 2, 5])
    ops = [str(tag)]
    live = 0
    for _ in range(rng.randrange(25, 70)):
        c = rng.random()
        ref = '%d:%d' % (rng.choice([tag, tag + 1]), rng.randrange(0, max(1, live + 2)))
        if c < 0.2:
            ops.append('pf:%d' % rng.randrange(100))
            live += 1
        elif c < 0.4:
            ops.append('pb:%d' % rng.randrange(100))
            live += 1
        elif c < 0.5:
            ops.append('ib:%s:%d' % (ref, rng.randrange(100)))
            live += 1
        elif c < 0.6:
            ops.append('ia:%s:%d' % (ref, rng.randrange(100)))
            live += 1
        elif c < 0.7:
            ops.append('rm:%s' % ref)
        elif c < 0.77:
            ops.append('get:%s' % ref)
        elif c < 0.83:
            ops.append('set:%s:%d' % (ref, rng.randrange(100)))
        elif c < 0.88:
            ops.append('nx:%s' % ref)
        elif c < 0.93:
            ops.append('pv:%s' % ref)
        elif c < 0.97:
            ops.append('len')
        else:
            ops.append('to_list')
    return ops

def _heap(rng, kind):
    words = ['apple', 'fig', 'pear', 'kiwi', 'date', 'plum', 'banana']
    ops = [kind]
    for _ in range(rng.randrange(25, 60)):
        c = rng.random()
        v = str(rng.randrange(1000)) if kind == 'u32' else rng.choice(words)
        if c < 0.4:
            ops.append('push:%s' % v)
        elif c < 0.62:
            ops.append('pop')
        elif c < 0.74:
            ops.append('peek')
        elif c < 0.8:
            vals = [str(rng.randrange(1000)) if kind == 'u32' else rng.choice(words) for _ in range(rng.randrange(1, 7))]
            ops.append('from:' + ','.join(vals))
        elif c < 0.9:
            ops.append('len')
        else:
            ops.append('sorted')
    return ops

def _bst(rng, kind):
    words = ['ant', 'bee', 'cow', 'doe', 'eel', 'fox', 'gnu', 'hen']
    ops = [kind]

    def key():
        return str(rng.randrange(20)) if kind == 'u32' else rng.choice(words)
    for _ in range(rng.randrange(30, 80)):
        c = rng.random()
        if c < 0.3:
            ops.append('ins:%s:%d' % (key(), rng.randrange(100)))
        elif c < 0.45:
            ops.append('rm:%s' % key())
        elif c < 0.55:
            ops.append('get:%s' % key())
        elif c < 0.63:
            ops.append('has:%s' % key())
        elif c < 0.69:
            ops.append('min')
        elif c < 0.75:
            ops.append('max')
        elif c < 0.82:
            ops.append('lb:%s' % key())
        elif c < 0.89:
            ops.append('range:%s:%s' % (key(), key()))
        elif c < 0.95:
            ops.append('len')
        else:
            ops.append('list')
    return ops

def _bitset(rng):
    n = rng.choice([1, 7, 32, 33, 64, 70])
    ops = [str(n)]
    for _ in range(rng.randrange(25, 60)):
        c = rng.random()
        i = rng.randrange(0, n + 2)
        if c < 0.25:
            ops.append('set:%d' % i)
        elif c < 0.4:
            ops.append('clear:%d' % i)
        elif c < 0.52:
            ops.append('get:%d' % i)
        elif c < 0.6:
            ops.append('count')
        elif c < 0.8:
            bits = ''.join((rng.choice('01') for _ in range(rng.choice([n, n, n, n + 1]))))
            ops.append(rng.choice(['or', 'and', 'diff', 'xor']) + ':' + bits)
        elif c < 0.9:
            ops.append('len')
        else:
            ops.append('list')
    return ops

def _uf(rng):
    n = rng.choice([1, 4, 9, 16])
    ops = [str(n)]
    for _ in range(rng.randrange(25, 60)):
        c = rng.random()
        (a, b) = (rng.randrange(0, n + 1), rng.randrange(0, n + 1))
        if c < 0.35:
            ops.append('union:%d:%d' % (a, b))
        elif c < 0.55:
            ops.append('find:%d' % a)
        elif c < 0.7:
            ops.append('conn:%d:%d' % (a, b))
        elif c < 0.85:
            ops.append('size:%d' % a)
        else:
            ops.append('count')
    return ops

def _seg(rng):
    if rng.random() < 0.5:
        n = rng.choice([1, 3, 8, 13])
        ops = ['new:%d' % n]
    else:
        n = rng.randrange(1, 14)
        ops = ['list:' + ','.join((str(rng.randrange(4294967295)) for _ in range(n)))]
    for _ in range(rng.randrange(25, 60)):
        c = rng.random()
        (i, j) = (rng.randrange(0, n + 2), rng.randrange(0, n + 2))
        if c < 0.2:
            ops.append('get:%d' % i)
        elif c < 0.4:
            ops.append('set:%d:%d' % (i, rng.randrange(4294967295)))
        elif c < 0.65:
            ops.append('query:%d:%d' % (i, j))
        elif c < 0.9:
            ops.append('add:%d:%d:%d' % (i, j, rng.randrange(4294967295)))
        else:
            ops.append('len')
    return ops

def differential(name, seed):
    """Deterministic pseudo-random operation history for one structure."""
    rng = random.Random(seed)
    if name == 'dynamic_array':
        return _da(rng, seed % 2 == 0)
    if name == 'deque':
        return _deque(rng)
    if name == 'queue':
        return _queue(rng)
    if name == 'doubly_linked_list':
        return _dll(rng)
    if name == 'binary_heap':
        return _heap(rng, 'u32' if seed % 2 else 'str')
    if name == 'balanced_search_tree':
        return _bst(rng, 'u32' if seed % 2 else 'str')
    if name == 'bitset':
        return _bitset(rng)
    if name == 'union_find':
        return _uf(rng)
    if name == 'segment_tree':
        return _seg(rng)
    raise KeyError(name)
LRU_SCENARIOS = [['3', 'len', 'keys', 'add:a:1', 'add:b:2', 'add:c:3', 'len', 'keys', 'get:a', 'keys', 'add:d:4', 'keys', 'peek:b', 'has:b', 'has:a', 'rm:a', 'keys', 'len', 'oldest', 'rmold', 'keys', 'len'], ['1', 'add:x:1', 'add:y:2', 'keys', 'get:x', 'get:y', 'len', 'rm:z', 'rm:y', 'len', 'keys', 'oldest'], ['2', 'get:missing', 'peek:missing', 'has:missing', 'rm:missing', 'oldest', 'rmold', 'len', 'keys']]
OPS['stack'] = {'new': '', 'length': 'len', 'push': 'push', 'pop': 'pop', 'peek': 'peek', 'to_list': 'to_list'}
CTOR_OPS['stack'] = {'new': lambda args: True}
FUNCTIONAL['stack'] = [['push:10', 'push:20', 'peek', 'len', 'pop', 'to_list', 'pop', 'len'], ['push:1', 'push:2', 'push:3', 'to_list', 'pop', 'push:4', 'to_list']]
BOUNDARY['stack'] = [['pop', 'peek', 'len', 'to_list'], ['push:0', 'pop', 'pop', 'to_list']]

def _generation_tokens(args):
    out = [args[0]]
    for token in args[1:]:
        p = token.split(':')
        if p[0] in ['rm', 'get', 'nx', 'pv'] and len(p) == 3:
            p.append('0')
        if p[0] in ['set', 'ib', 'ia'] and len(p) == 4:
            p.insert(3, '0')
        out.append(':'.join(p))
    return out
FUNCTIONAL['doubly_linked_list'] = [_generation_tokens(x) for x in FUNCTIONAL['doubly_linked_list']]
BOUNDARY['doubly_linked_list'] = [_generation_tokens(x) for x in BOUNDARY['doubly_linked_list']]
_previous_differential = differential

def differential(name, seed):
    if name == 'stack':
        return [x.replace('enq', 'push').replace('deq', 'pop') for x in _previous_differential('queue', seed)]
    args = _previous_differential(name, seed)
    return _generation_tokens(args) if name == 'doubly_linked_list' else args
