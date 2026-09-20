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

# ---------------------------------------------------------------- operations

OPS = {
    'dynamic_array': {
        'new': '', 'length': 'len', 'capacity': 'cap', 'get': 'get',
        'set': 'set', 'push': 'push', 'pop': 'pop', 'reserve': 'reserve',
        'clear': 'clear', 'to_list': 'to_list',
    },
    'deque': {
        'new': '', 'length': 'len', 'push_front': 'pf', 'push_back': 'pb',
        'pop_front': 'popf', 'pop_back': 'popb', 'peek_front': 'peekf',
        'peek_back': 'peekb', 'to_list': 'to_list',
    },
    'queue': {
        'new': '', 'length': 'len', 'enqueue': 'enq', 'dequeue': 'deq',
        'peek': 'peek', 'to_list': 'to_list',
    },
    'doubly_linked_list': {
        'new': '', 'length': 'len', 'push_front': 'pf', 'push_back': 'pb',
        'insert_before': 'ib', 'insert_after': 'ia', 'remove': 'rm',
        'get': 'get', 'set': 'set', 'next': 'nx', 'prev': 'pv',
        'to_list': 'to_list',
    },
    'binary_heap': {
        'new': '', 'length': 'len', 'push': 'push', 'peek': 'peek',
        'pop': 'pop', 'from_list': 'from', 'to_sorted_list': 'sorted',
    },
    'balanced_search_tree': {
        'new': '', 'length': 'len', 'insert': 'ins', 'remove': 'rm',
        'lookup': 'get', 'contains': 'has', 'min': 'min', 'max': 'max',
        'lower_bound': 'lb', 'range': 'range', 'to_list': 'list',
    },
    'bitset': {
        'new': '', 'length': 'len', 'get': 'get', 'set': 'set',
        'clear': 'clear', 'count': 'count', 'union': 'or',
        'intersection': 'and', 'difference': 'diff', 'xor': 'xor',
        'to_list': 'list',
    },
    'union_find': {
        'new': '', 'find': 'find', 'union': 'union', 'connected': 'conn',
        'component_size': 'size', 'component_count': 'count',
    },
    'fenwick_tree': {
        'new': '', 'from_list': '', 'length': 'len', 'add': 'add',
        'prefix_sum': 'prefix', 'range_sum': 'range',
    },
    'segment_tree': {
        'new': '', 'from_list': '', 'length': 'len', 'get': 'get',
        'set': 'set', 'range_query': 'query', 'range_add': 'add',
    },
    'prefix_trie': {
        'new': '', 'insert': 'ins', 'lookup': 'get', 'remove': 'rm',
        'contains': 'has', 'prefix_entries': 'pre', 'longest_prefix': 'lp',
    },
    'graph': {
        'new': '', 'add_vertex': 'av', 'remove_vertex': 'rv',
        'add_edge': 'ae', 'remove_edge': 're', 'has_vertex': 'hv',
        'has_edge': 'he', 'neighbors': 'nb', 'vertices': 'vs',
        'edges': 'edges',
    },
}

# Operations exercised by a constructor argument rather than by a token: the
# scenario prefix that counts as covering them.
CTOR_OPS = {
    'dynamic_array': {'new': lambda a: True},
    'deque': {'new': lambda a: True},
    'queue': {'new': lambda a: True},
    'doubly_linked_list': {'new': lambda a: True},
    'binary_heap': {'new': lambda a: True},
    'balanced_search_tree': {'new': lambda a: True},
    'bitset': {'new': lambda a: True},
    'union_find': {'new': lambda a: True},
    'fenwick_tree': {'new': lambda a: a[0].startswith('new'),
                     'from_list': lambda a: a[0].startswith('list')},
    'segment_tree': {'new': lambda a: a[0].startswith('new'),
                     'from_list': lambda a: a[0].startswith('list')},
    'prefix_trie': {'new': lambda a: True},
    'graph': {'new': lambda a: True},
}

# ---------------------------------------------------------------- functional

FUNCTIONAL = {
    'dynamic_array': [
        ['nat', '10', 'len', 'cap', 'push:5', 'push:7', 'push:9', 'len', 'cap',
         'get:0', 'get:2', 'set:1:42', 'to_list', 'pop', 'to_list', 'len',
         'reserve:100', 'cap', 'to_list', 'clear', 'len', 'cap', 'to_list'],
        ['u32', '10', 'push:4294967295', 'push:0', 'push:1', 'get:0', 'get:1',
         'set:2:123456789', 'to_list', 'len', 'cap', 'pop', 'to_list',
         'reserve:64', 'cap', 'clear', 'to_list', 'len'],
        ['u32', '5', 'reserve:17', 'cap', 'len', 'push:1', 'to_list', 'clear',
         'cap', 'len', 'to_list'],
    ],
    'deque': [
        ['len', 'pf:1', 'pb:2', 'pf:3', 'pb:4', 'to_list', 'len', 'peekf',
         'peekb', 'popf', 'to_list', 'popb', 'to_list', 'peekf', 'peekb',
         'popf', 'popb', 'len', 'to_list'],
        ['pb:1', 'pb:2', 'pb:3', 'pb:4', 'pb:5', 'popf', 'popf', 'to_list',
         'pf:9', 'peekf', 'peekb', 'popb', 'popb', 'to_list', 'len'],
    ],
    'queue': [
        ['len', 'enq:1', 'enq:2', 'enq:3', 'to_list', 'len', 'peek', 'deq',
         'to_list', 'deq', 'peek', 'deq', 'len', 'to_list'],
        ['enq:7', 'deq', 'enq:8', 'enq:9', 'peek', 'to_list', 'deq', 'deq',
         'len', 'to_list'],
    ],
    'doubly_linked_list': [
        ['1', 'len', 'pf:10', 'pb:20', 'pb:30', 'to_list', 'len',
         'get:1:0', 'get:1:1', 'set:1:1:21', 'to_list',
         'ib:1:2:15', 'to_list', 'ia:1:0:11', 'to_list',
         'nx:1:0', 'pv:1:0', 'nx:1:2', 'pv:1:2',
         'rm:1:0', 'to_list', 'len', 'rm:1:1', 'rm:1:2', 'to_list', 'len'],
        ['7', 'pb:1', 'pb:2', 'pb:3', 'nx:7:1', 'pv:7:1', 'ia:7:2:99',
         'to_list', 'ib:7:0:88', 'to_list', 'get:7:3', 'set:7:3:77',
         'to_list', 'rm:7:3', 'to_list', 'len'],
    ],
    'binary_heap': [
        ['u32', 'len', 'push:5', 'push:3', 'push:9', 'push:1', 'len', 'peek',
         'sorted', 'pop', 'sorted', 'pop', 'peek', 'len',
         'from:8,2,6,4,10,1', 'len', 'sorted', 'peek', 'pop', 'sorted'],
        ['str', 'push:pear', 'push:apple', 'push:fig', 'peek', 'sorted',
         'pop', 'sorted', 'len', 'from:kiwi,banana,date', 'sorted', 'peek',
         'pop', 'len'],
        ['u32', 'push:7', 'push:7', 'push:7', 'sorted', 'len', 'pop',
         'sorted', 'peek'],
    ],
    'balanced_search_tree': [
        ['u32', 'len', 'ins:5:50', 'ins:2:20', 'ins:8:80', 'ins:1:10',
         'ins:9:90', 'len', 'list', 'get:2', 'get:7', 'has:8', 'has:7',
         'min', 'max', 'lb:3', 'lb:9', 'lb:10', 'range:2:9', 'range:0:100',
         'range:5:5', 'ins:5:55', 'get:5', 'len', 'rm:2', 'list', 'rm:2',
         'len', 'list'],
        ['str', 'ins:pear:1', 'ins:apple:2', 'ins:fig:3', 'list', 'min',
         'max', 'get:fig', 'has:plum', 'lb:b', 'range:apple:fig', 'rm:apple',
         'list', 'len'],
        ['u32', 'min', 'max', 'get:1', 'rm:1', 'lb:1', 'list', 'len',
         'range:0:1'],
    ],
    'bitset': [
        ['12', 'len', 'count', 'list', 'set:0', 'set:5', 'set:11', 'count',
         'list', 'get:5', 'get:6', 'clear:5', 'count', 'list',
         'or:000000000011', 'list', 'and:100000000001', 'list',
         'diff:100000000000', 'list', 'xor:111111111111', 'list', 'count',
         'len'],
        ['40', 'set:0', 'set:31', 'set:32', 'set:39', 'count', 'list',
         'get:32', 'clear:32', 'list', 'count', 'len'],
        ['1', 'len', 'count', 'set:0', 'list', 'count', 'xor:1', 'list',
         'count'],
        # 65 bits: ceil(65/32) = 3 words, so the packed array has one whole
        # padding word on top of the 31 unused tail bits of the last used
        # word. count / to_list / the combines must ignore both.
        ['65', 'set:0', 'set:31', 'set:32', 'set:63', 'set:64', 'count',
         'list', 'get:64', 'get:65', 'set:65', 'clear:64', 'count', 'list',
         'xor:' + '1' * 65, 'count', 'list', 'len'],
    ],
    'union_find': [
        ['8', 'count', 'find:0', 'find:7', 'conn:0:1', 'union:0:1', 'conn:0:1',
         'count', 'size:0', 'union:2:3', 'union:0:2', 'count', 'size:0',
         'size:3', 'find:3', 'union:0:1', 'conn:1:3', 'size:7', 'count'],
        ['5', 'union:0:1', 'union:1:2', 'union:3:4', 'count', 'size:2',
         'size:4', 'union:2:4', 'count', 'size:0', 'find:4', 'conn:0:4'],
    ],
    'fenwick_tree': [
        ['new:8', 'len', 'prefix:0', 'prefix:8', 'add:0:5', 'add:3:7',
         'add:7:1', 'prefix:1', 'prefix:4', 'prefix:8', 'range:0:4',
         'range:3:8', 'range:4:4', 'len'],
        ['list:1,2,3,4,5', 'len', 'prefix:5', 'range:1:4', 'add:2:100',
         'range:1:4', 'prefix:5', 'prefix:0'],
        ['list:4294967295,2', 'prefix:2', 'add:0:3', 'prefix:1', 'prefix:2',
         'range:0:2', 'len'],
    ],
    'segment_tree': [
        ['new:8', 'len', 'get:0', 'set:2:9', 'get:2', 'query:0:8',
         'query:2:3', 'add:1:5:4', 'get:1', 'get:4', 'query:0:8', 'query:1:5',
         'set:1:0', 'query:0:8', 'len'],
        ['list:1,2,3,4', 'len', 'query:0:4', 'get:3', 'add:0:4:10',
         'query:0:4', 'get:0', 'set:3:0', 'query:2:4', 'query:4:4'],
        ['list:4294967295,1', 'query:0:2', 'add:0:2:2', 'get:0', 'get:1',
         'query:0:2'],
        ['new:8', 'add:2:8:5', 'query:0:8', 'query:4:6', 'query:5:8', 'get:5',
         'add:1:7:3', 'query:0:8', 'query:2:6', 'set:3:100', 'query:0:8',
         'add:0:8:1', 'query:0:8', 'query:3:7', 'len'],
    ],
    'prefix_trie': [
        ['ins:car:1', 'ins:cart:2', 'ins:cat:3', 'ins::9', 'get:car',
         'get:ca', 'has:cat', 'has:ca', 'pre:ca', 'pre:car', 'pre:',
         'lp:cartoon', 'lp:ca', 'lp:dog', 'rm:car', 'pre:ca', 'get:car',
         'rm:car', 'has:cart'],
        ['ins:a:1', 'ins:ab:2', 'ins:abc:3', 'ins:b:4', 'pre:a', 'lp:abcd',
         'lp:abz', 'rm:ab', 'pre:a', 'lp:abcd', 'get:abc', 'has:ab'],
    ],
    'graph': [
        ['dir', 'vs', 'edges', 'av:1', 'av:2', 'av:3', 'vs', 'hv:1', 'hv:9',
         'ae:1:2', 'ae:1:3', 'ae:2:3', 'edges', 'nb:1', 'nb:3', 'he:1:2',
         'he:2:1', 'ae:1:2', 'edges', 're:1:2', 'edges', 're:1:2',
         'rv:3', 'vs', 'edges', 'nb:1'],
        ['undir', 'av:1', 'av:2', 'av:3', 'ae:1:2', 'ae:2:3', 'edges', 'nb:1',
         'nb:2', 'he:2:1', 'he:1:3', 're:1:2', 'edges', 'nb:2', 'rv:2', 'vs',
         'edges', 'nb:3'],
    ],
}

# ---------------------------------------------------------------- boundaries
# Every scenario ends with observations of the full state, so a rejected
# operation is checked to have changed nothing.

BOUNDARY = {
    'dynamic_array': [
        ['nat', '10', 'pop', 'len', 'to_list', 'get:0', 'set:0:1', 'len',
         'to_list', 'cap'],
        ['u32', '2', 'push:1', 'push:2', 'push:3', 'push:4', 'push:5',
         'to_list', 'len', 'cap', 'reserve:5', 'to_list', 'len', 'cap'],
        ['nat', '3', 'push:1', 'get:1', 'set:9:9', 'to_list', 'len',
         'reserve:9999', 'to_list', 'len', 'cap'],
        ['nat', '0', 'push:1', 'push:2', 'to_list', 'len', 'cap'],
    ],
    'deque': [
        ['popf', 'popb', 'peekf', 'peekb', 'len', 'to_list'],
        ['pf:1', 'popf', 'popf', 'peekb', 'len', 'to_list'],
    ],
    'queue': [
        ['deq', 'peek', 'len', 'to_list'],
        ['enq:1', 'deq', 'deq', 'peek', 'len', 'to_list'],
    ],
    'doubly_linked_list': [
        ['1', 'get:1:0', 'rm:1:0', 'len', 'to_list'],
        ['1', 'pb:5', 'get:2:0', 'to_list', 'len', 'set:2:0:9', 'to_list',
         'rm:2:0', 'to_list', 'nx:2:0', 'pv:2:0', 'ib:2:0:1', 'to_list'],
        ['1', 'pb:5', 'rm:1:0', 'get:1:0', 'to_list', 'len', 'set:1:0:9',
         'to_list', 'rm:1:0', 'nx:1:0', 'pv:1:0', 'ia:1:0:7', 'to_list',
         'len'],
    ],
    'binary_heap': [
        ['u32', 'peek', 'pop', 'len', 'sorted'],
        ['str', 'pop', 'peek', 'len', 'sorted'],
    ],
    'balanced_search_tree': [
        ['u32', 'get:1', 'rm:1', 'min', 'max', 'lb:0', 'len', 'list'],
        ['u32', 'ins:5:1', 'rm:6', 'list', 'len', 'get:6', 'lb:6',
         'range:9:2', 'range:5:5', 'list'],
    ],
    'bitset': [
        ['0', 'len', 'count', 'list', 'get:0', 'set:0', 'clear:0', 'list',
         'count'],
        ['4', 'get:4', 'set:4', 'clear:4', 'list', 'count', 'or:11111',
         'list', 'and:1', 'list', 'count', 'len'],
        # operands one bit shorter and one bit longer than a bitset whose
        # word array has a padding word: both must be LengthMismatch.
        ['65', 'or:' + '1' * 64, 'count', 'or:' + '1' * 66, 'count',
         'and:' + '1' * 65, 'count', 'len'],
    ],
    'union_find': [
        ['0', 'count', 'find:0', 'union:0:0', 'size:0', 'conn:0:0'],
        ['3', 'find:3', 'union:0:3', 'union:3:0', 'conn:0:3', 'size:3',
         'count', 'union:1:1', 'conn:1:1', 'size:1', 'count'],
    ],
    'fenwick_tree': [
        ['new:0', 'len', 'prefix:0', 'prefix:1', 'range:0:0', 'add:0:1',
         'len', 'prefix:0'],
        ['new:4', 'add:4:1', 'prefix:5', 'range:3:1', 'range:0:5',
         'prefix:4', 'len'],
    ],
    'segment_tree': [
        ['new:0', 'len', 'query:0:0', 'get:0', 'set:0:1', 'add:0:0:1',
         'query:0:1', 'len'],
        ['new:4', 'get:4', 'set:4:1', 'query:0:5', 'query:3:1', 'add:0:5:1',
         'add:3:1:1', 'query:0:4', 'len'],
    ],
    'prefix_trie': [
        ['get:x', 'rm:x', 'has:x', 'pre:x', 'lp:x', 'pre:'],
        ['ins:ab:1', 'rm:a', 'get:a', 'lp:a', 'pre:abc', 'has:ab', 'pre:'],
    ],
    'graph': [
        ['dir', 'ae:1:2', 're:1:2', 'nb:1', 'he:1:2', 'vs', 'edges',
         'rv:1', 'vs'],
        ['dir', 'av:1', 'av:1', 'vs', 'ae:1:1', 'edges', 'nb:1', 'ae:1:2',
         'edges', 'he:1:2', 're:1:1', 'rv:2', 'vs', 'edges'],
        ['undir', 'av:1', 'av:2', 're:1:2', 'edges', 'ae:1:2', 'ae:1:2',
         'edges', 'nb:1', 'nb:2'],
    ],
}


# --------------------------------------------------------------- structural
# Extra scenarios whose expected output is a structural report rather than an
# operation result. Only the red-black tree defines any: kinds "rb32"/"rbstr"
# make tests/balanced_search_tree/main.bend re-derive, after EVERY operation,
# the invariants of the tree src/ actually built (black root, no red-red
# parent/child edge, uniform black height on every root-to-leaf path,
# strictly increasing in-order keys, cached size = entry count).


def _asc(lo, hi):
    return ['ins:%d:%d' % (i, i) for i in range(lo, hi)]


def _desc(hi, lo):
    return ['ins:%d:%d' % (i, i) for i in range(hi, lo, -1)]


def _adversarial():
    """Interleaved deletes and inserts that drive every fixup case: delete
    from an ascending build (left-heavy deficiencies), from a descending
    build (right-heavy), and alternately from both ends."""
    ops = _asc(1, 33)
    for i in range(1, 17):                 # strip the left edge one by one
        ops.append('rm:%d' % i)
    ops += _desc(64, 48)                   # refill on the right, descending
    for i in range(32, 16, -1):            # strip the right of the old range
        ops.append('rm:%d' % i)
    for i in range(49, 65):                # alternate delete / re-insert
        ops.append('rm:%d' % i)
        ops.append('ins:%d:%d' % (i + 100, i))
    for i in range(149, 165):              # drain from both ends
        ops.append('rm:%d' % i)
        ops.append('rm:%d' % (313 - i))
    ops += ['len', 'list']
    return ops


STRUCTURAL = {
    'balanced_search_tree': [
        # empty tree: every query and the failing removal keep it empty
        ['rb32', 'len', 'list', 'min', 'max', 'get:1', 'rm:1', 'lb:0', 'range:0:9'],
        # singleton: build it, observe it, empty it again
        ['rb32', 'ins:7:70', 'len', 'list', 'min', 'max', 'rm:7', 'len', 'list'],
        # duplicate-key insert: value replaced, size and shape unchanged
        ['rb32', 'ins:4:1', 'ins:4:2', 'ins:4:3', 'len', 'get:4', 'ins:9:1',
         'ins:9:2', 'ins:4:4', 'len', 'rm:4', 'len', 'rm:4'],
        # removal of an absent key must change nothing
        ['rb32', 'ins:1:1', 'ins:2:2', 'ins:3:3', 'rm:99', 'rm:0', 'rm:2',
         'rm:2', 'list', 'len'],
        # removing the key stored AT THE ROOT (2 after inserting 1, 2, 3)
        ['rb32', 'ins:1:1', 'ins:2:2', 'ins:3:3', 'rm:2', 'list', 'rm:1',
         'rm:3', 'len'],
        # ordered (ascending) insertion, then ordered removal
        ['rb32'] + _asc(1, 41) + ['len'] + ['rm:%d' % i for i in range(1, 41)] + ['len', 'list'],
        # reverse-ordered insertion, then reverse-ordered removal
        ['rb32'] + _desc(40, 0) + ['len'] + ['rm:%d' % i for i in range(40, 0, -1)] + ['len', 'list'],
        # adversarial mixed delete/insert history
        ['rb32'] + _adversarial(),
        # the same structural checks over String keys (String.order instance)
        ['rbstr', 'ins:pear:1', 'ins:apple:2', 'ins:fig:3', 'ins:apple:4',
         'ins:kiwi:5', 'ins:date:6', 'ins:banana:7', 'ins:plum:8', 'len',
         'rm:fig', 'rm:fig', 'rm:apple', 'list', 'rm:zzz', 'len'],
    ],
}

for _k in OPS:
    STRUCTURAL.setdefault(_k, [])


SEEDS = [11, 23, 37, 59, 101]

# ------------------------------------------------------------- differential


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
        elif c < 0.70:
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
        if c < 0.20:
            ops.append('pf:%d' % rng.randrange(100)); live += 1
        elif c < 0.40:
            ops.append('pb:%d' % rng.randrange(100)); live += 1
        elif c < 0.50:
            ops.append('ib:%s:%d' % (ref, rng.randrange(100))); live += 1
        elif c < 0.60:
            ops.append('ia:%s:%d' % (ref, rng.randrange(100))); live += 1
        elif c < 0.70:
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
        if c < 0.40:
            ops.append('push:%s' % v)
        elif c < 0.62:
            ops.append('pop')
        elif c < 0.74:
            ops.append('peek')
        elif c < 0.80:
            vals = [str(rng.randrange(1000)) if kind == 'u32' else rng.choice(words)
                    for _ in range(rng.randrange(1, 7))]
            ops.append('from:' + ','.join(vals))
        elif c < 0.90:
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
        if c < 0.30:
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
        elif c < 0.40:
            ops.append('clear:%d' % i)
        elif c < 0.52:
            ops.append('get:%d' % i)
        elif c < 0.60:
            ops.append('count')
        elif c < 0.80:
            bits = ''.join(rng.choice('01') for _ in range(rng.choice([n, n, n, n + 1])))
            ops.append(rng.choice(['or', 'and', 'diff', 'xor']) + ':' + bits)
        elif c < 0.90:
            ops.append('len')
        else:
            ops.append('list')
    return ops


def _uf(rng):
    n = rng.choice([1, 4, 9, 16])
    ops = [str(n)]
    for _ in range(rng.randrange(25, 60)):
        c = rng.random()
        a, b = rng.randrange(0, n + 1), rng.randrange(0, n + 1)
        if c < 0.35:
            ops.append('union:%d:%d' % (a, b))
        elif c < 0.55:
            ops.append('find:%d' % a)
        elif c < 0.70:
            ops.append('conn:%d:%d' % (a, b))
        elif c < 0.85:
            ops.append('size:%d' % a)
        else:
            ops.append('count')
    return ops


def _fen(rng):
    if rng.random() < 0.5:
        n = rng.choice([1, 3, 8, 13])
        ops = ['new:%d' % n]
    else:
        n = rng.randrange(1, 14)
        ops = ['list:' + ','.join(str(rng.randrange(4294967295)) for _ in range(n))]
    for _ in range(rng.randrange(25, 60)):
        c = rng.random()
        i, j = rng.randrange(0, n + 2), rng.randrange(0, n + 2)
        if c < 0.40:
            ops.append('add:%d:%d' % (i, rng.randrange(4294967295)))
        elif c < 0.65:
            ops.append('prefix:%d' % i)
        elif c < 0.90:
            ops.append('range:%d:%d' % (i, j))
        else:
            ops.append('len')
    return ops


def _seg(rng):
    if rng.random() < 0.5:
        n = rng.choice([1, 3, 8, 13])
        ops = ['new:%d' % n]
    else:
        n = rng.randrange(1, 14)
        ops = ['list:' + ','.join(str(rng.randrange(4294967295)) for _ in range(n))]
    for _ in range(rng.randrange(25, 60)):
        c = rng.random()
        i, j = rng.randrange(0, n + 2), rng.randrange(0, n + 2)
        if c < 0.20:
            ops.append('get:%d' % i)
        elif c < 0.40:
            ops.append('set:%d:%d' % (i, rng.randrange(4294967295)))
        elif c < 0.65:
            ops.append('query:%d:%d' % (i, j))
        elif c < 0.90:
            ops.append('add:%d:%d:%d' % (i, j, rng.randrange(4294967295)))
        else:
            ops.append('len')
    return ops


def _trie(rng):
    alpha = 'abc'
    ops = []

    def word():
        return ''.join(rng.choice(alpha) for _ in range(rng.randrange(0, 5)))

    for _ in range(rng.randrange(25, 70)):
        c = rng.random()
        if c < 0.35:
            ops.append('ins:%s:%d' % (word(), rng.randrange(100)))
        elif c < 0.50:
            ops.append('rm:%s' % word())
        elif c < 0.62:
            ops.append('get:%s' % word())
        elif c < 0.74:
            ops.append('has:%s' % word())
        elif c < 0.87:
            ops.append('pre:%s' % word())
        else:
            ops.append('lp:%s' % word())
    return ops


def _graph(rng, mode):
    ops = [mode]
    for _ in range(rng.randrange(30, 80)):
        c = rng.random()
        u, v = rng.randrange(0, 7), rng.randrange(0, 7)
        if c < 0.20:
            ops.append('av:%d' % u)
        elif c < 0.28:
            ops.append('rv:%d' % u)
        elif c < 0.48:
            ops.append('ae:%d:%d' % (u, v))
        elif c < 0.60:
            ops.append('re:%d:%d' % (u, v))
        elif c < 0.68:
            ops.append('hv:%d' % u)
        elif c < 0.78:
            ops.append('he:%d:%d' % (u, v))
        elif c < 0.87:
            ops.append('nb:%d' % u)
        elif c < 0.94:
            ops.append('vs')
        else:
            ops.append('edges')
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
    if name == 'fenwick_tree':
        return _fen(rng)
    if name == 'segment_tree':
        return _seg(rng)
    if name == 'prefix_trie':
        return _trie(rng)
    if name == 'graph':
        return _graph(rng, 'dir' if seed % 2 else 'undir')
    raise KeyError(name)


# ------------------------------------------------------------------- the LRU

LRU_SCENARIOS = [
    ['3', 'len', 'keys', 'add:a:1', 'add:b:2', 'add:c:3', 'len', 'keys',
     'get:a', 'keys', 'add:d:4', 'keys', 'peek:b', 'has:b', 'has:a',
     'rm:a', 'keys', 'len', 'oldest', 'rmold', 'keys', 'len'],
    ['1', 'add:x:1', 'add:y:2', 'keys', 'get:x', 'get:y', 'len', 'rm:z',
     'rm:y', 'len', 'keys', 'oldest'],
    ['2', 'get:missing', 'peek:missing', 'has:missing', 'rm:missing',
     'oldest', 'rmold', 'len', 'keys'],
]
