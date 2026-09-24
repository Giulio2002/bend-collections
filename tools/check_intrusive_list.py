#!/usr/bin/env python3
"""Compare actual Bend state and callback traces with a Python sequence model."""
import argparse
import itertools
import json
import os
from pathlib import Path
import random
import subprocess

ROOT = Path(__file__).resolve().parents[1]

class Model:
    def __init__(self):
        self.lists = [[], [], [], []]
        self.values = {i: i for i in range(1, 17)}
        self.pool = []
        self.fresh = 17
        self.events = []

    def remove(self, root, node):
        xs = self.lists[root]
        assert node in xs
        if xs[0] == node:
            self.events.append(1000 + root * 100 + (xs[1] if len(xs) > 1 else 0))
        xs.remove(node)

    def prepend(self, root, node):
        association = (0, 1) if root < 2 else (2, 3)
        assert all(node not in self.lists[r] for r in association)
        self.lists[root].insert(0, node)
        self.events.append(2000 + root * 100 + node)

    def predicate(self, mode, value):
        self.events.append(4000 + value)
        if mode == 3 and value == 1:
            self.remove(0, value)
            return False
        return mode in (1, 3) or (mode == 0 and value % 2 == 0)

    def convert(self, value):
        self.events.append(5000 + value)
        return value * 10 if value % 2 == 0 else None

    def make(self, value):
        n = self.fresh
        assert n < 32
        self.fresh += 1
        self.values[n] = value
        self.events.append(6000 + value)
        return n

    def free(self, n):
        assert n not in self.pool
        assert all(n not in xs for xs in self.lists)
        self.events.append(7000 + n)
        self.pool.insert(0, n)

    def snapshot(self, out):
        cells = [0] * 192
        for root, xs in enumerate(self.lists):
            cells[root] = xs[0] if xs else 0
            start = 32 if root < 2 else 96
            for i, n in enumerate(xs):
                cells[start + n] = xs[i+1] if i+1 < len(xs) else 0
                cells[start + 32 + n] = xs[i-1] if i else 0
        for i, n in enumerate(self.pool):
            cells[32+n] = self.pool[i+1] if i+1 < len(self.pool) else 0
        for n, v in self.values.items():
            cells[160+n] = v
        result = '|'.join([str(out), ','.join(map(str, cells)), ','.join(map(str, self.events)),
                           f'{self.fresh},{len(self.pool)},{self.pool[0] if self.pool else 0}'])
        self.events = []
        return result

    def step(self, token):
        fields = (token + ':0:0:0').split(':')
        op, x, y, fuel = fields[0], *map(int, fields[1:4])
        op = op.removesuffix('_same')
        out = 'OK'
        if op == 'reset':
            self.__init__()
        elif op in ('p', 'ps', 'p2'):
            self.prepend(x, y)
        elif op in ('r', 'r2'):
            self.remove(x, y)
        elif op == 'head':
            out = self.lists[x][0] if self.lists[x] else 'none'
        elif op in ('next', 'prev'):
            xs = next((xs for xs in self.lists[:2] if x in xs), [])
            at = xs.index(x) + (1 if op == 'next' else -1) if xs else -1
            out = xs[at] if 0 <= at < len(xs) else 'none'
        elif op == 'value':
            out = self.values[x]
        elif op in ('is_empty', 'non_empty', 'at_least_two'):
            out = int(not self.lists[x]) if op == 'is_empty' else int(len(self.lists[x]) >= (2 if op == 'at_least_two' else 1))
        elif op == 'length':
            out = len(self.lists[x]) if fuel >= len(self.lists[x]) else 'ERR limit'
        elif op in ('clear_list', 'clear_list_with_pool'):
            xs = self.lists[x][:]
            if len(xs) > fuel:
                out = 'ERR limit'
            elif xs:
                self.lists[x] = []
                self.events.append(1000 + x * 100)
                for n in xs[1:] + xs[:1]:
                    if op.endswith('with_pool'):
                        self.free(n)
                    else:
                        self.events.append(7000+n)
        elif op in ('foreach', 'foreach-remove', 'fold'):
            xs = self.lists[x][:]
            total = 0
            for n in xs[:fuel]:
                v = self.values[n]
                self.events.append(3000 + v)
                total += v
                if op == 'foreach-remove':
                    self.remove(y, v)
            out = 'ERR limit' if fuel < len(xs) else total if op == 'fold' else 'OK'
        elif op.startswith('foreach_remove_'):
            prefix = True
            current = self.lists[x][0] if self.lists[x] else None
            while current is not None:
                if fuel == 0:
                    out = 'ERR limit'
                    break
                fuel -= 1
                xs = self.lists[x]
                saved_next = xs[xs.index(current)+1:][:1]
                value = self.values[current]
                if 'convert' in op:
                    value = self.convert(value)
                if value is None:
                    keep = False
                elif op == 'foreach_remove_convert':
                    self.events.append(3000 + value)
                    keep = True
                else:
                    keep = self.predicate(y, value)
                if prefix:
                    if not self.lists[x]:
                        out = 'ERR traversal'
                        break
                    live = self.lists[x][0]
                    if keep:
                        prefix = False
                        current = self.lists[x][1] if len(self.lists[x]) > 1 else None
                    else:
                        self.remove(x, live)
                        self.events.append(7000 + live)
                        current = self.lists[x][0] if self.lists[x] else None
                else:
                    if not keep:
                        self.remove(x, current)
                        self.events.append(7000 + current)
                    current = saved_next[0] if saved_next else None
        elif op in ('map_to_list', 'flat_map_to_list', 'to_list'):
            xs = self.lists[x]
            if len(xs) > fuel:
                out = 'ERR limit'
            else:
                mapped = []
                for n in reversed(xs):
                    v = self.values[n]
                    if op != 'to_list':
                        self.events.append(3000 + v)
                    if op != 'flat_map_to_list' or v % 2 == 0:
                        mapped.insert(0, v if op == 'to_list' else 10*v)
                out = ','.join(map(str, mapped))
        elif op in ('find', 'find_some_this', 'find_convert', 'find_value', 'find_value_convert', 'exists', 'forall', 'count'):
            current = self.lists[x][0] if self.lists[x] else None
            out = 0 if op in ('count','exists') else 1 if op == 'forall' else 'none'
            while current is not None:
                if fuel == 0:
                    out = 'ERR limit'
                    break
                fuel -= 1
                value = self.values[current]
                if 'convert' in op:
                    value = self.convert(value)
                hit = value is not None and (value == y if 'value' in op else self.predicate(y, value))
                if op == 'count':
                    out += int(hit)
                elif hit != (op == 'forall'):
                    out = int(hit) if op in ('exists', 'forall') else current
                    break
                xs = self.lists[x]
                i = xs.index(current)+1 if current in xs else len(xs)
                current = xs[i] if i < len(xs) else None
        elif op in ('from_nodes', 'from_empty', 'from_values', 'map_from_nodes', 'map_from_values'):
            assert not self.lists[0]
            values = [] if op == 'from_empty' else [x,y]
            nodes = []
            for v in values:
                if op == 'map_from_values':
                    self.events.append(3000 + v)
                    v *= 10
                nodes.append(v if op == 'from_nodes' else self.make(v))
            self.lists[0] = nodes
            out = nodes[0] if nodes else 'none'
        elif op == 'pool-new':
            assert not self.pool
            # Construction calls the factory, not the user post-remove hook.
            for _ in range(max(1,fuel)):
                self.pool.insert(0,self.make(0))
        elif op == 'pool-free':
            self.free(x)
        elif op == 'pool-next':
            out = self.pool.pop(0) if self.pool else self.make(0)
        else:
            raise AssertionError(op)
        return self.snapshot(out)


def cases():
    commands = ['head','next','prev','value','is_empty','non_empty','at_least_two','length','find','find_some_this','find_convert','find_value','find_value_convert','exists','forall','count','foreach','fold','map_to_list','flat_map_to_list','to_list','clear_list','clear_list_same','clear_list_with_pool','clear_list_with_pool_same','foreach_remove_filter','foreach_remove_filter_same','foreach_remove_convert','foreach_remove_convert_same','foreach_remove_convert_filter','foreach_remove_convert_filter_same']
    # Every order of up to four distinct nodes; every bound around exhaustion.
    for size in range(5):
        for xs in itertools.permutations(range(1,size+1)):
            setup = [f'p:0:{n}' for n in reversed(xs)]
            for cmd in commands:
                for fuel in sorted({0,max(0,size-1),size,size+1}):
                    # Direct observations take identities, root operations a root.
                    x = 1 if cmd in ('next','prev','value') else 0
                    yield setup + [f'{cmd}:{x}:0:{fuel}']
    for size in range(5):
        setup = [f'ps:0:{n}' for n in range(size,0,-1)]
        for cmd in ['find','exists','forall','count','find_convert','foreach_remove_filter','foreach_remove_filter_same']:
            for mode in [1,2,3]:
                yield setup + [f'{cmd}:0:{mode}:16']
        yield setup+['foreach-remove:0:0:16']
        yield setup+['find_value:0:2:16','find_value_convert:0:20:16']
    for cmd in ['from_nodes','from_empty','from_values','map_from_values','map_from_nodes']:
        yield [f'{cmd}:4:5','to_list:0:0:16','clear_list:0:0:16']
    for size in [0,1,2,5]:
        yield [f'pool-new:0:0:{size}']+['pool-next']*(max(1,size)+1)
    yield ['p:0:3','p:0:2','p:0:1','clear_list_with_pool:0:0:3','pool-next','pool-next','pool-next','pool-next']
    yield ['pool-free:4','pool-free:5','pool-next','pool-next','pool-next']
    # Random legal membership changes in TWO simultaneous associations.
    for seed in range(64):
        rng = random.Random(seed)
        membership = [[None]*17 for _ in range(2)]
        ops=[]
        for _ in range(200):
            a = rng.randrange(2); n = rng.randrange(1,17); old = membership[a][n]
            if old is not None:
                ops.append(f'{"r2" if a else "r"}:{old}:{n}')
            root = 2*a + rng.randrange(2)
            if rng.randrange(4) != 0:
                ops.append(f'{"p2" if a else "p"}:{root}:{n}')
                membership[a][n] = root
            else:
                membership[a][n] = None
        yield ops


def execute(program, tokens):
    r=subprocess.run(program+tokens, cwd=ROOT, capture_output=True,text=True,timeout=30,check=False,
                     env={**os.environ,'BEND_NO_TELEMETRY':'1'})
    if r.returncode or r.stderr.strip():
        raise AssertionError({'exit':r.returncode,'stderr':r.stderr[-3000:],'tokens':len(tokens)})
    return r.stdout.splitlines()


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--native',default='build/intrusive-list/test')
    p.add_argument('--js',default='build/intrusive-list/test.js')
    p.add_argument('--quick',action='store_true',help='one case per API plus randomized traces; full gate omits this')
    args=p.parse_args()
    programs=[[str(ROOT/args.native)],['node',str(ROOT/args.js)]]
    total=0; histories=0
    all_cases=list(cases())
    selected=[tokens for j,tokens in enumerate(all_cases)
              if not args.quick or j%61 == 0 or j >= len(all_cases)-200]
    batches=[];batch=[];size=0
    for case in selected:
        if size+len(case)+1 > 512 and batch:
            batches.append(batch);batch=[];size=0
        batch.append(case);size+=len(case)+1
    if batch: batches.append(batch)
    for start,batch in enumerate(batches):
        tokens=[t for case in batch for t in ['reset']+case]
        model=Model(); expected=[model.step(t) for t in tokens]
        for program in programs:
            observed=execute(program,tokens)
            if observed != expected:
                at=next((i for i,(a,b) in enumerate(itertools.zip_longest(observed,expected)) if a!=b),0)
                raise AssertionError({'program':program,'batch':start,'tokens':tokens[max(0,at-8):at+1],
                                      'observed':observed[at:at+1],'expected':expected[at:at+1]})
        total+=sum(map(len,batch));histories+=len(batch)
    report={'histories':histories,'operations':total,'backends':['C','JS'],'passed':True,'quick':args.quick}
    (ROOT/'build/intrusive-list/conformance.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report))

if __name__=='__main__': main()
