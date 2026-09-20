#!/usr/bin/env python3
"""Dev helper: permute the top-level arguments of calls (and def parameter
lists) of named functions. usage: permute_args.py FILE NAME=i,j,k... ..."""
import sys

def split_args(s, i):
    # s[i] == '(' ; return (args, end_index_after_close)
    depth = 0; args = []; cur = ''; j = i + 1
    while j < len(s):
        ch = s[j]
        if ch in '({<[' :
            depth += 1
        elif ch in ')}>]':
            if depth == 0 and ch == ')':
                args.append(cur); return args, j + 1
            depth -= 1
        if ch == ',' and depth == 0:
            args.append(cur); cur = ''
        else:
            cur += ch
        j += 1
    raise ValueError('unbalanced')

def rewrite(s, name, perm):
    out = ''; i = 0
    while True:
        k = s.find(name + '(', i)
        if k < 0:
            out += s[i:]; return out
        prev = s[k-1] if k > 0 else ' '
        if prev.isalnum() or prev in '_.' and not s[max(0,k-2):k] == 'P.' and not name.startswith('P.'):
            out += s[i:k+len(name)]; i = k + len(name); continue
        args, end = split_args(s, k + len(name))
        args = [a.strip() for a in args]
        if len(args) != len(perm):
            out += s[i:end]; i = end; continue
        # recurse inside arguments first
        args = [rewrite(a, name, perm) for a in args]
        out += s[i:k] + name + '(' + ', '.join(args[p] for p in perm) + ')'
        i = end

f = sys.argv[1]
s = open(f).read()
for spec in sys.argv[2:]:
    name, p = spec.split('=')
    s = rewrite(s, name, [int(x) for x in p.split(',')])
open(f, 'w').write(s)
