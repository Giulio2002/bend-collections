import sys, re, os
# Macro expander for proof sources.
# usage: mac.py in.src out.bend  (or expand(lines) from python)
#   %def NAME text        $NAME expands to text
#   %def NAME(a, b) text  $NAME(x, y) expands to text with a, b replaced (balanced parens)
#   %include file         imports only the %def lines of file
def load(path):
    lines = []
    for line in open(path).read().split('\n'):
        m = re.match(r'^%include (\S+)$', line)
        if m:
            inc = os.path.join(os.path.dirname(path), m.group(1))
            lines += [l for l in load(inc) if l.startswith('%def ')]
        else:
            lines.append(line)
    return lines

def split_args(s, i):
    # s[i] == '(' ; returns (args, index after ')')
    depth = 0; cur = ''; args = []; j = i
    while j < len(s):
        c = s[j]
        if c in '({[':
            depth += 1
            if depth > 1: cur += c
        elif c in ')}]':
            depth -= 1
            if depth == 0:
                args.append(cur.strip()); return args, j + 1
            cur += c
        elif c == ',' and depth == 1:
            args.append(cur.strip()); cur = ''
        else:
            cur += c
        j += 1
    raise SystemExit('unbalanced macro call')

def expand(src):
    defs = {}; pdefs = {}
    out = []
    for line in src:
        m = re.match(r'^%def (\w+)\(([^)]*)\) (.*)$', line)
        if m:
            pdefs[m.group(1)] = ([p.strip() for p in m.group(2).split(',')], m.group(3)); continue
        m = re.match(r'^%def (\w+) (.*)$', line)
        if m:
            defs[m.group(1)] = m.group(2); continue
        out.append(line)
    text = '\n'.join(out)
    names = sorted(defs, key=len, reverse=True)
    pnames = sorted(pdefs, key=len, reverse=True)
    for _ in range(40):
        new = text
        for n in pnames:
            params, body = pdefs[n]
            while True:
                m = re.search(r'\$' + n + r'\(', new)
                if not m: break
                args, end = split_args(new, m.end() - 1)
                env = dict(zip(params, args))
                pat = r'(?<![A-Za-z0-9_])(' + '|'.join(re.escape(p) for p in sorted(params, key=len, reverse=True)) + r')(?![A-Za-z0-9_])'
                pat0 = r'\$(' + '|'.join(re.escape(p) for p in sorted(params, key=len, reverse=True)) + r')(?![A-Za-z0-9_])'
                b = re.sub(pat0, lambda _m: '\x00' + _m.group(1) + '\x00', body)
                b = re.sub(r'\x00(\w+)\x00|' + pat, lambda _m: env[_m.group(1) or _m.group(2)], b)
                new = new[:m.start()] + b + new[end:]
        for n in names:
            new = re.sub(r'\$' + n + r'(?![A-Za-z0-9_])', lambda m: defs[n], new)
        if new == text:
            break
        text = new
    if '$' in re.sub(r'"[^"]*"', '', text):
        for l in text.split('\n'):
            if '$' in l:
                print('unexpanded:', l[:200], file=sys.stderr)
    return text


if __name__ == '__main__':
    open(sys.argv[2], 'w').write(expand(load(sys.argv[1])))
