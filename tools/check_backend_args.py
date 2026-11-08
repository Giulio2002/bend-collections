#!/usr/bin/env python3
"""Check that each backend runner forwards exactly the application's arguments."""
from backend_diff import Module, PATHS, Runner


def main():
    module = Module('args', 'base', 'tests/backend_diff/args.bend', None, 0, 0, 'IO.args')
    runner = Runner(module, threads=2, timeout=60)
    errors = runner.build()
    if errors:
        raise SystemExit('\n'.join(errors))
    cases = [[], ['hello'], [''], ['with spaces', 'café'],
             ['--', '--threads', '1', '-1', '-o'], ['first', '', 'last']]
    for argv in cases:
        expected = ''.join('arg:' + arg + '\n' for arg in argv)
        for backend, (status, output, error, _) in runner.all(argv, PATHS).items():
            if status != 'ok' or output != expected:
                raise SystemExit('%s argv %r: expected %r, got %s %r (%s)' %
                                 (backend, argv, expected, status, output, error))
    print('backend args: %d cases pass across run/C/JS' % len(cases))


if __name__ == '__main__':
    main()
