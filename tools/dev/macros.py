#!/usr/bin/env python3
"""Dev helper: expand @NAME@ type macros in a .bend.in file into a .bend file.
usage: tools/dev/macros.py in_file out_file"""
import sys
M = {
  'NB': 'B.OrdMap<U32, Unit>',
  'NBL': 'List<&2, BE.Entry<U32, Unit>>',
  'ADJ': 'B.OrdMap<U32, B.OrdMap<U32, Unit>>',
  'ADJL': 'List<&2, BE.Entry<U32, B.OrdMap<U32, Unit>>>',
  'MADJ': 'List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>',
  'U': '~U32, ~U32.cmp',
  'UO': '~U32, ~U32.cmp, ~O.u32_order',
  'EL': 'List<&2, BE.Entry<String, V>>',
  'EN': 'BE.Entry<String, V>',
  'SKO': '~String, ~String.order, ~O.string_order',
  'SK': '~String, ~String.order',
  'MB': 'Maybe<&2, BE.Entry<String, V>>',
  'NT': 'D.Node<T>',
  'NM': 'B.OrdMap<Nat, D.Node<T>>',
  'NEL': 'List<&2, BE.Entry<Nat, D.Node<T>>>',
  'NE': 'BE.Entry<Nat, D.Node<T>>',
  'IL': 'List<&2, E.Item<T>>',
  'MN': 'Maybe<&2, Nat>',
  'MNT': 'Maybe<&2, D.Node<T>>',
  'NKO': '~Nat, ~Nat.cmp, ~O.nat_order',
  'NK': '~Nat, ~Nat.cmp',
  'St': 'D.DList<T>',
  'Mo': 'DS.Model<T>',
  'Ob': 'E.Obs<T>',
  'Op': 'E.Op<T>',
  'DL': 'D.DL{tag, fresh, count, head, tail, nodes}',
  'WX': 'W(T, count, nodes, head)',
  'FLD': '+tag: Nat, +fresh: Nat, +count: Nat, +head: Maybe<&2, Nat>, +tail: Maybe<&2, Nat>, +nodes: B.OrdMap<Nat, D.Node<T>>',
  'FA': 'tag, fresh, count, head, tail, nodes',
  'GD': 'F.Good(T, nodes, head, tail, count, fresh',
}
src = open(sys.argv[1]).read()
for k, v in M.items():
    src = src.replace('@' + k + '@', v)
open(sys.argv[2], 'w').write(src)
