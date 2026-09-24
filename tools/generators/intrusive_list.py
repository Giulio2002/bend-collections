#!/usr/bin/env python3
"""Lower the intrusive-list algorithms into Bend's state-threading helpers.

Only pair destructuring is generated. The emitted module has no interpreter,
callback dictionary, implicit storage, or FFI. Static callbacks let the native
compiler specialize link and root accessors without allocating closures.
"""
from pathlib import Path
import re
import argparse

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / 'src/containers/intrusive_doubly_linked_list.bend'
INTERNAL = ROOT / 'src/containers/internal/intrusive_list.bend'
COMPAT = ROOT / 'src/containers/compat/intrusive_doubly_linked_list.bend'
parts = []
SN = [('S', 'Type'), ('N', 'Data')]
NEXT = ('next', 'S -> N -> S & Maybe<&2, N>')
PREV = ('prev', 'S -> N -> S & Maybe<&2, N>')
SET_NEXT = ('set_next', 'S -> N -> Maybe<&2, N> -> S')
SET_PREV = ('set_prev', 'S -> N -> Maybe<&2, N> -> S')
GET = ('get_head', 'S -> H -> S & Maybe<&2, N>')
SET = ('set_head', 'S -> I -> Maybe<&2, N> -> S')
SET_FULL = ('set_head_nonempty', 'S -> I -> N -> S')
VALUE = ('value', 'S -> N -> S & V')
MN = 'Maybe<&2, N>'

PUBLIC_DOC = {
    'next': 'Read the next identity without changing membership.',
    'prev': 'Read the previous identity without changing membership.',
    'value': 'Observe a Data value (often the entity identity); payload ownership stays in S.',
    'get_head': 'Read a root; requires no writer context.',
    'remove': 'Detach a known member in O(1). Uses the nullable root setter only for a head.\n# Requires no root reader; preserves the node identity and payload.',
    'prepend_as': 'Prepend a detached node in O(1), using separate read/write contexts.\n# Calls the nonempty root setter exactly once.',
    'prepend': 'Prepend with the same context used to read and write the root.',
    'is_empty': 'O(1) empty-root query.',
    'non_empty': 'O(1) nonempty-root query.',
    'at_least_two': 'O(1) query: head exists and has a successor.',
    'fold_left': 'Forward fold, saving next before each callback. The accumulator may own Type data.',
    'foreach': 'Forward visit, saving next before each callback; removing current is supported.',
    'find': 'Return the first matching node identity; next is read after a failed predicate.',
    'find_some_this': 'Compatibility alias of find; Bend needs no preallocated Option wrapper.',
    'find_convert': 'Convert once per visited value, skip failed conversions, return the original node.',
    'find_value': 'Find with eq(wanted, observed_value), returning the node identity.',
    'find_value_convert': 'Find with eq(converted_value, wanted), returning the original node.',
    'exists': 'Short-circuit on the first true predicate; False for an empty list.',
    'forall': 'Short-circuit on the first false predicate; True for an empty list.',
    'count': 'Count matching values; read next after each predicate. O(n).',
    'length': 'Count members in O(n); no cached count is required in the root.',
    'clear_list_as': 'Preflight the bound, publish an empty root, detach suffix then original head.\n# Call post_remove once per detached node; a no-op callback needs no allocation.',
    'clear_list': 'Clear using one root context; see clear_list_as for callback order.',
    'clear_list_with_pool_as': 'Clear using a callback that returns each detached node to an application pool.\n# The pool argument locates that pool in S; post_remove performs the free.',
    'clear_list_with_pool': 'Clear to a pool using one root context.',
    'foreach_remove_filter_as': 'Keep true values, detach false values, then call post_remove on the removed node.\n# Re-read the live head in the prefix; save next when visiting the retained tail.',
    'foreach_remove_filter': 'Removal filter with one root context.',
    'foreach_remove_convert_filter_as': 'Remove failed conversions and false predicates; convert each visited value once.',
    'foreach_remove_convert_filter': 'Conversion/removal filter with one root context.',
    'foreach_remove_convert_as': 'Visit successfully converted values, remove failed conversions.',
    'foreach_remove_convert': 'Conversion/removal visitor with one root context.',
    'flat_map_to_list': 'Option filter-map: zero or one output per input. Callbacks run tail to head;\n# the newly allocated owning result list retains forward input order.',
    'map_to_list': 'Allocate a result list in forward order; evaluate callbacks tail to head.',
    'to_list': 'Allocate an owning list of observed values in forward order.',
    'from_values': 'Build from values in forward order using an application factory; return the head.\n# Factories must return distinct detached nodes. The root is not published here.',
    'from_nodes': 'Link distinct detached nodes in input order; return the head without allocating nodes.',
    'map_from_values': 'Convert then construct each node, both in forward order; return the head.',
    'map_from_nodes': 'Map each input to a detached node in forward order; return the head.',
    'pool_free': 'Push a detached node onto the LIFO pool; leave its payload unchanged. O(1).',
    'pool_next': 'Pop and clear the next link, or call make only when empty. O(1) before make.',
    'pool_new': 'Construct max(size, 1) nodes in a LIFO pool, using the application factory.',
    'new_node': 'Optional detached value wrapper. The application owns its storage and identities.',
}

def raw(s): parts.append(s.strip() + '\n\n')
def args(g): return ', '.join('~' + n for n, _ in g)
def call(n, g, *xs): return n + '(' + ', '.join([args(g)] + list(xs)) + ')'
def data(t):
    return t in {'N', 'V', 'H', 'I', 'C', 'D', 'Nat', 'Bool', 'U32', MN, 'Maybe<&2, V>', 'Maybe<&2, D>', 'List<&2, N>', 'List<&2, V>', 'List<&2, D>'}
def sig(ps): return ', '.join(('+' if data(t) else '') + n + ': ' + t for n, t in ps)
def fun(n, g, ps, out, body):
    params = ', '.join(['~' + k + ': ' + t for k, t in g] + ([sig(ps)] if ps else []))
    if n in PUBLIC_DOC:
        raw('# ' + PUBLIC_DOC[n])
    raw('def ' + n + '(' + params + ') -> ' + out + ':\n' + body)
def seq(n, g, ps, out, steps, expr):
    def build(j, known):
        if j == len(steps): return expr
        binds, run = steps[j]
        rest = ' '.join(s[1] for s in steps[j+1:]) + ' ' + expr
        captures = [(k,t) for k,t in known if k not in dict(binds) and re.search(r'\b'+k+r'\b', rest)]
        inner = build(j+1, captures + binds)
        name = n + '_' + str(j+1)
        if len(binds) == 1:
            fun(name, g, captures + binds, out, '  ' + inner)
        else:
            pat = ', '.join(('+' if data(t) else '') + k for k,t in binds)
            fun(name, g, captures + [('r', ' & '.join(t for k,t in binds))], out, '  ('+pat+') = r\n  '+inner)
        return call(name, g, *[k for k,t in captures], run)
    body = build(0, ps)
    fun(n, g, ps, out, '  ' + body)

raw('''# Generated by tools/generators/intrusive_list.py; edit that source.
import Base
import ./types/intrusive_doubly_linked_list.bend as E

# Intrusive doubly linked lists over application-owned nodes and roots.
#
# S is the affine application state, N a reusable node identity. Link accessors
# select one association; the same entity may have several independent pairs
# of links. H and I are independent read/write contexts for the same root.
# No container, tail, count, payload copy, or node allocation is required by
# prepend/remove. Bind the closed ~ accessors once in an application module.
#
# Preconditions: valid identities and coherent roots; prepend's node is
# detached in this association; remove's node belongs to the supplied root.
# Accessors preserve unrelated fields. Raw user input must be validated by
# the application before entering this preconditioned API.
#
# Traversals take an explicit step bound because array links are not a
# structurally decreasing Bend value. Exhaustion returns LimitExceeded with
# the updated state; callback effects already performed are retained.
# Link reads must be observations, and root hooks must preserve coherent links.
# clear preflights fuel before any write; callbacks may change only detached
# nodes and unrelated state, leaving the unvisited suffix intact.
# For finite fixed/decreasing membership, arena capacity is a sufficient
# O(1)-available bound. Callbacks must not invalidate a cached successor.
''')

# Public observations delegate to the application's selected association.
for name, param, T in [('next', NEXT, MN), ('prev', PREV, MN), ('value', VALUE, 'V')]:
    g = SN + ([('V','Data')] if name == 'value' else []) + [(name+'_of', param[1])]
    fun(name, g, [('s','S'),('node','N')], 'S & '+T, '  '+name+'_of(s, node)')

g = SN + [('H','Data'), GET]
fun('get_head', g, [('s','S'),('h','H')], 'S & '+MN, '  get_head(s, h)')

# Optional-neighbour writes are used by both edits and builders.
g = SN + [SET_NEXT]
fun('write_next', g, [('s','S'),('at',MN),('node',MN)], 'S', '''  match at:
    case None{}: s
    case Some{a}: set_next(s, a, node)''')
g = SN + [SET_PREV]
fun('write_prev', g, [('s','S'),('at',MN),('node',MN)], 'S', '''  match at:
    case None{}: s
    case Some{a}: set_prev(s, a, node)''')

rg = SN + [('I','Data'), SET_NEXT, SET_PREV, SET]
fun('remove_left', rg, [('s','S'),('i','I'),('node','N'),('before',MN),('after',MN)], 'S', '''  match before:
    case None{}:
      set_next(set_head(s, i, after), node, None{})
    case Some{+p}:
      set_next(set_prev(set_next(s, p, after), node, None{}), node, None{})''')
rg = SN + [('I','Data'), NEXT, PREV, SET_NEXT, SET_PREV, SET]
seq('remove', rg, [('s','S'),('i','I'),('node','N')], 'S', [
    ([('s','S'),('after',MN)], 'next(s, node)'),
    ([('s','S'),('before',MN)], 'prev(s, node)'),
    ([('s','S')], call('write_prev', SN+[SET_PREV], 's','after','before')),
], call('remove_left', SN+[('I','Data'),SET_NEXT,SET_PREV,SET], 's','i','node','before','after'))

pg = SN + [('H','Data'),('I','Data'),GET,SET_NEXT,SET_PREV,SET_FULL]
seq('prepend_as', pg, [('s','S'),('h','H'),('i','I'),('node','N')], 'S', [
    ([('s','S'),('head',MN)], 'get_head(s, h)'),
    ([('s','S')], 'set_next(s, node, head)'),
    ([('s','S')], call('write_prev',SN+[SET_PREV],'s','head','Some{node}')),
], 'set_head_nonempty(s, i, node)')
same = SN+[('H','Data'),GET,SET_NEXT,SET_PREV,('set_head_nonempty','S -> H -> N -> S')]
fun('prepend',same,[('s','S'),('h','H'),('node','N')],'S',
    '  prepend_as(~S, ~N, ~H, ~H, ~get_head, ~set_next, ~set_prev, ~set_head_nonempty, s, h, h, node)')

# Reader-only constant-time queries.
g = SN
fun('empty_result',g,[('r','S & '+MN)],'S & Bool','''  (s, m) = r
  (s, Maybe.is_none(&2, N, m))''')
fun('nonempty_result',g,[('r','S & '+MN)],'S & Bool','''  (s, m) = r
  (s, Maybe.is_some(&2, N, m))''')
g=SN+[('H','Data'),GET]
for name, helper in [('is_empty','empty_result'),('non_empty','nonempty_result')]:
    fun(name,g,[('s','S'),('h','H')],'S & Bool','  '+call(helper,SN,'get_head(s, h)'))
g=SN+[NEXT]
fun('two_head',g,[('s','S'),('head',MN)],'S & Bool','''  match head:
    case None{}: (s, False{})
    case Some{n}: '''+call('nonempty_result',SN,'next(s, n)'))
g=SN+[('H','Data'),GET,NEXT]
seq('at_least_two',g,[('s','S'),('h','H')],'S & Bool',[
    ([('s','S'),('head',MN)],'get_head(s, h)')],call('two_head',SN+[NEXT],'s','head'))

# ----- forward folds and visits -----
raw('# Forward visits save the successor before invoking user code.')
fg=SN+[('V','Data'),('A','Type'),('C','Data'),NEXT,VALUE,('fn','S -> C -> A -> V -> S & A')]
FR='S & Result<&2, &1, E.Error, A>'
FS='S & (Maybe<&2, N> & A)'
seq('fold_step',fg,[('s','S'),('node','N'),('c','C'),('acc','A')],FS,[
    ([('s','S'),('after',MN)],'next(s, node)'),
    ([('s','S'),('v','V')],'value(s, node)'),
    ([('s','S'),('acc','A')],'fn(s, c, acc, v)'),
], '(s, (after, acc))')
fun('fold_loop',fg,[('fuel','Nat'),('c','C'),('r',FS)],FR,'''  match fuel r:
    case _ Tuple{s, Tuple{None{}, acc}}: (s, Done{acc})
    case 0n Tuple{s, Tuple{Some{node}, acc}}: (s, Fail{E.LimitExceeded{}})
    case 1n+p Tuple{s, Tuple{Some{node}, acc}}:
      '''+call('fold_loop',fg,'p','c',call('fold_step',fg,'s','node','c','acc')))
g=SN+[('V','Data'),('A','Type'),('C','Data'),('H','Data'),GET,NEXT,VALUE,('fn','S -> C -> A -> V -> S & A')]
seq('fold_left',g,[('fuel','Nat'),('s','S'),('h','H'),('c','C'),('acc','A')],FR,[
    ([('s','S'),('head',MN)],'get_head(s, h)')],call('fold_loop',fg,'fuel','c','(s, (head, acc))'))

g=[('S','Type'),('V','Data'),('C','Data'),('fn','S -> C -> V -> S')]
fun('visit_fold',g,[('s','S'),('c','C'),('unit','Unit'),('v','V')],'S & Unit','  (fn(s, c, v), Unit{})')
g=SN+[('V','Data'),('C','Data'),('H','Data'),GET,NEXT,VALUE,('fn','S -> C -> V -> S')]
fun('foreach',g,[('fuel','Nat'),('s','S'),('h','H'),('c','C')],'S & Result<&2, &1, E.Error, Unit>',
    '  fold_left(~S, ~N, ~V, ~Unit, ~C, ~H, ~get_head, ~next, ~value, ~(s => c => a => v => visit_fold(~S, ~V, ~C, ~fn, s, c, a, v)), fuel, s, h, c, Unit{})')

# ----- first-match searches -----
sg=SN+[('V','Data'),('C','Data'),NEXT,VALUE,('pred','S -> C -> V -> S & Bool')]
SS='S & E.Search<N>'
SR='S & Result<&2, &1, E.Error, Maybe<&2, N>>'
seq('search_next',SN+[NEXT],[('s','S'),('node','N')],SS,[
    ([('s','S'),('after',MN)],'next(s, node)')],'(s, E.Seeking{after})')
fun('search_choice',SN+[NEXT],[('s','S'),('node','N'),('hit','Bool')],SS,'''  match hit:
    case True{}: (s, E.Found{node})
    case False{}: '''+call('search_next',SN+[NEXT],'s','node'))
seq('search_step',sg,[('s','S'),('node','N'),('c','C')],SS,[
    ([('s','S'),('v','V')],'value(s, node)'),
    ([('s','S'),('hit','Bool')],'pred(s, c, v)')],call('search_choice',SN+[NEXT],'s','node','hit'))
fun('search_loop',sg,[('fuel','Nat'),('c','C'),('r',SS)],SR,'''  match fuel r:
    case _ Tuple{s, E.Found{node}}: (s, Done{Some{node}})
    case _ Tuple{s, E.Seeking{None{}}}: (s, Done{None{}})
    case 0n Tuple{s, E.Seeking{Some{node}}}: (s, Fail{E.LimitExceeded{}})
    case 1n+p Tuple{s, E.Seeking{Some{node}}}:
      '''+call('search_loop',sg,'p','c',call('search_step',sg,'s','node','c')))
g=SN+[('V','Data'),('C','Data'),('H','Data'),GET,NEXT,VALUE,('pred','S -> C -> V -> S & Bool')]
seq('find',g,[('fuel','Nat'),('s','S'),('h','H'),('c','C')],SR,[
    ([('s','S'),('head',MN)],'get_head(s, h)')],call('search_loop',sg,'fuel','c','(s, E.Seeking{head})'))
fun('find_some_this',g,[('fuel','Nat'),('s','S'),('h','H'),('c','C')],SR,'  '+call('find',g,'fuel','s','h','c'))

BR='S & Result<&2, &1, E.Error, Bool>'
fun('search_bool',SN,[('negate','Bool'),('r',SR)],BR,'''  match negate r:
    case _ Tuple{s, Fail{e}}: (s, Fail{e})
    case False{} Tuple{s, Done{m}}: (s, Done{Maybe.is_some(&2, N, m)})
    case True{} Tuple{s, Done{m}}: (s, Done{Maybe.is_none(&2, N, m)})''')
fun('exists',g,[('fuel','Nat'),('s','S'),('h','H'),('c','C')],BR,
    '  '+call('search_bool',SN,'False{}',call('find',g,'fuel','s','h','c')))
fun('negated_result',[('S','Type')],[('r','S & Bool')],'S & Bool','''  (s, b) = r
  (s, Bool.not(b))''')
np=[('S','Type'),('V','Data'),('C','Data'),('pred','S -> C -> V -> S & Bool')]
fun('negated_pred',np,[('s','S'),('c','C'),('v','V')],'S & Bool','  negated_result(~S, pred(s, c, v))')
fun('forall',g,[('fuel','Nat'),('s','S'),('h','H'),('c','C')],BR,
    '  search_bool(~S, ~N, True{}, find(~S, ~N, ~V, ~C, ~H, ~get_head, ~next, ~value, ~(s => c => v => negated_pred(~S, ~V, ~C, ~pred, s, c, v)), fuel, s, h, c))')

fun('count_pick',[('S','Type')],[('count','Nat'),('r','S & Bool')],'S & Nat','''  match r:
    case Tuple{s, True{}}: (s, 1n+count)
    case Tuple{s, False{}}: (s, count)''')
cg=SN+[('V','Data'),('C','Data'),NEXT,VALUE,('pred','S -> C -> V -> S & Bool')]
CS='S & (Maybe<&2, N> & Nat)'
CR='S & Result<&2, &1, E.Error, Nat>'
seq('count_step',cg,[('s','S'),('node','N'),('c','C'),('acc','Nat')],CS,[
    ([('s','S'),('v','V')],'value(s, node)'),
    ([('s','S'),('acc','Nat')],'count_pick(~S, acc, pred(s, c, v))'),
    ([('s','S'),('after',MN)],'next(s, node)')],'(s, (after, acc))')
fun('count_loop',cg,[('fuel','Nat'),('c','C'),('r',CS)],CR,'''  match fuel r:
    case _ Tuple{s, Tuple{None{}, acc}}: (s, Done{acc})
    case 0n Tuple{s, Tuple{Some{node}, acc}}: (s, Fail{E.LimitExceeded{}})
    case 1n+p Tuple{s, Tuple{Some{node}, acc}}:
      '''+call('count_loop',cg,'p','c',call('count_step',cg,'s','node','c','acc')))
seq('count',g,[('fuel','Nat'),('s','S'),('h','H'),('c','C')],CR,[
    ([('s','S'),('head',MN)],'get_head(s, h)')],call('count_loop',cg,'fuel','c','(s, (head, 0n))'))
fun('node_value',SN,[('s','S'),('n','N')],'S & N','  (s, n)')
fun('count_node',SN,[('s','S'),('c','Unit'),('acc','Nat'),('node','N')],'S & Nat','  (s, 1n+acc)')
lg=SN+[('H','Data'),GET,NEXT]
fun('length',lg,[('fuel','Nat'),('s','S'),('h','H')],'S & Result<&2, &1, E.Error, Nat>',
    '  fold_left(~S, ~N, ~N, ~Nat, ~Unit, ~H, ~get_head, ~next, ~(s => n => node_value(~S, ~N, s, n)), ~(s => c => a => n => count_node(~S, ~N, s, c, a, n)), fuel, s, h, Unit{}, 0n)')

# Conversion is state-threaded too; each value is converted exactly once.
cv=[('convert','S -> V -> S & Maybe<&2, D>')]
cp=[('S','Type'),('V','Data'),('D','Data'),('C','Data')]+cv+[('pred','S -> C -> D -> S & Bool')]
fun('converted_pred_result',cp,[('c','C'),('r','S & Maybe<&2, D>')],'S & Bool','''  match r:
    case Tuple{s, None{}}: (s, False{})
    case Tuple{s, Some{v}}: pred(s, c, v)''')
fun('converted_pred',cp,[('s','S'),('c','C'),('v','V')],'S & Bool','  '+call('converted_pred_result',cp,'c','convert(s, v)'))
cg=SN+[('V','Data'),('D','Data'),('C','Data'),('H','Data'),GET,NEXT,VALUE]+cv+[('pred','S -> C -> D -> S & Bool')]
fun('find_convert',cg,[('fuel','Nat'),('s','S'),('h','H'),('c','C')],SR,
    '  find(~S, ~N, ~V, ~C, ~H, ~get_head, ~next, ~value, ~(s => c => v => converted_pred(~S, ~V, ~D, ~C, ~convert, ~pred, s, c, v)), fuel, s, h, c)')
eq=[('S','Type'),('V','Data'),('eq','V -> V -> Bool')]
fun('equal_value',eq,[('s','S'),('wanted','V'),('v','V')],'S & Bool','  (s, eq(wanted, v))')
g=SN+[('V','Data'),('H','Data'),GET,NEXT,VALUE,('eq','V -> V -> Bool')]
fun('find_value',g,[('fuel','Nat'),('s','S'),('h','H'),('wanted','V')],SR,
    '  find(~S, ~N, ~V, ~V, ~H, ~get_head, ~next, ~value, ~(s => c => v => equal_value(~S, ~V, ~eq, s, c, v)), fuel, s, h, wanted)')
# Converted-value equality compares the converted value on the left.
fun('equal_converted_value',eq,[('s','S'),('wanted','V'),('v','V')],'S & Bool','  (s, eq(v, wanted))')
g=SN+[('V','Data'),('D','Data'),('H','Data'),GET,NEXT,VALUE]+cv+[('eq','D -> D -> Bool')]
fun('find_value_convert',g,[('fuel','Nat'),('s','S'),('h','H'),('wanted','D')],SR,
    '  find_convert(~S, ~N, ~V, ~D, ~D, ~H, ~get_head, ~next, ~value, ~convert, ~(s => c => v => equal_converted_value(~S, ~D, ~eq, s, c, v)), fuel, s, h, wanted)')

# ----- clear: suffix first, original head last -----
post=('post_remove','S -> C -> N -> S')
dg=SN+[('C','Data'),NEXT,SET_NEXT,SET_PREV,post]
DR='S & Result<&2, &1, E.Error, Unit>'
seq('clear_step',dg,[('s','S'),('node','N'),('c','C')],'S & '+MN,[
    ([('s','S'),('after',MN)],'next(s, node)'),
    ([('s','S')],'set_prev(set_next(s, node, None{}), node, None{})'),
    ([('s','S')],'post_remove(s, c, node)')],'(s, after)')
fun('clear_loop',dg,[('fuel','Nat'),('head','N'),('c','C'),('r','S & '+MN)],DR,'''  match fuel r:
    case 0n Tuple{s, cursor}: (s, Fail{E.LimitExceeded{}})
    case 1n+p Tuple{s, None{}}:
      (post_remove(set_next(s, head, None{}), c, head), Done{Unit{}})
    case 1n+p Tuple{s, Some{node}}:
      '''+call('clear_loop',dg,'p','head','c',call('clear_step',dg,'s','node','c')))
ag=SN+[('H','Data'),('I','Data'),('C','Data'),GET,NEXT,SET_NEXT,SET_PREV,SET,post]
fun('clear_head',ag,[('fuel','Nat'),('s','S'),('h','H'),('i','I'),('c','C'),('head',MN)],DR,'''  match fuel head:
    case _ None{}: (s, Done{Unit{}})
    case 0n Some{node}: (s, Fail{E.LimitExceeded{}})
    case 1n+p Some{node}:
      '''+call('clear_loop',dg,'1n+p','node','c','next(set_head(s, i, None{}), node)'))
# Clear publishes an empty root before callbacks. Preflight prevents an
# insufficient bound from stranding a partially detached chain.
qg=SN+[NEXT]
fun('chain_fits',qg,[('fuel','Nat'),('r','S & '+MN)],'S & Bool','''  match fuel r:
    case _ Tuple{s, None{}}: (s, True{})
    case 0n Tuple{s, Some{node}}: (s, False{})
    case 1n+p Tuple{s, Some{node}}:
      '''+call('chain_fits',qg,'p','next(s, node)'))
fun('clear_checked',ag,[('fuel','Nat'),('h','H'),('i','I'),('c','C'),('head',MN),('r','S & Bool')],DR,'''  match r:
    case Tuple{s, False{}}: (s, Fail{E.LimitExceeded{}})
    case Tuple{s, True{}}:
      '''+call('clear_head',ag,'fuel','s','h','i','c','head'))
seq('clear_list_as',ag,[('fuel','Nat'),('s','S'),('h','H'),('i','I'),('c','C')],DR,[
    ([('s','S'),('head',MN)],'get_head(s, h)')],call('clear_checked',ag,'fuel','h','i','c','head',call('chain_fits',qg,'fuel','(s, head)')))

g=SN+[('H','Data'),('C','Data'),GET,NEXT,SET_NEXT,SET_PREV,('set_head','S -> H -> Maybe<&2, N> -> S'),post]
fun('clear_list',g,[('fuel','Nat'),('s','S'),('h','H'),('c','C')],DR,
    '  clear_list_as(~S, ~N, ~H, ~H, ~C, ~get_head, ~next, ~set_next, ~set_prev, ~set_head, ~post_remove, fuel, s, h, h, c)')
fun('ignore_removed',[('S','Type'),('C','Data'),('N','Data')],[('s','S'),('c','C'),('node','N')],'S','  s')
fun('clear_list_with_pool_as',ag,[('fuel','Nat'),('s','S'),('h','H'),('i','I'),('pool','C')],DR,
    '  '+call('clear_list_as',ag,'fuel','s','h','i','pool'))
fun('clear_list_with_pool',g,[('fuel','Nat'),('s','S'),('h','H'),('pool','C')],DR,
    '  '+call('clear_list',g,'fuel','s','h','pool'))

# ----- removal visitors: preserve the live-head prefix loop -----
raw('# Prefix predicates re-read the live head; the remaining tail saves next.')
ug=SN+[NEXT,PREV,SET_NEXT,SET_PREV]
fun('unlink_nonhead_links',SN+[SET_NEXT,SET_PREV],[('s','S'),('node','N'),('before',MN),('after',MN)],'S & Bool','''  match before:
    case None{}: (s, False{})
    case Some{+p}:
      (set_prev(set_next(set_next(write_prev(~S, ~N, ~set_prev, s, after, Some{p}), p, after), node, None{}), node, None{}), True{})''')
seq('unlink_nonhead',ug,[('s','S'),('node','N')],'S & Bool',[
    ([('s','S'),('after',MN)],'next(s, node)'),
    ([('s','S'),('before',MN)],'prev(s, node)')],call('unlink_nonhead_links',SN+[SET_NEXT,SET_PREV],'s','node','before','after'))

wg=SN+[('V','Data'),('H','Data'),('I','Data'),('C','Data'),GET,NEXT,PREV,SET_NEXT,SET_PREV,SET,VALUE,('pred','S -> C -> V -> S & Bool'),post]
WS='S & E.Filter<N>'
fun('filter_prefix_result',SN,[('r','S & '+MN)],WS,'''  (s, head) = r
  (s, E.Prefix{head})''')
fun('filter_tail_result',SN,[('r','S & '+MN)],WS,'''  (s, head) = r
  (s, E.Tail{head})''')
fun('filter_kept_head',wg,[('r','S & '+MN)],WS,'''  match r:
    case Tuple{s, None{}}: (s, E.FilterFailed{E.InvalidTraversal{}})
    case Tuple{s, Some{head}}: filter_tail_result(~S, ~N, next(s, head))''')
fun('filter_drop_head',wg,[('h','H'),('i','I'),('c','C'),('r','S & '+MN)],WS,'''  match r:
    case Tuple{s, None{}}: (s, E.FilterFailed{E.InvalidTraversal{}})
    case Tuple{s, Some{+node}}:
      filter_prefix_result(~S, ~N, get_head(post_remove(remove(~S, ~N, ~I, ~next, ~prev, ~set_next, ~set_prev, ~set_head, s, i, node), c, node), h))''')
fun('filter_prefix_choice',wg,[('h','H'),('i','I'),('c','C'),('r','S & Bool')],WS,'''  match r:
    case Tuple{s, True{}}:
      '''+call('filter_kept_head',wg,'get_head(s, h)')+'''
    case Tuple{s, False{}}:
      '''+call('filter_drop_head',wg,'h','i','c','get_head(s, h)'))
seq('filter_prefix_step',wg,[('s','S'),('h','H'),('i','I'),('c','C'),('node','N')],WS,[
    ([('s','S'),('v','V')],'value(s, node)')],call('filter_prefix_choice',wg,'h','i','c','pred(s, c, v)'))
fun('filter_tail_removed',wg,[('c','C'),('node','N'),('after',MN),('r','S & Bool')],WS,'''  match r:
    case Tuple{s, False{}}: (s, E.FilterFailed{E.InvalidTraversal{}})
    case Tuple{s, True{}}: (post_remove(s, c, node), E.Tail{after})''')
fun('filter_tail_choice',wg,[('c','C'),('node','N'),('after',MN),('r','S & Bool')],WS,'''  match r:
    case Tuple{s, True{}}: (s, E.Tail{after})
    case Tuple{s, False{}}:
      '''+call('filter_tail_removed',wg,'c','node','after',call('unlink_nonhead',ug,'s','node')))
seq('filter_tail_step',wg,[('s','S'),('c','C'),('node','N')],WS,[
    ([('s','S'),('after',MN)],'next(s, node)'),
    ([('s','S'),('v','V')],'value(s, node)')],call('filter_tail_choice',wg,'c','node','after','pred(s, c, v)'))
fun('filter_loop',wg,[('fuel','Nat'),('h','H'),('i','I'),('c','C'),('r',WS)],DR,'''  match fuel r:
    case _ Tuple{s, E.FilterFailed{e}}: (s, Fail{e})
    case _ Tuple{s, E.Prefix{None{}}}: (s, Done{Unit{}})
    case _ Tuple{s, E.Tail{None{}}}: (s, Done{Unit{}})
    case 0n Tuple{s, E.Prefix{Some{node}}}: (s, Fail{E.LimitExceeded{}})
    case 0n Tuple{s, E.Tail{Some{node}}}: (s, Fail{E.LimitExceeded{}})
    case 1n+p Tuple{s, E.Prefix{Some{node}}}:
      '''+call('filter_loop',wg,'p','h','i','c',call('filter_prefix_step',wg,'s','h','i','c','node'))+'''
    case 1n+p Tuple{s, E.Tail{Some{node}}}:
      '''+call('filter_loop',wg,'p','h','i','c',call('filter_tail_step',wg,'s','c','node')))
fun('foreach_remove_filter_as',wg,[('fuel','Nat'),('s','S'),('h','H'),('i','I'),('c','C')],DR,
    '  '+call('filter_loop',wg,'fuel','h','i','c','filter_prefix_result(~S, ~N, get_head(s, h))'))
swg=[p for p in wg if p[0]!='I']
swg=[(n,t.replace('I ->','H ->')) for n,t in swg]
fun('foreach_remove_filter',swg,[('fuel','Nat'),('s','S'),('h','H'),('c','C')],DR,
    '  foreach_remove_filter_as(~S, ~N, ~V, ~H, ~H, ~C, ~get_head, ~next, ~prev, ~set_next, ~set_prev, ~set_head, ~value, ~pred, ~post_remove, fuel, s, h, h, c)')
conv_g=SN+[('V','Data'),('D','Data'),('H','Data'),('I','Data'),('C','Data'),GET,NEXT,PREV,SET_NEXT,SET_PREV,SET,VALUE]+cv+[('pred','S -> C -> D -> S & Bool'),post]
fun('foreach_remove_convert_filter_as',conv_g,[('fuel','Nat'),('s','S'),('h','H'),('i','I'),('c','C')],DR,
    '  foreach_remove_filter_as(~S, ~N, ~V, ~H, ~I, ~C, ~get_head, ~next, ~prev, ~set_next, ~set_prev, ~set_head, ~value, ~(s => c => v => converted_pred(~S, ~V, ~D, ~C, ~convert, ~pred, s, c, v)), ~post_remove, fuel, s, h, i, c)')
scg=[(n,t.replace('I ->','H ->')) for n,t in conv_g if n!='I']
fun('foreach_remove_convert_filter',scg,[('fuel','Nat'),('s','S'),('h','H'),('c','C')],DR,
    '  foreach_remove_convert_filter_as(~S, ~N, ~V, ~D, ~H, ~H, ~C, ~get_head, ~next, ~prev, ~set_next, ~set_prev, ~set_head, ~value, ~convert, ~pred, ~post_remove, fuel, s, h, h, c)')
vg=[('S','Type'),('D','Data'),('C','Data'),('fn','S -> C -> D -> S')]
fun('visit_true',vg,[('s','S'),('c','C'),('v','D')],'S & Bool','  (fn(s, c, v), True{})')
cg=[(n,t) if n!='pred' else ('fn','S -> C -> D -> S') for n,t in conv_g]
fun('foreach_remove_convert_as',cg,[('fuel','Nat'),('s','S'),('h','H'),('i','I'),('c','C')],DR,
    '  foreach_remove_convert_filter_as(~S, ~N, ~V, ~D, ~H, ~I, ~C, ~get_head, ~next, ~prev, ~set_next, ~set_prev, ~set_head, ~value, ~convert, ~(s => c => v => visit_true(~S, ~D, ~C, ~fn, s, c, v)), ~post_remove, fuel, s, h, i, c)')
scg=[(n,t.replace('I ->','H ->')) for n,t in cg if n!='I']
fun('foreach_remove_convert',scg,[('fuel','Nat'),('s','S'),('h','H'),('c','C')],DR,
    '  foreach_remove_convert_as(~S, ~N, ~V, ~D, ~H, ~H, ~C, ~get_head, ~next, ~prev, ~set_next, ~set_prev, ~set_head, ~value, ~convert, ~fn, ~post_remove, fuel, s, h, h, c)')

# ----- result-list construction: reverse evaluation, forward output -----
fun('last_fold',SN,[('s','S'),('c','Unit'),('acc',MN),('node','N')],'S & '+MN,'  (s, Some{node})')
fun('last',lg,[('fuel','Nat'),('s','S'),('h','H')],SR,
    '  fold_left(~S, ~N, ~N, ~Maybe<&2, N>, ~Unit, ~H, ~get_head, ~next, ~(s => n => node_value(~S, ~N, s, n)), ~(s => c => a => n => last_fold(~S, ~N, s, c, a, n)), fuel, s, h, Unit{}, None{})')
fun('mapped_cons',[('T','Type')],[('m','Maybe<&1, T>'),('xs','List<&1, T>')],'List<&1, T>','''  match m:
    case None{}: xs
    case Some{x}: Con{x, xs}''')
mg=SN+[('V','Data'),('T','Type'),('C','Data'),PREV,VALUE,('fn','S -> C -> V -> S & Maybe<&1, T>')]
MS='S & (Maybe<&2, N> & List<&1, T>)'
MR='S & Result<&2, &1, E.Error, List<&1, T>>'
seq('map_step',mg,[('s','S'),('c','C'),('node','N'),('xs','List<&1, T>')],MS,[
    ([('s','S'),('v','V')],'value(s, node)'),
    ([('s','S'),('m','Maybe<&1, T>')],'fn(s, c, v)'),
    ([('xs','List<&1, T>')],'mapped_cons(~T, m, xs)'),
    ([('s','S'),('before',MN)],'prev(s, node)')],'(s, (before, xs))')
fun('map_loop',mg,[('fuel','Nat'),('c','C'),('r',MS)],MR,'''  match fuel r:
    case _ Tuple{s, Tuple{None{}, xs}}: (s, Done{xs})
    case 0n Tuple{s, Tuple{Some{node}, xs}}: (s, Fail{E.LimitExceeded{}})
    case 1n+p Tuple{s, Tuple{Some{node}, xs}}:
      '''+call('map_loop',mg,'p','c',call('map_step',mg,'s','c','node','xs')))
fun('map_last',mg,[('fuel','Nat'),('c','C'),('r',SR)],MR,'''  match r:
    case Tuple{s, Fail{e}}: (s, Fail{e})
    case Tuple{s, Done{end}}:
      '''+call('map_loop',mg,'fuel','c','(s, (end, Nil{}))'))
g=SN+[('V','Data'),('T','Type'),('C','Data'),('H','Data'),GET,NEXT,PREV,VALUE,('fn','S -> C -> V -> S & Maybe<&1, T>')]
fun('flat_map_to_list',g,[('fuel','Nat'),('s','S'),('h','H'),('c','C')],MR,
    '  '+call('map_last',mg,'fuel','c',call('last',lg,'fuel','s','h')))
fun('map_some_result',[('S','Type'),('T','Type')],[('r','S & T')],'S & Maybe<&1, T>','''  (s, v) = r
  (s, Some{v})''')
gg=SN+[('V','Data'),('T','Type'),('C','Data'),('H','Data'),GET,NEXT,PREV,VALUE,('fn','S -> C -> V -> S & T')]
fun('map_to_list',gg,[('fuel','Nat'),('s','S'),('h','H'),('c','C')],MR,
    '  flat_map_to_list(~S, ~N, ~V, ~T, ~C, ~H, ~get_head, ~next, ~prev, ~value, ~(s => c => v => map_some_result(~S, ~T, fn(s, c, v))), fuel, s, h, c)')
g=SN+[('V','Data'),('H','Data'),GET,NEXT,PREV,VALUE]
fun('to_list',g,[('fuel','Nat'),('s','S'),('h','H')],'S & Result<&2, &1, E.Error, List<&1, V>>',
    '  map_to_list(~S, ~N, ~V, ~V, ~Unit, ~H, ~get_head, ~next, ~prev, ~value, ~(s => c => v => (s, v)), fuel, s, h, Unit{})')

# ----- builders: application factories allocate nodes; links only connect them -----
bg=SN+[SET_NEXT,SET_PREV]
fun('append_node',bg,[('s','S'),('head',MN),('tail',MN),('node','N')],'S & (Maybe<&2, N> & Maybe<&2, N>)','''  match head:
    case None{}: (s, (Some{node}, Some{node}))
    case Some{+h}:
      (write_next(~S, ~N, ~set_next, set_next(set_prev(s, node, tail), node, None{}), tail, Some{node}), (Some{h}, Some{node}))''')
bg=SN+[('V','Data'),('C','Data'),SET_NEXT,SET_PREV,('make','S -> C -> V -> S & N')]
BS='S & (Maybe<&2, N> & Maybe<&2, N>)'
seq('build_step',bg,[('s','S'),('c','C'),('head',MN),('tail',MN),('v','V')],BS,[
    ([('s','S'),('node','N')],'make(s, c, v)')],call('append_node',SN+[SET_NEXT,SET_PREV],'s','head','tail','node'))
fun('build_loop',bg,[('xs','List<&2, V>'),('c','C'),('r',BS)],'S & '+MN,'''  match xs r:
    case Nil{} Tuple{s, Tuple{head, tail}}: (s, head)
    case Con{v, rest} Tuple{s, Tuple{head, tail}}:
      '''+call('build_loop',bg,'rest','c',call('build_step',bg,'s','c','head','tail','v')))
fun('from_values',bg,[('s','S'),('xs','List<&2, V>'),('c','C')],'S & '+MN,
    '  '+call('build_loop',bg,'xs','c','(s, (None{}, None{}))'))
g=SN+[SET_NEXT,SET_PREV]
fun('from_nodes',g,[('s','S'),('xs','List<&2, N>')],'S & '+MN,
    '  from_values(~S, ~N, ~N, ~Unit, ~set_next, ~set_prev, ~(s => c => n => (s, n)), s, xs, Unit{})')
factory=SN+[('V','Data'),('D','Data'),('C','Data'),('convert','S -> C -> V -> S & D'),('make','S -> C -> D -> S & N')]
seq('mapped_factory',factory,[('s','S'),('c','C'),('v','V')],'S & N',[
    ([('s','S'),('d','D')],'convert(s, c, v)')],'make(s, c, d)')
g=SN+[('V','Data'),('D','Data'),('C','Data'),SET_NEXT,SET_PREV,('convert','S -> C -> V -> S & D'),('make','S -> C -> D -> S & N')]
fun('map_from_values',g,[('s','S'),('xs','List<&2, V>'),('c','C')],'S & '+MN,
    '  from_values(~S, ~N, ~V, ~C, ~set_next, ~set_prev, ~(s => c => v => mapped_factory(~S, ~N, ~V, ~D, ~C, ~convert, ~make, s, c, v)), s, xs, c)')
fun('map_from_nodes',bg,[('s','S'),('xs','List<&2, V>'),('c','C')],'S & '+MN,
    '  '+call('from_values',bg,'s','xs','c'))

# ----- node pool: LIFO, preserve payload, make only on exhaustion -----
PK='E.Pool<N>'
PR='S & E.Pool<N>'
PN='S & (E.Pool<N> & N)'
g=SN+[SET_NEXT]
fun('pool_free',g,[('s','S'),('pool',PK),('node','N')],PR,'''  E.Pool{head, count} = pool
  (set_next(s, node, head), E.Pool{Some{node}, 1n+count})''')
g=SN+[('C','Data'),NEXT,SET_NEXT,('make','S -> C -> S & N')]
seq('pool_take',g,[('s','S'),('node','N'),('count','Nat')],PN,[
    ([('s','S'),('after',MN)],'next(s, node)')],'(set_next(s, node, None{}), (E.Pool{after, Nat.sub(count, 1n)}, node))')
seq('pool_fresh',g,[('s','S'),('c','C')],PN,[
    ([('s','S'),('node','N')],'make(s, c)')],'(s, (E.Pool{None{}, 0n}, node))')
fun('pool_next',g,[('s','S'),('pool',PK),('c','C')],PN,'''  match pool:
    case E.Pool{None{}, count}: '''+call('pool_fresh',g,'s','c')+'''
    case E.Pool{Some{node}, count}: '''+call('pool_take',g,'s','node','count'))
pg=SN+[('C','Data'),SET_NEXT,('make','S -> C -> S & N')]
seq('pool_grow_step',pg,[('s','S'),('pool',PK),('c','C')],PR,[
    ([('s','S'),('node','N')],'make(s, c)')],'pool_free(~S, ~N, ~set_next, s, pool, node)')
fun('pool_grow',pg,[('size','Nat'),('c','C'),('r',PR)],PR,'''  match size r:
    case 0n Tuple{s, pool}: (s, pool)
    case 1n+p Tuple{s, pool}:
      '''+call('pool_grow',pg,'p','c',call('pool_grow_step',pg,'s','pool','c')))
seq('pool_new',pg,[('size','Nat'),('s','S'),('c','C')],PR,[
    ([('s','S'),('node','N')],'make(s, c)')],call('pool_grow',pg,'Nat.sub(size, 1n)','c','(s, E.Pool{Some{node}, 1n})'))

# Optional value wrapper, analogous to a conventional intrusive node class.
# The application chooses stable identities and owns the storage for these.
g=[('N','Data'),('V','Data')]
fun('new_node',g,[('v','V')],'E.DefaultNode<N, V>','  E.Node{None{}, None{}, v}')

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--check', action='store_true', help='fail if the committed module needs regeneration')
options = parser.parse_args()
rendered = ''.join(parts).rstrip() + '\n'
# The normal API exposes membership, observations, traversal and pooling.
# Migration-only aliases and callback conventions remain available in a
# separate module; compiler-generated lowering helpers are never exported.
CORE = {
    'next', 'prev', 'value', 'get_head', 'remove', 'prepend_as', 'prepend',
    'is_empty', 'non_empty', 'at_least_two', 'fold_left', 'foreach', 'find',
    'exists', 'forall', 'count', 'length', 'to_list', 'from_nodes', 'from_values',
    'pool_free', 'pool_next', 'pool_new', 'new_node',
}

def facade(names, internal, types, explanation):
    text = ('# Generated by tools/generators/intrusive_list.py; edit that source.\n'
            'import Base\n' + f'import {internal} as Impl\nimport {types} as E\n\n'
            + explanation + '\n\n')
    seen = set()
    for match in re.finditer(r'^def (\w+)\((.*)\) -> ([^\n]+):$', rendered, re.M):
        name, parameters, result = match.groups()
        if name not in names:
            continue
        if name in seen:
            raise SystemExit(f'duplicate public operation: {name}')
        seen.add(name)
        arguments = [x.lstrip('+') for x in re.findall(r'(?:^|, )([~+]?\w+):', parameters)]
        text += '# ' + PUBLIC_DOC[name] + '\n'
        text += f'def {name}({parameters}) -> {result}:\n  Impl.{name}(' + ', '.join(arguments) + ')\n\n'
    if seen != names:
        raise SystemExit(f'public operations missing from generator: {sorted(names - seen)}')
    return text.rstrip() + '\n'

outputs = {
    INTERNAL: rendered.replace('import ./types/', 'import ../types/'),
    OUT: facade(CORE, './internal/intrusive_list.bend', './types/intrusive_doubly_linked_list.bend',
                '# Application-owned membership. Bind static accessors once; see INTRUSIVE_LIST.md.\n'
                '# Known-member edits require valid membership; callbacks must obey the documented\n'
                '# traversal contract. Legacy callback order and aliases live in compat/.'),
    COMPAT: facade(set(PUBLIC_DOC), '../internal/intrusive_list.bend', '../types/intrusive_doubly_linked_list.bend',
                   '# Complete migration surface, including legacy callback order and naming.\n'
                   '# For new code prefer ../intrusive_doubly_linked_list.bend.\n'
                   '# clear visits the suffix before the original head; mapping visits tail-first.'),
}
for path, content in outputs.items():
    if options.check:
        if not path.exists() or path.read_text() != content:
            raise SystemExit(f'{path.relative_to(ROOT)} needs regeneration')
    else:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content)
