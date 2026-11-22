"""
proof_bfs.py -- the same BFS skeleton, but edges are inference rules.

node     = a configuration of open goals (sequents: assumptions |- formula)
edge     = one sound natural-deduction rule applied backwards
level k  = proofs whose tree has exactly k rule applications
output   = proof trees -- valid by construction, so there is no post-hoc test

Dedup on goal configurations collapses derivations through identical states
(this kills RAA loops and bounds the search; "all proofs" is modulo that).

    python proof_bfs.py
"""

from collections import deque
from itertools import islice

BOT = ('⊥',)

# ---------- formulas: immutable tuples ----------
def Atom(p):   return ('atom', p)
def Neg(f):    return ('¬', f)
def And(a, b): return ('∧', a, b)
def Or(a, b):  return ('∨', a, b)
def Imp(a, b): return ('→', a, b)

def show(f):
    op = f[0]
    if op == 'atom': return f[1]
    if op == '⊥':    return '⊥'
    if op == '¬':
        s = show(f[1])
        return '¬' + (f'({s})' if f[1][0] in '∧∨→' else s)
    return f'({show(f[1])} {op} {show(f[2])})'

def subformulas(f):
    out, stack = set(), [f]
    while stack:
        g = stack.pop()
        if g in out: continue
        out.add(g)
        if g[0] in ('∧', '∨', '→'): stack += [g[1], g[2]]
        elif g[0] == '¬':           stack.append(g[1])
    return out

# ---------- backward moves: one goal -> premises of one rule ----------
def sequent_moves(G, phi, univ, classical=True):
    """G |- phi.  Returns [(rule_name, premises)].  Ax short-circuits."""
    if phi in G:
        return [('Ax', ())]
    moves, op = [], phi[0]
    if op == '∧':
        moves.append(('∧I', ((G, phi[1]), (G, phi[2]))))
    elif op == '→':
        moves.append(('→I', ((G | {phi[1]}, phi[2]),)))
    elif op == '¬':
        moves.append(('¬I', ((G | {phi[1]}, BOT),)))
    elif op == '∨':
        moves.append(('∨I:L', ((G, phi[1]),)))
        moves.append(('∨I:R', ((G, phi[2]),)))
    for c in G:                                   # eliminations, driven by context
        if c[0] == '∧':
            if phi == c[1]: moves.append(('∧E:L', ((G, c),)))
            if phi == c[2]: moves.append(('∧E:R', ((G, c),)))
        elif c[0] == '→' and c[2] == phi:
            moves.append(('→E', ((G, c), (G, c[1]))))
        elif c[0] == '∨':
            moves.append(('∨E', ((G, c), (G | {c[1]}, phi), (G | {c[2]}, phi))))
    if op == '⊥':                                 # ¬E: exhibit a with G |- a, G |- ¬a
        for a in univ:
            moves.append((f'¬E[{show(a)}]', ((G, a), (G, Neg(a)))))
    else:
        moves.append(('⊥E', ((G, BOT),)))
        if classical:
            moves.append(('RAA', ((G | {Neg(phi)}, BOT),)))
    return moves

# ---------- replay an action path into a proof tree ----------
def build_tree(goal, actions):
    """node = (rule, (G, phi), *children).  Fills placeholders in order."""
    root_box = [None]
    open_boxes = [((frozenset(), goal), root_box)]
    for G, phi, rule, premises in actions:
        k = next(i for i, (sq, _) in enumerate(open_boxes) if sq == (G, phi))
        _, box = open_boxes.pop(k)
        kids = [((g, f), [None]) for g, f in premises]
        box[0] = (rule, (G, phi), *[b for _, b in kids])
        open_boxes.extend(kids)
    assert not open_boxes and root_box[0] is not None
    return _resolve(root_box[0])

def _resolve(node):
    rule, seq, *boxes = node
    return (rule, seq, *(_resolve(b[0]) for b in boxes))

# ---------- the BFS ----------
def _search(goal, classical, max_steps, enumerate_all=False):
    univ = sorted(subformulas(goal) | {Neg(g) for g in subformulas(goal)},
                  key=show)
    start = ((frozenset(), goal),)
    seen = {start}
    queue = deque([(start, ())])                  # (open goals, actions taken)
    while queue:
        state, actions = queue.popleft()
        if not state:
            yield build_tree(goal, actions), len(actions)
            if not enumerate_all:
                return
            continue
        if len(actions) >= max_steps:
            continue
        for i, (G, phi) in enumerate(state):
            for rule, premises in sequent_moves(G, phi, univ, classical):
                new_state = state[:i] + state[i+1:] + tuple(premises)
                if new_state and new_state in seen:
                    continue
                if new_state:
                    seen.add(new_state)
                queue.append((new_state, actions + ((G, phi, rule, premises),)))

def shortest_proof(goal, classical=True, max_steps=30):
    """First level reached = minimal number of rule applications."""
    return next(_search(goal, classical, max_steps), (None, None))

def all_proofs(goal, max_steps, classical=True, limit=50):
    """All non-redundant proofs with <= max_steps rule nodes, BFS order."""
    yield from islice(_search(goal, classical, max_steps, True), limit)

# ---------- ASCII rendering ----------
def render(node):
    rule, (G, phi), *kids = node
    ctx = ', '.join(sorted(show(a) for a in G))
    concl = (ctx + ' ⊢ ' if ctx else '⊢ ') + show(phi)
    if not kids:
        return [concl + '   ' + rule]
    blocks = [render(k) for k in kids]
    h  = max(map(len, blocks))
    ws = [max(map(len, b)) for b in blocks]
    for b, w in zip(blocks, ws):
        b += [' ' * w] * (h - len(b))
    top = ['   '.join(p.ljust(w) for p, w in zip(row, ws))
           for row in zip(*blocks)]
    return top + ['─' * max(map(len, top)) + '  ' + rule, concl]

# ---------- demo ----------
if __name__ == "__main__":
    p, q = Atom('p'), Atom('q')
    peirce = Imp(Imp(Imp(p, q), p), p)

    for name, goal, cls, bound in [
        ("identity        ⊢ p → p",           Imp(p, p), True, 6),
        ("non-contradict. ⊢ ¬(p ∧ ¬p)",       Neg(And(p, Neg(p))), True, 10),
        ("contraposition  ⊢ (¬p→¬q) → (q→p)", Imp(Imp(Neg(p), Neg(q)), Imp(q, p)), True, 12),
        ("Peirce, classical",                 peirce, True, 14),
        ("Peirce, intuitionistic",            peirce, False, 12),
    ]:
        tree, k = shortest_proof(goal, classical=cls, max_steps=bound)
        verdict = f"{k} rule applications" if tree else "NO PROOF (search exhausted)"
        print(f"\n=== {name}: {verdict}")
        if tree:
            print('\n'.join(render(tree)))

    print("\n=== all proofs of ⊢ p → p with ≤ 3 steps:")
    for tree, k in all_proofs(Imp(p, p), max_steps=3):
        print(f"--- {k} steps")
        print('\n'.join(render(tree)))
