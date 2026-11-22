"""
z3_bridge.py -- Z3-powered oracles over the same formula language.

Optional module: `pip install z3-solver`.

- is_theorem / countermodel : decide propositional validity, get refutations
- goal_dead                 : admissible semantic prune for the ND search
- shortest_proof_len        : minimal #rule-applications via bounded planning
                              (bounded model checking over the proof space)
- extract_proof             : decode a satisfying model into an ND tree
- all_proofs_via_sat        : AllSAT enumeration of bounded proofs

Closure note: the plan encoding restricts formulas to subformulas + their
negations + ⊥, so classical RAA cannot stack ¬¬¬… forever. Shortest proofs
need at most one extra negation level, so minimal lengths are unaffected.
"""

from collections import deque, defaultdict

try:
    import z3 as Z
except ImportError as _e:                                    # pragma: no cover
    raise ImportError("z3-solver not installed -- run: pip install z3-solver") from _e

import proof_bfs as pb

BOT = pb.BOT


# ---------------------------------------------------------------- 1. decide
def to_z3(f):
    op = f[0]
    if op == 'atom': return Z.Bool(f[1])
    if op == '⊥':    return Z.BoolVal(False)
    if op == '¬':    return Z.Not(to_z3(f[1]))
    if op == '∧':    return Z.And(to_z3(f[1]), to_z3(f[2]))
    if op == '∨':    return Z.Or(to_z3(f[1]), to_z3(f[2]))
    if op == '→':    return Z.Implies(to_z3(f[1]), to_z3(f[2]))

def is_theorem(f):
    s = Z.Solver()
    s.add(Z.Not(to_z3(f)))
    return s.check() == Z.unsat

def countermodel(f):
    s = Z.Solver()
    s.add(Z.Not(to_z3(f)))
    return s.model() if s.check() == Z.sat else None

def goal_dead(G, phi):
    """This goal can never be closed: a model of G ∧ ¬φ exists.
    Admissible because ND is sound."""
    s = Z.Solver()
    for a in G:
        s.add(to_z3(a))
    s.add(Z.Not(to_z3(phi)))
    return s.check() == Z.sat


# ------------------------------------------------- 2. bounded plan encoding
def proof_universe(goal, classical=True):
    """Close the sequent space under the rules, restricted to the finite
    formula universe F = subformulas(goal) ∪ {¬f} ∪ {⊥}."""
    subfs = pb.subformulas(goal)
    F = set(subfs) | {pb.Neg(g) for g in subfs} | {BOT}
    univ = sorted(F - {BOT}, key=pb.show)
    start = (frozenset(), goal)
    seqs, rules, seen, queue = [start], [], {start}, deque([start])
    while queue:
        gseq = queue.popleft()
        for rule, premises in pb.sequent_moves(gseq[0], gseq[1], univ, classical):
            ps = tuple((G, f) for G, f in premises
                       if f in F and all(a in F for a in G))
            if len(ps) != len(premises):
                continue                       # outside closure: drop move
            rules.append((gseq, rule, ps))
            for p in ps:
                if p not in seen:
                    seen.add(p); seqs.append(p); queue.append(p)
    return seqs, rules


def _at_most_one(xs, tag):
    """Linear (sequential/ladder) AMO encoding."""
    cs, prev = [], None
    for i, x in enumerate(xs):
        y = Z.Bool(f'__amo_{tag}_{i}')
        cs += [Z.Or(Z.Not(x), y)]                       # x_i -> y_i
        if prev is not None:
            cs += [Z.Or(Z.Not(prev), Z.Not(x))]         # y_{i-1} -> ¬x_i
        prev = y
    return cs


def plan_solver(goal, k, classical=True):
    """O[i][t] = 'sequent i open at step t';  A[r][t] = 'rule r applied at t'."""
    seqs, rules = proof_universe(goal, classical)
    ix = {s: i for i, s in enumerate(seqs)}
    O = [[Z.Bool(f'o{i}_{t}') for t in range(k + 1)] for i in range(len(seqs))]
    A = [[Z.Bool(f'a{r}_{t}') for t in range(k)] for r in range(len(rules))]
    NOP = [Z.Bool(f'nop{t}') for t in range(k)]
    consumes, produces = {}, {}
    for r, (g, _, _) in enumerate(rules):
        consumes.setdefault(ix[g], []).append(r)
    for r, (_, _, ps) in enumerate(rules):
        for p in ps:
            produces.setdefault(ix[p], []).append(r)

    s = Z.Solver()
    for i, sq in enumerate(seqs):                        # initial state
        s.add(O[i][0] if sq == (frozenset(), goal) else Z.Not(O[i][0]))
    for t in range(k):
        acts = [A[r][t] for r in range(len(rules))] + [NOP[t]]
        s.add(Z.Or(acts))                                # one action per step
        for c in _at_most_one(acts, t):
            s.add(c)
        for r, (g, _, ps) in enumerate(rules):
            s.add(Z.Implies(A[r][t], O[ix[g]][t]))       # precondition
            for p in ps:                                 # effects
                s.add(Z.Implies(A[r][t], O[ix[p]][t + 1]))
        for i in range(len(seqs)):                       # frame + consumption
            cons = [A[r][t] for r in consumes.get(i, [])]
            prod = [A[r][t] for r in produces.get(i, [])]
            s.add(O[i][t + 1] == Z.Or(Z.And(O[i][t], Z.Not(Z.Or(cons))),
                                      Z.Or(prod)))
    for i in range(len(seqs)):                           # all goals closed at k
        s.add(Z.Not(O[i][k]))
    return s, seqs, rules, A


def shortest_proof_len(goal, kmax=14, classical=True):
    """First SAT bound = minimal number of rule applications."""
    for k in range(kmax + 1):
        s, *_ = plan_solver(goal, k, classical)
        if s.check() == Z.sat:
            return k
    return None


def extract_proof(goal, k, classical=True):      # noqa: F811
    s, seqs, rules, A = plan_solver(goal, k, classical)
    if s.check() != Z.sat:
        raise ValueError(f"no proof of ≤ {k} steps (call shortest_proof_len)")
    m = s.model()
    steps = []
    for t in range(k):
        for r in range(len(rules)):
            if Z.is_true(m.eval(A[r][t], model_completion=True)):
                steps.append(rules[r])
    open_boxes = defaultdict(list)
    root_box = [None]
    open_boxes[(frozenset(), goal)].append(root_box)
    for g, rule, ps in steps:                    # replay in time order
        if not open_boxes[g]:
            continue
        b = open_boxes[g].pop()
        kids = []
        for p in ps:
            nb = [None]
            open_boxes[p].append(nb)
            kids.append(nb)
        b[0] = (rule, g, *kids)
    assert not any(open_boxes.values()), "model left open goals"
    return pb._resolve(root_box[0])


def all_proofs_via_sat(goal, k, limit=100, classical=True):
    """AllSAT: enumerate bounded step-sequences by blocking each solution."""
    s, seqs, rules, A = plan_solver(goal, k, classical)
    found = 0
    while found < limit and s.check() == Z.sat:
        m = s.model()
        block, steps = [], []
        for t in range(k):
            for r in range(len(rules)):
                v = m.eval(A[r][t], model_completion=True)
                block.append(Z.Not(A[r][t]) if Z.is_true(v) else A[r][t])
                if Z.is_true(v):
                    steps.append(rules[r])
        yield steps
        s.add(Z.Or(block))
        found += 1


if __name__ == "__main__":
    p, q = pb.Atom('p'), pb.Atom('q')
    print("p→p theorem?      ", is_theorem(pb.Imp(p, p)))
    print("p→q theorem?      ", is_theorem(pb.Imp(p, q)),
          "| countermodel:", countermodel(pb.Imp(p, q)))
    print("min proof of p→p: ", shortest_proof_len(pb.Imp(p, p), kmax=4), "steps")
    tree = extract_proof(pb.Imp(p, p), 2)
    print('\n'.join(pb.render(tree)))
