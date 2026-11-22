"""Dependency-free sanity checks; Z3 cross-checks run only if z3 is present."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from string_bfs import is_wff
assert is_wff("p") and is_wff("¬p") and is_wff("(p∧q)") and is_wff("¬¬p")
assert not is_wff("p∧") and not is_wff("∧p") and not is_wff("()")
assert not is_wff("pq") and not is_wff(")")
print("string_bfs:  well-formedness oracle          ✓")

from proof_bfs import (Atom, Neg, And, Imp, shortest_proof, all_proofs)
p, q = Atom('p'), Atom('q')

tree, k = shortest_proof(Imp(p, p), max_steps=6)
assert tree is not None and k == 2, (tree, k)

tree, k = shortest_proof(Neg(And(p, Neg(p))), max_steps=10)
assert tree is not None and k == 6, (tree, k)

peirce = Imp(Imp(Imp(p, q), p), p)
assert shortest_proof(peirce, classical=True,  max_steps=16)[0] is not None
assert shortest_proof(peirce, classical=False, max_steps=8)[0]  is None

assert any(kk == 2 for _, kk in all_proofs(Imp(p, p), max_steps=3))
print("proof_bfs:   lengths, Peirce ±RAA, enum     ✓")

try:
    import z3_bridge
except ImportError:
    print("z3_bridge:   not installed -- skipping")
else:
    assert z3_bridge.is_theorem(Imp(p, p)) is True
    assert z3_bridge.is_theorem(Imp(p, q)) is False
    assert z3_bridge.countermodel(Imp(p, q)) is not None
    assert z3_bridge.shortest_proof_len(Imp(p, p), kmax=4) == 2
    # two independent oracles must agree on minimal proof length:
    contra = Imp(Imp(Neg(p), Neg(q)), Imp(q, p))
    for g in (Imp(p, p), Neg(And(p, Neg(p))), contra):
        kb = shortest_proof(g, classical=True, max_steps=12)[1]
        kz = z3_bridge.shortest_proof_len(g, kmax=12)
        assert kb == kz, (kb, kz)
    assert z3_bridge.extract_proof(Imp(p, p), 2)[0] == '→I'
    print("z3_bridge:   decide + min-length + BFS agreement ✓")

print("\nall sanity checks passed ✓")
