"""
string_bfs.py -- the literal algorithm, verbatim.

BFS over strings: level k holds every length-k string over the alphabet.
Each string is generated, then tested. Honest caveat: there is no meaningful
"is this string a proof" test, so the test used here is the weakest true one --
well-formedness. (For objects that ARE proofs, see proof_bfs.py.)

    python string_bfs.py [n]
"""

import sys

ALPHABET = "pq⊤⊥¬∧∨→()"
ATOMS, UNARY, BINARY = "pq⊤⊥", "¬", "∧∨→"


def is_wff(s: str) -> bool:
    """The test: one left-to-right scan for well-formedness
    (precedence style, parentheses optional)."""
    balance, expect_operand = 0, True
    for ch in s:
        if ch == '(':
            if not expect_operand: return False
            balance += 1
        elif ch == ')':
            if expect_operand or balance == 0: return False
            balance -= 1
        elif ch in ATOMS:
            if not expect_operand: return False
            expect_operand = False
        elif ch in UNARY:
            pass                                    # still expecting an operand
        elif ch in BINARY:
            if expect_operand: return False
            expect_operand = True
        else:
            return False
    return balance == 0 and not expect_operand


def bfs_strings(n: int):
    """Yield (length, tested, passed) for each level 1..n.
    Note what deliberately does NOT happen: failed strings still seed the
    next level. The test does not prune -- this is generate-and-test."""
    frontier = [""]
    for length in range(1, n + 1):
        tested, passed = 0, []
        for prefix in frontier:
            for ch in ALPHABET:
                s = prefix + ch
                tested += 1
                if is_wff(s):
                    passed.append(s)
        yield length, tested, passed
        frontier = [p + ch for p in frontier for ch in ALPHABET]


if __name__ == "__main__":
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    for length, tested, passed in bfs_strings(n):
        print(f"length {length}: tested {tested:>8}, passed {len(passed):>5}"
              f"   e.g. {' '.join(passed[:6])}")
