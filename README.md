# Proof-BFS Studio

Four engines over one formula language, from the literal "append characters and
test" algorithm up to SAT-based proof planning.

| file | engine | answers |
|---|---|---|
| `string_bfs.py` | generate-and-test BFS over strings | enumerate all statements ≤ n chars |
| `proof_bfs.py`  | BFS over inference steps (ND)        | shortest / all proof trees, ≤ k rules |
| `z3_bridge.py`  | SAT/SMT oracles (optional)           | validity, countermodels, minimal proof length |
| `bfs_gui.py`    | PySide6 visualizer                   | watch both searches run |

## Quickstart

```bash
./run.sh                          # GUI
python string_bfs.py 5           # CLI: all strings ≤ 5, tested
python proof_bfs.py              # CLI: demo proofs incl. Peirce ± RAA
python z3_bridge.py              # CLI: solver oracles demo
python tests/sanity.py           # full self-check
