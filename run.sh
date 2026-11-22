#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
if [ -f .venv/bin/python ]; then PY=.venv/bin/python; else PY=python; fi
exec "$PY" bfs_gui.py "$@"
