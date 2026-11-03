#!/usr/bin/env bash
# Copy into CpsLean/Base/ the LeanBase modules imported (directly or transitively) by CpsLean,
# renaming the namespace LeanBase to CpsLean.Base, for a submission that may not use a non-Mathlib
# dependency. Run from lean/. Do not run before the submission is decided.
set -euo pipefail
cd "$(dirname "$0")/.."
BASE="${LEAN_BASE_DIR:-../../lean-base}"
python3 - "$BASE" <<'PY'
import re, sys, pathlib
base = pathlib.Path(sys.argv[1]); out = pathlib.Path('CpsLean/Base'); out.mkdir(parents=True, exist_ok=True)
def imports(p):
    return re.findall(r'^(?:public\s+)?import\s+(LeanBase\.\S+)', p.read_text(), re.M)
todo = set()
for f in pathlib.Path('CpsLean').rglob('*.lean'):
    if 'Base' not in f.parts: todo |= set(imports(f))
seen = set()
while todo:
    m = todo.pop()
    if m in seen: continue
    seen.add(m); todo |= set(imports(base / (m.replace('.', '/') + '.lean')))
for m in sorted(seen):
    src = (base / (m.replace('.', '/') + '.lean')).read_text()
    src = re.sub(r'\bLeanBase\b', 'CpsLean.Base', src)
    dst = out / (m.split('.', 1)[1].replace('.', '/') + '.lean')
    dst.parent.mkdir(parents=True, exist_ok=True)
    dst.write_text(src.replace('/-!\n', '/-!\nCopied from lean-base (AGPL-3.0-or-later, same author).\n', 1))
    print('vendored', m, '->', dst)
PY
echo "Now replace 'import LeanBase.' with 'import CpsLean.Base.' in CpsLean and remove the LeanBase require."
