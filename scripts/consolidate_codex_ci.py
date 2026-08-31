from pathlib import Path
import re

root = Path('.')
workflows = root / '.github' / 'workflows'
branch = 'codex/lean-workbench'

# Specialist Codex workflows stay available, but no longer fan out on every push.
for path in workflows.glob('codex-*.yml'):
    if path.name in {'codex-fast.yml', 'codex-ci-consolidate.yml'}:
        continue
    text = path.read_text()
    original = text
    # Common branch-only push + workflow_dispatch form.
    text = re.sub(
        r'on:\n  push:\n    branches: \[(?:"codex/lean-workbench"|\'codex/lean-workbench\')\]\n  workflow_dispatch:',
        'on:\n  workflow_dispatch:',
        text,
        count=1,
    )
    # Also handle unquoted branch syntax.
    text = re.sub(
        r'on:\n  push:\n    branches: \[codex/lean-workbench\]\n  workflow_dispatch:',
        'on:\n  workflow_dispatch:',
        text,
        count=1,
    )
    if text != original:
        path.write_text(text)
        print(f'manual-only: {path}')

# Full project validation belongs on main/PR/manual, not every workbench push.
build = workflows / 'build.yml'
text = build.read_text()
text = text.replace(
    'on:\n  push:\n    branches: ["main", "codex/lean-workbench"]\n  pull_request:\n    branches: ["main", "codex/lean-workbench"]',
    'on:\n  push:\n    branches: ["main"]\n  pull_request:\n    branches: ["main"]\n  workflow_dispatch:'
)
build.write_text(text)
print('main/PR/manual only: build.yml')

# Replace the historical "fast" workflow (which had grown into dozens of gates)
# with a genuine changed-file smoke test. Downstream/global breakage is caught by
# the full build on PR/main/manual.
fast = workflows / 'codex-fast.yml'
fast.write_text(r'''name: Codex changed Lean smoke

on:
  push:
    branches: ["codex/lean-workbench"]
    paths:
      - 'GppVerify/**/*.lean'
      - 'lakefile.toml'
      - 'lean-toolchain'
      - '.github/workflows/codex-fast.yml'
  workflow_dispatch:

concurrency:
  group: codex-smoke-${{ github.ref }}
  cancel-in-progress: true

jobs:
  changed-lean:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
        with:
          fetch-depth: 2

      - name: Install elan
        run: |
          curl -sSfL https://github.com/leanprover/elan/releases/latest/download/elan-x86_64-unknown-linux-gnu.tar.gz | tar xz
          ./elan-init -y --default-toolchain none
          echo "$HOME/.elan/bin" >> "$GITHUB_PATH"

      - name: Cache Lean toolchain
        uses: actions/cache@v4
        with:
          path: ~/.elan/toolchains
          key: lean-toolchain-${{ hashFiles('lean-toolchain') }}

      - name: Cache lake packages
        uses: actions/cache@v4
        with:
          path: .lake
          key: lake-${{ hashFiles('lakefile.toml', 'lean-toolchain') }}-${{ runner.os }}
          restore-keys: |
            lake-${{ hashFiles('lakefile.toml', 'lean-toolchain') }}-

      - name: Get Mathlib cache
        run: lake exe cache get || true

      - name: Check changed Lean files
        shell: bash
        run: |
          set -euo pipefail
          BEFORE='${{ github.event.before }}'
          if [[ "${{ github.event_name }}" == "workflow_dispatch" ]] || [[ -z "$BEFORE" ]] || [[ "$BEFORE" =~ ^0+$ ]]; then
            echo 'Manual/initial run: compiling full project.'
            lake build 2>&1 | tee /tmp/build.log
          elif git diff --name-only "$BEFORE" "$GITHUB_SHA" -- lakefile.toml lean-toolchain | grep -q .; then
            echo 'Toolchain/project configuration changed: compiling full project.'
            lake build 2>&1 | tee /tmp/build.log
          else
            mapfile -t FILES < <(git diff --name-only "$BEFORE" "$GITHUB_SHA" -- 'GppVerify/**/*.lean')
            if ((${#FILES[@]} == 0)); then
              echo 'No Lean source changed.'
              exit 0
            fi
            printf 'Changed Lean files:\n%s\n' "${FILES[*]}"
            : > /tmp/build.log
            for file in "${FILES[@]}"; do
              [[ -f "$file" ]] || continue
              echo "=== $file ==="
              lake env lean "$file" 2>&1 | tee -a /tmp/build.log
            done
          fi
          if grep -F "declaration uses 'sorry'" /tmp/build.log; then
            echo "::error::A changed declaration uses 'sorry'."
            exit 1
          fi
''')
print('replaced codex-fast.yml with changed-file smoke gate')

# Remove the one-shot machinery from the resulting branch.
(root / 'scripts' / 'consolidate_codex_ci.py').unlink(missing_ok=True)
(workflows / 'codex-ci-consolidate.yml').unlink(missing_ok=True)
