#!/usr/bin/env python3
"""Interactive Lean4 tactic explorer.

Usage: python3 scripts/lean_check.py "tactic_code" [file] [line]

Replaces the sorry at the given line with the tactic, builds, and reports errors/goals.
Restores the original file afterward.
"""

import subprocess
import sys
import shutil
from pathlib import Path

def main():
    tactic = sys.argv[1] if len(sys.argv) > 1 else "sorry"
    file = sys.argv[2] if len(sys.argv) > 2 else "Fermat/Cases/SophieGermain.lean"
    line = int(sys.argv[3]) if len(sys.argv) > 3 else 173

    root = Path(__file__).parent.parent
    filepath = root / file
    backup = filepath.with_suffix(".lean.bak")

    # Backup
    shutil.copy2(filepath, backup)

    try:
        # Read file
        lines = filepath.read_text().splitlines()

        # Replace the sorry line
        if line - 1 < len(lines):
            indent = len(lines[line - 1]) - len(lines[line - 1].lstrip())
            lines[line - 1] = " " * indent + tactic

        filepath.write_text("\n".join(lines) + "\n")

        # Build
        result = subprocess.run(
            ["lake", "build", "Fermat.Cases.SophieGermain"],
            cwd=root,
            capture_output=True,
            text=True,
            timeout=120,
            env={**__import__("os").environ, "PATH": f"{Path.home()}/.elan/bin:" + __import__("os").environ.get("PATH", "")},
        )

        output = result.stdout + result.stderr

        # Filter to relevant lines
        relevant = []
        for line_text in output.split("\n"):
            if any(kw in line_text for kw in ["error:", "warning:", "⊢", "sorry", "goals", "Build completed"]):
                relevant.append(line_text.strip())

        print("\n".join(relevant[-30:]) if relevant else "No relevant output")
        print(f"\nExit code: {result.returncode}")

    finally:
        # Restore
        shutil.copy2(backup, filepath)
        backup.unlink()


if __name__ == "__main__":
    main()
