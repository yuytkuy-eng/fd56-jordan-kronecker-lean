#!/usr/bin/env python3
# Copyright 2026 Shifan Yu
# SPDX-License-Identifier: Apache-2.0
"""Build the library and audit every theorem. Requires Python 3 and Lake."""
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def require(condition, message):
    if not condition:
        raise SystemExit(message)


def audit_output(output, names):
    records = re.findall(
        r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|(does not depend on any axioms))",
        output,
    )
    require(len(records) == len(names), "Incomplete axiom audit")
    require({name for name, _, _ in records} == set(names), "Audit theorem mismatch")
    for name, axioms, _ in records:
        unexpected = {a.strip() for a in axioms.split(",") if a.strip()} - ALLOWED
        require(not unexpected, f"Unexpected axioms in {name}: {sorted(unexpected)}")


def theorem_names(source):
    scopes, names = [], []
    for line in source.splitlines():
        opening = re.fullmatch(r"(namespace|(?:noncomputable )?section)(?:\s+(\S+))?", line)
        closing = re.fullmatch(r"end(?:\s+(\S+))?", line)
        declaration = re.match(r"^(?:@\[[^\n]*\]\s+)?theorem\s+([\w.]+)", line)
        if opening:
            kind, name = opening.groups()
            require(kind != "namespace" or name, "Unnamed namespace")
            scopes.append((kind, name))
        elif closing:
            require(scopes, "Unmatched scope ending")
            _, name = scopes.pop()
            require(not closing[1] or closing[1] == name, "Mismatched scope ending")
        elif declaration:
            prefix = [name for kind, name in scopes if kind == "namespace"]
            require(prefix and prefix[0] == "FD56", "Theorem outside FD56")
            names.append(".".join([*prefix, declaration[1]]))
    require(not any(kind == "namespace" for kind, _ in scopes), "Unclosed namespace")
    return names


def main():
    sources = sorted((ROOT / "FD56").rglob("*.lean"))
    entry = (ROOT / "FD56.lean").read_text(encoding="utf-8")
    expected = {".".join(p.relative_to(ROOT).with_suffix("").parts) for p in sources}
    require(set(re.findall(r"^import (FD56\.[\w.]+)$", entry, re.M)) == expected,
            "FD56.lean must import every project module")
    names = []
    for path in [ROOT / "FD56.lean", *sources]:
        source = path.read_text(encoding="utf-8")
        # Intentionally strict: these tokens are disallowed even in comments.
        require(not re.search(r"\b(sorry|admit|axiom|native_decide)\b", source),
                f"Prohibited proof escape in {path.relative_to(ROOT)}")
        names.extend(theorem_names(source))
    require(names and len(names) == len(set(names)), "Empty or duplicate theorem inventory")
    subprocess.run(["lake", "build"], cwd=ROOT, check=True)
    out = ROOT / ".verification"
    out.mkdir(exist_ok=True)
    outputs = []
    for start in range(0, len(names), 100):
        batch = names[start:start + 100]
        audit = out / "Audit.lean"
        audit.write_text("import FD56\n" + "".join(f"#print axioms {n}\n" for n in batch),
                         encoding="utf-8")
        result = subprocess.run(["lake", "env", "lean", "-j1", "-s65536", str(audit)],
                                cwd=ROOT, text=True, encoding="utf-8", capture_output=True)
        output = result.stdout + result.stderr
        outputs.append(output)
        (out / "axioms.txt").write_text("\n".join(outputs), encoding="utf-8")
        require(result.returncode == 0,
                f"Lean audit at theorem {start + 1} exited with code {result.returncode}\n{output}")
        audit_output(output, batch)
    audit_output("\n".join(outputs), names)
    print(f"Build passed; all {len(names)} theorems passed the axiom audit.")


if __name__ == "__main__":
    main()
