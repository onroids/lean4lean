#!/usr/bin/env python3
"""Check that every retained experiment is built and imported by the axiom audit."""
from pathlib import Path
import re

root = Path(__file__).resolve().parent.parent
sources = sorted((root / "Lean4Lean/Research").rglob("*.lean"))
expected = {".".join(p.relative_to(root).with_suffix("").parts) for p in sources}
audit = (root / "research/AxiomAudit.lean").read_text()
imported = set(re.findall(r"^import (Lean4Lean\.Research\S+)$", audit, re.M))
if expected != imported:
    raise SystemExit(f"Axiom audit import mismatch: missing={expected-imported}, stale={imported-expected}")

def code_only(text: str) -> str:
    """Remove nested Lean comments and strings before scanning admission tokens."""
    out, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith("/-", i):
            depth += 1; i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1; i += 2
        elif depth:
            i += 1
        elif text.startswith("--", i):
            i = text.find("\n", i)
            if i < 0: break
        elif text[i] == '"':
            i += 1
            while i < len(text):
                if text[i] == "\\": i += 2
                elif text[i] == '"': i += 1; break
                else: i += 1
        else:
            out.append(text[i]); i += 1
    if depth:
        raise ValueError("unclosed block comment")
    return "".join(out)

for path in sources:
    code = code_only(path.read_text())
    if re.search(r"\b(sorry|sorryAx|admit|axiom)\b", code):
        raise SystemExit(f"Unreviewed admission in {path.relative_to(root)}")
print(f"source audit: {len(sources)} modules covered; no added admissions")
