#!/usr/bin/env python3
"""Render the local issue draft with immutable fork links; never publish it."""
import argparse
from pathlib import Path
import re
import subprocess

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("fork", help="GitHub OWNER/REPOSITORY")
parser.add_argument("--revision", default="HEAD", help="local commit to reference")
args = parser.parse_args()
if not re.fullmatch(r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+", args.fork):
    parser.error("fork must be OWNER/REPOSITORY")
root = Path(__file__).resolve().parent.parent
revision = subprocess.check_output(
    ["git", "rev-parse", "--verify", "--end-of-options", args.revision + "^{commit}"],
    cwd=root, text=True).strip()
body = (root / "research/ISSUE.md").read_text()
print(body.replace("__FORK_URL__", "https://github.com/" + args.fork)
          .replace("__REVISION__", revision), end="")
