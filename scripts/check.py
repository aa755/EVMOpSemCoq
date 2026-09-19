#!/usr/bin/env python3
"""Build, audit operational assumptions, and kernel-check the regression proofs.
Run inside the desired opam environment; this script never selects a switch.
"""
from pathlib import Path
import re
import subprocess

root = Path(__file__).resolve().parents[1]
subprocess.run(["dune", "build"], cwd=root, check=True)

# Ignore nested Rocq comments when checking for proof holes and arbitrary values.
def active_source(source):
    result, depth, i, in_string = [], 0, 0, False
    while i < len(source):
        if not in_string and source[i:i+2] == "(*":
            depth += 1
            i += 2
        elif depth and source[i:i+2] == "*)":
            depth -= 1
            i += 2
        elif depth:
            i += 1
        elif source[i] == '"':
            if in_string and source[i:i+2] == '""':
                i += 2
            else:
                in_string = not in_string
                i += 1
        else:
            result.append(" " if in_string else source[i])
            i += 1
    return "".join(result)

for folder in ("theories", "tests"):
    for source in (root / folder).rglob("*.v"):
        if re.search(r"\b(DAEMON|Admitted|admit)\b", active_source(source.read_text())):
            raise SystemExit(f"Unfinished proof or arbitrary inhabitant in {source}")

loadpath = ["-R", "_build/default/theories", "EVMOpSem",
            "-R", "_build/default/tests", "EVMOpSemTests"]
constants = ["gen_pow_aux", "boolListFromNatural", "boolListFromNatural_equation", "word256Add", "word256FromInteger",
             "instruction_sem", "step", "start_transaction", "end_transaction",
             "settle_transaction"]
query = "From EVMOpSem Require Import Lem.coqharness block.\n"
query += "\n".join(f"Print Assumptions {name}." for name in constants) + "\n"
audit = subprocess.run(["rocq", "top", "-quiet", *loadpath], cwd=root,
                       input=query, text=True, capture_output=True, check=True)
if "Error:" in audit.stdout + audit.stderr:
    raise SystemExit(audit.stdout + audit.stderr)
reports = audit.stdout.count("Axioms:") + audit.stdout.count("Closed under the global context")
if reports != len(constants):
    raise SystemExit(f"Expected {len(constants)} assumption reports, received {reports}")
assumptions = set(re.findall(r"^([A-Za-z][\w.]*)\s*:", audit.stdout, re.MULTILINE))
assumptions.discard("Axioms")
allowed = {"Classical_Prop.classic", "Description.constructive_definite_description"}
if assumptions - allowed:
    raise SystemExit(f"Unexpected operational assumptions: {assumptions - allowed}")
(root / "_build" / "operational-assumptions.txt").write_text(audit.stdout)
with (root / "_build" / "kernel-check.log").open("w") as log:
    subprocess.run(["rocqchk", *loadpath, "EVMOpSemTests.Harness",
                    "EVMOpSemTests.Rollback", "EVMOpSemTests.Transactions",
                    "EVMOpSemTests.Decoder"],
                   cwd=root, stdout=log, stderr=subprocess.STDOUT, check=True)
print("Build, operational assumption audit, and kernel checks passed.")
print("Operational axioms:", ", ".join(sorted(assumptions)))
