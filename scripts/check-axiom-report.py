"""Fail closed on missing declarations, unexpected output, or unapproved axioms."""
import json
import re
import sys
from pathlib import Path


if len(sys.argv) != 2:
    raise SystemExit("usage: check-axiom-report.py comparator.json")

try:
    config = json.loads(Path(sys.argv[1]).read_text(encoding="utf-8"))
except (OSError, UnicodeError, json.JSONDecodeError) as error:
    raise SystemExit(f"error: invalid Comparator config: {error}")

required = set(config.get("theorem_names", [])) | set(config.get("definition_names", [])) | {
    "NashBargaining.nashMaximizerExists",
    "NashBargaining.nashMaximizerUnique",
    "NashBargaining.nashSatisfiesAxioms",
    "NashBargaining.axiomsCharacterizeNash",
}
allowed = set(config.get("permitted_axioms", []))
expected_allowed = {"propext", "Quot.sound", "Classical.choice"}
if allowed != expected_allowed:
    raise SystemExit(f"error: permitted_axioms must be exactly {sorted(expected_allowed)}")

text = sys.stdin.read()
report = re.compile(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]")
coverage = re.compile(r"PALOMAR-AXIOM-AUDIT-COVERAGE:\s*(\d+)\s+declarations")
seen = set()
used_axioms = set()
coverage_count = None

for line in text.splitlines():
    match = report.search(line)
    if match:
        name, body = match.groups()
        if name in seen:
            raise SystemExit(f"error: duplicate axiom report for {name}")
        if not name.startswith("NashBargaining."):
            raise SystemExit(f"error: unexpected declaration in library audit: {name}")
        seen.add(name)
        used_axioms.update(axiom.strip() for axiom in body.split(",") if axiom.strip())
        continue

    match = coverage.search(line)
    if match:
        if coverage_count is not None:
            raise SystemExit("error: duplicate declaration coverage marker")
        coverage_count = int(match.group(1))
        continue

    residue = line.strip()
    if residue.startswith("info:"):
        residue = residue.removeprefix("info:").strip()
    if residue:
        raise SystemExit(f"error: unrecognized axiom report output: {line}")

missing = required - seen
if missing:
    raise SystemExit(f"error: axiom report is missing declarations: {sorted(missing)}")
if coverage_count is None or coverage_count != len(seen):
    raise SystemExit(
        f"error: declaration coverage mismatch: marker={coverage_count}, reports={len(seen)}"
    )
if used_axioms != expected_allowed:
    raise SystemExit(
        f"error: expected exact axiom set {sorted(expected_allowed)}, "
        f"found {sorted(used_axioms)}"
    )

print(
    f"Axiom audit passed for all {len(seen)} NashBargaining declarations; "
    f"exact axiom set: {', '.join(sorted(used_axioms))}."
)
