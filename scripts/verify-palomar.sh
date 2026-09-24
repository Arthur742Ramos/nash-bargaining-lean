#!/usr/bin/env bash
set -euo pipefail

repository_root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$repository_root"

if [ -d "$HOME/.elan/bin" ]; then
  export PATH="$HOME/.elan/bin:$PATH"
fi
command -v lake >/dev/null 2>&1 || {
  echo "error: lake is required" >&2
  exit 1
}
command -v python3 >/dev/null 2>&1 || {
  echo "error: python3 is required" >&2
  exit 1
}

for required_file in \
  lean-toolchain lake-manifest.json formalization.yaml Challenge.lean Solution.lean \
  comparator.json LICENSE THIRD_PARTY_NOTICES.md scripts/AxiomAudit.lean \
  scripts/check-axiom-report.py; do
  if [ ! -f "$required_file" ] || [ -L "$required_file" ]; then
    echo "error: required Palomar file is missing or not regular: $required_file" >&2
    exit 1
  fi
done

python3 - "$repository_root" <<'PY'
import json
import pathlib
import re
import subprocess
import sys
import yaml

root = pathlib.Path(sys.argv[1])
floor = "v4.28.0"
version_pattern = re.compile(
    r"^leanprover/lean4:v(?P<major>\d+)\.(?P<minor>\d+)\.(?P<patch>\d+)(?:-rc(?P<rc>\d+))?$"
)

def version_key(value):
    match = version_pattern.fullmatch(value)
    if not match:
        raise SystemExit(f"error: unsupported lean-toolchain value: {value}")
    major, minor, patch = (int(match.group(key)) for key in ("major", "minor", "patch"))
    rc = match.group("rc")
    return major, minor, patch, 0 if rc is not None else 1, int(rc or 0)

lakefiles = [name for name in ("lakefile.toml", "lakefile.lean") if (root / name).exists()]
if lakefiles != ["lakefile.lean"]:
    raise SystemExit(f"error: expected exactly lakefile.lean, found {lakefiles}")

toolchain = (root / "lean-toolchain").read_text(encoding="utf-8").strip()
version_key(toolchain)
pin_version = toolchain.removeprefix("leanprover/lean4:")
if version_key(toolchain) < version_key(f"leanprover/lean4:{floor}"):
    raise SystemExit(f"error: toolchain {pin_version} is below Palomar floor {floor}")

manifest_path = root / "lake-manifest.json"
try:
    subprocess.run(
        ["git", "ls-files", "--error-unmatch", "lake-manifest.json"],
        cwd=root,
        check=True,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
except (subprocess.CalledProcessError, OSError, UnicodeError, json.JSONDecodeError) as error:
    raise SystemExit(f"error: lake-manifest.json is missing, invalid, or untracked: {error}")
if manifest.get("version") != "1.2.0" or not manifest.get("packages"):
    raise SystemExit("error: lake-manifest.json has an unexpected or empty format")
for package in manifest["packages"]:
    if not re.fullmatch(r"[0-9a-f]{40}", package.get("rev", "")):
        raise SystemExit(f"error: dependency {package.get('name')} is not pinned to a full commit")
mathlib = next((p for p in manifest["packages"] if p.get("name") == "mathlib"), None)
if mathlib is None or mathlib.get("inputRev") != pin_version:
    raise SystemExit("error: mathlib and project toolchain pins do not match")

try:
    comparator = json.loads((root / "comparator.json").read_text(encoding="utf-8"))
except (OSError, UnicodeError, json.JSONDecodeError) as error:
    raise SystemExit(f"error: comparator.json is invalid: {error}")

required_keys = {
    "challenge_module", "solution_module", "theorem_names", "definition_names",
    "permitted_axioms", "enable_nanoda",
}
if not isinstance(comparator, dict) or set(comparator) != required_keys:
    raise SystemExit("error: comparator.json has an invalid key set")
expected_theorems = [
    "NashBargaining.Palomar.nashMaximizerExists",
    "NashBargaining.Palomar.nashMaximizerUnique",
    "NashBargaining.Palomar.nashSatisfiesAxioms",
    "NashBargaining.Palomar.axiomsCharacterizeNash",
]
expected_definitions = [
    "NashBargaining.Problem",
    "NashBargaining.nashProduct",
    "NashBargaining.IsNashMaximizer",
    "NashBargaining.Solution",
    "NashBargaining.Pareto",
    "NashBargaining.Symmetric",
    "NashBargaining.Invariance",
    "NashBargaining.IIA",
    "NashBargaining.NashAxioms",
]
if comparator["challenge_module"] != "Challenge" or comparator["solution_module"] != "Solution":
    raise SystemExit("error: Comparator modules must be Challenge and Solution")
if comparator["theorem_names"] != expected_theorems:
    raise SystemExit(f"error: unexpected theorem_names: {comparator['theorem_names']}")
if comparator["definition_names"] != expected_definitions:
    raise SystemExit(f"error: unexpected definition_names: {comparator['definition_names']}")
if set(comparator["permitted_axioms"]) != {"propext", "Classical.choice", "Quot.sound"}:
    raise SystemExit("error: Comparator permitted_axioms must be exactly the three standard axioms")
if comparator["enable_nanoda"] is not True:
    raise SystemExit("error: comparator.json must enable NanoDa")

challenge = root / "Challenge.lean"
challenge_text = challenge.read_text(encoding="utf-8")
if challenge.stat().st_size > 100 * 1024 or len(challenge_text.splitlines()) > 1000:
    raise SystemExit("error: Challenge.lean exceeds the 100 KiB or 1,000-line cap")
imports = [line for line in challenge_text.splitlines() if line.startswith("import ")]
if not imports or any(not line.startswith("import Mathlib.") for line in imports):
    raise SystemExit(f"error: Challenge imports must come only from Mathlib: {imports}")
challenge_holes = len(re.findall(r"\bsorry\b", challenge_text))
if challenge_holes != 4:
    raise SystemExit(f"error: expected exactly four deliberate Challenge statement sorries, found {challenge_holes}")
if re.search(r"\b(admit|oops)\b|^\s*(axiom|unsafe)\b", challenge_text, re.MULTILINE):
    raise SystemExit("error: Challenge.lean contains an undeclared placeholder, axiom, or unsafe declaration")

solution = (root / "Solution.lean").read_text(encoding="utf-8")
if re.search(r"\b(sorry|admit|oops)\b|^\s*(axiom|unsafe)\b", solution, re.MULTILINE):
    raise SystemExit("error: Solution.lean contains a proof placeholder, axiom, or unsafe declaration")

library_files = sorted((root / "NashBargaining").rglob("*.lean"))
if not library_files:
    raise SystemExit("error: NashBargaining library has no Lean modules")
for path in library_files:
    source = path.read_text(encoding="utf-8")
    if re.search(r"\b(sorry|admit|oops)\b|^\s*axiom\b", source, re.MULTILINE):
        raise SystemExit(f"error: library module contains sorry/admit/oops/axiom: {path.relative_to(root)}")

try:
    metadata = yaml.safe_load((root / "formalization.yaml").read_text(encoding="utf-8"))
except (OSError, UnicodeError, yaml.YAMLError) as error:
    raise SystemExit(f"error: formalization.yaml is invalid: {error}")
if not isinstance(metadata, dict) or metadata.get("version") != "v0.4":
    raise SystemExit("error: formalization.yaml version must be v0.4")
project = metadata.get("project")
if not isinstance(project, dict):
    raise SystemExit("error: project metadata is missing")
for key in ("name", "description"):
    if not isinstance(project.get(key), str) or not project[key].strip():
        raise SystemExit(f"error: project.{key} is missing")
for key in ("authors", "responsible_maintainers"):
    if not isinstance(project.get(key), list) or not project[key]:
        raise SystemExit(f"error: project.{key} is empty")
if project.get("license") != "BSD-3-Clause":
    raise SystemExit("error: project.license must match the root BSD-3-Clause license")
if not isinstance(metadata.get("classification"), dict):
    raise SystemExit("error: formalization.yaml classification is missing")
classification = metadata["classification"]
if not isinstance(classification.get("arxiv"), list) or not isinstance(classification.get("msc2020"), list):
    raise SystemExit("error: formalization.yaml classification is incomplete")
sources = metadata.get("sources")
if not isinstance(sources, list) or not sources:
    raise SystemExit("error: formalization.yaml sources must be nonempty")
valid_relationships = {"formalizes", "adapts", "independently-proves", "background"}
if any(not isinstance(source, dict) or source.get("relationship") not in valid_relationships for source in sources):
    raise SystemExit("error: formalization.yaml contains an invalid source relationship")
nash_doi = "https://doi.org/10.2307/1907266"
if not any(
    source.get("relationship") in {"formalizes", "adapts", "independently-proves"}
    and nash_doi in (source.get("id"), source.get("location"))
    for source in sources
):
    raise SystemExit("error: no formalization source cites Nash's 1950 paper")
automation = metadata.get("automation")
if not isinstance(automation, dict) or not isinstance(automation.get("methods"), list) or not automation["methods"]:
    raise SystemExit("error: automation.methods must be nonempty")
review = metadata.get("review")
if not isinstance(review, dict) or not isinstance(review.get("status"), str) or not review["status"].strip():
    raise SystemExit("error: review.status is missing")
status = metadata.get("status")
if not isinstance(status, dict) or status.get("sorry_count") != 0 or status.get("sorry_in_definitions") != 0:
    raise SystemExit("error: formalization.yaml must report zero implementation sorries")

print(
    f"Palomar package shape passed: Challenge {challenge.stat().st_size} bytes, "
    f"{challenge_holes} deliberate holes, toolchain {pin_version} >= registry floor {floor}."
)
print(f"lake-manifest.json is tracked and pins {len(manifest['packages'])} dependencies.")
print(f"Library placeholder audit passed for {len(library_files)} Lean files.")
print("Formalization metadata shape passed.")
PY

lake_manifest_tracked=$(git ls-files --error-unmatch lake-manifest.json)
lake build

challenge_dependencies=$(lake env lean --src-deps Challenge.lean)
while IFS= read -r dependency; do
  [ -z "$dependency" ] && continue
  case "$dependency" in
    */src/lean/*|*/.lake/packages/mathlib/*) ;;
    *)
      echo "error: Challenge import closure contains a non-allowlisted source: $dependency" >&2
      exit 1
      ;;
  esac
done <<< "$challenge_dependencies"

check_tmpdir=$(mktemp -d)
trap 'rm -rf -- "$check_tmpdir"' EXIT
python3 - "$repository_root/comparator.json" "$check_tmpdir" <<'PY'
import json
import pathlib
import sys

config = json.loads(pathlib.Path(sys.argv[1]).read_text(encoding="utf-8"))
root = pathlib.Path(sys.argv[2])
names = config["definition_names"] + config["theorem_names"]

for module in ("Challenge", "Solution"):
    checks = root / f"{module}Names.lean"
    checks.write_text(
        f"import {module}\n\n" + "".join(f"#check @{name}\n" for name in names),
        encoding="utf-8",
    )
    kinds = root / f"{module}Kinds.lean"
    with kinds.open("w", encoding="utf-8") as output:
        output.write(f"import {module}\n\nopen Lean\n\nrun_cmd do\n  let env ← getEnv\n")
        for key, expected_kind in (
            ("definition_names", "defnInfo"),
            ("theorem_names", "thmInfo"),
        ):
            for name in config[key]:
                output.write(f"  match env.find? {chr(96) + name} with\n")
                output.write(f"  | some (.{expected_kind} _) => logInfo m!\"{expected_kind}: {name}\"\n")
                output.write(f"  | some _ => throwError \"expected {expected_kind} for {name}\"\n")
                output.write(f"  | none => throwError \"missing declaration {name}\"\n")
PY

for module in Challenge Solution; do
  lake env lean "$check_tmpdir/$module"Names.lean
  lake env lean "$check_tmpdir/$module"Kinds.lean
done
rm -rf -- "$check_tmpdir"
trap - EXIT

audit_output=$(lake env lean scripts/AxiomAudit.lean 2>&1)
printf '%s\n' "$audit_output"
printf '%s\n' "$audit_output" | python3 scripts/check-axiom-report.py comparator.json

git diff --check
echo "Full Palomar preparation and declaration audit passed."
