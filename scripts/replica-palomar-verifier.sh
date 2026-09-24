#!/usr/bin/env bash
set -euo pipefail

repository_root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$repository_root"

command -v elan >/dev/null 2>&1 || {
  echo "error: elan is required to locate the pinned Lean toolchain" >&2
  exit 1
}
toolchain_lean=$(elan which lean)
toolchain_root=$(dirname -- "$(dirname -- "$toolchain_lean")")
export LAKE_HOME="$toolchain_root"
export LEAN_SYSROOT="$toolchain_root"
export LEAN="$toolchain_root/bin/lean"
export PATH="$toolchain_root/bin:$PATH"

for required_binary in lake leanexport nanoda_bin leanchecker-paranoid lean4lean con-leche con-ron; do
  if [ ! -x "$toolchain_root/bin/$required_binary" ]; then
    echo "error: pinned toolchain binary is missing: $toolchain_root/bin/$required_binary" >&2
    exit 1
  fi
done

expected_toolchain=$(tr -d '[:space:]' < lean-toolchain)
expected_version=$(printf '%s' "$expected_toolchain" | sed 's@^leanprover/lean4:v@@')
actual_toolchain=$(lake --version)
case "$actual_toolchain" in
  *"$expected_version"*) ;;
  *)
    echo "error: lake on PATH does not match $expected_toolchain: $actual_toolchain" >&2
    exit 1
    ;;
esac

if ! command -v bwrap >/dev/null 2>&1; then
  if [ "$(printenv PALOMAR_ALLOW_UNSANDBOXED_LOCAL || true)" != "1" ]; then
    echo "error: bwrap is unavailable; set PALOMAR_ALLOW_UNSANDBOXED_LOCAL=1 for the explicit local fallback" >&2
    exit 1
  fi
  echo "Local fallback: Comparator sandbox disabled because bwrap is unavailable."
  no_sandbox=1
else
  no_sandbox=0
fi

scripts/verify-palomar.sh

replica_tmpdir=$(mktemp -d)
trap 'rm -rf -- "$replica_tmpdir"' EXIT
export LEAN_PATH
LEAN_PATH=$(lake env printenv LEAN_PATH)

python3 - "$repository_root/comparator.json" "$toolchain_root" "$replica_tmpdir" <<'PY'
import json
import os
import pathlib
import subprocess
import sys

config = json.loads(pathlib.Path(sys.argv[1]).read_text(encoding="utf-8"))
toolchain_root = pathlib.Path(sys.argv[2])
out_dir = pathlib.Path(sys.argv[3])
if not config.get("theorem_names") and not config.get("definition_names"):
    raise SystemExit("error: Comparator configuration names no declarations")

# This mirrors Lake v4.35.0-rc2's Check.compareIt exportTargets order:
# builtin Quot declarations, configured theorems, permitted axioms,
# primitive kernel declarations, and configured definitions.
targets = []
if "Quot.sound" in config["permitted_axioms"]:
    targets.extend(["Quot", "Quot.mk", "Quot.lift", "Quot.ind"])
targets.extend(config["theorem_names"])
targets.extend(config["permitted_axioms"])
targets.extend([
    "Nat.add",
    "Nat.sub",
    "Nat.mul",
    "Nat.pow",
    "Nat.gcd",
    "Nat.div",
    "Nat.mod",
    "Nat.beq",
    "Nat.ble",
    "Nat.land",
    "Nat.lor",
    "Nat.xor",
    "Nat.shiftLeft",
    "Nat.shiftRight",
    "String.ofList",
    "Char.ofNat",
    "List",
    "eagerReduce",
    "Nat",
    "String",
    "String.mk",
    "Char",
    "optParam",
    "autoParam",
    "semiOutParam",
    "outParam",
])
targets.extend(config["definition_names"])
if len(targets) != len(set(targets)):
    raise SystemExit("error: duplicate target in Comparator export list")

print(
    f"Export target list: {len(targets)} declarations "
    f"({len(config['definition_names'])} definitions, {len(config['theorem_names'])} theorems, "
    "plus Comparator built-ins)."
)
for module in (config["challenge_module"], config["solution_module"]):
    output_path = out_dir / f"{module}.ndjson"
    with output_path.open("wb") as output:
        subprocess.run(
            [str(toolchain_root / "bin" / "leanexport"), module, "--", *targets],
            check=True,
            env=os.environ.copy(),
            stdout=output,
        )
    print(f"Exported {module}: {output_path.stat().st_size} bytes.")
PY

if [ "$no_sandbox" -eq 1 ]; then
  lake comparator \
    --config=comparator.json \
    --challenge-from-export="$replica_tmpdir/Challenge.ndjson" \
    --solution-from-export="$replica_tmpdir/Solution.ndjson" \
    --paranoid \
    --inadvisably-no-sandbox
else
  lake comparator \
    --config=comparator.json \
    --challenge-from-export="$replica_tmpdir/Challenge.ndjson" \
    --solution-from-export="$replica_tmpdir/Solution.ndjson" \
    --paranoid
fi

echo "REPLICA VERDICT: PASS"
echo "Statement matching, declaration kinds, permitted axioms, Lean kernel, and all bundled independent checkers passed."
