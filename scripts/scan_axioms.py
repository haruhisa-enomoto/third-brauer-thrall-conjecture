#!/usr/bin/env python3
"""Check every declaration of the library and Solution for axioms beyond the standard three.

A `module` file sees theorems without their proofs, so the scan runs in a generated
non-module file, which loads every proof body.
"""
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
SOURCE = """import LargeIndecomposable
import Solution

open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let mut count := 0
  let mut seen : NameSet := {}
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless (`LargeIndecomposable).isPrefixOf mod || mod == `Solution do continue
    count := count + 1
    for ax in ← collectAxioms name do
      seen := seen.insert ax
  let axioms := seen.toArray
  let extra := axioms.filter (fun a => !allowed.contains a)
  IO.println s!"scanned {count} declarations; axioms {axioms}; other {extra}"
"""


def main():
    output = ROOT / ".build-audit/axioms"
    output.mkdir(parents=True, exist_ok=True)
    source = output / "ScanAxioms.lean"
    source.write_text(SOURCE)
    result = subprocess.run(["lake", "env", "lean", "-j1", "-M30000", str(source.relative_to(ROOT))],
                            cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (output / "scan.log").write_text(result.stdout)
    line = next((l for l in result.stdout.splitlines() if l.startswith("scanned ")), None)
    if result.returncode or line is None or not line.endswith("other #[]"):
        raise SystemExit(result.stdout[-2000:])
    print(line)


if __name__ == "__main__":
    main()
