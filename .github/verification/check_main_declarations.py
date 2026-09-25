#!/usr/bin/env python3
"""Check designated API presence/kinds in the compiled, audited declaration inventory."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import time

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def check(contract, declarations):
    owner = contract.get("primaryOwner")
    if not isinstance(owner, str) or not owner:
        raise ValueError("Missing primary owner in main declaration contract")
    expected = contract["declarations"]
    if not expected or len({item["name"] for item in expected}) != len(expected):
        raise ValueError("Empty or duplicate main declaration contract")
    rows = {}
    for row in declarations:
        if row["name"] in rows:
            raise ValueError("Duplicate inventory name: " + row["name"])
        rows[row["name"]] = row
    for item in expected:
        name = item["name"]
        if name not in rows:
            raise ValueError("Missing main declaration: " + name)
        row = rows[name]
        if row["kind"] != item["kind"] or row["primaryOwner"] != owner:
            raise ValueError("Main declaration kind/owner changed: " + name)
        if item.get("module") and row["originModule"] != item["module"]:
            raise ValueError("Main declaration origin changed: " + name)
        if not row["isSafeKernelRoot"] or row["nonstandardAxioms"] or row["hasTransitiveSorry"]:
            raise ValueError("Main declaration failed proof policy: " + name)
    return len(expected)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--contract", type=Path, required=True)
    parser.add_argument("--verification", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    start = time.monotonic()
    report = {"passed": False, "startedUtc": datetime.now(timezone.utc).isoformat()}
    code = 1
    try:
        final_path = args.verification / "final.json"
        inventory_path = args.verification / "declarations.jsonl"
        final = json.loads(final_path.read_text())
        if final.get("passed") is not True or final.get("exitCode") != 0:
            raise ValueError("Mandatory verification has not passed")
        inventory_receipt = json.loads((args.verification / "inventory.json").read_text())
        bound = inventory_receipt["artifactSha256"].get(str(inventory_path.resolve()))
        if not inventory_receipt["passed"] or bound != digest(inventory_path):
            raise ValueError("Inventory artifact does not match successful stage receipt")
        for stage in final["stages"]:
            if not stage["passed"] or digest(Path(stage["receipt"])) != stage["sha256"]:
                raise ValueError("Verification stage receipt changed")
        count = check(json.loads(args.contract.read_text()),
                      (json.loads(line) for line in inventory_path.read_text().splitlines()))
        report.update(passed=True, declarationCount=count, inputSha256={
            str(path): digest(path) for path in [args.contract, final_path, inventory_path]})
        code = 0
    except Exception as error:
        report["error"] = str(error)
    report.update(exitCode=code, completedUtc=datetime.now(timezone.utc).isoformat(),
                  elapsedSeconds=round(time.monotonic() - start, 3),
                  scope="Presence and declaration kind; this does not compare theorem statements.")
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report))
    return code

if __name__ == "__main__":
    raise SystemExit(main())
