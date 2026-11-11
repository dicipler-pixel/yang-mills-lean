#!/usr/bin/env python3
# SCRIPT: YANG-MILLS-LEAN-VERIFY-01
"""Audit the Yang–Mills Lean library after `lake build`.

Why each check proves what it claims:

1. Axiom audit. `lake build` accepts a proof that uses `sorry` with only a
   warning, and a declared `axiom` would be accepted silently. `#print axioms`
   asks the kernel which axioms each theorem actually rests on. Requiring the
   answer to lie inside {propext, Classical.choice, Quot.sound} (the standard
   three every Mathlib theorem may use) rules out `sorry` (sorryAx), project
   axioms, and native_decide (Lean.ofReduceBool) for every named theorem.

2. Theorem inventory. The script discovers theorem names from the source files
   and fails if any expected module is missing or the count drops, so a theorem
   cannot silently disappear from the audit.

3. False controls. Each file in FalseControls/ states something deliberately
   false. It must FAIL to compile, and it must fail for a mathematical reason
   (unsolved goals, a failed tactic, a proposition proved false), not because of
   a typo or a missing name. This shows the checker can say no: a pipeline that
   accepts everything would pass the first two checks and fail this one.

4. Hashes. The SHA-256 of every source file is written to the report, so anyone
   can confirm the checked files are the files in the repository.

5. Banned tokens (ported from coxeter-rank2-lean scripts/gate.py). `sorry`,
   `admit`, `native_decide`, a declared `axiom`, `unsafe`, `implemented_by`,
   `opaque`, `Lean.ofReduceBool` or a `maxHeartbeats` override are refused by
   name in every top-level Lean file, before Lean runs. Files allowed a
   heartbeat override are listed in scripts/frozen_statements.json.

6. Statement parity (ported from gate.py). Each theorem listed in
   scripts/frozen_statements.json must still exist, and its statement (the text
   from `theorem <name>` to the first `:=`, comments stripped, whitespace
   collapsed) must equal the frozen text. A proof that quietly weakens a
   hypothesis or a conclusion therefore fails CI even though it compiles.
   Changing a frozen statement is deliberate: run
   `python3 scripts/verify.py --freeze` and commit the updated JSON.
   Files listed under "complete_files" are frozen whole: every theorem or lemma
   in them must be frozen, so a new or unlisted lemma cannot dodge the check.
   `--freeze` adds any missing theorems of those files.

`python3 scripts/verify.py --gate-only` runs checks 5 and 6 without Lean.
"""
from __future__ import annotations

import hashlib
import json
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
OUT = ROOT / "verification"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
CONFIG = json.loads((pathlib.Path(__file__).resolve().parent / "config.json").read_text())
MODULES = [(m["module"], m["path"]) for m in CONFIG["modules"]]
EXPECTED_THEOREMS = CONFIG["expected_theorems"]
EXPECTED_FALSE_CONTROLS = CONFIG["expected_false_controls"]
ROOT_IMPORTS = CONFIG["root_imports"]
# Private helper lemmas cannot be named from another file, so they are not listed; their
# axioms are audited through every public theorem that uses them.
THEOREM_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:protected\s+)?theorem\s+([^\s:({\[]+)", re.M)
NAMESPACE_RE = re.compile(r"^namespace\s+(\S+)", re.M)
MATH_FAILURE = re.compile(
    r"unsolved goals|proved that the proposition.*false|tactic '.*' failed|"
    r"linarith failed|failed to prove|decide failed|norm_num failed|type mismatch|"
    r"made no progress|failed to simplify",
    re.S | re.I)
INFRA_FAILURE = re.compile(
    r"unknown (?:module|identifier|constant|namespace)|unexpected token|"
    r"object file .* does not exist|invalid field", re.I)


FROZEN_PATH = pathlib.Path(__file__).resolve().parent / "frozen_statements.json"
BANNED = [
    (r"\bsorry\b", "sorry"),
    (r"\badmit\b", "admit"),
    (r"\bnative_decide\b", "native_decide"),
    (r"\bdecide\s*\+native\b", "decide +native"),
    (r"^\s*axiom\s", "declared axiom"),
    (r"\bopaque\s+(?:def|theorem)\b", "opaque"),
    (r"\bunsafe\b", "unsafe"),
    (r"\bimplemented_by\b", "implemented_by"),
    (r"\bLean\.ofReduceBool\b", "Lean.ofReduceBool"),
    (r"\bset_option\s+maxHeartbeats\b", "maxHeartbeats override"),
]
STATEMENT_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)?(?:theorem|lemma)\s+([^\s:({\[]+)",
    re.M)

LAST_OUTPUT = ""


def run(argv: list[str]) -> subprocess.CompletedProcess:
    global LAST_OUTPUT
    proc = subprocess.run(argv, cwd=ROOT, capture_output=True, text=True)
    LAST_OUTPUT = " ".join(argv) + "\n" + proc.stdout + proc.stderr
    return proc


def strip_comments(text: str) -> str:
    text = re.sub(r"/-.*?-/", "", text, flags=re.S)
    return re.sub(r"--[^\n]*", "", text)


def theorems_in(path: pathlib.Path) -> list[str]:
    text = strip_comments(path.read_text())
    spaces = sorted(set(NAMESPACE_RE.findall(text)))
    if len(spaces) != 1:
        raise SystemExit(f"{path}: expected exactly one namespace, found {spaces}")
    return [f"{spaces[0]}.{name}" for name in THEOREM_RE.findall(text)]


def statements(path: pathlib.Path) -> dict[str, str]:
    """Theorem name -> statement text (to the first `:=`), whitespace-normalised."""
    clean = strip_comments(path.read_text())
    out: dict[str, str] = {}
    for match in STATEMENT_RE.finditer(clean):
        tail = clean[match.end():]
        cut = tail.find(":=")
        text = " ".join((tail if cut < 0 else tail[:cut]).split())
        if match.group(1) in out:
            raise SystemExit(f"{path.name}: duplicate theorem name {match.group(1)}")
        out[match.group(1)] = text
    return out


def lean_sources() -> list[pathlib.Path]:
    return sorted(ROOT.glob("*.lean"))


def gate(frozen: dict) -> dict:
    """Checks 5 and 6: banned tokens and frozen-statement parity."""
    allow = set(frozen.get("allow_max_heartbeats", []))
    hits: dict[str, list[str]] = {}
    for path in lean_sources():
        clean = strip_comments(path.read_text())
        found = [label for pattern, label in BANNED
                 if re.search(pattern, clean, flags=re.M)
                 and not (label == "maxHeartbeats override" and path.name in allow)]
        if found:
            hits[path.name] = found
    if hits:
        raise SystemExit(f"banned tokens: {hits}")
    problems = []
    checked = 0
    for rel in frozen.get("complete_files", []):
        if rel not in frozen["statements"] or not (ROOT / rel).exists():
            problems.append(f"{rel}: complete file has no frozen statements or is missing")
            continue
        for name in statements(ROOT / rel):
            if name not in frozen["statements"][rel]:
                problems.append(f"{rel}: theorem {name} is not frozen (complete file)")
    for rel, frozen_stmts in frozen["statements"].items():
        path = ROOT / rel
        if not path.exists():
            problems.append(f"{rel}: file missing")
            continue
        have = statements(path)
        for name, text in frozen_stmts.items():
            checked += 1
            if name not in have:
                problems.append(f"{rel}: frozen theorem {name} missing")
            elif have[name] != text:
                problems.append(f"{rel}: statement of {name} changed\n"
                                f"  frozen: {text}\n  now:    {have[name]}")
    if problems:
        raise SystemExit("statement parity failed:\n" + "\n".join(problems))
    return {"banned_tokens": "none", "frozen_statements_checked": checked}


def freeze() -> int:
    """Rewrite frozen_statements.json from the current text of the listed theorems."""
    frozen = json.loads(FROZEN_PATH.read_text())
    for rel in frozen.get("complete_files", []):
        stmts = frozen["statements"].setdefault(rel, {})
        for name in statements(ROOT / rel):
            stmts.setdefault(name, "")
    for rel, stmts in frozen["statements"].items():
        have = statements(ROOT / rel)
        for name in stmts:
            if name not in have:
                raise SystemExit(f"{rel}: cannot freeze missing theorem {name}")
            stmts[name] = have[name]
    FROZEN_PATH.write_text(json.dumps(frozen, indent=2, ensure_ascii=False) + "\n")
    print(f"froze {sum(len(v) for v in frozen['statements'].values())} statements")
    return 0


def main() -> int:
    if "--freeze" in sys.argv:
        return freeze()
    gate_report = gate(json.loads(FROZEN_PATH.read_text()))
    if "--gate-only" in sys.argv:
        print(f"OK (gate only): no banned tokens, "
              f"{gate_report['frozen_statements_checked']} frozen statements match")
        return 0
    OUT.mkdir(exist_ok=True)
    report: dict = {"lean": run(["lean", "--version"]).stdout.strip(), "modules": {},
                    "gate": gate_report}

    # Inventory and hashes.
    names: list[str] = []
    for module, rel in MODULES:
        path = ROOT / rel
        found = theorems_in(path)
        if not found:
            raise SystemExit(f"no theorems found in {module}")
        report["modules"][module] = {
            "file": rel,
            "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
            "theorems": len(found),
        }
        names += found
    total = sum(v["theorems"] for v in report["modules"].values())
    if total != EXPECTED_THEOREMS:
        raise SystemExit(f"inventory changed: {total} theorems, expected {EXPECTED_THEOREMS}")
    report["theorems"] = total

    # Axiom audit.
    audit = OUT / "AxiomAudit.lean"
    lines = [f"import {m}" for m in ROOT_IMPORTS] + [""]
    lines += [f"#print axioms {name}" for name in names]
    audit.write_text("\n".join(lines) + "\n")
    proc = run(["lake", "env", "lean", str(audit.relative_to(ROOT))])
    log = proc.stdout + proc.stderr
    (OUT / "axioms.log").write_text(log)
    if proc.returncode != 0:
        print(log)
        raise SystemExit("axiom audit file did not compile")
    axioms: dict[str, list[str]] = {}
    for name in names:
        dep = re.search(re.escape(f"'{name}' depends on axioms: [") + r"([^\]]*)\]", log, re.S)
        none = f"'{name}' does not depend on any axioms" in log
        if dep:
            used = sorted(a.strip() for a in dep.group(1).replace("\n", " ").split(",") if a.strip())
        elif none:
            used = []
        else:
            raise SystemExit(f"no axiom report for {name}")
        bad = set(used) - ALLOWED
        if bad:
            raise SystemExit(f"{name} uses disallowed axioms {sorted(bad)}")
        axioms[name] = used
    report["axioms"] = axioms
    report["axiom_union"] = sorted({a for used in axioms.values() for a in used})

    # False controls.
    controls = {}
    for path in sorted((ROOT / "FalseControls").glob("*.lean")):
        proc = run(["lake", "env", "lean", str(path.relative_to(ROOT))])
        text = proc.stdout + proc.stderr
        (OUT / f"{path.stem}.log").write_text(text)
        if proc.returncode == 0:
            print(text)
            raise SystemExit(f"false control ACCEPTED: {path.name}")
        if INFRA_FAILURE.search(text) or not MATH_FAILURE.search(text):
            print(text)
            raise SystemExit(f"false control failed for the wrong reason: {path.name}")
        controls[path.stem] = "rejected"
    if len(controls) < EXPECTED_FALSE_CONTROLS:
        raise SystemExit(f"expected {EXPECTED_FALSE_CONTROLS} false controls, found {len(controls)}")
    report["false_controls"] = controls

    (OUT / "report.json").write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(f"OK: {total} theorems, "
          f"axioms used: {report['axiom_union']}, {len(controls)} false controls rejected, "
          f"{gate_report['frozen_statements_checked']} frozen statements match, no banned tokens")
    return 0


def annotate(message: str) -> None:
    """Surface a failure as a GitHub error annotation (readable without the log)."""
    flat = message.replace("%", "%25").replace("\r", "").replace("\n", "%0A")
    print(f"::error title=verify.py::{flat[:6000]}")


if __name__ == "__main__":
    try:
        sys.exit(main())
    except SystemExit as exc:
        if exc.code not in (0, None):
            annotate(str(exc.code) + "%0A" + LAST_OUTPUT[-5000:])
        raise
