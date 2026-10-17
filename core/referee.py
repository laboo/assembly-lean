#!/usr/bin/env python3
"""The referee for the strict core (model v4.0.0).

Everyday language:
  * LOCK.   `referee.py lock --by NAME` records the fingerprint of the core (its Lean files, the
            rulebook, this referee and the build file). Run it only with the author's go. Once
            locked, the referee refuses to run if anything in the core has changed.
  * SEAL.   `referee.py run TRIAL` asks the Lean runner for a prediction and writes it to the log
            BEFORE it opens the observed numbers. Only then does it open them and compare.
  * LOG.    Every try goes into core/log.jsonl, and each entry carries the fingerprint of the
            entry before it, so editing or deleting a try breaks the chain. Failures, stops and
            refusals are logged exactly like passes.
  * VERIFY. `referee.py verify` rechecks the whole chain.
  * REPORT. `referee.py report` lists every trial and every try, so cherry-picking shows.

The referee does no physics. Odds come only from the Lean runner; comparisons use exact fractions.
"""
import hashlib
import json
import subprocess
import sys
import time
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CORE = ROOT / "core"
LOG = CORE / "log.jsonl"
LOCK = CORE / "LOCK.json"
TRIALS = CORE / "trials"
OBSERVED = CORE / "observed"
RUNNER = ROOT / ".lake" / "build" / "bin" / "strictcore"
MODEL = "4.0.0"


def core_files():
    files = [ROOT / "StrictCore.lean", ROOT / "lakefile.toml", CORE / "RULEBOOK.md", CORE / "referee.py"]
    files += sorted((ROOT / "StrictCore").glob("*.lean"))
    return files


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def fingerprint():
    parts = {str(f.relative_to(ROOT)): sha(f.read_bytes()) for f in core_files()}
    whole = sha(json.dumps(parts, sort_keys=True).encode())
    return whole, parts


def read_log():
    if not LOG.exists():
        return []
    return [json.loads(line) for line in LOG.read_text().splitlines() if line.strip()]


def entry_hash(entry):
    body = {k: v for k, v in entry.items() if k != "hash"}
    return sha(json.dumps(body, sort_keys=True).encode())


def append(entry):
    log = read_log()
    entry["n"] = len(log)
    entry["prev"] = log[-1]["hash"] if log else "start"
    entry["time"] = time.strftime("%Y-%m-%dT%H:%M:%S%z")
    entry["hash"] = entry_hash(entry)
    with LOG.open("a") as fh:
        fh.write(json.dumps(entry, sort_keys=True) + "\n")
        fh.flush()
    return entry


def lock_state():
    whole, _ = fingerprint()
    if not LOCK.exists():
        return whole, "draft"
    locked = json.loads(LOCK.read_text())
    if locked["fingerprint"] != whole:
        return whole, "CHANGED"
    return whole, "locked"


def cmd_lock(by):
    whole, parts = fingerprint()
    LOCK.write_text(json.dumps({"model": MODEL, "fingerprint": whole, "files": parts,
                                "approved_by": by, "time": time.strftime("%Y-%m-%dT%H:%M:%S%z")},
                               indent=2, sort_keys=True) + "\n")
    append({"kind": "locked", "core": whole, "approved_by": by, "model": MODEL})
    print(f"Core locked: {whole[:16]}... (approved by {by})")


def cmd_run(name):
    whole, state = lock_state()
    if state == "CHANGED":
        print("REFUSED: the core has changed since it was locked. A change needs a new model "
              "version with the author's go, then a new lock.")
        sys.exit(2)
    trial_path = TRIALS / f"{name}.json"
    trial_bytes = trial_path.read_bytes()
    out = subprocess.run([str(RUNNER)], input=trial_bytes, capture_output=True, check=True)
    prediction = json.loads(out.stdout)
    base = {"trial": name, "trial_sha": sha(trial_bytes), "core": whole, "core_state": state,
            "model": MODEL, "prediction": prediction}
    if prediction["result"] != "odds":
        e = append(dict(base, kind=prediction["result"]))
        print(f"{name}: {prediction['result'].upper()} -- {prediction.get('reason', '')}  [log #{e['n']}]")
        return
    sealed = append(dict(base, kind="sealed"))
    # Only now, after the prediction is in the log, are the observed numbers opened.
    obs = json.loads((OBSERVED / f"{name}.json").read_text())
    verdict, detail = compare(prediction, obs)
    e = append({"kind": "compared", "trial": name, "sealed": sealed["hash"], "observed": obs,
                "verdict": verdict, "detail": detail, "core": whole, "core_state": state})
    print(f"{name}: {verdict.upper()} -- {detail}  [sealed #{sealed['n']}, compared #{e['n']}]")


def compare(prediction, obs):
    pred = {a["answer"]: Fraction(a["part"], a["whole"]) for a in prediction["answers"]}
    want = obs["answers"]
    if set(pred) != set(want):
        return "fail", f"answers {sorted(pred)} but observed {sorted(want)}"
    notes = []
    for k, p in pred.items():
        lo, hi = Fraction(want[k][0]), Fraction(want[k][1])
        if not (lo <= p <= hi):
            return "fail", f"'{k}' predicted {p}, observed between {lo} and {hi}"
        notes.append(f"{k} {p}")
    return "pass", ", ".join(notes) + " (each within the observed range)"


def cmd_verify():
    log = read_log()
    prev, sealed = "start", set()
    for e in log:
        if e["prev"] != prev or entry_hash(e) != e["hash"]:
            print(f"BROKEN at entry #{e.get('n')}: the log was edited or an entry was removed.")
            sys.exit(3)
        if e["kind"] == "sealed":
            sealed.add(e["hash"])
        if e["kind"] == "compared" and e["sealed"] not in sealed:
            print(f"BROKEN at entry #{e['n']}: a comparison with no sealed prediction before it.")
            sys.exit(3)
        prev = e["hash"]
    whole, state = lock_state()
    print(f"Log intact: {len(log)} entries, chain unbroken. Core is {state} ({whole[:16]}...).")


def cmd_report():
    log = read_log()
    rows = {}
    for e in log:
        if "trial" in e and e["kind"] != "sealed":
            rows.setdefault(e["trial"], []).append(e.get("verdict", e["kind"]))
    for name, tries in sorted(rows.items()):
        print(f"{name:32s} tries: {len(tries)}  results: {', '.join(tries)}")


if __name__ == "__main__":
    args = sys.argv[1:]
    if not args:
        print(__doc__)
    elif args[0] == "lock":
        cmd_lock(args[args.index("--by") + 1] if "--by" in args else "unknown")
    elif args[0] == "run":
        for n in args[1:]:
            cmd_run(n)
    elif args[0] == "verify":
        cmd_verify()
    elif args[0] == "report":
        cmd_report()
