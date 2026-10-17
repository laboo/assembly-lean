#!/usr/bin/env python3
"""The referee for the strict core (model v4.1.0).

Everyday language:
  * LOCK.   `referee.py lock --by NAME` records the fingerprint of the core (its Lean files, the
            rulebook, this referee and the build file). Run it only with the author's go. Once
            locked, the referee refuses to run if anything in the core has changed.
  * REGISTER. `referee.py register TRIAL` writes the trial's input and its observed numbers into
            the log, with their fingerprints, BEFORE anyone asks the core about that trial. It notes
            any earlier poke of the same input, so a prediction seen before registering shows.
  * SEAL.   `referee.py run TRIAL` refuses a trial that isn't registered, or whose input or observed
            file changed since it was registered. It asks the Lean runner for a prediction and writes
            it to the log BEFORE it opens the observed numbers. Only then does it open them and compare.
  * LOG.    Every try goes into core/log.jsonl, and each entry carries the fingerprint of the
            entry before it, so editing or deleting a try breaks the chain. Failures, stops and
            refusals are logged exactly like passes.
  * POKE.   `referee.py poke NAME` (a trial file) or `referee.py poke --json '{...}'` (typed inline)
            asks the core for a prediction and logs it as exploration, input and all. Explore as
            much as you like, but only through here: only logged results count, so the number of
            tries always shows. (The runner run on its own marks its answer "not logged".)
  * VERIFY. `referee.py verify` rechecks the whole chain.
  * REPORT. `referee.py report` lists every trial and every try, formal runs and pokes, with what
            each poke returned, counts the tries per kind of particle, so cherry-picking shows, and
            flags any formal run whose input was poked before it was registered.

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
MODEL = "4.1.0"


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


def canon(trial):
    """A trial's physics, ignoring its note: the same particle and experiment count as the same input."""
    return json.dumps({k: v for k, v in trial.items() if k != "note"}, sort_keys=True)


def registration(name):
    """The latest registration of a trial in the log, or None."""
    found = None
    for e in read_log():
        if e["kind"] == "registered" and e.get("trial") == name:
            found = e
    return found


def cmd_register(name):
    trial_bytes = (TRIALS / f"{name}.json").read_bytes()
    obs_path = OBSERVED / f"{name}.json"
    obs_bytes = obs_path.read_bytes() if obs_path.exists() else None   # none for a trial expected to stop
    t_sha = sha(trial_bytes)
    same = canon(json.loads(trial_bytes))
    seen = [e["n"] for e in read_log() if e["kind"] in ("explore", "sealed", "stop", "refused")
            and isinstance(e.get("input"), dict) and canon(e["input"]) == same]
    e = append({"kind": "registered", "trial": name, "trial_sha": t_sha, "input": json.loads(trial_bytes),
                "observed_sha": sha(obs_bytes) if obs_bytes is not None else None,
                "observed": json.loads(obs_bytes) if obs_bytes is not None else None, "model": MODEL,
                "asked_before_registering": seen})
    note = f" (this exact input was already asked at log {seen})" if seen else ""
    print(f"{name}: registered [log #{e['n']}]{note}")


def cmd_run(name):
    whole, state = refuse_if_changed()
    trial_bytes = (TRIALS / f"{name}.json").read_bytes()
    reg = registration(name)
    if reg is None:
        print(f"REFUSED: {name} is not registered. Register its input and observed numbers first.")
        sys.exit(2)
    obs_path = OBSERVED / f"{name}.json"
    obs_now = sha(obs_path.read_bytes()) if obs_path.exists() else None
    if sha(trial_bytes) != reg["trial_sha"] or obs_now != reg["observed_sha"]:
        print(f"REFUSED: {name}'s input or observed file changed since it was registered (log #{reg['n']}).")
        sys.exit(2)
    prediction = ask_core(trial_bytes)
    base = {"trial": name, "trial_sha": sha(trial_bytes), "input": json.loads(trial_bytes),
            "core": whole, "core_state": state, "model": MODEL, "prediction": prediction,
            "registered": reg["hash"]}
    if prediction["result"] != "odds":
        e = append(dict(base, kind=prediction["result"]))
        print(f"{name}: {prediction['result'].upper()} -- {prediction.get('reason', '')}  [log #{e['n']}]")
        return
    sealed = append(dict(base, kind="sealed"))
    if reg["observed_sha"] is None:
        print(f"{name}: SEALED, but no observed numbers were registered, so there is nothing to compare  [sealed #{sealed['n']}]")
        return
    # Only now, after the prediction is in the log, are the observed numbers opened.
    obs = json.loads(obs_path.read_text())
    verdict, detail = compare(prediction, obs)
    e = append({"kind": "compared", "trial": name, "sealed": sealed["hash"], "observed": obs,
                "verdict": verdict, "detail": detail, "core": whole, "core_state": state})
    print(f"{name}: {verdict.upper()} -- {detail}  [sealed #{sealed['n']}, compared #{e['n']}]")


def ask_core(trial_bytes):
    out = subprocess.run([str(RUNNER), "--referee"], input=trial_bytes, capture_output=True, check=True)
    return json.loads(out.stdout)


def refuse_if_changed():
    whole, state = lock_state()
    if state == "CHANGED":
        print("REFUSED: the core has changed since it was locked. A change needs the author's go "
              "and a relock (and a new model version if the rules changed).")
        sys.exit(2)
    return whole, state


def cmd_poke(args):
    whole, state = refuse_if_changed()
    if args and args[0] == "--json":
        name, trial_bytes = "inline", args[1].encode()
    else:
        name, trial_bytes = args[0], (TRIALS / f"{args[0]}.json").read_bytes()
    try:
        trial = json.loads(trial_bytes)
    except json.JSONDecodeError as err:
        trial = {"unreadable": str(err)}
    prediction = ask_core(trial_bytes)
    e = append({"kind": "explore", "trial": name, "trial_sha": sha(trial_bytes), "input": trial,
                "core": whole, "core_state": state, "model": MODEL, "prediction": prediction})
    print(f"[explore, log #{e['n']}] {json.dumps(prediction)}")


def signature(entry):
    trial = entry.get("input")
    if not isinstance(trial, dict):
        path = TRIALS / f"{entry.get('trial')}.json"   # entries written before inputs were logged
        trial = json.loads(path.read_text()) if path.exists() else {}
    p = trial.get("particle", {}) if isinstance(trial.get("particle"), dict) else {}
    return f"floor {p.get('floor', '?')} {p.get('kind', '?')}"


def compare(prediction, obs):
    verdict, detail = compare_odds(prediction, obs)
    if verdict == "pass" and "structural" in prediction:
        return "structural pass", detail + "; STRUCTURAL: " + prediction["structural"]
    return verdict, detail


def compare_odds(prediction, obs):
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
    prev, sealed, registered = "start", set(), {}
    for e in log:
        if e["prev"] != prev or entry_hash(e) != e["hash"]:
            print(f"BROKEN at entry #{e.get('n')}: the log was edited or an entry was removed.")
            sys.exit(3)
        if e["kind"] == "sealed":
            sealed.add(e["hash"])
        if e["kind"] == "compared" and e["sealed"] not in sealed:
            print(f"BROKEN at entry #{e['n']}: a comparison with no sealed prediction before it.")
            sys.exit(3)
        if e["kind"] == "registered":
            registered[e["hash"]] = e["trial_sha"]
        if "registered" in e and registered.get(e["registered"]) != e.get("trial_sha"):
            print(f"BROKEN at entry #{e['n']}: a formal run with no matching registration before it.")
            sys.exit(3)
        prev = e["hash"]
    whole, state = lock_state()
    print(f"Log intact: {len(log)} entries, chain unbroken. Core is {state} ({whole[:16]}...).")


def cmd_report():
    log = read_log()
    rows, kinds, sealed_input, regs, flags = {}, {}, {}, {}, []
    for e in log:
        if e["kind"] == "registered":
            regs[e["hash"]] = e
            continue
        if e["kind"] == "sealed":
            sealed_input[e["hash"]] = e
            reg = regs.get(e.get("registered"))
            if reg and reg.get("asked_before_registering"):
                flags.append(f"  {e['trial']} (sealed #{e['n']}): this input was asked at log "
                             f"{reg['asked_before_registering']} before it was registered")
        if "trial" in e and e["kind"] != "sealed":
            label = e.get("verdict", e["kind"])
            if e["kind"] == "explore":
                label = "explore:" + e.get("prediction", {}).get("result", "?")
            rows.setdefault(e["trial"], []).append(label)
            src = sealed_input.get(e.get("sealed"), e)
            kinds.setdefault(signature(src), []).append(label)
    print("Every trial, every try (formal runs and pokes):")
    for name, tries in sorted(rows.items()):
        print(f"  {name:32s} tries: {len(tries)}  results: {', '.join(tries)}")
    print("Tries per kind of particle (a high count before a pass means a search, not a prediction):")
    for sig, tries in sorted(kinds.items()):
        print(f"  {sig:32s} tries: {len(tries)}  results: {', '.join(tries)}")
    print("Formal runs whose input was asked before it was registered (a prediction seen first):")
    print("\n".join(flags) if flags else "  none")


if __name__ == "__main__":
    args = sys.argv[1:]
    if not args:
        print(__doc__)
    elif args[0] == "lock":
        cmd_lock(args[args.index("--by") + 1] if "--by" in args else "unknown")
    elif args[0] == "register":
        for n in args[1:]:
            cmd_register(n)
    elif args[0] == "run":
        for n in args[1:]:
            cmd_run(n)
    elif args[0] == "poke":
        cmd_poke(args[1:])
    elif args[0] == "verify":
        cmd_verify()
    elif args[0] == "report":
        cmd_report()
