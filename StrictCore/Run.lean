/-
  THE STRICT CORE, part 5: the runner.                                   Model v4.1.0.

  Reads one trial (JSON) and prints one prediction (JSON), using only the core's own functions.
  It never sees observed numbers; the referee opens those only after sealing this output.

  It gives exactly three kinds of answer:
  * "odds"    -- the model says, and the core works it out;
  * "stop"    -- the input is in the model's language, but the model doesn't say (rulebook hard stops);
  * "refused" -- the input is not in the model's language, or it tries to set by hand what the
                 model says must come out.

  Input (the rulebook, "What you can put in"):
    { "particle":   { "floor": n, "kind": "thing" | "operation", "antiparticle": true|false },
      "experiment": { "measure": [ device, device, ... ] },
      "note": "..." }
  A device is { "device": "magnet" | "polarizer", "axis": [x, y, z], "length": L } or
  { "device": "screen" }. The first device in the list prepares the particle (its "up" answer
  is kept: preparing is measuring and keeping one answer); every later device is measured, and
  the core gives the odds of every chain of their answers.

  Guards, the same on every floor:
  * every field and every device is checked before the core looks at the floor;
  * no state is ever typed in: a device prepares it;
  * speeds, masses, charges and the like are refused: they must come out of the model;
  * a magnet's or polarizer's axis must have a whole-number length.
-/
import Lean.Data.Json
import StrictCore.Measure

open Lean

namespace StrictCore.Run
open StrictCore

def modelVersion : String := "4.1.0"

def stopJ (reason : String) : Json :=
  Json.mkObj [("result", "stop"), ("reason", reason), ("model", modelVersion)]

def refuseJ (reason : String) : Json :=
  Json.mkObj [("result", "refused"), ("reason", reason), ("model", modelVersion)]

def keysOf : Json → List String
  | .obj kvs => kvs.foldl (fun acc k _ => k :: acc) []
  | _ => []

def hasKey (j : Json) (k : String) : Bool := (j.getObjVal? k).toOption.isSome

/-- Words that name a property of a particle. The model says these come out; they never go in. -/
def properties : List String :=
  ["speed", "velocity", "mass", "charge", "energy", "momentum", "spin", "turning", "phase", "copies"]

/-- Check every key of an object: a typed-in state, a property, or anything unknown is refused. -/
def checkKeys (j : Json) (allowed : List String) (where_ : String) : Except String Unit := do
  for k in keysOf j do
    if allowed.contains k then continue
    if k == "numbers" || k == "state" then
      throw s!"a state is never typed in, on any floor: a device prepares it ('{k}' in {where_})"
    if properties.contains k then
      throw s!"'{k}' comes out of the model; it never goes in ({where_})"
    throw s!"unknown field '{k}' in {where_}"

def ints (j : Json) : Except String (List Int) := do
  let arr ← j.getArr?
  arr.toList.mapM (fun x => x.getInt?)

def reduce (p : Int × Int) : Int × Int :=
  let g : Int := Int.ofNat (Int.gcd p.1 p.2)
  if g == 0 then p else (p.1 / g, p.2 / g)

def answerJ (name : String) (p : Int × Int) : Json :=
  let r := reduce p
  Json.mkObj [("answer", name), ("part", r.1), ("whole", r.2)]

structure Device where
  kind : String
  axis : List Int
  length : Int

/-- A device, checked the same way on every floor. -/
def readDevice (j : Json) : Except String Device := do
  let kind ← (j.getObjVal? "device" >>= Json.getStr?)
  if kind == "screen" then
    checkKeys j ["device"] "a screen"
    return { kind, axis := [], length := 0 }
  if kind != "magnet" && kind != "polarizer" then
    throw s!"no such device '{kind}': a measurement is a magnet (a turning), a polarizer (a direction) or a screen (places)"
  checkKeys j ["device", "axis", "length"] s!"a {kind}"
  let axis ← (j.getObjVal? "axis" >>= ints)
  let length ← (j.getObjVal? "length" >>= Json.getInt?)
  if axis.length != 3 then throw "an axis needs three whole numbers (devices sit on our floor)"
  if !wholeLength axis length then
    throw s!"axis {axis} does not have whole-number length {length}; other axes would need square roots"
  return { kind, axis, length }

def upDown (s : Int) : String := if s == 1 then "up" else "down"

def chainName (ss : List Int) : String := " then ".intercalate (ss.map upDown)

structure Trial where
  floor : Nat
  kind : String
  anti : Bool
  devices : List Device
  turn : Bool
  pair : Bool

/-- Read and check the whole trial. Every refusal happens here, before any stop or any odds. -/
def readTrial (t : Json) : Except String Trial := do
  checkKeys t ["particle", "experiment", "note", "particles"] "the trial"
  let pair := hasKey t "particles"
  let (floor, kind, anti) ← if pair then pure (0, "thing", false) else do
    let p ← t.getObjVal? "particle"
    checkKeys p ["floor", "kind", "antiparticle"] "the particle"
    let floor ← (p.getObjVal? "floor" >>= Json.getNat?)
    let kind ← (p.getObjVal? "kind" >>= Json.getStr?)
    if kind != "thing" && kind != "operation" then
      throw s!"a particle is a thing or an operation, not '{kind}'"
    let anti ← match p.getObjVal? "antiparticle" with
      | .ok j => j.getBool?
      | .error _ => pure false
    pure (floor, kind, anti)
  let e ← t.getObjVal? "experiment"
  if hasKey e "prepare" then
    throw "preparing is the first measurement: put the preparing device first in 'measure'"
  checkKeys e ["measure", "turn"] "the experiment"
  let ds ← (e.getObjVal? "measure" >>= Json.getArr?)
  if ds.size == 0 then throw "an experiment needs at least one device"
  if ds.size > 9 then throw "at most 9 devices in one trial (the core builds only what an input names)"
  let devices ← ds.toList.mapM readDevice
  return { floor, kind, anti, devices, turn := hasKey e "turn", pair }

/-- Where the model is silent, say so. `none` means the model says and the core can work it out. -/
def silence (tr : Trial) : Option String :=
  if tr.pair then
    some "several particles are one object on a higher floor, but the model doesn't say which floor or how they combine (rulebook hard stop)"
  else if tr.turn then
    some "a turn on its own is invisible or the same as tilting the devices; it can only be seen when two paths recombine, which needs motion (rulebook hard stop)"
  else if tr.anti then
    some "which mirror is a particle's antiparticle is checked, never set, and the check needs motion (rulebook hard stop)"
  else if tr.kind == "operation" then
    some "the model doesn't say what an operation is made of (rulebook hard stop)"
  else if tr.floor == 2 then
    some "a plane-floor particle with no path, that is, at rest (rulebook hard stop)"
  else if tr.floor ≥ 4 then
    some "how anything moves from one point to its neighbors (rulebook hard stop)"
  else if tr.devices.any (·.kind == "screen") then
    some "a screen's answers are places, and reaching a place needs motion (rulebook hard stop)"
  else if tr.devices.any (·.kind == "polarizer") then
    some "the model doesn't say how a direction acts on a thing; multiplying a thing by a direction from one side makes it a non-thing (rulebook hard stop)"
  else if tr.devices.length < 2 then
    some "the model doesn't say what a source sends: the first device prepares the particle, so measuring needs a second device (rulebook hard stop)"
  else none

def evalTrial (t : Json) : Json := Id.run do
  match readTrial t with
  | .error msg => return refuseJ msg
  | .ok tr =>
    if let some why := silence tr then return stopJ why
    if tr.floor ≤ 1 then
      -- point or line floor: one plain number, so every device has one answer
      return Json.mkObj [("result", "odds"), ("model", modelVersion),
        ("structural", "one plain number can only give one answer, whatever is measured"),
        ("answers", Json.arr #[answerJ "the only answer" (1, 1)])]
    -- our floor: the first magnet prepares, every later magnet is measured, chain by chain
    match tr.devices with
    | [] => return stopJ "no devices"
    | prep :: rest =>
      let x := preparedUp refJ prep.axis prep.length
      let ms := rest.map fun d => (d.axis, d.length)
      let whole := wholeOf ms * len2 x
      let answers := (chains refJ ms x).map fun (ss, v) => answerJ (chainName ss) (len2 v, whole)
      return Json.mkObj [("result", "odds"), ("model", modelVersion), ("answers", Json.arr answers.toArray)]

end StrictCore.Run

/-- Run on its own, the runner marks its answer as not logged, so it can never pass as a result.
    The referee calls it with `--referee` and logs every answer. -/
def markUnlogged (fromReferee : Bool) (j : Lean.Json) : Lean.Json :=
  if fromReferee then j else j.setObjVal! "logged" "not logged: does not count (run it through core/referee.py)"

def main (args : List String) : IO Unit := do
  let fromReferee := args.contains "--referee"
  let stdin ← IO.getStdin
  let input ← stdin.readToEnd
  match Lean.Json.parse input with
  | .error m => IO.println (markUnlogged fromReferee (StrictCore.Run.refuseJ s!"not readable: {m}")).compress
  | .ok t => IO.println (markUnlogged fromReferee (StrictCore.Run.evalTrial t)).compress
