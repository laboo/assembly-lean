/-
  THE STRICT CORE, part 5: the runner.                                   Model v4.0.0.

  Reads one trial (JSON) and prints one prediction (JSON), using only the core's own functions.
  It never sees observed numbers; the referee opens those only after sealing this output.

  Guards (rulebook, "What you can put in"):
  * Only the listed fields are accepted; any other field is refused.
  * A thing's state is PREPARED by a device, never typed in, so no one can tune a state.
  * Typed-in numbers (allowed only on the point and line floors) must be a thing: no spare
    piece of the compass may be given a job.
  * A magnet's axis must have a whole-number length.
  Where the model is silent, the runner answers "stop" with the reason.
-/
import Lean.Data.Json
import StrictCore.Measure

open Lean

namespace StrictCore.Run
open StrictCore

def stopJ (reason : String) : Json :=
  Json.mkObj [("result", "stop"), ("reason", reason), ("model", "4.0.0")]

def refuseJ (reason : String) : Json :=
  Json.mkObj [("result", "refused"), ("reason", reason), ("model", "4.0.0")]

def keysOf : Json → List String
  | .obj kvs => kvs.foldl (fun acc k _ => k :: acc) []
  | _ => []

def extraKey (j : Json) (allowed : List String) : Option String :=
  (keysOf j).find? (fun k => !allowed.contains k)

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

def readDevice (j : Json) : Except String Device := do
  if let some k := extraKey j ["device", "axis", "length"] then throw s!"unknown field '{k}' in a device"
  let kind ← (j.getObjVal? "device" >>= Json.getStr?)
  let axis ← (j.getObjVal? "axis" >>= ints)
  let length ← (j.getObjVal? "length" >>= Json.getInt?)
  if axis.length != 3 then throw "an axis needs three whole numbers (our floor)"
  if !wholeLength axis length then
    throw s!"axis {axis} does not have whole-number length {length}; other axes would need square roots"
  return { kind, axis, length }

def evalTrial (t : Json) : Json := Id.run do
  match (do
    if let some k := extraKey t ["particle", "experiment", "note"] then throw s!"unknown field '{k}'"
    let p ← t.getObjVal? "particle"
    let e ← t.getObjVal? "experiment"
    if let some k := extraKey p ["floor", "kind", "numbers"] then throw s!"unknown field '{k}' in particle"
    if let some k := extraKey e ["prepare", "measure"] then throw s!"unknown field '{k}' in experiment"
    let floor ← (p.getObjVal? "floor" >>= Json.getNat?)
    let kind ← (p.getObjVal? "kind" >>= Json.getStr?)
    let meas ← (e.getObjVal? "measure" >>= readDevice)
    return (p, e, floor, kind, meas) : Except String _) with
  | .error msg => return refuseJ msg
  | .ok (p, e, floor, kind, meas) =>
    if kind == "operation" then
      return stopJ "the model doesn't say what an operation is made of (rulebook hard stop)"
    if kind != "thing" then
      return refuseJ s!"a particle is a thing or an operation, not '{kind}'"
    if floor ≤ 1 then
      -- point or line floor: the thing is one plain number; no turning can sort it
      match p.getObjVal? "numbers" with
      | .ok nj =>
        match ints nj with
        | .ok xs =>
          if !(isThing floor xs) then
            return refuseJ "those numbers give a job to a spare piece of the compass"
          if len2 xs == 0 then return refuseJ "a particle of zero size"
        | .error m => return refuseJ m
      | .error _ => pure ()
      return Json.mkObj [("result", "odds"), ("model", "4.0.0"),
        ("answers", Json.arr #[answerJ "the only answer" (1, 1)])]
    if floor == 2 then
      return stopJ "a plane-floor particle with no path, that is, at rest (rulebook hard stop)"
    if floor ≥ 4 then
      return stopJ "how anything moves from one point to its neighbors (rulebook hard stop)"
    -- floor 3: our floor
    if (p.getObjVal? "numbers").toOption.isSome then
      return refuseJ "a thing's state on our floor is prepared by a device, never typed in"
    match (e.getObjVal? "prepare" >>= readDevice) with
    | .error m => return refuseJ s!"preparation: {m}"
    | .ok prep =>
      if prep.kind != "magnet" || meas.kind != "magnet" then
        return Json.mkObj [("result", "not built"), ("model", "4.0.0"),
          ("reason", "only magnets are built so far for things on our floor")]
      let x := preparedUp refJ prep.axis prep.length
      let up := thingUp refJ meas.axis meas.length x
      return Json.mkObj [("result", "odds"), ("model", "4.0.0"),
        ("answers", Json.arr #[answerJ "up" up, answerJ "down" (up.2 - up.1, up.2)])]

end StrictCore.Run

def main : IO Unit := do
  let stdin ← IO.getStdin
  let input ← stdin.readToEnd
  match Lean.Json.parse input with
  | .error m => IO.println (StrictCore.Run.refuseJ s!"not readable: {m}").compress
  | .ok t => IO.println (StrictCore.Run.evalTrial t).compress
