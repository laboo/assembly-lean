/-
  THE STRICT CORE, part 2: what the compass gives, checked by Lean.   Model v4.0.0.

  Each fact below is computed from the multiplication rule in `Compass.lean` and checked by
  Lean's kernel (`decide`). Nothing is typed in from physics. Where a fact is a consequence of
  a rule rather than an observation, the comment says so.
-/
import StrictCore.Compass

namespace StrictCore

set_option maxRecDepth 100000

/-! ## Rule 3, counted: how many pieces a thing may use on each floor -/

-- Point and line: one plain number (a turning needs two directions).
theorem width_point : thingWidth 0 = 1 := by decide
theorem width_line  : thingWidth 1 = 1 := by decide
-- Plane: two (the complex plane). Ours: four (the four-wide numbers). Fourth: eight.
theorem width_plane : thingWidth 2 = 2 := by decide
theorem width_ours  : thingWidth 3 = 4 := by decide
theorem width_four  : thingWidth 4 = 8 := by decide

/-! ## The plane's turning is the complex plane's i -/

-- The plane floor's turning, multiplied by itself, is minus one: it behaves exactly like i.
theorem plane_turning_is_i : mul 2 (piece 2 3) (piece 2 3) = plain 2 (-1) := by decide

/-! ## Rule 4: a full turn (four quarter turns) on our floor -/

/-- Four quarter turns in the plane of directions 0 and 1, applied to the plain number 1:
    the full-turn multiplier. -/
def fullTurn3 : C := rep (mul 3 (quarter 3 0 1)) 4 (plain 3 1)

-- A full turn multiplies by minus four: minus one, times a size factor that odds never see.
theorem fullTurn3_is_minus : fullTurn3 = plain 3 (-4) := by decide

-- So a thing after one full turn is minus itself (here a thing using all four of its pieces):
def aThing : C := [2, 0, 0, -1, 0, 3, 5, 0]   -- plain 2, turnings 01: -1, 02: 3, 12: 5
theorem aThing_is_thing : isThing 3 aThing = true := by decide
theorem thing_full_turn :
    rep (turnThing 3 (quarter 3 0 1)) 4 aThing = scale (-4) aThing := by decide
-- ...and back after two full turns.
theorem thing_two_turns :
    rep (turnThing 3 (quarter 3 0 1)) 8 aThing = scale 16 aThing := by decide

-- An operation (here a direction) comes back after ONE full turn, because it is turned from
-- both sides. (Size factor 16, which odds never see.)
theorem op_full_turn :
    rep (turnOp 3 (quarter 3 0 1)) 4 (piece 3 1) = scale 16 (piece 3 1) := by decide +kernel
-- After half a turn the direction points the opposite way.
theorem op_half_turn :
    rep (turnOp 3 (quarter 3 0 1)) 2 (piece 3 1) = scale (-4) (piece 3 1) := by decide +kernel

/-! ## The fourth floor: two halves, told apart by the volume piece -/

/-- The fourth floor's volume piece: all four directions multiplied together. -/
def vol4 : C := piece 4 15

-- Two turnings in separate planes multiply into the volume piece (so rule 3 takes it in).
theorem turnings_make_volume : mul 4 (piece 4 3) (piece 4 12) = vol4 := by decide
-- The volume piece times itself is plus one.
theorem vol4_squared : mul 4 vol4 vol4 = plain 4 1 := by decide
-- It commutes with every one of the six turnings, so it never mixes a thing's two halves.
theorem vol4_commutes_with_turnings :
    [3, 5, 6, 9, 10, 12].all (fun a => mul 4 vol4 (piece 4 a) == mul 4 (piece 4 a) vol4) = true := by
  decide
-- Multiplying by it never leaves a thing-piece where it was, so its "trace" on the eight
-- thing-pieces is zero. With "squared is one", this means the eight pieces split into
-- two halves of exactly four: two four-wide numbers, one for each handedness.
theorem vol4_trace_zero :
    (((List.range 16).filter (fun a => size 4 a % 2 == 0)).map
        (fun a => coef (mul 4 vol4 (piece 4 a)) a)).foldl (· + ·) 0 = 0 := by decide

/-! ## The hook to watch: our floor's volume piece behaves like i -/

def vol3 : C := piece 3 7
-- Squared, it is minus one...
theorem vol3_squared : mul 3 vol3 vol3 = plain 3 (-1) := by decide
-- ...and it commutes with every piece of our floor's compass.
theorem vol3_commutes :
    (List.range 8).all (fun a => mul 3 vol3 (piece 3 a) == mul 3 (piece 3 a) vol3) = true := by
  decide
-- But it is not a thing-piece (three directions is odd), so rule 3 forbids a thing to use it.
theorem vol3_not_thing : isThing 3 vol3 = false := by decide

end StrictCore
