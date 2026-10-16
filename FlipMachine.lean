import StreamMachine

/-!
# The mirror flip (plain Lean, no math library)

The mirror image of a spot keeps its east part and reverses its north part.
The mirrored twist, `−1 − i`, is the twist turned one quarter turn (`i · b`).
So flipping an address needs no carrying at all: on the whole-number floor `j` floors
below the ground floor, mirror the digit and turn it `j` more quarter turns. Plain 0s and 1s flip into exactly the five
mirror digits (0, or a 1 turned `j` quarter turns), which is where the mirror digits come
from.

The proofs here are whole-number proofs; the endless part is in `BuildingFlip.lean`.
-/

namespace Building

open Spot

/-! ## Mirror images and quarter turns of spots and digits -/

/-- The mirror image of a spot: same east part, north part reversed. -/
def Spot.flip (z : Spot) : Spot := ⟨z.re, -z.im⟩

@[simp] theorem Spot.flip_re (z : Spot) : z.flip.re = z.re := rfl
@[simp] theorem Spot.flip_im (z : Spot) : z.flip.im = -z.im := rfl

theorem Spot.flip_add (z w : Spot) : (z + w).flip = z.flip + w.flip := by
  ext <;> simp <;> omega

theorem Spot.flip_mul (z w : Spot) : (z * w).flip = z.flip * w.flip := by
  ext <;> simp <;> grind

/-- **The mirrored twist is the twist turned a quarter turn.** -/
theorem b_flip : b.flip = i * b := by decide

/-- Quarter turns: `i` multiplied `j` times. -/
def ipow : Nat → Spot
  | 0 => 1
  | j + 1 => i * ipow j

namespace MDigit

/-- The mirror image of a mirror digit. -/
def flip : MDigit → MDigit
  | zero => zero | one => one | negOne => negOne | up => down | down => up

/-- A quarter turn of a mirror digit. -/
def turn : MDigit → MDigit
  | zero => zero | one => up | up => negOne | negOne => down | down => one

/-- `j` quarter turns. -/
def turnN (d : MDigit) : Nat → MDigit
  | 0 => d
  | j + 1 => turn (turnN d j)

theorem toSpot_flip (d : MDigit) : d.flip.toSpot = d.toSpot.flip := by cases d <;> decide

theorem toSpot_turn (d : MDigit) : d.turn.toSpot = i * d.toSpot := by cases d <;> decide

theorem toSpot_turnN (d : MDigit) (j : Nat) : (d.turnN j).toSpot = ipow j * d.toSpot := by
  induction j with
  | zero => simp only [turnN, ipow]; ext <;> simp
  | succ j ih => rw [turnN, toSpot_turn, ih, ipow, Spot.mul_assoc]

theorem zero_turnN (j : Nat) : zero.turnN j = zero := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [turnN, ih, turn]

/-- A plain digit as a mirror digit. -/
def ofBool (d : Bool) : MDigit := if d then one else zero

/-- **The five mirror digits are 0 and the four quarter turns of 1.** -/
theorem eq_zero_or_turn_one (d : MDigit) : d = zero ∨ ∃ j < 4, d = one.turnN j := by
  cases d
  · exact Or.inl rfl
  · exact Or.inr ⟨0, by decide, rfl⟩
  · exact Or.inr ⟨2, by decide, rfl⟩
  · exact Or.inr ⟨1, by decide, rfl⟩
  · exact Or.inr ⟨3, by decide, rfl⟩

end MDigit

open MDigit

/-! ## Flipping the whole-number floors of an address -/

/-- Read a list of mirror digits, ground floor first and then each floor beneath it, as a
whole-number spot. -/
def valueM : List MDigit → Spot
  | [] => 0
  | d :: ds => d.toSpot + b * valueM ds

/-- Flip an address whose first digit sits `j` floors below the ground floor: mirror each
digit and turn it one more quarter turn per floor down. -/
def flipFrom : Nat → List MDigit → List MDigit
  | _, [] => []
  | j, d :: ds => d.flip.turnN (j % 4) :: flipFrom (j + 1) ds

theorem ipow_mod (j : Nat) : ipow (j % 4) = ipow j := by
  induction j using Nat.strongRecOn with
  | ind j ih =>
    by_cases h : j < 4
    · rw [Nat.mod_eq_of_lt h]
    · have h4 : j = (j - 4) + 4 := by omega
      rw [h4, Nat.add_mod_right, ih (j - 4) (by omega)]
      simp only [ipow]
      ext <;> simp <;> grind

theorem toSpot_turnN_mod (d : MDigit) (j : Nat) : (d.turnN (j % 4)).toSpot = ipow j * d.toSpot := by
  rw [toSpot_turnN, ipow_mod]

/-- **Flipping digit by digit gives the mirror image** (times the quarter turns of the floor
it starts on). No carrying is needed: each floor only looks at its own digit. -/
theorem valueM_flipFrom (j : Nat) (ds : List MDigit) :
    valueM (flipFrom j ds) = ipow j * (valueM ds).flip := by
  induction ds generalizing j with
  | nil => simp only [flipFrom, valueM]; ext <;> simp
  | cons d ds ih =>
    simp only [flipFrom, valueM, ih, toSpot_turnN_mod, toSpot_flip, Spot.flip_add, Spot.flip_mul,
      b_flip]
    simp only [ipow]
    ext <;> simp <;> grind

/-- Flip a whole address (first digit on the ground floor). -/
def flipWhole (ds : List MDigit) : List MDigit := flipFrom 0 ds

theorem valueM_flipWhole (ds : List MDigit) : valueM (flipWhole ds) = (valueM ds).flip := by
  rw [flipWhole, valueM_flipFrom]
  simp only [ipow]; ext <;> simp

/-- **The colleague's lead, checked.** Flip a plain 0/1 address, and the floor `k` floors
down holds either 0 or a 1 turned `k` quarter turns: plain digits flip into exactly the mirror digits. -/
theorem flip_plain_digits (ds : List Bool) (j k : Nat) :
    (flipFrom j (ds.map ofBool)).getD k .zero =
      if ds.getD k false then one.turnN ((j + k) % 4) else .zero := by
  induction ds generalizing j k with
  | nil => simp [flipFrom]
  | cons d ds ih =>
    cases k with
    | zero => cases d <;> simp [flipFrom, ofBool, MDigit.flip, zero_turnN]
    | succ k =>
      simp only [List.map_cons, flipFrom, List.getD_cons_succ]
      rw [ih (j + 1) k]
      simp only [Nat.add_assoc, Nat.add_comm 1 k]

end Building
