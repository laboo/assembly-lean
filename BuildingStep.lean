import BuildingLand
import StepMachine

/-!
# The Building, piece 9: the step rule (a toy), checked against Mathlib

Everyday-language summary (for the author):

* In Mathlib's complex plane, one tick of the checkerboard is: mix each cell's two arrows
  (each arrow carries on, plus a quarter turn of the other), then shrink by one floor's
  shrink, then step one cell. Lean checks that this **keeps the total exactly**: the
  arrows' squared sizes add up to the same amount after every tick. Physicists call such a
  step "unitary".
* The whole-number machine in `StepMachine.lean` does exactly this mix, and its "doubling
  total" is the same fact read one floor coarser: **read one floor finer per tick, the odds
  always add up to exactly one**.
* Nothing here depends on trusting our definitions: the size-keeping statement uses only
  Mathlib's own complex numbers, `I`, adding, multiplying and squared size.
-/

namespace Building

open Complex

/-- A spot's whole-number squared size is Mathlib's squared size. -/
theorem nsq_eq_normSq (z : Spot) : (nsq z : ℝ) = normSq z.toC := by
  simp only [nsq, normSq_apply, Spot.toC_re, Spot.toC_im]
  push_cast
  ring

/-- What a cell sends right, in Mathlib's plane: the right arrow plus a quarter turn back of
the left arrow. -/
theorem toC_sendR (c : Cell) : (sendR c).toC = c.1.toC - I * c.2.toC := by
  simp only [sendR, toC_sub, Spot.toC_mul, Spot.toC_i]

/-- What a cell sends left, in Mathlib's plane. -/
theorem toC_sendL (c : Cell) : (sendL c).toC = c.2.toC - I * c.1.toC := by
  simp only [sendL, toC_sub, Spot.toC_mul, Spot.toC_i]

theorem normSq_shrink : normSq shrink = 1 / 2 := by
  rw [Complex.normSq_eq_norm_sq, norm_shrink_sq]

/-- **One tick keeps the total exactly** (in Mathlib's own terms): mixing two arrows and
shrinking by one floor's shrink leaves the sum of their squared sizes unchanged. -/
theorem tick_keeps_total (R L : ℂ) :
    normSq (shrink * (R - I * L)) + normSq (shrink * (L - I * R)) = normSq R + normSq L := by
  rw [normSq_mul, normSq_mul, normSq_shrink]
  simp only [normSq_apply, sub_re, sub_im, mul_re, mul_im, I_re, I_im]
  ring

/-- **The odds always add up to one**: read one floor finer per tick (each floor's shrink
halves squared sizes), the machine's total after `t` ticks is exactly the starting total. -/
theorem odds_kept (t : ℕ) (row : Row) : (total (run t row) : ℝ) * (1 / 2) ^ t = total row := by
  rw [total_run]
  push_cast
  rw [mul_comm ((2 : ℝ) ^ t), mul_assoc, ← mul_pow]
  norm_num

/-- **Piece 9 in one statement.** -/
theorem piece_nine :
    (∀ R L : ℂ, normSq (shrink * (R - I * L)) + normSq (shrink * (L - I * R)) =
      normSq R + normSq L) ∧
    (∀ c : Cell, (sendR c).toC = c.1.toC - I * c.2.toC ∧ (sendL c).toC = c.2.toC - I * c.1.toC) ∧
    (∀ z : Spot, (nsq z : ℝ) = normSq z.toC) ∧
    (∀ (t : ℕ) (row : Row), (total (run t row) : ℝ) * (1 / 2) ^ t = total row) ∧
    (∀ (t : ℕ) (row : Row), (run t row).length = row.length + 2 * t) ∧
    (∀ row : Row, untick (tick row) = row.map (fun c => (c.1 + c.1, c.2 + c.2))) ∧
    (∀ t : ℕ, total (run t start) = 2 ^ t) :=
  ⟨tick_keeps_total, fun c => ⟨toC_sendR c, toC_sendL c⟩, nsq_eq_normSq, odds_kept, run_length,
    untick_tick, tickets_run⟩

end Building
