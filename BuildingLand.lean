import BuildingFull
import LandMachine

/-!
# The Building, piece 8: landing, floor by floor

Everyday-language summary (for the author):

* Landing picks one digit per floor with a coin handed in from outside
  (`LandMachine.lean`), and the spot it lands on is just the choices it made: after `n`
  floors, different chains of flips land on different spots.
* Here Lean checks **how fast a landing is pinned down**: after `n` flips, the final
  landing point is within `5/2 × (1/√2)^n` of the spot those flips chose, so each flip
  narrows where it lands by the same factor, `1/√2`, one floor's shrink.
* The odds of the flips stay outside the building, as in the model's open question.
  (Known math, not checked here: with fair coins, landings spread evenly over Penney's
  tile, the twin dragon.)
-/

namespace Building

open Complex Filter Topology

/-- Every endless address names a point within `5/2` of zero. -/
theorem norm_evalE_le (x : Endless) : ‖evalE x‖ ≤ 5 / 2 :=
  le_of_tendsto' ((continuous_norm.tendsto _).comp (tendsto_partialE x))
    (fun n => norm_partialE_le x n)

/-- What the floors beyond floor `n` add is that much smaller: one floor's shrink per floor. -/
theorem evalE_sub_partialE (x : Endless) (n : ℕ) :
    evalE x - partialE x n = shrink ^ n * evalE (fun k => x (k + n)) := by
  have h := twistC_pow_mul_evalE x n
  rw [toC_horner] at h
  have hp := shrink_pow_mul_twistC_pow n
  linear_combination (shrink ^ n) * h - (evalE x - partialE x n) * hp

/-- **Each floor narrows the point down by one floor's shrink.** -/
theorem narrowing (x : Endless) (n : ℕ) : ‖evalE x - partialE x n‖ ≤ 5 / 2 * ‖shrink‖ ^ n := by
  rw [evalE_sub_partialE, norm_mul, norm_pow, mul_comm]
  exact mul_le_mul_of_nonneg_right (norm_evalE_le _) (pow_nonneg (norm_nonneg _) n)

/-- **Landing is pinned down flip by flip**: after `n` flips, the landing point is within
`5/2 × (1/√2)^n` of the spot those flips chose on floor `n`. -/
theorem land_narrowing (coin : Coin) (n : ℕ) :
    ‖evalE (land coin) - shrink ^ n * (horner (land coin) n).toC‖ ≤ 5 / 2 * ‖shrink‖ ^ n := by
  have h : shrink ^ n * (horner (land coin) n).toC = partialE (land coin) n := by
    rw [toC_horner, ← mul_assoc, shrink_pow_mul_twistC_pow, one_mul]
  rw [h]
  exact narrowing _ n

/-- One floor's shrink, squared, is one half. -/
theorem shrink_sq_size : ‖shrink‖ ^ 2 = 1 / 2 := by
  rw [shrink, norm_inv, inv_pow, norm_twistC_sq]; norm_num

/-- **Piece 8 in one statement.** -/
theorem piece_eight :
    (∀ (coin coin' : Coin) (n : ℕ), horner (land coin) n = horner (land coin') n →
      ∀ k < n, coin k = coin' k) ∧
    (∀ (coin : Coin) (n : ℕ),
      ‖evalE (land coin) - shrink ^ n * (horner (land coin) n).toC‖ ≤ 5 / 2 * ‖shrink‖ ^ n) ∧
    ‖shrink‖ ^ 2 = 1 / 2 :=
  ⟨land_spot_determines_flips, land_narrowing, shrink_sq_size⟩

end Building
