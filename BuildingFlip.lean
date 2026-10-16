import BuildingFull

/-!
# The Building, piece 5: the mirror flip

Everyday-language summary (for the author):

* The mirror image of a point keeps its east part and reverses its north part
  (Mathlib calls it the conjugate).
* The mirrored twist is the twist turned a quarter turn, so a full address is flipped
  floor by floor with no carrying: on the whole-number floors, the digit `j` floors below
  the ground floor is mirrored and turned `j` quarter turns; on the finer floors, the
  digit `n + 1` floors above the ground floor is mirrored and turned back one quarter turn
  per floor.
* Lean checks that this lands exactly on Mathlib's mirror image, and that **a full
  address times its flip is its squared size** (the number that, in the model's open
  question about landing, would set the odds).
* Plain 0s and 1s flip into exactly the five mirror digits (`flip_plain_digits` in
  `FlipMachine.lean`): the mirror digits are what plain digits look like in the mirror.
-/

namespace Building

open Complex ComplexConjugate

theorem toC_flip (z : Spot) : z.flip.toC = conj z.toC := by
  apply Complex.ext <;> simp

theorem toC_one : (1 : Spot).toC = 1 := by
  apply Complex.ext <;> simp

theorem toC_ipow (j : ℕ) : (ipow j).toC = I ^ j := by
  induction j with
  | zero => simp only [ipow, toC_one, pow_zero]
  | succ j ih => rw [ipow, Spot.toC_mul, ih, Spot.toC_i, pow_succ, mul_comm]

theorem I_pow_mod (m : ℕ) : I ^ (m % 4) = I ^ m := by
  conv_rhs => rw [← Nat.div_add_mod m 4, pow_add, pow_mul, I_pow_four, one_pow, one_mul]

/-- The mirrored shrink is the shrink turned back a quarter turn. -/
theorem conj_shrink : conj shrink = -I * shrink := by
  rw [shrink, twistC, map_inv₀, map_add, map_neg, map_one, conj_I]
  have h1 : (-1 + I : ℂ) ≠ 0 := twistC_ne_zero
  have h2 : (-1 + -I : ℂ) ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this
  field_simp
  ring_nf
  rw [I_sq]
  ring

theorem term_flipE (x : Endless) (n : ℕ) : term (flipE x) n = conj (term x n) := by
  simp only [term, flipE, MDigit.toSpot_turnN, Spot.toC_mul, toC_ipow, MDigit.toSpot_flip,
    toC_flip, map_mul, map_pow, conj_shrink, I_pow_mod]
  have h3 : I ^ (3 * (n + 1)) = (-I) ^ (n + 1) := by
    rw [pow_mul]
    congr 1
    rw [pow_succ, I_sq]; ring
  rw [h3]
  ring

/-- **Flipping an endless address lands on Mathlib's mirror image.** -/
theorem evalE_flipE (x : Endless) : evalE (flipE x) = conj (evalE x) := by
  simp only [evalE, term_flipE]
  rw [Complex.conj_tsum]

/-- **Flipping a full address lands on Mathlib's mirror image.** -/
theorem fullValue_flipFull (A : Full) : fullValue (flipFull A) = conj (fullValue A) := by
  simp only [fullValue, flipFull, valueM_flipWhole, toC_flip, evalE_flipE, map_add]

/-- **A full address times its flip is its squared size**, a plain non-negative number. -/
theorem fullValue_mul_flip (A : Full) :
    fullValue (fullMul A (flipFull A)) = (normSq (fullValue A) : ℂ) := by
  rw [fullValue_mul, fullValue_flipFull, Complex.mul_conj]

/-- Flipping twice gives back the same point. -/
theorem fullValue_flip_flip (A : Full) : fullValue (flipFull (flipFull A)) = fullValue A := by
  rw [fullValue_flipFull, fullValue_flipFull, conj_conj]

/-- **Piece 5 in one statement.** -/
theorem piece_five :
    b.flip = Spot.i * b ∧
    (∀ A : Full, fullValue (flipFull A) = conj (fullValue A)) ∧
    (∀ A : Full, fullValue (fullMul A (flipFull A)) = (normSq (fullValue A) : ℂ)) ∧
    (∀ (ds : List Bool) (j k : ℕ), (flipFrom j (ds.map MDigit.ofBool)).getD k .zero =
      if ds.getD k false then MDigit.one.turnN ((j + k) % 4) else .zero) :=
  ⟨b_flip, fullValue_flipFull, fullValue_mul_flip, flip_plain_digits⟩

end Building
