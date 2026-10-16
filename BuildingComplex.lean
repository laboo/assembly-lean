import Building
import Mathlib.Basic.Complex.Basic

/-!
# The Building meets Mathlib's complex plane

Everyday-language summary (for the author):

Piece 1 (`Building.lean`) works with whole numbers only. This file brings in
Mathlib, the standard library of checked mathematics, and its official complex
numbers `ℂ`, and proves that our 0-and-1 machine agrees with them exactly:

1. Reading an address in Mathlib's complex plane is Penney's formula:
   digit + (−1 + i)·(digit + (−1 + i)·(…)).
2. Every point of the complex plane with whole-number coordinates has an address,
   and no two different addresses land on the same point.
3. Adding addresses with the carry machine lands on Mathlib's sum.
4. Multiplying addresses with nothing but that adder lands on Mathlib's product.

So a skeptic can read every statement below using only Mathlib's own `ℂ`, `I`,
`+` and `·`, without trusting any of our definitions of spots.
-/

namespace Building

open Complex

/-! ## Placing spots in the complex plane -/

/-- Put a spot into Mathlib's complex plane: east becomes the real part,
north becomes the imaginary part. -/
noncomputable def Spot.toC (z : Spot) : ℂ := ⟨z.re, z.im⟩

@[simp] theorem Spot.toC_re (z : Spot) : z.toC.re = z.re := rfl
@[simp] theorem Spot.toC_im (z : Spot) : z.toC.im = z.im := rfl

theorem Spot.toC_add (z w : Spot) : (z + w).toC = z.toC + w.toC := by
  apply Complex.ext <;> simp

/-- Our turning rule is exactly Mathlib's complex multiplication. -/
theorem Spot.toC_mul (z w : Spot) : (z * w).toC = z.toC * w.toC := by
  apply Complex.ext <;> simp

/-- Different spots land on different points of the plane. -/
theorem Spot.toC_injective : Function.Injective Spot.toC := by
  intro z w h
  have hr := congrArg Complex.re h
  have hi := congrArg Complex.im h
  simp only [Spot.toC_re, Spot.toC_im, Int.cast_inj] at hr hi
  exact Spot.ext hr hi

/-- Our quarter turn is Mathlib's `I`. -/
theorem Spot.toC_i : Spot.i.toC = I := by
  apply Complex.ext <;> simp

/-- Our twist is Mathlib's `−1 + I`. -/
theorem toC_b : b.toC = -1 + I := by
  apply Complex.ext <;> simp

/-! ## Reading an address directly in the complex plane -/

/-- Penney's formula, written only with Mathlib's complex numbers. -/
noncomputable def penney : List Bool → ℂ
  | [] => 0
  | d :: ds => (if d then 1 else 0) + (-1 + I) * penney ds

/-- Reading an address our way, then placing it in the plane, is Penney's formula. -/
theorem toC_value (ds : List Bool) : (value ds).toC = penney ds := by
  induction ds with
  | nil => apply Complex.ext <;> simp [penney]
  | cons d ds ih =>
    rw [value_cons, Spot.toC_add, Spot.toC_mul, toC_b, ih, penney]
    congr 1
    cases d <;> apply Complex.ext <;> simp

/-! ## The main result -/

/-- **The 0-and-1 machine agrees with Mathlib's complex plane.**

* every point `x + y·i` with whole-number `x` and `y` has an address,
* two addresses that land on the same point are the same (spare zeros on the bottom floors aside),
* adding addresses lands on Mathlib's sum,
* multiplying addresses lands on Mathlib's product. -/
theorem building_agrees_with_complex :
    (∀ x y : ℤ, penney (address ⟨x, y⟩) = ⟨x, y⟩) ∧
    (∀ ds es : List Bool, penney ds = penney es → trim ds = trim es) ∧
    (∀ ds es : List Bool, penney (addA ds es) = penney ds + penney es) ∧
    (∀ ds es : List Bool, penney (mulA ds es) = penney ds * penney es) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y
    rw [← toC_value, value_address]
    rfl
  · intro ds es h
    rw [← toC_value, ← toC_value] at h
    exact trim_eq_of_value_eq ds es (Spot.toC_injective h)
  · intro ds es
    rw [← toC_value, ← toC_value, ← toC_value, value_addA, Spot.toC_add]
  · intro ds es
    rw [← toC_value, ← toC_value, ← toC_value, value_mulA, Spot.toC_mul]

end Building
