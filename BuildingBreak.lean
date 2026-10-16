import BuildingFlip
import Mathlib.NumberTheory.Zsqrtd.QuadraticReciprocity
import Mathlib.NumberTheory.SumTwoSquares

/-!
# The Building, piece 7: breaking apart

Everyday-language summary (for the author):

The model says some whole numbers break apart into a turned piece and its mirror image,
others don't, and a number always breaks apart the same way. This file connects our spots
to Mathlib's whole-number points of the complex plane (its "Gaussian integers") and brings
in what mathematics already knows:

* our spots **are** Mathlib's Gaussian integers, with the same adding, turning and mirror;
* a prime number that leaves remainder 1 or 2 when divided by 4 (2, 5, 13, 17, …)
  **breaks apart into a turned piece times its mirror image**, e.g. 5 = (2 + i)(2 − i)
  (Fermat's two-square theorem, 1640, proved by Euler);
* a prime that leaves remainder 3 (3, 7, 11, …) **never breaks apart**, not even into
  pieces that aren't mirror images;
* breaking apart is **always the same** up to quarter turns of the pieces (whole-number
  points of the plane have unique factorization, Gauss, 1832).
-/

namespace Building

open GaussianInt

/-! ## Our spots are Mathlib's Gaussian integers -/

/-- A spot as one of Mathlib's Gaussian integers. -/
def Spot.toG (z : Spot) : GaussianInt := ⟨z.re, z.im⟩

/-- A Gaussian integer as a spot. -/
def Spot.ofG (g : GaussianInt) : Spot := ⟨g.re, g.im⟩

theorem Spot.ofG_toG (z : Spot) : Spot.ofG z.toG = z := rfl
theorem Spot.toG_ofG (g : GaussianInt) : (Spot.ofG g).toG = g := rfl

theorem Spot.toG_add (z w : Spot) : (z + w).toG = z.toG + w.toG := by
  ext <;> simp [Spot.toG]

/-- Our turning rule is Mathlib's multiplication of Gaussian integers. -/
theorem Spot.toG_mul (z w : Spot) : (z * w).toG = z.toG * w.toG := by
  ext <;> simp [Spot.toG] <;> ring

/-- Our mirror flip is Mathlib's conjugate of Gaussian integers. -/
theorem Spot.toG_flip (z : Spot) : z.flip.toG = star z.toG := by
  ext <;> simp [Spot.toG]

theorem Spot.toG_nat (p : ℕ) : (⟨p, 0⟩ : Spot).toG = (p : GaussianInt) := by
  ext <;> simp [Spot.toG]

/-! ## Which numbers break apart -/

/-- A spot times its mirror image is a plain whole number: its squared size. -/
theorem Spot.mul_flip (z : Spot) : z * z.flip = ⟨z.re * z.re + z.im * z.im, 0⟩ := by
  ext <;> simp <;> ring

/-- **Primes leaving remainder 1 or 2 break apart into a turned piece and its mirror
image** (Fermat's two-square theorem). -/
theorem breaks_apart (p : ℕ) [Fact p.Prime] (hp : p % 4 ≠ 3) :
    ∃ π : Spot, π * π.flip = ⟨p, 0⟩ := by
  obtain ⟨a, c, h⟩ := Nat.Prime.sq_add_sq hp
  refine ⟨⟨a, c⟩, ?_⟩
  rw [Spot.mul_flip]
  ext
  · simp only
    have : ((a ^ 2 + c ^ 2 : ℕ) : ℤ) = (p : ℤ) := by rw [h]
    push_cast at this
    linarith
  · rfl

theorem sq_add_sq_mod_four (x y : ℤ) : (x * x + y * y) % 4 ≠ 3 := by
  have hx : x % 4 = 0 ∨ x % 4 = 1 ∨ x % 4 = 2 ∨ x % 4 = 3 := by omega
  have hy : y % 4 = 0 ∨ y % 4 = 1 ∨ y % 4 = 2 ∨ y % 4 = 3 := by omega
  rcases hx with hx | hx | hx | hx <;> rcases hy with hy | hy | hy | hy <;>
    simp [Int.add_emod, Int.mul_emod, hx, hy]

/-- **Primes leaving remainder 3 never break into a piece and its mirror image.** -/
theorem never_breaks_into_mirror (p : ℕ) (hp : p % 4 = 3) :
    ¬ ∃ π : Spot, π * π.flip = ⟨p, 0⟩ := by
  rintro ⟨π, h⟩
  rw [Spot.mul_flip] at h
  have h1 := congrArg Spot.re h
  simp only at h1
  have h2 := sq_add_sq_mod_four π.re π.im
  rw [h1] at h2
  omega

/-- **In fact they never break apart at all**: such a prime is prime among the whole-number
points of the plane, and the primes leaving remainder 1 or 2 are not. -/
theorem prime_spot_iff (p : ℕ) [Fact p.Prime] :
    Prime (⟨p, 0⟩ : Spot).toG ↔ p % 4 = 3 := by
  rw [Spot.toG_nat]
  exact prime_iff_mod_four_eq_three_of_nat_prime p

/-- **Breaking apart is always the same** (up to quarter turns of the pieces): the
whole-number points of the plane have unique factorization. -/
instance : UniqueFactorizationMonoid GaussianInt := inferInstance

/-- **Piece 7 in one statement.** -/
theorem piece_seven :
    (∀ z w : Spot, (z * w).toG = z.toG * w.toG) ∧
    (∀ z : Spot, z.flip.toG = star z.toG) ∧
    (∀ (p : ℕ) [Fact p.Prime], p % 4 ≠ 3 → ∃ π : Spot, π * π.flip = ⟨p, 0⟩) ∧
    (∀ p : ℕ, p % 4 = 3 → ¬ ∃ π : Spot, π * π.flip = ⟨p, 0⟩) ∧
    (∀ (p : ℕ) [Fact p.Prime], Prime (⟨p, 0⟩ : Spot).toG ↔ p % 4 = 3) :=
  ⟨Spot.toG_mul, Spot.toG_flip, fun p _ hp => breaks_apart p hp, never_breaks_into_mirror,
    fun p _ => prime_spot_iff p⟩

end Building
