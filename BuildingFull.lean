import BuildingMul
import FullMachine

/-!
# The Building, piece 4: the translator, over the whole plane

Everyday-language summary (for the author):

This finishes the translator from the mission: anything in the complex plane can be
carried into the building, and adding and multiplying in the building land exactly on
the complex plane's answers, with nothing added or lost.

* A **full address** holds one mirror digit on every floor: finitely many whole-number
  floors (the ground floor and the floors beneath it) and endlessly many finer floors
  above the ground floor. On the whole-number floors, arithmetic writes the tidy plain
  0/1 spelling.
* **Every point of Mathlib's complex plane has a full address**: round the point to the
  nearest whole-number spot (its whole-number floors), and the small remainder, never
  more than half a step away in each direction, gets an endless address on the finer
  floors.
* **Adding and multiplying full addresses**, using only the machines from pieces 1–3,
  land exactly on Mathlib's sum and product. When a climbing machine's answer must be
  moved six or twelve floors down, its first few finer floors simply move down to the
  whole-number floors.
-/

namespace Building

open Complex Filter Topology Finset

/-- The point a full address names: its whole part plus its endless part. -/
noncomputable def fullValue (A : Full) : ℂ := (valueM A.whole).toC + evalE A.tail

theorem valueM_plainM (ds : List Bool) : valueM (plainM ds) = value ds := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    simp only [plainM, List.map_cons, valueM, value_cons] at ih ⊢
    rw [ih]
    cases d <;> rfl

theorem value_tidy (ds : List MDigit) : value (tidy ds) = valueM ds := value_address _

theorem evalE_zeroE : evalE zeroE = 0 := by
  have : ∀ n, term zeroE n = 0 := by
    intro n; simp only [term, zeroE, MDigit.toSpot]; rw [show (⟨0, 0⟩ : Spot) = 0 from rfl, toC_zero]
    ring
  simp only [evalE, this, tsum_zero]

theorem fullValue_zero : fullValue Full.zero = 0 := by
  simp only [fullValue, Full.zero, valueM, toC_zero, evalE_zeroE, add_zero]

/-! ## Moving an endless address some floors down -/

/-- Moving `j` floors down: the first `j` finer floors become a whole-number spot, and the
rest stays endless. -/
theorem twistC_pow_mul_evalE (t : Endless) (j : ℕ) :
    twistC ^ j * evalE t = (horner t j).toC + evalE (fun n => t (n + j)) := by
  have hs := (summable_term t).sum_add_tsum_nat_add j
  have hshift : ∀ i, term t (i + j) = shrink ^ j * term (fun n => t (n + j)) i := by
    intro i; simp only [term]; ring
  simp only [hshift] at hs
  rw [tsum_mul_left] at hs
  have hp := shrink_pow_mul_twistC_pow j
  rw [toC_horner, evalE, ← hs]
  change twistC ^ j * (partialE t j + shrink ^ j * evalE (fun n => t (n + j))) =
    twistC ^ j * partialE t j + evalE (fun n => t (n + j))
  linear_combination (evalE (fun n => t (n + j))) * hp

theorem fullValue_lift (t : Endless) (j : ℕ) : fullValue (lift t j) = twistC ^ j * evalE t := by
  simp only [fullValue, lift, valueM_plainM, value_address]
  rw [twistC_pow_mul_evalE]

theorem twistC_pow_twelve : twistC ^ 12 = -64 := by
  rw [show 12 = 6 * 2 by rfl, pow_mul, twistC_pow_six]
  ring_nf
  rw [I_sq]
  ring

/-! ## Adding and multiplying full addresses -/

theorem fullValue_addH (H : ℕ) (A B : Full) :
    fullValue (fullAddH H A B) = fullValue A + fullValue B := by
  simp only [fullValue, fullAddH, lookupOr_memoArr, valueM_plainM]
  rw [value_addA, value_addA, value_address, value_tidy, value_tidy, Spot.toC_add, Spot.toC_add]
  have h := twistC_pow_mul_evalE (addE A.tail B.tail) 6
  have h2 := addE_correct A.tail B.tail
  linear_combination h2 - h

/-- **Adding full addresses lands on Mathlib's sum.** -/
theorem fullValue_add (A B : Full) : fullValue (fullAdd A B) = fullValue A + fullValue B :=
  fullValue_addH _ A B

theorem fullValue_sumH (H : ℕ) (As : List Full) :
    fullValue (sumFullH H As) = (As.map fullValue).sum := by
  induction As generalizing H with
  | nil => simp [sumFullH, fullValue_zero]
  | cons A As ih => simp [sumFullH, fullValue_addH, ih]

theorem fullValue_sum (As : List Full) : fullValue (sumFull As) = (As.map fullValue).sum :=
  fullValue_sumH _ As

theorem sum_liftsOf (ds : List Bool) (t : Endless) (j : ℕ) :
    ((liftsOf ds t j).map fullValue).sum = twistC ^ j * (value ds).toC * evalE t := by
  induction ds generalizing j with
  | nil => simp [liftsOf, toC_zero]
  | cons d ds ih =>
    simp only [liftsOf, List.map_append, List.sum_append, ih, value_cons, Spot.toC_add,
      Spot.toC_mul, toC_b']
    cases d
    · simp only [Bool.false_eq_true, ↓reduceIte, List.map_nil, List.sum_nil, zero_add]
      have : (dval false).toC = 0 := by apply Complex.ext <;> simp
      rw [this]; ring
    · simp only [↓reduceIte, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero, fullValue_lift]
      have : (dval true).toC = 1 := by apply Complex.ext <;> simp
      rw [this]; ring

/-- **Multiplying full addresses lands on Mathlib's product.** -/
theorem fullValue_mul (A B : Full) : fullValue (fullMul A B) = fullValue A * fullValue B := by
  simp only [fullMul, fullMulH, lookupOr_memoArr, fullValue_sumH, List.map_append,
    List.sum_append, sum_liftsOf, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    fullValue_lift, value_tidy]
  have h1 : fullValue ⟨plainM (mulA (tidy A.whole) (tidy B.whole)), zeroE⟩ =
      (valueM A.whole).toC * (valueM B.whole).toC := by
    simp only [fullValue, valueM_plainM, value_mulA, value_tidy, Spot.toC_mul, evalE_zeroE,
      add_zero]
  rw [h1, twistC_pow_twelve]
  have h2 := mulE_correct A.tail B.tail
  simp only [fullValue, pow_zero, one_mul]
  linear_combination -h2

/-! ## Every point of the plane has a full address -/

/-- The full address of a point: round it to the nearest whole-number spot for the
whole-number floors, and give the small remainder an endless address on the finer
floors. -/
noncomputable def fullOf (z : ℂ) : Full :=
  ⟨plainM (address ⟨round z.re, round z.im⟩),
    endlessAddress (z - (⟨round z.re, round z.im⟩ : Spot).toC)⟩

theorem fullValue_fullOf (z : ℂ) : fullValue (fullOf z) = z := by
  simp only [fullValue, fullOf, valueM_plainM, value_address]
  rw [every_disk_point_has_address]
  · ring
  · refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    simp only [sub_re, sub_im, Spot.toC_re, Spot.toC_im]
    have h1 := abs_sub_round z.re
    have h2 := abs_sub_round z.im
    linarith

/-! ## The translator -/

/-- **The translator from the mission, checked.** Every point of Mathlib's complex plane
has a full address (one mirror digit on every floor), and
adding and multiplying full addresses, using only the building's own machines, land
exactly on Mathlib's sum and product. -/
theorem translator :
    (∀ z : ℂ, ∃ A : Full, fullValue A = z) ∧
    (∀ A B : Full, fullValue (fullAdd A B) = fullValue A + fullValue B) ∧
    (∀ A B : Full, fullValue (fullMul A B) = fullValue A * fullValue B) :=
  ⟨fun z => ⟨fullOf z, fullValue_fullOf z⟩, fullValue_add, fullValue_mul⟩

end Building
