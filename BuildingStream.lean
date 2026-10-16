import BuildingComplex
import StreamMachine
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Complex.Basic

/-!
# The Building, piece 2: the finer floors, endless addresses, and mirror digits

Everyday-language summary (for the author):

* Below the point, the floors go on forever. An **endless address** hands over one
  digit per floor, on demand. Its digits are the five **mirror digits**:
  0, 1, −1, i and −i (zero, a step east or west, a step north or south).
* Reading an endless address in Mathlib's complex plane means adding up
  digit × (one floor's shrink)^floor, forever. Lean checks that this always
  settles on one definite point.
* **Every point of the unit disk has an endless address** (onto): at each floor
  one of the five mirror digits always keeps what's left within the disk.
* **Adding two endless addresses, top floor first:** a machine reads one floor of
  each address and writes one floor of the sum, never looking ahead. It remembers
  only a small leftover, which is always one of 85 values (checked by running
  through every case). The sum comes out written six floors higher; reading it six
  floors lower gives exactly Mathlib's sum. Each written digit depends only on the
  floors read so far.
-/

namespace Building

open Complex Filter Topology Finset

/-! ## 1. Mirror digits -/

namespace MDigit

theorem norm_toC_le (d : MDigit) : ‖d.toSpot.toC‖ ≤ 1 := by
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  cases d <;> simp [toSpot]

end MDigit

/-! ## 2. Endless addresses and how to read them -/

/-- The twist `−1 + i` in Mathlib's complex plane. -/
noncomputable def twistC : ℂ := -1 + I

/-- One floor's shrink: dividing by the twist. -/
noncomputable def shrink : ℂ := twistC⁻¹

theorem twistC_ne_zero : twistC ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp [twistC] at this

theorem shrink_mul_twistC : shrink * twistC = 1 := inv_mul_cancel₀ twistC_ne_zero

theorem toC_b' : b.toC = twistC := toC_b

theorem norm_twistC_sq : ‖twistC‖ ^ 2 = 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [twistC]
  norm_num

theorem one_lt_norm_twistC : 1 < ‖twistC‖ := by
  nlinarith [norm_twistC_sq, norm_nonneg twistC]

theorem norm_shrink_lt_one : ‖shrink‖ < 1 := by
  rw [shrink, norm_inv]
  exact inv_lt_one_of_one_lt₀ one_lt_norm_twistC

theorem norm_shrink_nonneg : 0 ≤ ‖shrink‖ := norm_nonneg _

/-- The contribution of floor `n + 1`. -/
noncomputable def term (x : Endless) (n : ℕ) : ℂ := (x n).toSpot.toC * shrink ^ (n + 1)

theorem norm_term_le (x : Endless) (n : ℕ) : ‖term x n‖ ≤ ‖shrink‖ ^ n := by
  rw [term, norm_mul, norm_pow]
  calc ‖(x n).toSpot.toC‖ * ‖shrink‖ ^ (n + 1) ≤ 1 * ‖shrink‖ ^ (n + 1) := by
        gcongr; exact MDigit.norm_toC_le _
    _ ≤ ‖shrink‖ ^ n := by
        rw [one_mul]
        exact pow_le_pow_of_le_one norm_shrink_nonneg norm_shrink_lt_one.le (Nat.le_succ n)

theorem summable_term (x : Endless) : Summable (term x) :=
  Summable.of_norm_bounded (summable_geometric_of_lt_one norm_shrink_nonneg norm_shrink_lt_one)
    (norm_term_le x)

/-- The point an endless address names: the sum over all floors. -/
noncomputable def evalE (x : Endless) : ℂ := ∑' n, term x n

/-- Reading only the first `k` floors. -/
noncomputable def partialE (x : Endless) (k : ℕ) : ℂ := ∑ n ∈ range k, term x n

theorem tendsto_partialE (x : Endless) : Tendsto (partialE x) atTop (𝓝 (evalE x)) :=
  (summable_term x).hasSum.tendsto_sum_nat

theorem partialE_succ (x : Endless) (k : ℕ) : partialE x (k + 1) = partialE x k + term x k :=
  sum_range_succ _ _

/-- The workhorse: if reading the first `k` floors misses a target by
`shrink^k × (something that stays bounded)`, the endless address names the target. -/
theorem evalE_eq_of_bounded (p : Endless) (L : ℕ → ℂ) (lim : ℂ)
    (hL : Tendsto L atTop (𝓝 lim)) (r : ℕ → ℂ) (B : ℝ) (hr : ∀ k, ‖r k‖ ≤ B)
    (h : ∀ k, L k - partialE p k = shrink ^ k * r k) : evalE p = lim := by
  have h1 : Tendsto (fun k => L k - partialE p k) atTop (𝓝 (lim - evalE p)) :=
    hL.sub (tendsto_partialE p)
  have h2 : Tendsto (fun k => L k - partialE p k) atTop (𝓝 0) := by
    simp_rw [h]
    apply squeeze_zero_norm (a := fun k => ‖shrink‖ ^ k * B)
    · intro k
      rw [norm_mul, norm_pow]
      exact mul_le_mul_of_nonneg_left (hr k) (pow_nonneg norm_shrink_nonneg k)
    · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one norm_shrink_nonneg
        norm_shrink_lt_one).mul_const B
  have := tendsto_nhds_unique h1 h2
  exact (sub_eq_zero.mp this).symm

/-! ## 3. Every point of the unit disk has an endless address -/

/-- Five mirror digits are enough: anything within `√2` of zero is within 1 of a digit. -/
theorem cover (v : ℂ) (hv : normSq v ≤ 2) : ∃ d : MDigit, normSq (v - d.toSpot.toC) ≤ 1 := by
  obtain ⟨x, y⟩ := v
  simp only [normSq_apply] at hv
  have key : ∀ d : MDigit, normSq (⟨x, y⟩ - d.toSpot.toC) =
      (x - (d.toSpot.re : ℝ)) * (x - d.toSpot.re) + (y - d.toSpot.im) * (y - d.toSpot.im) := by
    intro d; simp [normSq_apply]
  by_cases h0 : x * x + y * y ≤ 1
  · exact ⟨.zero, by rw [key]; simp [MDigit.toSpot]; linarith⟩
  rcases le_total (|y|) x with h1 | h1
  · -- east is the biggest direction: write 1
    refine ⟨.one, ?_⟩
    rw [key]; simp only [MDigit.toSpot]; push_cast
    have hx0 : 0 ≤ x := le_trans (abs_nonneg y) h1
    have hy : y * y ≤ x * x := by
      have := mul_self_le_mul_self (abs_nonneg y) h1
      rwa [abs_mul_abs_self] at this
    by_cases hx : 1 ≤ x
    · nlinarith
    · nlinarith [mul_nonneg hx0 (by linarith : (0:ℝ) ≤ 1 - x)]
  rcases le_total (|y|) (-x) with h2 | h2
  · -- west is the biggest direction: write −1
    refine ⟨.negOne, ?_⟩
    rw [key]; simp only [MDigit.toSpot]; push_cast
    have hx0 : 0 ≤ -x := le_trans (abs_nonneg y) h2
    have hy : y * y ≤ x * x := by
      have := mul_self_le_mul_self (abs_nonneg y) h2
      rw [abs_mul_abs_self] at this; nlinarith
    by_cases hx : 1 ≤ -x
    · nlinarith
    · nlinarith [mul_nonneg hx0 (by linarith : (0:ℝ) ≤ 1 + x)]
  have hxy : |x| ≤ |y| := by rw [abs_le]; constructor <;> linarith
  have hx : x * x ≤ y * y := by
    have := mul_self_le_mul_self (abs_nonneg x) hxy
    rwa [abs_mul_abs_self, abs_mul_abs_self] at this
  rcases le_total 0 y with h3 | h3
  · -- north is the biggest direction: write i
    refine ⟨.up, ?_⟩
    rw [key]; simp only [MDigit.toSpot]; push_cast
    by_cases hy : 1 ≤ y
    · nlinarith
    · nlinarith [mul_nonneg h3 (by linarith : (0:ℝ) ≤ 1 - y)]
  · -- south is the biggest direction: write −i
    refine ⟨.down, ?_⟩
    rw [key]; simp only [MDigit.toSpot]; push_cast
    by_cases hy : 1 ≤ -y
    · nlinarith
    · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ -y) (by linarith : (0:ℝ) ≤ 1 + y)]

/-- The digit chosen for a point (any digit that keeps the leftover inside the disk). -/
noncomputable def pick (v : ℂ) : MDigit :=
  if h : normSq v ≤ 2 then Classical.choose (cover v h) else .zero

theorem pick_spec (v : ℂ) (h : normSq v ≤ 2) : normSq (v - (pick v).toSpot.toC) ≤ 1 := by
  simp only [pick, h, ↓reduceDIte]
  exact Classical.choose_spec (cover v h)

/-- What is left of `z` after `k` floors have been written. -/
noncomputable def leftoverC (z : ℂ) : ℕ → ℂ
  | 0 => z
  | k + 1 => twistC * leftoverC z k - (pick (twistC * leftoverC z k)).toSpot.toC

/-- The endless address of `z`, one floor at a time. -/
noncomputable def endlessAddress (z : ℂ) : Endless :=
  fun k => pick (twistC * leftoverC z k)

theorem normSq_twistC : normSq twistC = 2 := by
  rw [normSq_apply]; simp [twistC]; norm_num

theorem leftoverC_small (z : ℂ) (hz : normSq z ≤ 1) (k : ℕ) : normSq (leftoverC z k) ≤ 1 := by
  induction k with
  | zero => exact hz
  | succ k ih =>
    apply pick_spec
    rw [normSq_mul, normSq_twistC]
    linarith

theorem leftoverC_identity (z : ℂ) (k : ℕ) :
    z - partialE (endlessAddress z) k = shrink ^ k * leftoverC z k := by
  induction k with
  | zero => simp [partialE, leftoverC]
  | succ k ih =>
    rw [partialE_succ, ← sub_sub, ih, term, leftoverC, endlessAddress]
    have hc := shrink_mul_twistC
    linear_combination (-(shrink ^ k * leftoverC z k)) * hc

/-- **Every point of the unit disk has an endless address of mirror digits.** -/
theorem every_disk_point_has_address (z : ℂ) (hz : ‖z‖ ≤ 1) :
    evalE (endlessAddress z) = z := by
  have hz' : normSq z ≤ 1 := by
    rw [← Complex.sq_norm]; nlinarith [norm_nonneg z]
  apply evalE_eq_of_bounded _ (fun _ => z) z tendsto_const_nhds (leftoverC z) 1
  · intro k
    have h := leftoverC_small z hz' k
    rw [← Complex.sq_norm] at h
    nlinarith [norm_nonneg (leftoverC z k)]
  · exact leftoverC_identity z

/-! ### The adder lands on Mathlib's sum -/

theorem InR_norm_le (u : Spot) (hu : InR u) : ‖u.toC‖ ≤ 9 := by
  have hre : -5 ≤ u.re ∧ u.re ≤ 5 := by unfold InR at hu; omega
  have him : -4 ≤ u.im ∧ u.im ≤ 4 := by unfold InR at hu; omega
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  simp only [Spot.toC_re, Spot.toC_im]
  have h1 : |(u.re : ℝ)| ≤ 5 := by
    rw [abs_le]; constructor <;> exact_mod_cast (by omega : _)
  have h2 : |(u.im : ℝ)| ≤ 4 := by
    rw [abs_le]; constructor <;> exact_mod_cast (by omega : _)
  linarith

theorem toC_twist6 : twist6.toC = twistC ^ 6 := by
  simp only [twist6, Spot.toC_mul, toC_b']
  ring

theorem toC_zero : (0 : Spot).toC = 0 := by
  apply Complex.ext <;> simp

theorem addE_identity (x y : Endless) (k : ℕ) :
    shrink ^ 6 * (partialE x k + partialE y k) - partialE (addE x y) k =
      shrink ^ k * (shrink ^ 6 * (addState x y k).toC) := by
  induction k with
  | zero => simp [partialE, addState, toC_zero]
  | succ k ih =>
    have hstate : (addState x y (k + 1)).toC =
        twistC * (addState x y k).toC + ((x k).toSpot.toC + (y k).toSpot.toC) -
          (addE x y k).toSpot.toC * twistC ^ 6 := by
      simp only [addState, addE, addStep]
      rw [show ∀ (p q : Spot), (p - q).toC = p.toC - q.toC from fun p q => by
        apply Complex.ext <;> simp]
      simp only [Spot.toC_add, Spot.toC_mul, toC_b', toC_twist6]
    rw [partialE_succ, partialE_succ, partialE_succ, hstate]
    have hc := shrink_mul_twistC
    have expand : shrink ^ 6 * (partialE x k + term x k + (partialE y k + term y k)) -
        (partialE (addE x y) k + term (addE x y) k) =
        (shrink ^ 6 * (partialE x k + partialE y k) - partialE (addE x y) k) +
        (shrink ^ 6 * (term x k + term y k) - term (addE x y) k) := by ring
    rw [expand, ih, term, term, term]
    set c := shrink
    set β := twistC
    set u := (addState x y k).toC
    set p := (addE x y k).toSpot.toC
    linear_combination
      (-(c ^ (k + 6) * u) + c ^ (k + 1) * p *
        (1 + c * β + (c * β) ^ 2 + (c * β) ^ 3 + (c * β) ^ 4 + (c * β) ^ 5)) * hc

/-- **Adding two endless addresses, top floor first, lands on Mathlib's sum**:
the written address, read six floors lower, is exactly `x + y`. -/
theorem addE_correct (x y : Endless) : twistC ^ 6 * evalE (addE x y) = evalE x + evalE y := by
  have h : evalE (addE x y) = shrink ^ 6 * (evalE x + evalE y) := by
    apply evalE_eq_of_bounded _ (fun k => shrink ^ 6 * (partialE x k + partialE y k))
      (shrink ^ 6 * (evalE x + evalE y))
      (((tendsto_partialE x).add (tendsto_partialE y)).const_mul _)
      (fun k => shrink ^ 6 * (addState x y k).toC) 9
    · intro k
      rw [norm_mul, norm_pow]
      calc ‖shrink‖ ^ 6 * ‖(addState x y k).toC‖ ≤ 1 * 9 := by
            apply mul_le_mul (pow_le_one₀ norm_shrink_nonneg norm_shrink_lt_one.le)
              (InR_norm_le _ (addState_small x y k)) (norm_nonneg _) zero_le_one
        _ = 9 := one_mul 9
    · exact addE_identity x y
  rw [h, ← mul_assoc, ← mul_pow, mul_comm twistC, shrink_mul_twistC, one_pow, one_mul]

/-- Six floors of twist is `8i` in Mathlib's plane too. -/
theorem twistC_pow_six : twistC ^ 6 = 8 * I := by
  rw [← toC_twist6, twist6_eq]
  apply Complex.ext <;> simp

/-- The same result, said plainly: `8i` times the written sum is `x + y`. -/
theorem addE_correct_8i (x y : Endless) : 8 * I * evalE (addE x y) = evalE x + evalE y := by
  rw [← twistC_pow_six]; exact addE_correct x y

/-! ## 5. Piece 2 in one statement -/

/-- **Piece 2 of the proof that runs.**

* every endless address of mirror digits names exactly one point of Mathlib's plane
  (the reading settles),
* every point of the unit disk has such an address,
* the top-floor-first adder writes the sum one floor at a time, never looking ahead,
  holding one of only 85 leftovers, and lands exactly on Mathlib's sum. -/
theorem piece_two :
    (∀ x : Endless, Tendsto (partialE x) atTop (𝓝 (evalE x))) ∧
    (∀ z : ℂ, ‖z‖ ≤ 1 → ∃ x : Endless, evalE x = z) ∧
    (∀ x y : Endless, 8 * I * evalE (addE x y) = evalE x + evalE y) ∧
    (∀ (x y : Endless) (k : ℕ), InR (addState x y k)) :=
  ⟨tendsto_partialE, fun z hz => ⟨_, every_disk_point_has_address z hz⟩, addE_correct_8i,
    addState_small⟩

end Building
