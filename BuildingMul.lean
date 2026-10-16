import BuildingStream
import MulMachine

/-!
# The Building, piece 3: multiplying endless addresses

Everyday-language summary (for the author):

* The multiplier in `MulMachine.lean` climbs: on each finer floor it reads one digit of
  each endless address and writes one digit of the product, never looking further up.
* What decides each digit is a **leftover**: everything read so far, minus the product
  written so far, magnified to the current floor. Lean checks that the leftover always
  stays inside a small **four-pointed star** (`4·|east| − |north| ≤ 2` and
  `4·|north| − |east| ≤ 2`), because the five mirror digits cover the star, turned and
  grown by one floor, with room to spare (the Prague group's "wiggle room", here with
  an explicit star instead of a picture).
* Because the leftover stays small while its floor gets finer and finer, the written
  product homes in on the true product: **−64 × the written product is exactly
  Mathlib's `x · y`** (moving the written product twelve floors down multiplies it by
  −64).
-/

namespace Building

open Complex Filter Topology Finset

/-! ## 1. The star and the digit rule, in Mathlib's plane -/

/-- The four-pointed star. -/
def InStar (z : ℂ) : Prop := 4 * |z.re| - |z.im| ≤ 2 ∧ 4 * |z.im| - |z.re| ≤ 2

/-- The digit rule on a point given by its east and north parts. -/
noncomputable def ruleR (x y : ℝ) : MDigit :=
  if |y| ≤ |x| then
    (if 4 * |x| - |y| ≤ 2 then .zero else if 0 < x then .one else .negOne)
  else
    (if 4 * |y| - |x| ≤ 2 then .zero else if 0 < y then .up else .down)

/-- The star test on east and north parts. -/
def InStarR (x y : ℝ) : Prop := 4 * |x| - |y| ≤ 2 ∧ 4 * |y| - |x| ≤ 2

/-! The four directions of the wiggle room. In each, `a` and `c` are the east and north
parts of a point of the star, and `dx`, `dy` the nudge. -/

theorem cover_east (a c dx dy : ℝ) (h1 : 4 * |a| - |c| ≤ 2) (h2 : 4 * |c| - |a| ≤ 2)
    (hdx : |dx| ≤ 5 / 64) (hdy : |dy| ≤ 5 / 64)
    (_hA : |a - c + dy| ≤ |-a - c + dx|) (hB : 2 < 4 * |-a - c + dx| - |a - c + dy|)
    (hpos : 0 < -a - c + dx) :
    InStarR (-a - c + dx - 1) (a - c + dy) := by
  obtain ⟨hdx1, hdx2⟩ := abs_le.mp hdx
  obtain ⟨hdy1, hdy2⟩ := abs_le.mp hdy
  rw [abs_of_pos hpos] at _hA hB
  unfold InStarR
  rcases abs_cases a with ⟨ea, sa⟩ | ⟨ea, sa⟩ <;>
  rcases abs_cases c with ⟨ec, sc⟩ | ⟨ec, sc⟩ <;>
  rcases abs_cases (a - c + dy) with ⟨ey, sy⟩ | ⟨ey, sy⟩ <;>
  rcases abs_cases (-a - c + dx - 1) with ⟨e1, s1⟩ | ⟨e1, s1⟩ <;>
  constructor <;> linarith

theorem cover_west (a c dx dy : ℝ) (h1 : 4 * |a| - |c| ≤ 2) (h2 : 4 * |c| - |a| ≤ 2)
    (hdx : |dx| ≤ 5 / 64) (hdy : |dy| ≤ 5 / 64)
    (_hA : |a - c + dy| ≤ |-a - c + dx|) (hB : 2 < 4 * |-a - c + dx| - |a - c + dy|)
    (hneg : -a - c + dx < 0) :
    InStarR (-a - c + dx + 1) (a - c + dy) := by
  obtain ⟨hdx1, hdx2⟩ := abs_le.mp hdx
  obtain ⟨hdy1, hdy2⟩ := abs_le.mp hdy
  rw [abs_of_neg hneg] at _hA hB
  unfold InStarR
  rcases abs_cases a with ⟨ea, sa⟩ | ⟨ea, sa⟩ <;>
  rcases abs_cases c with ⟨ec, sc⟩ | ⟨ec, sc⟩ <;>
  rcases abs_cases (a - c + dy) with ⟨ey, sy⟩ | ⟨ey, sy⟩ <;>
  rcases abs_cases (-a - c + dx + 1) with ⟨e1, s1⟩ | ⟨e1, s1⟩ <;>
  constructor <;> linarith

theorem cover_north (a c dx dy : ℝ) (h1 : 4 * |a| - |c| ≤ 2) (h2 : 4 * |c| - |a| ≤ 2)
    (hdx : |dx| ≤ 5 / 64) (hdy : |dy| ≤ 5 / 64)
    (hA : |-a - c + dx| < |a - c + dy|) (hB : 2 < 4 * |a - c + dy| - |-a - c + dx|)
    (hpos : 0 < a - c + dy) :
    InStarR (-a - c + dx) (a - c + dy - 1) := by
  obtain ⟨hdx1, hdx2⟩ := abs_le.mp hdx
  obtain ⟨hdy1, hdy2⟩ := abs_le.mp hdy
  rw [abs_of_pos hpos] at hA hB
  unfold InStarR
  rcases abs_cases a with ⟨ea, sa⟩ | ⟨ea, sa⟩ <;>
  rcases abs_cases c with ⟨ec, sc⟩ | ⟨ec, sc⟩ <;>
  rcases abs_cases (-a - c + dx) with ⟨ey, sy⟩ | ⟨ey, sy⟩ <;>
  rcases abs_cases (a - c + dy - 1) with ⟨e1, s1⟩ | ⟨e1, s1⟩ <;>
  constructor <;> linarith

theorem cover_south (a c dx dy : ℝ) (h1 : 4 * |a| - |c| ≤ 2) (h2 : 4 * |c| - |a| ≤ 2)
    (hdx : |dx| ≤ 5 / 64) (hdy : |dy| ≤ 5 / 64)
    (hA : |-a - c + dx| < |a - c + dy|) (hB : 2 < 4 * |a - c + dy| - |-a - c + dx|)
    (hneg : a - c + dy < 0) :
    InStarR (-a - c + dx) (a - c + dy + 1) := by
  obtain ⟨hdx1, hdx2⟩ := abs_le.mp hdx
  obtain ⟨hdy1, hdy2⟩ := abs_le.mp hdy
  rw [abs_of_neg hneg] at hA hB
  unfold InStarR
  rcases abs_cases a with ⟨ea, sa⟩ | ⟨ea, sa⟩ <;>
  rcases abs_cases c with ⟨ec, sc⟩ | ⟨ec, sc⟩ <;>
  rcases abs_cases (-a - c + dx) with ⟨ey, sy⟩ | ⟨ey, sy⟩ <;>
  rcases abs_cases (a - c + dy + 1) with ⟨e1, s1⟩ | ⟨e1, s1⟩ <;>
  constructor <;> linarith

/-- **The wiggle room.** Turn and grow a point of the star by one floor, nudge it by up
to `5/64` in each direction, and the digit rule brings it back inside the star. -/
theorem star_cover (r δ : ℂ) (hr : InStar r) (hδr : |δ.re| ≤ 5 / 64) (hδi : |δ.im| ≤ 5 / 64) :
    InStar (twistC * r + δ - (ruleR (twistC * r + δ).re (twistC * r + δ).im).toSpot.toC) := by
  have hwr : (twistC * r + δ).re = -r.re - r.im + δ.re := by simp [twistC]
  have hwi : (twistC * r + δ).im = r.re - r.im + δ.im := by simp [twistC]; ring
  obtain ⟨h1, h2⟩ := hr
  have key : ∀ d : MDigit, InStar (twistC * r + δ - d.toSpot.toC) ↔
      InStarR (-r.re - r.im + δ.re - (d.toSpot.re : ℝ)) (r.re - r.im + δ.im - (d.toSpot.im : ℝ)) := by
    intro d; simp only [InStar, InStarR, sub_re, sub_im, hwr, hwi, Spot.toC_re, Spot.toC_im]
  rw [key, hwr, hwi]
  unfold ruleR
  split_ifs with hA hB hC hD hE
  · -- write 0: the point is already in the star
    simp only [MDigit.toSpot, Int.cast_zero, sub_zero]
    exact ⟨hB, by linarith⟩
  · -- write 1
    have := cover_east _ _ _ _ h1 h2 hδr hδi hA (by linarith) hC
    simpa [MDigit.toSpot] using this
  · -- write −1
    have := cover_west _ _ _ _ h1 h2 hδr hδi hA (by linarith)
      (lt_of_le_of_ne (not_lt.mp hC) (by
        intro h0; rw [h0, abs_zero] at hA hB; linarith [abs_nonneg (r.re - r.im + δ.im)]))
    simpa [MDigit.toSpot] using this
  · -- write 0: the point is already in the star
    simp only [MDigit.toSpot, Int.cast_zero, sub_zero]
    exact ⟨by linarith [not_le.mp hA], hD⟩
  · -- write i
    have := cover_north _ _ _ _ h1 h2 hδr hδi (not_le.mp hA) (by linarith) hE
    simpa [MDigit.toSpot] using this
  · -- write −i
    have := cover_south _ _ _ _ h1 h2 hδr hδi (not_le.mp hA) (by linarith)
      (lt_of_le_of_ne (not_lt.mp hE) (by
        intro h0; rw [h0, abs_zero] at hD; linarith [abs_nonneg (-r.re - r.im + δ.re)]))
    simpa [MDigit.toSpot] using this

/-- Inside the star, a point is within `4/3` of zero. -/
theorem InStar_norm_le (z : ℂ) (h : InStar z) : ‖z‖ ≤ 4 / 3 := by
  obtain ⟨h1, h2⟩ := h
  refine (Complex.norm_le_abs_re_add_abs_im z).trans ?_
  linarith

/-! ## 2. Sizes: one floor's shrink, and how big a partial reading can be -/

theorem norm_shrink_sq : ‖shrink‖ ^ 2 = 1 / 2 := by
  rw [shrink, norm_inv, inv_pow, norm_twistC_sq]; norm_num

theorem norm_shrink_le : ‖shrink‖ ≤ 5 / 7 := by
  nlinarith [norm_shrink_sq, norm_nonneg shrink]

theorem norm_shrink_pow_twelve : ‖shrink‖ ^ 12 = 1 / 64 := by
  rw [show 12 = 2 * 6 by rfl, pow_mul, norm_shrink_sq]; norm_num

theorem norm_term_le' (x : Endless) (n : ℕ) : ‖term x n‖ ≤ ‖shrink‖ ^ (n + 1) := by
  rw [term, norm_mul, norm_pow]
  calc ‖(x n).toSpot.toC‖ * ‖shrink‖ ^ (n + 1) ≤ 1 * ‖shrink‖ ^ (n + 1) := by
        gcongr; exact MDigit.norm_toC_le _
    _ = ‖shrink‖ ^ (n + 1) := one_mul _

/-- Reading any number of floors of an endless address stays within `5/2` of zero. -/
theorem norm_partialE_le (x : Endless) (k : ℕ) : ‖partialE x k‖ ≤ 5 / 2 := by
  set q := ‖shrink‖
  have hq0 : 0 ≤ q := norm_nonneg _
  have hq1 : q ≤ 5 / 7 := norm_shrink_le
  have key : ∀ k, ‖partialE x k‖ ≤ 5 / 2 - 5 / 2 * q ^ k := by
    intro k
    induction k with
    | zero => simp [partialE]
    | succ k ih =>
      rw [partialE_succ]
      have ht := norm_term_le' x k
      have hpk : 0 ≤ q ^ k := pow_nonneg hq0 k
      calc ‖partialE x k + term x k‖ ≤ ‖partialE x k‖ + ‖term x k‖ := norm_add_le _ _
        _ ≤ 5 / 2 - 5 / 2 * q ^ k + q ^ (k + 1) := by linarith
        _ ≤ 5 / 2 - 5 / 2 * q ^ (k + 1) := by
          rw [pow_succ]
          nlinarith [mul_nonneg hpk (by linarith : (0 : ℝ) ≤ 5 / 2 - 7 / 2 * q)]
  have := key k
  have : 0 ≤ q ^ k := pow_nonneg hq0 k
  linarith

/-! ## 3. Linking the machine's whole numbers to Mathlib's plane -/

theorem toC_spow (z : Spot) (n : ℕ) : (spow z n).toC = z.toC ^ n := by
  induction n with
  | zero => apply Complex.ext <;> simp [spow]
  | succ n ih => rw [spow, Spot.toC_mul, ih, pow_succ, mul_comm]

theorem toC_sub (z w : Spot) : (z - w).toC = z.toC - w.toC := by
  apply Complex.ext <;> simp

theorem shrink_pow_mul_twistC_pow (n : ℕ) : shrink ^ n * twistC ^ n = 1 := by
  rw [← mul_pow, shrink_mul_twistC, one_pow]

/-- Reading the first `k` floors as one whole-number spot is the partial reading,
magnified `k` floors. -/
theorem toC_horner (x : Endless) (k : ℕ) : (horner x k).toC = twistC ^ k * partialE x k := by
  induction k with
  | zero => simp [horner, partialE, toC_zero]
  | succ k ih =>
    rw [horner, Spot.toC_add, Spot.toC_mul, toC_b', ih, partialE_succ, term]
    have hp := shrink_pow_mul_twistC_pow (k + 1)
    linear_combination (-(x k).toSpot.toC) * hp

theorem cbar_toC : cbar.toC = 2 * shrink := by
  rw [shrink, twistC]
  have h : (-1 + I : ℂ) ≠ 0 := twistC_ne_zero
  field_simp
  apply Complex.ext <;> simp [cbar] <;> norm_num

/-- The leftover, in Mathlib's plane: what was read so far (scaled down twelve floors)
minus what was written so far, magnified to floor `k`. -/
noncomputable def rC (x y : Endless) (k : ℕ) : ℂ :=
  twistC ^ k * (shrink ^ 12 * partialE x k * partialE y k - partialE (mulE x y) k)

/-- The point the machine settles on floor `k`, in Mathlib's plane. -/
noncomputable def VC (x y : Endless) (k : ℕ) : ℂ :=
  twistC * rC x y k +
    shrink ^ 12 * ((x k).toSpot.toC * partialE y (k + 1) + (y k).toSpot.toC * partialE x k)

theorem rC_succ (x y : Endless) (k : ℕ) :
    rC x y (k + 1) = VC x y k - (mulE x y k).toSpot.toC := by
  have hp := shrink_pow_mul_twistC_pow (k + 1)
  have hY1 : partialE y (k + 1) = partialE y k + (y k).toSpot.toC * shrink ^ (k + 1) := by
    rw [partialE_succ, term]
  simp only [rC, VC]
  rw [partialE_succ x, partialE_succ (mulE x y), term, term]
  set c := shrink
  set β := twistC
  set X := partialE x k
  set Y := partialE y k
  set Y1 := partialE y (k + 1)
  set P := partialE (mulE x y) k
  set xd := (x k).toSpot.toC
  set yd := (y k).toSpot.toC
  set pd := (mulE x y k).toSpot.toC
  linear_combination (c ^ 12 * xd * Y1 - pd + c ^ 12 * yd * X) * hp +
    (β ^ (k + 1) * c ^ 12 * X) * hY1

theorem toC_vint (x y : Endless) (k : ℕ) :
    (vint x y k (mulP x y k)).toC = 2 ^ (mulShift + k + 1) * VC x y k := by
  have hp := shrink_pow_mul_twistC_pow (k + 1)
  have h12 := shrink_pow_mul_twistC_pow 12
  have hX1 : partialE x (k + 1) = partialE x k + (x k).toSpot.toC * shrink ^ (k + 1) := by
    rw [partialE_succ, term]
  have hY1 : partialE y (k + 1) = partialE y k + (y k).toSpot.toC * shrink ^ (k + 1) := by
    rw [partialE_succ, term]
  simp only [vint, Spot.toC_mul, toC_sub, toC_spow, cbar_toC, toC_b', toC_horner,
    mulP_eq_horner, VC, rC, mulShift]
  set c := shrink
  set β := twistC
  set X := partialE x k
  set Y := partialE y k
  set X1 := partialE x (k + 1)
  set Y1 := partialE y (k + 1)
  set P := partialE (mulE x y) k
  set xd := (x k).toSpot.toC
  set yd := (y k).toSpot.toC
  rw [mul_pow]
  linear_combination (2 ^ (12 + k + 1) * c ^ 12 * β ^ (k + 1) * X1 * Y1 +
      2 ^ (12 + k + 1) * c ^ 12 * (xd * Y1 + yd * X) -
      2 ^ (12 + k + 1) * β ^ (k + 1) * P * (c ^ 12 * β ^ 12)) * hp +
    (- 2 ^ (12 + k + 1) * β ^ (k + 1) * P) * h12 +
    (2 ^ (12 + k + 1) * c ^ 12 * β ^ (k + 1) * Y1) * hX1 +
    (2 ^ (12 + k + 1) * c ^ 12 * β ^ (k + 1) * X) * hY1

/-- The machine's whole-number digit rule is the digit rule in Mathlib's plane. -/
theorem starRule_eq (G : Spot) (N : ℕ) :
    starRule G N = ruleR ((G.re : ℝ) / 2 ^ N) ((G.im : ℝ) / 2 ^ N) := by
  have hs : (0 : ℝ) < 2 ^ N := by positivity
  have absdiv : ∀ t : ℤ, |(t : ℝ) / 2 ^ N| = |(t : ℝ)| / 2 ^ N := by
    intro t; rw [abs_div, abs_of_pos hs]
  have cast_abs : ∀ t : ℤ, (((t.natAbs : ℤ)) : ℝ) = |(t : ℝ)| := by
    intro t; push_cast; rfl
  unfold starRule ruleR
  simp only [absdiv]
  have e1 : ∀ p q : ℤ, (p.natAbs : ℤ) ≤ q.natAbs ↔ |(p : ℝ)| / 2 ^ N ≤ |(q : ℝ)| / 2 ^ N := by
    intro p q
    rw [div_le_div_iff_of_pos_right hs, ← cast_abs, ← cast_abs]
    exact_mod_cast Iff.rfl
  have e2 : ∀ p q : ℤ, 4 * (p.natAbs : ℤ) - q.natAbs ≤ 2 * 2 ^ N ↔
      4 * (|(p : ℝ)| / 2 ^ N) - |(q : ℝ)| / 2 ^ N ≤ 2 := by
    intro p q
    rw [show 4 * (|(p : ℝ)| / 2 ^ N) - |(q : ℝ)| / 2 ^ N = (4 * |(p : ℝ)| - |(q : ℝ)|) / 2 ^ N
      by ring, div_le_iff₀ hs, ← cast_abs, ← cast_abs]
    exact_mod_cast Iff.rfl
  have e3 : ∀ p : ℤ, 0 < p ↔ 0 < (p : ℝ) / 2 ^ N := by
    intro p
    rw [lt_div_iff₀ hs, zero_mul]
    exact_mod_cast Iff.rfl
  simp only [e1, e2, e3]

/-- The digit the machine writes on floor `k` is the digit rule applied to `VC`. -/
theorem mulE_eq_rule (x y : Endless) (k : ℕ) :
    mulE x y k = ruleR (VC x y k).re (VC x y k).im := by
  have hv := toC_vint x y k
  set N := mulShift + k + 1
  have hs : (2 : ℂ) ^ N = ((2 ^ N : ℝ) : ℂ) := by push_cast; rfl
  have hre := congrArg Complex.re hv
  have him := congrArg Complex.im hv
  rw [hs, Complex.re_ofReal_mul] at hre
  rw [hs, Complex.im_ofReal_mul] at him
  simp only [Spot.toC_re, Spot.toC_im] at hre him
  have hpos : (0 : ℝ) < 2 ^ N := by positivity
  have e1 : (VC x y k).re = ((vint x y k (mulP x y k)).re : ℝ) / 2 ^ N := by
    rw [hre]; field_simp
  have e2 : (VC x y k).im = ((vint x y k (mulP x y k)).im : ℝ) / 2 ^ N := by
    rw [him]; field_simp
  rw [e1, e2, ← starRule_eq]
  rfl

/-! ## 4. The leftover never leaves the star -/

theorem norm_digit_le (d : MDigit) : ‖d.toSpot.toC‖ ≤ 1 := MDigit.norm_toC_le d

/-- The nudge on each floor is at most `5/64` in each direction. -/
theorem nudge_small (x y : Endless) (k : ℕ) :
    ‖shrink ^ 12 * ((x k).toSpot.toC * partialE y (k + 1) + (y k).toSpot.toC * partialE x k)‖
      ≤ 5 / 64 := by
  rw [norm_mul, norm_pow, norm_shrink_pow_twelve]
  have h1 := norm_digit_le (x k)
  have h2 := norm_digit_le (y k)
  have h3 := norm_partialE_le y (k + 1)
  have h4 := norm_partialE_le x k
  have : ‖(x k).toSpot.toC * partialE y (k + 1) + (y k).toSpot.toC * partialE x k‖ ≤ 5 := by
    calc _ ≤ ‖(x k).toSpot.toC * partialE y (k + 1)‖ + ‖(y k).toSpot.toC * partialE x k‖ :=
          norm_add_le _ _
      _ = ‖(x k).toSpot.toC‖ * ‖partialE y (k + 1)‖ + ‖(y k).toSpot.toC‖ * ‖partialE x k‖ := by
          rw [norm_mul, norm_mul]
      _ ≤ 1 * (5 / 2) + 1 * (5 / 2) := by
          gcongr
      _ = 5 := by norm_num
  linarith

/-- **The leftover always stays inside the star.** -/
theorem rC_in_star (x y : Endless) (k : ℕ) : InStar (rC x y k) := by
  induction k with
  | zero =>
    simp only [rC, partialE, range_zero, sum_empty, mul_zero, sub_zero, mul_zero]
    unfold InStar; simp
  | succ k ih =>
    rw [rC_succ, mulE_eq_rule]
    set δ := shrink ^ 12 * ((x k).toSpot.toC * partialE y (k + 1) +
      (y k).toSpot.toC * partialE x k)
    have hδ := nudge_small x y k
    have hVC : VC x y k = twistC * rC x y k + δ := rfl
    rw [hVC]
    exact star_cover _ _ ih ((Complex.abs_re_le_norm δ).trans hδ)
      ((Complex.abs_im_le_norm δ).trans hδ)

/-! ## 5. The multiplier lands on Mathlib's product -/

theorem shrink_pow_twelve : shrink ^ 12 = -1 / 64 := by
  have h2 : shrink ^ 2 = I / 2 := by
    rw [shrink, twistC, inv_pow]
    have : ((-1 + I) ^ 2 : ℂ) = -2 * I := by ring_nf; rw [I_sq]; ring
    rw [this]
    field_simp
    rw [I_sq]
  rw [show 12 = 2 * 6 by rfl, pow_mul, h2, div_pow]
  rw [show (I : ℂ) ^ 6 = (I ^ 2) ^ 3 by ring, I_sq]
  norm_num

/-- **Multiplying two endless addresses, climbing one floor at a time, lands on Mathlib's
product**: the written product, moved twelve floors down, is exactly `x · y`. -/
theorem mulE_correct (x y : Endless) : evalE x * evalE y = -64 * evalE (mulE x y) := by
  have h : evalE (mulE x y) = shrink ^ 12 * (evalE x * evalE y) := by
    apply evalE_eq_of_bounded _ (fun k => shrink ^ 12 * partialE x k * partialE y k)
      (shrink ^ 12 * (evalE x * evalE y))
      (by
        have := ((tendsto_partialE x).mul (tendsto_partialE y)).const_mul (shrink ^ 12)
        simpa [mul_assoc] using this)
      (rC x y) (4 / 3)
    · intro k; exact InStar_norm_le _ (rC_in_star x y k)
    · intro k
      simp only [rC]
      have hp := shrink_pow_mul_twistC_pow k
      linear_combination (-(shrink ^ 12 * partialE x k * partialE y k -
        partialE (mulE x y) k)) * hp
  rw [h, shrink_pow_twelve]
  ring

/-- **Piece 3 in one statement.** The climbing multiplier writes each digit from
the floors read so far, keeps its leftover inside the four-pointed star, and lands
exactly on Mathlib's product. -/
theorem piece_three :
    (∀ x y : Endless, evalE x * evalE y = -64 * evalE (mulE x y)) ∧
    (∀ (x y : Endless) (k : ℕ), InStar (rC x y k)) ∧
    (∀ (x y x' y' : Endless) (k : ℕ), (∀ n ≤ k, x n = x' n) → (∀ n ≤ k, y n = y' n) →
      mulE x y k = mulE x' y' k) :=
  ⟨mulE_correct, rC_in_star, mulE_local⟩

end Building
