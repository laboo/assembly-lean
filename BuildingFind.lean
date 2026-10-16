import BuildingFlip
import FindMachine

/-!
# The Building, piece 6: the address finder

Everyday-language summary (for the author):

* A point is handed to the machine as approximations: asked for precision `m`, a rule
  answers with a whole-number spot on a halving grid within `1 / 2^m` of the point.
* The finder climbs one floor at a time. On each floor it asks for a good enough
  approximation and applies the multiplier's star digit rule.
* What decides each digit is a leftover that Lean proves always stays inside the
  four-pointed star, even though the finder only ever sees approximations: their small
  error is absorbed by the star's wiggle room.
* So **the endless address it writes names exactly the point**, and with a first step
  that moves any point into the star, **any point of the plane can be handed in and
  run**.
-/

namespace Building

open Complex Filter Topology Finset

/-- `ap` hands over approximations of the point `z`. -/
def IsApprox (ap : Approx) (z : ℂ) : Prop :=
  ∀ m, ‖z - (ap m).1.toC / 2 ^ (ap m).2‖ ≤ 1 / 2 ^ m

section Finder

variable (ap : Approx) (z : ℂ)

/-- The approximation the finder asks for on floor `k`. -/
noncomputable def zt (k : ℕ) : ℂ := (ap (findPrec k)).1.toC / 2 ^ (ap (findPrec k)).2

/-- The true leftover after `k` floors: what's left of the point, magnified to floor `k`. -/
noncomputable def rF (k : ℕ) : ℂ := twistC ^ k * (z - partialE (findE ap) k)

/-- What the finder sees on floor `k` (worked out from the approximation). -/
noncomputable def VF (k : ℕ) : ℂ := twistC ^ (k + 1) * (zt ap k - partialE (findE ap) k)

/-- The error in what it sees. -/
noncomputable def δF (k : ℕ) : ℂ := VF ap k - twistC * rF ap z k

/-- The leftover as the finder sees it ("shadow" leftover). -/
noncomputable def sh : ℕ → ℂ
  | 0 => z
  | k + 1 => VF ap k - (findE ap k).toSpot.toC

end Finder

theorem norm_twistC_le_two : ‖twistC‖ ≤ 2 := by
  nlinarith [norm_twistC_sq, norm_nonneg twistC]

theorem δF_eq (ap : Approx) (z : ℂ) (k : ℕ) :
    δF ap z k = twistC ^ (k + 1) * (zt ap k - z) := by
  simp only [δF, VF, rF]; ring

/-- The error is tiny: at most `1/64`. -/
theorem norm_δF (ap : Approx) (z : ℂ) (hap : IsApprox ap z) (k : ℕ) : ‖δF ap z k‖ ≤ 1 / 64 := by
  rw [δF_eq, norm_mul, norm_pow, norm_sub_rev]
  have h1 : ‖z - zt ap k‖ ≤ 1 / 2 ^ (2 * k + 7) := hap (findPrec k)
  have h2 : ‖twistC‖ ^ (k + 1) ≤ 2 ^ (k + 1) :=
    pow_le_pow_left₀ (norm_nonneg _) norm_twistC_le_two _
  have h3 : (2 : ℝ) ^ (k + 1) * (1 / 2 ^ (2 * k + 7)) = 1 / 2 ^ (k + 6) := by
    rw [show 2 * k + 7 = (k + 1) + (k + 6) by ring, pow_add]
    field_simp
    ring
  have h4 : (1 : ℝ) / 2 ^ (k + 6) ≤ 1 / 64 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num), one_mul, one_mul]
    calc (64 : ℝ) = 2 ^ 6 := by norm_num
      _ ≤ 2 ^ (k + 6) := pow_le_pow_right₀ (by norm_num) (by omega)
  calc ‖twistC‖ ^ (k + 1) * ‖z - zt ap k‖ ≤ 2 ^ (k + 1) * (1 / 2 ^ (2 * k + 7)) :=
        mul_le_mul h2 h1 (norm_nonneg _) (by positivity)
    _ = 1 / 2 ^ (k + 6) := h3
    _ ≤ 1 / 64 := h4

theorem rF_zero (ap : Approx) (z : ℂ) : rF ap z 0 = z := by
  simp [rF, partialE]

theorem rF_succ (ap : Approx) (z : ℂ) (k : ℕ) :
    rF ap z (k + 1) = twistC * rF ap z k - (findE ap k).toSpot.toC := by
  have hp := shrink_pow_mul_twistC_pow (k + 1)
  simp only [rF]
  rw [partialE_succ, term]
  linear_combination (-(findE ap k).toSpot.toC) * hp

theorem sh_succ (ap : Approx) (z : ℂ) (k : ℕ) :
    sh ap z (k + 1) = rF ap z (k + 1) + δF ap z k := by
  simp only [sh, rF_succ, δF]; ring

/-- The nudge between what the finder sees and the turned shadow leftover is small. -/
theorem nudge_find (ap : Approx) (z : ℂ) (hap : IsApprox ap z) (k : ℕ) :
    ‖VF ap k - twistC * sh ap z k‖ ≤ 3 / 64 := by
  cases k with
  | zero =>
    have : VF ap 0 - twistC * sh ap z 0 = δF ap z 0 := by
      simp only [sh, δF, rF_zero]
    rw [this]; linarith [norm_δF ap z hap 0]
  | succ k =>
    have : VF ap (k + 1) - twistC * sh ap z (k + 1) = δF ap z (k + 1) - twistC * δF ap z k := by
      rw [sh_succ]; simp only [δF]; ring
    rw [this]
    calc ‖δF ap z (k + 1) - twistC * δF ap z k‖
        ≤ ‖δF ap z (k + 1)‖ + ‖twistC * δF ap z k‖ := norm_sub_le _ _
      _ = ‖δF ap z (k + 1)‖ + ‖twistC‖ * ‖δF ap z k‖ := by rw [norm_mul]
      _ ≤ 1 / 64 + 2 * (1 / 64) := by
          gcongr
          · exact norm_δF ap z hap (k + 1)
          · exact norm_twistC_le_two
          · exact norm_δF ap z hap k
      _ = 3 / 64 := by norm_num

theorem toC_two_pow (d : ℕ) : (⟨(2 : ℤ) ^ d, 0⟩ : Spot).toC = 2 ^ d := by
  induction d with
  | zero => apply Complex.ext <;> simp
  | succ d ih =>
    have h : (⟨(2 : ℤ) ^ (d + 1), 0⟩ : Spot) = ⟨2, 0⟩ * ⟨(2 : ℤ) ^ d, 0⟩ := by
      ext <;> simp [pow_succ] <;> ring
    rw [h, Spot.toC_mul, ih, pow_succ, mul_comm]
    congr 1
    apply Complex.ext <;> simp

/-- The finder's whole-number picture is exactly what it sees, `VF`. -/
theorem toC_findNum (ap : Approx) (k : ℕ) :
    (findNum ap k (findP ap k)).toC = 2 ^ (ap (findPrec k)).2 * VF ap k := by
  simp only [findNum, toC_sub, Spot.toC_mul, toC_spow, toC_b', toC_two_pow, findP_eq_horner,
    toC_horner, VF, zt]
  have h2 : (2 : ℂ) ^ (ap (findPrec k)).2 ≠ 0 := pow_ne_zero _ two_ne_zero
  field_simp
  ring

/-- The digit the finder writes on floor `k` is the star rule applied to what it sees. -/
theorem findE_eq_rule (ap : Approx) (k : ℕ) :
    findE ap k = ruleR (VF ap k).re (VF ap k).im := by
  have hv := toC_findNum ap k
  set N := (ap (findPrec k)).2
  have hs : (2 : ℂ) ^ N = ((2 ^ N : ℝ) : ℂ) := by push_cast; rfl
  have hre := congrArg Complex.re hv
  have him := congrArg Complex.im hv
  rw [hs, Complex.re_ofReal_mul] at hre
  rw [hs, Complex.im_ofReal_mul] at him
  simp only [Spot.toC_re, Spot.toC_im] at hre him
  have hpos : (0 : ℝ) < 2 ^ N := by positivity
  have e1 : (VF ap k).re = ((findNum ap k (findP ap k)).re : ℝ) / 2 ^ N := by
    rw [hre]; field_simp
  have e2 : (VF ap k).im = ((findNum ap k (findP ap k)).im : ℝ) / 2 ^ N := by
    rw [him]; field_simp
  rw [e1, e2, ← starRule_eq]
  rfl

/-- **The finder's leftover, as it sees it, always stays inside the star.** -/
theorem sh_in_star (ap : Approx) (z : ℂ) (hap : IsApprox ap z) (hz : InStar z) (k : ℕ) :
    InStar (sh ap z k) := by
  induction k with
  | zero => exact hz
  | succ k ih =>
    have hν := nudge_find ap z hap k
    set ν := VF ap k - twistC * sh ap z k with hνdef
    have hV : VF ap k = twistC * sh ap z k + ν := by rw [hνdef]; ring
    have hsh : sh ap z (k + 1) = VF ap k - (findE ap k).toSpot.toC := rfl
    rw [hsh, findE_eq_rule, hV]
    exact star_cover _ _ ih ((Complex.abs_re_le_norm ν).trans (by linarith))
      ((Complex.abs_im_le_norm ν).trans (by linarith))

theorem rF_bound (ap : Approx) (z : ℂ) (hap : IsApprox ap z) (hz : InStar z) (k : ℕ) :
    ‖rF ap z k‖ ≤ 2 := by
  cases k with
  | zero => rw [rF_zero]; linarith [InStar_norm_le z hz]
  | succ k =>
    have h := sh_succ ap z k
    have : rF ap z (k + 1) = sh ap z (k + 1) - δF ap z k := by rw [h]; ring
    rw [this]
    calc ‖sh ap z (k + 1) - δF ap z k‖ ≤ ‖sh ap z (k + 1)‖ + ‖δF ap z k‖ := norm_sub_le _ _
      _ ≤ 4 / 3 + 1 / 64 := by
          gcongr
          · exact InStar_norm_le _ (sh_in_star ap z hap hz (k + 1))
          · exact norm_δF ap z hap k
      _ ≤ 2 := by norm_num

/-- **The finder's endless address names exactly the point** (for a point inside the star). -/
theorem findE_correct (ap : Approx) (z : ℂ) (hap : IsApprox ap z) (hz : InStar z) :
    evalE (findE ap) = z := by
  apply evalE_eq_of_bounded _ (fun _ => z) z tendsto_const_nhds (rF ap z) 2
    (rF_bound ap z hap hz)
  intro k
  have hp := shrink_pow_mul_twistC_pow k
  simp only [rF]
  linear_combination (-(z - partialE (findE ap) k)) * hp

/-! ## Any point of the plane -/

theorem norm_shrink_le_one : ‖shrink‖ ≤ 1 := norm_shrink_lt_one.le

theorem shiftApprox_spec (ap : Approx) (z : ℂ) (hap : IsApprox ap z) (K : ℕ) :
    IsApprox (shiftApprox ap K) (shrink ^ K * z) := by
  intro m
  simp only [shiftApprox, Spot.toC_mul, toC_spow, cbar_toC]
  have h2 : (2 : ℂ) ^ (ap m).2 ≠ 0 := pow_ne_zero _ two_ne_zero
  have h2K : (2 : ℂ) ^ K ≠ 0 := pow_ne_zero _ two_ne_zero
  have : shrink ^ K * z - (2 * shrink) ^ K * (ap m).1.toC / 2 ^ ((ap m).2 + K) =
      shrink ^ K * (z - (ap m).1.toC / 2 ^ (ap m).2) := by
    rw [mul_pow, pow_add]; field_simp
  rw [this, norm_mul, norm_pow]
  calc ‖shrink‖ ^ K * ‖z - (ap m).1.toC / 2 ^ (ap m).2‖ ≤ 1 * (1 / 2 ^ m) :=
        mul_le_mul (pow_le_one₀ (norm_nonneg _) norm_shrink_le_one) (hap m) (norm_nonneg _)
          zero_le_one
    _ = 1 / 2 ^ m := one_mul _

/-- After the first step, the point sits well inside the star. -/
theorem shifted_in_star (ap : Approx) (z : ℂ) (hap : IsApprox ap z) :
    InStar (shrink ^ findShift ap * z) := by
  set G := (ap 0).1
  set d := (ap 0).2
  set M : ℕ := G.re.natAbs + G.im.natAbs + 2 ^ d
  set L := (3 * M).log2 + 1
  have hK : findShift ap = 2 * L := rfl
  -- a rough size of the point
  have hd : (1 : ℝ) ≤ 2 ^ d := one_le_pow₀ (by norm_num)
  have h0 := hap 0
  simp only [pow_zero, div_one] at h0
  have hzt : ‖G.toC / 2 ^ d‖ ≤ ((G.re.natAbs + G.im.natAbs : ℕ) : ℝ) / 2 ^ d := by
    rw [norm_div, norm_pow, Complex.norm_two]
    gcongr
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    simp only [Spot.toC_re, Spot.toC_im, Nat.cast_add, Nat.cast_natAbs, Int.cast_abs, le_refl]
  have hz : ‖z‖ ≤ (M : ℝ) := by
    have : ‖z‖ ≤ ‖G.toC / 2 ^ d‖ + 1 := by
      have := norm_le_norm_add_norm_sub' z (G.toC / 2 ^ d)
      linarith
    have hM : ((G.re.natAbs + G.im.natAbs : ℕ) : ℝ) / 2 ^ d + 1 ≤ M := by
      have hM' : (M : ℝ) = ((G.re.natAbs + G.im.natAbs : ℕ) : ℝ) + 2 ^ d := by
        simp only [M]; push_cast; ring
      rw [hM']
      have hnn : (0 : ℝ) ≤ ((G.re.natAbs + G.im.natAbs : ℕ) : ℝ) := by positivity
      have : ((G.re.natAbs + G.im.natAbs : ℕ) : ℝ) / 2 ^ d ≤ ((G.re.natAbs + G.im.natAbs : ℕ) : ℝ) :=
        div_le_self hnn hd
      linarith
    linarith
  -- the shrink of `2L` floors halves sizes `L` times
  have hshr : ‖shrink ^ (2 * L)‖ = 1 / 2 ^ L := by
    rw [norm_pow, pow_mul, norm_shrink_sq, one_div, inv_pow, one_div]
  have hL : (3 * M : ℝ) < 2 ^ L := by exact_mod_cast Nat.lt_log2_self
  have hsmall : ‖shrink ^ findShift ap * z‖ ≤ 1 / 3 := by
    rw [hK, norm_mul, hshr]
    have h2L : (0 : ℝ) < 2 ^ L := by positivity
    rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ h2L (by norm_num)]
    linarith
  have hre := (Complex.abs_re_le_norm (shrink ^ findShift ap * z)).trans hsmall
  have him := (Complex.abs_im_le_norm (shrink ^ findShift ap * z)).trans hsmall
  constructor <;> linarith [abs_nonneg (shrink ^ findShift ap * z).re,
    abs_nonneg (shrink ^ findShift ap * z).im]

/-- **Hand in any point of the plane, as approximations, and the full address the machine
writes names exactly that point.** -/
theorem findFull_correct (ap : Approx) (z : ℂ) (hap : IsApprox ap z) :
    fullValue (findFull ap) = z := by
  simp only [findFull, lookupOr_memoArr]
  rw [fullValue_lift,
    findE_correct _ _ (shiftApprox_spec ap z hap _) (shifted_in_star ap z hap)]
  rw [← mul_assoc, ← mul_pow, mul_comm twistC, shrink_mul_twistC, one_pow, one_mul]

/-- **Piece 6 in one statement.** The address finder runs on approximations, and what it
writes names exactly the point, anywhere in the plane. -/
theorem piece_six : ∀ (ap : Approx) (z : ℂ), IsApprox ap z → fullValue (findFull ap) = z :=
  findFull_correct

end Building
