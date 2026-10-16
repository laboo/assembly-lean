import StreamMachine

/-!
# The multiplying machine (plain Lean, no math library)

Multiplies two endless addresses top floor first, writing one floor of the product
for each floor it reads, never looking ahead. Unlike the adder it has to remember
everything read so far (the way long multiplication on paper does), but the part
that decides each digit, the leftover, always stays inside a small four-pointed star:
`4·|east| − |north| ≤ 2` and `4·|north| − |east| ≤ 2`, whose points reach `2/3` of a
step along the diagonals.

The product comes out written twelve floors higher: `−64 ×` the written product is the
true product. The proof that it lands on Mathlib's product is in `BuildingMul.lean`.
-/

namespace Building

/-- How many floors higher the product is written. -/
def mulShift : Nat := 12

/-- `−1 − i`: twice one floor's shrink. -/
def cbar : Spot := ⟨-1, -1⟩

/-- Powers of a spot. -/
def spow (z : Spot) : Nat → Spot
  | 0 => 1
  | n + 1 => z * spow z n

/-- The first `k` floors of an endless address, read as one whole-number spot
(the same Horner reading as the ground floor). -/
def horner (x : Endless) : Nat → Spot
  | 0 => 0
  | k + 1 => b * horner x k + (x k).toSpot

/-- The digit rule. The point to settle is `G / 2^N`. Look at its bigger direction:
if the point is already inside the star, write 0; otherwise write the step
(1, −1, i or −i) pointing that way. Everything is whole-number comparison. -/
def starRule (G : Spot) (N : Nat) : MDigit :=
  let X : Int := G.re.natAbs
  let Y : Int := G.im.natAbs
  let T : Int := 2 * 2 ^ N
  if Y ≤ X then
    (if 4 * X - Y ≤ T then .zero else if 0 < G.re then .one else .negOne)
  else
    (if 4 * Y - X ≤ T then .zero else if 0 < G.im then .up else .down)

/-- The point to settle on floor `k`, scaled up by `2^(mulShift + k + 1)` so it is a
whole-number spot: everything read so far, minus the product written so far. -/
def vint (x y : Endless) (k : Nat) (P : Spot) : Spot :=
  spow cbar (mulShift + k + 1) *
    (horner x (k + 1) * horner y (k + 1) - spow b (mulShift + k + 2) * P)

/-- The product written so far, read as a whole-number spot. -/
def mulP (x y : Endless) : Nat → Spot
  | 0 => 0
  | k + 1 => b * mulP x y k + (starRule (vint x y k (mulP x y k)) (mulShift + k + 1)).toSpot

/-- The product, as an endless address, one floor at a time (written twelve floors higher). -/
def mulE (x y : Endless) : Endless :=
  fun k => starRule (vint x y k (mulP x y k)) (mulShift + k + 1)

theorem mulP_eq_horner (x y : Endless) (k : Nat) : mulP x y k = horner (mulE x y) k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [mulP, horner, ih, mulE]

theorem horner_local (x x' : Endless) (k : Nat) (h : ∀ n, n < k → x n = x' n) :
    horner x k = horner x' k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [horner]
    rw [ih (fun n hn => h n (Nat.lt_succ_of_lt hn)), h k (Nat.lt_succ_self k)]

/-- **Each written digit of the product depends only on the floors read so far.** -/
theorem mulE_local (x y x' y' : Endless) (k : Nat)
    (hx : ∀ n ≤ k, x n = x' n) (hy : ∀ n ≤ k, y n = y' n) : mulE x y k = mulE x' y' k := by
  have hP : ∀ m ≤ k, mulP x y m = mulP x' y' m := by
    intro m hm
    induction m with
    | zero => rfl
    | succ m ih =>
      simp only [mulP, vint]
      rw [ih (by omega),
        horner_local x x' (m + 1) (fun n hn => hx n (by omega)),
        horner_local y y' (m + 1) (fun n hn => hy n (by omega))]
  simp only [mulE, vint]
  rw [hP k (Nat.le_refl k),
    horner_local x x' (k + 1) (fun n hn => hx n (by omega)),
    horner_local y y' (k + 1) (fun n hn => hy n (by omega))]

end Building
