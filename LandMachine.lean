import FullMachine

/-!
# Landing (plain Lean, no math library)

The model: "landing is climbing in reverse … it picks one [choice] per floor, like a chain
of coin flips, and the spot it lands on is just the choices it made. The coin flips are
the one outside ingredient."

Here the coin is handed in from outside (a rule giving one flip per floor), and on each
finer floor the flip picks the plain digit 0 or 1. The odds of the flips are left to the
outside, as in the model, where how the coin flips get their odds is an open question.

Checked here: **the spot it lands on is just the choices it made**. After `n` floors, no
two different chains of flips land on the same spot, so the `2^n` chains land on `2^n`
different spots. (How quickly the landing point is pinned down is in `BuildingLand.lean`.)
-/

namespace Building

/-- A coin handed in from outside: one flip per floor. -/
abbrev Coin := Nat → Bool

/-- Land by coin flips: on each finer floor the flip picks 0 or 1. -/
def land (coin : Coin) : Endless := fun n => MDigit.ofBool (coin n)

/-! ## The spot it lands on is just the choices it made -/

/-- Every plain address is its tidy form with some zeros on the coarsest floors. -/
theorem trim_append (ds : List Bool) : ∃ k, ds = trim ds ++ List.replicate k false := by
  induction ds with
  | nil => exact ⟨0, rfl⟩
  | cons d ds ih =>
    obtain ⟨k, hk⟩ := ih
    cases d with
    | false =>
      cases h : trim ds with
      | nil =>
        refine ⟨k + 1, ?_⟩
        simp only [trim, h]
        rw [h] at hk
        simp only [List.nil_append] at hk
        rw [hk]
        simp [List.replicate_succ]
      | cons t ts =>
        refine ⟨k, ?_⟩
        simp only [trim, h]
        rw [h] at hk
        rw [hk]
        simp
    | true =>
      refine ⟨k, ?_⟩
      simp only [trim]
      exact congrArg (List.cons true) hk

/-- Two plain addresses of the same length naming the same spot are the same. -/
theorem eq_of_value_eq_of_length_eq (ds es : List Bool) (hv : value ds = value es)
    (hl : ds.length = es.length) : ds = es := by
  have ht := trim_eq_of_value_eq ds es hv
  obtain ⟨k, hk⟩ := trim_append ds
  obtain ⟨k', hk'⟩ := trim_append es
  have hkk : k = k' := by
    have h1 := congrArg List.length hk
    have h2 := congrArg List.length hk'
    simp only [List.length_append, List.length_replicate] at h1 h2
    rw [ht] at h1
    omega
  rw [hk, hk', ht, hkk]

/-- The first `n` flips as a plain address read finest floor first (the order the
landed spot on floor `n` is read in). -/
def chain (coin : Coin) : Nat → List Bool
  | 0 => []
  | n + 1 => coin n :: chain coin n

theorem horner_land (coin : Coin) (n : Nat) : horner (land coin) n = value (chain coin n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [horner, chain, value_cons, ih, land]
    have : (MDigit.ofBool (coin n)).toSpot = dval (coin n) := by
      cases coin n <;> rfl
    rw [this, Spot.add_comm]

theorem chain_length (coin : Coin) (n : Nat) : (chain coin n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [chain, ih]

theorem chain_eq_iff (coin coin' : Coin) (n : Nat) :
    chain coin n = chain coin' n ↔ ∀ k < n, coin k = coin' k := by
  induction n with
  | zero => simp [chain]
  | succ n ih =>
    simp only [chain, List.cons.injEq, ih]
    constructor
    · rintro ⟨h1, h2⟩ k hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | hk
      · exact h2 k hk
      · subst hk; exact h1
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun k hk => h k (Nat.lt_succ_of_lt hk)⟩

/-- **The spot it lands on is just the choices it made**: two chains of `n` flips that land
on the same spot on floor `n` made exactly the same choices. -/
theorem land_spot_determines_flips (coin coin' : Coin) (n : Nat)
    (h : horner (land coin) n = horner (land coin') n) : ∀ k < n, coin k = coin' k := by
  rw [horner_land, horner_land] at h
  have := eq_of_value_eq_of_length_eq _ _ h (by rw [chain_length, chain_length])
  exact (chain_eq_iff coin coin' n).mp this

end Building
