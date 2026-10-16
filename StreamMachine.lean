import Building

/-!
# The stream machine (plain Lean, no math library)

The runnable part of piece 2: the five mirror digits, endless addresses handed over
one floor at a time, and the top-floor-first adder with its 85-leftover certificate.
The proof that it lands on the complex plane's sum is in `BuildingStream.lean`.
-/

namespace Building

/-! ## 1. Mirror digits -/

/-- The five mirror digits: 0, 1, −1, i, −i. -/
inductive MDigit
  | zero | one | negOne | up | down
deriving DecidableEq, Repr, Inhabited

namespace MDigit

/-- A mirror digit as a spot. -/
def toSpot : MDigit → Spot
  | zero => ⟨0, 0⟩
  | one => ⟨1, 0⟩
  | negOne => ⟨-1, 0⟩
  | up => ⟨0, 1⟩
  | down => ⟨0, -1⟩

def all : List MDigit := [zero, one, negOne, up, down]

theorem mem_all (d : MDigit) : d ∈ all := by cases d <;> simp [all]

end MDigit

/-- An endless address: the digit on floor `n + 1` below the point, for every `n`. -/
abbrev Endless := Nat → MDigit

/-! ## 4. Adding two endless addresses, top floor first

The machine below reads one floor of each address and writes one floor of the
answer. It keeps a leftover `u`, a whole-number spot. At each floor:
turn the leftover one floor (`b · u`), add the two digits just read, and write the
mirror digit that leaves the smallest leftover, removing that digit's worth
measured six floors up (`b⁶ = 8i`). -/

/-- Six floors of twist: `b⁶ = 8i`. -/
def twist6 : Spot := b * b * b * b * b * b

theorem twist6_eq : twist6 = ⟨0, 8⟩ := by decide

/-- Squared length of a spot, in whole numbers. -/
def nsq (z : Spot) : Int := z.re * z.re + z.im * z.im

/-- The mirror digit that leaves the smallest leftover (ties go to the earlier digit). -/
def nearest (v : Spot) : MDigit :=
  MDigit.all.foldl
    (fun best p => if nsq (v - p.toSpot * twist6) < nsq (v - best.toSpot * twist6) then p else best)
    MDigit.zero

/-- One floor of the adder: given the leftover and the floor's digit total,
the digit written and the new leftover. -/
def addStep (u s : Spot) : MDigit × Spot :=
  let v := b * u + s
  let p := nearest v
  (p, v - p.toSpot * twist6)

/-- The leftover after reading `k` floors of each address. -/
def addState (x y : Endless) : Nat → Spot
  | 0 => 0
  | k + 1 => (addStep (addState x y k) ((x k).toSpot + (y k).toSpot)).2

/-- The sum, as an endless address, one floor at a time (written six floors higher). -/
def addE (x y : Endless) : Endless :=
  fun k => (addStep (addState x y k) ((x k).toSpot + (y k).toSpot)).1

/-! ### The adder is a finite machine: 85 leftovers -/

/-- The leftovers the adder can ever hold: the 9 × 9 square around zero, plus four more. -/
def InR (u : Spot) : Prop :=
  (u.re.natAbs ≤ 4 ∧ u.im.natAbs ≤ 4) ∨ (u.re.natAbs = 5 ∧ u.im.natAbs = 3)

instance (u : Spot) : Decidable (InR u) := by unfold InR; infer_instance

/-- Checked by running through every leftover and every pair of digits. -/
theorem addStep_closed_finite : ∀ a ∈ List.range 11, ∀ c ∈ List.range 9,
    InR ⟨(a : Int) - 5, (c : Int) - 4⟩ →
    ∀ d ∈ MDigit.all, ∀ e ∈ MDigit.all,
      InR (addStep ⟨(a : Int) - 5, (c : Int) - 4⟩ (d.toSpot + e.toSpot)).2 := by
  decide +kernel

theorem addStep_closed (u : Spot) (hu : InR u) (d e : MDigit) :
    InR (addStep u (d.toSpot + e.toSpot)).2 := by
  have hre : -5 ≤ u.re ∧ u.re ≤ 5 := by unfold InR at hu; omega
  have him : -4 ≤ u.im ∧ u.im ≤ 4 := by unfold InR at hu; omega
  have key := addStep_closed_finite (u.re + 5).toNat (List.mem_range.mpr (by omega))
    (u.im + 4).toNat (List.mem_range.mpr (by omega))
  have hu' : (⟨((u.re + 5).toNat : Int) - 5, ((u.im + 4).toNat : Int) - 4⟩ : Spot) = u := by
    ext <;> simp <;> omega
  rw [hu'] at key
  exact key hu d (MDigit.mem_all d) e (MDigit.mem_all e)

/-- **The adder never needs more than 85 leftovers.** -/
theorem addState_small (x y : Endless) (k : Nat) : InR (addState x y k) := by
  induction k with
  | zero => exact (by decide : InR ⟨0, 0⟩)
  | succ k ih => exact addStep_closed _ ih _ _

/-- **Each written digit depends only on the floors read so far.** -/
theorem addE_local (x y x' y' : Endless) (k : Nat)
    (hx : ∀ n ≤ k, x n = x' n) (hy : ∀ n ≤ k, y n = y' n) : addE x y k = addE x' y' k := by
  have hs : ∀ m ≤ k, addState x y m = addState x' y' m := by
    intro m hm
    induction m with
    | zero => rfl
    | succ m ih =>
      simp only [addState]
      rw [ih (by omega), hx m (by omega), hy m (by omega)]
  simp only [addE]
  rw [hs k (Nat.le_refl k), hx k (Nat.le_refl k), hy k (Nat.le_refl k)]

end Building
