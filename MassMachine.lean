import StepMachine

/-!
# Which masses the floors allow (plain Lean, no math library)

Everyday-language summary (for the author):

* In the checkerboard (piece 9), **mass is how often an arrow turns around**. Each tick, an
  arrow's weight splits into a "carry on" part and a "turn" part. A particle that never
  turns has no mass and moves at light speed; one that turns more often is heavier.
* If each tick climbs whole floors, keeping the total means the two parts' squared sizes
  add up to a power of 2 (1, 2, 4, 8, …), whole numbers only.
* **Lean checks that this leaves exactly three possibilities**:
  1. the turn part is zero: the particle never turns, **no mass** (light);
  2. the two parts are the same size: **the toy's one mass**, which is enormous in grid
     units (it turns half the time);
  3. the carry-on part is zero: it always turns and **stays put** (infinitely heavy).
* So with whole floors alone, light comes free and every ordinary mass needs something
  more. The reason is plain arithmetic: two sums of two squares that add up to a power of 2
  must be equal, or one of them must be zero.
-/

namespace Building

theorem msq_nonneg (x : Int) : 0 ≤ x * x := by
  rcases Int.le_total 0 x with h | h
  · exact Int.mul_nonneg h h
  · have := Int.mul_nonneg (Int.neg_nonneg_of_nonpos h) (Int.neg_nonneg_of_nonpos h)
    simpa [Int.neg_mul_neg] using this

theorem msq_eq_zero (x : Int) (h : x * x = 0) : x = 0 := by
  rcases Int.mul_eq_zero.mp h with h | h <;> exact h

theorem sq_two (a : Int) : (2 * a) * (2 * a) = 4 * (a * a) := by grind

/-- An even number's square is a multiple of 4; an odd number's square leaves 1 when
divided by 8. -/
theorem sq_par (x : Int) : (x % 2 = 0 ∧ (x * x) % 4 = 0) ∨ (x % 2 = 1 ∧ (x * x) % 8 = 1) := by
  rcases Int.emod_two_eq x with h | h
  · left
    refine ⟨h, ?_⟩
    obtain ⟨q, rfl⟩ : ∃ q, x = 2 * q := ⟨x / 2, by omega⟩
    rw [sq_two]
    omega
  · right
    refine ⟨h, ?_⟩
    have hm := Int.mul_emod x x 8
    have hx : x % 8 = 1 ∨ x % 8 = 3 ∨ x % 8 = 5 ∨ x % 8 = 7 := by omega
    generalize x * x = X at hm ⊢
    rcases hx with hx | hx | hx | hx <;> rw [hx] at hm <;> omega

/-- **The arithmetic heart**: if `x² + y²` and `u² + v²` add up to a power of 2, they are
equal, or one of them is zero. -/
theorem two_masses_int : ∀ (k : Nat) (x y u v : Int),
    x * x + y * y + (u * u + v * v) = 2 ^ k →
      x * x + y * y = u * u + v * v ∨ (x = 0 ∧ y = 0) ∨ (u = 0 ∧ v = 0) := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro x y u v h
    by_cases hk : k ≤ 2
    · -- small totals (1, 2 or 4): every square is 0, 1 or 4
      have hp : (2 : Int) ^ k = 1 ∨ (2 : Int) ^ k = 2 ∨ (2 : Int) ^ k = 4 := by
        have : k = 0 ∨ k = 1 ∨ k = 2 := by omega
        rcases this with rfl | rfl | rfl <;> decide
      have px := sq_par x
      have py := sq_par y
      have pu := sq_par u
      have pv := sq_par v
      have nx := msq_nonneg x
      have ny := msq_nonneg y
      have nu := msq_nonneg u
      have nv := msq_nonneg v
      have zx := msq_eq_zero x
      have zy := msq_eq_zero y
      have zu := msq_eq_zero u
      have zv := msq_eq_zero v
      generalize (2 : Int) ^ k = T at h hp
      generalize x * x = X at *
      generalize y * y = Y at *
      generalize u * u = U at *
      generalize v * v = V at *
      have bX : X = 0 ∨ X = 1 ∨ X = 4 := by rcases px with ⟨_, h1⟩ | ⟨_, h1⟩ <;> omega
      have bY : Y = 0 ∨ Y = 1 ∨ Y = 4 := by rcases py with ⟨_, h1⟩ | ⟨_, h1⟩ <;> omega
      have bU : U = 0 ∨ U = 1 ∨ U = 4 := by rcases pu with ⟨_, h1⟩ | ⟨_, h1⟩ <;> omega
      have bV : V = 0 ∨ V = 1 ∨ V = 4 := by rcases pv with ⟨_, h1⟩ | ⟨_, h1⟩ <;> omega
      have key : X + Y = U + V ∨ (X = 0 ∧ Y = 0) ∨ (U = 0 ∧ V = 0) := by
        clear px py pu pv zx zy zu zv
        rcases bX with rfl | rfl | rfl <;> rcases bY with rfl | rfl | rfl <;>
          rcases bU with rfl | rfl | rfl <;> rcases bV with rfl | rfl | rfl <;> omega
      rcases key with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl h1
      · exact Or.inr (Or.inl ⟨zx h1, zy h2⟩)
      · exact Or.inr (Or.inr ⟨zu h1, zv h2⟩)
    · -- totals of 8 or more: all four numbers are even, so halve them and repeat
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
      have h8 : (2 : Int) ^ (j + 3) = 8 * 2 ^ j := by
        simp only [Int.pow_succ]; omega
      have hev : x % 2 = 0 ∧ y % 2 = 0 ∧ u % 2 = 0 ∧ v % 2 = 0 := by
        have px := sq_par x
        have py := sq_par y
        have pu := sq_par u
        have pv := sq_par v
        rw [h8] at h
        generalize (2 : Int) ^ j = P at h
        generalize x * x = X at *
        generalize y * y = Y at *
        generalize u * u = U at *
        generalize v * v = V at *
        rcases px with ⟨ex, hx⟩ | ⟨ex, hx⟩ <;> rcases py with ⟨ey, hy⟩ | ⟨ey, hy⟩ <;>
          rcases pu with ⟨eu, hu⟩ | ⟨eu, hu⟩ <;> rcases pv with ⟨ev, hv⟩ | ⟨ev, hv⟩ <;> omega
      obtain ⟨ex, ey, eu, ev⟩ := hev
      obtain ⟨a, rfl⟩ : ∃ a, x = 2 * a := ⟨x / 2, by omega⟩
      obtain ⟨c, rfl⟩ : ∃ c, y = 2 * c := ⟨y / 2, by omega⟩
      obtain ⟨d, rfl⟩ : ∃ d, u = 2 * d := ⟨u / 2, by omega⟩
      obtain ⟨e, rfl⟩ : ∃ e, v = 2 * e := ⟨v / 2, by omega⟩
      have h4 : (2 : Int) ^ (j + 3) = 4 * 2 ^ (j + 1) := by
        simp only [Int.pow_succ]; omega
      rw [sq_two, sq_two, sq_two, sq_two, h4] at h
      have h' : a * a + c * c + (d * d + e * e) = 2 ^ (j + 1) := by omega
      rw [sq_two, sq_two, sq_two, sq_two]
      rcases ih (j + 1) (by omega) a c d e h' with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left; omega
      · right; left; omega
      · right; right; omega

/-- **Which masses the floors allow.** Split an arrow's weight into a carry-on part `α` and
a turn part `β` (whole-number spots). If climbing whole floors keeps the total, their squared
sizes add up to a power of 2, and then: they are the same size (the toy's one mass), or the
turn part is zero (no mass), or the carry-on part is zero (always turns, stays put). -/
theorem two_masses (k : Nat) (α β : Spot) (h : nsq α + nsq β = 2 ^ k) :
    nsq α = nsq β ∨ β = 0 ∨ α = 0 := by
  obtain ⟨x, y⟩ := α
  obtain ⟨u, v⟩ := β
  simp only [nsq] at h ⊢
  rcases two_masses_int k x y u v h with h1 | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inr rfl)
  · exact Or.inr (Or.inl rfl)

/-- The toy's mix (carry on with weight 1, turn with weight −i) is the middle case: two
equal parts, squared sizes adding up to 2, one floor per tick. -/
theorem toy_mix : nsq (1 : Spot) = nsq (-Spot.i) ∧ nsq (1 : Spot) + nsq (-Spot.i) = 2 ^ 1 := by
  decide

end Building
