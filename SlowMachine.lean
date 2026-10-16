import StepMachine

/-!
# Lighter masses: turning only every n-th tick (plain Lean, no math library)

Everyday-language summary (for the author):

* Piece 10 showed that if each tick climbs whole floors, the checkerboard allows only no
  mass, one enormous mass, or standing still. The way out checked here: **let an arrow turn
  only on every n-th tick**, and simply carry on in between. Nothing new is added: the
  carry-on ticks use no arithmetic at all, and the turning tick is the toy's.
* **Lean checks that this is exactly the toy running on a grid n cells coarser.** The cells
  `r, r + n, r + 2n, …` behave, period after period, exactly like the toy's row, and they
  never mix with the other cells. In the toy's own units the particle turns half the time;
  measured on the fine grid, its steps are n cells and n ticks long, so its mass is
  **1/n of the toy's**, for any whole number n, while light still moves one cell per tick.
* The price: a particle of mass 1/n only ever sees every n-th cell. Standard physics has the
  same kind of limit: a particle can't be pinned down finer than its "Compton wavelength"
  (trying creates new particles), and the lighter it is, the coarser that limit.
* A reading, not a result: a particle's mass becomes a whole number, the count of ticks
  between turns.
-/

namespace Building

/-- A whole line of cells: a cell for every position. -/
abbrev Line := Int → Cell

/-- **One tick of the toy, on a whole line**: each cell's right arrow is what the cell on its
left sends right, and its left arrow is what the cell on its right sends left (the same rule
as `tick` in `StepMachine.lean`). -/
def stepL (f : Line) : Line := fun x => (sendR (f (x - 1)), sendL (f (x + 1)))

/-- A tick with no turning: every arrow carries on one cell, unchanged. -/
def carry (f : Line) : Line := fun x => ((f (x - 1)).1, (f (x + 1)).2)

/-- `k` ticks of carrying on. -/
def carryN : Nat → Line → Line
  | 0, f => f
  | k + 1, f => carry (carryN k f)

theorem carryN_apply (k : Nat) (f : Line) (x : Int) :
    carryN k f x = ((f (x - k)).1, (f (x + k)).2) := by
  induction k generalizing x with
  | zero => simp [carryN]
  | succ k ih =>
    simp only [carryN, carry, ih]
    have e1 : x - 1 - (k : Int) = x - ((k + 1 : Nat) : Int) := by omega
    have e2 : x + 1 + (k : Int) = x + ((k + 1 : Nat) : Int) := by omega
    rw [e1, e2]

/-- **Turning only every n-th tick**: one tick of the toy, then `n − 1` ticks of carrying on. -/
def slowPeriod (n : Nat) (f : Line) : Line := carryN (n - 1) (stepL f)

/-- Over one period, each arrow moves `n` cells and turns (or not) once. -/
theorem slowPeriod_apply (n : Nat) (hn : 1 ≤ n) (f : Line) (x : Int) :
    slowPeriod n f x = (sendR (f (x - n)), sendL (f (x + n))) := by
  simp only [slowPeriod, carryN_apply, stepL]
  have e1 : x - ((n - 1 : Nat) : Int) - 1 = x - (n : Int) := by omega
  have e2 : x + ((n - 1 : Nat) : Int) + 1 = x + (n : Int) := by omega
  rw [e1, e2]

/-- The cells `r, r + n, r + 2n, …` of a line, as a line of their own: the coarse grid. -/
def coarse (n : Nat) (r : Int) (f : Line) : Line := fun y => f (r + n * y)

/-- **Turning every n-th tick is exactly the toy on a grid n cells coarser.** -/
theorem slow_is_coarse (n : Nat) (hn : 1 ≤ n) (r : Int) (f : Line) :
    coarse n r (slowPeriod n f) = stepL (coarse n r f) := by
  funext y
  simp only [coarse, slowPeriod_apply n hn, stepL]
  have e1 : r + (n : Int) * y - n = r + n * (y - 1) := by rw [Int.mul_sub, Int.mul_one]; omega
  have e2 : r + (n : Int) * y + n = r + n * (y + 1) := by rw [Int.mul_add, Int.mul_one]; omega
  rw [e1, e2]

/-- `t` periods of turning every n-th tick. -/
def slowRun (n : Nat) : Nat → Line → Line
  | 0, f => f
  | t + 1, f => slowPeriod n (slowRun n t f)

/-- `t` ticks of the toy. -/
def runL : Nat → Line → Line
  | 0, f => f
  | t + 1, f => stepL (runL t f)

/-- **For any number of periods**, the coarse cells run exactly like the toy. -/
theorem slowRun_is_coarse (n : Nat) (hn : 1 ≤ n) (r : Int) (t : Nat) (f : Line) :
    coarse n r (slowRun n t f) = runL t (coarse n r f) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [slowRun, runL, slow_is_coarse n hn, ih]

/-- **A particle of mass 1/n only ever sees every n-th cell**: what happens on the cells
`r, r + n, r + 2n, …` depends only on those cells, never on the cells in between. -/
theorem slow_sees_every_nth (n : Nat) (hn : 1 ≤ n) (r : Int) (t : Nat) (f g : Line)
    (h : ∀ y, f (r + n * y) = g (r + n * y)) (y : Int) :
    slowRun n t f (r + n * y) = slowRun n t g (r + n * y) := by
  have hf := congrFun (slowRun_is_coarse n hn r t f) y
  have hg := congrFun (slowRun_is_coarse n hn r t g) y
  have hc : coarse n r f = coarse n r g := funext h
  simp only [coarse] at hf hg
  rw [hf, hg, hc]

/-- With `n = 1` nothing is slowed: it is the toy itself. -/
theorem slow_one (f : Line) : slowPeriod 1 f = stepL f := rfl

/-- **Piece 11 in one statement.** -/
theorem piece_eleven :
    (∀ (n : Nat), 1 ≤ n → ∀ (r : Int) (t : Nat) (f : Line),
      coarse n r (slowRun n t f) = runL t (coarse n r f)) ∧
    (∀ (n : Nat), 1 ≤ n → ∀ (r : Int) (t : Nat) (f g : Line),
      (∀ y, f (r + n * y) = g (r + n * y)) →
        ∀ y, slowRun n t f (r + n * y) = slowRun n t g (r + n * y)) :=
  ⟨slowRun_is_coarse, slow_sees_every_nth⟩

end Building
