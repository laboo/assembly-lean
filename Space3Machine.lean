import StepMachine

/-!
# Three directions of space (plain Lean, no math library)

Everyday-language summary (for the author):

* **Space now has three directions**, east-west, north-south and up-down, with a cell at
  every place. Each cell holds **two arrows**. A free particle with no mass (one that always
  moves at light speed) is the simplest thing to run first.
* **One tick has three moves, one per direction.** Before each move the cell's two arrows
  are **turned** so that, for that direction, one arrow points "forward" and the other
  "back"; then the forward arrow steps one cell forward and the back arrow one cell back.
  This is the standard way of building the Dirac and Weyl equations step by step
  ("operator splitting"); Arrighi, Nesme and Forets (2014) proved it approaches the real
  equation as the grid gets finer.
* **The turns are whole-number turns, one floor each.** Each of the three turns adds and
  quarter-turns the two arrows, and doubles the cell's squared size exactly: one floor. So
  one tick climbs three floors, one per direction moved, and the three turns together come
  back to where they started (times `2 − 2i`, three floors).
* Lean checks:
  1. each turn doubles every cell's squared size exactly (nothing created or lost, read one
     floor finer), and each turn can be undone (undoing gives back the arrows, doubled);
  2. each move only carries arrows to a neighbor and can be undone exactly;
  3. the three turns together return to the start, three floors down;
  4. **nothing moves faster than one cell per direction per tick**: what a place holds after
     a tick depends only on the 27 places around it.
* Measured by running (not proved here): at long wavelengths the particle moves at the
  same speed in every direction; the grid only shows up at short wavelengths.
-/

namespace Building

open Spot

/-- Space in three directions: a cell (two arrows) at every place `x, y, z`. -/
abbrev Space := Int → Int → Int → Cell

/-- Turn so that east-west becomes "forward/back": add and subtract the two arrows. -/
def turnZX (c : Cell) : Cell := (c.1 + c.2, c.1 - c.2)

/-- Turn from east-west to north-south. -/
def turnXY (c : Cell) : Cell := (-(i * c.1) + c.2, c.1 - i * c.2)

/-- Turn from north-south to up-down. -/
def turnYZ (c : Cell) : Cell := (c.1 + c.2, i * c.1 - i * c.2)

/-- Apply a turn in every cell. -/
def mapS (t : Cell → Cell) (f : Space) : Space := fun x y z => t (f x y z)

/-- Move along east-west: the forward arrow steps one cell east, the back arrow one west. -/
def moveX (f : Space) : Space := fun x y z => ((f (x - 1) y z).1, (f (x + 1) y z).2)

/-- Move along north-south. -/
def moveY (f : Space) : Space := fun x y z => ((f x (y - 1) z).1, (f x (y + 1) z).2)

/-- Move along up-down. -/
def moveZ (f : Space) : Space := fun x y z => ((f x y (z - 1)).1, (f x y (z + 1)).2)

/-- **One tick in three directions**: turn, move east-west; turn, move north-south; turn,
move up-down. -/
def step3 (f : Space) : Space :=
  moveZ (mapS turnYZ (moveY (mapS turnXY (moveX (mapS turnZX f)))))

/-! ## 1. Each turn doubles every cell exactly, and can be undone -/

theorem turnZX_size (c : Cell) : cellSize (turnZX c) = 2 * cellSize c := by
  simp only [cellSize, nsq, turnZX, Spot.add_re, Spot.add_im, Spot.sub_re, Spot.sub_im]
  grind

theorem turnXY_size (c : Cell) : cellSize (turnXY c) = 2 * cellSize c := by
  simp only [cellSize, nsq, turnXY, Spot.add_re, Spot.add_im, Spot.sub_re, Spot.sub_im,
    Spot.neg_re, Spot.neg_im, Spot.mul_re, Spot.mul_im, Spot.i_re, Spot.i_im]
  grind

theorem turnYZ_size (c : Cell) : cellSize (turnYZ c) = 2 * cellSize c := by
  simp only [cellSize, nsq, turnYZ, Spot.add_re, Spot.add_im, Spot.sub_re, Spot.sub_im,
    Spot.mul_re, Spot.mul_im, Spot.i_re, Spot.i_im]
  grind

/-- Undo the east-west turn (it is its own undo). -/
def backZX (c : Cell) : Cell := turnZX c

/-- Undo the north-south turn. -/
def backXY (c : Cell) : Cell := (i * c.1 + c.2, c.1 + i * c.2)

/-- Undo the up-down turn. -/
def backYZ (c : Cell) : Cell := (c.1 - i * c.2, c.1 + i * c.2)

/-- Every arrow doubled. -/
def dbl (c : Cell) : Cell := (c.1 + c.1, c.2 + c.2)

theorem back_turnZX (c : Cell) : backZX (turnZX c) = dbl c := by
  simp only [backZX, turnZX, dbl, Prod.mk.injEq]
  constructor <;> ext <;> simp <;> omega

theorem back_turnXY (c : Cell) : backXY (turnXY c) = dbl c := by
  simp only [backXY, turnXY, dbl, Prod.mk.injEq]
  constructor <;> ext <;> simp <;> grind

theorem back_turnYZ (c : Cell) : backYZ (turnYZ c) = dbl c := by
  simp only [backYZ, turnYZ, dbl, Prod.mk.injEq]
  constructor <;> ext <;> simp <;> grind

/-- **The three turns together come back to the start**, times `2 − 2i` (three floors). -/
theorem three_turns (c : Cell) :
    turnYZ (turnXY (turnZX c)) = ((⟨2, -2⟩ : Spot) * c.1, (⟨2, -2⟩ : Spot) * c.2) := by
  simp only [turnYZ, turnXY, turnZX, Prod.mk.injEq]
  constructor <;> ext <;> simp <;> grind

/-! ## 2. Moves only carry arrows, and can be undone exactly -/

def unmoveX (f : Space) : Space := fun x y z => ((f (x + 1) y z).1, (f (x - 1) y z).2)
def unmoveY (f : Space) : Space := fun x y z => ((f x (y + 1) z).1, (f x (y - 1) z).2)
def unmoveZ (f : Space) : Space := fun x y z => ((f x y (z + 1)).1, (f x y (z - 1)).2)

theorem unmoveX_moveX (f : Space) : unmoveX (moveX f) = f := by
  funext x y z; simp [unmoveX, moveX]

theorem unmoveY_moveY (f : Space) : unmoveY (moveY f) = f := by
  funext x y z; simp [unmoveY, moveY]

theorem unmoveZ_moveZ (f : Space) : unmoveZ (moveZ f) = f := by
  funext x y z; simp [unmoveZ, moveZ]

/-! ## 3. Nothing moves faster than one cell per direction per tick -/

/-- **What a place holds after a tick depends only on the 27 places around it.** -/
theorem step3_local (f g : Space) (x y z : Int)
    (h : ∀ a b c, x - 1 ≤ a → a ≤ x + 1 → y - 1 ≤ b → b ≤ y + 1 → z - 1 ≤ c → c ≤ z + 1 →
      f a b c = g a b c) :
    step3 f x y z = step3 g x y z := by
  simp only [step3, moveZ, mapS, moveY, moveX]
  simp (disch := omega) only [h]

/-- **Piece 13 in one statement.** -/
theorem piece_thirteen :
    (∀ c, cellSize (turnZX c) = 2 * cellSize c ∧ cellSize (turnXY c) = 2 * cellSize c ∧
      cellSize (turnYZ c) = 2 * cellSize c) ∧
    (∀ c, backZX (turnZX c) = dbl c ∧ backXY (turnXY c) = dbl c ∧ backYZ (turnYZ c) = dbl c) ∧
    (∀ f : Space, unmoveX (moveX f) = f ∧ unmoveY (moveY f) = f ∧ unmoveZ (moveZ f) = f) ∧
    (∀ c, turnYZ (turnXY (turnZX c)) = ((⟨2, -2⟩ : Spot) * c.1, (⟨2, -2⟩ : Spot) * c.2)) :=
  ⟨fun c => ⟨turnZX_size c, turnXY_size c, turnYZ_size c⟩,
   fun c => ⟨back_turnZX c, back_turnXY c, back_turnYZ c⟩,
   fun f => ⟨unmoveX_moveX f, unmoveY_moveY f, unmoveZ_moveZ f⟩,
   three_turns⟩

end Building
