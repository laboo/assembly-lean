/-!
# The Building, piece 1: the ground floor's addresses

Everyday-language summary (for the author):

* A **spot** is a place on a flat grid: so many steps east and so many steps north,
  both whole numbers. Two spots can be added (walk one, then the other) and
  multiplied by the **turning rule**, the same rule the complex plane uses.
* The **twist** is the number `b = −1 + i`: going one floor down means
  "turn three-eighths of a lap and grow a little". Every spot gets an
  **address** made only of 0s and 1s, one digit per floor (Penney, 1965).
* **Which way is up** (the same in every file, and the same as in the model): up means
  finer, down means coarser. The **ground floor** holds a spot's ones digit. A whole-number
  spot's address uses the ground floor and the floors beneath it; the finer floors above
  the ground floor go on forever (pieces 2 onward). Moving something down a floor means
  turning it three-eighths of a lap and growing it; moving it up a floor shrinks it back.
* This file proves, and Lean checks, that:
  1. every spot has an address (nothing is left without a home),
  2. no two different addresses name the same spot (exactly one home each),
  3. adding two addresses digit by digit, with a small carry passed from
     floor to floor, gives exactly the address of the sum, and the carry never
     needs more than a fixed handful of values (the machine is finite and local),
  4. multiplying two addresses with nothing but that adder gives exactly the
     address of the product, so the turning rule comes out of 0s and 1s.

Nothing here is borrowed from a math library: only whole numbers, adding,
subtracting, multiplying, and halving numbers that are already even.
-/

namespace Building

/-! ## 1. Spots and the turning rule -/

/-- A spot on the grid: `re` steps east, `im` steps north (negative means west or south). -/
@[ext] structure Spot where
  re : Int
  im : Int
deriving DecidableEq, Repr, Inhabited

namespace Spot

instance : Add Spot := ⟨fun z w => ⟨z.re + w.re, z.im + w.im⟩⟩
instance : Neg Spot := ⟨fun z => ⟨-z.re, -z.im⟩⟩
instance : Sub Spot := ⟨fun z w => ⟨z.re - w.re, z.im - w.im⟩⟩
/-- The turning rule: exactly how the complex plane multiplies `(a + bi)(c + di)`. -/
instance : Mul Spot := ⟨fun z w => ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩⟩
instance : OfNat Spot 0 := ⟨⟨0, 0⟩⟩
instance : OfNat Spot 1 := ⟨⟨1, 0⟩⟩

/-- One step north: the quarter turn. -/
def i : Spot := ⟨0, 1⟩

@[simp] theorem add_re (z w : Spot) : (z + w).re = z.re + w.re := rfl
@[simp] theorem add_im (z w : Spot) : (z + w).im = z.im + w.im := rfl
@[simp] theorem neg_re (z : Spot) : (-z).re = -z.re := rfl
@[simp] theorem neg_im (z : Spot) : (-z).im = -z.im := rfl
@[simp] theorem sub_re (z w : Spot) : (z - w).re = z.re - w.re := rfl
@[simp] theorem sub_im (z w : Spot) : (z - w).im = z.im - w.im := rfl
@[simp] theorem mul_re (z w : Spot) : (z * w).re = z.re * w.re - z.im * w.im := rfl
@[simp] theorem mul_im (z w : Spot) : (z * w).im = z.re * w.im + z.im * w.re := rfl
@[simp] theorem zero_re : (0 : Spot).re = 0 := rfl
@[simp] theorem zero_im : (0 : Spot).im = 0 := rfl
@[simp] theorem one_re : (1 : Spot).re = 1 := rfl
@[simp] theorem one_im : (1 : Spot).im = 0 := rfl
@[simp] theorem i_re : i.re = 0 := rfl
@[simp] theorem i_im : i.im = 1 := rfl

/-! The everyday laws of arithmetic hold for spots (Lean checks each one). -/

theorem add_comm (z w : Spot) : z + w = w + z := by ext <;> simp <;> omega
theorem add_assoc (z w v : Spot) : z + w + v = z + (w + v) := by ext <;> simp <;> omega
theorem zero_add (z : Spot) : 0 + z = z := by ext <;> simp
theorem add_zero (z : Spot) : z + 0 = z := by ext <;> simp
theorem mul_comm (z w : Spot) : z * w = w * z := by ext <;> simp <;> grind
theorem mul_assoc (z w v : Spot) : z * w * v = z * (w * v) := by ext <;> simp <;> grind
theorem mul_add (z w v : Spot) : z * (w + v) = z * w + z * v := by ext <;> simp <;> grind
theorem mul_one (z : Spot) : z * 1 = z := by ext <;> simp
theorem mul_zero (z : Spot) : z * 0 = 0 := by ext <;> simp

/-- Minus is half a turn: two quarter turns make minus one. -/
theorem i_mul_i : i * i = -1 := by decide

end Spot

open Spot

/-! ## 2. The twist between floors -/

/-- The twist `b = −1 + i`: one step west and one step north. Its direction is
three-eighths of a lap, and its length is the square root of 2. -/
def b : Spot := ⟨-1, 1⟩

@[simp] theorem b_re : b.re = -1 := rfl
@[simp] theorem b_im : b.im = 1 := rfl
theorem b_mul_re (w : Spot) : (b * w).re = -w.re - w.im := by simp <;> omega
theorem b_mul_im (w : Spot) : (b * w).im = w.re - w.im := by simp <;> omega

/-- Two floors down is a quarter turn (clockwise) plus doubling: `b · b = −2i`. -/
theorem b_mul_b : b * b = ⟨0, -2⟩ := by decide

/-- Four floors down is a half turn plus a factor of four: `b⁴ = −4`. -/
theorem b_pow_four : b * b * (b * b) = ⟨-4, 0⟩ := by decide

/-! ## 3. Addresses: one digit (0 or 1) per floor

An address is a list of digits, ground floor first (the last digit written), then each
floor beneath it in turn.
`true` is the digit 1 and `false` the digit 0. -/

/-- A digit as a spot: 1 or 0. -/
def dval (d : Bool) : Spot := ⟨if d then 1 else 0, 0⟩

@[simp] theorem dval_re (d : Bool) : (dval d).re = if d then 1 else 0 := rfl
@[simp] theorem dval_im (d : Bool) : (dval d).im = 0 := rfl

/-- Read an address with something (`top`) still waiting on the floors further down:
digit + b·(digit + b·(digit + … + b·top)). -/
def valueWith : List Bool → Spot → Spot
  | [], top => top
  | d :: ds, top => dval d + b * valueWith ds top

/-- The spot an address names. -/
def value (ds : List Bool) : Spot := valueWith ds 0

@[simp] theorem value_nil : value [] = 0 := rfl
@[simp] theorem value_cons (d : Bool) (ds : List Bool) :
    value (d :: ds) = dval d + b * value ds := rfl

/-- Which digit a spot puts on the current floor: 1 exactly when east + north is odd. -/
def digitOf (z : Spot) : Bool := decide ((z.re + z.im) % 2 = 1)

/-- Peel off the current floor's digit and step down one floor: `(z − digit) / b`.
The division is exact; it only ever halves even numbers. -/
def peel (z : Spot) : Spot :=
  let d : Int := (z.re + z.im) % 2
  ⟨(z.im - z.re + d) / 2, (d - z.re - z.im) / 2⟩

/-- The heart of it: every spot is its digit plus `b` times what's left further down. -/
theorem digit_add_b_peel (z : Spot) : dval (digitOf z) + b * peel z = z := by
  by_cases h : (z.re + z.im) % 2 = 1 <;> ext <;> simp [digitOf, peel, h] <;> omega

/-- The first `n` digits of a spot's address. -/
def firstDigits : Nat → Spot → List Bool
  | 0, _ => []
  | n + 1, z => digitOf z :: firstDigits n (peel z)

/-- What is still left further down after `n` floors. -/
def leftover : Nat → Spot → Spot
  | 0, z => z
  | n + 1, z => leftover n (peel z)

/-- Nothing is lost: the first `n` digits, plus what's left further down, give back the spot. -/
theorem valueWith_firstDigits (n : Nat) (z : Spot) :
    valueWith (firstDigits n z) (leftover n z) = z := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    simp only [firstDigits, leftover, valueWith]
    rw [ih]
    exact digit_add_b_peel z

/-! ### Every spot runs out of digits

Two floors at a time, the spot's size (its larger coordinate) roughly halves,
so after enough floors nothing is left further down. -/

/-- The larger of a spot's two coordinates, as a size. -/
def size (z : Spot) : Nat := max z.re.natAbs z.im.natAbs

theorem peel_zero : peel 0 = 0 := by decide

theorem leftover_zero (n : Nat) : leftover n 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [leftover, peel_zero, ih]

theorem leftover_add (m n : Nat) (z : Spot) :
    leftover (m + n) z = leftover n (leftover m z) := by
  induction m generalizing z with
  | zero => simp [leftover]
  | succ m ih =>
    rw [Nat.add_right_comm]
    simp only [leftover, ih]

/-- Two floors up, a spot of size at most `M + 1` (with `M ≥ 1`) has size at most `M`. -/
theorem size_peel_peel (z : Spot) (M : Nat) (hM : 1 ≤ M)
    (hr : z.re.natAbs ≤ M + 1) (hi : z.im.natAbs ≤ M + 1) :
    (peel (peel z)).re.natAbs ≤ M ∧ (peel (peel z)).im.natAbs ≤ M := by
  simp only [peel]
  omega

/-- The nine spots of size at most 1 all run out within 8 floors (checked by running). -/
theorem small_runs_out : ∀ x y : Int, x.natAbs ≤ 1 → y.natAbs ≤ 1 →
    leftover 8 ⟨x, y⟩ = 0 := by
  intro x y hx hy
  have hx' : x = -1 ∨ x = 0 ∨ x = 1 := by omega
  have hy' : y = -1 ∨ y = 0 ∨ y = 1 := by omega
  rcases hx' with rfl | rfl | rfl <;> rcases hy' with rfl | rfl | rfl <;> decide

theorem runs_out (M : Nat) : ∀ z : Spot, z.re.natAbs ≤ M → z.im.natAbs ≤ M →
    leftover (2 * M + 8) z = 0 := by
  induction M with
  | zero =>
    intro z hr hi
    exact small_runs_out z.re z.im (by omega) (by omega)
  | succ M ih =>
    intro z hr hi
    by_cases hM : M = 0
    · subst hM
      have := small_runs_out z.re z.im hr hi
      have h8 : leftover (2 * (0 + 1) + 8) z = leftover 2 (leftover 8 z) := by
        rw [← leftover_add]
      rw [h8, this, leftover_zero]
    · have ⟨h1, h2⟩ := size_peel_peel z M (by omega) hr hi
      have : leftover (2 * (M + 1) + 8) z = leftover (2 * M + 8) (peel (peel z)) := by
        rw [show 2 * (M + 1) + 8 = 2 + (2 * M + 8) by omega, leftover_add]
        rfl
      rw [this]
      exact ih _ h1 h2

/-! ### Tidy addresses: no extra zeros on the bottom floors -/

/-- Drop spare zeros on the lowest floors (leading zeros, when the address is written out). -/
def trim : List Bool → List Bool
  | [] => []
  | d :: ds =>
    match d, trim ds with
    | false, [] => []
    | d, t => d :: t

theorem value_trim (ds : List Bool) : value (trim ds) = value ds := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    simp only [trim]
    split
    · next h =>
      rw [value_cons, ← ih, h]
      ext <;> simp
    · simp [ih]

theorem trim_trim (ds : List Bool) : trim (trim ds) = trim ds := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    cases d <;> cases h : trim ds <;> simp_all [trim]

/-- The address of a spot: as many floors as it needs, and no more. -/
def address (z : Spot) : List Bool := trim (firstDigits (2 * size z + 8) z)

/-- **Every spot has an address**: reading the address gives back the spot. -/
theorem value_address (z : Spot) : value (address z) = z := by
  unfold address
  rw [value_trim]
  have h := valueWith_firstDigits (2 * size z + 8) z
  rw [runs_out (size z) z (by simp [size]; omega) (by simp [size]; omega)] at h
  exact h

/-! ### Exactly one address per spot -/

/-- If two floors' worth of reading agree, the digits agree and so does everything further down. -/
theorem digit_unique (d e : Bool) (u v : Spot) (h : dval d + b * u = dval e + b * v) :
    d = e ∧ u = v := by
  have hr := congrArg Spot.re h
  have hi := congrArg Spot.im h
  simp at hr hi
  cases d <;> cases e <;> simp at hr hi
  · exact ⟨rfl, by ext <;> omega⟩
  · omega
  · omega
  · exact ⟨rfl, by ext <;> omega⟩

theorem trim_of_value_zero (ds : List Bool) (h : value ds = 0) : trim ds = [] := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    have h' : dval d + b * value ds = dval false + b * 0 := by
      rw [← value_cons, h]; decide
    have ⟨hd, hv⟩ := digit_unique _ _ _ _ h'
    subst hd
    simp [trim, ih hv]

/-- **No two different addresses name the same spot** (once spare zeros on the bottom floors are dropped). -/
theorem trim_eq_of_value_eq (ds es : List Bool) (h : value ds = value es) :
    trim ds = trim es := by
  induction ds generalizing es with
  | nil =>
    rw [trim_of_value_zero es h.symm]; rfl
  | cons d ds ih =>
    cases es with
    | nil => exact trim_of_value_zero _ h
    | cons e es =>
      have ⟨hd, hv⟩ := digit_unique _ _ _ _ h
      subst hd
      simp only [trim, ih es hv]

theorem trim_address (z : Spot) : trim (address z) = address z := by
  simp [address, trim_trim]

/-- **The address of what an address names is that address**, tidied. -/
theorem address_value (ds : List Bool) : address (value ds) = trim ds := by
  rw [← trim_address]
  exact trim_eq_of_value_eq _ _ (value_address _)

/-! ## 4. Adding addresses floor by floor -/

/-- Line two addresses up floor by floor. Each floor then holds 0, 1 or 2. -/
def columns : List Bool → List Bool → List Spot
  | [], [] => []
  | d :: ds, [] => dval d :: columns ds []
  | [], e :: es => dval e :: columns [] es
  | d :: ds, e :: es => (dval d + dval e) :: columns ds es

/-- Read a list of floor totals the same way as an address. -/
def valueCols : List Spot → Spot
  | [] => 0
  | c :: cs => c + b * valueCols cs

theorem valueCols_columns_nil_right (ds : List Bool) :
    valueCols (columns ds []) = value ds := by
  induction ds with
  | nil => simp [columns, valueCols]
  | cons d ds ih => simp [columns, valueCols, ih]

theorem valueCols_columns_nil_left (es : List Bool) :
    valueCols (columns [] es) = value es := by
  induction es with
  | nil => simp [columns, valueCols]
  | cons e es ih => simp [columns, valueCols, ih]

theorem valueCols_columns (ds es : List Bool) :
    valueCols (columns ds es) = value ds + value es := by
  induction ds generalizing es with
  | nil => rw [valueCols_columns_nil_left]; ext <;> simp
  | cons d ds ih =>
    cases es with
    | nil => rw [valueCols_columns_nil_right]; ext <;> simp
    | cons e es =>
      simp only [columns, valueCols, ih, value_cons]
      ext <;> simp <;> omega

/-- Settle floor totals into 0/1 digits, starting at the ground floor and passing a carry
down one floor at a time. Every floor follows the same rule: add the carry, write the
digit, pass the rest down. When the floors run out, the last carry is written out with
that same rule. -/
def settle : List Spot → Spot → List Bool
  | [], carry => address carry
  | col :: cols, carry => digitOf (col + carry) :: settle cols (peel (col + carry))

theorem value_settle (cols : List Spot) (carry : Spot) :
    value (settle cols carry) = valueCols cols + carry := by
  induction cols generalizing carry with
  | nil => simp [settle, valueCols, value_address, zero_add]
  | cons col cols ih =>
    simp only [settle, value_cons, ih, valueCols]
    have hv := digit_add_b_peel (col + carry)
    have hr := congrArg Spot.re hv
    have hi := congrArg Spot.im hv
    ext <;> simp at hr hi ⊢ <;> omega

/-- Add two addresses using nothing but digits and a carry. -/
def addA (ds es : List Bool) : List Bool := settle (columns ds es) 0

theorem value_addA (ds es : List Bool) : value (addA ds es) = value ds + value es := by
  simp [addA, value_settle, valueCols_columns, add_zero]

/-! ### The adder is a finite machine

The carry passed from one floor to the next is always one of these fifteen spots,
so each floor needs only its own two digits and one of fifteen carries. -/

/-- Every carry the adder can ever need. -/
def carries : List Spot :=
  [⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩, ⟨-1, -2⟩,
   ⟨0, 2⟩, ⟨-1, 1⟩, ⟨1, -1⟩, ⟨0, -2⟩, ⟨-2, -1⟩, ⟨-2, 0⟩, ⟨1, 2⟩]

/-- A floor total for adding two addresses: 0, 1 or 2. -/
def ColOK (col : Spot) : Prop := col.im = 0 ∧ 0 ≤ col.re ∧ col.re ≤ 2

/-- Checked by running through all 15 × 3 cases. -/
theorem carries_closed' : ∀ c ∈ carries, ∀ k ∈ ([0, 1, 2] : List Int),
    peel (⟨k, 0⟩ + c) ∈ carries := by decide

theorem carries_closed (c : Spot) (hc : c ∈ carries) (col : Spot) (h : ColOK col) :
    peel (col + c) ∈ carries := by
  obtain ⟨h0, h1, h2⟩ := h
  have hk : col = ⟨col.re, 0⟩ := by ext <;> simp [h0]
  rw [hk]
  apply carries_closed' c hc
  have : col.re = 0 ∨ col.re = 1 ∨ col.re = 2 := by omega
  rcases this with h | h | h <;> simp [h]

theorem columns_ok (ds es : List Bool) : ∀ col ∈ columns ds es, ColOK col := by
  induction ds generalizing es with
  | nil =>
    induction es with
    | nil => simp [columns]
    | cons e es ih =>
      simp only [columns, List.mem_cons]
      rintro col (rfl | h)
      · cases e <;> simp [ColOK]
      · exact ih col h
  | cons d ds ih =>
    cases es with
    | nil =>
      have := ih []
      simp only [columns, List.mem_cons] at this ⊢
      rintro col (rfl | h)
      · cases d <;> simp [ColOK]
      · exact this col h
    | cons e es =>
      simp only [columns, List.mem_cons]
      rintro col (rfl | h)
      · cases d <;> cases e <;> simp [ColOK]
      · exact ih es col h

/-- The carries used on the way down, floor by floor. -/
def carryTrail : List Spot → Spot → List Spot
  | [], carry => [carry]
  | col :: cols, carry => carry :: carryTrail cols (peel (col + carry))

theorem carryTrail_small (cols : List Spot) (h : ∀ col ∈ cols, ColOK col)
    (carry : Spot) (hc : carry ∈ carries) : ∀ c ∈ carryTrail cols carry, c ∈ carries := by
  induction cols generalizing carry with
  | nil => simp [carryTrail, hc]
  | cons col cols ih =>
    simp only [carryTrail, List.mem_cons]
    rintro c (rfl | hmem)
    · exact hc
    · exact ih (fun x hx => h x (List.mem_cons_of_mem _ hx)) _
        (carries_closed carry hc col (h col List.mem_cons_self)) c hmem

/-- **Adding two addresses never needs more than fifteen carry values.** -/
theorem addA_finite (ds es : List Bool) :
    ∀ c ∈ carryTrail (columns ds es) 0, c ∈ carries :=
  carryTrail_small _ (columns_ok ds es) 0 (by decide)

/-! ## 5. Multiplying addresses with nothing but the adder -/

/-- The schoolbook way: for every 1 in the second address, add a copy of the first,
moved down as many floors as that 1 sits below the ground floor. -/
def mulA (ds : List Bool) : List Bool → List Bool
  | [] => []
  | e :: es => addA (if e then ds else []) (false :: mulA ds es)

theorem value_mulA (ds es : List Bool) : value (mulA ds es) = value ds * value es := by
  induction es with
  | nil => simp [mulA, mul_zero]
  | cons e es ih =>
    simp only [mulA, value_addA, value_cons, ih]
    cases e <;> ext <;> simp <;> grind

/-! ## 6. Landing on the complex plane's answers -/

/-- **Piece 1 of the proof that runs.** Working only with 0/1 addresses, one digit per
floor, and a carry that is always one of fifteen values, adding and multiplying land
exactly on the addresses of the complex plane's answers (after dropping spare zeros on
the bottom floors). -/
theorem ground_floor_lands (z w : Spot) :
    trim (addA (address z) (address w)) = address (z + w) ∧
    trim (mulA (address z) (address w)) = address (z * w) := by
  constructor
  · rw [← address_value, value_addA, value_address, value_address]
  · rw [← address_value, value_mulA, value_address, value_address]

end Building
