import StepMachine
import MassMachine

/-!
# Two particles on a line (plain Lean, no math library)

Everyday-language summary (for the author):

* **The cell reading.** Space is a row of places. With two particles, the building keeps one
  **pair-cell for every pair of places** (particle 1 here, particle 2 there): "one cell for
  each way they could be arranged," as the model says. Each pair-cell holds **four arrows**,
  one for each combination of directions (both right, right-left, left-right, both left).
* **Each particle moves on its own.** Particle 1's tick mixes and moves only its own
  direction and place; particle 2's tick does the same for particle 2. Both are the toy's
  checkerboard step (piece 9), whole numbers only, one floor per tick.
* Lean checks:
  1. **the total is kept**: each particle's tick exactly doubles the total of the squared
     sizes, so read one floor finer per tick the odds always add up to one;
  2. **no messages**: anything done to particle 2 alone that keeps its total, including
     moving it or leaving it frozen, leaves particle 1's own odds exactly as they were
     (read at the matching floor); so a link between them can never carry a signal;
  3. **a linked pair is one thing**: the pair that starts as "particle 1 heading right and
     particle 2 heading left, minus the reverse" can't be split into an arrow pair for
     particle 1 times an arrow pair for particle 2. Linked particles are exactly what
     can't be factored apart (the model's matching table, v0.6, now checked);
  4. **who moves first doesn't matter** (checked by running, on the linked pair).
* **The room upstairs, in plain view.** Two particles on 9 places need 81 pair-cells, not
  18 cells: the room grows as a product, which is the exponential room the machine has to
  supply. Where the pair-cells live is the model's open question.
-/

namespace Building

open Spot

/-- Two particles: for every place of particle 1 (outer list), two rows over particle 2's
places, one for particle 1 heading right (`.1`) and one for particle 1 heading left (`.2`).
Each row's cells hold particle 2's right and left arrows. -/
abbrev Grid := List (Row × Row)

/-- Mix two rows place by place: `a − i·b` in both of particle 2's arrows. -/
def rowMix (a b : Row) : Row :=
  List.zipWith (fun c d => (c.1 - i * d.1, c.2 - i * d.2)) a b

/-- What particle 1 sends one place right: its right arrow carries on, its left arrow turns. -/
def sendR1 (p : Row × Row) : Row := rowMix p.1 p.2

/-- What particle 1 sends one place left. -/
def sendL1 (p : Row × Row) : Row := rowMix p.2 p.1

/-- A row of empty cells. -/
def zeroRow (m : Nat) : Row := List.replicate m (0, 0)

/-- How many places particle 2 has. -/
def width : Grid → Nat
  | [] => 0
  | p :: _ => p.1.length

/-- **Particle 1's tick**: the checkerboard step on particle 1's place and direction. -/
def tick1 (g : Grid) : Grid :=
  List.zip ([zeroRow (width g), zeroRow (width g)] ++ g.map sendR1)
    (g.map sendL1 ++ [zeroRow (width g), zeroRow (width g)])

/-- **Particle 2's tick**: the checkerboard step on every one of particle 2's rows. -/
def tick2 (g : Grid) : Grid := g.map fun p => (tick p.1, tick p.2)

/-- The total of all the arrows' squared sizes. -/
def totalG (g : Grid) : Int := (g.map (fun p => total p.1)).sum + (g.map (fun p => total p.2)).sum

/-- Particle 1's own odds (as tickets): for each of its places, everything in its two rows. -/
def marg1 (g : Grid) : List Int := g.map fun p => total p.1 + total p.2

/-! ## 1. The total is kept -/

theorem tick2_total (g : Grid) : totalG (tick2 g) = 2 * totalG g := by
  induction g with
  | nil => rfl
  | cons p ps ih =>
    simp only [tick2, totalG, List.map_cons, List.sum_cons, total_tick] at ih ⊢
    omega

theorem total_zeroRow (m : Nat) : total (zeroRow m) = 0 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [zeroRow, List.replicate_succ, total, List.map_cons, List.sum_cons] at ih ⊢
    rw [nsq_zero]; omega

theorem rowMix_total (a b : Row) (hl : a.length = b.length) :
    total (rowMix a b) + total (rowMix b a) = 2 * (total a + total b) := by
  induction a generalizing b with
  | nil => cases b with
    | nil => rfl
    | cons d ds => simp at hl
  | cons c cs ih => cases b with
    | nil => simp at hl
    | cons d ds =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      have h := ih ds hl
      have s1 := send_size (c.1, d.1)
      have s2 := send_size (c.2, d.2)
      simp only [sendR, sendL, cellSize] at s1 s2
      simp only [rowMix, List.zipWith_cons_cons, total, List.map_cons, List.sum_cons] at h ⊢
      omega

theorem sum_send1 (g : Grid) (h : ∀ p ∈ g, p.1.length = p.2.length) :
    (g.map (fun p => total (sendR1 p))).sum + (g.map (fun p => total (sendL1 p))).sum =
      2 * totalG g := by
  induction g with
  | nil => rfl
  | cons p ps ih =>
    have hp := rowMix_total p.1 p.2 (h p List.mem_cons_self)
    have hs := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
    simp only [sendR1, sendL1, totalG, List.map_cons, List.sum_cons] at hs hp ⊢
    omega

/-- **Particle 1's tick exactly doubles the total** (each pair of rows having one width). -/
theorem tick1_total (g : Grid) (h : ∀ p ∈ g, p.1.length = p.2.length) :
    totalG (tick1 g) = 2 * totalG g := by
  have h1 : (tick1 g).map Prod.fst = [zeroRow (width g), zeroRow (width g)] ++ g.map sendR1 := by
    unfold tick1; apply List.map_fst_zip; simp
  have h2 : (tick1 g).map Prod.snd = g.map sendL1 ++ [zeroRow (width g), zeroRow (width g)] := by
    unfold tick1; apply List.map_snd_zip; simp
  have e1 : (tick1 g).map (fun p => total p.1) = ((tick1 g).map Prod.fst).map total := by
    simp [List.map_map, Function.comp_def]
  have e2 : (tick1 g).map (fun p => total p.2) = ((tick1 g).map Prod.snd).map total := by
    simp [List.map_map, Function.comp_def]
  have hs := sum_send1 g h
  unfold totalG at hs ⊢
  rw [e1, e2, h1, h2]
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, total_zeroRow, List.map_map, Function.comp_def]
  omega

/-! ## 2. No messages -/

/-- **No messages.** Do anything at all to particle 2 alone, as long as it keeps particle 2's
total (up to the same whole-number factor everywhere, such as one floor per tick): particle
1's own odds are unchanged, up to that same factor. -/
theorem no_messages (op : Row → Row) (c : Int) (hop : ∀ r, total (op r) = c * total r)
    (g : Grid) : marg1 (g.map fun p => (op p.1, op p.2)) = (marg1 g).map fun v => c * v := by
  induction g with
  | nil => rfl
  | cons p ps ih =>
    simp only [marg1, List.map_cons, hop] at ih ⊢
    rw [ih, Int.mul_add]

/-- Moving particle 2 one tick changes particle 1's odds only by the floor (a factor of 2). -/
theorem tick2_no_messages (g : Grid) : marg1 (tick2 g) = (marg1 g).map fun v => 2 * v :=
  no_messages tick 2 total_tick g

/-! ## 3. A linked pair is one thing -/

theorem nsq_mul (z w : Spot) : nsq (z * w) = nsq z * nsq w := by
  simp only [nsq, Spot.mul_re, Spot.mul_im]
  grind

theorem spot_eq_zero (z : Spot) (h : nsq z = 0) : z = 0 := by
  have hr := msq_nonneg z.re
  have hi := msq_nonneg z.im
  simp only [nsq] at h
  have h1 : z.re * z.re = 0 := by omega
  have h2 : z.im * z.im = 0 := by omega
  ext
  · exact msq_eq_zero _ h1
  · exact msq_eq_zero _ h2

/-- Two spots multiply to zero only if one of them is zero. -/
theorem spot_mul_eq_zero (z w : Spot) (h : z * w = 0) : z = 0 ∨ w = 0 := by
  have hn : nsq z * nsq w = 0 := by rw [← nsq_mul, h]; decide
  rcases Int.mul_eq_zero.mp hn with h1 | h1
  · exact Or.inl (spot_eq_zero z h1)
  · exact Or.inr (spot_eq_zero w h1)

theorem zero_mul' (w : Spot) : (0 : Spot) * w = 0 := by ext <;> simp

/-- The linked pair, in one pair-cell: "particle 1 heading right and particle 2 heading left"
minus "particle 1 heading left and particle 2 heading right". -/
def linked : Grid := [([((0 : Spot), (1 : Spot))], [((-1 : Spot), (0 : Spot))])]

/-- **A linked pair can't be split.** There are no arrows `a` for particle 1 (right, left) and
`b` for particle 2 (right, left) whose products give the linked pair's four arrows. -/
theorem linked_cannot_split :
    ¬ ∃ a b : Cell, a.1 * b.1 = 0 ∧ a.1 * b.2 = 1 ∧ a.2 * b.1 = -1 ∧ a.2 * b.2 = 0 := by
  rintro ⟨a, b, h1, h2, h3, _⟩
  rcases spot_mul_eq_zero _ _ h1 with ha | hb
  · rw [ha, zero_mul'] at h2
    have := congrArg Spot.re h2
    simp at this
  · rw [hb, Spot.mul_zero] at h3
    have := congrArg Spot.re h3
    simp at this

/-- The linked pair's four arrows are exactly those in the theorem above. -/
theorem linked_arrows :
    linked = [([((0 : Spot), (1 : Spot))], [((-1 : Spot), (0 : Spot))])] := rfl

/-! ## 4. Who moves first doesn't matter (checked by running) -/

/-- **Checked by running**, on the linked pair for two rounds: particle 1 then particle 2
gives exactly the same arrows as particle 2 then particle 1. -/
theorem order_doesnt_matter :
    tick1 (tick2 (tick1 (tick2 linked))) = tick2 (tick1 (tick2 (tick1 linked))) := by
  decide +kernel

end Building
