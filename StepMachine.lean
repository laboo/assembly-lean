import StreamMachine
import LandMachine

/-!
# The step rule, a toy (plain Lean, no math library)

Everyday-language summary (for the author):

* **Space here is a row of cells** (one direction only, a toy). Each cell holds **two
  arrows**: one heading right and one heading left. Two are forced: a rule that keeps the
  total and only looks at neighbors can't work with one arrow per cell (Meyer, 1996).
* **One tick:** every arrow either carries on or turns around, and turning costs a quarter
  turn. Then every arrow steps one cell the way it is heading. This is Feynman's
  checkerboard (1965), today called a quantum walk.
* **Whole numbers only.** The machine adds and turns by quarter turns, nothing else. The
  exact rule also shrinks every arrow by 1/√2 each tick, which is the size of one floor's
  shrink, so instead of shrinking, the machine keeps whole numbers and each tick is read
  **one floor finer**. Each tick climbs one floor.
* Lean checks, in whole numbers:
  1. nothing moves faster than one cell per tick (the row grows by exactly one cell at each
     end per tick),
  2. the total of the arrows' squared sizes exactly doubles each tick, which read one floor
     finer means it never changes (the odds always add up to one),
  3. the run can be reversed exactly: undoing a tick gives back every arrow, doubled.
* **Landing.** Starting from a single arrow of size 1, after `t` ticks the squared sizes add
  up to exactly `2^t`: think of them as `2^t` tickets, each cell holding as many tickets as
  its squared size. So exactly `t` fair coin flips pick a ticket, and the particle lands in
  the cell that holds it: one coin flip per floor climbed. The odds (squared size) are the
  model's open question, used here as a labeled placeholder.

The link to Mathlib's complex plane is in `BuildingStep.lean`.
-/

namespace Building

open Spot

/-- A cell: the arrow heading right (`.1`) and the arrow heading left (`.2`). -/
abbrev Cell := Spot × Spot

/-- A row of cells, leftmost first. -/
abbrev Row := List Cell

/-- What a cell sends one cell to the right: its right arrow carries on, and its left arrow
turns around, costing a quarter turn (`−i`). -/
def sendR (c : Cell) : Spot := c.1 - i * c.2

/-- What a cell sends one cell to the left: its left arrow carries on, and its right arrow
turns around, costing a quarter turn (`−i`). -/
def sendL (c : Cell) : Spot := c.2 - i * c.1

/-- **One tick.** Every cell sends to its neighbors; each new cell's right arrow comes only
from the cell on its left, and its left arrow only from the cell on its right. The row grows
by one cell at each end. -/
def tick (row : Row) : Row :=
  List.zip ([0, 0] ++ row.map sendR) (row.map sendL ++ [0, 0])

/-- `t` ticks. -/
def run : Nat → Row → Row
  | 0, row => row
  | t + 1, row => tick (run t row)

/-- A cell's squared size: the squared sizes of its two arrows (its number of tickets). -/
def cellSize (c : Cell) : Int := nsq c.1 + nsq c.2

/-- The total of all the arrows' squared sizes. -/
def total (row : Row) : Int := (row.map (fun c => nsq c.1)).sum + (row.map (fun c => nsq c.2)).sum

/-! ## 1. Nothing moves faster than one cell per tick -/

theorem tick_length (row : Row) : (tick row).length = row.length + 2 := by
  simp [tick, List.length_zip]

/-- **The row grows by exactly one cell at each end per tick**: after `t` ticks, nothing has
moved more than `t` cells. -/
theorem run_length (t : Nat) (row : Row) : (run t row).length = row.length + 2 * t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [run, tick_length, ih]; omega

/-! ## 2. The total doubles exactly each tick -/

/-- The heart of it, for one cell: what it sends right and left has exactly twice its
squared size. -/
theorem send_size (c : Cell) : nsq (sendR c) + nsq (sendL c) = 2 * cellSize c := by
  simp only [nsq, sendR, sendL, cellSize, Spot.sub_re, Spot.sub_im, Spot.mul_re, Spot.mul_im,
    Spot.i_re, Spot.i_im]
  grind

theorem nsq_zero : nsq (0 : Spot) = 0 := by decide

theorem sum_send (row : Row) :
    (row.map (fun c => nsq (sendR c))).sum + (row.map (fun c => nsq (sendL c))).sum =
      2 * total row := by
  induction row with
  | nil => simp [total]
  | cons c cs ih =>
    simp only [total, List.map_cons, List.sum_cons] at ih ⊢
    have h := send_size c
    simp only [cellSize] at h
    omega

/-- **The total exactly doubles each tick.** Read one floor finer (each floor's shrink halves
squared sizes), it never changes. -/
theorem total_tick (row : Row) : total (tick row) = 2 * total row := by
  have h1 : ((tick row).map Prod.fst) = [0, 0] ++ row.map sendR := by
    unfold tick; apply List.map_fst_zip; simp
  have h2 : ((tick row).map Prod.snd) = row.map sendL ++ [0, 0] := by
    unfold tick; apply List.map_snd_zip; simp
  have e1 : (tick row).map (fun c => nsq c.1) = ((tick row).map Prod.fst).map nsq := by
    simp [List.map_map, Function.comp_def]
  have e2 : (tick row).map (fun c => nsq c.2) = ((tick row).map Prod.snd).map nsq := by
    simp [List.map_map, Function.comp_def]
  have hs := sum_send row
  unfold total at hs ⊢
  rw [e1, e2, h1, h2]
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, nsq_zero, List.map_map, Function.comp_def]
  omega

/-- After `t` ticks the total is `2^t` times the start: read `t` floors finer, unchanged. -/
theorem total_run (t : Nat) (row : Row) : total (run t row) = 2 ^ t * total row := by
  induction t with
  | zero => simp [run]
  | succ t ih => rw [run, total_tick, ih, Int.pow_succ]; grind

/-! ## 3. The run can be reversed exactly -/

/-- Undo a tick: each old cell is worked out from what its two neighbors received. The
result is the old row with every arrow doubled (a whole-number factor, so nothing is lost). -/
def untick (row : Row) : Row :=
  List.zipWith (fun a c => (a + i * c, i * a + c)) ((row.map Prod.fst).drop 2) (row.map Prod.snd)

theorem unsend (c : Cell) : (sendR c + i * sendL c, i * sendR c + sendL c) = (c.1 + c.1, c.2 + c.2) := by
  simp only [sendR, sendL, Prod.mk.injEq]
  constructor <;> ext <;> simp <;> grind

theorem zipWith_send (row : Row) :
    List.zipWith (fun a c => (a + i * c, i * a + c)) (row.map sendR) (row.map sendL ++ [0, 0]) =
      row.map (fun c => (c.1 + c.1, c.2 + c.2)) := by
  induction row with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.map_cons, List.cons_append, List.zipWith_cons_cons, ih, unsend]

/-- **Undoing a tick gives back every arrow, doubled.** -/
theorem untick_tick (row : Row) : untick (tick row) = row.map (fun c => (c.1 + c.1, c.2 + c.2)) := by
  have h1 : ((tick row).map Prod.fst) = [0, 0] ++ row.map sendR := by
    unfold tick; apply List.map_fst_zip; simp
  have h2 : ((tick row).map Prod.snd) = row.map sendL ++ [0, 0] := by
    unfold tick; apply List.map_snd_zip; simp
  unfold untick
  rw [h1, h2]
  simpa using zipWith_send row

/-! ## 4. Landing: one coin flip per floor -/

/-- A single arrow of size 1, heading right, in a row of one cell. -/
def start : Row := [((1 : Spot), (0 : Spot))]

theorem total_start : total start = 1 := by decide

/-- **From a single arrow, after `t` ticks there are exactly `2^t` tickets.** -/
theorem tickets_run (t : Nat) : total (run t start) = 2 ^ t := by
  rw [total_run, total_start, Int.mul_one]

/-- Which cell holds ticket number `k` (cells counted from the left, each holding as many
tickets as its squared size). -/
def landAt : Row → Int → Nat
  | [], _ => 0
  | c :: cs, k => if k < cellSize c then 0 else landAt cs (k - cellSize c) + 1

/-- The ticket picked by `t` coin flips: the flips are its binary digits. -/
def ticketOf (coin : Coin) : Nat → Int
  | 0 => 0
  | t + 1 => 2 * ticketOf coin t + (if coin t then 1 else 0)

/-- **Landing**: after `t` ticks, `t` coin flips pick the cell the particle lands in. -/
def landCell (t : Nat) (coin : Coin) : Nat := landAt (run t start) (ticketOf coin t)

/-- Every ticket a chain of `t` flips can pick is one of the `2^t`. -/
theorem ticketOf_range (coin : Coin) (t : Nat) : 0 ≤ ticketOf coin t ∧ ticketOf coin t < 2 ^ t := by
  induction t with
  | zero => simp [ticketOf]
  | succ t ih =>
    simp only [ticketOf, Int.pow_succ]
    split <;> omega

/-- For each cell, how many of the `2^t` tickets land there. -/
def landCounts (t : Nat) : List Nat :=
  let row := run t start
  (List.range row.length).map fun j =>
    ((List.range (2 ^ t)).filter fun (k : Nat) => landAt row (Int.ofNat k) == j).length

/-- The tickets each cell holds, as counts. -/
def ticketCounts (t : Nat) : List Nat := (run t start).map fun c => (cellSize c).toNat

/-- **Checked by running every chain of 6 flips:** each cell is landed in by exactly as many
chains of coin flips as it holds tickets. -/
theorem landing_matches_tickets_6 : landCounts 6 = ticketCounts 6 := by decide +kernel

end Building
