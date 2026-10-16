import FullMachine

/-!
# The address finder (plain Lean, no math library)

Hand the machine a point and it climbs, writing the point's endless address one floor at
a time.

How a point is handed over: a program can't take an arbitrary point "all at once", since
most points need endlessly many digits to write down. So a point comes as a rule `ap`:
asked for precision `m`, it answers with a whole-number spot `G` and a grid `d`, meaning
the point `G / 2^d`, within `1 / 2^m` of the true point (Bishop's way of handing over a
number, with halving grids).

On each floor the finder asks for a good enough approximation, works out (in whole
numbers) where the point sits relative to the digits written so far, and applies the same
star digit rule the multiplier uses. The star's wiggle room absorbs the approximation's
small error, so rough approximations are enough.

The proof that the address names the point is in `BuildingFind.lean`.
-/

namespace Building

/-- A point handed over as approximations: `ap m = (G, d)` names `G / 2^d`, which must be
within `1 / 2^m` of the point. -/
abbrev Approx := Nat → Spot × Nat

/-- How much precision floor `k` asks for. -/
def findPrec (k : Nat) : Nat := 2 * k + 7

/-- The whole-number picture of where the point sits on floor `k`, given the digits written
so far (read as the whole-number spot `P`): the numerator over `2^d`. -/
def findNum (ap : Approx) (k : Nat) (P : Spot) : Spot :=
  spow b (k + 1) * (ap (findPrec k)).1 - ⟨(2 : Int) ^ (ap (findPrec k)).2, 0⟩ * (b * P)

/-- The digits written so far, read as one whole-number spot. -/
def findP (ap : Approx) : Nat → Spot
  | 0 => 0
  | k + 1 => b * findP ap k + (starRule (findNum ap k (findP ap k)) (ap (findPrec k)).2).toSpot

/-- **The endless address of the point**, one floor at a time. -/
def findE (ap : Approx) : Endless :=
  fun k => starRule (findNum ap k (findP ap k)) (ap (findPrec k)).2

theorem findP_eq_horner (ap : Approx) (k : Nat) : findP ap k = horner (findE ap) k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [findP, horner, ih, findE]

/-! ## Any point in the plane -/

/-- Approximations of the point moved up `K` floors (shrunk and turned by `K` twists),
worked out from approximations of the point itself. -/
def shiftApprox (ap : Approx) (K : Nat) : Approx :=
  fun m => (spow cbar K * (ap m).1, (ap m).2 + K)

/-- How many floors to move a point up so it sits well inside the star: twice the number
of binary digits of three times a rough size of the point. -/
def findShift (ap : Approx) : Nat :=
  let G := (ap 0).1
  let M := G.re.natAbs + G.im.natAbs + 2 ^ (ap 0).2
  2 * ((3 * M).log2 + 1)

/-- **The full address of any point of the plane**: move the point up until it sits inside
the star, find its endless address, then move those first floors back down above the
point. -/
def findFull (ap : Approx) : Full :=
  let K := findShift ap
  let t := findE (shiftApprox ap K)
  let arr := memoArr t (horizon + K + 24)
  lift (fun n => lookupOr arr t n) K

end Building
