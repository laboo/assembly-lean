import MulMachine
import FlipMachine

/-!
# Full addresses (plain Lean, no math library)

A **full address** holds one mirror digit (0, 1, −1, i or −i) on every floor:
finitely many floors above the point and endlessly many below. There is one digit
story everywhere. Above the point, every address also has a **tidy spelling** in plain
0s and 1s (Penney's, piece 1), and that is what arithmetic writes there.

Adding and multiplying full addresses uses only the machines already built:
the plain 0/1 adder and multiplier above the point (after tidying), and the endless
adder and multiplier below it. When an endless answer comes out written some floors higher,
those top floors simply move above the point.

The proof that this lands on Mathlib's sum and product, everywhere in the plane,
is in `BuildingFull.lean`.
-/

namespace Building

/-- A full address: mirror digits on every floor, finitely many above the point
(ground floor first) and endlessly many below. -/
structure Full where
  whole : List MDigit
  tail : Endless

/-- The tidy plain 0/1 spelling of the floors above the point. -/
def tidy (ds : List MDigit) : List Bool := address (valueM ds)

/-- Plain 0s and 1s, written as mirror digits. -/
def plainM (ds : List Bool) : List MDigit := ds.map MDigit.ofBool

/-- Work out the first `n` digits of an endless address once and keep them in a list. -/
def memoArr (x : Endless) (n : Nat) : Array MDigit := Array.ofFn (n := n) (fun i => x i)

/-- Look a digit up in the kept list if it is there; otherwise work it out. -/
def lookupOr (arr : Array MDigit) (x : Endless) (k : Nat) : MDigit :=
  if h : k < arr.size then arr[k] else x k

/-- Keeping digits changes nothing about the address; it only saves time when running. -/
theorem lookupOr_memoArr (x : Endless) (n : Nat) : lookupOr (memoArr x n) x = x := by
  funext k
  unfold lookupOr memoArr
  split <;> simp

/-- How many digits to remember at each step when running. -/
def horizon : Nat := 100

/-- The endless address of zero. -/
def zeroE : Endless := fun _ => .zero

/-- Zero, as a full address. -/
def Full.zero : Full := ⟨[], zeroE⟩

/-- An endless address read `j` floors higher: its first `j` floors move above the point
(rewritten in plain 0s and 1s), and the rest stays below. -/
def lift (t : Endless) (j : Nat) : Full := ⟨plainM (address (horner t j)), fun n => t (n + j)⟩

/-- **Adding full addresses.** Above the point: the plain 0/1 adder. Below the point: the
endless adder, whose answer comes out six floors higher, so its top six floors move up. -/
def fullAddH (H : Nat) (A B : Full) : Full :=
  let E := addE A.tail B.tail
  let arr := memoArr E (H + 6)
  ⟨plainM (addA (addA (tidy A.whole) (tidy B.whole)) (address (horner (lookupOr arr E) 6))),
    fun n => lookupOr arr E (n + 6)⟩

/-- Adding full addresses (remembering enough digits for `horizon` floors of the answer). -/
def fullAdd (A B : Full) : Full := fullAddH horizon A B

/-- Add up a list of full addresses. Each step inward remembers six more floors, because
the adder reads six floors further than it writes. -/
def sumFullH : Nat → List Full → Full
  | _, [] => Full.zero
  | H, A :: As => fullAddH H A (sumFullH (H + 6) As)

def sumFull (As : List Full) : Full := sumFullH horizon As

/-- One copy of the endless address `t`, lifted `j` floors, for every 1 in a plain address
(starting at floor `j`). This is how a whole number multiplies an endless address. -/
def liftsOf : List Bool → Endless → Nat → List Full
  | [], _, _ => []
  | d :: ds, t, j => (if d then [lift t j] else []) ++ liftsOf ds t (j + 1)

/-- **Multiplying full addresses**: (whole A + tail A) × (whole B + tail B), as four parts.
Whole × whole: the plain 0/1 multiplier. Tail × tail: the endless multiplier, whose answer
comes out twelve floors higher. Whole × tail: shifted copies of the tail, one per 1. -/
def fullMulH (H : Nat) (A B : Full) : Full :=
  let a := tidy A.whole
  let c := tidy B.whole
  let M := mulE A.tail B.tail
  let arr := memoArr M (H + 24)
  sumFullH H ([⟨plainM (mulA a c), zeroE⟩, lift (fun n => lookupOr arr M n) 12] ++
    liftsOf a B.tail 0 ++ liftsOf c A.tail 0)

def fullMul (A B : Full) : Full := fullMulH horizon A B

/-! ## The mirror flip of a full address -/

/-- Flip an endless address: floor `n + 1` below the point is mirrored and turned
three quarter turns per floor (the mirrored shrink is the shrink turned back a quarter). -/
def flipE (x : Endless) : Endless := fun n => (x n).flip.turnN ((3 * (n + 1)) % 4)

/-- **The mirror image of a full address**, worked out floor by floor with no carrying. -/
def flipFull (A : Full) : Full := ⟨flipWhole A.whole, flipE A.tail⟩

end Building
