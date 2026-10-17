/-
  THE STRICT CORE, part 1: the compass.            Model v4.1.0 (its rules unchanged since v4.0.0, approved Oct 16, 2026).

  Everyday language first:
  * A floor has n directions. Every direction is alike: each one, multiplied by itself, gives 1.
  * The compass on a floor is everything its directions make when multiplied together.
    Each piece of the compass is a set of directions (written as a bit pattern), so floor n
    has 2^n pieces: the plain number, the directions, the turnings (two directions), and so on.
  * A compass number is a list of whole numbers, one for each piece. No decimals anywhere.
  * Rule 3 of the rulebook: a THING uses everything its floor's turnings make when
    multiplied together -- the pieces built from an even number of directions.
  * Rule 4: a turn is multiplying by a piece of the compass. A thing is multiplied from one
    side; an operation from both sides.

  Nothing in this file is tuned to any particle. There are no speeds, no circles, no copies.
-/
namespace StrictCore

/-! ## Pieces of the compass -/

/-- Is direction `i` part of piece `a`? -/
def has (a i : Nat) : Bool := (a / 2 ^ i) % 2 == 1

/-- How many directions piece `a` is made of, on a floor with `n` directions. -/
def size (n a : Nat) : Nat := ((List.range n).filter (has a ·)).length

/-- Multiplying piece `a` by piece `b` means putting the directions in order; each swap of two
    different directions flips the sign. This counts the swaps. -/
def swaps (n a b : Nat) : Nat :=
  (List.range n).foldl
    (fun acc j => if has b j then acc + ((List.range n).filter (fun i => i > j && has a i)).length
                  else acc) 0

/-- The sign that comes from multiplying piece `a` by piece `b`. (A direction times itself is 1,
    so shared directions drop out with no extra sign.) -/
def sign (n a b : Nat) : Int := if swaps n a b % 2 == 0 then 1 else -1

/-! ## Compass numbers: one whole number per piece -/

/-- A compass number on a floor with `n` directions: `2^n` whole numbers, piece `a` at index `a`. -/
abbrev C := List Int

def coef (x : C) (a : Nat) : Int := x.getD a 0

/-- The compass number that is just piece `a` (with coefficient 1). -/
def piece (n a : Nat) : C := (List.range (2 ^ n)).map fun c => if c == a then 1 else 0

def plain (n : Nat) (k : Int) : C := (List.range (2 ^ n)).map fun c => if c == 0 then k else 0

def add (x y : C) : C := List.zipWith (· + ·) x y
def scale (k : Int) (x : C) : C := x.map (k * ·)

/-- Multiplying two compass numbers: every piece of `x` times every piece of `y`.
    Piece `a` times piece `b` is piece `a xor b`, with the sign from the swaps. -/
def mul (n : Nat) (x y : C) : C :=
  (List.range (2 ^ n)).map fun c =>
    (List.range (2 ^ n)).foldl (fun acc a =>
      let b := a ^^^ c
      acc + sign n a b * coef x a * coef y b) 0

/-- Reversing the order of every product (one of the compass's built-in mirrors). -/
def rev (n : Nat) (x : C) : C :=
  (List.range (2 ^ n)).map fun a =>
    let k := size n a
    (if (k * (k - 1) / 2) % 2 == 0 then 1 else -1) * coef x a

/-- Flipping every direction (another built-in mirror). -/
def flip (n : Nat) (x : C) : C :=
  (List.range (2 ^ n)).map fun a => (if size n a % 2 == 0 then 1 else -1) * coef x a

/-- The whole squared length: the sum of the squares of the whole numbers. -/
def len2 (x : C) : Int := x.foldl (fun acc v => acc + v * v) 0

/-! ## Rule 3: what a thing may use -/

/-- A thing may use only pieces made of an even number of directions: everything the turnings make
    when multiplied together. Anything else is a spare piece, and no input may give it a job. -/
def isThing (n : Nat) (x : C) : Bool :=
  x.length == 2 ^ n &&
  (List.range (2 ^ n)).all fun a => size n a % 2 == 0 || coef x a == 0

/-- How many pieces a thing may use on a floor: counted, not set. -/
def thingWidth (n : Nat) : Nat := ((List.range (2 ^ n)).filter (fun a => size n a % 2 == 0)).length

/-! ## Rule 4: turning -/

/-- A turn is a compass number (built from an even number of directions). A thing is turned by
    multiplying it from one side. -/
def turnThing (n : Nat) (r x : C) : C := mul n r x

/-- An operation is turned from both sides, so that a turned operation still acts correctly on
    turned things. -/
def turnOp (n : Nat) (r a : C) : C := mul n (mul n r a) (rev n r)

/-- A quarter turn in the plane of directions `i` and `j`: the plain number plus that turning.
    (Exact in whole numbers; it also grows lengths by a fixed factor, which odds never see.) -/
def quarter (n i j : Nat) : C := add (plain n 1) (piece n (2 ^ i + 2 ^ j))

/-- Apply the same turn `k` times. -/
def rep (f : C → C) : Nat → C → C
  | 0, x => x
  | k + 1, x => rep f k (f x)

end StrictCore
