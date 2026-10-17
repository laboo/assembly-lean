/-
  THE STRICT CORE, part 3: measurement and odds (rules 5 and 6).      Model v4.0.0.

  Everyday language:
  * A measurement is one piece of the compass, set by what the device is made of.
    A polarizer (a slot of wires) is a DIRECTION. A magnet (circling current) is a TURNING:
    the plane across its axis.
  * Its answers are the parts of the particle that piece leaves alone (only flipped or only turned).
  * Odds = squared length of the shadow on an answer's part, out of the whole squared length.
    Every odds is two whole numbers: a part and a whole.

  NAMED, NOT HIDDEN: reading a THING's answer with a magnet needs one reference turning on the
  thing's free side (its right side), which plays the role of the wave's i. The core fixes it once
  (`refJ`, the turning of directions 0 and 1) and Lean checks below that prepare-then-measure odds
  come out the same whichever turning is used. A choice that cannot change any result is a
  convention, not a knob.

  WHOLE NUMBERS: a magnet's axis must have a whole-number length (like 3, 4 -> 5). Other axes
  would need square roots, so the core refuses them rather than rounding.
-/
import StrictCore.Compass

namespace StrictCore

/-- Dot product of two compass numbers (the shadow of one on the other, unsquared). -/
def dot (x y : C) : Int := (List.zipWith (· * ·) x y).foldl (· + ·) 0

/-- A direction of our floor from three whole numbers. -/
def dir3 (m : List Int) : C := [0, m.getD 0 0, m.getD 1 0, 0, m.getD 2 0, 0, 0, 0]

/-- A magnet with axis `m` is the turning across that axis: the axis times the volume piece. -/
def magnet (m : List Int) : C := mul 3 (dir3 m) (piece 3 7)

/-- The one fixed reference turning on a thing's free side (see the note above). -/
def refJ : C := piece 3 3

/-- The answer-sorting map for a thing under a magnet: minus (magnet * thing * J).
    Parts it leaves alone are "up"; parts it flips are "down". -/
def sortThing (J : C) (m : List Int) (x : C) : C := scale (-1) (mul 3 (mul 3 (magnet m) x) J)

/-- Odds of "up" for thing `x` under a magnet with axis `m` of whole length `L`:
    (part, whole) = (L|x|^2 + <x, sort x>,  2 L |x|^2). -/
def thingUp (J : C) (m : List Int) (L : Int) (x : C) : Int × Int :=
  (L * len2 x + dot x (sortThing J m x), 2 * L * len2 x)

/-- The thing a magnet with axis `m` (length `L`) leaves certain to read "up": the "up" part of
    the first basic thing-piece whose "up" part is not zero. (Any nonzero choice gives the same
    later odds, because the "up" part is one state up to its own turning.) -/
def preparedUp (J : C) (m : List Int) (L : Int) : C :=
  let tries := [0, 3, 5, 6].map fun a =>
    add (scale L (piece 3 a)) (sortThing J m (piece 3 a))
  (tries.find? (fun t => len2 t != 0)).getD (plain 3 0)

/-- Does an axis have whole-number length `L`? -/
def wholeLength (m : List Int) (L : Int) : Bool :=
  L > 0 && L * L == (m.map (fun v => v * v)).foldl (· + ·) 0

/-! ## Operations measured by a direction (a polarizer): along and across -/

/-- For an operation `a` on the plane floor and a polarizer direction `p` (both directions of
    that floor), odds of "along": the mirror p a p leaves the along-part alone and flips the
    across-part. (part, whole) = (| |p|^2 a + p a p |^2,  4 |p|^4 |a|^2). -/
def dir2 (p : List Int) : C := [0, p.getD 0 0, p.getD 1 0, 0]

def polarAlong (p a : List Int) : Int × Int :=
  let P := dir2 p
  let A := dir2 a
  let mirrored := mul 2 (mul 2 P A) P
  let along2 := add (scale (len2 P) A) mirrored
  (len2 along2, 4 * len2 P * len2 P * len2 A)

/-! ## Operations measured by a turning (a magnet): left alone or turned -/

/-- For an operation that is a direction `a` of our floor and a magnet with axis `m`:
    the magnet turns the operation from both sides. The part along the axis is left alone;
    the part across it is turned (half a turn). Odds of "left alone". -/
def opAlone (m a : List Int) : Int × Int :=
  let B := magnet m
  let A := dir3 a
  let turned := mul 3 (mul 3 B A) (rev 3 B)
  let alone2 := add (scale (len2 B) A) turned
  (len2 alone2, 4 * len2 B * len2 B * len2 A)

/-- Two fractions are equal (cross-multiplied, whole numbers only). -/
def sameOdds (p q : Int × Int) : Bool := p.1 * q.2 == q.1 * p.2

end StrictCore
