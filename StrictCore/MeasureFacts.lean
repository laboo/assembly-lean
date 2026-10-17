/-
  THE STRICT CORE, part 4: what the measurement rule gives, checked by Lean.   Model v4.1.0.

  These are the core's own computations, not comparisons with observation; the referee does the
  comparing. Where the result happens to equal a known law, the comment names the law, so a
  reader can see what will be compared.
-/
import StrictCore.Measure

namespace StrictCore

set_option maxRecDepth 100000

/-- Magnet axes with whole-number lengths, used for the checks below. -/
def testAxes : List (List Int × Int) :=
  [([0,0,1],1), ([1,0,0],1), ([0,1,0],1), ([0,0,-1],1), ([3,0,4],5), ([0,3,4],5),
   ([1,2,2],3), ([2,3,6],7), ([-2,1,2],3)]

-- Every axis above really has the whole-number length given.
theorem testAxes_whole : testAxes.all (fun (m, L) => wholeLength m L) = true := by decide

/-- The four reference turnings tried for the thing's free side. -/
def testJs : List C := [piece 3 3, piece 3 5, piece 3 6, scale (-1) (piece 3 3)]

/-- Odds of "up" for thing `x` under a magnet with axis `m` of whole length `L`, from the "up"
    shadow alone: (|up shadow|^2, (2L)^2 |x|^2). -/
def upOdds (J : C) (m : List Int) (L : Int) (x : C) : Int × Int :=
  (len2 (flat J m L 1 x), 4 * L * L * len2 x)

/-- For a thing on our floor: prepare "up" with a magnet along n, then measure with a magnet
    along m. Check (1) the odds are the same for every reference turning J, and (2) they equal
    (1 + cos of the angle between n and m) / 2. (For the core's own J, `OddsFacts.lean` proves
    (2) for every pair of axes; this check is what still covers the other three J's.) -/
def thingCheck : Bool :=
  testAxes.all fun (n, Ln) => testAxes.all fun (m, Lm) =>
    let os := testJs.map fun J => upOdds J m Lm (preparedUp J n Ln)
    let nm := (List.zipWith (· * ·) n m).foldl (· + ·) 0
    os.all (fun o => sameOdds o (Ln * Lm + nm, 2 * Ln * Lm))

-- 81 prepare-then-measure pairs, four choices of J each: the reference turning never changes a
-- result (so it is a convention, not a knob), and the odds are (1 + cos)/2 -- the observed law
-- for the electron's spin (to be compared by the referee).
theorem thing_odds : thingCheck = true := by decide +kernel

-- A thing after one full turn is minus itself (part 2), but minus a thing gives the same odds
-- under every magnet: the sign is invisible to one particle alone. Seeing it needs two paths
-- recombined, which needs motion -- a hard stop.
theorem full_turn_invisible_alone :
    testAxes.all (fun (m, L) =>
      sameOdds (upOdds refJ m L (preparedUp refJ [0,0,1] 1))
               (upOdds refJ m L (scale (-1) (preparedUp refJ [0,0,1] 1)))) = true := by
  decide +kernel

-- Light (an operation that is a direction of the plane floor) through two polarizers at an angle
-- whose cosine is 3/5: odds 9/25, the square of the cosine (Malus's law, to be compared).
theorem polarizer_3_4 : sameOdds (polarAlong [1,0] [3,4]) (9, 25) = true := by decide
theorem polarizer_same : sameOdds (polarAlong [1,0] [1,0]) (1, 1) = true := by decide
theorem polarizer_crossed : sameOdds (polarAlong [1,0] [0,1]) (0, 1) = true := by decide

-- An operation that is a direction of our floor (the W or Z as placed), measured by a magnet:
-- only TWO answers exist, "left alone" (along the axis) and "turned" (across it). Odds of
-- "left alone" at an angle with cosine 4/5: 16/25.
theorem op_magnet_4_5 : sameOdds (opAlone [0,0,1] [3,0,4]) (16, 25) = true := by decide

end StrictCore
