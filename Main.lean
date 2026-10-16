import Building
import StreamMachine
import MulMachine
import FullMachine
import FlipMachine
import FindMachine
import LandMachine
import StepMachine
open Building Building.Spot

/-- Every other entry (the cells a particle can reach on this tick). -/
def everyOther (l : List Int) : List Int :=
  (List.range l.length).filterMap fun j => if j % 2 == 0 then l[j]? else none

/-- A plain coin-flip walk, for comparison: same moves, but each tick a fair coin decides
"carry on" or "turn", with no arrows. Counts out of `2^t` chains, cell by cell. -/
def plainWalk (t : Nat) : List Int :=
  let tickP (row : List (Int × Int)) : List (Int × Int) :=
    List.zip ([0, 0] ++ row.map (fun c => c.1 + c.2)) (row.map (fun c => c.1 + c.2) ++ [0, 0])
  let rec go : Nat → List (Int × Int) → List (Int × Int)
    | 0, row => row
    | n + 1, row => go n (tickP row)
  (go t [(1, 0)]).map fun c => c.1 + c.2

/-- Undo `n` ticks. -/
def runBack : Nat → Row → Row
  | 0, row => row
  | n + 1, row => runBack n (untick row)

/-- Write an address the usual way, biggest place first: the lowest floor first, the
ground floor last. -/
def showAddr (ds : List Bool) : String :=
  match trim ds with
  | [] => "0"
  | t => String.ofList (t.reverse.map fun d => if d then '1' else '0')

/-- Write a spot as `east + north·i`. -/
def showSpot (z : Spot) : String :=
  let sign := if z.im < 0 then "-" else "+"
  s!"{z.re} {sign} {z.im.natAbs}i"

def showDigit : MDigit → String
  | .zero => "0" | .one => "1" | .negOne => "-1" | .up => "i" | .down => "-i"

/-- A made-up endless address with no pattern to speak of (a simple scrambler). -/
def scrambled (seed : Nat) : Endless := fun n =>
  match ((n + seed) * 2654435761 / 65536) % 5 with
  | 0 => .zero | 1 => .one | 2 => .negOne | 3 => .up | _ => .down

/-- Read the first `n` floors of an endless address in ordinary floating-point numbers,
just to show the answer approximately: digit × (one floor's shrink)^floor. -/
def approx (x : Endless) (n : Nat) : Float × Float := Id.run do
  let mut re := 0.0
  let mut im := 0.0
  let mut pr := 1.0
  let mut pi := 0.0
  for k in List.range n do
    -- multiply the running power by one floor's shrink (−1 − i)/2
    let nr := (-pr + pi) / 2.0
    let ni := (-pr - pi) / 2.0
    pr := nr
    pi := ni
    let d := (x k).toSpot
    re := re + Float.ofInt d.re * pr - Float.ofInt d.im * pi
    im := im + Float.ofInt d.re * pi + Float.ofInt d.im * pr
  return (re, im)

/-- Exact whole-number check that the multiplier's leftover is inside the star on floor `k`. -/
def starOK (x y : Endless) (k : Nat) : Bool :=
  let G := spow cbar (mulShift + k) * (horner x k * horner y k - spow b (mulShift + k) * mulP x y k)
  let X : Int := G.re.natAbs
  let Y : Int := G.im.natAbs
  let T : Int := 2 * 2 ^ (mulShift + k)
  decide (4 * X - Y ≤ T) && decide (4 * Y - X ≤ T)

/-- Read a full address approximately: whole part exactly, endless part to 60 floors. -/
def approxFull (A : Full) : Float × Float :=
  let w := valueM A.whole
  let (tr, ti) := approx A.tail 60
  (Float.ofInt w.re + tr, Float.ofInt w.im + ti)

/-- Round `a / q` to the nearest whole number (q > 0). -/
def roundDiv (a q : Int) : Int := (2 * a + q) / (2 * q)

/-- √2 + i/3, handed over as approximations: on the grid of size `1/2^(m+1)`,
east is ⌊√2 · 2^(m+1)⌋ and north is 2^(m+1)/3 rounded. -/
def sqrt2PlusThird : Approx := fun m =>
  let e := m + 1
  (⟨(Nat.sqrt (2 * 4 ^ e) : Int), roundDiv ((2 : Int) ^ e) 3⟩, e)

/-- A rational point `(a + c i) / q`, handed over as approximations. -/
def ratPoint (a c q : Int) : Approx := fun m =>
  let e := m + 1
  (⟨roundDiv (a * 2 ^ e) q, roundDiv (c * 2 ^ e) q⟩, e)

/-- Search for a spot that, times its mirror image, gives `p` (a piece and its mirror). -/
def mirrorPiece (p : Nat) : Option Spot := Id.run do
  for a in List.range (p + 1) do
    for c in List.range (p + 1) do
      if a * a + c * c == p then return some ⟨a, c⟩
  return none

def range (n : Int) : List Int :=
  (List.range (2 * n.toNat + 1)).map fun (k : Nat) => (Int.ofNat k) - n

def main : IO Unit := do
  IO.println "== Addresses: one digit (0 or 1) per floor, lowest floor first, ground floor last =="
  let samples : List Spot :=
    [⟨0,0⟩, ⟨1,0⟩, ⟨2,0⟩, ⟨-1,0⟩, ⟨0,1⟩, ⟨0,-1⟩, ⟨-1,1⟩, ⟨2,1⟩, ⟨2,-1⟩, ⟨5,0⟩]
  for z in samples do
    IO.println s!"  {showSpot z}   ->   {showAddr (address z)}"

  IO.println ""
  IO.println "== Arithmetic done only on 0s and 1s, then read back =="
  let one := address 1
  let i' := address i
  let a := address ⟨2, 1⟩
  let a' := address ⟨2, -1⟩
  IO.println s!"  1 + 1          : {showAddr one} + {showAddr one} = {showAddr (addA one one)}   reads as {showSpot (value (addA one one))}"
  IO.println s!"  i × i          : {showAddr i'} × {showAddr i'} = {showAddr (mulA i' i')}   reads as {showSpot (value (mulA i' i'))}"
  IO.println s!"  (2+i) × (2−i)  : {showAddr a} × {showAddr a'} = {showAddr (mulA a a')}   reads as {showSpot (value (mulA a a'))}"

  IO.println ""
  IO.println "== Running every pair of spots with both coordinates from -8 to 8 =="
  let mut pairs := 0
  let mut addMiss := 0
  let mut mulMiss := 0
  let mut carryOut := 0
  let mut longest := 0
  for x1 in range 8 do
    for y1 in range 8 do
      for x2 in range 8 do
        for y2 in range 8 do
          let z : Spot := ⟨x1, y1⟩
          let w : Spot := ⟨x2, y2⟩
          let az := address z
          let aw := address w
          pairs := pairs + 1
          if trim (addA az aw) != address (z + w) then addMiss := addMiss + 1
          if trim (mulA az aw) != address (z * w) then mulMiss := mulMiss + 1
          for c in carryTrail (columns az aw) 0 do
            if !(carries.contains c) then carryOut := carryOut + 1
          longest := max longest (address (z * w)).length
  IO.println s!"  pairs run: {pairs}"
  IO.println s!"  sums that missed the plane's answer: {addMiss}"
  IO.println s!"  products that missed the plane's answer: {mulMiss}"
  IO.println s!"  carries outside the fifteen allowed: {carryOut}"
  IO.println s!"  floors in the longest product address: {longest}"

  IO.println ""
  IO.println "== Endless addresses: adding by climbing, one finer floor at a time =="
  let x : Endless := fun _ => .one
  let y : Endless := scrambled 7
  IO.println s!"  x, first 12 floors:   {(List.range 12).map (fun n => showDigit (x n))}"
  IO.println s!"  y, first 12 floors:   {(List.range 12).map (fun n => showDigit (y n))}"
  IO.println s!"  sum, first 12 floors: {(List.range 12).map (fun n => showDigit (addE x y n))}"
  IO.println s!"  floor 400 of the sum, asked for directly: {showDigit (addE x y 400)}"

  -- Whole-number check at every floor: (x read so far) + (y read so far) − 8i × (sum written so far)
  -- must equal the machine's small leftover exactly.
  let mut xi : Spot := 0
  let mut yi : Spot := 0
  let mut pi : Spot := 0
  let mut u : Spot := 0
  let mut ok := true
  let mut biggest : Nat := 0
  let x2 := scrambled 1
  let y2 := scrambled 2
  for k in List.range 300 do
    let s := (x2 k).toSpot + (y2 k).toSpot
    let (p, u') := addStep u s
    xi := b * xi + (x2 k).toSpot
    yi := b * yi + (y2 k).toSpot
    pi := b * pi + p.toSpot
    u := u'
    if xi + yi - twist6 * pi != u then ok := false
    biggest := max biggest (max u.re.natAbs u.im.natAbs)
  IO.println s!"  300 floors, exact whole-number check at every floor passed: {ok}"
  IO.println s!"  largest leftover coordinate seen: {biggest} (allowed: at most 5)"

  IO.println ""
  IO.println "== Endless addresses: multiplying by climbing, one finer floor at a time =="
  let mx := scrambled 3
  let my := scrambled 5
  let mp := mulE mx my
  IO.println s!"  product, floors 13 to 24: {(List.range 12).map (fun n => showDigit (mp (n + 12)))}"
  let starAll := (List.range 120).all (fun k => starOK mx my k)
  IO.println s!"  120 floors, leftover inside the star at every floor (exact check): {starAll}"
  let (xr, xi') := approx mx 60
  let (yr, yi') := approx my 60
  let (pr', pi') := approx mp 60
  IO.println s!"  x × y, read in ordinary decimals:          {xr * yr - xi' * yi'} + {xr * yi' + xi' * yr} i"
  IO.println s!"  −64 × (written product), read the same way: {-64.0 * pr'} + {-64.0 * pi'} i"

  IO.println ""
  IO.println "== Full addresses: whole-number floors in 0s and 1s, finer floors in mirror digits =="
  let fa : Full := ⟨plainM (address ⟨3, 2⟩), scrambled 3⟩
  let fb : Full := ⟨plainM (address ⟨-5, 4⟩), scrambled 8⟩
  let (ar, ai) := approxFull fa
  let (br, bi) := approxFull fb
  IO.println s!"  A = {ar} + {ai} i   (whole-number floors, tidy spelling: {showAddr (tidy fa.whole)})"
  IO.println s!"  B = {br} + {bi} i   (whole-number floors, tidy spelling: {showAddr (tidy fb.whole)})"
  let (sr, si) := approxFull (fullAdd fa fb)
  IO.println s!"  A + B by the building: {sr} + {si} i"
  IO.println s!"  A + B in decimals:     {ar + br} + {ai + bi} i"
  let (mr, mi) := approxFull (fullMulH 60 fa fb)
  IO.println s!"  A × B by the building: {mr} + {mi} i"
  IO.println s!"  A × B in decimals:     {ar * br - ai * bi} + {ar * bi + ai * br} i"

  IO.println ""
  IO.println "== The mirror flip, floor by floor, no carrying =="
  let ff := flipFull fa
  let (fr, fi) := approxFull ff
  IO.println s!"  flip of A by the building: {fr} + {fi} i   (A was {ar} + {ai} i)"
  IO.println s!"  A's whole-number floors, flipped (ground floor first): {(flipWhole fa.whole).map showDigit}"
  let (nr, ni) := approxFull (fullMulH 60 fa ff)
  IO.println s!"  A × flip(A) by the building: {nr} + {ni} i"
  IO.println s!"  A's squared size in decimals: {ar * ar + ai * ai}"

  IO.println ""
  IO.println "== Handing a point in: the address finder =="
  let fz := findFull sqrt2PlusThird
  let (zr, zi) := approxFull fz
  IO.println s!"  √2 + i/3 handed in as approximations; the building writes:"
  IO.println s!"    whole-number floors (tidy spelling): {showAddr (tidy fz.whole)}"
  IO.println s!"    first 12 finer floors: {(List.range 12).map (fun n => showDigit (fz.tail n))}"
  IO.println s!"    read back in decimals: {zr} + {zi} i   (√2 = 1.414214, 1/3 = 0.333333)"
  let fp := findFull (ratPoint 37 (-20) 7)
  let (pr2, pi2) := approxFull fp
  IO.println s!"  37/7 − (20/7) i handed in; read back: {pr2} + {pi2} i   (37/7 = 5.285714, 20/7 = 2.857143)"
  let (qr, qi) := approxFull (fullMulH 60 fz fp)
  IO.println s!"  their product by the building: {qr} + {qi} i"
  IO.println s!"  their product in decimals:     {zr * pr2 - zi * pi2} + {zr * pi2 + zi * pr2} i"

  IO.println ""
  IO.println "== Breaking apart: a piece times its mirror image =="
  for p in [2, 3, 5, 7, 11, 13, 17, 19, 23, 29] do
    match mirrorPiece p with
    | some π =>
      let check := π * π.flip
      IO.println s!"  {p} = ({showSpot π}) × ({showSpot π.flip})   check: {showSpot check}"
    | none => IO.println s!"  {p} does not break apart (it leaves remainder 3 when divided by 4)"

  IO.println ""
  IO.println "== Landing: one coin flip per floor =="
  let coin : Coin := fun n => ((n + 11) * 2654435761 / 65536) % 2 == 1
  let landed := land coin
  IO.println s!"  first 16 flips: {(List.range 16).map (fun n => if coin n then 1 else 0)}"
  for n in [4, 8, 16, 32] do
    let (lr, li) := approx landed n
    IO.println s!"  after {n} floors the landing spot is pinned to: {lr} + {li} i"
  let (fr2, fi2) := approx landed 60
  IO.println s!"  where it lands (60 floors):                   {fr2} + {fi2} i"

  IO.println ""
  IO.println "== The step rule (a toy): one particle on a row of cells, two arrows per cell =="
  IO.println "  start: one arrow of size 1, heading right; each tick climbs one floor"
  let t8 := run 8 start
  IO.println "  tickets after 8 ticks, cells -8 to 8 (odd cells are always empty, so skipped):"
  IO.println s!"    the checkerboard:     {everyOther (t8.map cellSize)}"
  IO.println s!"    a plain coin walk:    {everyOther (plainWalk 8)}"
  IO.println "    (same 256 tickets; the arrows' cancelling empties the middle and piles up on the right)"
  -- find an arrow where two paths meet and cancel exactly
  let r2 := run 2 start
  for j in List.range r2.length do
    let c := r2.getD j (0, 0)
    if c.1 != 0 && c.2 != 0 && sendL c == 0 then
      IO.println s!"  exact cancellation at tick 3, cell {(j : Int) - 2 - 1}: a left arrow {showSpot c.2} carried on, plus a right arrow turned, {showSpot (-(i * c.1))}, gives 0"
  for t in [1, 5, 10, 20] do
    IO.println s!"  tickets after {t} ticks: {total (run t start)}   (2^{t} = {(2 : Int) ^ t})"
  let back := runBack 10 (run 10 start)
  IO.println s!"  10 ticks forward, then 10 back: {back.map (fun c => (showSpot c.1, showSpot c.2))}   (the start, doubled 10 times = 1024)"
  let stepCoin : Coin := fun n => ((n + 5) * 2654435761 / 65536) % 2 == 1
  let k := ticketOf stepCoin 8
  let cell := landCell 8 stepCoin
  IO.println s!"  landing after 8 ticks: 8 coin flips {(List.range 8).map (fun n => if stepCoin n then 1 else 0)} pick ticket {k} of 256"
  IO.println s!"    it lands in cell {(cell : Int) - 8}, which holds {cellSize (t8.getD cell (0, 0))} of the 256 tickets"
  IO.println s!"  every chain of 8 flips checked: each cell is landed in by exactly as many chains as it has tickets: {landCounts 8 == ticketCounts 8}"
