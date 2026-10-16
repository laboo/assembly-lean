# The Building in Lean: the cell's arithmetic, running and checked

A proof that runs, written in Lean 4 (version 4.35.0). The machines use only whole numbers; Mathlib, the standard library of checked mathematics, serves as the referee.

**Where the files live:** the GitHub repository [laboo/assembly-lean](https://github.com/laboo/assembly-lean), together with the compiled library. The Claude project keeps only this README.

**Which way is up** (the same as in the model): up means finer, down means coarser. The **ground floor** holds a spot's ones digit. A whole-number spot's address uses the ground floor and the floors beneath it (finitely many); the finer floors above the ground floor go on forever. Moving something down a floor turns it three-eighths of a lap and grows it; moving it up a floor shrinks it back. The climbing machines start just above the ground floor and work up, one finer floor at a time.

**Piece 1: the ground floor's addresses.** What Lean has checked (in `Building.lean`, 42 theorems, no gaps):

1. Every spot on the grid has an address made of 0s and 1s, one digit per floor, using the twist −1 + i.
2. No two different addresses name the same spot.
3. Adding two addresses digit by digit, starting at the ground floor and passing a carry down one floor at a time, gives exactly the address of the sum, and the carry is always one of 15 values, so the adder is a finite, local machine.
4. Multiplying two addresses using nothing but that adder gives exactly the address of the product: the complex plane's turning rule comes out of 0s and 1s.

**Linked to Mathlib's complex plane** (in `BuildingComplex.lean`, checked against Mathlib v4.35.0, the standard library of checked mathematics): reading an address in Mathlib's own complex numbers is Penney's formula, digit + (−1 + i)·(digit + …); every point with whole-number coordinates has an address; no two addresses land on the same point; and the 0-and-1 adder and multiplier land exactly on Mathlib's sum and product. These statements use only Mathlib's `ℂ`, `I`, `+` and `·`.

**Piece 2: the finer floors** (in `StreamMachine.lean`, plain Lean, and `BuildingStream.lean`, checked against Mathlib): an endless address hands over one mirror digit (0, 1, −1, i, −i) per finer floor above the ground floor. Lean checks that reading an endless address in Mathlib's plane always settles on one point; that every point of the unit disk has an endless address; and that a machine adding two endless addresses by climbing, one finer floor at a time and never looking further up, lands exactly on Mathlib's sum (the sum comes out shifted: moved six floors down, which multiplies it by 8i, what it writes is the true sum). The machine only ever holds one of 85 leftovers, and each digit it writes depends only on the floors read so far.

**Piece 3: multiplying endless addresses** (in `MulMachine.lean`, plain Lean, and `BuildingMul.lean`, checked against Mathlib): a machine multiplies two endless addresses by climbing, writing one floor of the product per floor read and never looking further up. What decides each digit is a leftover that Lean proves always stays inside a four-pointed star (4·|east| − |north| ≤ 2 and 4·|north| − |east| ≤ 2), because the five mirror digits cover the star, turned and grown by one floor, with room to spare. The product lands exactly on Mathlib's: −64 times the written product is x · y (moving it twelve floors down multiplies it by −64). Unlike the adder, the multiplier must remember everything read so far, the way long multiplication on paper does.

**Piece 4: the translator, over the whole plane** (in `FullMachine.lean`, plain Lean, and `BuildingFull.lean`, checked against Mathlib): a full address holds one mirror digit on every floor, finitely many whole-number floors (the ground floor and beneath) and endlessly many finer floors above (one digit story); on the whole-number floors, arithmetic writes the tidy plain 0/1 spelling. Every point of Mathlib's complex plane has one, and adding and multiplying full addresses, using only the machines from pieces 1–3, land exactly on Mathlib's sum and product.

**Piece 5: the mirror flip** (in `FlipMachine.lean`, plain Lean, and `BuildingFlip.lean`, checked against Mathlib): the mirrored twist is the twist turned a quarter turn, so a full address is flipped floor by floor with no carrying. Lean checks that this lands on Mathlib's mirror image (conjugate), that a full address times its flip is its squared size, and that plain 0s and 1s flip into exactly the five mirror digits.

**Piece 6: the address finder** (in `FindMachine.lean`, plain Lean, and `BuildingFind.lean`, checked against Mathlib): hand the machine any point of the plane as approximations (a rule that, asked for precision m, gives a whole-number spot on a halving grid within 1/2^m of the point), and it writes the point's full address, climbing one floor at a time. Lean checks that the address names exactly that point: the finder's leftover stays inside the four-pointed star even though it only ever sees approximations, because the star's wiggle room absorbs their error.

**Piece 7: breaking apart** (in `BuildingBreak.lean`, checked against Mathlib): our spots are Mathlib's whole-number points of the plane (its Gaussian integers), with the same adding, turning and mirror flip. Lean checks that a prime leaving remainder 1 or 2 when divided by 4 breaks apart into a turned piece times its mirror image (5 = (2 + i)(2 − i); Fermat's two-square theorem), that a prime leaving remainder 3 never breaks apart at all, and that breaking apart is always the same up to quarter turns of the pieces (unique factorization, Gauss). This piece is known mathematics brought in from Mathlib, connected to the building.

**Piece 8: landing, floor by floor** (in `LandMachine.lean`, plain Lean, and `BuildingLand.lean`, checked against Mathlib): a coin handed in from outside picks 0 or 1 on each finer floor. Lean checks that the spot it lands on is just the choices it made (after n floors, different chains of flips land on different spots), and that each flip narrows where it lands by one floor's shrink, 1/√2: after n flips the landing point is within 5/2 × (1/√2)^n of the spot those flips chose. The odds of the flips stay outside the building, as in the model's open question. Open for the author: the program picks from the ground floor up, which in the model's words is climbing, while the model describes landing as coming down.

**What running it shows** (`Main.lean`):

```
  1 + 1          : 1 + 1 = 1100   reads as 2 + 0i
  i × i          : 11 × 11 = 11101   reads as -1 + 0i
  (2+i) × (2−i)  : 1111 × 111011 = 111010001   reads as 5 + 0i
  pairs run: 83521, misses: 0, carries outside the fifteen: 0
  endless sum, 300 floors, exact whole-number check at every floor: passed
  largest leftover coordinate seen: 4 (allowed: at most 5)
  endless product, 120 floors, leftover inside the star at every floor (exact check): true
  x × y, read in ordinary decimals:            -0.380352 + -0.114836 i
  −64 × (written product), read the same way:  -0.380352 + -0.114836 i
  full addresses, A + B by the building:       -2.409769 + 6.805859 i
  A + B in decimals:                           -2.409769 + 6.805859 i
  full addresses, A × B by the building:       -21.279668 + 0.110248 i
  A × B in decimals:                           -21.279668 + 0.110248 i
  flip of A by the building:                   2.334822 - 2.229030 i   (A was 2.334822 + 2.229030 i)
  A × flip(A) by the building:                 10.419969 + 0.000000 i
  A's squared size in decimals:                10.419969
  √2 + i/3 handed in as approximations, read back: 1.414214 + 0.333333 i
  37/7 − (20/7) i handed in, read back:            5.285714 - 2.857143 i
  their product by the building:                   8.427510 - 2.278705 i
  their product in decimals:                       8.427510 - 2.278705 i
  5 = (1 + 2i) × (1 - 2i)   check: 5 + 0i
  7 does not break apart (it leaves remainder 3 when divided by 4)
  13 = (2 + 3i) × (2 - 3i)   check: 13 + 0i
  after 4 floors the landing spot is pinned to: 0.250000 + 0.250000 i
  after 16 floors the landing spot is pinned to: 0.195312 + 0.218750 i
  where it lands (60 floors):                   0.193762 + 0.218744 i
```

**To run it yourself:** install Lean (https://lean-lang.org), then in this folder run `lake exe cache get` (downloads Mathlib pre-checked), `lake build BuildingComplex BuildingStream BuildingMul BuildingFull BuildingFlip BuildingFind BuildingBreak BuildingLand` (checks every proof, including the Mathlib links), and `lake build && .lake/build/bin/building` (runs the demo, about 2 seconds).

**In a Claude workspace** (where Mathlib's download is blocked): the files and the compiled library are in the GitHub repository `laboo/assembly-lean`; clone it and run `bash setup.sh` (about a minute), and everything checks in seconds.

**Not yet covered:** the step rule (how each cell changes from one tick to the next, using only its neighbors). The wording pass is done: comments, the README and the demo's labels now say "up" for finer, as the model does. Two code names were left as they are so that no checked statement changes: the mirror digits `up` and `down` mean a step north or south on a floor (i and −i), and `lift` moves an endless address down, lifting digits out of its endless part.
