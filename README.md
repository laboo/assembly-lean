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

**Piece 8: landing, floor by floor** (in `LandMachine.lean`, plain Lean, and `BuildingLand.lean`, checked against Mathlib): a coin handed in from outside picks 0 or 1 on each finer floor. Lean checks that the spot it lands on is just the choices it made (after n floors, different chains of flips land on different spots), and that each flip narrows where it lands by one floor's shrink, 1/√2: after n flips the landing point is within 5/2 × (1/√2)^n of the spot those flips chose. The odds of the flips stay outside the building, as in the model's open question. The program picks from the ground floor up, which matches the model since v1.2.0 ("landing undoes the climb").

**Piece 9: the step rule, a toy** (in `StepMachine.lean`, plain Lean, and `BuildingStep.lean`, checked against Mathlib): space is a row of cells (one direction only), and each cell holds two arrows, one heading right and one heading left. Two are forced: no total-keeping rule that looks only at neighbors works with one arrow per cell (Meyer, 1996). Each tick, every arrow carries on or turns around, turning costs a quarter turn, and then every arrow steps one cell its way: Feynman's checkerboard (1965), today called a quantum walk. The machine uses whole numbers only; the exact rule's shrink of 1/√2 per tick is the size of one floor's shrink, so each tick is read one floor finer: each tick climbs one floor. Lean checks that nothing moves faster than one cell per tick, that the total of the arrows' squared sizes doubles exactly each tick (read one floor finer, the odds always add up to one; in Mathlib's own terms, one tick keeps the total), and that undoing a tick gives back every arrow, doubled. Starting from one arrow of size 1, after t ticks there are exactly 2^t tickets (squared sizes), so exactly t fair coin flips pick where the particle lands: one coin flip per floor climbed. Every chain of 6 flips was checked by Lean (and every chain of 8 by the demo) to land in each cell exactly as often as the cell's tickets say. The odds rule (squared size) is used as a labeled placeholder, as in the model's open question.

**Piece 10: which masses the floors allow** (in `MassMachine.lean`, plain Lean): in the checkerboard, mass is how often an arrow turns around. If each tick climbs whole floors, the carry-on and turn parts' squared sizes must add up to a power of 2, and Lean checks that this leaves only three cases: the parts are the same size (the toy's one mass, enormous in grid units), the turn part is zero (no mass: light), or the carry-on part is zero (always turns: stays put). The reason is plain arithmetic: two sums of two squares that add up to a power of 2 are equal, or one is zero. So with whole floors per tick, light comes free and every ordinary mass needs more.

**Piece 11: lighter masses, by turning only every n-th tick** (in `SlowMachine.lean`, plain Lean): an arrow turns only on every n-th tick and simply carries on in between, so nothing new is added. Lean checks that this is exactly the toy running on a grid n cells coarser: the cells r, r + n, r + 2n, … run period after period exactly like the toy's row, and they never depend on the cells in between. Measured on the fine grid, the particle's steps are n cells and n ticks long while light still moves one cell per tick, so its mass is 1/n of the toy's, for any whole number n. The price is that a particle of mass 1/n only ever sees every n-th cell; standard physics has the same kind of limit (a particle can't be pinned down finer than its Compton wavelength, and the lighter it is, the coarser that limit). A reading, not a result: a particle's mass becomes a whole number, the count of ticks between turns.

**Piece 12: two particles on a line** (in `PairMachine.lean`, plain Lean): under the cell reading, space is a row of places, and two particles get one pair-cell for every pair of places ("one cell for each way they could be arranged," as the model says), each holding four arrows, one per combination of directions. Each particle's tick is the toy's step on its own place and direction. Lean checks that each particle's tick exactly doubles the total (read one floor finer per tick, the odds add up to one); that anything done to particle 2 alone that keeps its total, including moving it or leaving it frozen, leaves particle 1's own odds exactly as they were, so a link can never carry a message; and that the linked pair ("1 heading right and 2 heading left, minus the reverse") can't be split into arrows for particle 1 times arrows for particle 2: linked particles are exactly what can't be factored apart (the model's matching table, v0.6). Checked by running: who moves first doesn't matter. The demo shows the linked pair tending to fly apart (if particle 1 lands at +2, particle 2 lands at −2 in 136 of 192 tickets) and the room growing as a product (9 places each need 81 pair-cells). Where the pair-cells live is the model's open question.

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
  step rule, tickets after 8 ticks, cells -8 to 8 (even cells):
    the checkerboard:     [1, 26, 10, 18, 18, 26, 106, 50, 1]
    a plain coin walk:    [1, 8, 28, 56, 70, 56, 28, 8, 1]
  exact cancellation at tick 3, cell -1: a left arrow 0 - 1i carried on, plus a right arrow turned, 0 + 1i, gives 0
  tickets after 20 ticks: 1048576   (2^20 = 1048576)
  10 ticks forward, then 10 back: the start, doubled 10 times
  landing after 8 ticks: 8 coin flips pick ticket 153 of 256; it lands in cell 4, which holds 106 of them
  every chain of 8 flips checked: each cell is landed in exactly as often as it has tickets: true
  two particles, linked, tickets after 4 rounds (rows: particle 1 at -4..4; columns: particle 2):
    [0, 4, 4, 20, 4]
    [4, 8, 24, 136, 20]
    [4, 24, 8, 24, 4]
    [20, 136, 24, 8, 4]
    [4, 20, 4, 4, 0]
  particle 1's own tickets, particle 2 moving:  [32, 192, 64, 192, 32]
  particle 1's own tickets, particle 2 frozen:  [32, 192, 64, 192, 32]   (x 16)
  room: 9 places for each particle need 81 pair-cells, not 18 cells
```

**To run it yourself:** install Lean (https://lean-lang.org), then in this folder run `lake exe cache get` (downloads Mathlib pre-checked), `lake build BuildingComplex BuildingStream BuildingMul BuildingFull BuildingFlip BuildingFind BuildingBreak BuildingLand BuildingStep MassMachine SlowMachine PairMachine` (checks every proof, including the Mathlib links), and `lake build && .lake/build/bin/building` (runs the demo, about 2 seconds).

**In a Claude workspace** (where Mathlib's download is blocked): the files and the compiled library are in the GitHub repository `laboo/assembly-lean`; clone it and run `bash setup.sh` (about a minute), and everything checks in seconds.

**Not yet covered:** the step rule beyond the toy: more than one direction of space, masses that are not 1/n of the toy's (piece 11 gives 1/n for any whole number n; any other ratio would need floors the building doesn't have), particles that act on each other (pieces 9 to 12 have no forces), and where the pair-cells live. The wording pass is done: comments, the README and the demo's labels now say "up" for finer, as the model does. Two code names were left as they are so that no checked statement changes: the mirror digits `up` and `down` mean a step north or south on a floor (i and −i), and `lift` moves an endless address down, lifting digits out of its endless part.
