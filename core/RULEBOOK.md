# The Strict Core: Rulebook (locked)

Written Oct 16, 2026, evening. This builds model v4.0.0, the compass, which the author approved at 6:57 pm. The core was first locked at 7:14 pm and relocked at the author's go when the referee gained the poke command; `core/LOCK.json` holds the current fingerprint, and the log records every lock.

## How the core works

The core holds only the rules below, and each rule comes from the model.

**What you can put in.** A particle, named by its floor, its kind and its compass numbers, and an experiment, named by its devices, their directions and the turns. Nothing else can be put in: no speeds, no extra circles, no copies. No input can give a spare piece of the compass a job; only a new model version can.

**What it measures.** The core works out the odds and seals them before anyone opens the observed numbers. Then the two are compared.

**Locks and records.**
- The core is locked by its fingerprint. Any change breaks the fingerprint and needs the author's go and a relock; a change to the model's rules also needs a new model version.
- Every try is written to a log in which each entry carries the fingerprint of the one before it. Editing or deleting a try breaks the chain, and failures are logged like passes.
- Where the model is silent, the core does not fill the gap. It stops and says "the model doesn't say."
- **Only logged results count.** Exploring is welcome, but through the referee: `python3 core/referee.py poke NAME` (a trial file) or `poke --json '{...}'` (typed inline) logs every exploratory try, with its input, so the number of tries always shows. The Lean runner can be run on its own, but then it marks its answer "not logged: does not count," and such answers are never reported. Why: trying many inputs privately and showing only the one that fits makes a search look like a prediction (the look-elsewhere effect).

## Rules

1. **Floors are nested grids.** The point, the line, the plane, ours (three directions), the fourth, and up. Each floor contains the ones below it. A particle lives on its floor's grid, and what we see is its shadow on ours: the distortion of converting it into our three directions. (The Building.)

2. **Whole numbers only.** Every number in the core is a whole number. Odds come out as two whole numbers, a part and a whole. No decimals appear anywhere. (The Building; The Machine.)

3. **The compass** (settles issues 1 and 4). Every point of every grid carries the same compass: everything the directions make when multiplied together.
   - In known math this is the geometric algebra (Clifford, 1878; Hestenes, 1966).
   - Its size doubles with each floor (1, 2, 4, 8 and on), and each floor's compass sits inside the next one's, so each level inherits the compass below and adds to it.
   - **The rule: a thing uses everything its floor's turnings make when multiplied together.** It is one rule for every floor. (In known math this is the "even part" of the compass, the part Hestenes uses.)

   *What the rule gives (results, not extra rules):*
   - The point floor and the line: one plain number, since a turning needs two directions. So the Higgs gets one number with no exception.
   - The plane: the complex plane, one compass with its turning built in.
   - Ours: the four-wide numbers. From our floor up, the order of multiplying matters, as the order of turns does.
   - The fourth floor: two turnings in separate planes multiply into the volume piece, so the rule takes it in. The result is exactly two four-wide numbers, one for each handedness, told apart by that volume piece (known math; physics calls it chirality). This is the Oct 16 electron's "second copy," which now falls out of the rule instead of being added. Not yet tested in the core.

4. **Turning** (settles issue 2). No one sets how anything turns. A turn is multiplying by a piece of the compass.
   - A thing is turned by multiplying it from one side.
   - An operation is turned from both sides. This is forced: a turned operation must still act correctly on turned things.
   - So things come back after two full turns and operations after one. Turning speeds are measured by the core, never set.
   - Whether a particle is a thing (matter) or an operation (a force carrier, as in the model since Oct 13) is a placement, checked like any other, and trying both shows in the log.

5. **Odds.** The odds of an answer are the squared length of the particle's shadow on that answer's part, out of its whole squared length. That the odds add to one is proved once, in Lean. (Landing and Chance.)

6. **Measurement** (settles issue 3). A measurement is one piece of the compass, either a direction or a turning. Its answers are the parts of the particle that piece leaves alone, only flipped or only turned.
   - Which piece it is comes from what the device is made of: a slot of wires is a direction; a magnet, which is circling current, is a turning.
   - By the same rule, a screen is made of places, so its answers are places. This covers the double slit (review round 1).
   - The experiment's record names the device; the tester never chooses.
   - (Known physics agrees: in geometric algebra the electric field is a direction and the magnetic field is a turning.)

7. **Mirrors.** The compass has a few built-in mirrors: reverse the order of every product, flip every direction, or both. Which mirror is a particle's antiparticle is checked, never set. That check needs motion, so it waits on the first hard stop below. (Signs and Mirrors.)

8. **Several particles.** Several particles together are one object on a higher floor, one point for each way they could be arranged. (Numbers and Particles; Linked Particles.)

## Hard stops (the model doesn't say, so the core refuses)

- **How anything moves from one point to its neighbors.** There is no step rule. This blocks mass, the positron, the double slit and charge. Warning for whoever proposes one: multiplying a thing by a direction turns it into a non-thing, so a step must either alternate halves each tick or step by a turning.
- **Charge.** The model doesn't say where it lives.
- **What an operation is made of** (the author, Oct 16: "Operations may have to come later"). The core refuses to measure light, the W or the Z until the model says which pieces an operation uses. Exploratory notes, not counted as results: light placed as a direction of the plane floor gives Malus's law through polarizers, and the W placed as a direction of our floor gives only two answers under a magnet, where three are observed.
- **Which particles flip sign when two of them swap.** Proposed to leave this list: for objects with size in three directions that form one object together (rule 8), swapping two is the same as giving one a full turn (Finkelstein and Rubinstein, 1968). So things, which come back only after two turns, must flip sign, and operations must not. This is checked against the literature, not yet run in the core, and it is waiting on the author's go.
- **Events,** the only place where opposite marks are said to cancel.
- **A plane-floor particle with no path,** that is, one at rest.
- **Where the line floor sits inside ours.**
- **Size.** The compass never ends, so the core builds only the part up to the highest floor an input names.

## What the core will measure first

The odds of measurements, before and after turns of our world, for things: the Higgs and the electron's spin. The electron's two-turn return is computed (a thing is minus itself after one full turn), but comparing it with observation needs two paths recombined, which waits on motion.
