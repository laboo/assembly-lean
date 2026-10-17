# The Strict Core: Rulebook (draft 2, not locked)

Drafted Oct 16, 2026, evening. This builds the model as proposed in this chat: the compass (a proposed v4.0.0, not yet approved), with "measurement" in place of "look" (v3.0.1, approved). Nothing here is locked until the author approves the whole rulebook.

## How the core works

The core holds only the rules below, and each rule comes from the model.

**What you can put in.** A particle, named by its floor, its kind and its compass numbers, and an experiment, named by its devices, their directions and the turns. Nothing else can be put in: no speeds, no extra circles, no copies. No input can give a spare piece of the compass a job; only a new model version can.

**What it measures.** The core works out the odds and seals them before anyone opens the observed numbers. Then the two are compared.

**Locks and records.**
- The core is locked by its fingerprint. Any change breaks the fingerprint and needs a new model version with the author's go.
- Every try is written to a log in which each entry carries the fingerprint of the one before it. Editing or deleting a try breaks the chain, and failures are logged like passes.
- Where the model is silent, the core does not fill the gap. It stops and says "the model doesn't say."

## Rules

1. **Floors are nested grids.** The point, the line, the plane, ours (three directions), the fourth, and up. Each floor contains the ones below it. A particle lives on its floor's grid, and what we see is its shadow on ours: the distortion of converting it into our three directions. (The Building.)

2. **Whole numbers only.** Every number in the core is a whole number. Odds come out as two whole numbers, a part and a whole. No decimals appear anywhere. (The Building; The Machine.)

3. **The compass** (settles issues 1 and 4). Every point of every grid carries the same compass: everything the directions make when multiplied together.
   - In known math this is the geometric algebra (Clifford, 1878; Hestenes, 1966).
   - Its size doubles with each floor (1, 2, 4, 8 and on), and each floor's compass sits inside the next one's, so each level inherits the compass below and adds to it.
   - A particle on a floor uses only the part of the compass made from that floor's directions:
     - On the point floor, that part is one plain number, so the Higgs gets one number with no exception.
     - On the plane, it contains the complex plane: one compass, with the turning built in.
     - On ours, it contains the four-wide numbers. From our floor up, the order of multiplying matters, as the order of turns does.

4. **Turning** (settles issue 2). No one sets how anything turns. A turn is multiplying by a piece of the compass.
   - A thing is turned by multiplying it from one side.
   - An operation is turned from both sides. This is forced: a turned operation must still act correctly on turned things.
   - So things come back after two full turns and operations after one. Turning speeds are measured by the core, never set.
   - Whether a particle is a thing (matter) or an operation (a force carrier, as in the model since Oct 13) is a placement, checked like any other, and trying both shows in the log.

5. **Odds.** The odds of an answer are the squared length of the particle's shadow on that answer's part, out of its whole squared length. That the odds add to one is proved once, in Lean. (Landing and Chance.)

6. **Measurement** (settles issue 3). A measurement is one piece of the compass, either a direction or a turning. Its answers are the parts of the particle that piece leaves alone, only flipped or only turned.
   - Which piece it is comes from what the device is made of: a slot of wires is a direction; a magnet, which is circling current, is a turning.
   - The experiment's record names the device; the tester never chooses.
   - (Known physics agrees: in geometric algebra the electric field is a direction and the magnetic field is a turning.)

7. **Mirrors.** The compass has a few built-in mirrors: reverse the order of every product, flip every direction, or both. Which mirror is a particle's antiparticle is checked, never set. That check needs motion, so it waits on the first hard stop below. (Signs and Mirrors.)

8. **Several particles.** Several particles together are one object on a higher floor, one point for each way they could be arranged. (Numbers and Particles; Linked Particles.)

## Hard stops (the model doesn't say, so the core refuses)

- **How anything moves from one point to its neighbors.** There is no step rule. This blocks mass, the positron, the double slit and charge.
- **Charge.** The model doesn't say where it lives.
- **Which particles flip sign when two of them swap.**
- **Events,** the only place where opposite marks are said to cancel.
- **A plane-floor particle with no path,** that is, one at rest.
- **Where the line floor sits inside ours.**
- **Size.** The compass never ends, so the core builds only the part up to the highest floor an input names.

## What the core will measure first

The odds of measurements, before and after turns of our world, for the Higgs, light, the electron's spin, and the W as a thing and as an operation. This includes the electron's two-turn return, which the compass predicts and which observation confirms.
