# The Strict Core: Rulebook (locked)

Written Oct 16, 2026, evening, and revised that night. This builds model v4.1.0, the compass: v4.0.0, which the author approved at 6:57 pm, plus one open question (where several particles live) added with his go at 7:41 pm. The core was first locked at 7:14 pm, relocked at 7:18 pm when the referee gained the poke command, and relocked again that night after six fixes found by poking it (the author: "Go on all 6"). `core/LOCK.json` holds the current fingerprint, and the log records every lock.

## How the core works

The core holds only the rules below, and each rule comes from the model.

**What you can put in.**
- A particle, named by its floor and its kind (a thing or an operation), and, if you are asking about its antiparticle, that.
- An experiment: a row of devices, each a magnet or a polarizer with a direction in whole numbers, or a screen. The first device prepares the particle; every later device measures it.
- Nothing else. No state is ever typed in, on any floor: a device prepares it. Speeds, masses, charges and the like are refused, because the model says they must come out, never go in. So no input can give a spare piece of the compass a job; only a new model version can.
- Every field and every device is checked the same way on every floor, before the core looks at the floor.

**What comes out.** Exactly one of three answers:
- **odds**: the model says, and the core works it out. An answer that can't come out any other way (one plain number can only give one answer) is stamped **structural**, and the referee reports its pass as a structural pass.
- **stop**: the input is in the model's language, but the model doesn't say ("the model doesn't say"). The hard stops are listed below.
- **refused**: the input isn't in the model's language, or it tries to set by hand what the model says must come out.

**Locks and records.**
- The core is locked by its fingerprint. Any change breaks the fingerprint and needs the author's go and a relock; a change to the model's rules also needs a new model version.
- Every try is written to a log in which each entry carries the fingerprint of the one before it. Editing or deleting a try breaks the chain, and failures are logged like passes.
- **Register before asking.** A trial's input and its observed numbers are written into the log (`referee.py register NAME`) before the core is asked about it. A formal run is refused if the trial isn't registered, or if its input or observed file has changed since. If the same input was asked before it was registered, the registration says so and the report flags the run, because its prediction was seen first.
- **Seal before opening.** A formal run writes the prediction to the log before the referee opens the observed numbers.
- Where the model is silent, the core does not fill the gap. It stops and says "the model doesn't say."
- **Only logged results count.** Exploring is welcome, but through the referee: `python3 core/referee.py poke NAME` (a trial file) or `poke --json '{...}'` (typed inline) logs every exploratory try, with its input, and the report shows what each one returned, so the number of tries always shows. The Lean runner can be run on its own, but then it marks its answer "not logged: does not count," and such answers are never reported. Why: trying many inputs privately and showing only the one that fits makes a search look like a prediction (the look-elsewhere effect).

## Rules

1. **Floors are nested grids.** The point, the line, the plane, ours (three directions), the fourth, and up. Each floor contains the ones below it. A particle lives on its floor's grid, and what we see is its shadow on ours: the distortion of converting it into our three directions. (The Building.)

2. **Whole numbers only.** Every number in the core is a whole number. Odds come out as two whole numbers, a part and a whole. No decimals appear anywhere. (The Building; The Machine.)

3. **The compass.** Every point of every grid carries the same compass: everything the directions make when multiplied together.
   - In known math this is the geometric algebra (Clifford, 1878; Hestenes, 1966).
   - Its size doubles with each floor (1, 2, 4, 8 and on), and each floor's compass sits inside the next one's, so each level inherits the compass below and adds to it.
   - **The rule: a thing uses everything its floor's turnings make when multiplied together.** It is one rule for every floor. (In known math this is the "even part" of the compass, the part Hestenes uses.)

   *What the rule gives (results, not extra rules):*
   - The point floor and the line: one plain number, since a turning needs two directions. So a thing there has one answer under any measurement, and the core stamps that answer structural (the Higgs; a line-floor thing).
   - The plane: the complex plane, one compass with its turning built in.
   - Ours: the four-wide numbers. From our floor up, the order of multiplying matters, as the order of turns does.
   - The fourth floor: two turnings in separate planes multiply into the volume piece, so the rule takes it in. The result is exactly two four-wide numbers, one for each handedness, told apart by that volume piece (known math; physics calls it chirality). This is the Oct 16 electron's "second copy," which now falls out of the rule instead of being added. Not yet tested in the core.

4. **Turning.** No one sets how anything turns. A turn is multiplying by a piece of the compass.
   - A thing is turned by multiplying it from one side.
   - An operation is turned from both sides. This is forced: a turned operation must still act correctly on turned things.
   - So things come back after two full turns and operations after one (computed in `Facts.lean`). Turning speeds are never set.
   - A turn is not an input yet: on its own it is either invisible (a thing after a full turn is minus itself, which no measurement of it alone can see, proved in `MeasureFacts.lean`) or the same as tilting the devices. It can only be seen when two paths recombine, which needs motion.
   - Whether a particle is a thing (matter) or an operation (a force carrier, as in the model since Oct 13) is a placement, checked like any other, and trying both shows in the log.

5. **Odds.** The odds of an answer are the squared length of the particle's shadow on that answer's part, out of its whole squared length. (Landing and Chance.)
   - Each answer's shadow is worked out on its own. No answer is "whatever the others leave."
   - **Proved once, in Lean, for every thing on our floor and every magnet with a whole-length axis** (`OddsFacts.lean`, no gaps, Lean's three standard background rules):
     - the odds of "up" and "down" add to one (`up_down_whole`);
     - for any row of magnets, the odds of all the chains of answers add to one (`chains_whole`);
     - a prepared thing's next odds are (1 + cos)/2 for "up" and (1 − cos)/2 for "down", whatever thing was flattened to prepare it (`prepared_odds`);
     - along a whole row of magnets, every chain's odds are the same whatever thing was flattened (`start_free`). So the starting piece the core picks is not a choice.
   - Still checked on cases rather than proved: the reference turning on a thing's free side (`refJ`) gives the same odds as three other choices, on 81 prepare-then-measure pairs (`MeasureFacts.lean`).

6. **Measurement.** A measurement is one piece of the compass, either a direction or a turning. Its answers are the parts of the particle that piece leaves alone, only flipped or only turned.
   - Which piece it is comes from what the device is made of: a slot of wires (a polarizer) is a direction; a magnet, which is circling current, is a turning.
   - By the same rule, a screen is made of places, so its answers are places.
   - A measurement flattens the particle onto its answer's part. **Preparing is measuring and keeping one answer**: the first device keeps "up". **Measurements in a row**: each device flattens what the one before left, and the core gives the odds of every chain of answers. (Landing and Chance.)
   - The experiment's record names the device; the tester never chooses.
   - (Known physics agrees: in geometric algebra the electric field is a direction and the magnetic field is a turning.)

7. **Mirrors.** The compass has a few built-in mirrors: reverse the order of every product, flip every direction, or both. Which mirror is a particle's antiparticle is checked, never set, so an input can ask about the antiparticle but can't name a mirror. That check needs motion, so it waits on the first hard stop below. (Signs and Mirrors.)

8. **Several particles.** Several particles together are one object on a higher floor, one point for each way they could be arranged. (Numbers and Particles; Linked Particles.) Which floor, and how they combine, is a hard stop below.

## Hard stops (the model doesn't say, so the core stops)

- **How anything moves from one point to its neighbors.** There is no step rule. This blocks mass, the positron, the double slit, charge, screens and turns that can be seen. Warning for whoever proposes one: multiplying a thing by a direction turns it into a non-thing, so a step must either alternate halves each tick or step by a turning.
- **Charge.** The model doesn't say where it lives.
- **What an operation is made of** (the author, Oct 16: "Operations may have to come later"). The core stops for light, the W or the Z until the model says which pieces an operation uses. Exploratory notes, not counted as results: light placed as a direction of the plane floor gives Malus's law through polarizers, and the W placed as a direction of our floor gives only two answers under a magnet, where three are observed.
- **Where several particles live** (model v4.1.0, Open Questions). The model says they are one object on a higher floor, but not which floor or how they combine. Named danger: the obvious fill-in is standard physics' space of arrangements, which would be a knob unless a rule forces it.
- **How a direction acts on a thing.** A polarizer is a direction, and multiplying a thing by a direction from one side makes it a non-thing; the model doesn't say what a polarizer does to a thing.
- **What a source sends.** The model doesn't describe a source, so the first device prepares the particle, and measuring needs a second device.
- **Which particles flip sign when two of them swap.** Proposed to leave this list: for objects with size in three directions that form one object together (rule 8), swapping two is the same as giving one a full turn (Finkelstein and Rubinstein, 1968). So things, which come back only after two turns, must flip sign, and operations must not. This is checked against the literature, not yet run in the core, and it is waiting on the author's go.
- **Events,** the only place where opposite marks are said to cancel.
- **A plane-floor particle with no path,** that is, one at rest.
- **Where the line floor sits inside ours,** for motion along the line. It can't change a measurement of a line-floor thing at rest: that thing is one plain number, so its answer is structural, like the Higgs.
- **Size.** The compass never ends, so the core builds only the part up to the highest floor an input names, and at most nine devices in one trial.

## What the core measures now

The odds of measurements in a row, for things on our floor under magnets (the electron's spin), and the structural one-answer cases on the point and line floors (the Higgs). The electron's two-turn return is computed (a thing is minus itself after one full turn), but comparing it with observation needs two paths recombined, which waits on motion.
