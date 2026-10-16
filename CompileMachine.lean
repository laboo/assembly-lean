import FlipMachine
import PairMachine

/-!
# The compiler: small turns from whole-number reflections (plain Lean, no math library)

Everyday-language summary (for the author):

* Physics needs turns by arbitrary amounts (a mass, the pull of a charge), but the building's
  exact single steps are a small fixed set (piece 10). The way out is the one quantum
  computers use: **compile** each wanted turn into a sequence of exact whole-number steps.
* **The step used here is a reflection.** Pick a direction made of four whole-number spots
  whose squared length is `n` (a power of 2). Reflecting a cell's four arrows across it,
  `n · arrows − 2 · (how much of the arrows lies along the direction) · direction`, uses
  only whole numbers, and **Lean checks that it multiplies every cell's squared size by
  exactly `n²`** (it climbs floors and creates or loses nothing).
* **Two reflections make a turn** by twice the angle between their directions. Choosing two
  nearly parallel whole-number directions gives a small turn, a mass turn for the electron.
  The directions can't lie exactly in the wanted plane (piece 10), so each turn carries a
  tiny tilt; **pairing it with its mirror image cancels the tilt** (measured by running).
* Below, one compiled mass turn is written out in exact whole numbers: four reflections
  across directions of squared length 2^40 (320 floors in all). Measured by running, the
  electron with this turn has its rest energy and inertia agreeing as closely as with an
  exact turn on the same grid (E = mc², up to the grid's own effect, which vanishes as the
  grid gets finer), and its spin splitting is about 2 parts in 100 million of its rest
  energy.
-/

namespace Building

open Spot

/-- A cell with four arrows: left-handed spin up and down, right-handed spin up and down. -/
structure Quad where
  a : Spot
  b : Spot
  c : Spot
  d : Spot
deriving DecidableEq, Repr

namespace Quad

/-- Squared size of a four-arrow cell. -/
def size (q : Quad) : Int := nsq q.a + nsq q.b + nsq q.c + nsq q.d

/-- How much of `q` lies along `v`: the sum of each arrow times the mirror image of `v`'s. -/
def along (v q : Quad) : Spot := v.a.flip * q.a + v.b.flip * q.b + v.c.flip * q.c + v.d.flip * q.d

/-- **The reflection across a whole-number direction `v`** (of squared length `n`):
`n · q − 2 · (along v q) · v`, arrow by arrow. -/
def reflect (v : Quad) (n : Int) (q : Quad) : Quad :=
  let s := along v q
  let m : Spot := ⟨n, 0⟩
  let t : Spot := ⟨2, 0⟩
  ⟨m * q.a - t * s * v.a, m * q.b - t * s * v.b, m * q.c - t * s * v.c, m * q.d - t * s * v.d⟩

end Quad

open Quad

/-- The real part of `x` times the mirror image of `y`. -/
def rdot (x y : Spot) : Int := x.re * y.re + x.im * y.im

theorem nsq_sub (x y : Spot) : nsq (x - y) = nsq x - 2 * rdot x y + nsq y := by
  simp only [nsq, rdot, Spot.sub_re, Spot.sub_im]; grind

theorem nsq_scale (n : Int) (x : Spot) : nsq ((⟨n, 0⟩ : Spot) * x) = n * n * nsq x := by
  simp only [nsq, Spot.mul_re, Spot.mul_im]; grind

theorem nsq_two_mul (s v : Spot) : nsq ((⟨2, 0⟩ : Spot) * s * v) = 4 * (nsq s * nsq v) := by
  simp only [nsq, Spot.mul_re, Spot.mul_im]; grind

theorem rdot_scale (n : Int) (x s v : Spot) :
    rdot ((⟨n, 0⟩ : Spot) * x) ((⟨2, 0⟩ : Spot) * s * v) = 2 * n * rdot x (s * v) := by
  simp only [rdot, Spot.mul_re, Spot.mul_im]; grind

/-- The four cross terms add up to the squared size of `along v q`. -/
theorem cross_sum (v q : Quad) :
    rdot q.a (along v q * v.a) + rdot q.b (along v q * v.b) + rdot q.c (along v q * v.c) +
      rdot q.d (along v q * v.d) = nsq (along v q) := by
  simp only [rdot, along, nsq, Spot.mul_re, Spot.mul_im, Spot.add_re, Spot.add_im, Spot.flip_re,
    Spot.flip_im]
  grind

/-- **A reflection keeps every cell's total exactly**: if the direction's squared length is
`n`, the reflected cell's squared size is exactly `n²` times the original. -/
theorem reflect_size (v q : Quad) (n : Int) (hv : v.size = n) :
    (reflect v n q).size = n * n * q.size := by
  have hc := cross_sum v q
  simp only [reflect, Quad.size, nsq_sub, nsq_scale, nsq_two_mul, rdot_scale] at hv ⊢
  generalize along v q = s at hc ⊢
  have e : 4 * (nsq s * nsq v.a) + 4 * (nsq s * nsq v.b) + 4 * (nsq s * nsq v.c) +
      4 * (nsq s * nsq v.d) = 4 * nsq s * n := by rw [← hv]; grind
  have e2 : 2 * (2 * n * rdot q.a (s * v.a)) + 2 * (2 * n * rdot q.b (s * v.b)) +
      2 * (2 * n * rdot q.c (s * v.c)) + 2 * (2 * n * rdot q.d (s * v.d)) = 4 * n * nsq s := by
    rw [← hc]; grind
  grind

/-! ## One compiled mass turn, in exact whole numbers -/

/-- The four unit directions (squared length 1). -/
def e0 : Quad := ⟨1, 0, 0, 0⟩
def e1 : Quad := ⟨0, 1, 0, 0⟩

/-- Two nearly parallel whole-number directions for the spin-up and spin-down planes, and
their mirror images (small leftover parts reversed). Squared length 2^40 each. -/
def v1 : Quad := ⟨⟨1047265, 0⟩, ⟨11, 25⟩, ⟨9, -52418⟩, 0⟩
def v2 : Quad := ⟨⟨11, 25⟩, ⟨1047265, 0⟩, 0, ⟨9, -52418⟩⟩
def w1 : Quad := ⟨⟨1047265, 0⟩, ⟨-11, -25⟩, ⟨9, -52418⟩, 0⟩
def w2 : Quad := ⟨⟨-11, -25⟩, ⟨1047265, 0⟩, 0, ⟨9, -52418⟩⟩

theorem v1_size : v1.size = 2 ^ 40 := by decide
theorem v2_size : v2.size = 2 ^ 40 := by decide
theorem w1_size : w1.size = 2 ^ 40 := by decide
theorem w2_size : w2.size = 2 ^ 40 := by decide
theorem e0_size : e0.size = 1 := by decide
theorem e1_size : e1.size = 1 := by decide

/-- One compiled turn: reflect across `e1`, then `v2`, then `e0`, then `v1`. -/
def turnOnce (q : Quad) : Quad :=
  reflect v1 (2 ^ 40) (reflect e0 1 (reflect v2 (2 ^ 40) (reflect e1 1 q)))

/-- Its mirror image. -/
def turnMirror (q : Quad) : Quad :=
  reflect w1 (2 ^ 40) (reflect e0 1 (reflect w2 (2 ^ 40) (reflect e1 1 q)))

/-- **The compiled mass turn**: a turn followed by its mirror image, so the tilts cancel. -/
def massTurn (q : Quad) : Quad := turnMirror (turnOnce q)

/-- **The compiled mass turn keeps every cell's total exactly**, climbing 320 floors. -/
theorem massTurn_size (q : Quad) : (massTurn q).size = 2 ^ 320 * q.size := by
  simp only [massTurn, turnMirror, turnOnce]
  rw [reflect_size _ _ _ w1_size, reflect_size _ _ _ e0_size, reflect_size _ _ _ w2_size,
    reflect_size _ _ _ e1_size, reflect_size _ _ _ v1_size, reflect_size _ _ _ e0_size,
    reflect_size _ _ _ v2_size, reflect_size _ _ _ e1_size]
  generalize q.size = s
  grind

/-- **Piece 14 in one statement.** -/
theorem piece_fourteen :
    (∀ (v q : Quad) (n : Int), v.size = n → (reflect v n q).size = n * n * q.size) ∧
    (∀ q : Quad, (massTurn q).size = 2 ^ 320 * q.size) :=
  ⟨reflect_size, massTurn_size⟩

end Building
