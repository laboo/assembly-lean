/-
  THE STRICT CORE, part 6: the odds facts, proved for EVERY thing and EVERY magnet.   Model v4.1.0.

  Everyday language:
  * The odds of each answer come from that answer's own shadow (`flat` in Measure.lean).
    Nothing is "whatever is left over", so adding to one is something to prove, not something
    built in. It is proved here once, for every thing on our floor and every magnet whose axis
    has a whole length, and for measurements in a row of any length.
  * Preparing keeps one answer of a magnet. Proved here: whichever thing is flattened, the next
    magnet's odds depend only on the two magnets' directions, so the starting piece the core
    picks is not a choice. Every kept answer is again a prepared thing (along the magnet's axis
    or against it), so the same holds at every step of a row of measurements.
  * These are statements about the core's own functions, not comparisons with observation.

  Mathspeak: a thing on floor 3 is `thingOf w x y z` (pieces 0, 3, 5, 6). Each `*_formula` lemma
  unfolds the core's multiplication once; everything after is ring arithmetic (`grind`).
-/
import StrictCore.Measure

namespace StrictCore

set_option maxRecDepth 100000

/-- A thing on our floor: the plain number and the three turnings (pieces 0, 3, 5, 6). -/
def thingOf (w x y z : Int) : C := [w, 0, 0, x, 0, y, z, 0]

/-! ## Unfolding the core's own functions once -/

theorem len2_thingOf (w x y z : Int) : len2 (thingOf w x y z) = w*w + x*x + y*y + z*z := by
  simp [len2, thingOf]

theorem dot_thingOf (w x y z p q r t : Int) :
    dot (thingOf w x y z) (thingOf p q r t) = w*p + x*q + y*r + z*t := by
  simp [dot, thingOf]

set_option maxHeartbeats 4000000 in
theorem sort_formula (a b c w x y z : Int) :
    sortThing refJ [a, b, c] (thingOf w x y z) =
      thingOf (a*y + b*z + c*w) (a*z - b*y + c*x) (a*w - b*x - c*y) (a*x + b*w - c*z) := by
  simp [sortThing, mul, magnet, dir3, piece, refJ, thingOf, scale, coef, sign, swaps, has,
        List.range, List.range.loop]
  grind

theorem flat_formula (a b c L s w x y z : Int) :
    flat refJ [a, b, c] L s (thingOf w x y z) =
      thingOf (L*w + s*(a*y + b*z + c*w)) (L*x + s*(a*z - b*y + c*x))
              (L*y + s*(a*w - b*x - c*y)) (L*z + s*(a*x + b*w - c*z)) := by
  rw [flat, sort_formula]
  simp [add, scale, thingOf]

/-- Flattening keeps a thing a thing. -/
theorem flat_thing (a b c L s w x y z : Int) :
    ∃ p q r t, flat refJ [a, b, c] L s (thingOf w x y z) = thingOf p q r t :=
  ⟨_, _, _, _, flat_formula a b c L s w x y z⟩

/-- Keeping "down" of a magnet is keeping "up" of the magnet turned around (a convention of
    names, not a choice). -/
theorem flat_down (a b c L w x y z : Int) :
    flat refJ [a, b, c] L (-1) (thingOf w x y z) = flat refJ [-a, -b, -c] L 1 (thingOf w x y z) := by
  rw [flat_formula, flat_formula]; simp [thingOf]; grind

/-! ## Fact 1: for one magnet, "up" and "down" add to the whole -/

/-- For every thing and every magnet with a whole-length axis:
    |up shadow|^2 + |down shadow|^2 = (2L)^2 |thing|^2, i.e. the two odds add to one. -/
theorem up_down_whole (a b c L w x y z : Int) (hL : L * L = a*a + b*b + c*c) :
    len2 (flat refJ [a, b, c] L 1 (thingOf w x y z)) +
      len2 (flat refJ [a, b, c] L (-1) (thingOf w x y z)) =
    4 * L * L * len2 (thingOf w x y z) := by
  rw [flat_formula, flat_formula, len2_thingOf, len2_thingOf, len2_thingOf]
  grind

/-! ## Fact 2: for measurements in a row, all chains together add to the whole -/

/-- The sum of the squared lengths of every chain's shadow. -/
def sumLen : List (List Int × C) → Int
  | [] => 0
  | p :: ps => len2 p.2 + sumLen ps

theorem sumLen_append (xs ys : List (List Int × C)) : sumLen (xs ++ ys) = sumLen xs + sumLen ys := by
  induction xs with
  | nil => simp [sumLen]
  | cons p ps ih => simp [sumLen, ih]; grind

theorem sumLen_map_label (f : List Int → List Int) (xs : List (List Int × C)) :
    sumLen (xs.map (fun p => (f p.1, p.2))) = sumLen xs := by
  induction xs with
  | nil => simp [sumLen]
  | cons p ps ih => simp [sumLen, ih]

/-- A magnet the core accepts: three whole numbers and a whole length. -/
def wholeMagnet (p : List Int × Int) : Prop :=
  ∃ a b c, p.1 = [a, b, c] ∧ p.2 * p.2 = a*a + b*b + c*c

/-- For every thing and every row of magnets with whole-length axes, the odds of all the
    chains of answers add to one: their squared shadows add to (2L1)^2 (2L2)^2 ... |thing|^2. -/
theorem chains_whole (ms : List (List Int × Int)) (hms : ∀ p ∈ ms, wholeMagnet p) :
    ∀ w x y z : Int,
      sumLen (chains refJ ms (thingOf w x y z)) = wholeOf ms * len2 (thingOf w x y z) := by
  induction ms with
  | nil => intro w x y z; simp [chains, sumLen, wholeOf]
  | cons p rest ih =>
    intro w x y z
    obtain ⟨m, L⟩ := p
    obtain ⟨a, b, c, hm, hL⟩ := hms (m, L) (by simp)
    simp only at hm hL
    subst hm
    have ih' := ih (fun q hq => hms q (by simp [hq]))
    simp only [chains, sumLen_append, sumLen_map_label, wholeOf]
    rw [flat_formula a b c L 1, flat_formula a b c L (-1), ih', ih',
        ← flat_formula a b c L 1, ← flat_formula a b c L (-1)]
    have h := up_down_whole a b c L w x y z hL
    grind

/-! ## Fact 3: the starting piece cannot matter -/

/-- A prepared thing (one flattened onto "up" by a magnet along n = (a,b,c) of whole length Ln)
    seen by a second magnet along (d,e,f): its shadow-sum is Ln times the plain overlap of the
    two directions. In words: a prepared thing points exactly along its preparing magnet,
    whatever thing was flattened to make it. -/
theorem prepared_points_along (a b c Ln d e f w x y z : Int) (hn : Ln * Ln = a*a + b*b + c*c) :
    let u := flat refJ [a, b, c] Ln 1 (thingOf w x y z)
    Ln * dot u (sortThing refJ [d, e, f] u) = (a*d + b*e + c*f) * len2 u := by
  intro u
  obtain ⟨p, q, r, t, hu⟩ := flat_thing a b c Ln 1 w x y z
  have hu' := flat_formula a b c Ln 1 w x y z
  simp only [u]
  rw [hu', sort_formula, dot_thingOf, len2_thingOf]
  grind

theorem sort_len (a b c w x y z : Int) :
    len2 (sortThing refJ [a, b, c] (thingOf w x y z)) = (a*a + b*b + c*c) * len2 (thingOf w x y z) := by
  rw [sort_formula, len2_thingOf, len2_thingOf]; grind

theorem square_nonneg (w : Int) : 0 ≤ w * w := by
  rcases Int.le_total 0 w with h | h
  · exact Int.mul_nonneg h h
  · exact Int.mul_nonneg_of_nonpos_of_nonpos h h

theorem len2_nonneg_thing (w x y z : Int) : 0 ≤ len2 (thingOf w x y z) := by
  rw [len2_thingOf]
  exact Int.add_nonneg (Int.add_nonneg (Int.add_nonneg (square_nonneg w)
    (square_nonneg x)) (square_nonneg y)) (square_nonneg z)

/-- Keeping answer s of a magnet is keeping "up" of the magnet along s times its axis (s = -1: turned around). -/
theorem flat_sign (a b c L s w x y z : Int) :
    flat refJ [a, b, c] L s (thingOf w x y z) = flat refJ [s*a, s*b, s*c] L 1 (thingOf w x y z) := by
  rw [flat_formula, flat_formula]; simp [thingOf]; grind

/-- The odds of either answer of a prepared thing depend only on the two magnets' directions:
    |shadow|^2 / ((2Lm)^2 |thing|^2) = (Ln Lm + s (n . m)) / (2 Ln Lm), written without division.
    For the "up" answer this is (1 + cos)/2. Whatever thing was flattened, the answer is the same. -/
theorem prepared_odds (a b c Ln d e f Lm s w x y z : Int) (hn : Ln * Ln = a*a + b*b + c*c)
    (hm : Lm * Lm = d*d + e*e + f*f) (hs : s * s = 1) :
    let u := flat refJ [a, b, c] Ln 1 (thingOf w x y z)
    Ln * len2 (flat refJ [d, e, f] Lm s u) = 2 * Lm * (Ln * Lm + s * (a*d + b*e + c*f)) * len2 u := by
  intro u
  have h1 := prepared_points_along a b c Ln d e f w x y z hn
  simp only [u] at h1 ⊢
  rw [flat_formula a b c Ln 1] at h1 ⊢
  rw [flat_formula d e f Lm s, len2_thingOf, len2_thingOf]
  rw [sort_formula, dot_thingOf, len2_thingOf] at h1
  grind

/-! ## Fact 4: along a whole row of measurements, the starting piece still cannot matter -/

/-- Follow one chain of answers through a row of magnets. -/
def follow (J : C) : List (List Int × Int) → List Int → C → C
  | (m, L) :: rest, s :: ss, x => follow J rest ss (flat J m L s x)
  | _, _, x => x

/-- Every list of answers (1 or -1) of a given length. -/
def signLists : Nat → List (List Int)
  | 0 => [[]]
  | k + 1 => (signLists k).map (1 :: ·) ++ (signLists k).map ((-1) :: ·)

/-- The core's `chains` is exactly: every list of answers, each followed through the row. -/
theorem chains_eq_follow (J : C) (ms : List (List Int × Int)) :
    ∀ x, chains J ms x = (signLists ms.length).map (fun ss => (ss, follow J ms ss x)) := by
  induction ms with
  | nil => intro x; simp [chains, signLists, follow]
  | cons p rest ih =>
    intro x
    obtain ⟨m, L⟩ := p
    simp [chains, signLists, ih, follow, List.map_append, List.map_map, Function.comp_def]

theorem follow_zero (ms : List (List Int × Int)) (hms : ∀ p ∈ ms, wholeMagnet p) :
    ∀ ss, (∀ s ∈ ss, s * s = 1) → ∀ w x y z : Int, len2 (thingOf w x y z) = 0 →
      ∃ p q r t, follow refJ ms ss (thingOf w x y z) = thingOf p q r t ∧ len2 (thingOf p q r t) = 0 := by
  induction ms with
  | nil => intro ss _ w x y z h; exact ⟨w, x, y, z, by simp [follow], h⟩
  | cons p rest ih =>
    intro ss hss w x y z h
    obtain ⟨m, L⟩ := p
    obtain ⟨a, b, c, hm, hL⟩ := hms (m, L) (by simp)
    simp only at hm hL
    subst hm
    cases ss with
    | nil => exact ⟨w, x, y, z, by simp [follow], h⟩
    | cons s ss' =>
      have hs : s * s = 1 := hss s (by simp)
      have hw := up_down_whole a b c L w x y z hL
      rw [h, Int.mul_zero] at hw
      obtain ⟨P, Q, R, T, hv⟩ := flat_thing a b c L s w x y z
      have hzero : len2 (thingOf P Q R T) = 0 := by
        have h1 : 0 ≤ len2 (flat refJ [a, b, c] L 1 (thingOf w x y z)) := by
          rw [flat_formula]; exact len2_nonneg_thing _ _ _ _
        have h2 : 0 ≤ len2 (flat refJ [a, b, c] L (-1) (thingOf w x y z)) := by
          rw [flat_formula]; exact len2_nonneg_thing _ _ _ _
        rw [← hv]
        have hs' : s = 1 ∨ s = -1 := by
          have : (s - 1) * (s + 1) = 0 := by grind
          rcases Int.mul_eq_zero.mp this with h | h
          · left; omega
          · right; omega
        rcases hs' with rfl | rfl <;> omega
      have := ih (fun q hq => hms q (by simp [hq])) ss' (fun s hs => hss s (by simp [hs])) P Q R T hzero
      simpa [follow, hv] using this

theorem start_free (ms : List (List Int × Int)) (hms : ∀ p ∈ ms, wholeMagnet p ∧ 0 < p.2) :
    ∀ ss, (∀ s ∈ ss, s * s = 1) →
    ∀ a b c Ln : Int, 0 < Ln → Ln * Ln = a*a + b*b + c*c →
    ∀ w x y z w' x' y' z' : Int,
      len2 (follow refJ ms ss (flat refJ [a, b, c] Ln 1 (thingOf w x y z))) *
          len2 (flat refJ [a, b, c] Ln 1 (thingOf w' x' y' z')) =
        len2 (follow refJ ms ss (flat refJ [a, b, c] Ln 1 (thingOf w' x' y' z'))) *
          len2 (flat refJ [a, b, c] Ln 1 (thingOf w x y z)) := by
  induction ms with
  | nil => intro ss _ a b c Ln _ _ w x y z w' x' y' z'; simp [follow]; grind
  | cons p rest ih =>
    intro ss hss a b c Ln hLn hn w x y z w' x' y' z'
    obtain ⟨m, Lm⟩ := p
    obtain ⟨⟨d, e, f, hm, hLm⟩, hpos⟩ := hms (m, Lm) (by simp)
    simp only at hm hLm hpos
    subst hm
    cases ss with
    | nil => simp [follow]; grind
    | cons s ss' =>
      have hs : s * s = 1 := hss s (by simp)
      have hrest : ∀ q ∈ rest, wholeMagnet q ∧ 0 < q.2 := fun q hq => hms q (by simp [hq])
      have hss' : ∀ s ∈ ss', s * s = 1 := fun s hs => hss s (by simp [hs])
      obtain ⟨P, Q, R, T, hu⟩ := flat_thing a b c Ln 1 w x y z
      obtain ⟨P', Q', R', T', hu'⟩ := flat_thing a b c Ln 1 w' x' y' z'
      have k1 := prepared_odds a b c Ln d e f Lm s w x y z hn hLm hs
      have k2 := prepared_odds a b c Ln d e f Lm s w' x' y' z' hn hLm hs
      simp only at k1 k2
      rw [hu] at k1; rw [hu'] at k2
      simp only [follow]
      rw [hu, hu'] at *
      rw [hu, hu']
      rw [flat_sign d e f Lm s P Q R T, flat_sign d e f Lm s P' Q' R' T'] at *
      have hsm : Lm * Lm = (s*d)*(s*d) + (s*e)*(s*e) + (s*f)*(s*f) := by grind
      have IH := ih hrest ss' hss' (s*d) (s*e) (s*f) Lm hpos hsm P Q R T P' Q' R' T'
      generalize hk : 2 * Lm * (Ln * Lm + s * (a*d + b*e + c*f)) = k at k1 k2
      generalize hF : len2 (follow refJ rest ss' (flat refJ [s*d, s*e, s*f] Lm 1 (thingOf P Q R T))) = F at IH ⊢
      generalize hF' : len2 (follow refJ rest ss' (flat refJ [s*d, s*e, s*f] Lm 1 (thingOf P' Q' R' T'))) = F' at IH ⊢
      generalize hV : len2 (flat refJ [s*d, s*e, s*f] Lm 1 (thingOf P Q R T)) = V at IH k1
      generalize hV' : len2 (flat refJ [s*d, s*e, s*f] Lm 1 (thingOf P' Q' R' T')) = V' at IH k2
      by_cases hk0 : k = 0
      · -- this answer is impossible: both shadows vanish, and so does everything after them
        subst hk0
        have hV0 : V = 0 := by
          have : Ln * V = 0 := by grind
          rcases Int.mul_eq_zero.mp this with h | h
          · omega
          · exact h
        have hV0' : V' = 0 := by
          have : Ln * V' = 0 := by grind
          rcases Int.mul_eq_zero.mp this with h | h
          · omega
          · exact h
        obtain ⟨g0, g1, g2, g3, hg⟩ := flat_thing (s*d) (s*e) (s*f) Lm 1 P Q R T
        obtain ⟨g0', g1', g2', g3', hg'⟩ := flat_thing (s*d) (s*e) (s*f) Lm 1 P' Q' R' T'
        have hrest' : ∀ q ∈ rest, wholeMagnet q := fun q hq => (hrest q hq).1
        obtain ⟨_, _, _, _, hf1, hz1⟩ := follow_zero rest hrest' ss' hss' g0 g1 g2 g3 (by rw [← hg, hV, hV0])
        obtain ⟨_, _, _, _, hf2, hz2⟩ := follow_zero rest hrest' ss' hss' g0' g1' g2' g3' (by rw [← hg', hV', hV0'])
        rw [hg] at hF; rw [hg'] at hF'
        rw [hf1, hz1] at hF; rw [hf2, hz2] at hF'
        subst hF hF'; simp
      · -- k (F U') = F (Ln V') = Ln (F V') = Ln (F' V) = F' (Ln V) = k (F' U); then cancel k
        have h3 : k * (F * len2 (thingOf P' Q' R' T')) = k * (F' * len2 (thingOf P Q R T)) := by
          calc k * (F * len2 (thingOf P' Q' R' T'))
              = F * (k * len2 (thingOf P' Q' R' T')) := by grind
            _ = F * (Ln * V') := by rw [← k2]
            _ = Ln * (F * V') := by grind
            _ = Ln * (F' * V) := by rw [IH]
            _ = F' * (Ln * V) := by grind
            _ = F' * (k * len2 (thingOf P Q R T)) := by rw [k1]
            _ = k * (F' * len2 (thingOf P Q R T)) := by grind
        exact Int.eq_of_mul_eq_mul_left hk0 h3

end StrictCore
