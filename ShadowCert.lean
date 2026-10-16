import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Join
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Shadow certificates (pure geometry)

An object is a list of corners in `n` dimensions with whole-number coordinates.
A tilt-and-flatten map keeps three directions: three rows of `n` numbers and a shift,
all scaled by one common whole number `D`. The shadow of a corner `v` is
`(r₀·v, r₁·v, r₂·v) + t`, again scaled by `D`.

A certificate claims two things:
* the three rows, divided by `D`, have length one and are at right angles
  (so the map really is a tilt followed by dropping directions, with no stretching), and
* the outline of the shadow has exactly the listed corners.

`Cert.check` verifies a certificate using whole-number arithmetic only.
`Cert.sound` proves, once and for all certificates, that passing the check means exactly what
the certificate claims, stated with Mathlib's own convex hull and extreme points over `ℚ`.
Each particular shadow then needs only `check = true`, which Lean's kernel verifies by computation.
-/

namespace Shadow

/-- Dot product of two lists of whole numbers. -/
def dot : List Int → List Int → Int
  | a :: as, b :: bs => a * b + dot as bs
  | _, _ => 0

/-- A point of 3-space with whole-number coordinates (scaled by `D`). -/
structure V3 where
  x : Int
  y : Int
  z : Int
deriving DecidableEq, Repr

def V3.add (a b : V3) : V3 := ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩
def V3.smul (k : Int) (a : V3) : V3 := ⟨k * a.x, k * a.y, k * a.z⟩
def V3.dot (a b : V3) : Int := a.x * b.x + a.y * b.y + a.z * b.z
def V3.zero : V3 := ⟨0, 0, 0⟩

/-- A shadow certificate. -/
structure Cert where
  /-- the common scale -/
  D : Int
  /-- the object's corners -/
  obj : List (List Int)
  /-- the three kept rows of the tilt, times `D` -/
  r0 : List Int
  r1 : List Int
  r2 : List Int
  /-- the shift, times `D` -/
  t : V3
  /-- the shadow's corners, times `D` -/
  corners : List V3
  /-- `corners[k]` is the shadow of object corner `idx[k]` -/
  idx : List Nat
  /-- `wit[k]` is a direction in which `corners[k]` sticks out further than every other shadow point -/
  wit : List V3
  /-- for each object corner, positive weights on corners whose balance point is its shadow -/
  wts : List (List (Nat × Int))

namespace Cert

/-- the object's number of dimensions -/
def n (c : Cert) : Nat := c.r0.length

/-- the shadow of a corner, times `D` -/
def img (c : Cert) (v : List Int) : V3 :=
  ⟨dot c.r0 v + c.t.x, dot c.r1 v + c.t.y, dot c.r2 v + c.t.z⟩

/-- weighted sum of corners named by position -/
def comb (c : Cert) : List (Nat × Int) → V3
  | [] => V3.zero
  | p :: rest => V3.add (V3.smul p.2 (c.corners.getD p.1 V3.zero)) (comb c rest)

/-- total weight -/
def wsum : List (Nat × Int) → Int
  | [] => 0
  | p :: rest => p.2 + wsum rest

def rowsOK (c : Cert) : Bool :=
  decide (0 < c.D) && c.r1.length == c.n && c.r2.length == c.n &&
  c.obj.all (fun v => v.length == c.n) &&
  dot c.r0 c.r0 == c.D * c.D && dot c.r1 c.r1 == c.D * c.D && dot c.r2 c.r2 == c.D * c.D &&
  dot c.r0 c.r1 == 0 && dot c.r0 c.r2 == 0 && dot c.r1 c.r2 == 0

def matchOK (c : Cert) : Bool :=
  c.idx.length == c.corners.length &&
  (c.corners.zip c.idx).all (fun p => decide (p.2 < c.obj.length) && c.img (c.obj.getD p.2 []) == p.1)

def witOK (c : Cert) : Bool :=
  c.wit.length == c.corners.length &&
  (c.corners.zip c.wit).all (fun p =>
    c.obj.all (fun v => c.img v == p.1 || decide (V3.dot p.2 (c.img v) < V3.dot p.2 p.1)))

def wtsOK (c : Cert) : Bool :=
  c.wts.length == c.obj.length &&
  (c.obj.zip c.wts).all (fun p =>
    !p.2.isEmpty &&
    p.2.all (fun q => decide (q.1 < c.corners.length) && decide (0 < q.2)) &&
    c.comb p.2 == V3.smul (wsum p.2) (c.img p.1))

/-- The whole check: whole-number arithmetic only. -/
def check (c : Cert) : Bool := c.rowsOK && c.matchOK && c.witOK && c.wtsOK

end Cert

/-! ## The geometry, over `ℚ` -/

/-- a scaled whole-number point as an actual point of 3-space -/
def toQ (D : Int) (a : V3) : Fin 3 → ℚ := ![(a.x : ℚ) / D, (a.y : ℚ) / D, (a.z : ℚ) / D]

/-- the shadow: the flattened corners of the object -/
def Cert.shadow (c : Cert) : Set (Fin 3 → ℚ) := {p | ∃ v ∈ c.obj, p = toQ c.D (c.img v)}

/-- the claimed corners -/
def Cert.cornerSet (c : Cert) : Set (Fin 3 → ℚ) := {p | ∃ a ∈ c.corners, p = toQ c.D a}

/-- a straight-line measure of how far a point sticks out in direction `w` -/
def lin (w : V3) (p : Fin 3 → ℚ) : ℚ := (w.x : ℚ) * p 0 + (w.y : ℚ) * p 1 + (w.z : ℚ) * p 2

theorem lin_isLinear (w : V3) : IsLinearMap ℚ (lin w) :=
  ⟨fun x y => by simp only [lin, Pi.add_apply]; ring,
   fun k x => by simp only [lin, Pi.smul_apply, smul_eq_mul]; ring⟩

theorem lin_toQ (w : V3) (D : Int) (a : V3) : lin w (toQ D a) = (V3.dot w a : ℚ) / D := by
  simp only [lin, toQ, V3.dot, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  push_cast; ring

theorem toQ_add (D : Int) (a b : V3) : toQ D (a.add b) = toQ D a + toQ D b := by
  funext i; fin_cases i <;> simp [toQ, V3.add] <;> ring

theorem toQ_smul (D : Int) (k : Int) (a : V3) : toQ D (V3.smul k a) = (k : ℚ) • toQ D a := by
  funext i; fin_cases i <;> simp [toQ, V3.smul] <;> ring

theorem toQ_zero (D : Int) : toQ D V3.zero = 0 := by
  funext i; fin_cases i <;> simp [toQ, V3.zero]

theorem toQ_inj {D : Int} (hD : D ≠ 0) {a b : V3} (h : toQ D a = toQ D b) : a = b := by
  have hD' : (D : ℚ) ≠ 0 := by exact_mod_cast hD
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  simp only [toQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2
  rw [div_left_inj' hD'] at h0 h1 h2
  cases a; cases b
  simp only [V3.mk.injEq]
  exact ⟨by exact_mod_cast h0, by exact_mod_cast h1, by exact_mod_cast h2⟩

/-! ## Two general facts about outlines -/

/-- If `a` sticks out further than every other point of `S` in some straight-line direction,
then no other point of the outline of `S` reaches as far. -/
theorem hull_max_unique {S : Set (Fin 3 → ℚ)} {a : Fin 3 → ℚ} {f : (Fin 3 → ℚ) → ℚ}
    (hf : IsLinearMap ℚ f) (hS : ∀ p ∈ S, p ≠ a → f p < f a) :
    ∀ y ∈ convexHull ℚ S, f a ≤ f y → y = a := by
  intro y hy hfy
  set T : Set (Fin 3 → ℚ) := {p | p ∈ S ∧ p ≠ a} with hTdef
  have hST : S ⊆ insert a T := by
    intro p hp
    by_cases hpa : p = a
    · exact Or.inl hpa
    · exact Or.inr ⟨hp, hpa⟩
  have hy' : y ∈ convexHull ℚ (insert a T) := convexHull_mono hST hy
  rcases Set.eq_empty_or_nonempty T with hT | hT
  · rw [hT] at hy'
    simpa [convexHull_singleton] using hy'
  · rw [convexHull_insert hT, mem_convexJoin] at hy'
    obtain ⟨a', ha', z, hz, hyz⟩ := hy'
    rw [Set.mem_singleton_iff] at ha'
    subst ha'
    have hTlt : convexHull ℚ T ⊆ {w | f w < f a'} :=
      convexHull_min (fun p hp => hS p hp.1 hp.2) (convex_halfSpace_lt hf _)
    have hzlt : f z < f a' := hTlt hz
    obtain ⟨s, t, hs, ht, hst, rfl⟩ := hyz
    have hfy' : f (s • a' + t • z) = s * f a' + t * f z := by
      rw [hf.map_add, hf.map_smul, hf.map_smul, smul_eq_mul, smul_eq_mul]
    rw [hfy'] at hfy
    rcases eq_or_lt_of_le ht with ht0 | ht0
    · subst ht0
      have : s = 1 := by linarith
      subst this
      simp
    · exfalso
      have : t * f z < t * f a' := mul_lt_mul_of_pos_left hzlt ht0
      have hsum1 : s * f a' + t * f a' = f a' := by rw [← add_mul, hst, one_mul]
      linarith

/-- Such a point is a genuine corner (an extreme point) of the outline. -/
theorem mem_extreme {S : Set (Fin 3 → ℚ)} {a : Fin 3 → ℚ} {f : (Fin 3 → ℚ) → ℚ}
    (hf : IsLinearMap ℚ f) (ha : a ∈ S) (hS : ∀ p ∈ S, p ≠ a → f p < f a) :
    a ∈ (convexHull ℚ S).extremePoints ℚ := by
  have hle : convexHull ℚ S ⊆ {w | f w ≤ f a} := by
    refine convexHull_min (fun p hp => ?_) (convex_halfSpace_le hf _)
    by_cases hpa : p = a
    · show f p ≤ f a
      rw [hpa]
    · exact le_of_lt (hS p hp hpa)
  rw [mem_extremePoints]
  refine ⟨subset_convexHull ℚ S ha, fun x₁ hx₁ x₂ hx₂ hx => ?_⟩
  obtain ⟨s, t, hs, ht, hst, hsum⟩ := hx
  have h1 : f x₁ ≤ f a := hle hx₁
  have h2 : f x₂ ≤ f a := hle hx₂
  have hfa : f a = s * f x₁ + t * f x₂ := by
    rw [← hsum, hf.map_add, hf.map_smul, hf.map_smul, smul_eq_mul, smul_eq_mul]
  have key : s * (f a - f x₁) + t * (f a - f x₂) = 0 := by
    linear_combination (f a) * hst + hfa
  have n1 : 0 ≤ s * (f a - f x₁) := mul_nonneg hs.le (sub_nonneg.2 h1)
  have n2 : 0 ≤ t * (f a - f x₂) := mul_nonneg ht.le (sub_nonneg.2 h2)
  have k1 : s * (f a - f x₁) = 0 := le_antisymm (by linarith) n1
  have k2 : t * (f a - f x₂) = 0 := le_antisymm (by linarith) n2
  have e1 : f a ≤ f x₁ := by
    rcases mul_eq_zero.1 k1 with h | h
    · exact absurd h hs.ne'
    · linarith
  have e2 : f a ≤ f x₂ := by
    rcases mul_eq_zero.1 k2 with h | h
    · exact absurd h ht.ne'
    · linarith
  exact ⟨hull_max_unique hf hS x₁ hx₁ e1, hull_max_unique hf hS x₂ hx₂ e2⟩

/-! ## Reading a passing check -/

theorem getD_of_lt {α : Type*} {l : List α} {i : Nat} (d : α) (h : i < l.length) :
    l.getD i d = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

theorem exists_zip_left {α β : Type*} {l₁ : List α} {l₂ : List β} (h : l₁.length = l₂.length)
    {a : α} (ha : a ∈ l₁) : ∃ b, (a, b) ∈ l₁.zip l₂ := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
  have hi2 : i < l₂.length := h ▸ hi
  refine ⟨l₂[i], ?_⟩
  have hz : i < (l₁.zip l₂).length := by simp [List.length_zip, hi, hi2]
  have := List.getElem_mem hz
  rwa [List.getElem_zip] at this

namespace Cert

theorem toQ_comb (c : Cert) (ws : List (Nat × Int)) :
    toQ c.D (c.comb ws) = ((ws.map fun p => (p.2 : ℚ) • toQ c.D (c.corners.getD p.1 V3.zero)).sum) := by
  induction ws with
  | nil => simp [comb, toQ_zero]
  | cons p rest ih => simp [comb, toQ_add, toQ_smul, ih]

theorem wsum_pos (ws : List (Nat × Int)) (hne : ws ≠ []) (hpos : ∀ p ∈ ws, 0 < p.2) : 0 < wsum ws := by
  induction ws with
  | nil => exact absurd rfl hne
  | cons p rest ih =>
    simp only [wsum]
    have hp := hpos p (by simp)
    by_cases hr : rest = []
    · subst hr; simp [wsum]; exact hp
    · have := ih hr (fun q hq => hpos q (by simp [hq]))
      linarith

/-- A positively weighted collection of claimed corners balances at a point of their outline. -/
theorem comb_mem (c : Cert) (ws : List (Nat × Int)) (hne : ws ≠ [])
    (hok : ∀ p ∈ ws, p.1 < c.corners.length ∧ 0 < p.2) :
    ∃ q ∈ convexHull ℚ c.cornerSet, toQ c.D (c.comb ws) = ((wsum ws : Int) : ℚ) • q := by
  induction ws with
  | nil => exact absurd rfl hne
  | cons p rest ih =>
    obtain ⟨hk, hw⟩ := hok p (by simp)
    have hP : toQ c.D (c.corners.getD p.1 V3.zero) ∈ convexHull ℚ c.cornerSet := by
      apply subset_convexHull
      refine ⟨c.corners.getD p.1 V3.zero, ?_, rfl⟩
      rw [getD_of_lt _ hk]
      exact List.getElem_mem hk
    by_cases hr : rest = []
    · subst hr
      refine ⟨_, hP, ?_⟩
      simp [comb, wsum, toQ_add, toQ_smul, toQ_zero]
    · obtain ⟨q', hq', heq'⟩ := ih hr (fun q hq => hok q (by simp [hq]))
      have hW' : (0 : ℚ) < (wsum rest : ℚ) := by
        exact_mod_cast wsum_pos rest hr (fun q hq => (hok q (by simp [hq])).2)
      have hw' : (0 : ℚ) < (p.2 : ℚ) := by exact_mod_cast hw
      have htot : (0 : ℚ) < (p.2 : ℚ) + (wsum rest : ℚ) := by linarith
      set P := toQ c.D (c.corners.getD p.1 V3.zero)
      refine ⟨((p.2 : ℚ) / ((p.2 : ℚ) + wsum rest)) • P +
              ((wsum rest : ℚ) / ((p.2 : ℚ) + wsum rest)) • q', ?_, ?_⟩
      · exact convex_convexHull ℚ _ hP hq' (div_nonneg hw'.le htot.le) (div_nonneg hW'.le htot.le)
          (by field_simp)
      · simp only [comb, wsum, toQ_add, toQ_smul]
        rw [heq']
        funext i
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        push_cast
        field_simp
        rfl

/-- **Soundness.** If a certificate passes the whole-number check, then:
the rows (divided by `D`) have length one and are at right angles, and the outline of the
object's shadow is the outline of the listed corners, whose corners are exactly the listed ones. -/
theorem sound (c : Cert) (h : c.check = true) :
    (c.r1.length = c.n ∧ c.r2.length = c.n ∧ ∀ v ∈ c.obj, v.length = c.n) ∧
    ((dot c.r0 c.r0 : ℚ) / (c.D * c.D) = 1 ∧ (dot c.r1 c.r1 : ℚ) / (c.D * c.D) = 1 ∧
      (dot c.r2 c.r2 : ℚ) / (c.D * c.D) = 1 ∧
      (dot c.r0 c.r1 : ℚ) = 0 ∧ (dot c.r0 c.r2 : ℚ) = 0 ∧ (dot c.r1 c.r2 : ℚ) = 0) ∧
    convexHull ℚ c.shadow = convexHull ℚ c.cornerSet ∧
    (convexHull ℚ c.shadow).extremePoints ℚ = c.cornerSet := by
  simp only [check, rowsOK, matchOK, witOK, wtsOK, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hD, hl1⟩, hl2⟩, hlv⟩, h00⟩, h11⟩, h22⟩, h01⟩, h02⟩, h12⟩,
    ⟨hidxl, hmatch⟩⟩, ⟨hwitl, hwit⟩⟩, ⟨hwtsl, hwts⟩⟩ := h
  have hDq : (c.D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  have hDD : (c.D : ℚ) * c.D ≠ 0 := mul_ne_zero hDq hDq
  -- corners are shadows of object corners
  have hCS : c.cornerSet ⊆ c.shadow := by
    rintro p ⟨a, ha, rfl⟩
    obtain ⟨i, hi⟩ := exists_zip_left hidxl.symm ha
    obtain ⟨hilt, himg⟩ := hmatch (a, i) hi
    refine ⟨c.obj.getD i [], ?_, by rw [himg]⟩
    rw [getD_of_lt _ hilt]
    exact List.getElem_mem hilt
  -- every shadow point lies in the outline of the corners
  have hSC : c.shadow ⊆ convexHull ℚ c.cornerSet := by
    rintro p ⟨v, hv, rfl⟩
    obtain ⟨ws, hws⟩ := exists_zip_left hwtsl.symm hv
    obtain ⟨⟨hne, hall⟩, hcomb⟩ := hwts (v, ws) hws
    simp only [Bool.not_eq_true', List.isEmpty_eq_false_iff] at hne
    have hok : ∀ q ∈ ws, q.1 < c.corners.length ∧ 0 < q.2 := by
      intro q hq
      have := hall q hq
      simpa [Bool.and_eq_true, decide_eq_true_eq] using this
    obtain ⟨q, hq, heq⟩ := comb_mem c ws hne hok
    have hW : ((wsum ws : Int) : ℚ) ≠ 0 := by
      exact_mod_cast (wsum_pos ws hne (fun q hq => (hok q hq).2)).ne'
    have : toQ c.D (c.comb ws) = ((wsum ws : Int) : ℚ) • toQ c.D (c.img v) := by
      rw [hcomb, toQ_smul]
    rw [this] at heq
    have := smul_right_injective (Fin 3 → ℚ) hW heq
    rw [this]; exact hq
  have hhull : convexHull ℚ c.shadow = convexHull ℚ c.cornerSet :=
    le_antisymm (convexHull_min hSC (convex_convexHull ℚ _)) (convexHull_mono hCS)
  refine ⟨⟨hl1, hl2, fun v hv => hlv v hv⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, hhull, ?_⟩
  · rw [show (dot c.r0 c.r0 : ℚ) = c.D * c.D by exact_mod_cast h00]; exact div_self hDD
  · rw [show (dot c.r1 c.r1 : ℚ) = c.D * c.D by exact_mod_cast h11]; exact div_self hDD
  · rw [show (dot c.r2 c.r2 : ℚ) = c.D * c.D by exact_mod_cast h22]; exact div_self hDD
  · exact_mod_cast h01
  · exact_mod_cast h02
  · exact_mod_cast h12
  · apply le_antisymm
    · rw [hhull]; exact extremePoints_convexHull_subset
    · rintro p ⟨a, ha, rfl⟩
      obtain ⟨w, hw⟩ := exists_zip_left hwitl.symm ha
      have hwa := hwit (a, w) hw
      refine mem_extreme (lin_isLinear w) (hCS ⟨a, ha, rfl⟩) ?_
      rintro p ⟨v, hv, rfl⟩ hne
      have hv' := hwa v hv
      simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hv'
      rcases hv' with heq | hlt
      · exact absurd (by rw [heq]) hne
      · rw [lin_toQ, lin_toQ]
        have hDpos : (0 : ℚ) < c.D := by exact_mod_cast hD
        exact div_lt_div_of_pos_right (by exact_mod_cast hlt) hDpos

end Cert

end Shadow
