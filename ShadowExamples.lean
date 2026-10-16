import ShadowCert

/-! Shadow certificates written by shadow_workbench.py. Each one: the tilt is exact, and
the outline of the object's shadow has exactly the listed corners (see `Shadow.Cert.sound`). -/

namespace Shadow.Examples

open Shadow Shadow.Cert

def cube4_straight_on : Cert where
  D := 1
  obj := [[-1, -1, -1, -1], [-1, -1, -1, 1], [-1, -1, 1, -1], [-1, -1, 1, 1], [-1, 1, -1, -1], [-1, 1, -1, 1], [-1, 1, 1, -1], [-1, 1, 1, 1], [1, -1, -1, -1], [1, -1, -1, 1], [1, -1, 1, -1], [1, -1, 1, 1], [1, 1, -1, -1], [1, 1, -1, 1], [1, 1, 1, -1], [1, 1, 1, 1]]
  r0 := [1, 0, 0, 0]
  r1 := [0, 1, 0, 0]
  r2 := [0, 0, 1, 0]
  t := ⟨0, 0, 0⟩
  corners := [⟨-1, -1, -1⟩, ⟨-1, -1, 1⟩, ⟨-1, 1, -1⟩, ⟨-1, 1, 1⟩, ⟨1, -1, -1⟩, ⟨1, -1, 1⟩, ⟨1, 1, -1⟩, ⟨1, 1, 1⟩]
  idx := [0, 2, 4, 6, 8, 10, 12, 14]
  wit := [⟨-1, -1, -1⟩, ⟨-1, -1, 1⟩, ⟨-1, 1, -1⟩, ⟨-1, 1, 1⟩, ⟨1, -1, -1⟩, ⟨1, -1, 1⟩, ⟨1, 1, -1⟩, ⟨1, 1, 1⟩]
  wts := [[(0, 1)], [(0, 1)], [(1, 1)], [(1, 1)], [(2, 1)], [(2, 1)], [(3, 1)], [(3, 1)], [(4, 1)], [(4, 1)], [(5, 1)], [(5, 1)], [(6, 1)], [(6, 1)], [(7, 1)], [(7, 1)]]

theorem cube4_straight_on_checks : cube4_straight_on.check = true := by decide +kernel

/-- cube4_straight_on: the tilt is exact (rows of length one at right angles, after dividing by D). -/
theorem cube4_straight_on_tilt_exact :
    (dot cube4_straight_on.r0 cube4_straight_on.r0 : ℚ) / (cube4_straight_on.D * cube4_straight_on.D) = 1 ∧ (dot cube4_straight_on.r1 cube4_straight_on.r1 : ℚ) / (cube4_straight_on.D * cube4_straight_on.D) = 1 ∧
    (dot cube4_straight_on.r2 cube4_straight_on.r2 : ℚ) / (cube4_straight_on.D * cube4_straight_on.D) = 1 ∧
    (dot cube4_straight_on.r0 cube4_straight_on.r1 : ℚ) = 0 ∧ (dot cube4_straight_on.r0 cube4_straight_on.r2 : ℚ) = 0 ∧ (dot cube4_straight_on.r1 cube4_straight_on.r2 : ℚ) = 0 :=
  (Cert.sound cube4_straight_on cube4_straight_on_checks).2.1

/-- cube4_straight_on: the outline of the object's shadow is the outline of the listed corners,
and its corners are exactly the listed ones. -/
theorem cube4_straight_on_casts :
    convexHull ℚ cube4_straight_on.shadow = convexHull ℚ cube4_straight_on.cornerSet ∧
    (convexHull ℚ cube4_straight_on.shadow).extremePoints ℚ = cube4_straight_on.cornerSet :=
  (Cert.sound cube4_straight_on cube4_straight_on_checks).2.2

def cube4_corner_first : Cert where
  D := 2
  obj := [[-1, -1, -1, -1], [-1, -1, -1, 1], [-1, -1, 1, -1], [-1, -1, 1, 1], [-1, 1, -1, -1], [-1, 1, -1, 1], [-1, 1, 1, -1], [-1, 1, 1, 1], [1, -1, -1, -1], [1, -1, -1, 1], [1, -1, 1, -1], [1, -1, 1, 1], [1, 1, -1, -1], [1, 1, -1, 1], [1, 1, 1, -1], [1, 1, 1, 1]]
  r0 := [1, -1, 1, -1]
  r1 := [1, 1, -1, -1]
  r2 := [1, -1, -1, 1]
  t := ⟨0, 0, 0⟩
  corners := [⟨-4, 0, 0⟩, ⟨-2, -2, -2⟩, ⟨-2, -2, 2⟩, ⟨-2, 2, -2⟩, ⟨-2, 2, 2⟩, ⟨0, -4, 0⟩, ⟨0, 0, -4⟩, ⟨0, 0, 4⟩, ⟨0, 4, 0⟩, ⟨2, -2, -2⟩, ⟨2, -2, 2⟩, ⟨2, 2, -2⟩, ⟨2, 2, 2⟩, ⟨4, 0, 0⟩]
  idx := [5, 7, 1, 4, 13, 3, 6, 9, 12, 2, 11, 14, 8, 10]
  wit := [⟨-4, 0, 0⟩, ⟨-2, -2, -2⟩, ⟨-2, -2, 2⟩, ⟨-2, 2, -2⟩, ⟨-2, 2, 2⟩, ⟨0, -4, 0⟩, ⟨0, 0, -4⟩, ⟨0, 0, 4⟩, ⟨0, 4, 0⟩, ⟨2, -2, -2⟩, ⟨2, -2, 2⟩, ⟨2, 2, -2⟩, ⟨2, 2, 2⟩, ⟨4, 0, 0⟩]
  wts := [[(0, 1), (13, 1)], [(2, 1)], [(9, 1)], [(5, 1)], [(3, 1)], [(0, 1)], [(6, 1)], [(1, 1)], [(12, 1)], [(7, 1)], [(13, 1)], [(10, 1)], [(8, 1)], [(4, 1)], [(11, 1)], [(0, 1), (13, 1)]]

theorem cube4_corner_first_checks : cube4_corner_first.check = true := by decide +kernel

/-- cube4_corner_first: the tilt is exact (rows of length one at right angles, after dividing by D). -/
theorem cube4_corner_first_tilt_exact :
    (dot cube4_corner_first.r0 cube4_corner_first.r0 : ℚ) / (cube4_corner_first.D * cube4_corner_first.D) = 1 ∧ (dot cube4_corner_first.r1 cube4_corner_first.r1 : ℚ) / (cube4_corner_first.D * cube4_corner_first.D) = 1 ∧
    (dot cube4_corner_first.r2 cube4_corner_first.r2 : ℚ) / (cube4_corner_first.D * cube4_corner_first.D) = 1 ∧
    (dot cube4_corner_first.r0 cube4_corner_first.r1 : ℚ) = 0 ∧ (dot cube4_corner_first.r0 cube4_corner_first.r2 : ℚ) = 0 ∧ (dot cube4_corner_first.r1 cube4_corner_first.r2 : ℚ) = 0 :=
  (Cert.sound cube4_corner_first cube4_corner_first_checks).2.1

/-- cube4_corner_first: the outline of the object's shadow is the outline of the listed corners,
and its corners are exactly the listed ones. -/
theorem cube4_corner_first_casts :
    convexHull ℚ cube4_corner_first.shadow = convexHull ℚ cube4_corner_first.cornerSet ∧
    (convexHull ℚ cube4_corner_first.shadow).extremePoints ℚ = cube4_corner_first.cornerSet :=
  (Cert.sound cube4_corner_first cube4_corner_first_checks).2.2

def cube4_found_1 : Cert where
  D := 81
  obj := [[-1, -1, -1, -1], [-1, -1, -1, 1], [-1, -1, 1, -1], [-1, -1, 1, 1], [-1, 1, -1, -1], [-1, 1, -1, 1], [-1, 1, 1, -1], [-1, 1, 1, 1], [1, -1, -1, -1], [1, -1, -1, 1], [1, -1, 1, -1], [1, -1, 1, 1], [1, 1, -1, -1], [1, 1, -1, 1], [1, 1, 1, -1], [1, 1, 1, 1]]
  r0 := [42, 26, -5, 64]
  r1 := [36, 3, -66, -30]
  r2 := [-30, 74, -8, -11]
  t := ⟨405, -243, 243⟩
  corners := [⟨268, -318, 202⟩, ⟨278, -186, 218⟩, ⟨320, -312, 350⟩, ⟨330, -180, 366⟩, ⟨352, -246, 142⟩, ⟨362, -114, 158⟩, ⟨396, -378, 180⟩, ⟨414, -108, 306⟩, ⟨448, -372, 328⟩, ⟨458, -240, 344⟩, ⟨480, -306, 120⟩, ⟨490, -174, 136⟩, ⟨532, -300, 268⟩, ⟨542, -168, 284⟩]
  idx := [2, 0, 6, 4, 10, 8, 3, 12, 7, 5, 11, 9, 15, 13]
  wit := [⟨-109, -66, -5⟩, ⟨-91, 29, 10⟩, ⟨-81, -67, 87⟩, ⟨-63, 28, 102⟩, ⟨-28, 1, -92⟩, ⟨-10, 96, -77⟩, ⟨-18, -95, -15⟩, ⟨18, 95, 15⟩, ⟨10, -96, 77⟩, ⟨28, -1, 92⟩, ⟨63, -28, -102⟩, ⟨81, 67, -87⟩, ⟨91, -29, -10⟩, ⟨109, 66, 5⟩]
  wts := [[(1, 1)], [(0, 38), (10, 8), (11, 23), (13, 20)], [(0, 1)], [(6, 1)], [(3, 1)], [(9, 1)], [(2, 1)], [(8, 1)], [(5, 1)], [(11, 1)], [(4, 1)], [(10, 1)], [(7, 1)], [(13, 1)], [(0, 20), (3, 8), (9, 23), (13, 15)], [(12, 1)]]

theorem cube4_found_1_checks : cube4_found_1.check = true := by decide +kernel

/-- cube4_found_1: the tilt is exact (rows of length one at right angles, after dividing by D). -/
theorem cube4_found_1_tilt_exact :
    (dot cube4_found_1.r0 cube4_found_1.r0 : ℚ) / (cube4_found_1.D * cube4_found_1.D) = 1 ∧ (dot cube4_found_1.r1 cube4_found_1.r1 : ℚ) / (cube4_found_1.D * cube4_found_1.D) = 1 ∧
    (dot cube4_found_1.r2 cube4_found_1.r2 : ℚ) / (cube4_found_1.D * cube4_found_1.D) = 1 ∧
    (dot cube4_found_1.r0 cube4_found_1.r1 : ℚ) = 0 ∧ (dot cube4_found_1.r0 cube4_found_1.r2 : ℚ) = 0 ∧ (dot cube4_found_1.r1 cube4_found_1.r2 : ℚ) = 0 :=
  (Cert.sound cube4_found_1 cube4_found_1_checks).2.1

/-- cube4_found_1: the outline of the object's shadow is the outline of the listed corners,
and its corners are exactly the listed ones. -/
theorem cube4_found_1_casts :
    convexHull ℚ cube4_found_1.shadow = convexHull ℚ cube4_found_1.cornerSet ∧
    (convexHull ℚ cube4_found_1.shadow).extremePoints ℚ = cube4_found_1.cornerSet :=
  (Cert.sound cube4_found_1 cube4_found_1_checks).2.2

def cube4_found_2 : Cert where
  D := 693
  obj := [[-1, -1, -1, -1], [-1, -1, -1, 1], [-1, -1, 1, -1], [-1, -1, 1, 1], [-1, 1, -1, -1], [-1, 1, -1, 1], [-1, 1, 1, -1], [-1, 1, 1, 1], [1, -1, -1, -1], [1, -1, -1, 1], [1, -1, 1, -1], [1, -1, 1, 1], [1, 1, -1, -1], [1, 1, -1, 1], [1, 1, 1, -1], [1, 1, 1, 1]]
  r0 := [368, -132, 280, 499]
  r1 := [-557, 132, 224, 320]
  r2 := [-60, -99, -588, 348]
  t := ⟨3465, -1386, -2079⟩
  corners := [⟨2186, -1241, -1878⟩, ⟨2450, -1505, -1680⟩, ⟨2746, -793, -3054⟩, ⟨2922, -2355, -1998⟩, ⟨3184, -601, -1182⟩, ⟨3186, -2619, -1800⟩, ⟨3448, -865, -984⟩, ⟨3482, -1907, -3174⟩, ⟨3744, -153, -2358⟩, ⟨3746, -2171, -2976⟩, ⟨4008, -417, -2160⟩, ⟨4184, -1979, -1104⟩, ⟨4480, -1267, -2478⟩, ⟨4744, -1531, -2280⟩]
  idx := [4, 0, 6, 12, 5, 8, 1, 14, 7, 10, 3, 9, 15, 11]
  wit := [⟨-422, 10, 114⟩, ⟨-455, -287, 763⟩, ⟨33, 297, -649⟩, ⟨-224, -155, -62⟩, ⟨-198, 165, 176⟩, ⟨-257, -452, 587⟩, ⟨-231, -132, 825⟩, ⟨231, 132, -825⟩, ⟨257, 452, -587⟩, ⟨198, -165, -176⟩, ⟨224, 155, 62⟩, ⟨-33, -297, 649⟩, ⟨455, 287, -763⟩, ⟨422, -10, -114⟩]
  wts := [[(1, 1)], [(6, 1)], [(0, 7), (2, 29), (7, 16), (8, 8)], [(10, 1)], [(0, 1)], [(4, 1)], [(2, 1)], [(8, 1)], [(5, 1)], [(11, 1)], [(9, 1)], [(13, 1)], [(3, 1)], [(0, 8), (6, 1), (10, 7), (11, 52)], [(7, 1)], [(12, 1)]]

theorem cube4_found_2_checks : cube4_found_2.check = true := by decide +kernel

/-- cube4_found_2: the tilt is exact (rows of length one at right angles, after dividing by D). -/
theorem cube4_found_2_tilt_exact :
    (dot cube4_found_2.r0 cube4_found_2.r0 : ℚ) / (cube4_found_2.D * cube4_found_2.D) = 1 ∧ (dot cube4_found_2.r1 cube4_found_2.r1 : ℚ) / (cube4_found_2.D * cube4_found_2.D) = 1 ∧
    (dot cube4_found_2.r2 cube4_found_2.r2 : ℚ) / (cube4_found_2.D * cube4_found_2.D) = 1 ∧
    (dot cube4_found_2.r0 cube4_found_2.r1 : ℚ) = 0 ∧ (dot cube4_found_2.r0 cube4_found_2.r2 : ℚ) = 0 ∧ (dot cube4_found_2.r1 cube4_found_2.r2 : ℚ) = 0 :=
  (Cert.sound cube4_found_2 cube4_found_2_checks).2.1

/-- cube4_found_2: the outline of the object's shadow is the outline of the listed corners,
and its corners are exactly the listed ones. -/
theorem cube4_found_2_casts :
    convexHull ℚ cube4_found_2.shadow = convexHull ℚ cube4_found_2.cornerSet ∧
    (convexHull ℚ cube4_found_2.shadow).extremePoints ℚ = cube4_found_2.cornerSet :=
  (Cert.sound cube4_found_2 cube4_found_2_checks).2.2

def cube4_found_3 : Cert where
  D := 143
  obj := [[-1, -1, -1, -1], [-1, -1, -1, 1], [-1, -1, 1, -1], [-1, -1, 1, 1], [-1, 1, -1, -1], [-1, 1, -1, 1], [-1, 1, 1, -1], [-1, 1, 1, 1], [1, -1, -1, -1], [1, -1, -1, 1], [1, -1, 1, -1], [1, -1, 1, 1], [1, 1, -1, -1], [1, 1, -1, 1], [1, 1, 1, -1], [1, 1, 1, 1]]
  r0 := [96, -12, 33, 100]
  r1 := [91, 78, 0, -78]
  r2 := [54, -114, -44, -51]
  t := ⟨715, 286, 143⟩
  corners := [⟨474, 351, 70⟩, ⟨498, 195, 298⟩, ⟨540, 351, -18⟩, ⟨666, 533, 178⟩, ⟨674, 195, -32⟩, ⟨690, 377, 406⟩, ⟨698, 39, 196⟩, ⟨732, 533, 90⟩, ⟨740, 195, -120⟩, ⟨756, 377, 318⟩, ⟨764, 39, 108⟩, ⟨890, 221, 304⟩, ⟨932, 377, -12⟩, ⟨956, 221, 216⟩]
  idx := [4, 0, 6, 12, 5, 8, 1, 14, 7, 10, 3, 9, 15, 11]
  wit := [⟨-60, -15, -19⟩, ⟨-29, -74, 118⟩, ⟨-31, 59, -137⟩, ⟨-17, 23, 10⟩, ⟨-43, -38, -29⟩, ⟨14, -36, 147⟩, ⟨-12, -97, 108⟩, ⟨12, 97, -108⟩, ⟨-14, 36, -147⟩, ⟨43, 38, 29⟩, ⟨17, -23, -10⟩, ⟨31, -59, 137⟩, ⟨29, 74, -118⟩, ⟨60, 15, 19⟩]
  wts := [[(1, 1)], [(6, 1)], [(0, 35), (1, 49), (5, 6), (6, 42)], [(10, 1)], [(0, 1)], [(4, 1)], [(2, 1)], [(8, 1)], [(5, 1)], [(11, 1)], [(9, 1)], [(13, 1)], [(3, 1)], [(0, 6), (7, 1), (9, 35), (12, 96)], [(7, 1)], [(12, 1)]]

theorem cube4_found_3_checks : cube4_found_3.check = true := by decide +kernel

/-- cube4_found_3: the tilt is exact (rows of length one at right angles, after dividing by D). -/
theorem cube4_found_3_tilt_exact :
    (dot cube4_found_3.r0 cube4_found_3.r0 : ℚ) / (cube4_found_3.D * cube4_found_3.D) = 1 ∧ (dot cube4_found_3.r1 cube4_found_3.r1 : ℚ) / (cube4_found_3.D * cube4_found_3.D) = 1 ∧
    (dot cube4_found_3.r2 cube4_found_3.r2 : ℚ) / (cube4_found_3.D * cube4_found_3.D) = 1 ∧
    (dot cube4_found_3.r0 cube4_found_3.r1 : ℚ) = 0 ∧ (dot cube4_found_3.r0 cube4_found_3.r2 : ℚ) = 0 ∧ (dot cube4_found_3.r1 cube4_found_3.r2 : ℚ) = 0 :=
  (Cert.sound cube4_found_3 cube4_found_3_checks).2.1

/-- cube4_found_3: the outline of the object's shadow is the outline of the listed corners,
and its corners are exactly the listed ones. -/
theorem cube4_found_3_casts :
    convexHull ℚ cube4_found_3.shadow = convexHull ℚ cube4_found_3.cornerSet ∧
    (convexHull ℚ cube4_found_3.shadow).extremePoints ℚ = cube4_found_3.cornerSet :=
  (Cert.sound cube4_found_3 cube4_found_3_checks).2.2

def cell16_found_1 : Cert where
  D := 39
  obj := [[1, 0, 0, 0], [-1, 0, 0, 0], [0, 1, 0, 0], [0, -1, 0, 0], [0, 0, 1, 0], [0, 0, -1, 0], [0, 0, 0, 1], [0, 0, 0, -1]]
  r0 := [-6, -3, 24, 30]
  r1 := [19, -10, -24, 22]
  r2 := [10, -34, 12, -11]
  t := ⟨-156, 117, 195⟩
  corners := [⟨-186, 95, 206⟩, ⟨-180, 141, 183⟩, ⟨-162, 136, 205⟩, ⟨-159, 107, 161⟩, ⟨-153, 127, 229⟩, ⟨-150, 98, 185⟩, ⟨-132, 93, 207⟩, ⟨-126, 139, 184⟩]
  idx := [7, 5, 0, 2, 3, 1, 4, 6]
  wit := [⟨-96, -56, 41⟩, ⟨-91, 81, -33⟩, ⟨0, 45, 12⟩, ⟨3, -16, -116⟩, ⟨-3, 16, 116⟩, ⟨0, -45, -12⟩, ⟨91, -81, 33⟩, ⟨96, 56, -41⟩]
  wts := [[(2, 1)], [(5, 1)], [(3, 1)], [(4, 1)], [(6, 1)], [(1, 1)], [(7, 1)], [(0, 1)]]

theorem cell16_found_1_checks : cell16_found_1.check = true := by decide +kernel

/-- cell16_found_1: the tilt is exact (rows of length one at right angles, after dividing by D). -/
theorem cell16_found_1_tilt_exact :
    (dot cell16_found_1.r0 cell16_found_1.r0 : ℚ) / (cell16_found_1.D * cell16_found_1.D) = 1 ∧ (dot cell16_found_1.r1 cell16_found_1.r1 : ℚ) / (cell16_found_1.D * cell16_found_1.D) = 1 ∧
    (dot cell16_found_1.r2 cell16_found_1.r2 : ℚ) / (cell16_found_1.D * cell16_found_1.D) = 1 ∧
    (dot cell16_found_1.r0 cell16_found_1.r1 : ℚ) = 0 ∧ (dot cell16_found_1.r0 cell16_found_1.r2 : ℚ) = 0 ∧ (dot cell16_found_1.r1 cell16_found_1.r2 : ℚ) = 0 :=
  (Cert.sound cell16_found_1 cell16_found_1_checks).2.1

/-- cell16_found_1: the outline of the object's shadow is the outline of the listed corners,
and its corners are exactly the listed ones. -/
theorem cell16_found_1_casts :
    convexHull ℚ cell16_found_1.shadow = convexHull ℚ cell16_found_1.cornerSet ∧
    (convexHull ℚ cell16_found_1.shadow).extremePoints ℚ = cell16_found_1.cornerSet :=
  (Cert.sound cell16_found_1 cell16_found_1_checks).2.2

def cell16_found_2 : Cert where
  D := 2729
  obj := [[1, 0, 0, 0], [-1, 0, 0, 0], [0, 1, 0, 0], [0, -1, 0, 0], [0, 0, 1, 0], [0, 0, -1, 0], [0, 0, 0, 1], [0, 0, 0, -1]]
  r0 := [-1128, -852, 1217, 1992]
  r1 := [-1087, -792, -2328, 468]
  r2 := [108, 2288, -552, 1377]
  t := ⟨10916, 10916, -5458⟩
  corners := [⟨8924, 10448, -6835⟩, ⟨9699, 13244, -4906⟩, ⟨9788, 9829, -5350⟩, ⟨10064, 10124, -3170⟩, ⟨11768, 11708, -7746⟩, ⟨12044, 12003, -5566⟩, ⟨12133, 8588, -6010⟩, ⟨12908, 11384, -4081⟩]
  idx := [7, 5, 0, 2, 3, 1, 4, 6]
  wit := [⟨-7528, -1452, -4699⟩, ⟨-3823, 7860, 1884⟩, ⟨-2400, -3965, 396⟩, ⟨-3495, -2583, 7771⟩, ⟨3495, 2583, -7771⟩, ⟨2400, 3965, -396⟩, ⟨3823, -7860, -1884⟩, ⟨7528, 1452, 4699⟩]
  wts := [[(2, 1)], [(5, 1)], [(3, 1)], [(4, 1)], [(6, 1)], [(1, 1)], [(7, 1)], [(0, 1)]]

theorem cell16_found_2_checks : cell16_found_2.check = true := by decide +kernel

/-- cell16_found_2: the tilt is exact (rows of length one at right angles, after dividing by D). -/
theorem cell16_found_2_tilt_exact :
    (dot cell16_found_2.r0 cell16_found_2.r0 : ℚ) / (cell16_found_2.D * cell16_found_2.D) = 1 ∧ (dot cell16_found_2.r1 cell16_found_2.r1 : ℚ) / (cell16_found_2.D * cell16_found_2.D) = 1 ∧
    (dot cell16_found_2.r2 cell16_found_2.r2 : ℚ) / (cell16_found_2.D * cell16_found_2.D) = 1 ∧
    (dot cell16_found_2.r0 cell16_found_2.r1 : ℚ) = 0 ∧ (dot cell16_found_2.r0 cell16_found_2.r2 : ℚ) = 0 ∧ (dot cell16_found_2.r1 cell16_found_2.r2 : ℚ) = 0 :=
  (Cert.sound cell16_found_2 cell16_found_2_checks).2.1

/-- cell16_found_2: the outline of the object's shadow is the outline of the listed corners,
and its corners are exactly the listed ones. -/
theorem cell16_found_2_casts :
    convexHull ℚ cell16_found_2.shadow = convexHull ℚ cell16_found_2.cornerSet ∧
    (convexHull ℚ cell16_found_2.shadow).extremePoints ℚ = cell16_found_2.cornerSet :=
  (Cert.sound cell16_found_2 cell16_found_2_checks).2.2

def cell16_found_3 : Cert where
  D := 229
  obj := [[1, 0, 0, 0], [-1, 0, 0, 0], [0, 1, 0, 0], [0, -1, 0, 0], [0, 0, 1, 0], [0, 0, -1, 0], [0, 0, 0, 1], [0, 0, 0, -1]]
  r0 := [-174, -57, 104, 90]
  r1 := [78, 144, 135, 86]
  r2 := [-120, 166, -102, -9]
  t := ⟨-916, 0, 458⟩
  corners := [⟨-1090, 78, 338⟩, ⟨-1020, -135, 560⟩, ⟨-973, 144, 624⟩, ⟨-859, -144, 292⟩, ⟨-812, 135, 356⟩, ⟨-742, -78, 578⟩]
  idx := [0, 5, 2, 3, 4, 1]
  wit := [⟨-648, 200, -396⟩, ⟨-528, -624, 360⟩, ⟨-144, 528, 552⟩, ⟨144, -528, -552⟩, ⟨528, 624, -360⟩, ⟨648, -200, 396⟩]
  wts := [[(0, 1)], [(5, 1)], [(2, 1)], [(3, 1)], [(4, 1)], [(1, 1)], [(0, 7), (2, 60), (4, 228), (5, 89)], [(0, 89), (1, 228), (3, 60), (5, 7)]]

theorem cell16_found_3_checks : cell16_found_3.check = true := by decide +kernel

/-- cell16_found_3: the tilt is exact (rows of length one at right angles, after dividing by D). -/
theorem cell16_found_3_tilt_exact :
    (dot cell16_found_3.r0 cell16_found_3.r0 : ℚ) / (cell16_found_3.D * cell16_found_3.D) = 1 ∧ (dot cell16_found_3.r1 cell16_found_3.r1 : ℚ) / (cell16_found_3.D * cell16_found_3.D) = 1 ∧
    (dot cell16_found_3.r2 cell16_found_3.r2 : ℚ) / (cell16_found_3.D * cell16_found_3.D) = 1 ∧
    (dot cell16_found_3.r0 cell16_found_3.r1 : ℚ) = 0 ∧ (dot cell16_found_3.r0 cell16_found_3.r2 : ℚ) = 0 ∧ (dot cell16_found_3.r1 cell16_found_3.r2 : ℚ) = 0 :=
  (Cert.sound cell16_found_3 cell16_found_3_checks).2.1

/-- cell16_found_3: the outline of the object's shadow is the outline of the listed corners,
and its corners are exactly the listed ones. -/
theorem cell16_found_3_casts :
    convexHull ℚ cell16_found_3.shadow = convexHull ℚ cell16_found_3.cornerSet ∧
    (convexHull ℚ cell16_found_3.shadow).extremePoints ℚ = cell16_found_3.cornerSet :=
  (Cert.sound cell16_found_3 cell16_found_3_checks).2.2

def cell24_found_1 : Cert where
  D := 494
  obj := [[-1, -1, 0, 0], [-1, 0, -1, 0], [-1, 0, 0, -1], [-1, 0, 0, 1], [-1, 0, 1, 0], [-1, 1, 0, 0], [0, -1, -1, 0], [0, -1, 0, -1], [0, -1, 0, 1], [0, -1, 1, 0], [0, 0, -1, -1], [0, 0, -1, 1], [0, 0, 1, -1], [0, 0, 1, 1], [0, 1, -1, 0], [0, 1, 0, -1], [0, 1, 0, 1], [0, 1, 1, 0], [1, -1, 0, 0], [1, 0, -1, 0], [1, 0, 0, -1], [1, 0, 0, 1], [1, 0, 1, 0], [1, 1, 0, 0]]
  r0 := [461, 95, 137, -61]
  r1 := [-137, 95, 449, 121]
  r2 := [61, -475, 121, -7]
  t := ⟨-1976, 988, -494⟩
  corners := [⟨-2574, 676, -676⟩, ⟨-2532, 1030, -80⟩, ⟨-2498, 1246, -562⟩, ⟨-2342, 1220, -1030⟩, ⟨-2300, 1574, -434⟩, ⟨-2208, 444, -140⟩, ⟨-2052, 418, -608⟩, ⟨-2018, 634, -1090⟩, ⟨-2010, 772, -12⟩, ⟨-1942, 1204, -976⟩, ⟨-1934, 1342, 102⟩, ⟨-1900, 1558, -380⟩, ⟨-1744, 1532, -848⟩, ⟨-1652, 402, -554⟩, ⟨-1610, 756, 42⟩, ⟨-1454, 730, -426⟩, ⟨-1420, 946, -908⟩, ⟨-1378, 1300, -312⟩]
  idx := [1, 0, 3, 5, 4, 6, 10, 14, 7, 16, 9, 13, 17, 19, 18, 20, 23, 22]
  wit := [⟨-1380, -720, -420⟩, ⟨-1160, 92, 972⟩, ⟨-766, 202, -66⟩, ⟨-588, 394, -980⟩, ⟨-526, 1112, 164⟩, ⟨-418, -1102, 684⟩, ⟨-240, -910, -230⟩, ⟨-36, -716, -1336⟩, ⟨-178, -192, 914⟩, ⟨178, 192, -914⟩, ⟨36, 716, 1336⟩, ⟨240, 910, 230⟩, ⟨418, 1102, -684⟩, ⟨526, -1112, -164⟩, ⟨588, -394, 980⟩, ⟨766, -202, 66⟩, ⟨1160, -92, -972⟩, ⟨1380, 720, 420⟩]
  wts := [[(1, 1)], [(0, 1)], [(0, 13), (4, 3), (10, 1), (11, 4)], [(2, 1)], [(4, 1)], [(3, 1)], [(5, 1)], [(8, 1)], [(0, 1), (1, 4), (8, 7), (10, 6)], [(10, 1)], [(6, 1)], [(0, 13), (13, 3), (15, 4), (16, 1)], [(0, 5), (10, 2), (11, 14), (17, 15)], [(11, 1)], [(7, 1)], [(0, 1), (7, 4), (9, 7), (16, 6)], [(9, 1)], [(12, 1)], [(14, 1)], [(13, 1)], [(15, 1)], [(0, 5), (15, 14), (16, 2), (17, 15)], [(17, 1)], [(16, 1)]]

theorem cell24_found_1_checks : cell24_found_1.check = true := by decide +kernel

/-- cell24_found_1: the tilt is exact (rows of length one at right angles, after dividing by D). -/
theorem cell24_found_1_tilt_exact :
    (dot cell24_found_1.r0 cell24_found_1.r0 : ℚ) / (cell24_found_1.D * cell24_found_1.D) = 1 ∧ (dot cell24_found_1.r1 cell24_found_1.r1 : ℚ) / (cell24_found_1.D * cell24_found_1.D) = 1 ∧
    (dot cell24_found_1.r2 cell24_found_1.r2 : ℚ) / (cell24_found_1.D * cell24_found_1.D) = 1 ∧
    (dot cell24_found_1.r0 cell24_found_1.r1 : ℚ) = 0 ∧ (dot cell24_found_1.r0 cell24_found_1.r2 : ℚ) = 0 ∧ (dot cell24_found_1.r1 cell24_found_1.r2 : ℚ) = 0 :=
  (Cert.sound cell24_found_1 cell24_found_1_checks).2.1

/-- cell24_found_1: the outline of the object's shadow is the outline of the listed corners,
and its corners are exactly the listed ones. -/
theorem cell24_found_1_casts :
    convexHull ℚ cell24_found_1.shadow = convexHull ℚ cell24_found_1.cornerSet ∧
    (convexHull ℚ cell24_found_1.shadow).extremePoints ℚ = cell24_found_1.cornerSet :=
  (Cert.sound cell24_found_1 cell24_found_1_checks).2.2

def cell24_found_2 : Cert where
  D := 5246
  obj := [[-1, -1, 0, 0], [-1, 0, -1, 0], [-1, 0, 0, -1], [-1, 0, 0, 1], [-1, 0, 1, 0], [-1, 1, 0, 0], [0, -1, -1, 0], [0, -1, 0, -1], [0, -1, 0, 1], [0, -1, 1, 0], [0, 0, -1, -1], [0, 0, -1, 1], [0, 0, 1, -1], [0, 0, 1, 1], [0, 1, -1, 0], [0, 1, 0, -1], [0, 1, 0, 1], [0, 1, 1, 0], [1, -1, 0, 0], [1, 0, -1, 0], [1, 0, 0, -1], [1, 0, 0, 1], [1, 0, 1, 0], [1, 1, 0, 0]]
  r0 := [1655, 4297, 2389, -781]
  r1 := [-2521, 2891, -3563, -335]
  r2 := [-1459, -799, 845, -4903]
  t := ⟨10492, 5246, 0⟩
  corners := [⟨3806, 5918, -46⟩, ⟨4540, 4876, 2258⟩, ⟨5414, 2020, -4104⟩, ⟨6448, 11330, 614⟩, ⟨6976, 2690, 5702⟩, ⟨7322, 8474, -5748⟩, ⟨7850, -166, -660⟩, ⟨8584, -1208, 1644⟩, ⟨9618, 8102, 6362⟩, ⟨11366, 2390, -6362⟩, ⟨12400, 11700, -1644⟩, ⟨13134, 10658, 660⟩, ⟨13662, 2018, 5748⟩, ⟨14008, 7802, -5702⟩, ⟨14536, -838, -614⟩, ⟨15570, 8472, 4104⟩, ⟨16444, 5616, -2258⟩, ⟨17178, 4574, 46⟩]
  idx := [6, 0, 8, 1, 7, 11, 18, 9, 2, 21, 14, 5, 12, 16, 22, 15, 23, 17]
  wit := [⟨-8722, 2040, -2114⟩, ⟨-11404, -542, 5806⟩, ⟨-9706, -5846, -6000⟩, ⟨-7728, 12268, 2828⟩, ⟨-2682, -2582, 7920⟩, ⟨-8036, 8044, -14112⟩, ⟨-984, -7886, -3886⟩, ⟨-3666, -10468, 4034⟩, ⟨-2976, 8496, 14736⟩, ⟨2976, -8496, -14736⟩, ⟨3666, 10468, -4034⟩, ⟨984, 7886, 3886⟩, ⟨8036, -8044, 14112⟩, ⟨2682, 2582, -7920⟩, ⟨7728, -12268, -2828⟩, ⟨9706, 5846, 6000⟩, ⟨11404, 542, -5806⟩, ⟨8722, -2040, 2114⟩]
  wts := [[(1, 1)], [(3, 1)], [(8, 1)], [(0, 1522), (5, 1238), (10, 139), (13, 1138)], [(0, 1380), (12, 1522), (15, 139), (17, 996)], [(11, 1)], [(0, 1)], [(4, 1)], [(2, 1)], [(7, 1)], [(0, 139), (3, 1138), (8, 2515), (11, 384)], [(5, 1)], [(12, 1)], [(0, 139), (6, 106), (9, 2515), (14, 1416)], [(10, 1)], [(15, 1)], [(13, 1)], [(17, 1)], [(6, 1)], [(0, 2515), (9, 139), (13, 1522), (16, 1238)], [(0, 1277), (12, 5030), (14, 278), (17, 1767)], [(9, 1)], [(14, 1)], [(16, 1)]]

theorem cell24_found_2_checks : cell24_found_2.check = true := by decide +kernel

/-- cell24_found_2: the tilt is exact (rows of length one at right angles, after dividing by D). -/
theorem cell24_found_2_tilt_exact :
    (dot cell24_found_2.r0 cell24_found_2.r0 : ℚ) / (cell24_found_2.D * cell24_found_2.D) = 1 ∧ (dot cell24_found_2.r1 cell24_found_2.r1 : ℚ) / (cell24_found_2.D * cell24_found_2.D) = 1 ∧
    (dot cell24_found_2.r2 cell24_found_2.r2 : ℚ) / (cell24_found_2.D * cell24_found_2.D) = 1 ∧
    (dot cell24_found_2.r0 cell24_found_2.r1 : ℚ) = 0 ∧ (dot cell24_found_2.r0 cell24_found_2.r2 : ℚ) = 0 ∧ (dot cell24_found_2.r1 cell24_found_2.r2 : ℚ) = 0 :=
  (Cert.sound cell24_found_2 cell24_found_2_checks).2.1

/-- cell24_found_2: the outline of the object's shadow is the outline of the listed corners,
and its corners are exactly the listed ones. -/
theorem cell24_found_2_casts :
    convexHull ℚ cell24_found_2.shadow = convexHull ℚ cell24_found_2.cornerSet ∧
    (convexHull ℚ cell24_found_2.shadow).extremePoints ℚ = cell24_found_2.cornerSet :=
  (Cert.sound cell24_found_2 cell24_found_2_checks).2.2

def cell24_found_3 : Cert where
  D := 290
  obj := [[-1, -1, 0, 0], [-1, 0, -1, 0], [-1, 0, 0, -1], [-1, 0, 0, 1], [-1, 0, 1, 0], [-1, 1, 0, 0], [0, -1, -1, 0], [0, -1, 0, -1], [0, -1, 0, 1], [0, -1, 1, 0], [0, 0, -1, -1], [0, 0, -1, 1], [0, 0, 1, -1], [0, 0, 1, 1], [0, 1, -1, 0], [0, 1, 0, -1], [0, 1, 0, 1], [0, 1, 1, 0], [1, -1, 0, 0], [1, 0, -1, 0], [1, 0, 0, -1], [1, 0, 0, 1], [1, 0, 1, 0], [1, 1, 0, 0]]
  r0 := [47, 211, 187, 49]
  r1 := [-221, 137, -71, -107]
  r2 := [181, 103, -119, -163]
  t := ⟨-870, 580, 1160⟩
  corners := [⟨-1268, 514, 1176⟩, ⟨-1128, 664, 876⟩, ⟨-1106, 758, 1442⟩, ⟨-1104, 872, 1098⟩, ⟨-1034, 222, 1238⟩, ⟨-1032, 336, 894⟩, ⟨-1010, 430, 1460⟩, ⟨-966, 908, 1142⟩, ⟨-872, 466, 1504⟩, ⟨-868, 694, 816⟩, ⟨-774, 252, 1178⟩, ⟨-730, 730, 860⟩, ⟨-708, 824, 1426⟩, ⟨-706, 938, 1082⟩, ⟨-636, 288, 1222⟩, ⟨-634, 402, 878⟩, ⟨-612, 496, 1444⟩, ⟨-472, 646, 1144⟩]
  idx := [6, 0, 10, 1, 18, 8, 19, 2, 20, 3, 21, 4, 15, 5, 22, 13, 23, 17]
  wit := [⟨-830, -216, 104⟩, ⟨-246, 36, -352⟩, ⟨-440, 388, 588⟩, ⟨-318, 508, -196⟩, ⟨-248, -652, 204⟩, ⟨-324, -616, -668⟩, ⟨-320, -180, 360⟩, ⟨-72, 472, 156⟩, ⟨76, -276, 752⟩, ⟨-76, 276, -752⟩, ⟨72, -472, -156⟩, ⟨320, 180, -360⟩, ⟨324, 616, 668⟩, ⟨248, 652, -204⟩, ⟨318, -508, 196⟩, ⟨440, -388, -588⟩, ⟨246, -36, 352⟩, ⟨830, 216, -104⟩]
  wts := [[(1, 1)], [(3, 1)], [(7, 1)], [(9, 1)], [(11, 1)], [(13, 1)], [(0, 1)], [(0, 365), (12, 48), (16, 34), (17, 19)], [(5, 1)], [(0, 24), (5, 108), (10, 17), (15, 84)], [(2, 1)], [(0, 293), (11, 34), (15, 48), (17, 91)], [(0, 66), (12, 24), (16, 17), (17, 126)], [(15, 1)], [(0, 24), (2, 36), (7, 17), (12, 156)], [(12, 1)], [(0, 30), (11, 17), (15, 24), (17, 162)], [(17, 1)], [(4, 1)], [(6, 1)], [(8, 1)], [(10, 1)], [(14, 1)], [(16, 1)]]

theorem cell24_found_3_checks : cell24_found_3.check = true := by decide +kernel

/-- cell24_found_3: the tilt is exact (rows of length one at right angles, after dividing by D). -/
theorem cell24_found_3_tilt_exact :
    (dot cell24_found_3.r0 cell24_found_3.r0 : ℚ) / (cell24_found_3.D * cell24_found_3.D) = 1 ∧ (dot cell24_found_3.r1 cell24_found_3.r1 : ℚ) / (cell24_found_3.D * cell24_found_3.D) = 1 ∧
    (dot cell24_found_3.r2 cell24_found_3.r2 : ℚ) / (cell24_found_3.D * cell24_found_3.D) = 1 ∧
    (dot cell24_found_3.r0 cell24_found_3.r1 : ℚ) = 0 ∧ (dot cell24_found_3.r0 cell24_found_3.r2 : ℚ) = 0 ∧ (dot cell24_found_3.r1 cell24_found_3.r2 : ℚ) = 0 :=
  (Cert.sound cell24_found_3 cell24_found_3_checks).2.1

/-- cell24_found_3: the outline of the object's shadow is the outline of the listed corners,
and its corners are exactly the listed ones. -/
theorem cell24_found_3_casts :
    convexHull ℚ cell24_found_3.shadow = convexHull ℚ cell24_found_3.cornerSet ∧
    (convexHull ℚ cell24_found_3.shadow).extremePoints ℚ = cell24_found_3.cornerSet :=
  (Cert.sound cell24_found_3 cell24_found_3_checks).2.2

end Shadow.Examples
