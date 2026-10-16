"""The compiler: turns by any amount, built from whole-number reflections.

Given a turn size `psi` (radians) between two arrows of a four-arrow cell, and an accuracy
target, this finds whole-number directions whose squared length is a power of 2, pairs each
turn with its mirror image (so the unavoidable tilt cancels), and reports how many floors
the turn costs and how far it is from the exact turn.

Everything that defines the turn is exact integers. Lean (CompileMachine.lean) checks that
any such reflection keeps every cell's total exactly; this program only searches and
measures. Accuracy is measured with 60-digit arithmetic.

Arrows are ordered: left spin-up, left spin-down, right spin-up, right spin-down.
The mass turn mixes left with right for both spins: planes (0, 2) and (1, 3).

Usage:  python3 compile.py            (prints a table)
"""
import math
from mpmath import mp, mpf, mpc, matrix, cos, sin, sqrt as msqrt
from sympy.solvers.diophantine.diophantine import sum_of_three_squares

mp.dps = 60


def legendre_ok(R):
    """R is a sum of three squares (Legendre's three-square theorem)."""
    if R == 0:
        return True
    while R % 4 == 0:
        R //= 4
    return R % 8 != 7


def find_direction(half, j, plane, spare, window=400, depth=6):
    """Whole-number direction of squared length 2^j, at angle `half` from arrow plane[0]
    toward arrow plane[1] (with a quarter turn), plus a small tilt into arrow `spare`.
    Returns the four Gaussian integers as (re, im) pairs and the squared tilt."""
    N = 2 ** j
    r = math.isqrt(N)
    A = round(math.sqrt(N) * math.cos(half))
    best = None
    for a in range(max(1, A - window), min(r, A + window) + 1):
        bmax = math.isqrt(N - a * a)
        for b in range(max(0, bmax - depth), bmax + 1):
            R = N - a * a - b * b
            if R <= 0 or not legendre_ok(R):
                continue
            ang = math.atan2(b, a)
            score = max(abs(ang - half) / max(half, 1e-300), math.sqrt(R / N) / max(math.sin(half), 1e-300))
            if best is None or score < best[0]:
                best = (score, a, b, R)
    _, a, b, R = best
    x, y, z = sum_of_three_squares(R)
    v = [(0, 0)] * 4
    v[plane[0]] = (a, 0)
    v[plane[1]] = (x, -b)          # -i * (b + i x)  =  x - i b
    v[spare] = (y, z)
    assert sum(p * p + q * q for p, q in v) == N
    return v, R


def mirror(v, spare):
    w = list(v)
    w[spare] = (-v[spare][0], -v[spare][1])
    return w


def to_m(v):
    return matrix([[mpc(p, q)] for p, q in v])


def reflection(v):
    u = to_m(v)
    n = sum(abs(u[k]) ** 2 for k in range(4))
    I = matrix(4, 4)
    for k in range(4):
        I[k, k] = 1
    return I - 2 * (u * u.H) / n


def unit(k):
    e = [(0, 0)] * 4
    e[k] = (1, 0)
    return e


def mass_turn(psi, j):
    """Compiled turn by `psi` mixing left with right (both spins): a turn by psi/2 followed
    by its mirror image. Returns the directions used (exact integers) and the 4x4 matrix."""
    half = psi / 4                      # each of the two turns is psi/2; each reflection pair doubles
    v1, R1 = find_direction(half, j, (0, 2), 1)
    v2, R2 = find_direction(half, j, (1, 3), 0)
    w1, w2 = mirror(v1, 1), mirror(v2, 0)
    seq = [unit(1), v2, unit(0), v1, unit(1), w2, unit(0), w1]
    U = matrix(4, 4)
    for k in range(4):
        U[k, k] = 1
    for v in seq:
        U = reflection(v) * U
    return (v1, v2, w1, w2), U, max(R1, R2)


def exact_turn(psi):
    c, s = cos(psi), sin(psi)
    T = matrix(4, 4)
    for k in range(4):
        T[k, k] = c
    for p, q in [(0, 2), (1, 3)]:
        T[p, q] = -1j * s
        T[q, p] = -1j * s
    return T


def distance(U, T):
    """Distance from U to T, ignoring an overall phase (Frobenius, normalized)."""
    tr = sum((T.H * U)[k, k] for k in range(4))
    ph = tr / abs(tr)
    D = U - ph * T
    return msqrt(sum(abs(D[a, b]) ** 2 for a in range(4) for b in range(4)) / 4)


def compile_turn(psi, accuracy, jmax=160):
    """Smallest j (in steps of 4) whose compiled turn is within `accuracy` of the exact turn,
    relative to the turn's size. Returns (j, floors, relative error, directions)."""
    T = exact_turn(mpf(psi))
    for j in range(8, jmax + 1, 4):
        dirs, U, R = mass_turn(psi, j)
        err = float(distance(U, T)) / psi
        if err <= accuracy:
            return j, 4 * 2 * j, err, dirs
    return None


def to_lean(psi, accuracy):
    """A Lean file that defines the compiled turn in exact whole numbers and has Lean check
    that it keeps every cell's total exactly (check with: lake env lean <file>)."""
    j, floors, err, (v1, v2, w1, w2) = compile_turn(psi, accuracy)
    q = lambda v: "⟨" + ", ".join(f"⟨{a}, {b}⟩" for a, b in v) + "⟩"
    n = f"2 ^ {j}"
    out = [f"-- compiled mass turn {psi}, relative error {err:.1e}, {floors} floors",
           "import CompileMachine", "namespace Building", "open Quad"]
    for nm, v in [("c1", v1), ("c2", v2), ("d1", w1), ("d2", w2)]:
        out.append(f"def {nm} : Quad := {q(v)}")
        out.append(f"theorem {nm}_size : {nm}.size = {n} := by decide +kernel")
    out += [f"def turnC (q : Quad) : Quad := reflect d1 ({n}) (reflect e0 1 (reflect d2 ({n}) "
            f"(reflect e1 1 (reflect c1 ({n}) (reflect e0 1 (reflect c2 ({n}) (reflect e1 1 q)))))))",
            f"theorem turnC_size (q : Quad) : (turnC q).size = 2 ^ {8 * j} * q.size := by",
            "  simp only [turnC]",
            "  rw [reflect_size _ _ _ d1_size, reflect_size _ _ _ e0_size, reflect_size _ _ _ d2_size,",
            "    reflect_size _ _ _ e1_size, reflect_size _ _ _ c1_size, reflect_size _ _ _ e0_size,",
            "    reflect_size _ _ _ c2_size, reflect_size _ _ _ e1_size]",
            "  generalize q.size = s", "  grind", "end Building"]
    return "\n".join(out) + "\n"


if __name__ == "__main__":
    import sys
    if len(sys.argv) == 4 and sys.argv[1] == "--lean":     # python3 compile.py --lean 0.001 1e-7
        print(to_lean(float(sys.argv[2]), float(sys.argv[3])), end="")
        sys.exit()
    print("compiled mass turns (four costly reflections of squared length 2^j each = 8j floors)")
    for psi in [1e-1, 1e-2, 1e-3]:
        for acc in [1e-3, 1e-5, 1e-7]:
            res = compile_turn(psi, acc)
            if res is None:
                print(f"  turn {psi:g}, accuracy {acc:g}: not reached by j = 160")
            else:
                j, floors, err, _ = res
                print(f"  turn {psi:g}, accuracy {acc:g}: j = {j:3d}, {floors:4d} floors, relative error {err:.1e}")
