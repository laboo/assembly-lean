#!/usr/bin/env python3
"""
Shadow workbench: pure geometry, exact arithmetic.

- Build corner shapes in any number of dimensions with whole-number coordinates.
- Tilt them exactly (rational turns, so no rounding ever happens).
- Flatten them into 3D (the outline shadow) and describe the shadow:
  corners, edges, faces, face shapes, symmetry through the center, size.
- Check whether an object can cast a given 3D shadow:
  first the quick restrictions, then a search that matches corners to corners
  and returns an exact tilt when it finds one.

Everything is integers and fractions. No floating point anywhere.
This version handles solid shapes without dents (the shadow is then the
outline of the flattened corners).
"""
from fractions import Fraction as F
from itertools import product, combinations
from math import gcd, isqrt
from collections import Counter
import random


# ---------------------------------------------------------------- objects

def cube(n):
    """The n-dimensional cube with corners at every (+-1, ..., +-1)."""
    return [tuple(c) for c in product((-1, 1), repeat=n)]


def cross(n):
    """The n-dimensional cross shape (the 16-cell when n = 4): corners +-e_i."""
    pts = []
    for i in range(n):
        for s in (1, -1):
            v = [0] * n
            v[i] = s
            pts.append(tuple(v))
    return pts


def simplex(n):
    """The simplest n-dimensional solid: the origin and the n unit corners."""
    pts = [tuple([0] * n)]
    for i in range(n):
        v = [0] * n
        v[i] = 1
        pts.append(tuple(v))
    return pts


def cell24():
    """The 24-cell: every arrangement of (+-1, +-1, 0, 0)."""
    pts = set()
    for i, j in combinations(range(4), 2):
        for si in (1, -1):
            for sj in (1, -1):
                v = [0] * 4
                v[i], v[j] = si, sj
                pts.add(tuple(v))
    return sorted(pts)


# ---------------------------------------------------------------- exact linear algebra

def mat_mul(A, B):
    return [[sum(a * b for a, b in zip(row, col)) for col in zip(*B)] for row in A]


def transpose(A):
    return [list(r) for r in zip(*A)]


def identity(n):
    return [[F(int(i == j)) for j in range(n)] for i in range(n)]


def mat_inv(M):
    n = len(M)
    A = [[F(x) for x in row] + [F(int(i == j)) for j in range(n)] for i, row in enumerate(M)]
    for c in range(n):
        p = next((r for r in range(c, n) if A[r][c] != 0), None)
        if p is None:
            return None
        A[c], A[p] = A[p], A[c]
        pv = A[c][c]
        A[c] = [x / pv for x in A[c]]
        for r in range(n):
            if r != c and A[r][c] != 0:
                f = A[r][c]
                A[r] = [a - f * b for a, b in zip(A[r], A[c])]
    return [row[n:] for row in A]


def rank(rows):
    A = [[F(x) for x in r] for r in rows]
    if not A:
        return 0
    m, n = len(A), len(A[0])
    rk, col = 0, 0
    while rk < m and col < n:
        p = next((r for r in range(rk, m) if A[r][col] != 0), None)
        if p is None:
            col += 1
            continue
        A[rk], A[p] = A[p], A[rk]
        for r in range(rk + 1, m):
            if A[r][col] != 0:
                f = A[r][col] / A[rk][col]
                A[r] = [a - f * b for a, b in zip(A[r], A[rk])]
        rk += 1
        col += 1
    return rk


def affine_rank(pts):
    if len(pts) <= 1:
        return 0
    p0 = pts[0]
    return rank([[a - b for a, b in zip(p, p0)] for p in pts[1:]])


# ---------------------------------------------------------------- exact tilts

def turn(A):
    """An exact turn of n-space from any skew table A: (I - A)(I + A)^-1.
    Its entries are fractions, and it keeps every length exactly."""
    n = len(A)
    I = identity(n)
    IminusA = [[I[i][j] - A[i][j] for j in range(n)] for i in range(n)]
    IplusA = [[I[i][j] + A[i][j] for j in range(n)] for i in range(n)]
    return mat_mul(IminusA, mat_inv(IplusA))


def random_turn(n, rng):
    A = [[F(0)] * n for _ in range(n)]
    for i in range(n):
        for j in range(i + 1, n):
            x = F(rng.randint(-3, 3), rng.randint(1, 3))
            A[i][j], A[j][i] = x, -x
    return turn(A)


def is_projection(P):
    """True if the rows of P have length one and are at right angles: a true shadow map."""
    return mat_mul(P, transpose(P)) == identity(len(P))


def shadow_map(Q):
    """Keep the first three directions after the turn."""
    return [list(r) for r in Q[:3]]


def apply(P, V, t=None):
    out = []
    for v in V:
        w = [sum(F(a) * b for a, b in zip(row, v)) for row in P]
        if t is not None:
            w = [a + b for a, b in zip(w, t)]
        out.append(tuple(w))
    return out


# ---------------------------------------------------------------- the shadow's outline

def _lcm(a, b):
    return a * b // gcd(a, b)


def _to_ints(pts):
    L = 1
    for p in pts:
        for x in p:
            L = _lcm(L, F(x).denominator)
    return [tuple(int(F(x) * L) for x in p) for p in pts], L


def _sub(a, b):
    return tuple(x - y for x, y in zip(a, b))


def _dot(a, b):
    return sum(x * y for x, y in zip(a, b))


def _crs(a, b):
    return (a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0])


def _hull2(pts):
    """Corners of a flat convex polygon (integer 2D points), in order."""
    pts = sorted(set(pts))
    if len(pts) <= 2:
        return pts

    def cr(o, a, b):
        return (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0])

    lower, upper = [], []
    for p in pts:
        while len(lower) >= 2 and cr(lower[-2], lower[-1], p) <= 0:
            lower.pop()
        lower.append(p)
    for p in reversed(pts):
        while len(upper) >= 2 and cr(upper[-2], upper[-1], p) <= 0:
            upper.pop()
        upper.append(p)
    return lower[:-1] + upper[:-1]


def _symmetric(points):
    """True if a set of points is symmetric through its own center (exact)."""
    pts = list(points)
    n = len(pts)
    if n <= 2:
        return True
    d = len(pts[0])
    s = [sum(p[i] for p in pts) for i in range(d)]
    scaled = {tuple(n * x for x in p) for p in pts}
    return all(tuple(2 * s[i] - n * p[i] for i in range(d)) in scaled for p in pts)


def object_faces(V):
    """Every face of a solid n-dimensional corner shape, as sets of corner indices (exact).
    Facets come from flat walls through n corners with every corner on one side;
    every other face is a meeting of facets."""
    pts = sorted(set(V))
    n = len(pts[0])
    facets = set()
    for combo in combinations(range(len(pts)), n):
        rows = [_sub(pts[c], pts[combo[0]]) for c in combo[1:]]
        if rank(rows) < n - 1:
            continue
        u = _nullvec(rows, n)
        L = 1
        for x in u:
            L = _lcm(L, x.denominator)
        u = [int(x * L) for x in u]
        d = _dot(u, pts[combo[0]])
        side = [_dot(u, p) - d for p in pts]
        if all(s <= 0 for s in side) or all(s >= 0 for s in side):
            facets.add(frozenset(i for i, s in enumerate(side) if s == 0))
    faces = set(facets)
    frontier = set(facets)
    while frontier:
        new = set()
        for a in frontier:
            for b in facets:
                c = a & b
                if c and c not in faces:
                    new.add(c)
        faces |= new
        frontier = new
    return pts, faces


def all_faces_symmetric(V):
    pts, faces = object_faces(V)
    return _symmetric(pts) and all(_symmetric([pts[i] for i in f]) for f in faces)


def outline(points3):
    """Describe the 3D outline shadow of a set of 3D points (exact).
    Returns corners (as fractions), counts of corners, edges and faces, face shapes,
    symmetry through the center, and size (largest squared distance)."""
    ipts, L = _to_ints(points3)
    pts = sorted(set(ipts))
    dim = affine_rank(pts)
    res = {"dimension": dim}
    if dim == 3:
        facets = {}
        for a, b, c in combinations(range(len(pts)), 3):
            nrm = _crs(_sub(pts[b], pts[a]), _sub(pts[c], pts[a]))
            if nrm == (0, 0, 0):
                continue
            d = _dot(nrm, pts[a])
            side = [_dot(nrm, p) - d for p in pts]
            if all(s <= 0 for s in side):
                pass
            elif all(s >= 0 for s in side):
                nrm, d = tuple(-x for x in nrm), -d
            else:
                continue
            g = 0
            for x in (*nrm, d):
                g = gcd(g, abs(x))
            key = (tuple(x // g for x in nrm), d // g)
            if key not in facets:
                facets[key] = frozenset(i for i, p in enumerate(pts) if _dot(key[0], p) == key[1])
        corners = []
        for i in range(len(pts)):
            normals = [k[0] for k, on in facets.items() if i in on]
            if rank(normals) == 3:
                corners.append(i)
        cs = set(corners)
        face_sizes = [len(on & cs) for on in facets.values()]
        V, Fc = len(corners), len(facets)
        E = sum(face_sizes) // 2
        assert V - E + Fc == 2, "Euler check failed"
        corner_pts = [pts[i] for i in corners]
        res.update(corners=V, edges=E, faces=Fc, face_shapes=dict(sorted(Counter(face_sizes).items())))
        res["faces_symmetric"] = all(_symmetric([pts[i] for i in on & cs]) for on in facets.values())
        res["_facets"] = [(k[0], sorted(on & cs)) for k, on in facets.items()]
        res["_pts"] = pts
        res["_corner_idx"] = corners
    elif dim == 2:
        # flat shadow: drop a coordinate that keeps the plane one-to-one
        p0 = pts[0]
        rows = [_sub(p, p0) for p in pts[1:]]
        u = next(r for r in rows if r != (0, 0, 0))
        w = next(r for r in rows if _crs(u, r) != (0, 0, 0))
        nrm = _crs(u, w)
        k = next(i for i in range(3) if nrm[i] != 0)
        keep = [i for i in range(3) if i != k]
        flat = {(p[keep[0]], p[keep[1]]): p for p in pts}
        corner_pts = [flat[q] for q in _hull2(list(flat))]
        res.update(corners=len(corner_pts), edges=len(corner_pts), faces=1,
                   face_shapes={len(corner_pts): 1})
        res["faces_symmetric"] = _symmetric(corner_pts)
    else:
        corner_pts = [min(pts), max(pts)] if dim == 1 else pts[:1]
        res.update(corners=len(corner_pts), edges=dim, faces=0, face_shapes={})
        res["faces_symmetric"] = True
    # symmetry through the center
    n = len(corner_pts)
    s = tuple(sum(p[i] for p in corner_pts) for i in range(3))
    scaled = {tuple(n * x for x in p) for p in corner_pts}
    res["symmetric"] = all(tuple(2 * s[i] - n * p[i] for i in range(3)) in scaled for p in corner_pts)
    res["size"] = max((F(_dot(_sub(a, b), _sub(a, b)), L * L)
                       for a, b in combinations(corner_pts, 2)), default=F(0))
    res["corner_points"] = sorted(tuple(F(x, L) for x in p) for p in corner_pts)
    return res


def object_facts(V):
    pts = sorted(set(V))
    n = len(pts)
    s = [sum(p[i] for p in pts) for i in range(len(pts[0]))]
    scaled = {tuple(n * x for x in p) for p in pts}
    sym = all(tuple(2 * s[i] - n * p[i] for i in range(len(p))) in scaled for p in pts)
    size = max(_dot(_sub(a, b), _sub(a, b)) for a, b in combinations(pts, 2))
    return {"corners": n, "dimension": affine_rank(pts), "symmetric": sym, "size": F(size)}


def describe_shape(r):
    shapes = {3: "triangles", 4: "four-sided", 5: "five-sided", 6: "six-sided", 8: "eight-sided"}
    fs = ", ".join(f"{c} {shapes.get(k, str(k) + '-sided')}" for k, c in r["face_shapes"].items())
    sym = "symmetric through center" if r["symmetric"] else "NOT symmetric"
    return f"{r['corners']} corners, {r['edges']} edges, {r['faces']} faces ({fs}); {sym}"


def describe(r):
    return f"{describe_shape(r)}; size {r['size']}"


# ---------------------------------------------------------------- restrictions and search

def restrictions(obj, target):
    """Quick rule-outs, each a fact true of every shadow of every object."""
    why = []
    if target["corners"] > obj["corners"]:
        why.append(f"the shadow has {target['corners']} corners but the object has only {obj['corners']}")
    if target["dimension"] > obj["dimension"]:
        why.append("the shadow has more dimensions than the object")
    if obj["symmetric"] and not target["symmetric"]:
        why.append("the object is symmetric through its center but the shadow is not")
    if target["size"] > obj["size"]:
        why.append("the shadow is wider than the object")
    return why


def _rational_sqrt(x):
    x = F(x)
    if x < 0:
        return None
    a, b = x.numerator, x.denominator
    ra, rb = isqrt(a), isqrt(b)
    return F(ra, rb) if ra * ra == a and rb * rb == b else None


def _nullvec(rows, n):
    """One nonzero vector at right angles to every row (the rows have rank n - 1)."""
    A = [[F(x) for x in r] for r in rows]
    pivots, r = [], 0
    for c in range(n):
        p = next((i for i in range(r, len(A)) if A[i][c] != 0), None)
        if p is None:
            continue
        A[r], A[p] = A[p], A[r]
        pv = A[r][c]
        A[r] = [x / pv for x in A[r]]
        for i in range(len(A)):
            if i != r and A[i][c] != 0:
                f = A[i][c]
                A[i] = [a - f * b for a, b in zip(A[i], A[r])]
        pivots.append(c)
        r += 1
    free = [c for c in range(n) if c not in pivots]
    if not free:
        return None
    fc = free[0]
    u = [F(0)] * n
    u[fc] = F(1)
    for i, pc in enumerate(pivots):
        u[pc] = -A[i][fc]
    return u


def _solve_map(Vc, Sc, n):
    """Every exact shadow map P (with shift t) that sends object corners Vc[i] to shadow points Sc[i].
    If the chosen corners span all n directions the map is pinned outright. If they span all but one,
    the missing direction is recovered from the rule that a shadow map keeps right angles and lengths
    (two mirror-image choices); it is kept only if it stays exact."""
    D_all = [[F(a - b) for a, b in zip(Vc[i], Vc[0])] for i in range(1, len(Vc))]
    S_all = [[F(a) - F(b) for a, b in zip(Sc[i], Sc[0])] for i in range(1, len(Sc))]
    rk = rank(D_all)
    if rk == n:
        Dinv = mat_inv(transpose(D_all))
        cands = [mat_mul(transpose(S_all), Dinv)]
    elif rk == n - 1:
        basis, bS = [], []
        for d, s in zip(D_all, S_all):
            if rank(basis + [d]) > len(basis):
                basis.append(d)
                bS.append(s)
            if len(basis) == n - 1:
                break
        Ginv = mat_inv(mat_mul(basis, transpose(basis)))
        B = mat_mul(mat_mul(transpose(bS), Ginv), basis)      # the map on the seen directions
        u = _nullvec(basis, n)                                  # the one unseen direction
        uu = sum(x * x for x in u)
        BBt = mat_mul(B, transpose(B))
        R = [[uu * (F(int(i == j)) - BBt[i][j]) for j in range(3)] for i in range(3)]
        k = max(range(3), key=lambda i: R[i][i])
        if R[k][k] == 0:
            qs = [[F(0)] * 3]
        else:
            rt = _rational_sqrt(R[k][k])
            if rt is None:
                return []
            q = [R[i][k] / rt for i in range(3)]
            if any(q[i] * q[j] != R[i][j] for i in range(3) for j in range(3)):
                return []
            qs = [q, [-x for x in q]]
        cands = [[[B[i][j] + q[i] * u[j] / uu for j in range(n)] for i in range(3)] for q in qs]
    else:
        return []
    out = []
    for P in cands:
        if not is_projection(P):
            continue
        if any([sum(P[r][c] * d[c] for c in range(n)) for r in range(3)] != s for d, s in zip(D_all, S_all)):
            continue
        t = [F(Sc[0][r]) - sum(P[r][c] * F(Vc[0][c]) for c in range(n)) for r in range(3)]
        out.append((P, t))
    return out


class _OutOfBudget(Exception):
    pass


def find_tilt(V, target_points, max_subsets=40, seed=0, budget=300000):
    """Look for an exact shadow map P (rows of length one at right angles) and a shift t
    so that the outline of P*V + t has exactly the target's corners.
    Returns ("yes", P, t), ("ruled out", reasons), ("undetermined", why) or ("none found", note)."""
    n = len(V[0])
    obj = object_facts(V)
    tgt = outline(target_points)
    why = restrictions(obj, tgt)
    if not tgt["faces_symmetric"] and all_faces_symmetric(V):
        why.append("every face of the object is symmetric through its own center, but a face of the shadow "
                   "is not (every face of a shadow is the shadow of some face of the object)")
    if why:
        return ("ruled out", why)
    T = tgt["corner_points"]
    if len(T) < n + 1:
        return ("undetermined", f"the shadow has fewer than {n + 1} corners, so corners alone can't pin the tilt")
    Tset = set(T)
    m = len(V)
    dV = [[_dot(_sub(V[i], V[j]), _sub(V[i], V[j])) for j in range(m)] for i in range(m)]
    rng = random.Random(seed)
    subsets = list(combinations(range(len(T)), n + 1))
    rng.shuffle(subsets)
    nodes = [0]
    tried = 0
    for S in subsets[:max_subsets]:
        tried += 1
        Sp = [T[k] for k in S]
        dS = [[sum((a - b) ** 2 for a, b in zip(Sp[i], Sp[j])) for j in range(n + 1)] for i in range(n + 1)]
        chosen = []

        def go(k):
            nodes[0] += 1
            if nodes[0] > budget:
                raise _OutOfBudget
            if k == n + 1:
                for P, t in _solve_map([V[c] for c in chosen], Sp, n):
                    if set(outline(apply(P, V, t))["corner_points"]) == Tset:
                        return (P, t)
                return None
            for i in range(m):
                if i in chosen:
                    continue
                if all(dS[k][j] <= dV[i][chosen[j]] for j in range(k)):
                    chosen.append(i)
                    r = go(k + 1)
                    chosen.pop()
                    if r:
                        return r
            return None

        try:
            found = go(0)
        except _OutOfBudget:
            return ("none found", f"search budget used up after {tried} choices of shadow corners; "
                                  "this is not a proof of 'no'")
        if found:
            return ("yes", found[0], found[1])
    return ("none found", f"searched {tried} choices of {n + 1} shadow corners; this is not a proof of 'no'")


# ---------------------------------------------------------------- certificates for Lean

def certificate(V, P, t):
    """Turn a found tilt into a certificate Lean can check with whole numbers only.
    Everything is scaled by one common whole number D. Contents:
      r0, r1, r2, t : the three kept rows of the tilt and the shift, times D
      corners       : the shadow's corners, times D
      idx           : corners[k] is the shadow of object corner idx[k]
      wit           : wit[k] is a direction in which corners[k] sticks out further than every other shadow point
      wts           : for each object corner, positive weights on corners whose balance point is its shadow"""
    D = 1
    for row in P:
        for x in row:
            D = _lcm(D, F(x).denominator)
    for x in t:
        D = _lcm(D, F(x).denominator)
    rows = [[int(F(x) * D) for x in row] for row in P]
    tt = [int(F(x) * D) for x in t]
    imgs = [tuple(_dot(rows[r], v) + tt[r] for r in range(3)) for v in V]
    o = outline(imgs)                        # integer points, so no further scaling
    assert o["dimension"] == 3, "only solid 3D shadows are certified"
    pts, corner_idx, facets = o["_pts"], o["_corner_idx"], o["_facets"]
    corners = [pts[i] for i in corner_idx]
    idx = [imgs.index(cp) for cp in corners]
    wit = []
    for ci in corner_idx:
        w = [0, 0, 0]
        for nrm, on in facets:
            if ci in on:
                w = [a + b for a, b in zip(w, nrm)]
        wit.append(tuple(w))
    # check the witnesses really single out each corner
    for cp, w in zip(corners, wit):
        for x in imgs:
            assert x == cp or _dot(w, x) < _dot(w, cp)
    # weights: place each shadow point inside a small pyramid of corners
    a0 = 0
    tetras = []
    for nrm, on in facets:
        on_c = [corner_idx.index(i) for i in on]
        if a0 in on_c:
            continue
        for b, cc, d in combinations(on_c, 3):
            tetras.append((a0, b, cc, d))
    wts = []
    for x in imgs:
        if x in corners:
            wts.append([(corners.index(x), 1)])
            continue
        done = None
        for (i0, i1, i2, i3) in tetras:
            A = [[F(corners[j][r] - corners[i0][r]) for j in (i1, i2, i3)] for r in range(3)]
            inv = mat_inv(A)
            if inv is None:
                continue
            rhs = [F(x[r] - corners[i0][r]) for r in range(3)]
            lam = [sum(inv[r][k] * rhs[k] for k in range(3)) for r in range(3)]
            if all(l >= 0 for l in lam) and sum(lam) <= 1:
                bary = [(i0, 1 - sum(lam)), (i1, lam[0]), (i2, lam[1]), (i3, lam[2])]
                bary = [(k, w) for k, w in bary if w > 0]
                L = 1
                for _, w in bary:
                    L = _lcm(L, w.denominator)
                done = [(k, int(w * L)) for k, w in bary]
                break
        assert done is not None, "no pyramid of corners holds this point"
        W = sum(w for _, w in done)
        assert tuple(sum(w * corners[k][r] for k, w in done) for r in range(3)) == tuple(W * c for c in x)
        wts.append(done)
    return {"D": D, "obj": [list(v) for v in V], "r0": rows[0], "r1": rows[1], "r2": rows[2],
            "t": tt, "corners": corners, "idx": idx, "wit": wit, "wts": wts}


def lean_cert(name, c):
    def lst(xs):
        return "[" + ", ".join(str(x) for x in xs) + "]"

    def v3(p):
        return f"⟨{p[0]}, {p[1]}, {p[2]}⟩"

    return "\n".join([
        f"def {name} : Cert where",
        f"  D := {c['D']}",
        f"  obj := [{', '.join(lst(v) for v in c['obj'])}]",
        f"  r0 := {lst(c['r0'])}",
        f"  r1 := {lst(c['r1'])}",
        f"  r2 := {lst(c['r2'])}",
        f"  t := {v3(c['t'])}",
        f"  corners := [{', '.join(v3(p) for p in c['corners'])}]",
        f"  idx := {lst(c['idx'])}",
        f"  wit := [{', '.join(v3(p) for p in c['wit'])}]",
        f"  wts := [{', '.join('[' + ', '.join(f'({k}, {w})' for k, w in ws) + ']' for ws in c['wts'])}]",
        "",
        f"theorem {name}_checks : {name}.check = true := by decide +kernel",
        "",
        f"/-- {name}: the tilt is exact (rows of length one at right angles, after dividing by D). -/",
        f"theorem {name}_tilt_exact :",
        f"    (dot {name}.r0 {name}.r0 : ℚ) / ({name}.D * {name}.D) = 1 ∧ (dot {name}.r1 {name}.r1 : ℚ) / ({name}.D * {name}.D) = 1 ∧",
        f"    (dot {name}.r2 {name}.r2 : ℚ) / ({name}.D * {name}.D) = 1 ∧",
        f"    (dot {name}.r0 {name}.r1 : ℚ) = 0 ∧ (dot {name}.r0 {name}.r2 : ℚ) = 0 ∧ (dot {name}.r1 {name}.r2 : ℚ) = 0 :=",
        f"  (Cert.sound {name} {name}_checks).2.1",
        "",
        f"/-- {name}: the outline of the object's shadow is the outline of the listed corners,",
        f"and its corners are exactly the listed ones. -/",
        f"theorem {name}_casts :",
        f"    convexHull ℚ {name}.shadow = convexHull ℚ {name}.cornerSet ∧",
        f"    (convexHull ℚ {name}.shadow).extremePoints ℚ = {name}.cornerSet :=",
        f"  (Cert.sound {name} {name}_checks).2.2",
        "",
    ])


# ---------------------------------------------------------------- the examples

def run():
    rng = random.Random(2026)
    print("=" * 72)
    print("SHADOWS (outline, exact)")
    print("=" * 72)

    # 4D cube straight on: keep x, y, z, drop w
    straight = [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0]]
    print("4D cube, straight on:     ", describe(outline(apply(straight, cube(4)))))

    # 4D cube corner first: look along (1,1,1,1); an exact right-angled shadow map
    corner_first = [[F(1, 2), F(-1, 2), F(1, 2), F(-1, 2)],
                    [F(1, 2), F(1, 2), F(-1, 2), F(-1, 2)],
                    [F(1, 2), F(-1, 2), F(-1, 2), F(1, 2)]]
    assert is_projection(corner_first)
    print("4D cube, corner first:    ", describe(outline(apply(corner_first, cube(4)))))

    for k in range(5):
        P = shadow_map(random_turn(4, rng))
        assert is_projection(P)
        print(f"4D cube, random tilt {k + 1}:  ", describe(outline(apply(P, cube(4)))))

    P = shadow_map(random_turn(5, rng))
    print("5D cube, random tilt:     ", describe(outline(apply(P, cube(5)))))

    print("16-cell, straight on:     ", describe(outline(apply(straight, cross(4)))))
    P = shadow_map(random_turn(4, rng))
    print("16-cell, random tilt:     ", describe(outline(apply(P, cross(4)))))

    print("24-cell, straight on:     ", describe(outline(apply(straight, cell24()))))
    P = shadow_map(random_turn(4, rng))
    print("24-cell, random tilt:     ", describe(outline(apply(P, cell24()))))

    kinds = Counter()
    for k in range(40):
        P = shadow_map(random_turn(4, rng))
        r = outline(apply(P, simplex(4)))
        kinds[describe_shape(r)] += 1
    print("4D simplex, 40 random tilts, kinds of shadow seen:")
    for d, c in kinds.items():
        print(f"    {c:2d} x  {d}")

    print()
    print("=" * 72)
    print("CAN THIS OBJECT CAST THIS SHADOW?  (hidden-tilt round trips)")
    print("=" * 72)
    import time
    certs = []
    certs.append(("cube4_straight_on", certificate(cube(4), [[F(x) for x in r] for r in straight], [F(0)] * 3)))
    certs.append(("cube4_corner_first", certificate(cube(4), corner_first, [F(0)] * 3)))
    for name, V in [("4D cube", cube(4)), ("16-cell", cross(4)), ("24-cell", cell24())]:
        for trial in range(3):
            Q = random_turn(4, rng)
            P = shadow_map(Q)
            shift = [F(rng.randint(-5, 5)), F(rng.randint(-5, 5)), F(rng.randint(-5, 5))]
            target = apply(P, V, shift)
            t0 = time.time()
            res = find_tilt(V, target)
            dt = time.time() - t0
            if res[0] == "yes":
                P2, t2 = res[1], res[2]
                ok = is_projection(P2) and set(outline(apply(P2, V, t2))["corner_points"]) == set(outline(target)["corner_points"])
                print(f"{name}, trial {trial + 1}: hidden tilt -> search found an exact tilt: "
                      f"{'VERIFIED' if ok else 'FAILED CHECK'} ({dt:.1f}s)")
                tag = {"4D cube": "cube4", "16-cell": "cell16", "24-cell": "cell24"}[name]
                certs.append((f"{tag}_found_{trial + 1}", certificate(V, P2, t2)))
            else:
                print(f"{name}, trial {trial + 1}: {res[0]}: {res[1]} ({dt:.1f}s)")

    print()
    print("=" * 72)
    print("RULE-OUTS AND MISSES")
    print("=" * 72)
    pyramid = [(1, 1, 0), (1, -1, 0), (-1, 1, 0), (-1, -1, 0), (0, 0, 1)]
    print("square pyramid from 4D cube:     ", find_tilt(cube(4), pyramid)[:2])
    five_cube_shadow = apply(shadow_map(random_turn(5, rng)), cube(5))
    print("5D-cube shadow from 4D cube:     ", find_tilt(cube(4), five_cube_shadow)[:2])
    big_cube = [tuple(2 * x for x in c) for c in cube(3)]
    print("cube twice as wide from 4D cube: ", find_tilt(cube(4), big_cube)[:2])
    cubocta = apply(straight, cell24())
    print("24-cell's shadow from 4D cube:   ", find_tilt(cube(4), cubocta)[:2])

    header = ("import ShadowCert\n\n"
              "/-! Shadow certificates written by shadow_workbench.py. Each one: the tilt is exact, and\n"
              "the outline of the object's shadow has exactly the listed corners (see `Shadow.Cert.sound`). -/\n\n"
              "namespace Shadow.Examples\n\nopen Shadow Shadow.Cert\n\n")
    body = "\n".join(lean_cert(n, c) for n, c in certs)
    with open("ShadowExamples.lean", "w") as fh:
        fh.write(header + body + "\nend Shadow.Examples\n")
    print()
    print(f"wrote ShadowExamples.lean with {len(certs)} certificates")


# ---------------------------------------------------------------- odds: the share of an object that casts a shadow
#
# The odds of a shadow outcome are the share of the object's possibilities that cast it.
# Two kinds of possibility:
#   - the object's own points (a point is picked evenly from the object; where does its shadow land?)
#   - the tilt (the object is turned evenly at random; what kind of shadow does it cast?)
# Answers are exact when the shape allows, and otherwise sampled and labelled with their error.

import numpy as np
from math import comb as _choose


class Ball:
    """The ball of radius one in n dimensions: its surface (solid=False) or the whole solid."""

    def __init__(self, n, solid=False):
        self.n, self.solid, self.dim = n, solid, n

    def __repr__(self):
        return f"{'solid ' if self.solid else ''}ball in {self.n}D"

    def sample(self, k, rng):
        v = rng.normal(size=(k, self.n))
        v /= np.linalg.norm(v, axis=1, keepdims=True)
        if self.solid:
            v *= rng.random(k)[:, None] ** (1 / self.n)
        return v

    def shadow_power(self):
        """On any line, this ball's shadow has density proportional to (1 - x^2)^power."""
        return F(self.n - 1, 2) if self.solid else F(self.n - 3, 2)


class Points:
    """Finitely many equally likely points, for example an object's corners."""

    def __init__(self, pts):
        self.pts = [tuple(F(x) for x in p) for p in pts]
        self.dim = len(self.pts[0])

    def __repr__(self):
        return f"{len(self.pts)} points in {self.dim}D"

    def sample(self, k, rng):
        arr = np.array([[float(x) for x in p] for p in self.pts])
        return arr[rng.integers(len(self.pts), size=k)]


class Together:
    """One object made of several parts: a point of it is one point of each part, side by side."""

    def __init__(self, *parts):
        self.parts, self.dim = parts, sum(p.dim for p in parts)

    def __repr__(self):
        return " + ".join(repr(p) for p in self.parts) + " (one object)"

    def sample(self, k, rng):
        return np.hstack([p.sample(k, rng) for p in self.parts])


class Past:
    """A shadow outcome: the shadow on line number k lands at t or beyond."""

    def __init__(self, k, t):
        self.k, self.t = k, F(t)

    def __call__(self, s):
        return s[:, self.k] >= self.t


def _ball_share_past(power, c):
    """Share of a ball whose shadow on a unit line lands at c or beyond. Exact if power is a whole number."""
    if isinstance(c, F):
        c = max(F(-1), min(F(1), c))
    if isinstance(c, F) and power.denominator == 1 and power >= 0:
        p = int(power)

        def G(x):     # antiderivative of (1 - x^2)^p
            return sum(F(_choose(p, j) * (-1) ** j) * x ** (2 * j + 1) / (2 * j + 1) for j in range(p + 1))
        return (G(F(1)) - G(c)) / (G(F(1)) - G(F(-1))), "exact"
    # otherwise integrate sin^(2p+1) over the angle (smooth), to about twelve digits
    c = float(c)
    e = float(2 * power + 1)
    phi = np.arccos(np.clip(c, -1, 1))

    def integral(top, steps=20000):
        x = np.linspace(0, top, steps + 1)
        y = np.sin(x) ** e
        return (top / steps) * (y[0] + y[-1] + 4 * y[1:-1:2].sum() + 2 * y[2:-1:2].sum()) / 3
    return integral(phi) / integral(np.pi), "formula (decimal)"


def share(obj, lines, region, samples=400_000, seed=0):
    """The share of the object's points whose shadow on the given lines lands in the region.
    lines: direction vectors in the object's space; the shadow of a point is its list of
    positions along these lines. region: Past(k, t) or any function of the shadow array."""
    lines = [[F(x) for x in u] for u in lines]
    # exact: a ball and one "past" outcome
    if isinstance(obj, Ball) and isinstance(region, Past):
        u = lines[region.k]
        q = sum(x * x for x in u)
        r = _rational_sqrt(q)
        c = region.t / r if r is not None else float(region.t) / float(q) ** 0.5
        val, how = _ball_share_past(obj.shadow_power(), c)
        return {"value": val, "how": how}
    # exact: finitely many points, any region
    if isinstance(obj, Points):
        S = np.array([[sum(a * b for a, b in zip(u, p)) for u in lines] for p in obj.pts], dtype=object)
        hits = region(S)
        return {"value": F(int(sum(bool(h) for h in hits)), len(obj.pts)), "how": "exact"}
    # otherwise: sample
    rng = np.random.default_rng(seed)
    X = obj.sample(samples, rng)
    U = np.array([[float(x) for x in u] for u in lines])
    hits = np.asarray(region(X @ U.T), dtype=bool)
    v = hits.mean()
    return {"value": v, "how": "sampled", "error": 2 * (v * (1 - v) / samples) ** 0.5}


def shares(obj, lines, outcome, samples=400_000, seed=0):
    """Share of each outcome, where outcome(shadow array) labels every point's shadow."""
    lines_f = np.array([[float(x) for x in u] for u in lines])
    if isinstance(obj, Points):
        S = np.array([[sum(F(a) * b for a, b in zip(u, p)) for u in lines] for p in obj.pts], dtype=object)
        labels = outcome(S)
        cnt = Counter(tuple(l) if isinstance(l, np.ndarray) else l for l in labels)
        return {k: (F(v, len(obj.pts)), "exact", 0) for k, v in cnt.items()}
    rng = np.random.default_rng(seed)
    labels = outcome(obj.sample(samples, rng) @ lines_f.T)
    cnt = Counter(map(tuple, labels) if labels.ndim > 1 else labels.tolist())
    out = {}
    for k, v in cnt.items():
        p = v / samples
        out[k] = (p, "sampled", 2 * (p * (1 - p) / samples) ** 0.5)
    return out


def even_turn(n, rng, denom=400):
    """A turn chosen evenly among all turns of n-space, made exact: the Cayley table of a random
    turn, rounded to fractions (this moves it by about one part in a hundred thousand)."""
    I = np.eye(n)
    while True:
        Q, R = np.linalg.qr(rng.normal(size=(n, n)))
        Q = Q * np.sign(np.diag(R))
        M = I + Q
        if abs(np.linalg.det(M)) < 1e-3:
            continue
        A = (I - Q) @ np.linalg.inv(M)
        Af = [[F(0)] * n for _ in range(n)]
        for i in range(n):
            for j in range(i + 1, n):
                x = F((A[i, j] - A[j, i]) / 2).limit_denominator(denom)
                Af[i][j], Af[j][i] = x, -x
        return turn(Af)


def shadow_kinds(V, tilts=500, seed=0):
    """Turn the object evenly at random and report the share of each kind of shadow it casts."""
    rng = np.random.default_rng(seed)
    n = len(V[0])
    cnt = Counter()
    for _ in range(tilts):
        cnt[describe_shape(outline(apply(shadow_map(even_turn(n, rng)), V)))] += 1
    return {k: (v / tilts, 2 * ((v / tilts) * (1 - v / tilts) / tilts) ** 0.5) for k, v in cnt.most_common()}


def _fmt(val, how, err=0):
    if how == "exact":
        return f"{str(val):>9} = {float(val):.4f}  exact"
    if how == "sampled":
        return f"{float(val):.4f} ± {err:.4f}  sampled"
    return f"{float(val):.6f}  {how}"


def run_odds():
    print()
    print("=" * 72)
    print("ODDS: THE SHARE OF AN OBJECT THAT CASTS A SHADOW")
    print("=" * 72)

    print("\nA ball's shadow on a line, cut into five equal pieces: the share of the ball over each piece")
    cuts = [F(-1), F(-3, 5), F(-1, 5), F(1, 5), F(3, 5), F(1)]
    for n in [2, 3, 4, 5, 6]:
        b = Ball(n)
        past = [share(b, [[1] + [0] * (n - 1)], Past(0, c)) for c in cuts]
        pieces = [past[i]["value"] - past[i + 1]["value"] for i in range(5)]
        how = past[1]["how"]
        txt = "  ".join(f"{str(p) if how == 'exact' else f'{float(p):.4f}':>7}" for p in pieces)
        print(f"   surface of a ball in {n}D: {txt}   ({how})")

    print("\nOne spin: a ball in 3D, read on a line at an angle to the spin's direction.")
    print("Outcome 'up': the shadow lands past the spin direction's own shadow, taken from the other side.")
    for c, s in [(1, 0), (F(4, 5), F(3, 5)), (F(3, 5), F(4, 5)), (0, 1), (F(-3, 5), F(4, 5)), (-1, 0)]:
        line = [F(s), 0, F(c)]                         # a unit line whose angle has cosine c
        r = share(Ball(3), [line], Past(0, -F(c)))
        smp = share(Together(Ball(3)), [line], Past(0, -F(c)))
        print(f"   cosine {str(F(c)):>5}: share up {_fmt(r['value'], r['how'])};"
              f"  check by sampling {_fmt(smp['value'], smp['how'], smp['error'])}")

    print("\nKinds of shadow over random tilts (each object turned evenly at random):")
    for name, V, k in [("4D simplex", simplex(4), 1000), ("16-cell", cross(4), 1000),
                       ("4D cube", cube(4), 300), ("24-cell", cell24(), 300)]:
        print(f"   {name} ({k} tilts):")
        for kind, (p, e) in shadow_kinds(V, k, seed=7).items():
            print(f"      {p:.3f} ± {e:.3f}   {kind}")

    print("\nThe 4D cube's corners as equally likely points: share whose shadow is a corner of the outline")
    straight = [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0]]
    corner_first = [[F(1, 2), F(-1, 2), F(1, 2), F(-1, 2)], [F(1, 2), F(1, 2), F(-1, 2), F(-1, 2)],
                    [F(1, 2), F(-1, 2), F(-1, 2), F(1, 2)]]
    for name, P in [("straight on", straight), ("corner first", corner_first),
                    ("random tilt", shadow_map(random_turn(4, random.Random(3))))]:
        img = apply(P, cube(4))
        cs = set(outline(img)["corner_points"])
        on = F(sum(1 for p in img if p in cs), len(img))
        print(f"   {name:>12}: {_fmt(on, 'exact')}   (outline has {len(cs)} corners)")

    print("\nTwo balls taken as one object, shadowed on two lines at once (four shadow numbers).")
    print("Outcomes read from the joint shadow (the rule from the linked-pair test);")
    print("the two lines are at an angle whose cosine is 3/5 (about 53°):")
    a = [F(0), F(0), F(1)]
    b = [F(4, 5), F(0), F(3, 5)]
    z = [F(0)] * 3

    def pair(S):
        sg = lambda x: np.where(x >= 0, 1, -1)
        A = -sg(S[:, 0])
        c = sg(S[:, 0]) * sg(S[:, 1])
        B = sg(S[:, 2] + c * S[:, 3])
        return np.stack([A, B], axis=1)
    out = shares(Together(Ball(3), Ball(3)), [a + z, z + a, b + z, z + b], pair)
    for k in sorted(out):
        p, how, e = out[k]
        print(f"   answers {('up' if k[0] > 0 else 'down'):>4}, {('up' if k[1] > 0 else 'down'):>4}: "
              f"{_fmt(p, how, e)}")


if __name__ == "__main__":
    import sys
    if "odds" not in sys.argv:
        run()
    if "shapes" not in sys.argv:
        run_odds()


# ---------------------------------------------------------------- particles on floors (the building, start small)

def floor_odds(k, phi_deg):
    """A particle's direction sits on floor k's ball (the surface of the ball in k dimensions).
    A look along a line at angle phi (on that ball) to the direction answers 'yes' when a random
    point of the ball casts its shadow past the direction's own shadow, taken from the other side.
    Returns the share of the ball that answers 'yes'."""
    c = F(float(np.cos(np.radians(phi_deg))))
    r = share(Ball(k), [[1] + [0] * (k - 1)], Past(0, -c))
    return float(r["value"])


def run_floors():
    print()
    print("=" * 72)
    print("PARTICLES ON FLOORS: does the floor's ball give the observed odds?")
    print("=" * 72)
    print("\nElectron spin: magnet turned by angle t; observed odds of 'up' = (1 + cos t)/2.")
    print(f"{'t':>5} {'observed':>9} {'plane floor':>12} {'our floor':>10} {'4th floor':>10}")
    for t in [0, 30, 60, 90, 120, 150, 180]:
        obs = (1 + np.cos(np.radians(t))) / 2
        print(f"{t:>4}° {obs:>9.4f} {floor_odds(2, t):>12.4f} {floor_odds(3, t):>10.4f} {floor_odds(4, t):>10.4f}")
    print("\nLight: polarizer turned by angle t; observed odds of passing = cos^2 t.")
    print("(Light turned by a quarter turn is fully blocked, so on any ball it sits opposite: angle 2t.)")
    print(f"{'t':>5} {'observed':>9} {'plane floor':>12} {'our floor':>10} {'4th floor':>10}")
    for t in [0, 15, 30, 45, 60, 75, 90]:
        obs = np.cos(np.radians(t)) ** 2
        print(f"{t:>4}° {obs:>9.4f} {floor_odds(2, 2 * t):>12.4f} {floor_odds(3, 2 * t):>10.4f} {floor_odds(4, 2 * t):>10.4f}")


if __name__ == "__main__" and "floors" in sys.argv:
    run_floors()


# ---------------------------------------------------------------- the locator: where in the building does each particle live?
#
# Placements come only from the model: a floor of the building (0 = point, 1 = line, 2 = plane,
# 3 = ours, 4, 5), and on it the particle as some directions on that floor's compass
# (the compass = every direction one can point in on that floor).
# Several directions can sit on separate compasses side by side, or all on one shared compass.
# A look along a line: each direction answers 'yes' when the compass's random point casts its shadow
# past that direction's own shadow (taken from the other side); the particle's answer is how many say yes.
# Each particle's fingerprint comes only from observation: how many answers a look can give,
# the turn of the look that reverses the answer (sets how far around the compass a turn goes),
# and the observed odds as the look is turned.

def _compass_share(k, a):
    """Share of floor k's compass whose shadow lands at a or beyond."""
    if k == 1:                       # the line's compass is just its two ends
        return sum(1 for p in (-1, 1) if p >= a) / 2
    return float(_ball_share_past(Ball(k).shadow_power(), F(float(a)))[0])


def placement_odds(k, dirs, phi, shared):
    """Odds of each answer (number of 'yes') for directions at compass angles `dirs` (0 = north),
    looked at along a line turned by phi on the compass."""
    m = len(dirs)
    if m == 0:
        return [1.0]
    if k == 0:
        return None                  # a point has no directions to point in
    th = [-float(np.cos(np.radians(phi - d))) for d in dirs]
    if shared:                       # one random point of one compass answers for every direction
        ts = sorted(th)
        ge = [1.0] + [_compass_share(k, t) for t in ts] + [0.0]
        return [ge[j] - ge[j + 1] for j in range(m + 1)]
    ps = [_compass_share(k, t) for t in th]   # separate compasses: independent answers
    dist = [1.0]
    for p in ps:
        new = [0.0] * (len(dist) + 1)
        for j, q in enumerate(dist):
            new[j] += q * (1 - p)
            new[j + 1] += q * p
        dist = new
    return dist


PARTICLES = [
    # name, directions on the compass, turn that reverses the answer (deg), observed odds of 0..m 'yes' at turn t
    ("Higgs", [], None, lambda t: [1.0]),
    ("electron (spin pointing up)", [0], 180,
     lambda t: [(1 - np.cos(t)) / 2, (1 + np.cos(t)) / 2]),
    ("light (polarized)", [0], 90,
     lambda t: [np.sin(t) ** 2, np.cos(t) ** 2]),
    ("graviton (expected, not yet seen)", [0], 45,
     lambda t: [np.sin(2 * t) ** 2, np.cos(2 * t) ** 2]),
    ("W or Z, pointing up", [0, 0], 180,
     lambda t: [((1 - np.cos(t)) / 2) ** 2, np.sin(t) ** 2 / 2, ((1 + np.cos(t)) / 2) ** 2]),
    ("W or Z, pointing sideways", [0, 180], 180,
     lambda t: [np.sin(t) ** 2 / 2, np.cos(t) ** 2, np.sin(t) ** 2 / 2]),
]


def run_locator():
    print()
    print("=" * 72)
    print("THE LOCATOR: where does each particle live?")
    print("=" * 72)
    turns = list(range(0, 181, 15))
    floors = {0: "point", 1: "line", 2: "plane", 3: "ours", 4: "4th", 5: "5th"}
    for name, dirs, rev, observed in PARTICLES:
        m = len(dirs)
        s = 1 if rev is None else 180 // rev            # compass turn per turn of the look
        print(f"\n{name}: {m + 1} possible answer(s)" + ("" if rev is None else f", answer reverses at a {rev}° turn"))
        variants = [False] if m <= 1 else [False, True]
        for shared in variants:
            row = []
            for k in floors:
                worst = 0.0
                ok = True
                for t in turns:
                    pred = placement_odds(k, dirs, s * t, shared)
                    if pred is None:
                        ok = False
                        break
                    obs = observed(np.radians(t))
                    worst = max(worst, max(abs(a - b) for a, b in zip(pred, obs)))
                row.append("no room" if not ok else ("FITS" if worst < 1e-6 else f"off {worst:.3f}"))
            label = "" if m <= 1 else ("  one shared compass: " if shared else "  separate compasses: ")
            print(f"  {label:<23}" + "  ".join(f"{floors[k]}: {r:<8}" for k, r in zip(floors, row)))


if __name__ == "__main__" and "locate" in sys.argv:
    run_locator()


# ---------------------------------------------------------------- the locator, version 2: squared shadows
#
# A particle is one point on a floor's ball (written with arrows where the floor needs them).
# A look gives each possible answer its own flat plane through the center; the planes sit at right
# angles and fill the floor. The odds of an answer are the squared length of the point's shadow on
# that answer's plane (so the odds always add to one, and shadows can cancel before squaring).
# Each floor turns in its own natural way when our world turns:
#   point floor: it doesn't turn;           plane floor: it turns only about one path (r times as fast);
#   our floor:   ordinary turning;          4th floor: turning by the four-wide numbers (half as fast).
# A massive particle can be looked at along any direction, so its floor must turn with every turn of
# our world; a massless one is looked at only by turning about its path.

def _rot3(axis, ang):
    k = np.asarray(axis, float)
    k = k / np.linalg.norm(k)
    K = np.array([[0, -k[2], k[1]], [k[2], 0, -k[0]], [-k[1], k[0], 0]])
    return np.eye(3) + np.sin(ang) * K + (1 - np.cos(ang)) * K @ K


def _su2(axis, ang):
    k = np.asarray(axis, float)
    k = k / np.linalg.norm(k)
    sx = np.array([[0, 1], [1, 0]], complex)
    sy = np.array([[0, -1j], [1j, 0]])
    sz = np.array([[1, 0], [0, -1]], complex)
    return np.cos(ang / 2) * np.eye(2) - 1j * np.sin(ang / 2) * (k[0] * sx + k[1] * sy + k[2] * sz)


def _proj(v):
    v = np.asarray(v, complex)
    v = v / np.linalg.norm(v)
    return np.outer(v, v.conj())


s2 = 1 / np.sqrt(2)
FLOORS2 = {
    "point": {"any_axis": True, "turn": lambda ax, a, r: np.eye(1),
              "answers": {1: [[np.eye(1)]]}},
    "plane": {"any_axis": False, "turn": lambda ax, a, r: _rot3([0, 0, 1], r * a)[:2, :2],
              "answers": {2: [[_proj([1, 0]), _proj([0, 1])]]}},
    "ours": {"any_axis": True, "turn": lambda ax, a, r: _rot3(ax, a),
             "answers": {2: [[_proj([0, 0, 1]), np.eye(3) - _proj([0, 0, 1])],
                             [np.eye(3) - _proj([0, 0, 1]), _proj([0, 0, 1])],
                             [_proj([1, 0, 0]), np.eye(3) - _proj([1, 0, 0])]],
                         3: [[_proj([s2, 1j * s2, 0]), _proj([0, 0, 1]), _proj([s2, -1j * s2, 0])]]}},
    "4th": {"any_axis": True, "turn": lambda ax, a, r: _su2(ax, a),
            "answers": {2: [[_proj([1, 0]), _proj([0, 1])]]}},
}

PARTICLES2 = [
    # name, massive?, observed odds: for massive, a function of the look's direction n (prepared along z);
    # for massless, a function of the polarizer turn t; and which answer is certain at the start
    ("Higgs", True, lambda n: [1.0], 0),
    ("electron, spin up", True, lambda n: [(1 + n[2]) / 2, (1 - n[2]) / 2], 0),
    ("W or Z, pointing up", True,
     lambda n: [((1 + n[2]) / 2) ** 2, (1 - n[2] ** 2) / 2, ((1 - n[2]) / 2) ** 2], 0),
    ("W or Z, pointing sideways", True,
     lambda n: [(1 - n[2] ** 2) / 2, n[2] ** 2, (1 - n[2] ** 2) / 2], 1),
    ("light, polarized", False, lambda t: [np.cos(t) ** 2, np.sin(t) ** 2], 0),
    ("graviton (expected)", False, lambda t: [np.cos(2 * t) ** 2, np.sin(2 * t) ** 2], 0),
]


def _fit(floor, answers, massive, observed, start, rate, rng, objects=300):
    """Best possible match over every object certain to give answer `start` at the first look."""
    F_ = FLOORS2[floor]
    P0 = answers[start]
    w, V = np.linalg.eigh(P0)
    basis = V[:, w > 0.5]                       # the start answer's plane
    if massive:
        looks = [np.array([0, 0, 1.0])] + [v / np.linalg.norm(v) for v in rng.normal(size=(40, 3))]
    else:
        looks = list(np.radians(np.arange(0, 180, 7.5)))
    best = np.inf
    for _ in range(objects):
        c = rng.normal(size=basis.shape[1]) + 1j * rng.normal(size=basis.shape[1])
        psi = basis @ c
        psi = psi / np.linalg.norm(psi)
        worst = 0.0
        for lk in looks:
            if massive:
                n = lk
                ax = np.cross([0, 0, 1.0], n)
                ang = np.arccos(np.clip(n[2], -1, 1))
                if np.linalg.norm(ax) < 1e-12:
                    ax = np.array([1.0, 0, 0])
                U = F_["turn"](ax, ang, rate)
                obs = observed(n)
            else:
                U = F_["turn"]([0, 0, 1], lk, rate)
                obs = observed(lk)
            pred = [float(np.real(psi.conj() @ (U @ P @ U.conj().T) @ psi)) for P in answers]
            worst = max(worst, max(abs(a - b) for a, b in zip(pred, obs)))
        best = min(best, worst)
        if best < 1e-9:
            break
    return best


def run_locator2():
    print()
    print("=" * 72)
    print("THE LOCATOR, SQUARED SHADOWS: the smallest floor where each particle fits")
    print("=" * 72)
    rng = np.random.default_rng(4)
    order = ["point", "plane", "ours", "4th"]
    for name, massive, observed, start in PARTICLES2:
        k = len(observed(np.array([0, 0, 1.0])) if massive else observed(0.0))
        cells = []
        home = None
        for fl in order:
            F_ = FLOORS2[fl]
            if massive and not F_["any_axis"]:
                cells.append(f"{fl}: can't turn with every turn of our world")
                continue
            if k not in F_["answers"]:
                cells.append(f"{fl}: can't give {k} answers")
                continue
            rates = [1] if fl != "plane" else [1, 2, 3]
            best, best_r = np.inf, None
            for answers in F_["answers"][k]:
                for r in rates:
                    g = _fit(fl, answers, massive, observed, start, r, rng)
                    if g < best:
                        best, best_r = g, r
            if best < 1e-9:
                cells.append(f"{fl}: FITS" + (f" (turning {best_r}x as fast)" if fl == "plane" else ""))
                home = home or fl
            else:
                cells.append(f"{fl}: off {best:.3f}")
        print(f"\n{name} ({'massive' if massive else 'massless'}, {k} answer{'s' if k > 1 else ''}):"
              f"   smallest floor that fits: {home or 'none'}")
        for c in cells:
            print("     " + c)


if __name__ == "__main__" and "locate2" in sys.argv:
    run_locator2()
