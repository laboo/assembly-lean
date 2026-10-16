#!/usr/bin/env python3
"""The electron, steps 5 to 7 (placements on the building, each checked by a shadow)."""
import numpy as np
import itertools
import time
import sys

SX = np.array([[0, 1], [1, 0]], complex)
SY = np.array([[0, -1j], [1j, 0]])
SZ = np.array([[1, 0], [0, -1]], complex)
I2, Z2 = np.eye(2), np.zeros((2, 2))


def sp(p):
    return p[0] * SX + p[1] * SY + p[2] * SZ


def electron_rule(p, m=1.0):
    """The electron's object: two 4th-floor copies (left- and right-handed), mass = switching."""
    return np.block([[-sp(p), m * I2], [m * I2, sp(p)]])


def step5(m=1.0):
    print("=" * 74)
    print("STEP 5: THE POSITRON (placed as the mirror image of the electron's object)")
    print("=" * 74)
    rng = np.random.default_rng(5)
    # The mirror: a fixed mixing C of the four arrows applied to their mirror images (complex conjugates).
    # Find every C for which the mirror of a solution is again a solution of the same rule:
    #   C conj(H(p)) = -H(-p) C   for all p  (linear in C)
    rows = []
    for _ in range(6):
        p = rng.normal(size=3)
        A, B = np.conj(electron_rule(p, m)), -electron_rule(-p, m)
        # C A - B C = 0  ->  (A^T kron I - I kron B) vec(C) = 0
        rows.append(np.kron(A.T, np.eye(4)) - np.kron(np.eye(4), B))
    M = np.vstack(rows)
    _, s, Vh = np.linalg.svd(M)
    null = Vh[np.abs(s) < 1e-9] if (np.abs(s) < 1e-9).any() else Vh[-1:]
    C = null[-1].reshape(4, 4, order="F")
    C = C / np.sqrt(np.abs(np.linalg.det(C)) ** 0.5)
    print(f"mirrors that turn electron solutions into solutions of the same rule: {int((s < 1e-9).sum())} (up to a factor)")

    def mirror(psi):
        return C @ np.conj(psi)

    worst_e = worst_rate = 0.0
    charge_ok = True
    for _ in range(100):
        p = rng.normal(size=3) * rng.uniform(0.1, 3)
        w, V = np.linalg.eigh(electron_rule(p, m))
        E = np.sqrt(p @ p + m * m)
        for k in range(4):
            psi = V[:, k]
            if w[k] < 0:                       # the electron rule's backward-turning part
                phi = mirror(psi)              # its mirror image, at wave number -p
                rate = np.real(np.vdot(phi, electron_rule(-p, m) @ phi) / np.vdot(phi, phi))
                worst_rate = max(worst_rate, abs(rate - E))
        a = rng.uniform(0, 2 * np.pi)
        psi = rng.normal(size=4) + 1j * rng.normal(size=4)
        # shared turn: the electron turns by a; its mirror turns by -a
        lhs = mirror(np.exp(1j * a) * psi)
        rhs = np.exp(-1j * a) * mirror(psi)
        charge_ok &= np.allclose(lhs, rhs)
    twice = C @ np.conj(C)
    print(f"the mirror of the electron's backward-turning part turns forward at the electron's own rate"
          f" (same mass, same energy rule): off by at most {worst_rate:.1e}")
    print(f"under the shared turn the mirror turns the opposite way (opposite charge): {'yes' if charge_ok else 'no'}")
    print(f"mirror twice gives back the original (up to a sign): "
          f"{'yes' if np.allclose(twice, twice[0, 0] * np.eye(4)) and np.isclose(abs(twice[0, 0]), 1) else 'no'}"
          f" (sign {twice[0, 0].real:+.0f})")
    print("an electron and its mirror together: charges +1 and -1, total 0 exactly, so the pair can turn")
    print("entirely into light (which carries no charge), keeping the energy of two masses.")


if __name__ == "__main__":
    steps = sys.argv[1:] or ["5", "6", "7"]
    if "5" in steps:
        step5()


def step6():
    print()
    print("=" * 74)
    print("STEP 6: CHARGE (turning on the crushed circle when stepping through a field)")
    print("=" * 74)
    print("Placement: each step between neighbours turns the electron's shared circle by the field's amount")
    print("on that link. A sealed tube between the two slits holds the field; the electron never enters it.")
    Nx, Ny, dt, k0 = 512, 620, 0.2, 1.0
    yb, ys, d, w = 150, 560, 40, 8
    x1, x2 = Nx // 2 - d // 2, Nx // 2 + d // 2
    xc = Nx // 2 - 1                                  # the tube sits between the slits, just behind them
    yt = yb + 10
    X, Y = np.meshgrid(np.arange(Nx), np.arange(Ny), indexing="ij")
    edge = 40
    dist = np.minimum.reduce([X, Nx - 1 - X, Y, Ny - 1 - Y]).astype(float)
    mask = np.where(dist < edge, np.exp(-((edge - dist) / edge) ** 2 * 0.08), 1.0)
    wall = np.zeros((Nx, Ny), bool)
    wall[:, yb:yb + 4] = True
    for xs in (x1, x2):
        wall[xs - w // 2: xs + w // 2, yb:yb + 4] = False
    wall[xc - 3: xc + 5, yt: yt + 8] = True            # the sealed tube
    env = np.exp(-((X - Nx / 2) ** 2) / (2 * 70.0 ** 2) - ((Y - 70) ** 2) / (2 * 20.0 ** 2))
    psi0 = env * np.exp(1j * k0 * Y)

    def run(theta, steps=3600):
        # turn on the links from column xc to xc+1, from inside the tube up to the top: the field is only
        # where those links end, inside the tube; everywhere the electron goes, the field is zero
        Px = np.ones((Nx, Ny), complex)
        Px[xc, yt + 4:] = np.exp(1j * theta)

        def H(f):
            return -0.5 * (Px * np.roll(f, -1, 0) + np.conj(np.roll(Px, 1, 0)) * np.roll(f, 1, 0)
                           + np.roll(f, -1, 1) + np.roll(f, 1, 1) - 4 * f)
        prev = psi0 * ~wall
        cur = prev - 1j * dt * H(prev)
        cur[wall] = 0
        screen = np.zeros(Nx)
        for _ in range(steps):
            nxt = prev - 2j * dt * H(cur)
            nxt[wall] = 0
            nxt *= mask
            prev, cur = cur * mask, nxt
            screen += np.abs(cur[:, ys]) ** 2
        return screen / screen.sum()

    t0 = time.time()
    thetas = [0, 0.25, 0.5, 0.75, 1.0]
    pats = {f: run(2 * np.pi * f) for f in thetas}
    print(f"({len(thetas)} runs, {time.time() - t0:.0f}s)")
    base = pats[0]
    win = slice(Nx // 2 - 154, Nx // 2 + 155)
    xs_ = np.arange(Nx)[win]
    # stripe spacing from the unturned run, then each run's stripe position as a fraction of a stripe
    q = base[win]
    pk = [i for i in range(1, len(q) - 1) if q[i] > q[i - 1] and q[i] >= q[i + 1] and q[i] > 0.2 * q.max()]
    S = np.mean(np.diff(pk))

    def phase(p):
        return np.angle(np.sum(p[win] * np.exp(-2j * np.pi * xs_ / S)))
    print(f"stripe spacing {S:.1f} cells")
    print(f"{'turn enclosed by the two paths':>32} {'stripes shift by':>17} {'expected':>9}")
    for f in thetas:
        sh = ((phase(pats[f]) - phase(base)) / (2 * np.pi)) % 1
        sh = sh if sh < 0.999 else 0.0
        exp = f % 1
        print(f"{f:>26.2f} of a full turn {sh:>13.3f} {exp:>9.2f}  (stripes)")
    print("Observed (electrons around a sealed magnetic tube): the stripes shift in step with the field")
    print("inside, by one whole stripe per fixed amount of field, though the electrons never touch it.")
    c = lambda p: (p[Nx // 2 - 70: Nx // 2 + 70].max() - p[Nx // 2 - 70: Nx // 2 + 70].min()) / \
        (p[Nx // 2 - 70: Nx // 2 + 70].max() + p[Nx // 2 - 70: Nx // 2 + 70].min())
    print(f"stripe contrast stays: {', '.join(f'{c(pats[f]):.3f}' for f in thetas)}")


if __name__ == "__main__" and "6" in (sys.argv[1:] or ["5", "6", "7"]):
    step6()


def step7():
    print()
    print("=" * 74)
    print("STEP 7: NO SHARING (several electrons as one object that flips sign when any two swap)")
    print("=" * 74)
    rng = np.random.default_rng(7)
    # two electrons on a small row of 10 places, each with its two spin answers: 20 slots
    S = 20
    T = rng.normal(size=(S, S)) + 1j * rng.normal(size=(S, S))
    flip = T - T.T                      # the object that flips sign when the two electrons swap
    keep = T + T.T                      # an object that doesn't flip, for contrast
    odds = lambda O: np.abs(O) ** 2 / (np.abs(O) ** 2).sum()
    same = lambda O: sum(odds(O)[s, s] for s in range(S))
    print(f"odds both electrons sit in the same slot (place and spin):  flipping object {same(flip):.3f};"
          f"  non-flipping object {same(keep):.3f}")
    # same place, opposite spins is a different pair of slots, so it stays allowed
    o = odds(flip)
    same_place_opposite_spin = sum(o[2 * k, 2 * k + 1] + o[2 * k + 1, 2 * k] for k in range(S // 2))
    print(f"odds they share a place with opposite spins (still allowed):  {same_place_opposite_spin:.3f}")

    print("\nHow many electrons fit in each shell of an atom?")
    print("Slots per shell come from the atom's whole-number turns: shell n has bands of 1, 3, 5, ... up to n bands,")
    print("so n*n turn patterns, each with the electron's two spin answers.")
    print(f"{'shell':>6} {'slots':>6} {'most electrons a flipping object can hold':>44}")
    for n in range(1, 5):
        slots = sum(2 * l + 1 for l in range(n)) * 2
        # build the flipping object for k electrons from k one-electron states in these slots;
        # it vanishes exactly when the k states cannot all be told apart (k > slots)
        cap = 0
        for k in range(1, slots + 2):
            A = rng.normal(size=(k, slots)) + 1j * rng.normal(size=(k, slots))
            sv = np.linalg.svd(A, compute_uv=False)
            nonzero = sv.min() > 1e-9 if k <= slots else False   # k rows in 'slots' columns: rank <= slots
            if k > slots:
                nonzero = np.linalg.matrix_rank(A) == k
            if nonzero:
                cap = k
        print(f"{n:>6} {slots:>6} {cap:>44}")
    print("Observed: shells hold 2, 8, 18 and 32 electrons.")
    print("A non-flipping object has no limit: any number can pile into one slot (as light does in a laser).")


if __name__ == "__main__" and "7" in (sys.argv[1:] or ["5", "6", "7"]):
    step7()
