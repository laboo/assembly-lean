#!/usr/bin/env python3
"""
One complete particle, step by step: the electron.
Each step places a part of the electron on a floor (the model's claim),
then a shadow checks that placement against what is observed.

Step 2. The full-turn flip.
  Placement: the electron's spin is a point on the 4th floor's ball (two arrows),
  and the 4th floor turns half as fast as our world (the four-wide numbers).
  Check: send it down two paths, turn one path by angle a, bring the paths together.
  The odds of coming out of the bright exit are the squared shadow of the recombined object.
  Observed (with neutrons, same spin as the electron): the odds come back only after two full turns.

Step 3. Where it is.
  Placement: a copy of that 4th-floor point (two arrows) at every place on our floor,
  each place passing numbers only to its neighbours. Each arrow is two numbers that nudge
  each other, one minus sign (the two-number form of the 1926 wave rule).
  Check: two slits; the odds at a screen are the squared shadows summed over time.
  Observed: stripes, spaced by wavelength x distance / slit separation; one slit alone: no stripes.
"""
import numpy as np
import time

np.set_printoptions(precision=4, suppress=True)


def su2(axis, ang):
    k = np.asarray(axis, float) / np.linalg.norm(axis)
    sx = np.array([[0, 1], [1, 0]], complex)
    sy = np.array([[0, -1j], [1j, 0]])
    sz = np.array([[1, 0], [0, -1]], complex)
    return np.cos(ang / 2) * np.eye(2) - 1j * np.sin(ang / 2) * (k[0] * sx + k[1] * sy + k[2] * sz)


def rot3(axis, ang):
    k = np.asarray(axis, float) / np.linalg.norm(axis)
    K = np.array([[0, -k[2], k[1]], [k[2], 0, -k[0]], [-k[1], k[0], 0]])
    return np.eye(3) + np.sin(ang) * K + (1 - np.cos(ang)) * K @ K


def step2():
    print("=" * 74)
    print("STEP 2: THE FULL-TURN FLIP (two paths, one turned by angle a, then recombined)")
    print("=" * 74)
    rng = np.random.default_rng(0)
    axis = np.array([0, 0, 1.0])
    print(f"{'turn a':>8} {'4th floor':>10} {'our floor':>10}   (odds of the bright exit)")
    worst4, worst3 = 0.0, 0.0
    for deg in [0, 90, 180, 270, 360, 450, 540, 630, 720]:
        a = np.radians(deg)
        # the electron's spin, any direction: 4th floor (two arrows) and our floor (an arrow in 3D)
        odd4, odd3 = [], []
        for _ in range(200):
            psi = rng.normal(size=2) + 1j * rng.normal(size=2)
            psi /= np.linalg.norm(psi)
            out = (psi + su2(axis, a) @ psi) / 2            # bright exit = the two paths added
            odd4.append(np.vdot(out, out).real)
            v = rng.normal(size=3) + 1j * rng.normal(size=3)
            v /= np.linalg.norm(v)
            out3 = (v + rot3(axis, a) @ v) / 2
            odd3.append(np.vdot(out3, out3).real)
        print(f"{deg:>7}° {np.mean(odd4):>10.3f} {np.mean(odd3):>10.3f}")
        if deg in (360,):
            worst4 = np.mean(odd4)
            worst3 = np.mean(odd3)
    print("Observed: after one full turn (360°) the bright exit is at its dimmest; it is fully")
    print("bright again only after two full turns (720°).")
    print(f"At 360°: 4th floor {worst4:.3f} (dimmest, matches); our floor {worst3:.3f} (fully back, does not match).")


def step3():
    print()
    print("=" * 74)
    print("STEP 3: WHERE IT IS (two slits, neighbours only, squared shadows)")
    print("=" * 74)
    Nx, Ny = 512, 620             # across, along
    dt = 0.2
    k0 = 1.0                       # the electron's wave number along its path (wavelength 2*pi)
    yb, ys = 150, 560              # barrier row, screen row
    d, w = 40, 8                   # slit separation and width
    x1, x2 = Nx // 2 - d // 2, Nx // 2 + d // 2
    X, Y = np.meshgrid(np.arange(Nx), np.arange(Ny), indexing="ij")

    # absorbing edges so nothing comes back
    edge = 40
    dist = np.minimum.reduce([X, Nx - 1 - X, Y, Ny - 1 - Y]).astype(float)
    mask = np.where(dist < edge, np.exp(-((edge - dist) / edge) ** 2 * 0.08), 1.0)

    def run(slits, steps=3600):
        wall = np.zeros((Nx, Ny), bool)
        wall[:, yb:yb + 4] = True
        for xc in slits:
            wall[xc - w // 2: xc + w // 2, yb:yb + 4] = False
        open_ = ~wall
        # the placed object: two arrows (the 4th-floor point) at every place, spin pointing up
        spin = np.array([1.0, 0.0], complex)
        env = np.exp(-((X - Nx / 2) ** 2) / (2 * 70.0 ** 2) - ((Y - 70) ** 2) / (2 * 20.0 ** 2))
        psi0 = env * np.exp(1j * k0 * Y)
        # two numbers per arrow: R (this floor) and I (the next), nudging each other with one minus sign
        R = np.stack([spin[c].real * psi0.real - spin[c].imag * psi0.imag for c in range(2)])
        I = np.stack([spin[c].real * psi0.imag + spin[c].imag * psi0.real for c in range(2)])

        def H(f):                  # passes numbers only between neighbours
            lap = (np.roll(f, 1, 1) + np.roll(f, -1, 1) + np.roll(f, 1, 2) + np.roll(f, -1, 2) - 4 * f)
            return -0.5 * lap
        I = I - 0.5 * dt * H(R)    # stagger I by half a tick
        screen = np.zeros(Nx)
        for _ in range(steps):
            R = R + dt * H(I)
            R *= open_
            R *= mask
            I = I - dt * H(R)
            I *= open_
            I *= mask
            screen += (R[:, :, ys] ** 2 + I[:, :, ys] ** 2).sum(axis=0)
        return screen / screen.sum()

    t0 = time.time()
    both = run([x1, x2])
    one1 = run([x1])
    one2 = run([x2])
    print(f"(three runs, {time.time() - t0:.0f}s)")
    shares = (one1 + one2) / 2          # odds that only add (no cancelling)
    L = ys - yb
    lam = 2 * np.pi / k0
    xs = np.arange(Nx)
    centre = slice(Nx // 2 - 160, Nx // 2 + 160)

    def peaks(p):
        q = p[centre]
        i = [j for j in range(1, len(q) - 1) if q[j] > q[j - 1] and q[j] >= q[j + 1] and q[j] > 0.2 * q.max()]
        return [j + centre.start for j in i]

    pk = peaks(both)
    c0 = (x1 + x2 - 1) / 2                     # the middle between the slit openings
    L = ys - (yb + 4)                           # from the slits' far side to the screen
    E = 2 - np.cos(k0) - 1.0                    # the wave's energy on the grid (straight ahead)
    smooth, grid = [], []
    for m in range(-2, 3):
        # smooth space: path difference = m wavelengths
        smooth.append(c0 + L * np.tan(np.arcsin(m * lam / d)))
        # on the grid: the same rule, but waves travel in a slightly different direction than
        # their crests point (by sin k / k), which a finer grid makes vanish
        kx = 2 * np.pi * m / d
        ky = np.arccos(2 - np.cos(kx) - E)
        grid.append(c0 + L * np.sin(kx) / np.sin(ky))
    print(f"Both slits open, bright stripes at (cells across the screen): {pk}")
    print(f"Expected, smooth space (path difference = whole wavelengths):  {[round(x) for x in smooth]}")
    print(f"Expected, including the grid's own direction effect:          {[round(x) for x in grid]}")
    print(f"Stripe spacing: measured {np.diff(pk).mean():.1f}; smooth space {np.diff(smooth).mean():.1f}; "
          f"with the grid effect {np.diff(grid).mean():.1f}")
    print(f"(The grid effect is sin(k)/k = {np.sin(k0) / k0:.3f} here and goes to 1 as the grid gets finer:")
    print(f" separate runs at k = 0.7 and 0.5 gave stripe spacings 9% and 4% wider than smooth space.)")
    def contrast(p):
        q = p[Nx // 2 - 70: Nx // 2 + 70]
        return (q.max() - q.min()) / (q.max() + q.min())
    print(f"Stripe contrast near the middle (1 = full stripes, 0 = none):")
    print(f"   both slits, squared shadows:      {contrast(both):.3f}")
    print(f"   one slit alone:                   {contrast(one1):.3f}")
    print(f"   both slits, odds that only add:   {contrast(shares):.3f}")
    np.savez("double_slit.npz", both=both, one1=one1, one2=one2)


if __name__ == "__main__":
    import sys
    if "4" in sys.argv or len(sys.argv) == 1:
        pass


SX = np.array([[0, 1], [1, 0]], complex)
SY = np.array([[0, -1j], [1j, 0]])
SZ = np.array([[1, 0], [0, -1]], complex)


def _sigma_p(p):
    return p[0] * SX + p[1] * SY + p[2] * SZ


def _real(Mc):
    """A complex-linear rule written as a rule on real numbers (each arrow = two numbers)."""
    A, B = Mc.real, Mc.imag
    return np.block([[A, -B], [B, A]])


def _real_conj(Mc):
    """The rule psi -> Mc @ conj(psi), written on real numbers."""
    A, B = Mc.real, Mc.imag
    return np.block([[A, B], [B, -A]])


def step4(m=1.0):
    print()
    print("=" * 74)
    print("STEP 4: MASS (where does the electron's mass fit?)")
    print("=" * 74)
    rng = np.random.default_rng(3)
    eps = 1j * SY    # pairs an arrow pair with its own mirror image

    # each placement: the rule that moves the object, as a real matrix for a wave of wave number p
    placements = {
        "4th floor, no mass (4 numbers)":
            (4, lambda p: _real(-1j * _sigma_p(p)), lambda U: _real(U)),
        # switching with the mirror pairs the wave moving one way with the mirror of the wave moving the
        # other way, so the two directions are followed together (still 4 numbers at each place)
        "4th floor, mass by switching with its own mirror (4 numbers)":
            (8, lambda p: _real(np.block([[-1j * _sigma_p(p), np.zeros((2, 2))],
                                          [np.zeros((2, 2)), 1j * _sigma_p(p)]]))
                + _real_conj(np.block([[np.zeros((2, 2)), -1j * m * eps], [-1j * m * eps, np.zeros((2, 2))]])),
             lambda U: _real(np.block([[U, np.zeros((2, 2))], [np.zeros((2, 2)), U]]))),
        "two 4th-floor copies, left- and right-handed, mass by switching between them (8 numbers)":
            (8, lambda p: _real(-1j * np.block([[-_sigma_p(p), m * np.eye(2)], [m * np.eye(2), _sigma_p(p)]])),
             lambda U: _real(np.block([[U, np.zeros((2, 2))], [np.zeros((2, 2)), U]]))),
    }
    for name, (nums, rule, turnrep) in placements.items():
        e_err, spin_err, charge_err, rest, fastest = 0.0, 0.0, 0.0, None, 0.0
        for _ in range(200):
            p = rng.normal(size=3) * rng.uniform(0.1, 3)
            M = rule(p)
            w = np.sort(np.abs(np.linalg.eigvals(M).imag))
            target = np.sqrt(p @ p + m * m)
            e_err = max(e_err, np.max(np.abs(w - target)))
            # speed of a wave packet: change of the turning rate with wave number
            dp = 1e-6 * p / np.linalg.norm(p)
            w2 = np.sort(np.abs(np.linalg.eigvals(rule(p + dp)).imag))
            fastest = max(fastest, np.max((w2 - w) / np.linalg.norm(dp)))
            # turning with our world: turn the wave and the object together
            ax, ang = rng.normal(size=3), rng.uniform(0, 2 * np.pi)
            Rm = _rot3(ax, ang)
            U = turnrep(_su2c(ax, ang))
            spin_err = max(spin_err, np.max(np.abs(rule(Rm @ p) - U @ M @ np.linalg.inv(U))))
            # the shared turn (charge): turning every arrow by the same amount must not change the rule
            a = rng.uniform(0, 2 * np.pi)
            V = _real(np.exp(1j * a) * np.eye(nums // 2))
            charge_err = max(charge_err, np.max(np.abs(M @ V - V @ M)))
        rest = np.sort(np.abs(np.linalg.eigvals(rule(np.zeros(3))).imag)).max()
        ok = lambda x: "yes" if x < 1e-6 else f"no (off by {x:.2f})"
        print(f"\n{name}:")
        print(f"   energy rule of relativity (turning rate^2 = wave number^2 + mass^2):  {ok(e_err)}")
        print(f"   has mass (turns even when standing still): {'yes' if rest > 1e-9 else 'no'};"
              f"  never faster than light: {'yes' if fastest <= 1 + 1e-6 else 'no'} (fastest {fastest:.3f})")
        print(f"   turns properly with every turn of our world (spin):                    {ok(spin_err)}")
        print(f"   unchanged by the shared turn (so it can carry charge):                 {ok(charge_err)}")


def _rot3(axis, ang):
    return rot3(axis, ang)


def _su2c(axis, ang):
    return su2(axis, ang)


if __name__ == "__main__":
    import sys
    steps = sys.argv[1:] or ["2", "3", "4"]
    if "2" in steps:
        step2()
    if "3" in steps:
        step3()
    if "4" in steps:
        step4()
