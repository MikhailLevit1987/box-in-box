"""Reference implementation of the criterion NC for fitting a box into a box.

This is a literal transcription of the definitions `stripOK`, `stripH`, `Fit2`, `NCcase`, `NC`
from `lean/Boxes/Statement.lean`. The Lean theorem `Boxes.fits_iff_NC` states that, for
p > 0 and q >= 0, the box with edges q fits into the box with edges p (under arbitrary rigid
motions) if and only if NC(p, q) holds.

Floating-point caveat: the comparisons below are exact only in exact arithmetic. Near the boundary
(when the box fits "exactly") rounding may flip the answer.

Usage:
    python box_fit.py P1 P2 P3 Q1 Q2 Q3          # does box Q fit into box P?
    python box_fit.py --place P1 P2 P3 Q1 Q2 Q3  # and if so, an explicit placement x -> R x + t
    python box_fit.py --selftest                 # examples, cross-check with Carver's 2D formula,
                                                 # verification of the placements
"""
import itertools
import math
import random
import sys


def strip_ok(u, v, s):
    """The u x v rectangle can be put into a strip of width s."""
    return min(u, v) <= s


def strip_h(u, v, s):
    """Least extent along a strip of width s of the u x v rectangle placed in it (Lemma 1)."""
    x, y = max(u, v), min(u, v)
    if x <= s:
        return y
    r2 = x * x + y * y
    return min(x, (2 * x * y * s + (x * x - y * y) * math.sqrt(r2 - s * s)) / r2)


def fit2(a, b, u, v):
    """The u x v rectangle fits into the a x b rectangle."""
    return strip_ok(u, v, a) and strip_h(u, v, a) <= b


def nc_case(p, q, sigma, tau):
    """One check: axis sigma[0] is the height, edge tau[0] is horizontal."""
    return (strip_ok(q[tau[1]], q[tau[2]], p[sigma[0]])
            and fit2(p[sigma[1]], p[sigma[2]], q[tau[0]],
                     strip_h(q[tau[1]], q[tau[2]], p[sigma[0]])))


def nc(p, q):
    """Criterion NC: some check passes (all 36 pairs of permutations, as in Lean)."""
    perms = list(itertools.permutations(range(3)))
    return any(nc_case(p, q, s, t) for s in perms for t in perms)


def strip_angle(u, v, s):
    """(c, d), c, d >= 0, c^2 + d^2 = 1, with u*c + v*d <= s and u*d + v*c <= strip_h(u, v, s).

    The optimal direction from the proof of the strip lemma (Lemma 3.1(a)); needs min(u, v) <= s.
    """
    x, y = max(u, v), min(u, v)
    if x <= s:
        c, d = 1.0, 0.0
    else:
        r2 = x * x + y * y
        rt = math.sqrt(r2 - s * s)
        c, d = (x * s - y * rt) / r2, (y * s + x * rt) / r2
        if x * d + y * c > x:          # the endpoint theta = pi/2 is better
            c, d = 0.0, 1.0
    return (d, c) if u < v else (c, d)


def place(p, q):
    """An explicit placement of box q in box p, or None if it does not fit.

    Returns (sigma, tau, theta1, theta2, R, t): the check that holds, the two angles (radians) of the
    construction of Proposition 4.1, a rotation matrix R (det R = 1) and a translation t such that
    x -> R x + t maps the box [0,q1] x [0,q2] x [0,q3] into [0,p1] x [0,p2] x [0,p3].
    """
    perms = list(itertools.permutations(range(3)))
    for s in perms:
        for t in perms:
            if not nc_case(p, q, s, t):
                continue
            c1, d1 = strip_angle(q[t[1]], q[t[2]], p[s[0]])
            h = strip_h(q[t[1]], q[t[2]], p[s[0]])
            c2, d2 = strip_angle(q[t[0]], h, p[s[1]])
            r0 = [[0.0, c1, -d1], [c2, -d1 * d2, -c1 * d2], [d2, d1 * c2, c1 * c2]]
            rm = [[0.0] * 3 for _ in range(3)]
            for a in range(3):
                for b in range(3):
                    rm[s[a]][t[b]] = r0[a][b]
            det = (rm[0][0] * (rm[1][1] * rm[2][2] - rm[1][2] * rm[2][1])
                   - rm[0][1] * (rm[1][0] * rm[2][2] - rm[1][2] * rm[2][0])
                   + rm[0][2] * (rm[1][0] * rm[2][1] - rm[1][1] * rm[2][0]))
            if det < 0:                    # reverse one edge: same box, proper rotation
                for a in range(3):
                    rm[a][t[0]] = -rm[a][t[0]]
            tr = [-sum(min(0.0, rm[i][j] * q[j]) for j in range(3)) for i in range(3)]
            return s, t, math.atan2(d1, c1), math.atan2(d2, c2), rm, tr
    return None


def nc_fast(p, q):
    """Criterion NC with only the 9 essentially different checks (same answer as nc).

    nc runs through all 36 pairs of permutations, like the Lean definition.  A check depends only on
    the height axis i and the horizontal edge j: H is symmetric in its first two arguments, and
    Fit(a, b; u, v) and Fit(b, a; u, v) both say that the u x v rectangle fits into the a x b one
    (Remark 3.2), so one order of the floor axes suffices.
    """
    for i in range(3):
        a, b = p[(i + 1) % 3], p[(i + 2) % 3]
        for j in range(3):
            u, v = q[(j + 1) % 3], q[(j + 2) % 3]
            if min(u, v) <= p[i] and fit2(a, b, q[j], strip_h(u, v, p[i])):
                return True
    return False


def strip_h_strict(u, v, s):
    """Strict version of strip_h (Lean: stripHs). Note the branch `x < s`, not `x <= s`."""
    x, y = max(u, v), min(u, v)
    if x < s:
        return y
    r2 = x * x + y * y
    return min(x, (2 * x * y * s + (x * x - y * y) * math.sqrt(max(r2 - s * s, 0.0))) / r2)


def nc_strict(p, q):
    """Strict criterion NCs (Lean: fitsStrict_iff_NCs): Q fits into the open box P."""
    perms = list(itertools.permutations(range(3)))
    for s in perms:
        for t in perms:
            if not min(q[t[1]], q[t[2]]) < p[s[0]]:
                continue
            h = strip_h_strict(q[t[1]], q[t[2]], p[s[0]])
            if min(q[t[0]], h) < p[s[1]] and strip_h_strict(q[t[0]], h, p[s[1]]) < p[s[2]]:
                return True
    return False


def carver(a, b, u, v):
    """Carver's closed-form 2D criterion (independent cross-check of fit2, not used by nc)."""
    a, b = max(a, b), min(a, b)
    x, y = max(u, v), min(u, v)
    if x <= a and y <= b:
        return True
    if y > b or x == y:
        return False
    return ((a + b) / (x + y)) ** 2 + ((a - b) / (x - y)) ** 2 >= 2


def selftest():
    s2 = math.sqrt(2)
    examples = [
        ("rod of length sqrt(3)-0.01 in the unit cube", (1, 1, 1), (math.sqrt(3) - 0.01, 0, 0), True),
        ("rod of length sqrt(3)+0.01 in the unit cube", (1, 1, 1), (math.sqrt(3) + 0.01, 0, 0), False),
        ("square plate 1.05 x 1.05 in the unit cube", (1, 1, 1), (1.05, 1.05, 0), True),
        ("square plate 1.07 x 1.07 in the unit cube (> 3*sqrt(2)/4)", (1, 1, 1), (1.07, 1.07, 0), False),
        ("1.1 x 1.1 x 0.01 in the unit cube", (1, 1, 1), (1.1, 1.1, 0.01), False),
        ("box into itself", (3, 4, 8), (3, 4, 8), True),
        ("2 x 2 x 2 into the unit cube", (1, 1, 1), (2, 2, 2), False),
        ("thin rod 12 x 1 x 1 into the cube of side 9", (9, 9, 9), (12, 1, 1), True),
        ("largest square 3*sqrt(2)/4 - 1e-9", (1, 1, 1), (3 * s2 / 4 - 1e-9,) * 2 + (0,), True),
    ]
    ok = True
    for name, p, q, expected in examples:
        got = nc(p, q)
        flag = "ok " if got == expected else "BAD"
        ok &= got == expected
        print(f"{flag} {name}: {got}")
    strict_examples = [
        ("strict: 1 x 0.5 x 0.5 into the unit cube (touches)", (1, 1, 1), (1, 0.5, 0.5), False),
        ("strict: 0.99 x 0.5 x 0.5 into the unit cube", (1, 1, 1), (0.99, 0.5, 0.5), True),
        ("strict: box into itself", (3, 4, 8), (3, 4, 8), False),
        ("strict: 12 x 2 x 3 into 10 x 10 x 3.01", (10, 10, 3.01), (12, 2, 3), True),
    ]
    for name, p, q, expected in strict_examples:
        got = nc_strict(p, q)
        flag = "ok " if got == expected else "BAD"
        ok &= got == expected
        print(f"{flag} {name}: {got}")
    rnd = random.Random(1)
    mismatches = 0
    n = 200000
    for _ in range(n):
        a, b, u, v = (rnd.uniform(0.01, 2) for _ in range(4))
        if abs(max(u, v) - max(a, b)) < 1e-9:
            continue
        c = carver(a, b, u, v)
        if fit2(a, b, u, v) != c or fit2(b, a, u, v) != c:
            mismatches += 1
    print(f"fit2 (both orientations) vs Carver on {n} random rectangles: {mismatches} mismatches")
    fast_bad = 0
    for _ in range(200000):
        p = [rnd.uniform(0.5, 3) for _ in range(3)]
        q = [rnd.uniform(0, 3) for _ in range(3)]
        if nc_fast(p, q) != nc(p, q):
            fast_bad += 1
    print(f"nc_fast (9 checks) vs nc (36 checks) on 200000 random pairs: {fast_bad} mismatches")
    ok &= fast_bad == 0
    placed, bad = 0, 0
    for _ in range(50000):
        p = [rnd.uniform(0.5, 3) for _ in range(3)]
        q = [rnd.uniform(0, 3) for _ in range(3)]
        res = place(p, q)
        if (res is None) != (not nc(p, q)):
            bad += 1
        if res is None:
            continue
        placed += 1
        *_, rm, tr = res
        orth = max(abs(sum(rm[i][k] * rm[j][k] for k in range(3)) - (i == j))
                   for i in range(3) for j in range(3))
        det = (rm[0][0] * (rm[1][1] * rm[2][2] - rm[1][2] * rm[2][1])
               - rm[0][1] * (rm[1][0] * rm[2][2] - rm[1][2] * rm[2][0])
               + rm[0][2] * (rm[1][0] * rm[2][1] - rm[1][1] * rm[2][0]))
        inside = all(-1e-9 <= sum(rm[i][j] * e[j] * q[j] for j in range(3)) + tr[i] <= p[i] + 1e-9
                     for e in itertools.product((0, 1), repeat=3) for i in range(3))
        if orth > 1e-9 or abs(det - 1) > 1e-9 or not inside:
            bad += 1
    print(f"place: {placed} placements checked (rotation, det = 1, all vertices inside): {bad} failures")
    return ok and mismatches == 0 and bad == 0


if __name__ == "__main__":
    if sys.argv[1:] == ["--selftest"]:
        sys.exit(0 if selftest() else 1)
    args = sys.argv[1:]
    want_place = args[:1] == ["--place"]
    if want_place:
        args = args[1:]
    if len(args) != 6:
        print(__doc__)
        sys.exit(2)
    vals = [float(x) for x in args]
    pp, qq = vals[:3], vals[3:]
    if not want_place:
        print("fits" if nc(pp, qq) else "does not fit")
        sys.exit(0)
    res = place(pp, qq)
    if res is None:
        print("does not fit")
        sys.exit(0)
    sg, ta, th1, th2, rm, tr = res
    print(f"fits: height axis {sg[0] + 1}, horizontal edge {ta[0] + 1}; "
          f"tilt of the face in the vertical strip {math.degrees(th1):.4f} deg, "
          f"rotation on the floor {math.degrees(th2):.4f} deg")
    print("x -> R x + t with")
    for i in range(3):
        print("  R[%d] = [%s]   t[%d] = %.9f" % (i + 1, ", ".join(f"{v + 0.0: .9f}" for v in rm[i]), i + 1, tr[i] + 0.0))
    print("vertices of the placed box:")
    for e in itertools.product((0, 1), repeat=3):
        v = [sum(rm[i][j] * e[j] * qq[j] for j in range(3)) + tr[i] for i in range(3)]
        print("  (" + ", ".join(f"{x:.6f}" for x in v) + ")")
