"""Reference implementation of the criterion NC for fitting a box into a box.

This is a literal transcription of the definitions `stripOK`, `stripH`, `Fit2`, `NCcase`, `NC`
from `lean/Boxes/Statement.lean`. The Lean theorem `Boxes.fits_iff_NC` states that, for
p > 0 and q >= 0, the box with edges q fits into the box with edges p (under arbitrary rigid
motions) if and only if NC(p, q) holds.

Floating-point caveat: the comparisons below are exact only in exact arithmetic. Near the boundary
(when the box fits "exactly") rounding may flip the answer.

Usage:
    python box_fit.py P1 P2 P3 Q1 Q2 Q3      # does box Q fit into box P?
    python box_fit.py --selftest             # examples + cross-check with Carver's 2D formula
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
    return ok and mismatches == 0


if __name__ == "__main__":
    if sys.argv[1:] == ["--selftest"]:
        sys.exit(0 if selftest() else 1)
    if len(sys.argv) != 7:
        print(__doc__)
        sys.exit(2)
    vals = [float(x) for x in sys.argv[1:]]
    print("fits" if nc(vals[:3], vals[3:]) else "does not fit")
