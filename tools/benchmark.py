"""Timing of the criterion and of the explicit placement versus a numerical search over rotations.

The numerical baseline minimises F(R) = max_i w_i(R) / p_i over rotations by Nelder-Mead from random
starts (quaternion parametrisation) and answers "fits" as soon as some start reaches F <= 1. Such a
search can confirm fitting, but a "does not fit" answer only means that no start succeeded.

Test pairs lie close to the boundary: q is scaled by t*(1 + e) or t*(1 - e), where t* is the
largest scale at which q fits (found by bisection with the criterion) and 1e-4 <= e <= 1e-2.

Requires numpy and scipy.  Usage: python benchmark.py
"""
import math
import time

import numpy as np
from scipy.optimize import minimize

import box_fit as bf


def rot(v):
    w, x, y, z = v / np.linalg.norm(v)
    return np.array([[1 - 2 * (y * y + z * z), 2 * (x * y - w * z), 2 * (x * z + w * y)],
                     [2 * (x * y + w * z), 1 - 2 * (x * x + z * z), 2 * (y * z - w * x)],
                     [2 * (x * z - w * y), 2 * (y * z + w * x), 1 - 2 * (x * x + y * y)]])


def numeric_place(p, q, starts, rng):
    """A rotation found by the numerical search, or None."""
    p, q = np.asarray(p), np.asarray(q)
    f = lambda v: np.max(np.abs(rot(v)) @ q / p)
    for _ in range(starts):
        r = minimize(f, rng.normal(size=4), method='Nelder-Mead',
                     options={'xatol': 1e-10, 'fatol': 1e-12, 'maxiter': 4000})
        if r.fun <= 1:
            return rot(r.x)
    return None


def instances(n, rng):
    out = []
    while len(out) < n:
        p = np.sort(rng.uniform(1, 3, 3))[::-1]
        q = np.sort(rng.uniform(0.2, 3, 3))[::-1]
        lo, hi = 0.0, 3.0
        for _ in range(60):
            mid = (lo + hi) / 2
            if bf.nc(list(p), list(mid * q)):
                lo = mid
            else:
                hi = mid
        s = lo * (1 + rng.choice([-1, 1]) * 10 ** rng.uniform(-4, -2))
        out.append(([float(x) for x in p], [float(s * x) for x in q]))
    return out


def per_call(fn, data, repeat=20):
    t = time.perf_counter()
    for _ in range(repeat):
        for p, q in data:
            fn(p, q)
    return (time.perf_counter() - t) / (repeat * len(data))


def main():
    rng = np.random.default_rng(1)
    data = instances(200, rng)
    exact = [bf.nc(p, q) for p, q in data]
    fitting = [d for d, e in zip(data, exact) if e]
    print(f"{len(data)} pairs near the boundary, {len(fitting)} of them fit")
    t_nc = per_call(bf.nc, data)
    t_pl = per_call(bf.place, fitting)
    print(f"criterion NC (yes/no):             {t_nc * 1e6:8.1f} us per pair")
    print(f"criterion + explicit placement:    {t_pl * 1e6:8.1f} us per fitting pair")
    for starts in (5, 20, 50):
        t = time.perf_counter()
        num = [numeric_place(p, q, starts, rng) is not None for p, q in data]
        t_num = (time.perf_counter() - t) / len(data)
        wrong = sum(a != b for a, b in zip(exact, num))
        print(f"numerical search, {starts:2d} starts:     {t_num * 1e3:8.1f} ms per pair "
              f"(~{t_num / t_nc:,.0f} times slower), wrong answers: {wrong} of {len(data)}")


if __name__ == "__main__":
    main()
