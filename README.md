# When does a box fit into a box?

An explicit necessary and sufficient condition for a rectangular box with edges `q₁, q₂, q₃ ≥ 0`
to fit, after an arbitrary rigid motion, into a rectangular box with edges `p₁, p₂, p₃ > 0`,
with a complete formal proof in Lean 4 / Mathlib.

*Русская версия статьи: [`paper/box-in-box-ru.pdf`](paper/box-in-box-ru.pdf).*

## The criterion

For `x ≥ y ≥ 0`, `s ≥ 0` let

```
H(x, y; s) = y                                                   if x ≤ s,
H(x, y; s) = min( x, (2xys + (x² − y²)·√(x² + y² − s²)) / (x² + y²) )   if x > s,
```

`H(u, v; s) = H(max(u,v), min(u,v); s)`, and `Fit(a, b; u, v) :⇔ min(u,v) ≤ a and H(u, v; a) ≤ b`
(the `u × v` rectangle fits into the `a × b` rectangle).

**Theorem.** The box `q` fits into the box `p` if and only if for some choice of a "height" axis `i`
of `p` (the other two being `i', i''`) and a "horizontal" edge `j` of `q` (the other two being `k, l`)

```
min(q_k, q_l) ≤ p_i   and   Fit(p_i', p_i''; q_j, H(q_k, q_l; p_i)).
```

These are 9 explicit checks (18 counting the order of `i', i''`). The key step: if a box fits at
all, it fits with one of its edges perpendicular to one of the axes of the container, because at any
other position all three widths of the box can be decreased simultaneously.

## Contents

| Path | What |
|---|---|
| [`paper/box-in-box-en.pdf`](paper/box-in-box-en.pdf), [`paper/box-in-box-ru.pdf`](paper/box-in-box-ru.pdf) | The paper (English, Russian), LaTeX sources alongside |
| [`lean/`](lean/) | Lean 4 formalization; main theorem `Boxes.fits_iff_NC` in `lean/Boxes/Necessity.lean` |
| [`lean/Boxes/Statement.lean`](lean/Boxes/Statement.lean) | The statement: definitions `box`, `Fits` and the criterion `NC` |
| [`tools/box_fit.py`](tools/box_fit.py) | Reference implementation of the criterion (a literal transcription of the Lean definitions) |
| [`verification/`](verification/) | A self-contained prompt for independent checking that the Lean statement matches the theorem |

## Checking the formal proof

Requires [elan](https://github.com/leanprover/elan) (the Lean toolchain manager).

```sh
cd lean
lake exe cache get      # download prebuilt Mathlib (several GB)
lake build              # builds the Boxes library; a few minutes
lake env lean CheckAxioms.lean
```

Expected output of the last command:

```
'Boxes.fits_iff_NC' depends on axioms: [propext, Classical.choice, Quot.sound]
'Boxes.fits_of_NC' depends on axioms: [propext, Classical.choice, Quot.sound]
'Boxes.NC_of_fits' depends on axioms: [propext, Classical.choice, Quot.sound]
```

i.e. no `sorryAx`. The meaning of the theorem depends only on the definitions `box` and `Fits`
(`lean/Boxes/Statement.lean`); the criterion `NC` is the formula above, and its equivalence with
`Fits` is what is proved.

## Using the reference implementation

```sh
python tools/box_fit.py 8 4 3  9.43 0 0     # a rod of length 9.43 into an 8 × 4 × 3 box → fits
python tools/box_fit.py --selftest
```

Floating-point comparisons are exact only in exact arithmetic; near the boundary rounding may flip
the answer.
