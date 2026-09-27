# When does a box fit into a box?

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22974798.svg)](https://doi.org/10.5281/zenodo.22974798)

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

### Strict fitting

For fitting without touching the container (`lean/Boxes/Strict.lean`):

* `fitsStrict_iff_shrink`: the box fits strictly ⇔ it fits (criterion above) into `p − ε` for some `ε > 0`;
* `fitsStrict_iff_NCs`: an explicit strict criterion — all inequalities strict **and** the case split
  in `H` changed from `x ≤ s` to `x < s`. Making only the inequalities strict is wrong: for the unit
  cube and the `1 × 0.5 × 0.5` box it would answer "fits strictly".

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
'Boxes.fitsStrict_iff_shrink' depends on axioms: [propext, Classical.choice, Quot.sound]
'Boxes.fitsStrict_iff_NCs' depends on axioms: [propext, Classical.choice, Quot.sound]
```

i.e. no `sorryAx`. The meaning of the theorem depends only on the definitions `box` and `Fits`
(`lean/Boxes/Statement.lean`); the criterion `NC` is the formula above, and its equivalence with
`Fits` is what is proved.

## Using the reference implementation

```sh
python tools/box_fit.py 8 4 3  9.43 0 0             # a rod of length 9.43 into an 8 × 4 × 3 box → fits
python tools/box_fit.py --place 1.2 2.7 2.64  2.8 1.3 0.25   # the placement: angles, R, t, vertices
python tools/box_fit.py --selftest
python tools/benchmark.py                           # timing versus a numerical search (numpy, scipy)
```

`--place` returns a rotation `R` (det R = 1) and a translation `t` such that `x ↦ R x + t` maps the
box `q` into the box `p`; it is the construction from the proof of sufficiency. The criterion takes
about 20–25 µs per pair in Python, the placement about 20 µs; a multi-start numerical search over
rotations is 3·10³–2·10⁴ times slower on pairs near the boundary and can wrongly answer "does not fit"
(section "Computation" of the paper).

Floating-point comparisons are exact only in exact arithmetic; near the boundary rounding may flip
the answer.

## Citation

Mikhail Levit, *When does a box fit into a box? An explicit criterion with a formal proof*, 2026.
Zenodo, [doi:10.5281/zenodo.22974798](https://doi.org/10.5281/zenodo.22974798) (all versions;
version 1.0: [doi:10.5281/zenodo.22974799](https://doi.org/10.5281/zenodo.22974799)).

## License

Code (`lean/`, `tools/`, `verification/`): [Apache License 2.0](LICENSE), the same as Mathlib.
Paper (`paper/`): [Creative Commons Attribution 4.0 International](paper/LICENSE).
