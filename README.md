# When does a box fit into a box?

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22974798.svg)](https://doi.org/10.5281/zenodo.22974798)

An explicit necessary and sufficient condition for a rectangular box with edges $q_1, q_2, q_3 \ge 0$
to fit, after an arbitrary rigid motion, into a rectangular box with edges $p_1, p_2, p_3 > 0$,
with a complete formal proof in Lean 4 / Mathlib.

*Русская версия статьи: [`paper/box-in-box-ru.pdf`](paper/box-in-box-ru.pdf).*

## The criterion

For $x \ge y \ge 0$ and $s \ge 0$ let

```math
H(x,y;s)=\begin{cases}
y, & x\le s,\\[4pt]
\min\left(x,\ \dfrac{2xys+(x^2-y^2)\sqrt{x^2+y^2-s^2}}{x^2+y^2}\right), & x>s,
\end{cases}
```

$H(u,v;s)=H(\max(u,v),\min(u,v);s)$, and $\mathrm{Fit}(a,b;u,v)$ means $\min(u,v)\le a$ and
$H(u,v;a)\le b$ (the $u\times v$ rectangle fits into the $a\times b$ rectangle).

**Theorem.** The box $q$ fits into the box $p$ if and only if for some choice of a "height" axis $i$
of $p$ (the other two being $i', i''$) and a "horizontal" edge $j$ of $q$ (the other two being $k, l$)

```math
\min(q_k,q_l)\le p_i \qquad\text{and}\qquad \mathrm{Fit}\bigl(p_{i'},\,p_{i''};\;q_j,\;H(q_k,q_l;p_i)\bigr).
```

These are 9 essentially different checks: $H$ is symmetric in $q_k, q_l$, and both orders of
$p_{i'}, p_{i''}$ give the same condition. (The Lean definition and `tools/box_fit.py` simply run
through all 36 pairs of permutations.) The key step: if a box fits at
all, it fits with one of its edges perpendicular to one of the axes of the container, because at any
other position all three widths of the box can be decreased simultaneously.

### Strict fitting

For fitting without touching the container (`lean/Boxes/Strict.lean`):

* `fitsStrict_iff_shrink`: the box fits strictly ⇔ it fits (criterion above) into `p − ε` for some `ε > 0`;
* `fitsStrict_iff_NCs`: an explicit strict criterion — every inequality made strict, including the
  case split in `H` (`x ≤ s` becomes `x < s`); the cost is the same. Making strict only the
  inequalities of the checks, with `H` unchanged, is wrong: for the unit cube and the
  `1 × 0.5 × 0.5` box it would answer "fits strictly".

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
about 40 µs per pair in Python with all 36 checks (`nc`) and about 7 µs with the 9 essentially
different ones (`nc_fast`), the placement about 12 µs; a multi-start local numerical search
over rotations is 2·10³–10⁴ times slower on pairs near the boundary and can wrongly answer "does not
fit" (section "Computation" of the paper).

Floating-point comparisons are exact only in exact arithmetic; near the boundary rounding may flip
the answer.

## Citation

Mikhail Levit, *When does a box fit into a box? An explicit criterion with a formal proof*, 2026.
Zenodo, [doi:10.5281/zenodo.22974798](https://doi.org/10.5281/zenodo.22974798) (all versions,
resolves to the latest one).

| Version | DOI |
|---|---|
| 1.1 | [10.5281/zenodo.22986340](https://doi.org/10.5281/zenodo.22986340) |
| 1.0 | [10.5281/zenodo.22974799](https://doi.org/10.5281/zenodo.22974799) |

## License

Code (`lean/`, `tools/`, `verification/`): [Apache License 2.0](LICENSE), the same as Mathlib.
Paper (`paper/`): [Creative Commons Attribution 4.0 International](paper/LICENSE).
