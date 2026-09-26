# Results of the equivalence check

Prompt: [`equivalence-prompt-en.md`](equivalence-prompt-en.md). Each row is one independent run.
The last column records whether the model's arguments were checked by hand and found correct.

| # | Date | Model | Verdict | Items flagged | Arguments checked |
|---|---|---|---|---|---|
| 1 | 2026-09-26 | not recorded | EQUIVALENT | none (1–7: OK) | yes, all seven correct |

## Run 1 — details

- Item 2: every distance-preserving self-map of `ℝ³` is bijective, so quantifying over `E3 ≃ᵢ E3` is
  the same as over all isometries; reflections are included. Correct (Mazur–Ulam: such a map is
  affine with an orthogonal linear part).
- Item 3: the square root is used only when `x > s ≥ 0`, so its argument `x² + y² − s²` is positive;
  boundary cases match. Correct.
- Item 4: `NCcase` passes the arguments of `Fit2` in the order of `Fit(p_{i'}, p_{i''}; q_j, h*)`.
  Correct.
- Item 5: `σ 0, σ 1, σ 2 ↔ i, i', i''` and `τ 0, τ 1, τ 2 ↔ j, k, l`; `Equiv.Perm (Fin 3)` ranges over
  all permutations. Correct.
- Items 1, 6, 7: no issues. Correct.
