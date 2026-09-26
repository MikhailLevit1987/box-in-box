# Task: check that a Lean 4 statement says exactly what a mathematical theorem says

You are reviewing a formalization. Your only job is to decide whether the **Lean statement** below
is logically equivalent to the **mathematical theorem** below. Do **not** try to prove or disprove the
theorem, and do not assess the proof: the Lean proof has been machine-checked (no `sorry`, only the
standard axioms `propext`, `Classical.choice`, `Quot.sound`). The only remaining risk is that the
formal statement does not mean what the mathematical statement means. Be skeptical and precise.

## 1. The mathematical theorem

Let `P = [0,p₁]×[0,p₂]×[0,p₃]` with `pᵢ > 0` and `Q = [0,q₁]×[0,q₂]×[0,q₃]` with `qⱼ ≥ 0`
(closed boxes in Euclidean 3-space). `Q` *fits into* `P` if `f(Q) ⊆ P` for some isometry `f` of `ℝ³`
(rotations, translations and reflections allowed).

For `x ≥ y ≥ 0`, `s ≥ 0`:

```
H(x, y; s) = y                                                   if x ≤ s
H(x, y; s) = min( x, (2xys + (x² − y²)·√(x² + y² − s²)) / (x² + y²) )   if x > s
```

and for arbitrary `u, v ≥ 0`: `H(u, v; s) = H(max(u,v), min(u,v); s)`.

`Fit(a, b; u, v)` means: `min(u,v) ≤ a` and `H(u, v; a) ≤ b`.

**Criterion NC(p, q):** there exist a permutation `(i, i', i'')` of the axes `(1,2,3)` and a
permutation `(j, k, l)` of the edges `(1,2,3)` such that

```
min(q_k, q_l) ≤ p_i   and   Fit(p_{i'}, p_{i''}; q_j, h*),   where h* = H(q_k, q_l; p_i).
```

**Theorem.** If `p₁, p₂, p₃ > 0` and `q₁, q₂, q₃ ≥ 0`, then `Q` fits into `P` if and only if
`NC(p, q)` holds.

## 2. The Lean 4 statement (verbatim; Lean 4 + Mathlib, indices are `0, 1, 2`)

```lean
namespace Boxes
open Real

/-- Euclidean space `ℝ³`. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- The closed box with edges `q` along the coordinate axes. -/
def box (q : Fin 3 → ℝ) : Set E3 := {x | ∀ i, 0 ≤ x i ∧ x i ≤ q i}

/-- The box with edges `q` fits into the box with edges `p`. -/
def Fits (p q : Fin 3 → ℝ) : Prop := ∃ f : E3 ≃ᵢ E3, f '' box q ⊆ box p

def stripOK (u v s : ℝ) : Prop := min u v ≤ s

noncomputable def stripH (u v s : ℝ) : ℝ :=
  let x := max u v
  let y := min u v
  if x ≤ s then y
  else min x ((2 * x * y * s + (x ^ 2 - y ^ 2) * √(x ^ 2 + y ^ 2 - s ^ 2)) / (x ^ 2 + y ^ 2))

def Fit2 (a b u v : ℝ) : Prop := stripOK u v a ∧ stripH u v a ≤ b

def NCcase (p q : Fin 3 → ℝ) (σ τ : Equiv.Perm (Fin 3)) : Prop :=
  stripOK (q (τ 1)) (q (τ 2)) (p (σ 0)) ∧
  Fit2 (p (σ 1)) (p (σ 2)) (q (τ 0)) (stripH (q (τ 1)) (q (τ 2)) (p (σ 0)))

def NC (p q : Fin 3 → ℝ) : Prop := ∃ σ τ : Equiv.Perm (Fin 3), NCcase p q σ τ

theorem fits_iff_NC (p q : Fin 3 → ℝ) (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 ≤ q i) :
    Fits p q ↔ NC p q
```

Notes on Lean/Mathlib notation, for reference:
* `EuclideanSpace ℝ (Fin 3)` is `ℝ³` with the Euclidean distance; `x i` is the `i`-th coordinate.
* `E3 ≃ᵢ E3` is the type of isometric bijections of `E3` onto itself (`IsometryEquiv`).
* `f '' S` is the image of the set `S` under `f`; `⊆` is set inclusion.
* `√t` is `Real.sqrt t`, which is defined for all reals and equals `0` for `t < 0`.
* `Equiv.Perm (Fin 3)` is the type of permutations of `{0, 1, 2}`.
* `min`, `max` on `ℝ` are the usual ones; `if … then … else …` is an ordinary case split.

## 3. What to check (answer every item)

1. Does `box q` coincide with `[0,q₀]×[0,q₁]×[0,q₂]` (closed, axis-parallel, one corner at the origin)?
2. Does `Fits p q` coincide with "Q fits into P" as defined above? In particular: is quantifying over
   isometric **bijections** `E3 ≃ᵢ E3` the same as quantifying over all isometries of `ℝ³`? Does
   allowing reflections matter for boxes?
3. Does `stripH u v s` coincide with `H(u, v; s)` for all `u, v ≥ 0`, `s ≥ 0`, including boundary cases
   (`x = s`, `y = s`, `y = 0`, `x = y`, `u = v = 0`)? Can the square root ever receive a negative
   argument in the branch where it is used?
4. Does `Fit2 a b u v` coincide with `Fit(a, b; u, v)` (mind the order of arguments)?
5. Does `NC p q` coincide with the criterion `NC(p, q)`: is the correspondence between
   `σ, τ` and `(i, i', i'')`, `(j, k, l)` exact (every mathematical check is some Lean `NCcase`, and
   vice versa)?
6. Do the hypotheses `hp`, `hq` of `fits_iff_NC` match `pᵢ > 0`, `qⱼ ≥ 0`, with nothing added or missing?
7. Is there any other way in which the Lean statement is weaker, stronger, or vacuous compared with
   the mathematical theorem (e.g. an implicit coercion, an off-by-one index, a definition that is
   trivially true or false)?

## 4. Required answer format

```
VERDICT: EQUIVALENT | NOT EQUIVALENT | UNSURE
1: OK | PROBLEM — <one or two sentences>
2: OK | PROBLEM — ...
3: OK | PROBLEM — ...
4: OK | PROBLEM — ...
5: OK | PROBLEM — ...
6: OK | PROBLEM — ...
7: OK | PROBLEM — ...
DETAILS: <any explanation; for every PROBLEM give a concrete input (numbers) on which the two
statements differ, or say explicitly that you could not find one>
```

Do not answer `NOT EQUIVALENT` without a concrete distinguishing example or a precise logical reason.
If you are not sure about a Lean/Mathlib detail, say so and answer `UNSURE` rather than guessing.
