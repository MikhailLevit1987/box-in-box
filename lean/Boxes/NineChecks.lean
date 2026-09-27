import Boxes.Necessity

/-!
# Nine checks suffice

The criterion `NC` runs through all 36 pairs of permutations `σ, τ`. Only 9 checks are essentially
different: a check depends only on the height axis `σ 0` and the horizontal edge `τ 0`, because
`stripH` is symmetric in its first two arguments and `Fit2 a b u v ↔ Fit2 b a u v` (both say that the
`u × v` rectangle fits into the `a × b` rectangle).

`NC9` is the criterion with these 9 checks (the other two axes and edges taken in cyclic order);
it is what `tools/box_fit.py` computes in `nc_fast`. `NC_iff_NC9` shows that it is equivalent to `NC`.
-/

namespace Boxes

open Real

lemma stripOK_comm (u v s : ℝ) : stripOK u v s ↔ stripOK v u s := by
  unfold stripOK; rw [min_comm]

lemma stripH_comm (u v s : ℝ) : stripH u v s = stripH v u s := by
  simp only [stripH, max_comm u v, min_comm u v]

lemma stripH_nonneg {u v s : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hs : 0 ≤ s) (h : stripOK u v s) :
    0 ≤ stripH u v s := by
  obtain ⟨c, d, hc, hd, -, -, h2⟩ := strip_exists hu hv hs h
  nlinarith [mul_nonneg hu hd, mul_nonneg hv hc]

/-- `Fit2` does not depend on the order of the sides of the container rectangle. -/
lemma Fit2_comm {a b u v : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (h : Fit2 a b u v) : Fit2 b a u v := by
  obtain ⟨c, d, hc, hd, hcd, h1, h2⟩ := strip_exists hu hv ha h.1
  obtain ⟨k1, k2⟩ := strip_min (c := d) (d := c) hu hv hb hd hc (by linarith) (by linarith [h.2])
  exact ⟨k1, by linarith⟩

/-- The criterion with the 9 essentially different checks: axis `i` is the height, edge `j` is
horizontal, the other axes and edges are taken in cyclic order. -/
def NC9 (p q : Fin 3 → ℝ) : Prop :=
  ∃ i j : Fin 3, stripOK (q (j + 1)) (q (j + 2)) (p i) ∧
    Fit2 (p (i + 1)) (p (i + 2)) (q j) (stripH (q (j + 1)) (q (j + 2)) (p i))

/-- In a permutation of `Fin 3`, the images of `1` and `2` are the two elements other than the
image of `0`, in one of the two orders. -/
lemma perm_three (σ : Equiv.Perm (Fin 3)) :
    (σ 1 = σ 0 + 1 ∧ σ 2 = σ 0 + 2) ∨ (σ 1 = σ 0 + 2 ∧ σ 2 = σ 0 + 1) := by
  have h01 : σ 0 ≠ σ 1 := σ.injective.ne (by decide)
  have h02 : σ 0 ≠ σ 2 := σ.injective.ne (by decide)
  have h12 : σ 1 ≠ σ 2 := σ.injective.ne (by decide)
  generalize σ 0 = a at *
  generalize σ 1 = b at *
  generalize σ 2 = c at *
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp_all

/-- The cyclic permutation `k ↦ k + i`. -/
lemma addRight_apply (i k : Fin 3) : Equiv.addRight i k = i + k := by
  simp [add_comm]

theorem NC_iff_NC9 (p q : Fin 3 → ℝ) (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 ≤ q i) :
    NC p q ↔ NC9 p q := by
  constructor
  · rintro ⟨σ, τ, hc⟩
    obtain ⟨h1, h2⟩ : stripOK (q (τ 1)) (q (τ 2)) (p (σ 0)) ∧
        Fit2 (p (σ 1)) (p (σ 2)) (q (τ 0)) (stripH (q (τ 1)) (q (τ 2)) (p (σ 0))) := hc
    refine ⟨σ 0, τ 0, ?_⟩
    -- the two edges in the vertical plane: order does not matter
    have e1 : stripOK (q (τ 0 + 1)) (q (τ 0 + 2)) (p (σ 0)) ∧
        stripH (q (τ 0 + 1)) (q (τ 0 + 2)) (p (σ 0)) = stripH (q (τ 1)) (q (τ 2)) (p (σ 0)) := by
      rcases perm_three τ with ⟨ht1, ht2⟩ | ⟨ht1, ht2⟩
      · rw [← ht1, ← ht2]; exact ⟨h1, rfl⟩
      · rw [← ht1, ← ht2, stripOK_comm, stripH_comm]; exact ⟨h1, rfl⟩
    refine ⟨e1.1, ?_⟩
    rw [e1.2]
    -- the two floor axes: order does not matter either
    rcases perm_three σ with ⟨hs1, hs2⟩ | ⟨hs1, hs2⟩
    · rw [← hs1, ← hs2]; exact h2
    · rw [← hs1, ← hs2]
      exact Fit2_comm (hp _).le (hp _).le (hq _)
        (stripH_nonneg (hq _) (hq _) (hp _).le h1) h2
  · rintro ⟨i, j, h1, h2⟩
    refine ⟨Equiv.addRight i, Equiv.addRight j, ?_⟩
    show stripOK (q (Equiv.addRight j 1)) (q (Equiv.addRight j 2)) (p (Equiv.addRight i 0)) ∧
      Fit2 (p (Equiv.addRight i 1)) (p (Equiv.addRight i 2)) (q (Equiv.addRight j 0))
        (stripH (q (Equiv.addRight j 1)) (q (Equiv.addRight j 2)) (p (Equiv.addRight i 0)))
    simp only [addRight_apply, add_zero]
    exact ⟨h1, h2⟩

/-- The main theorem with the 9 essentially different checks. -/
theorem fits_iff_NC9 (p q : Fin 3 → ℝ) (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 ≤ q i) :
    Fits p q ↔ NC9 p q :=
  (fits_iff_NC p q hp hq).trans (NC_iff_NC9 p q hp hq)

end Boxes
