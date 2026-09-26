import Mathlib

/-!
# Basic reduction: a linearly mapped box inside an axis-parallel box

For `q : ι → ℝ` with `q ≥ 0` let `Q = Icc 0 q = ∏ⱼ [0, qⱼ]`.
For any real matrix `R` (not necessarily orthogonal), some translate of `R • Q` lies in the
axis-parallel box `Icc 0 p` if and only if `∑ⱼ qⱼ |Rᵢⱼ| ≤ pᵢ` for every `i`.

Orthogonality is not needed here; it enters only in `Boxes.Statement`, where fitting is
understood as an arbitrary isometry of Euclidean space.
-/

open Finset Matrix

namespace Boxes

variable {ι κ : Type*} [Fintype ι]

/-- Lower end of the projection of `R • Icc 0 q` onto axis `i`. -/
noncomputable def lo (R : Matrix κ ι ℝ) (q : ι → ℝ) (i : κ) : ℝ :=
  ∑ j, min 0 (R i j * q j)

/-- Upper end of the projection of `R • Icc 0 q` onto axis `i`. -/
noncomputable def hi (R : Matrix κ ι ℝ) (q : ι → ℝ) (i : κ) : ℝ :=
  ∑ j, max 0 (R i j * q j)

/-- The width of the projection onto axis `i` is `∑ⱼ qⱼ |Rᵢⱼ|`. -/
theorem hi_sub_lo (R : Matrix κ ι ℝ) (q : ι → ℝ) (hq : 0 ≤ q) (i : κ) :
    hi R q i - lo R q i = ∑ j, q j * |R i j| := by
  unfold hi lo
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [max_sub_min_eq_abs, sub_zero, abs_mul, abs_of_nonneg ((show (0:ℝ) ≤ q j from hq j)), mul_comm]

lemma term_bounds (a x q : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ q) :
    min 0 (a * q) ≤ a * x ∧ a * x ≤ max 0 (a * q) := by
  rcases le_total 0 a with ha | ha
  · exact ⟨(min_le_left _ _).trans (mul_nonneg ha h0),
      (mul_le_mul_of_nonneg_left h1 ha).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_left h1 ha),
      (by nlinarith : a * x ≤ 0).trans (le_max_left _ _)⟩

lemma mulVec_apply_eq (R : Matrix κ ι ℝ) (x : ι → ℝ) (i : κ) :
    (R *ᵥ x) i = ∑ j, R i j * x j := by
  simp [Matrix.mulVec, dotProduct]

/-- The projection of every point of the box lies between `lo` and `hi`. -/
lemma lo_le_mulVec_le_hi (R : Matrix κ ι ℝ) (q x : ι → ℝ) (hx : x ∈ Set.Icc 0 q) (i : κ) :
    lo R q i ≤ (R *ᵥ x) i ∧ (R *ᵥ x) i ≤ hi R q i := by
  rw [mulVec_apply_eq]
  exact ⟨Finset.sum_le_sum fun j _ => (term_bounds _ _ _ (hx.1 j) (hx.2 j)).1,
    Finset.sum_le_sum fun j _ => (term_bounds _ _ _ (hx.1 j) (hx.2 j)).2⟩

/-- The values `lo` and `hi` are attained at vertices of the box. -/
lemma exists_vertices (R : Matrix κ ι ℝ) (q : ι → ℝ) (hq : 0 ≤ q) (i : κ) :
    ∃ xp ∈ Set.Icc (0 : ι → ℝ) q, ∃ xm ∈ Set.Icc (0 : ι → ℝ) q,
      (R *ᵥ xp) i = hi R q i ∧ (R *ᵥ xm) i = lo R q i := by
  classical
  refine ⟨fun j => if 0 ≤ R i j then q j else 0, ⟨fun j => ?_, fun j => ?_⟩,
    fun j => if 0 ≤ R i j then 0 else q j, ⟨fun j => ?_, fun j => ?_⟩, ?_, ?_⟩
  · by_cases h : 0 ≤ R i j <;> simp [h, (show (0:ℝ) ≤ q j from hq j)]
  · by_cases h : 0 ≤ R i j <;> simp [h, (show (0:ℝ) ≤ q j from hq j)]
  · by_cases h : 0 ≤ R i j <;> simp [h, (show (0:ℝ) ≤ q j from hq j)]
  · by_cases h : 0 ≤ R i j <;> simp [h, (show (0:ℝ) ≤ q j from hq j)]
  · rw [mulVec_apply_eq, hi]
    refine Finset.sum_congr rfl fun j _ => ?_
    have := (show (0:ℝ) ≤ q j from hq j)
    by_cases h : 0 ≤ R i j
    · simp only [h, ite_true]; rw [max_eq_right (mul_nonneg h this)]
    · simp only [h, ite_false, mul_zero]
      rw [max_eq_left (by nlinarith)]
  · rw [mulVec_apply_eq, lo]
    refine Finset.sum_congr rfl fun j _ => ?_
    have := (show (0:ℝ) ≤ q j from hq j)
    by_cases h : 0 ≤ R i j
    · simp only [h, ite_true, mul_zero]; rw [min_eq_left (mul_nonneg h this)]
    · simp only [h, ite_false]
      rw [min_eq_right (by nlinarith)]

/-- **Basic reduction** (for an arbitrary real matrix `R`, any finite dimensions):
some translate of `R • [0,q]` lies in `[0,p]` ⇔ `∑ⱼ qⱼ|Rᵢⱼ| ≤ pᵢ` for all `i`. -/
theorem exists_translate_mem_box_iff [Fintype κ] (R : Matrix κ ι ℝ) (q : ι → ℝ) (p : κ → ℝ)
    (hq : 0 ≤ q) :
    (∃ t : κ → ℝ, ∀ x ∈ Set.Icc (0 : ι → ℝ) q, R *ᵥ x + t ∈ Set.Icc (0 : κ → ℝ) p) ↔
      ∀ i, ∑ j, q j * |R i j| ≤ p i := by
  constructor
  · rintro ⟨t, ht⟩ i
    obtain ⟨xp, hxp, xm, hxm, ep, em⟩ := exists_vertices R q hq i
    have h1 := (ht xp hxp).2 i
    have h2 := (ht xm hxm).1 i
    simp only [Pi.add_apply, Pi.zero_apply, ep, em] at h1 h2
    rw [← hi_sub_lo R q hq i]
    linarith
  · intro h
    refine ⟨fun i => -lo R q i, fun x hx => ⟨fun i => ?_, fun i => ?_⟩⟩
    · have := (lo_le_mulVec_le_hi R q x hx i).1
      simp only [Pi.add_apply, Pi.zero_apply]
      linarith
    · have := (lo_le_mulVec_le_hi R q x hx i).2
      have h' := h i
      rw [← hi_sub_lo R q hq i] at h'
      simp only [Pi.add_apply]
      linarith

end Boxes
