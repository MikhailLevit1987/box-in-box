import Boxes.ZeroEntry
import Boxes.Descent

/-!
# Necessity: reduction to Theorem Z, and the main theorem

* `F(R) = maxᵢ wᵢ(R)/pᵢ` (`Fmax`) is continuous on the compact set `O(3)` and attains its minimum.
* `descent` (Theorem Z): for `q > 0`, at a point where all `Rᵢⱼ ≠ 0`, the value of `F` can be
  decreased. Hence a minimum point has a zero entry.
* The case `q ≥ 0` (plate, rod) is a limit argument without sequences: the continuous function
  `φ(R) = maxᵢ (wᵢ(R) − pᵢ)` would have a positive minimum on the compact set of orthogonal
  matrices with a zero entry.
-/

namespace Boxes

open Matrix

/-- The width of the rotated box along axis `i`. -/
def width (q : Fin 3 → ℝ) (R : Matrix (Fin 3) (Fin 3) ℝ) (i : Fin 3) : ℝ := ∑ j, q j * |R i j|

/-- `F(R) = maxᵢ wᵢ(R)/pᵢ`. -/
noncomputable def Fmax (p q : Fin 3 → ℝ) (R : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  max (max (width q R 0 / p 0) (width q R 1 / p 1)) (width q R 2 / p 2)

lemma le_Fmax (p q : Fin 3 → ℝ) (R : Matrix (Fin 3) (Fin 3) ℝ) (i : Fin 3) :
    width q R i / p i ≤ Fmax p q R := by
  unfold Fmax
  fin_cases i
  · exact le_trans (le_max_left _ _) (le_max_left _ _)
  · exact le_trans (le_max_right _ _) (le_max_left _ _)
  · exact le_max_right _ _

lemma Fmax_le_iff {p q : Fin 3 → ℝ} {R : Matrix (Fin 3) (Fin 3) ℝ} {c : ℝ} :
    Fmax p q R ≤ c ↔ ∀ i, width q R i / p i ≤ c := by
  refine ⟨fun h i => le_trans (le_Fmax p q R i) h, fun h => ?_⟩
  unfold Fmax
  exact max_le (max_le (h 0) (h 1)) (h 2)

lemma Fmax_lt_iff {p q : Fin 3 → ℝ} {R : Matrix (Fin 3) (Fin 3) ℝ} {c : ℝ} :
    Fmax p q R < c ↔ ∀ i, width q R i / p i < c := by
  refine ⟨fun h i => lt_of_le_of_lt (le_Fmax p q R i) h, fun h => ?_⟩
  unfold Fmax
  exact max_lt (max_lt (h 0) (h 1)) (h 2)

lemma continuous_width (q : Fin 3 → ℝ) (i : Fin 3) :
    Continuous fun R : Matrix (Fin 3) (Fin 3) ℝ => width q R i := by
  unfold width
  fun_prop

lemma continuous_Fmax (p q : Fin 3 → ℝ) : Continuous (Fmax p q) := by
  unfold Fmax
  have := continuous_width q
  fun_prop

lemma abs_le_one_of_orth {R : Matrix (Fin 3) (Fin 3) ℝ} (hR : R ∈ orthogonalGroup (Fin 3) ℝ)
    (i j : Fin 3) : |R i j| ≤ 1 := by
  have := congrFun (congrFun ((mem_orthogonalGroup_iff (Fin 3) ℝ).1 hR) i) i
  simp [Matrix.mul_apply, Fin.sum_univ_three] at this
  rw [abs_le_one_iff_mul_self_le_one]
  fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
    nlinarith [mul_self_nonneg (R i 0), mul_self_nonneg (R i 1), mul_self_nonneg (R i 2)]

lemma isCompact_orth : IsCompact (orthogonalGroup (Fin 3) ℝ : Set (Matrix (Fin 3) (Fin 3) ℝ)) := by
  have hcl : IsClosed (orthogonalGroup (Fin 3) ℝ : Set (Matrix (Fin 3) (Fin 3) ℝ)) := by
    have : (orthogonalGroup (Fin 3) ℝ : Set (Matrix (Fin 3) (Fin 3) ℝ)) = {A | A * Aᵀ = 1} := by
      ext A
      exact mem_orthogonalGroup_iff (Fin 3) ℝ
    rw [this]
    exact isClosed_eq (continuous_id.matrix_mul continuous_id.matrix_transpose) continuous_const
  refine IsCompact.of_isClosed_subset
    (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc (a := (-1 : ℝ)) (b := 1))
    hcl ?_
  intro R hR i _ j _
  exact abs_le.1 (abs_le_one_of_orth hR i j)

/-- **Theorem Z** (descent form): for `q > 0`, `F` is not minimal at a point where all `Rᵢⱼ ≠ 0`. -/
theorem descent (p q : Fin 3 → ℝ) (hp : ∀ i, 0 < p i) (hq : ∀ j, 0 < q j)
    (R : Matrix (Fin 3) (Fin 3) ℝ) (hR : R ∈ orthogonalGroup (Fin 3) ℝ) (hnz : ∀ i j, R i j ≠ 0) :
    ∃ R' ∈ orthogonalGroup (Fin 3) ℝ, Fmax p q R' < Fmax p q R := by
  obtain ⟨R', hR', hlt⟩ := core hR hnz hq
  exact ⟨R', hR', Fmax_lt_iff.2 fun i =>
    lt_of_lt_of_le (div_lt_div_of_pos_right (hlt i) (hp i)) (le_Fmax p q R i)⟩

/-- For `q > 0`: if the box fits, it also fits in a position with a zero entry. -/
lemma exists_zero_pos (p q : Fin 3 → ℝ) (hp : ∀ i, 0 < p i) (hq : ∀ j, 0 < q j)
    (h : ∃ R ∈ orthogonalGroup (Fin 3) ℝ, ∀ i, width q R i ≤ p i) :
    ∃ R ∈ orthogonalGroup (Fin 3) ℝ, (∀ i, width q R i ≤ p i) ∧ ∃ i j, R i j = 0 := by
  obtain ⟨R0, hR0, hw0⟩ := h
  obtain ⟨R, hR, hmin⟩ :=
    isCompact_orth.exists_isMinOn ⟨R0, hR0⟩ (continuous_Fmax p q).continuousOn
  have hF : Fmax p q R ≤ 1 :=
    le_trans (isMinOn_iff.1 hmin R0 hR0) (Fmax_le_iff.2 fun i => (div_le_one (hp i)).2 (hw0 i))
  refine ⟨R, hR, fun i => (div_le_one (hp i)).1 (Fmax_le_iff.1 hF i), ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨R', hR', hlt⟩ := descent p q hp hq R hR hcon
  exact absurd (isMinOn_iff.1 hmin R' hR') (not_le.2 hlt)

lemma width_add (q : Fin 3 → ℝ) (δ : ℝ) (R : Matrix (Fin 3) (Fin 3) ℝ) (i : Fin 3) :
    width (fun j => q j + δ) R i = width q R i + δ * ∑ j, |R i j| := by
  simp [width, add_mul, Finset.sum_add_distrib, Finset.mul_sum]

lemma sum_abs_le_three {R : Matrix (Fin 3) (Fin 3) ℝ} (hR : R ∈ orthogonalGroup (Fin 3) ℝ)
    (i : Fin 3) : ∑ j, |R i j| ≤ 3 := by
  rw [Fin.sum_univ_three]
  linarith [abs_le_one_of_orth hR i 0, abs_le_one_of_orth hR i 1, abs_le_one_of_orth hR i 2]

/-- For `q ≥ 0`: if the box fits, it also fits in a position with a zero entry. -/
lemma exists_zero (p q : Fin 3 → ℝ) (hp : ∀ i, 0 < p i) (hq : ∀ j, 0 ≤ q j)
    (h : ∃ R ∈ orthogonalGroup (Fin 3) ℝ, ∀ i, width q R i ≤ p i) :
    ∃ R ∈ orthogonalGroup (Fin 3) ℝ, (∀ i, width q R i ≤ p i) ∧ ∃ i j, R i j = 0 := by
  by_contra hcon
  obtain ⟨R0, hR0, hw0⟩ := h
  -- the compact set of orthogonal matrices with a zero entry
  set Z : Set (Matrix (Fin 3) (Fin 3) ℝ) :=
    (orthogonalGroup (Fin 3) ℝ : Set (Matrix (Fin 3) (Fin 3) ℝ)) ∩ {R | ∏ i, ∏ j, R i j = 0} with hZ
  have hZc : IsCompact Z :=
    isCompact_orth.inter_right (isClosed_eq (by fun_prop) continuous_const)
  have hmemZ : ∀ R ∈ Z, R ∈ orthogonalGroup (Fin 3) ℝ ∧ ∃ i j, R i j = 0 := by
    rintro R ⟨hR, hR0⟩
    simp only [Set.mem_ofPred_eq, Finset.prod_eq_zero_iff, Finset.mem_univ, true_and] at hR0
    obtain ⟨i, j, h⟩ := hR0
    exact ⟨hR, i, j, h⟩
  have h1Z : (1 : Matrix (Fin 3) (Fin 3) ℝ) ∈ Z := by
    refine ⟨one_mem _, ?_⟩
    simp only [Set.mem_ofPred_eq, Finset.prod_eq_zero_iff, Finset.mem_univ, true_and]
    exact ⟨0, 1, by simp⟩
  set φ : Matrix (Fin 3) (Fin 3) ℝ → ℝ := fun R =>
    max (max (width q R 0 - p 0) (width q R 1 - p 1)) (width q R 2 - p 2) with hφ
  have hφc : Continuous φ := by
    have := continuous_width q
    fun_prop
  have hφpos : ∀ R ∈ Z, 0 < φ R := by
    intro R hRZ
    obtain ⟨hR, i, j, h0⟩ := hmemZ R hRZ
    by_contra hle
    push Not at hle
    have hw : ∀ i, width q R i ≤ p i := by
      intro i
      have : width q R i - p i ≤ φ R := by
        simp only [hφ]
        fin_cases i
        · exact le_trans (le_max_left _ _) (le_max_left _ _)
        · exact le_trans (le_max_right _ _) (le_max_left _ _)
        · exact le_max_right _ _
      linarith
    exact hcon ⟨R, hR, hw, i, j, h0⟩
  obtain ⟨Rm, hRm, hmin⟩ := hZc.exists_isMinOn ⟨1, h1Z⟩ hφc.continuousOn
  set m := φ Rm
  have hm : 0 < m := hφpos Rm hRm
  -- shift `q ↦ q + δ`, `p ↦ p + 3δ` with `3δ < m`
  set δ := m / 6 with hδ
  have hδ0 : 0 < δ := by positivity
  obtain ⟨R1, hR1, hw1, i1, j1, h01⟩ := exists_zero_pos (fun i => p i + 3 * δ) (fun j => q j + δ)
    (fun i => by linarith [hp i]) (fun j => by linarith [hq j])
    ⟨R0, hR0, fun i => by
      rw [width_add]
      nlinarith [hw0 i, sum_abs_le_three hR0 i]⟩
  have hR1Z : R1 ∈ Z := by
    refine ⟨hR1, ?_⟩
    simp only [Set.mem_ofPred_eq, Finset.prod_eq_zero_iff, Finset.mem_univ, true_and]
    exact ⟨i1, j1, h01⟩
  have hle : ∀ i, width q R1 i - p i ≤ 3 * δ := by
    intro i
    have := hw1 i
    rw [width_add] at this
    have h0 : 0 ≤ δ * ∑ j, |R1 i j| :=
      mul_nonneg hδ0.le (Finset.sum_nonneg fun j _ => abs_nonneg _)
    linarith
  have hφ1 : φ R1 ≤ 3 * δ := by
    simp only [hφ]
    exact max_le (max_le (hle 0) (hle 1)) (hle 2)
  have := isMinOn_iff.1 hmin R1 hR1Z
  linarith

/-- **Necessity.** -/
theorem NC_of_fits (p q : Fin 3 → ℝ) (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 ≤ q i) :
    Fits p q → NC p q := by
  intro h
  rw [fits_iff_widths p q hq] at h
  obtain ⟨R, hR, hw, i, j, h0⟩ := exists_zero p q hp hq h
  exact NC_of_zero p q hp hq R hR hw i j h0

/-- **Main theorem.** -/
theorem fits_iff_NC (p q : Fin 3 → ℝ) (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 ≤ q i) :
    Fits p q ↔ NC p q :=
  ⟨NC_of_fits p q hp hq, fits_of_NC p q hp hq⟩

end Boxes
