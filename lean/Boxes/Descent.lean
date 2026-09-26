import Boxes.Motzkin

/-!
# Descent (Theorem Z): at a rotation without zero entries all three widths can be decreased

Notation (for an orthogonal `R` without zero entries and `q > 0`):
* `sgn R i j = ±1` — the sign of `Rᵢⱼ`;
* `avec R q i` — the vector `aᵢ = R gᵢ`, `gᵢ = (sgn Rᵢⱼ · qⱼ)ⱼ`; its `i`-th component is the width `wᵢ`;
* `bvec a i = a × eᵢ`, so that `(v × a)ᵢ = bvec a i · v` (linear part of the width increment);
* `Pq a i v = vᵢ (v·a) − |v|² aᵢ` (quadratic part).

Main steps:
* `key_neg` — under the "symmetry" `∑ νᵢ bᵢ = 0` with two positive `νᵢ` the form `∑ νᵢ Pᵢ(h)` is
  negative for `h ≠ 0` (estimates (B1)–(B2));
* `cay` — the Cayley rotation, `cay_mulVec` — the exact width increment;
* `choose_hz` — the choice of a descent curve via Motzkin's alternative;
* `core` — all three widths decrease simultaneously.
-/

namespace Boxes

open Matrix Topology Filter

/-- The sign of a matrix entry (`±1`). -/
noncomputable def sgn (R : Matrix (Fin 3) (Fin 3) ℝ) (i j : Fin 3) : ℝ := if 0 < R i j then 1 else -1

/-- `aᵢ = R gᵢ`, `gᵢⱼ = sgn Rᵢⱼ · qⱼ`. -/
noncomputable def avec (R : Matrix (Fin 3) (Fin 3) ℝ) (q : Fin 3 → ℝ) (i : Fin 3) : Fin 3 → ℝ :=
  fun k => ∑ j, R k j * (sgn R i j * q j)

/-- `a × eᵢ`. -/
def bvec (a : Fin 3 → ℝ) : Fin 3 → Fin 3 → ℝ
  | 0 => ![0, a 2, -a 1]
  | 1 => ![-a 2, 0, a 0]
  | 2 => ![a 1, -a 0, 0]

/-- Quadratic part of the width increment. -/
def Pq (a : Fin 3 → ℝ) (i : Fin 3) (v : Fin 3 → ℝ) : ℝ := v i * (v ⬝ᵥ a) - (v ⬝ᵥ v) * a i

lemma sgn_sq (R : Matrix (Fin 3) (Fin 3) ℝ) (i j : Fin 3) : sgn R i j * sgn R i j = 1 := by
  unfold sgn; split_ifs <;> norm_num

lemma sgn_mul_self {R : Matrix (Fin 3) (Fin 3) ℝ} {i j : Fin 3} (h : R i j ≠ 0) :
    sgn R i j * R i j = |R i j| := by
  unfold sgn
  split_ifs with hp
  · rw [one_mul, abs_of_pos hp]
  · rw [abs_of_neg (lt_of_le_of_ne (not_lt.1 hp) h)]; ring

lemma sgn_mul_le_abs (R : Matrix (Fin 3) (Fin 3) ℝ) (i j : Fin 3) (x : ℝ) :
    sgn R i j * x ≤ |x| ∧ -(sgn R i j * x) ≤ |x| := by
  unfold sgn
  split_ifs
  · simp [le_abs_self, neg_le_abs]
  · simp [le_abs_self, neg_le_abs]

/-- The width via `avec`: `wᵢ = (aᵢ)ᵢ`. -/
lemma avec_self {R : Matrix (Fin 3) (Fin 3) ℝ} (hnz : ∀ i j, R i j ≠ 0) (q : Fin 3 → ℝ) (i : Fin 3) :
    avec R q i i = ∑ j, q j * |R i j| := by
  unfold avec
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← sgn_mul_self (hnz i j)]; ring

/-- Rows of an orthogonal matrix are orthogonal. -/
lemma row_orth {R : Matrix (Fin 3) (Fin 3) ℝ} (hR : R ∈ orthogonalGroup (Fin 3) ℝ) {i k : Fin 3}
    (hik : i ≠ k) : ∑ j, R i j * R k j = 0 := by
  have := congrFun (congrFun ((mem_orthogonalGroup_iff (Fin 3) ℝ).1 hR) i) k
  simpa [Matrix.mul_apply, Matrix.one_apply_ne hik] using this

/-- **(B1)** `|(aᵢ)ₖ| < wₖ` for `i ≠ k`. -/
lemma B1 {R : Matrix (Fin 3) (Fin 3) ℝ} (hR : R ∈ orthogonalGroup (Fin 3) ℝ) (hnz : ∀ i j, R i j ≠ 0)
    {q : Fin 3 → ℝ} (hq : ∀ j, 0 < q j) {i k : Fin 3} (hik : i ≠ k) :
    |avec R q i k| < avec R q k k := by
  rw [avec_self hnz]
  have hrow := row_orth hR hik
  have hpos : ∀ j, 0 < R i j * R k j ∨ R i j * R k j < 0 := fun j =>
    lt_or_gt_of_ne (mul_ne_zero (hnz i j) (hnz k j)).symm |>.imp id id
  -- `Rᵢⱼ Rₖⱼ = |Rᵢⱼ| · (sgn Rᵢⱼ · Rₖⱼ)`
  have hprod : ∀ j, R i j * R k j = |R i j| * (sgn R i j * R k j) := by
    intro j
    rw [← sgn_mul_self (hnz i j)]
    linear_combination (R i j * R k j) * (sgn_sq R i j).symm
  have habs : ∀ j, 0 < |R i j| := fun j => abs_pos.2 (hnz i j)
  have e : ∀ j, R k j * (sgn R i j * q j) = q j * (sgn R i j * R k j) := fun j => by ring
  unfold avec
  rw [abs_lt]
  constructor
  · -- `−wₖ < (aᵢ)ₖ`
    by_contra hcon
    push Not at hcon
    have hle : ∀ j, q j * (-(sgn R i j * R k j)) ≤ q j * |R k j| := fun j =>
      mul_le_mul_of_nonneg_left (sgn_mul_le_abs R i j _).2 (hq j).le
    have heq : ∀ j, -(sgn R i j * R k j) = |R k j| := by
      intro j
      simp only [Fin.sum_univ_three, e] at hcon
      have h0 := hle 0; have h1 := hle 1; have h2 := hle 2
      have : q j * (-(sgn R i j * R k j)) = q j * |R k j| := by
        refine le_antisymm (hle j) ?_
        rcases (show j = 0 ∨ j = 1 ∨ j = 2 by fin_cases j <;> simp) with rfl | rfl | rfl <;> linarith
      exact mul_left_cancel₀ (hq j).ne' this
    have hneg : ∀ j, R i j * R k j < 0 := by
      intro j
      rw [hprod j]
      have : sgn R i j * R k j = -|R k j| := by linarith [heq j]
      rw [this]
      nlinarith [habs j, abs_pos.2 (hnz k j)]
    rw [Fin.sum_univ_three] at hrow
    linarith [hneg 0, hneg 1, hneg 2]
  · -- `(aᵢ)ₖ < wₖ`
    by_contra hcon
    push Not at hcon
    have hle : ∀ j, q j * (sgn R i j * R k j) ≤ q j * |R k j| := fun j =>
      mul_le_mul_of_nonneg_left (sgn_mul_le_abs R i j _).1 (hq j).le
    have heq : ∀ j, sgn R i j * R k j = |R k j| := by
      intro j
      simp only [Fin.sum_univ_three, e] at hcon
      have h0 := hle 0; have h1 := hle 1; have h2 := hle 2
      have : q j * (sgn R i j * R k j) = q j * |R k j| := by
        refine le_antisymm (hle j) ?_
        rcases (show j = 0 ∨ j = 1 ∨ j = 2 by fin_cases j <;> simp) with rfl | rfl | rfl <;> linarith
      exact mul_left_cancel₀ (hq j).ne' this
    have hposj : ∀ j, 0 < R i j * R k j := by
      intro j
      rw [hprod j, heq j]
      exact mul_pos (habs j) (abs_pos.2 (hnz k j))
    rw [Fin.sum_univ_three] at hrow
    linarith [hposj 0, hposj 1, hposj 2]

/-! ### The quadratic form: brackets -/

/-- The bracket `dᵢ y² + dₖ x² − 2 m x y` is nonnegative when `m² ≤ dᵢ dₖ`. -/
lemma bracket_nonneg {di dk m x y : ℝ} (hdi : 0 ≤ di) (hdk : 0 ≤ dk) (hm : m ^ 2 ≤ di * dk) :
    0 ≤ di * y ^ 2 + dk * x ^ 2 - 2 * m * x * y := by
  rcases eq_or_lt_of_le hdi with h0 | hpos
  · subst h0
    have : m = 0 := by nlinarith [sq_nonneg m]
    subst this
    nlinarith [sq_nonneg x]
  · have key : di * (di * y ^ 2 + dk * x ^ 2 - 2 * m * x * y) =
        (di * y - m * x) ^ 2 + (di * dk - m ^ 2) * x ^ 2 := by ring
    have : 0 ≤ di * (di * y ^ 2 + dk * x ^ 2 - 2 * m * x * y) := by
      rw [key]; nlinarith [sq_nonneg (di * y - m * x), sq_nonneg x]
    exact nonneg_of_mul_nonneg_right (by linarith) hpos

/-- The bracket is positive if `dᵢ > 0` and `y ≠ 0`. -/
lemma bracket_pos {di dk m x y : ℝ} (hdi : 0 < di) (hdk : 0 ≤ dk) (hm : m ^ 2 ≤ di * dk)
    (hs : 0 < dk → m ^ 2 < di * dk) (hy : y ≠ 0) :
    0 < di * y ^ 2 + dk * x ^ 2 - 2 * m * x * y := by
  have key : di * (di * y ^ 2 + dk * x ^ 2 - 2 * m * x * y) =
      (di * y - m * x) ^ 2 + (di * dk - m ^ 2) * x ^ 2 := by ring
  rcases eq_or_lt_of_le hdk with h0 | hpos
  · subst h0
    have : m = 0 := by nlinarith [sq_nonneg m]
    subst this
    have := sq_pos_of_ne_zero hy
    nlinarith
  · have hs' := hs hpos
    by_cases hx : x = 0
    · subst hx
      have := sq_pos_of_ne_zero hy
      nlinarith
    · have : 0 < di * (di * y ^ 2 + dk * x ^ 2 - 2 * m * x * y) := by
        rw [key]
        have := sq_pos_of_ne_zero hx
        nlinarith [sq_nonneg (di * y - m * x)]
      exact pos_of_mul_pos_right this hdi.le

/-- The bracket is positive if `dᵢ > 0, y ≠ 0` or `dₖ > 0, x ≠ 0`. -/
lemma bracket_pos2 {di dk m x y : ℝ} (hdi : 0 ≤ di) (hdk : 0 ≤ dk) (hm : m ^ 2 ≤ di * dk)
    (hs : 0 < di → 0 < dk → m ^ 2 < di * dk) (h : (0 < di ∧ y ≠ 0) ∨ (0 < dk ∧ x ≠ 0)) :
    0 < di * y ^ 2 + dk * x ^ 2 - 2 * m * x * y := by
  rcases h with ⟨hd, hy⟩ | ⟨hd, hx⟩
  · exact bracket_pos hd hdk hm (hs hd) hy
  · have := bracket_pos (di := dk) (dk := di) (m := m) (x := y) (y := x) hd hdi (by linarith)
      (fun h' => by have := hs h' hd; linarith) hx
    linarith

/-- **(B2)** `mᵢₖ² ≤ dᵢ dₖ` (`mᵢₖ = νᵢ Aᵢₖ = νₖ Aₖᵢ`, `dᵢ = νᵢ Aᵢᵢ`), strictly if `νᵢ, νₖ > 0`. -/
lemma m_bound {νi νk Aik Aki Aii Akk : ℝ} (hi : 0 ≤ νi) (hk : 0 ≤ νk)
    (h1 : |Aik| < Akk) (h2 : |Aki| < Aii) (hs : νi * Aik = νk * Aki) :
    (νi * Aik) ^ 2 ≤ (νi * Aii) * (νk * Akk) ∧
      (0 < νi → 0 < νk → (νi * Aik) ^ 2 < (νi * Aii) * (νk * Akk)) := by
  have e : (νi * Aik) ^ 2 = (νi * νk) * (Aik * Aki) := by
    calc (νi * Aik) ^ 2 = (νi * Aik) * (νk * Aki) := by rw [sq, ← hs]
      _ = _ := by ring
  have e2 : (νi * Aii) * (νk * Akk) = (νi * νk) * (Akk * Aii) := by ring
  have hlt : Aik * Aki < Akk * Aii := by
    calc Aik * Aki ≤ |Aik| * |Aki| := by rw [← abs_mul]; exact le_abs_self _
      _ < Akk * Aii := mul_lt_mul'' h1 h2 (abs_nonneg _) (abs_nonneg _)
  rw [e, e2]
  exact ⟨mul_le_mul_of_nonneg_left hlt.le (mul_nonneg hi hk),
    fun hi' hk' => mul_lt_mul_of_pos_left hlt (mul_pos hi' hk')⟩

/-- If two of the `νᵢ` are positive, then for every `c` there is `i ≠ c` with `νᵢ > 0`. -/
lemma two_pos {ν : Fin 3 → ℝ} (h : ∃ a b, a ≠ b ∧ 0 < ν a ∧ 0 < ν b) (c : Fin 3) :
    ∃ i, i ≠ c ∧ 0 < ν i := by
  obtain ⟨a, b, hab, ha, hb⟩ := h
  by_cases hac : a = c
  · exact ⟨b, fun hbc => hab (hac.trans hbc.symm), hb⟩
  · exact ⟨a, hac, ha⟩

/-- The algebraic core of `key_neg` for an arbitrary family `a` satisfying (B1). -/
theorem key_core (a : Fin 3 → Fin 3 → ℝ) (ν h : Fin 3 → ℝ) (hν : ∀ i, 0 ≤ ν i)
    (hB : ∀ i k, i ≠ k → |a i k| < a k k) (hsym : ∑ i, ν i • bvec (a i) i = 0)
    (htwo : ∀ c, ∃ i, i ≠ c ∧ 0 < ν i) (hh : h ≠ 0) :
    ∑ i, ν i * Pq (a i) i h < 0 := by
  -- symmetry `νᵢ Aᵢₖ = νₖ Aₖᵢ`
  have s0 : ν 1 * a 1 2 = ν 2 * a 2 1 := by
    have := congrFun hsym 0
    simp [Fin.sum_univ_three, bvec] at this
    linarith
  have s1 : ν 0 * a 0 2 = ν 2 * a 2 0 := by
    have := congrFun hsym 1
    simp [Fin.sum_univ_three, bvec] at this
    linarith
  have s2 : ν 0 * a 0 1 = ν 1 * a 1 0 := by
    have := congrFun hsym 2
    simp [Fin.sum_univ_three, bvec] at this
    linarith
  have hA : ∀ k, 0 < a k k := fun k => by
    obtain ⟨i, hik⟩ : ∃ i, i ≠ k := ⟨k + 1, by fin_cases k <;> decide⟩
    exact lt_of_le_of_lt (abs_nonneg _) (hB i k hik)
  have hd : ∀ k, 0 ≤ ν k * a k k := fun k => mul_nonneg (hν k) (hA k).le
  have hνpos : ∀ k, 0 < ν k * a k k → 0 < ν k := fun k hk => by
    rcases (hν k).lt_or_eq with h' | h'
    · exact h'
    · rw [← h', zero_mul] at hk; exact absurd hk (lt_irrefl 0)
  have hdpos : ∀ k, 0 < ν k → 0 < ν k * a k k := fun k hk => mul_pos hk (hA k)
  have b01 := m_bound (hν 0) (hν 1) (hB 0 1 (by decide)) (hB 1 0 (by decide)) s2
  have b02 := m_bound (hν 0) (hν 2) (hB 0 2 (by decide)) (hB 2 0 (by decide)) s1
  have b12 := m_bound (hν 1) (hν 2) (hB 1 2 (by decide)) (hB 2 1 (by decide)) s0
  -- `∑ νᵢ Pᵢ(h) = −(B₀₁ + B₀₂ + B₁₂)`
  have hsum : ∑ i, ν i * Pq (a i) i h =
      -((ν 0 * a 0 0 * h 1 ^ 2 + ν 1 * a 1 1 * h 0 ^ 2 - 2 * (ν 0 * a 0 1) * h 0 * h 1) +
        (ν 0 * a 0 0 * h 2 ^ 2 + ν 2 * a 2 2 * h 0 ^ 2 - 2 * (ν 0 * a 0 2) * h 0 * h 2) +
        (ν 1 * a 1 1 * h 2 ^ 2 + ν 2 * a 2 2 * h 1 ^ 2 - 2 * (ν 1 * a 1 2) * h 1 * h 2)) := by
    simp only [Fin.sum_univ_three, Pq, dotProduct]
    linear_combination (-(h 0 * h 1)) * s2 + (-(h 0 * h 2)) * s1 + (-(h 1 * h 2)) * s0
  have n01 := bracket_nonneg (x := h 0) (y := h 1) (hd 0) (hd 1) b01.1
  have n02 := bracket_nonneg (x := h 0) (y := h 2) (hd 0) (hd 2) b02.1
  have n12 := bracket_nonneg (x := h 1) (y := h 2) (hd 1) (hd 2) b12.1
  have P01 := bracket_pos2 (x := h 0) (y := h 1) (hd 0) (hd 1) b01.1
    (fun x y => b01.2 (hνpos 0 x) (hνpos 1 y))
  have P02 := bracket_pos2 (x := h 0) (y := h 2) (hd 0) (hd 2) b02.1
    (fun x y => b02.2 (hνpos 0 x) (hνpos 2 y))
  have P12 := bracket_pos2 (x := h 1) (y := h 2) (hd 1) (hd 2) b12.1
    (fun x y => b12.2 (hνpos 1 x) (hνpos 2 y))
  rw [hsum]
  obtain ⟨c, hc⟩ : ∃ c, h c ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hh (funext hc)
  obtain ⟨i, hic, hi⟩ := htwo c
  have hdi := hdpos i hi
  rcases (show c = 0 ∨ c = 1 ∨ c = 2 by fin_cases c <;> simp) with rfl | rfl | rfl <;>
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 by fin_cases i <;> simp) with rfl | rfl | rfl <;>
  first
  | exact absurd rfl hic
  | linarith [P01 (Or.inl ⟨hdi, hc⟩)]
  | linarith [P01 (Or.inr ⟨hdi, hc⟩)]
  | linarith [P02 (Or.inl ⟨hdi, hc⟩)]
  | linarith [P02 (Or.inr ⟨hdi, hc⟩)]
  | linarith [P12 (Or.inl ⟨hdi, hc⟩)]
  | linarith [P12 (Or.inr ⟨hdi, hc⟩)]

/-- **`key_neg`**: if `∑ νᵢ bvec(aᵢ) i = 0` and two of the `νᵢ` are positive, then the form
`∑ νᵢ Pᵢ(h)` is negative for `h ≠ 0`. -/
theorem key_neg {R : Matrix (Fin 3) (Fin 3) ℝ} (hR : R ∈ orthogonalGroup (Fin 3) ℝ)
    (hnz : ∀ i j, R i j ≠ 0) {q : Fin 3 → ℝ} (hq : ∀ j, 0 < q j) (ν h : Fin 3 → ℝ)
    (hν : ∀ i, 0 ≤ ν i) (hsym : ∑ i, ν i • bvec (avec R q i) i = 0)
    (htwo : ∃ a b, a ≠ b ∧ 0 < ν a ∧ 0 < ν b) (hh : h ≠ 0) :
    ∑ i, ν i * Pq (avec R q i) i h < 0 :=
  key_core (fun i => avec R q i) ν h hν (fun _ _ hik => B1 hR hnz hq hik) hsym (two_pos htwo) hh

/-! ### The Cayley rotation and the width increment -/

/-- `|v|²`, written explicitly (convenient for `fun_prop`/`positivity`). -/
def nrm (v : Fin 3 → ℝ) : ℝ := v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2

/-- `(1 − |v|²) I + 2 [v]× + 2 v vᵀ` (the rotation of the quaternion `(1, v)`, unnormalized). -/
def cayN (v : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1 - nrm v + 2 * v 0 ^ 2, 2 * v 0 * v 1 - 2 * v 2, 2 * v 0 * v 2 + 2 * v 1;
     2 * v 1 * v 0 + 2 * v 2, 1 - nrm v + 2 * v 1 ^ 2, 2 * v 1 * v 2 - 2 * v 0;
     2 * v 2 * v 0 - 2 * v 1, 2 * v 2 * v 1 + 2 * v 0, 1 - nrm v + 2 * v 2 ^ 2]

/-- The Cayley rotation. -/
noncomputable def cay (v : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ := (1 + nrm v)⁻¹ • cayN v

lemma one_add_nrm_pos (v : Fin 3 → ℝ) : 0 < 1 + nrm v := by unfold nrm; positivity

lemma cay_mem (v : Fin 3 → ℝ) : cay v ∈ orthogonalGroup (Fin 3) ℝ := by
  refine (mem_orthogonalGroup_iff (Fin 3) ℝ).2 ?_
  show cay v * (cay v)ᵀ = 1
  have hs := (one_add_nrm_pos v).ne'
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cay, cayN, Matrix.mul_apply, Fin.sum_univ_three] <;> field_simp <;> unfold nrm <;> ring

lemma cay_zero : cay 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cay, cayN, nrm]

lemma continuous_cay : Continuous cay := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  fin_cases i <;> fin_cases j <;> simp only [cay, cayN, nrm] <;> simp <;>
    exact Continuous.mul (Continuous.inv₀ (by fun_prop) fun x => by positivity) (by fun_prop)

/-- Linear plus quadratic part of the width increment. -/
def Dq (a : Fin 3 → ℝ) (i : Fin 3) (v : Fin 3 → ℝ) : ℝ := bvec a i ⬝ᵥ v + Pq a i v

/-- `(cay v · a)ᵢ − aᵢ = 2 (1+|v|²)⁻¹ Dᵢ(v)`. -/
lemma cay_mulVec (v a : Fin 3 → ℝ) (i : Fin 3) :
    (cay v *ᵥ a) i - a i = 2 * (1 + nrm v)⁻¹ * Dq a i v := by
  have hs := (one_add_nrm_pos v).ne'
  fin_cases i <;>
    simp [cay, cayN, Dq, bvec, Pq, mulVec, dotProduct, Fin.sum_univ_three] <;>
    field_simp <;> unfold nrm <;> ring

/-- If `0 < Rᵢⱼ x`, then `|x| = sgn(Rᵢⱼ) x`. -/
lemma abs_eq_sgn_mul {R : Matrix (Fin 3) (Fin 3) ℝ} {i j : Fin 3} {x : ℝ} (h : 0 < R i j * x) :
    |x| = sgn R i j * x := by
  unfold sgn
  split_ifs with hp
  · have : 0 < x := by
      by_contra hx; push Not at hx; nlinarith
    rw [one_mul, abs_of_pos this]
  · have : x < 0 := by
      by_contra hx; push Not at hx; push Not at hp; nlinarith
    rw [abs_of_neg this]; ring

/-- If `C R` has the same sign pattern as `R`, then the width of `C R` equals `(C aᵢ)ᵢ`. -/
lemma width_mul {C R : Matrix (Fin 3) (Fin 3) ℝ} (hs : ∀ i j, 0 < R i j * (C * R) i j)
    (q : Fin 3 → ℝ) (i : Fin 3) :
    ∑ j, q j * |(C * R) i j| = (C *ᵥ avec R q i) i := by
  simp only [abs_eq_sgn_mul (hs i _)]
  simp only [Matrix.mul_apply, mulVec, dotProduct, avec, Fin.sum_univ_three]
  ring

/-! ### Descent along the curve `t ↦ t (h + t z)` -/

lemma Pq_smul (a : Fin 3 → ℝ) (i : Fin 3) (t : ℝ) (u : Fin 3 → ℝ) :
    Pq a i (t • u) = t ^ 2 * Pq a i u := by
  simp only [Pq, dotProduct, Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul]
  ring

lemma dot_smul (b u : Fin 3 → ℝ) (t : ℝ) : b ⬝ᵥ (t • u) = t * (b ⬝ᵥ u) := by
  simp only [dotProduct, Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul]; ring

lemma dot_add_smul (b h z : Fin 3 → ℝ) (t : ℝ) : b ⬝ᵥ (h + t • z) = b ⬝ᵥ h + t * (b ⬝ᵥ z) := by
  simp only [dotProduct, Fin.sum_univ_three, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

lemma continuous_Pq_line (a : Fin 3 → ℝ) (i : Fin 3) (h z : Fin 3 → ℝ) :
    Continuous fun t : ℝ => Pq a i (h + t • z) := by
  simp only [Pq, dotProduct, Fin.sum_univ_three, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  fun_prop

/-- A continuous function negative at `0` is negative on a right neighbourhood of `0`. -/
lemma ev_of_cont {g : ℝ → ℝ} (hg : Continuous g) (h0 : g 0 < 0) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧ g t < 0 :=
  eventually_mem_nhdsWithin.and
    (nhdsWithin_le_nhds ((hg.tendsto 0).eventually (gt_mem_nhds h0)))

lemma ev_ne (x z : ℝ) (hz : z ≠ 0) : ∀ᶠ t in 𝓝[>] (0 : ℝ), x + t * z ≠ 0 := by
  by_cases hx : x = 0
  · subst hx
    filter_upwards [eventually_mem_nhdsWithin] with t ht
    rw [zero_add]
    exact mul_ne_zero (ne_of_gt ht) hz
  · have hc : Continuous fun t : ℝ => x + t * z := by fun_prop
    have := (hc.tendsto 0).eventually_ne (by simpa using hx)
    exact nhdsWithin_le_nhds this

/-- First/second order: `Dᵢ(t (h + t z)) < 0` for small `t > 0`. -/
lemma ev_neg {a : Fin 3 → ℝ} {i : Fin 3} {h z : Fin 3 → ℝ}
    (H : bvec a i ⬝ᵥ h < 0 ∨ (bvec a i ⬝ᵥ h = 0 ∧ bvec a i ⬝ᵥ z + Pq a i h < 0)) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), Dq a i (t • (h + t • z)) < 0 := by
  have hP := continuous_Pq_line a i h z
  have expand : ∀ t : ℝ, Dq a i (t • (h + t • z)) =
      t * (bvec a i ⬝ᵥ h + t * (bvec a i ⬝ᵥ z) + t * Pq a i (h + t • z)) := by
    intro t
    rw [Dq, dot_smul, dot_add_smul, Pq_smul]; ring
  rcases H with hA | ⟨hB0, hB⟩
  · have hg : Continuous fun t : ℝ =>
        bvec a i ⬝ᵥ h + t * (bvec a i ⬝ᵥ z) + t * Pq a i (h + t • z) := by fun_prop
    filter_upwards [ev_of_cont hg (by simpa using hA)] with t ⟨ht, hgt⟩
    rw [expand]
    exact mul_neg_of_pos_of_neg ht hgt
  · have hg : Continuous fun t : ℝ => bvec a i ⬝ᵥ z + Pq a i (h + t • z) := by fun_prop
    filter_upwards [ev_of_cont hg (by simpa using hB)] with t ⟨ht, hgt⟩
    have : Dq a i (t • (h + t • z)) = t ^ 2 * (bvec a i ⬝ᵥ z + Pq a i (h + t • z)) := by
      rw [expand, hB0]; ring
    rw [this]
    exact mul_neg_of_pos_of_neg (by positivity) hgt

/-- If `bvec a i = 0` (i.e. `a ∥ eᵢ`), then `Pᵢ(u) = −aᵢ Σ_{m≠i} u_m² < 0`. -/
lemma Pq_neg_of_b0 {a : Fin 3 → ℝ} {i : Fin 3} {u : Fin 3 → ℝ} (hb : bvec a i = 0) (ha : 0 < a i)
    (hu : ∀ m, u m ≠ 0) : Pq a i u < 0 := by
  have p0 := mul_self_pos.2 (hu 0)
  have p1 := mul_self_pos.2 (hu 1)
  have p2 := mul_self_pos.2 (hu 2)
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 by fin_cases i <;> simp) with rfl | rfl | rfl
  · have h1 : a 1 = 0 := by simpa [bvec] using congrFun hb 2
    have h2 : a 2 = 0 := by simpa [bvec] using congrFun hb 1
    simp only [Pq, dotProduct, Fin.sum_univ_three, h1, h2]
    nlinarith [mul_pos ha p1, mul_pos ha p2]
  · have h0 : a 0 = 0 := by simpa [bvec] using congrFun hb 2
    have h2 : a 2 = 0 := by simpa [bvec] using congrFun hb 0
    simp only [Pq, dotProduct, Fin.sum_univ_three, h0, h2]
    nlinarith [mul_pos ha p0, mul_pos ha p2]
  · have h0 : a 0 = 0 := by simpa [bvec] using congrFun hb 1
    have h1 : a 1 = 0 := by simpa [bvec] using congrFun hb 0
    simp only [Pq, dotProduct, Fin.sum_univ_three, h0, h1]
    nlinarith [mul_pos ha p0, mul_pos ha p1]

lemma ev_neg_Z {a : Fin 3 → ℝ} {i : Fin 3} {h z : Fin 3 → ℝ} (hb : bvec a i = 0) (ha : 0 < a i)
    (hz : ∀ m, z m ≠ 0) : ∀ᶠ t in 𝓝[>] (0 : ℝ), Dq a i (t • (h + t • z)) < 0 := by
  have hne : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ m, h m + t * z m ≠ 0 :=
    eventually_all.2 fun m => ev_ne (h m) (z m) (hz m)
  filter_upwards [hne, eventually_mem_nhdsWithin] with t ht htp
  have ht0 : (0 : ℝ) < t := htp
  have hP : Pq a i (h + t • z) < 0 :=
    Pq_neg_of_b0 hb ha fun m => by simpa using ht m
  rw [Dq, hb, zero_dotProduct, zero_add, Pq_smul]
  exact mul_neg_of_pos_of_neg (by positivity) hP

/-! ### Choice of the direction (theorem of the alternative) -/

lemma ev_lt (α β c : ℝ) (h : α < c) : ∀ᶠ δ in 𝓝[>] (0 : ℝ), α + δ * β < c := by
  have hc : Continuous fun δ : ℝ => α + δ * β - c := by fun_prop
  filter_upwards [ev_of_cont hc (by simpa using h)] with δ ⟨_, hδ⟩
  linarith

/-- Directions `h`, `z`: for every `i` with `bᵢ ≠ 0` the first or the second order term is negative. -/
lemma choose_hz {R : Matrix (Fin 3) (Fin 3) ℝ} (hR : R ∈ orthogonalGroup (Fin 3) ℝ)
    (hnz : ∀ i j, R i j ≠ 0) {q : Fin 3 → ℝ} (hq : ∀ j, 0 < q j) :
    ∃ h z : Fin 3 → ℝ, (∀ m, z m ≠ 0) ∧ ∀ i, bvec (avec R q i) i ≠ 0 →
      (bvec (avec R q i) i ⬝ᵥ h < 0 ∨
        (bvec (avec R q i) i ⬝ᵥ h = 0 ∧
          bvec (avec R q i) i ⬝ᵥ z + Pq (avec R q i) i h < 0)) := by
  classical
  obtain ⟨b, hbdef⟩ : ∃ b : Fin 3 → Fin 3 → ℝ, b = fun i => bvec (avec R q i) i := ⟨_, rfl⟩
  have hb : ∀ i, bvec (avec R q i) i = b i := fun i => by rw [hbdef]
  simp only [hb]
  let K : Finset (Fin 3) := Finset.univ.filter fun i => b i ≠ 0
  have hK : ∀ i, i ∈ K ↔ b i ≠ 0 := fun i => by simp [K]
  rcases motzkinS K b 0 with ⟨h, hh⟩ | ⟨μ, hμ0, hμK, ⟨i0, hi0⟩, hμb, -⟩
  · refine ⟨h, fun _ => 1, fun _ => one_ne_zero, fun i hi => Or.inl ?_⟩
    simpa using hh i ((hK i).2 hi)
  · -- the rows `bᵢ` are linearly dependent ⇒ there is `h ≠ 0` with `bᵢ · h = 0` for all `i`
    have hμne : μ ≠ 0 := fun h0 => by rw [h0] at hi0; simp at hi0
    have hdet : (Matrix.of b).det = 0 := by
      refine exists_vecMul_eq_zero_iff.1 ⟨μ, hμne, ?_⟩
      ext k
      have := congrFun hμb k
      simpa [vecMul, dotProduct, Finset.sum_apply] using this
    obtain ⟨h, hh0, hMh⟩ := exists_mulVec_eq_zero_iff.2 hdet
    have hbh : ∀ i, b i ⬝ᵥ h = 0 := fun i => by
      have := congrFun hMh i
      simpa [mulVec] using this
    rcases motzkinS K b (fun i => -Pq (avec R q i) i h) with
      ⟨z0, hz0⟩ | ⟨ν, hν0, hνK, ⟨i1, hi1⟩, hνb, hνc⟩
    · -- shift `z0` by `δ (1,1,1)` to make all components nonzero
      have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), (∀ m, z0 m + δ * 1 ≠ 0) ∧
          ∀ i ∈ K, b i ⬝ᵥ z0 + δ * (b i ⬝ᵥ fun _ => 1) < -Pq (avec R q i) i h := by
        refine (eventually_all.2 fun m => ev_ne (z0 m) 1 one_ne_zero).and ?_
        have : ∀ i, ∀ᶠ δ in 𝓝[>] (0 : ℝ), i ∈ K →
            b i ⬝ᵥ z0 + δ * (b i ⬝ᵥ fun _ => 1) < -Pq (avec R q i) i h := fun i => by
          by_cases hi : i ∈ K
          · filter_upwards [ev_lt _ (b i ⬝ᵥ fun _ => 1) _ (hz0 i hi)] with δ hδ _ using hδ
          · exact Eventually.of_forall fun _ h' => absurd h' hi
        filter_upwards [eventually_all.2 this] with δ hδ i hi using hδ i hi
      obtain ⟨δ, hδz, hδK⟩ := hev.exists
      refine ⟨h, z0 + δ • fun _ => 1, fun m => by simpa using hδz m,
        fun i hi => Or.inr ⟨hbh i, ?_⟩⟩
      have := hδK i ((hK i).2 hi)
      rw [dot_add_smul]
      linarith
    · -- the certificate `ν` contradicts `key_neg`
      exfalso
      have hi1K : i1 ∈ K := by
        by_contra hn; rw [hνK i1 hn] at hi1; exact lt_irrefl 0 hi1
      obtain ⟨i2, hi21, hi2⟩ : ∃ i2, i2 ≠ i1 ∧ 0 < ν i2 := by
        by_contra hn
        push Not at hn
        have hz : ∀ i, i ≠ i1 → ν i = 0 := fun i hi => le_antisymm (hn i hi) (hν0 i)
        have hs : ∑ i, ν i • b i = ν i1 • b i1 :=
          Finset.sum_eq_single i1 (fun i _ hi => by rw [hz i hi, zero_smul])
            (fun h' => absurd (Finset.mem_univ _) h')
        rw [hs] at hνb
        rcases smul_eq_zero.1 hνb with h' | h'
        · exact lt_irrefl 0 (h' ▸ hi1)
        · exact (hK i1).1 hi1K h'
      have hneg := key_neg hR hnz hq ν h hν0 (by simpa only [hb] using hνb)
        ⟨i2, i1, hi21, hi2, hi1⟩ hh0
      have : ∑ i, ν i * -Pq (avec R q i) i h = -∑ i, ν i * Pq (avec R q i) i h := by
        simp [mul_neg, Finset.sum_neg_distrib]
      linarith

/-! ### Theorem Z: all three widths can be decreased -/

lemma avec_self_pos {R : Matrix (Fin 3) (Fin 3) ℝ} (hnz : ∀ i j, R i j ≠ 0) {q : Fin 3 → ℝ}
    (hq : ∀ j, 0 < q j) (i : Fin 3) : 0 < avec R q i i := by
  rw [avec_self hnz]
  exact Finset.sum_pos (fun j _ => mul_pos (hq j) (abs_pos.2 (hnz i j))) Finset.univ_nonempty

/-- **core**: for an orthogonal `R` without zero entries all three widths decrease simultaneously. -/
theorem core {R : Matrix (Fin 3) (Fin 3) ℝ} (hR : R ∈ orthogonalGroup (Fin 3) ℝ)
    (hnz : ∀ i j, R i j ≠ 0) {q : Fin 3 → ℝ} (hq : ∀ j, 0 < q j) :
    ∃ R' ∈ orthogonalGroup (Fin 3) ℝ, ∀ i, ∑ j, q j * |R' i j| < ∑ j, q j * |R i j| := by
  obtain ⟨h, z, hz, hhz⟩ := choose_hz hR hnz hq
  have hD : ∀ i, ∀ᶠ t in 𝓝[>] (0 : ℝ), Dq (avec R q i) i (t • (h + t • z)) < 0 := by
    intro i
    by_cases hb : bvec (avec R q i) i = 0
    · exact ev_neg_Z hb (avec_self_pos hnz hq i) hz
    · exact ev_neg (hhz i hb)
  have hv : Continuous fun t : ℝ => t • (h + t • z) := by fun_prop
  have hS : ∀ i j, ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < R i j * (cay (t • (h + t • z)) * R) i j := by
    intro i j
    have hc : Continuous fun t : ℝ => R i j * (cay (t • (h + t • z)) * R) i j := by
      have hm : Continuous fun t : ℝ => cay (t • (h + t • z)) * R :=
        (continuous_cay.comp hv).matrix_mul continuous_const
      exact continuous_const.mul ((continuous_apply j).comp ((continuous_apply i).comp hm))
    have h0 : 0 < R i j * (cay ((0 : ℝ) • (h + (0 : ℝ) • z)) * R) i j := by
      simpa [cay_zero] using mul_self_pos.2 (hnz i j)
    exact nhdsWithin_le_nhds ((hc.tendsto 0).eventually (lt_mem_nhds h0))
  obtain ⟨t, hDt, hSt⟩ :=
    ((eventually_all.2 hD).and (eventually_all.2 fun i => eventually_all.2 (hS i))).exists
  refine ⟨cay (t • (h + t • z)) * R, mul_mem (cay_mem _) hR, fun i => ?_⟩
  rw [width_mul hSt q i, ← avec_self hnz q i]
  have e := cay_mulVec (t • (h + t • z)) (avec R q i) i
  have hneg : 2 * (1 + nrm (t • (h + t • z)))⁻¹ * Dq (avec R q i) i (t • (h + t • z)) < 0 :=
    mul_neg_of_pos_of_neg (by have := one_add_nrm_pos (t • (h + t • z)); positivity) (hDt i)
  linarith

end Boxes
