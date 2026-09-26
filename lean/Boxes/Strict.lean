import Boxes.Necessity

/-!
# Strict fitting: the box does not touch the container

* `openBox p` — the open box `(0, p₀) × (0, p₁) × (0, p₂)`;
  `FitsStrict p q` — some isometry maps `box q` into `openBox p`.
* `fitsStrict_iff_shrink` — strict fitting ⇔ `NC (p − ε) q` for some `ε > 0`.
* `fitsStrict_iff_NCs` — an explicit strict criterion `NCs`. It is **not** obtained from `NC` by
  replacing `≤` with `<` only: the case split inside `stripH` changes as well (`x ≤ s` becomes
  `x < s`), because the least extent along a strip jumps when the longer side equals the width of
  the strip. (For the unit cube and the `1 × 0.5 × 0.5` box the naive replacement answers "fits
  strictly", which is false.)
-/

namespace Boxes

open Real Matrix Topology Filter

/-- The open box with edges `p` along the coordinate axes. -/
def openBox (p : Fin 3 → ℝ) : Set E3 := {x | ∀ i, 0 < x i ∧ x i < p i}

/-- The box with edges `q` fits into the box with edges `p` without touching its boundary. -/
def FitsStrict (p q : Fin 3 → ℝ) : Prop := ∃ f : E3 ≃ᵢ E3, f '' box q ⊆ openBox p

/-! ## The strict criterion -/

/-- Strict version of `stripOK`. -/
def stripOKs (u v s : ℝ) : Prop := min u v < s

/-- Strict version of `stripH`: the infimum of the extent along a strip of width `s` over positions
strictly inside the strip. Note the case split `x < s` (not `x ≤ s`). -/
noncomputable def stripHs (u v s : ℝ) : ℝ :=
  let x := max u v
  let y := min u v
  if x < s then y
  else min x ((2 * x * y * s + (x ^ 2 - y ^ 2) * √(x ^ 2 + y ^ 2 - s ^ 2)) / (x ^ 2 + y ^ 2))

/-- The `u × v` rectangle fits strictly inside the `a × b` rectangle. -/
def Fit2s (a b u v : ℝ) : Prop := stripOKs u v a ∧ stripHs u v a < b

/-- One check of the strict criterion (same roles of `σ`, `τ` as in `NCcase`). -/
def NCcaseS (p q : Fin 3 → ℝ) (σ τ : Equiv.Perm (Fin 3)) : Prop :=
  stripOKs (q (τ 1)) (q (τ 2)) (p (σ 0)) ∧
  Fit2s (p (σ 1)) (p (σ 2)) (q (τ 0)) (stripHs (q (τ 1)) (q (τ 2)) (p (σ 0)))

/-- **Strict criterion.** -/
def NCs (p q : Fin 3 → ℝ) : Prop := ∃ σ τ : Equiv.Perm (Fin 3), NCcaseS p q σ τ

/-! ## Reduction to strict widths -/

open WithLp in
/-- Every isometry of `E3` is `x ↦ R x + f 0` with an orthogonal `R`. -/
lemma isom_matrix (f : E3 ≃ᵢ E3) :
    ∃ R ∈ orthogonalGroup (Fin 3) ℝ, ∀ x : Fin 3 → ℝ, ofLp (f (toLp 2 x)) = R *ᵥ x + ofLp (f 0) := by
  set L := f.toRealLinearIsometryEquiv
  set b := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  set R := LinearMap.toMatrix b b (L : E3 →ₗ[ℝ] E3)
  have hRmem : R ∈ orthogonalGroup (Fin 3) ℝ :=
    L.toMatrix_mem_unitaryGroup (EuclideanSpace.basisFun (Fin 3) ℝ) (EuclideanSpace.basisFun (Fin 3) ℝ)
  have hL : ∀ x : Fin 3 → ℝ, ofLp (L (toLp 2 x)) = R *ᵥ x := by
    intro x
    have : toEuclideanLin R = (L : E3 →ₗ[ℝ] E3) := by
      rw [toEuclideanLin_eq_toLin_orthonormal, Matrix.toLin_toMatrix]
    rw [← LinearIsometryEquiv.coe_toLinearEquiv, ← LinearEquiv.coe_toLinearMap]
    change ofLp ((L : E3 →ₗ[ℝ] E3) (toLp 2 x)) = _
    rw [← this, toLpLin_apply]
  refine ⟨R, hRmem, fun x => ?_⟩
  have e : f (toLp 2 x) = L (toLp 2 x) + f 0 := by
    rw [IsometryEquiv.toRealLinearIsometryEquiv_apply]; abel
  rw [e, ofLp_add, hL]

open WithLp in
/-- Strict widths: `FitsStrict` ⇔ some orthogonal `R` has `∑ⱼ qⱼ |Rᵢⱼ| < pᵢ` for all `i`. -/
theorem fitsStrict_iff_widths (p q : Fin 3 → ℝ) (hq : ∀ i, 0 ≤ q i) :
    FitsStrict p q ↔ ∃ R ∈ orthogonalGroup (Fin 3) ℝ, ∀ i, ∑ j, q j * |R i j| < p i := by
  have hq' : (0 : Fin 3 → ℝ) ≤ q := fun i => hq i
  constructor
  · rintro ⟨f, hf⟩
    obtain ⟨R, hR, hfx⟩ := isom_matrix f
    refine ⟨R, hR, fun i => ?_⟩
    obtain ⟨xp, hxp, xm, hxm, ep, em⟩ := exists_vertices R q hq' i
    have hXp : toLp 2 xp ∈ box q := (mem_box_iff q _).2 (by simpa using hxp)
    have hXm : toLp 2 xm ∈ box q := (mem_box_iff q _).2 (by simpa using hxm)
    have h1 : (ofLp (f (toLp 2 xp))) i < p i := (hf ⟨_, hXp, rfl⟩ i).2
    have h2 : 0 < (ofLp (f (toLp 2 xm))) i := (hf ⟨_, hXm, rfl⟩ i).1
    rw [hfx, Pi.add_apply, ep] at h1
    rw [hfx, Pi.add_apply, em] at h2
    rw [← hi_sub_lo R q hq' i]
    linarith
  · rintro ⟨R, hR, hw⟩
    refine ⟨motion R hR (fun i => -lo R q i + (p i - ∑ j, q j * |R i j|) / 2), ?_⟩
    rintro _ ⟨X, hX, rfl⟩ i
    have hx := (mem_box_iff q X).1 hX
    have b1 := (lo_le_mulVec_le_hi R q (ofLp X) hx i).1
    have b2 := (lo_le_mulVec_le_hi R q (ofLp X) hx i).2
    have hd := hi_sub_lo R q hq' i
    have hwi := hw i
    show 0 < (R *ᵥ ofLp X + fun i => -lo R q i + (p i - ∑ j, q j * |R i j|) / 2) i ∧
      (R *ᵥ ofLp X + fun i => -lo R q i + (p i - ∑ j, q j * |R i j|) / 2) i < p i
    simp only [Pi.add_apply]
    constructor <;> linarith

open WithLp in
/-- Permutations for strict widths. -/
lemma widths_perm_strict (p q : Fin 3 → ℝ) (σ τ : Equiv.Perm (Fin 3))
    (h : ∃ R ∈ orthogonalGroup (Fin 3) ℝ, ∀ i, ∑ j, q (τ j) * |R i j| < p (σ i)) :
    ∃ R ∈ orthogonalGroup (Fin 3) ℝ, ∀ i, ∑ j, q j * |R i j| < p i := by
  obtain ⟨R, hR, hw⟩ := h
  refine ⟨R.submatrix σ.symm τ.symm, ?_, fun i => ?_⟩
  · rw [mem_orthogonalGroup_iff] at hR ⊢
    rw [transpose_submatrix, submatrix_mul_equiv, hR, submatrix_one_equiv]
  · have := hw (σ.symm i)
    rw [Equiv.apply_symm_apply] at this
    rw [← Equiv.sum_comp τ]
    simpa using this

/-! ## Theorem 1: strict fitting via shrinking -/

/-- A uniform gap: strict widths leave room `ε > 0` on every axis. -/
lemma exists_gap {p w : Fin 3 → ℝ} (hw0 : ∀ i, 0 ≤ w i) (h : ∀ i, w i < p i) :
    ∃ ε > 0, (∀ i, ε < p i) ∧ ∀ i, w i ≤ p i - ε := by
  set m := min (min (p 0 - w 0) (p 1 - w 1)) (p 2 - w 2) with hm
  have hm0 : 0 < m := lt_min (lt_min (by linarith [h 0]) (by linarith [h 1])) (by linarith [h 2])
  have hmi : ∀ i, m ≤ p i - w i := by
    intro i
    fin_cases i
    · exact le_trans (min_le_left _ _) (min_le_left _ _)
    · exact le_trans (min_le_left _ _) (min_le_right _ _)
    · exact min_le_right _ _
  refine ⟨m / 2, by positivity, fun i => ?_, fun i => ?_⟩
  · have := hmi i; have := hw0 i; linarith
  · have := hmi i; linarith

/-- **Theorem 1.** The box `q` fits strictly into the box `p` if and only if it fits (in the sense of
`NC`) into the box `p − ε` for some `ε > 0`. -/
theorem fitsStrict_iff_shrink (p q : Fin 3 → ℝ) (hq : ∀ i, 0 ≤ q i) :
    FitsStrict p q ↔ ∃ ε > 0, (∀ i, ε < p i) ∧ NC (fun i => p i - ε) q := by
  rw [fitsStrict_iff_widths p q hq]
  constructor
  · rintro ⟨R, hR, hw⟩
    obtain ⟨ε, hε, hεp, hle⟩ := exists_gap (w := fun i => ∑ j, q j * |R i j|)
      (fun i => Finset.sum_nonneg fun j _ => mul_nonneg (hq j) (abs_nonneg _)) hw
    refine ⟨ε, hε, hεp, NC_of_fits _ q (fun i => by linarith [hεp i]) hq ?_⟩
    exact (fits_iff_widths _ q hq).2 ⟨R, hR, hle⟩
  · rintro ⟨ε, hε, hεp, hNC⟩
    obtain ⟨R, hR, hw⟩ := (fits_iff_widths _ q hq).1
      (fits_of_NC _ q (fun i => by linarith [hεp i]) hq hNC)
    exact ⟨R, hR, fun i => lt_of_le_of_lt (hw i) (show p i - ε < p i by linarith)⟩

/-! ## Strict strip lemma -/

lemma stripHs_nonneg {u v s : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hs : 0 ≤ s) : 0 ≤ stripHs u v s := by
  simp only [stripHs]
  have hy : 0 ≤ min u v := le_min hu hv
  have hyx : min u v ≤ max u v := min_le_max
  split_ifs
  · exact hy
  · refine le_min (le_trans hy hyx) (div_nonneg (add_nonneg (by positivity) (mul_nonneg ?_ (sqrt_nonneg _)))
      (by positivity))
    nlinarith

/-- Strict minimality (`y ≤ x`): a position strictly inside the strip has extent along the strip at
least the strict value. -/
lemma strip_min_strict_aux {x y s c d : ℝ} (hy : 0 ≤ y) (hyx : y ≤ x) (hs : 0 ≤ s)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hcd : c ^ 2 + d ^ 2 = 1) (h : x * c + y * d < s) :
    y < s ∧ (if x < s then y
        else min x ((2 * x * y * s + (x ^ 2 - y ^ 2) * √(x ^ 2 + y ^ 2 - s ^ 2)) / (x ^ 2 + y ^ 2)))
      ≤ x * d + y * c := by
  have hcd1 : 1 ≤ c + d := by nlinarith [mul_nonneg hc hd]
  have hc1 : c ≤ 1 := by nlinarith [sq_nonneg d]
  have hyA : y ≤ x * c + y * d := by nlinarith [mul_le_mul_of_nonneg_right hyx hc]
  refine ⟨lt_of_le_of_lt hyA h, ?_⟩
  split_ifs with hxs
  · nlinarith [mul_le_mul_of_nonneg_right hyx hd]
  push Not at hxs
  have hx : 0 < x := by linarith
  have hA0 : 0 ≤ x * c + y * d := le_trans hy hyA
  have hAE : (x * c + y * d) ^ 2 + (x * d - y * c) ^ 2 = x ^ 2 + y ^ 2 := by
    linear_combination (x ^ 2 + y ^ 2) * hcd
  -- `E ≥ 0`: otherwise `A ≥ x ≥ s`
  have hE0 : 0 ≤ x * d - y * c := by
    by_contra hneg
    push Not at hneg
    have h1 : y * c - x * d ≤ y := by nlinarith [mul_nonneg hx.le hd, mul_le_mul_of_nonneg_left hc1 hy]
    have h1' : 0 ≤ y * c - x * d := by linarith
    have h2 : x ^ 2 ≤ (x * c + y * d) ^ 2 := by nlinarith [mul_le_mul h1 h1 h1' hy]
    have h3 : x ≤ x * c + y * d := (sq_le_sq₀ hx.le hA0).1 h2
    linarith
  exact chord_core hy hyx hx hs hyA h.le hE0 (sqrt_nonneg _) hAE (by ring)
    (sq_sqrt (by nlinarith))

/-- Strict minimality, general form. -/
lemma strip_min_strict {u v s c d : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hs : 0 ≤ s)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hcd : c ^ 2 + d ^ 2 = 1) (h : u * c + v * d < s) :
    stripOKs u v s ∧ stripHs u v s ≤ u * d + v * c := by
  unfold stripOKs
  simp only [stripHs]
  rcases le_total v u with huv | huv
  · rw [max_eq_left huv, min_eq_right huv]
    exact strip_min_strict_aux hv huv hs hc hd hcd h
  · rw [max_eq_right huv, min_eq_left huv]
    have := strip_min_strict_aux hu huv hs hd hc (by linarith) (by linarith)
    exact ⟨this.1, by linarith [this.2]⟩

/-- Strict existence (`y ≤ x`): if the strict value is `< t`, some position lies strictly inside the
strip with extent `< t` along it. -/
lemma strip_exists_strict_aux {x y s t : ℝ} (hy : 0 ≤ y) (hyx : y ≤ x) (hys : y < s)
    (ht : (if x < s then y
        else min x ((2 * x * y * s + (x ^ 2 - y ^ 2) * √(x ^ 2 + y ^ 2 - s ^ 2)) / (x ^ 2 + y ^ 2)))
      < t) :
    ∃ c d : ℝ, 0 ≤ c ∧ 0 ≤ d ∧ c ^ 2 + d ^ 2 = 1 ∧ x * c + y * d < s ∧ x * d + y * c < t := by
  split_ifs at ht with hxs
  · exact ⟨1, 0, by norm_num, le_refl _, by norm_num, by simpa using hxs, by simpa using ht⟩
  push Not at hxs
  rcases min_lt_iff.1 ht with hxt | hTt
  · -- lying on its side
    exact ⟨0, 1, le_refl _, by norm_num, by norm_num, by simpa using hys, by simpa using hxt⟩
  -- a slightly narrower strip `s' < s` still gives extent `< t`
  set g : ℝ → ℝ := fun s' =>
    (2 * x * y * s' + (x ^ 2 - y ^ 2) * √(x ^ 2 + y ^ 2 - s' ^ 2)) / (x ^ 2 + y ^ 2) with hg
  have hgc : Continuous g := by rw [hg]; fun_prop
  have ev1 : ∀ᶠ s' in 𝓝[<] s, g s' < t :=
    nhdsWithin_le_nhds ((hgc.tendsto s).eventually (gt_mem_nhds hTt))
  have ev2 : ∀ᶠ s' in 𝓝[<] s, s' ∈ Set.Ioo y s := Ioo_mem_nhdsLT hys
  obtain ⟨s', hgs, hys', hss⟩ := (ev1.and ev2).exists
  obtain ⟨c, d, hc, hd, hcd, hA, hB⟩ := strip_aux hy hyx (by linarith) hys'.le
  have hxs' : ¬ x ≤ s' := by linarith
  simp only [hxs', ↓reduceIte] at hB
  exact ⟨c, d, hc, hd, hcd, by linarith, lt_of_le_of_lt (le_trans hB (min_le_right _ _)) hgs⟩

/-- Strict existence, general form. -/
lemma strip_exists_strict {u v s t : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hok : stripOKs u v s) (ht : stripHs u v s < t) :
    ∃ c d : ℝ, 0 ≤ c ∧ 0 ≤ d ∧ c ^ 2 + d ^ 2 = 1 ∧ u * c + v * d < s ∧ u * d + v * c < t := by
  unfold stripOKs at hok
  simp only [stripHs] at ht
  rcases le_total v u with huv | huv
  · rw [max_eq_left huv, min_eq_right huv] at *
    exact strip_exists_strict_aux hv huv hok ht
  · rw [max_eq_right huv, min_eq_left huv] at *
    obtain ⟨c, d, hc, hd, h1, h2, h3⟩ := strip_exists_strict_aux hu huv hok ht
    exact ⟨d, c, hd, hc, by linarith, by linarith, by linarith⟩

/-! ## Theorem 2: the explicit strict criterion -/

/-- Strict sufficiency for `σ = τ = id`. -/
lemma widths_of_case_strict (p q : Fin 3 → ℝ) (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 ≤ q i)
    (h1 : stripOKs (q 1) (q 2) (p 0))
    (h2 : Fit2s (p 1) (p 2) (q 0) (stripHs (q 1) (q 2) (p 0))) :
    ∃ R ∈ orthogonalGroup (Fin 3) ℝ, ∀ i, ∑ j, q j * |R i j| < p i := by
  set H := stripHs (q 1) (q 2) (p 0)
  have hH : 0 ≤ H := stripHs_nonneg (hq 1) (hq 2) (hp 0).le
  obtain ⟨c₂, d₂, hc₂, hd₂, e₂, hC, hD⟩ := strip_exists_strict (hq 0) hH h2.1 h2.2
  have hc₂1 : c₂ ≤ 1 := by nlinarith [sq_nonneg d₂]
  have hd₂1 : d₂ ≤ 1 := by nlinarith [sq_nonneg c₂]
  -- room to replace `H` by a slightly larger `T`
  obtain ⟨η, hη, hη1, hη2⟩ : ∃ η > 0, q 0 * c₂ + (H + η) * d₂ < p 1 ∧ q 0 * d₂ + (H + η) * c₂ < p 2 := by
    set g := min (p 1 - (q 0 * c₂ + H * d₂)) (p 2 - (q 0 * d₂ + H * c₂)) with hgdef
    have hg : 0 < g := lt_min (by linarith) (by linarith)
    refine ⟨g / 2, by positivity, ?_, ?_⟩
    · have := min_le_left (p 1 - (q 0 * c₂ + H * d₂)) (p 2 - (q 0 * d₂ + H * c₂))
      nlinarith [mul_le_mul_of_nonneg_left hd₂1 (le_of_lt (half_pos hg))]
    · have := min_le_right (p 1 - (q 0 * c₂ + H * d₂)) (p 2 - (q 0 * d₂ + H * c₂))
      nlinarith [mul_le_mul_of_nonneg_left hc₂1 (le_of_lt (half_pos hg))]
  obtain ⟨c₁, d₁, hc₁, hd₁, e₁, hA, hB⟩ :=
    strip_exists_strict (hq 1) (hq 2) h1 (show H < H + η by linarith)
  refine ⟨!![0, c₁, -d₁; c₂, -(d₁ * d₂), -(c₁ * d₂); d₂, d₁ * c₂, c₁ * c₂], ?_, ?_⟩
  · rw [mem_orthogonalGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three] <;>
      first
        | ring1
        | linear_combination e₁
        | linear_combination d₂ ^ 2 * e₁ + e₂
        | linear_combination c₂ ^ 2 * e₁ + e₂
        | linear_combination (-(c₂ * d₂)) * e₁
  · have k₁ := mul_le_mul_of_nonneg_right hB.le hd₂
    have k₂ := mul_le_mul_of_nonneg_right hB.le hc₂
    have := hq 0; have := hq 1; have := hq 2
    intro i
    fin_cases i <;>
      simp [Fin.sum_univ_three, abs_mul, abs_of_nonneg, hc₁, hd₁, hc₂, hd₂] <;>
      nlinarith

/-- Strict version of Lemma 2 (⇒) for `i = j = 0`. -/
lemma NCcaseS_of_zero (p q : Fin 3 → ℝ) (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 ≤ q i)
    (R : Matrix (Fin 3) (Fin 3) ℝ) (hR : R ∈ orthogonalGroup (Fin 3) ℝ)
    (hw : ∀ i, ∑ j, q j * |R i j| < p i) (h0 : R 0 0 = 0) :
    stripOKs (q 1) (q 2) (p 0) ∧ Fit2s (p 1) (p 2) (q 0) (stripHs (q 1) (q 2) (p 0)) := by
  have cof := abs_eq_abs_adjugate hR
  have e11 : |R 1 1| = |R 0 2| * |R 2 0| := by
    rw [cof, adjugate_fin_three]; simp [h0, abs_mul]
  have e12 : |R 1 2| = |R 0 1| * |R 2 0| := by
    rw [cof, adjugate_fin_three]; simp [h0, abs_mul]
  have e21 : |R 2 1| = |R 0 2| * |R 1 0| := by
    rw [cof, adjugate_fin_three]; simp [h0, abs_mul]
  have e22 : |R 2 2| = |R 0 1| * |R 1 0| := by
    rw [cof, adjugate_fin_three]; simp [h0, abs_mul]
  have hrow : |R 0 1| ^ 2 + |R 0 2| ^ 2 = 1 := by
    have := congrFun (congrFun ((mem_orthogonalGroup_iff (Fin 3) ℝ).1 hR) 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_three, h0] at this
    rw [sq_abs, sq_abs]; linear_combination this
  have hcol : |R 1 0| ^ 2 + |R 2 0| ^ 2 = 1 := by
    have := congrFun (congrFun ((mem_orthogonalGroup_iff' (Fin 3) ℝ).1 hR) 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_three, h0] at this
    rw [sq_abs, sq_abs]; linear_combination this
  have w0 := hw 0
  have w1 := hw 1
  have w2 := hw 2
  simp only [Fin.sum_univ_three, h0, abs_zero, mul_zero, zero_add] at w0 w1 w2
  rw [e11, e12] at w1
  rw [e21, e22] at w2
  obtain ⟨hOK, hH1⟩ := strip_min_strict (hq 1) (hq 2) (hp 0).le (abs_nonneg (R 0 1))
    (abs_nonneg (R 0 2)) hrow w0
  have hH : 0 ≤ stripHs (q 1) (q 2) (p 0) := stripHs_nonneg (hq 1) (hq 2) (hp 0).le
  have k1 := mul_le_mul_of_nonneg_right hH1 (abs_nonneg (R 2 0))
  have k2 := mul_le_mul_of_nonneg_right hH1 (abs_nonneg (R 1 0))
  obtain ⟨hOK2, hH2⟩ := strip_min_strict (hq 0) hH (hp 1).le (abs_nonneg (R 1 0))
    (abs_nonneg (R 2 0)) hcol (by nlinarith)
  exact ⟨hOK, hOK2, by nlinarith⟩

/-- Strict version of Lemma 2 (⇒). -/
theorem NCs_of_zero (p q : Fin 3 → ℝ) (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 ≤ q i)
    (R : Matrix (Fin 3) (Fin 3) ℝ) (hR : R ∈ orthogonalGroup (Fin 3) ℝ)
    (hw : ∀ i, ∑ j, q j * |R i j| < p i) (i j : Fin 3) (h0 : R i j = 0) : NCs p q := by
  refine ⟨Equiv.swap 0 i, Equiv.swap 0 j, ?_⟩
  have hR' : R.submatrix (Equiv.swap 0 i) (Equiv.swap 0 j) ∈ orthogonalGroup (Fin 3) ℝ := by
    rw [mem_orthogonalGroup_iff] at hR ⊢
    rw [transpose_submatrix, submatrix_mul_equiv, hR, submatrix_one_equiv]
  exact NCcaseS_of_zero (fun a => p (Equiv.swap 0 i a)) (fun b => q (Equiv.swap 0 j b))
    (fun _ => hp _) (fun _ => hq _) _ hR'
    (fun a => (Equiv.sum_comp (Equiv.swap 0 j)
      (fun b => q b * |R (Equiv.swap 0 i a) b|)).trans_lt (hw _))
    (by simp [h0])

/-- **Theorem 2.** The box `q` fits strictly into the box `p` if and only if the explicit strict
criterion `NCs` holds. -/
theorem fitsStrict_iff_NCs (p q : Fin 3 → ℝ) (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 ≤ q i) :
    FitsStrict p q ↔ NCs p q := by
  rw [fitsStrict_iff_widths p q hq]
  constructor
  · rintro ⟨R, hR, hw⟩
    obtain ⟨ε, hε, hεp, hle⟩ := exists_gap (w := fun i => ∑ j, q j * |R i j|)
      (fun i => Finset.sum_nonneg fun j _ => mul_nonneg (hq j) (abs_nonneg _)) hw
    obtain ⟨R', hR', hw', i, j, h0⟩ := exists_zero (fun i => p i - ε) q
      (fun i => by linarith [hεp i]) hq ⟨R, hR, hle⟩
    exact NCs_of_zero p q hp hq R' hR' (fun k => by have := hw' k; unfold width at this; linarith) i j h0
  · rintro ⟨σ, τ, h1, h2⟩
    exact widths_perm_strict p q σ τ
      (widths_of_case_strict (fun i => p (σ i)) (fun j => q (τ j)) (fun i => hp _) (fun j => hq _) h1 h2)

end Boxes
