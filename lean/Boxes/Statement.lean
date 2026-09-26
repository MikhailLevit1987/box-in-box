import Boxes.Reduction

/-!
# Statement: a box in a box

**Trusted definitions.** The meaning of the main theorem `Boxes.fits_iff_NC` depends only on the
definitions `box` and `Fits` below, which formalize the geometric problem. The remaining definitions
(`stripOK`, `stripH`, `Fit2`, `NCcase`, `NC`) constitute the criterion itself; their equivalence with
`Fits` is the content of the theorem and is verified by the proof checker.

* `box q` — the closed box `[0, q₀] × [0, q₁] × [0, q₂]` in Euclidean `ℝ³`.
* `Fits p q` — some isometry of space (any rigid motion, reflections included) maps `box q`
  into `box p`. Allowing reflections changes nothing: a box is mirror-symmetric.

The criterion `NC` is a disjunction of explicit checks (9 essentially different ones; 36 counting
the permutations `σ`, `τ` with repetitions), see the paper, Section 4.

This file contains the statement, the reduction to widths and the sufficiency direction.
-/

namespace Boxes

open Real

/-- Euclidean space `ℝ³`. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- The closed box with edges `q` along the coordinate axes. -/
def box (q : Fin 3 → ℝ) : Set E3 := {x | ∀ i, 0 ≤ x i ∧ x i ≤ q i}

/-- **Statement.** The box with edges `q` fits into the box with edges `p`. -/
def Fits (p q : Fin 3 → ℝ) : Prop := ∃ f : E3 ≃ᵢ E3, f '' box q ⊆ box p

/-! ## The criterion -/

/-- A `u × v` rectangle can be put into a strip of width `s`: its shorter side is not wider than
the strip. -/
def stripOK (u v s : ℝ) : Prop := min u v ≤ s

/-- The least extent along a strip of width `s` of a `u × v` rectangle placed in the strip
(the formula of Lemma 1; meaningful when `stripOK u v s`). With `x = max u v`, `y = min u v`. -/
noncomputable def stripH (u v s : ℝ) : ℝ :=
  let x := max u v
  let y := min u v
  if x ≤ s then y
  else min x ((2 * x * y * s + (x ^ 2 - y ^ 2) * √(x ^ 2 + y ^ 2 - s ^ 2)) / (x ^ 2 + y ^ 2))

/-- The `u × v` rectangle fits into the `a × b` rectangle (in "strip of width `a`" form). -/
def Fit2 (a b u v : ℝ) : Prop := stripOK u v a ∧ stripH u v a ≤ b

/-- One check of the criterion: axis `σ 0` of the container is the "height" (a strip), axes
`σ 1`, `σ 2` form the "floor"; edge `τ 0` of the box is horizontal, edges `τ 1`, `τ 2` lie in a
vertical plane. -/
def NCcase (p q : Fin 3 → ℝ) (σ τ : Equiv.Perm (Fin 3)) : Prop :=
  stripOK (q (τ 1)) (q (τ 2)) (p (σ 0)) ∧
  Fit2 (p (σ 1)) (p (σ 2)) (q (τ 0)) (stripH (q (τ 1)) (q (τ 2)) (p (σ 0)))

/-- **Criterion NC**: at least one of the checks passes. -/
def NC (p q : Fin 3 → ℝ) : Prop := ∃ σ τ : Equiv.Perm (Fin 3), NCcase p q σ τ

/-! ## Reduction to widths -/

open Matrix WithLp in
/-- An orthogonal matrix preserves the squared norm. -/
lemma dot_mulVec_self_of_orth {R : Matrix (Fin 3) (Fin 3) ℝ} (hR : Rᵀ * R = 1) (v : Fin 3 → ℝ) :
    (R *ᵥ v) ⬝ᵥ (R *ᵥ v) = v ⬝ᵥ v := by
  calc (R *ᵥ v) ⬝ᵥ (R *ᵥ v) = ((R *ᵥ v) ᵥ* R) ⬝ᵥ v := dotProduct_mulVec _ _ _
    _ = (Rᵀ *ᵥ (R *ᵥ v)) ⬝ᵥ v := by rw [mulVec_transpose]
    _ = v ⬝ᵥ v := by rw [mulVec_mulVec, hR, one_mulVec]

open Matrix WithLp in
/-- The motion `x ↦ R x + t` for an orthogonal `R`. -/
noncomputable def motion (R : Matrix (Fin 3) (Fin 3) ℝ) (hR : R ∈ orthogonalGroup (Fin 3) ℝ)
    (t : Fin 3 → ℝ) : E3 ≃ᵢ E3 where
  toFun x := toLp 2 (R *ᵥ ofLp x + t)
  invFun y := toLp 2 (Rᵀ *ᵥ (ofLp y - t))
  left_inv x := by
    have h : Rᵀ * R = 1 := (mem_orthogonalGroup_iff' (Fin 3) ℝ).1 hR
    simp [mulVec_mulVec, h]
  right_inv y := by
    have h : R * Rᵀ = 1 := (mem_orthogonalGroup_iff (Fin 3) ℝ).1 hR
    simp [mulVec_mulVec, h]
  isometry_toFun := by
    have h : Rᵀ * R = 1 := (mem_orthogonalGroup_iff' (Fin 3) ℝ).1 hR
    refine Isometry.of_dist_eq fun x y => ?_
    rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq]
    congr 1
    have key := dot_mulVec_self_of_orth h (ofLp x - ofLp y)
    simp only [dotProduct, mulVec_sub] at key
    simp only [Pi.add_apply, Real.dist_eq, sq_abs]
    convert key using 2 with i _ i _
    · simp [Pi.sub_apply, sq]
    · simp [sq]

open Matrix WithLp in
lemma mem_box_iff (q : Fin 3 → ℝ) (X : E3) : X ∈ box q ↔ ofLp X ∈ Set.Icc (0 : Fin 3 → ℝ) q := by
  simp [box, Set.mem_Icc, Pi.le_def, forall_and]

/-- Widths: `Fits` ⇔ there is an orthogonal matrix `R` with `∑ⱼ qⱼ |Rᵢⱼ| ≤ pᵢ` for all `i`.
(Mazur–Ulam + `Boxes.exists_translate_mem_box_iff`.) -/
theorem fits_iff_widths (p q : Fin 3 → ℝ) (hq : ∀ i, 0 ≤ q i) :
    Fits p q ↔ ∃ R ∈ Matrix.orthogonalGroup (Fin 3) ℝ, ∀ i, ∑ j, q j * |R i j| ≤ p i := by
  open Matrix WithLp in
  have hq' : (0 : Fin 3 → ℝ) ≤ q := fun i => hq i
  constructor
  · rintro ⟨f, hf⟩
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
    refine ⟨R, hRmem, (exists_translate_mem_box_iff R q p hq').1 ⟨ofLp (f 0), fun x hx => ?_⟩⟩
    have hX : toLp 2 x ∈ box q := (mem_box_iff q _).2 (by simpa using hx)
    have := (mem_box_iff p _).1 (hf ⟨_, hX, rfl⟩)
    have e : f (toLp 2 x) = L (toLp 2 x) + f 0 := by
      rw [IsometryEquiv.toRealLinearIsometryEquiv_apply]; abel
    rw [e, ofLp_add, hL] at this
    exact this
  · rintro ⟨R, hR, hw⟩
    obtain ⟨t, ht⟩ := (exists_translate_mem_box_iff R q p hq').2 hw
    refine ⟨motion R hR t, ?_⟩
    rintro _ ⟨X, hX, rfl⟩
    rw [mem_box_iff]
    exact ht _ ((mem_box_iff q X).1 hX)

/-! ## Sufficiency -/

/-- Lemma 1 (strip) for `y ≤ x`: the rotation `(c, d) = (cos θ, sin θ)` puts the `x × y` rectangle
into the strip of width `s` (`x c + y d ≤ s`), and its extent along the strip (`x d + y c`) is at most
`stripH`. For `x > s` the angle is explicit:
`c = (x s − y √(x²+y²−s²))/(x²+y²)`, `d = (y s + x √(x²+y²−s²))/(x²+y²)`. -/
lemma strip_aux {x y s : ℝ} (hy : 0 ≤ y) (hyx : y ≤ x) (hs : 0 ≤ s) (hys : y ≤ s) :
    ∃ c d : ℝ, 0 ≤ c ∧ 0 ≤ d ∧ c ^ 2 + d ^ 2 = 1 ∧ x * c + y * d ≤ s ∧
      x * d + y * c ≤ (if x ≤ s then y
        else min x ((2 * x * y * s + (x ^ 2 - y ^ 2) * √(x ^ 2 + y ^ 2 - s ^ 2)) / (x ^ 2 + y ^ 2))) := by
  split_ifs with hxs
  · exact ⟨1, 0, by norm_num, le_refl _, by norm_num, by simpa using hxs, by simp⟩
  push Not at hxs
  set T := (2 * x * y * s + (x ^ 2 - y ^ 2) * √(x ^ 2 + y ^ 2 - s ^ 2)) / (x ^ 2 + y ^ 2) with hT
  rcases le_total x T with hxT | hTx
  · -- lying on its side: height `y`, extent `x` along the strip
    rw [min_eq_left hxT]
    exact ⟨0, 1, le_refl _, by norm_num, by norm_num, by simpa using hys, by simp⟩
  rw [min_eq_right hTx]
  have hx : 0 < x := lt_of_le_of_lt hs hxs
  have hr : 0 < x ^ 2 + y ^ 2 := by positivity
  set R := √(x ^ 2 + y ^ 2 - s ^ 2) with hRdef
  have hR0 : 0 ≤ R := sqrt_nonneg _
  have hR2 : R ^ 2 = x ^ 2 + y ^ 2 - s ^ 2 := sq_sqrt (by nlinarith)
  have hyR : y * R ≤ x * s := by
    by_contra hlt
    push Not at hlt
    have := mul_self_lt_mul_self (by positivity) hlt
    nlinarith [mul_nonneg hr.le (sq_nonneg y), mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hy hys 2) hr.le]
  refine ⟨(x * s - y * R) / (x ^ 2 + y ^ 2), (y * s + x * R) / (x ^ 2 + y ^ 2),
    div_nonneg (by linarith) hr.le, div_nonneg (by positivity) hr.le, ?_, ?_, ?_⟩
  · rw [div_pow, div_pow, ← add_div, div_eq_one_iff_eq (by positivity)]
    linear_combination (x ^ 2 + y ^ 2) * hR2
  · rw [mul_div_assoc', mul_div_assoc', ← add_div, div_le_iff₀ hr]
    nlinarith
  · rw [hT, mul_div_assoc', mul_div_assoc', ← add_div]
    exact le_of_eq (by ring)

/-- Lemma 1 (strip), general form. -/
lemma strip_exists {u v s : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hs : 0 ≤ s) (h : stripOK u v s) :
    ∃ c d : ℝ, 0 ≤ c ∧ 0 ≤ d ∧ c ^ 2 + d ^ 2 = 1 ∧ u * c + v * d ≤ s ∧
      u * d + v * c ≤ stripH u v s := by
  unfold stripOK at h
  simp only [stripH]
  rcases le_total v u with huv | huv
  · rw [max_eq_left huv, min_eq_right huv] at *
    exact strip_aux hv huv hs h
  · rw [max_eq_right huv, min_eq_left huv] at *
    obtain ⟨c, d, hc, hd, h1, h2, h3⟩ := strip_aux hu huv hs h
    exact ⟨d, c, hd, hc, by linarith, by linarith, by linarith⟩

open Matrix in
/-- Assembling the 3D position for `σ = τ = id`: axis 0 is the height, edge 0 is horizontal.
The columns of `R` are the edge directions: `m = (0, c₂, d₂)`, `c₁·e₀ + d₁·n`, `−d₁·e₀ + c₁·n`,
where `n = (0, −d₂, c₂)`. -/
lemma widths_of_case (p q : Fin 3 → ℝ) (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 ≤ q i)
    (h1 : stripOK (q 1) (q 2) (p 0)) (h2 : Fit2 (p 1) (p 2) (q 0) (stripH (q 1) (q 2) (p 0))) :
    ∃ R ∈ orthogonalGroup (Fin 3) ℝ, ∀ i, ∑ j, q j * |R i j| ≤ p i := by
  set H := stripH (q 1) (q 2) (p 0)
  obtain ⟨c₁, d₁, hc₁, hd₁, e₁, hA, hB⟩ := strip_exists (hq 1) (hq 2) (hp 0).le h1
  have hH : 0 ≤ H := le_trans (add_nonneg (mul_nonneg (hq 1) hd₁) (mul_nonneg (hq 2) hc₁)) hB
  obtain ⟨c₂, d₂, hc₂, hd₂, e₂, hC, hD⟩ := strip_exists (hq 0) hH (hp 1).le h2.1
  have hD' := le_trans hD h2.2
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
  · have k₁ := mul_le_mul_of_nonneg_right hB hd₂
    have k₂ := mul_le_mul_of_nonneg_right hB hc₂
    have := hq 0; have := hq 1; have := hq 2
    intro i
    fin_cases i <;>
      simp [Fin.sum_univ_three, abs_mul, abs_of_nonneg, hc₁, hd₁, hc₂, hd₂] <;>
      nlinarith

open Matrix in
/-- Permuting the axes of the container and the edges of the box preserves the existence of a
suitable rotation. -/
lemma widths_perm (p q : Fin 3 → ℝ) (σ τ : Equiv.Perm (Fin 3))
    (h : ∃ R ∈ orthogonalGroup (Fin 3) ℝ, ∀ i, ∑ j, q (τ j) * |R i j| ≤ p (σ i)) :
    ∃ R ∈ orthogonalGroup (Fin 3) ℝ, ∀ i, ∑ j, q j * |R i j| ≤ p i := by
  obtain ⟨R, hR, hw⟩ := h
  refine ⟨R.submatrix σ.symm τ.symm, ?_, fun i => ?_⟩
  · rw [mem_orthogonalGroup_iff] at hR ⊢
    rw [transpose_submatrix, submatrix_mul_equiv, hR, submatrix_one_equiv]
  · have := hw (σ.symm i)
    rw [Equiv.apply_symm_apply] at this
    rw [← Equiv.sum_comp τ]
    simpa using this

/-- **Sufficiency** (Lemma 1 applied twice, constructively): every check of `NC` yields an
explicit rotation. -/
theorem fits_of_NC (p q : Fin 3 → ℝ) (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 ≤ q i) :
    NC p q → Fits p q := by
  rintro ⟨σ, τ, h1, h2⟩
  rw [fits_iff_widths p q hq]
  exact widths_perm p q σ τ
    (widths_of_case (fun i => p (σ i)) (fun j => q (τ j)) (fun i => hp _) (fun j => hq _) h1 h2)

/-! ## Sanity checks of the statement itself (about `Fits`, without `NC`) -/

/-- A box fits into itself. -/
theorem fits_self (p : Fin 3 → ℝ) : Fits p p :=
  ⟨IsometryEquiv.refl E3, by rintro _ ⟨x, hx, rfl⟩; exact hx⟩

/-- The `2 × 2 × 2` cube does not fit into the unit cube. -/
theorem not_fits_double_cube : ¬ Fits (fun _ => 1) (fun _ => 2) := by
  rintro ⟨f, hf⟩
  -- two points of the big cube at distance 2
  set a : E3 := EuclideanSpace.single 0 0
  set b : E3 := EuclideanSpace.single 0 2
  have ha : a ∈ box (fun _ => 2) := by
    intro i; fin_cases i <;> simp [a]
  have hb : b ∈ box (fun _ => 2) := by
    intro i; fin_cases i <;> simp [b]
  have hab : dist a b = 2 := by
    simp [a, b]
  -- in the unit cube the squared distance is at most 3
  have key : ∀ x ∈ box (fun _ => (1 : ℝ)), ∀ y ∈ box (fun _ => (1 : ℝ)), dist x y ^ 2 ≤ 3 := by
    intro x hx y hy
    rw [EuclideanSpace.dist_eq, sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _), Fin.sum_univ_three]
    have h : ∀ i, dist (x i) (y i) ^ 2 ≤ 1 := by
      intro i
      obtain ⟨h1, h2⟩ := hx i; obtain ⟨h3, h4⟩ := hy i
      rw [Real.dist_eq, sq_abs]; nlinarith
    linarith [h 0, h 1, h 2]
  have := key (f a) (hf ⟨a, ha, rfl⟩) (f b) (hf ⟨b, hb, rfl⟩)
  rw [f.dist_eq, hab] at this
  norm_num at this

end Boxes
