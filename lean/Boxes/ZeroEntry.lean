import Boxes.Statement

/-!
# Lemma 2 (⇒): a position with a horizontal edge yields a check of `NC`

If an orthogonal `R` with `∑ⱼ qⱼ|Rᵢⱼ| ≤ pᵢ` has a zero entry `R i j = 0`, then `NC` holds.

* `strip_min` — the converse side of Lemma 1 (`strip_exists`): if a rectangle stands in a strip,
  its extent along the strip is at least `stripH`.
* `abs_eq_abs_adjugate` — for an orthogonal matrix `|Rₐᵦ|` equals the absolute value of the
  corresponding cofactor.
-/

namespace Boxes

open Real Matrix

/-- Core of minimality: a point `(A, E)` of the circle of radius `r = √(x²+y²)` with
`y ≤ A ≤ s`, `E ≥ 0` lies above the chord between `(y, x)` and `(s, R)`, `R = √(r² − s²)`; hence
`B = (2xyA + (x²−y²)E)/r² ≥ min(x, T)`, where `T` is the value of `B` at `A = s`. -/
lemma chord_core {x y s A E B R : ℝ} (hy : 0 ≤ y) (hyx : y ≤ x) (hx : 0 < x) (hs : 0 ≤ s)
    (hyA : y ≤ A) (hAs : A ≤ s) (hE0 : 0 ≤ E) (hR0 : 0 ≤ R)
    (hAE : A ^ 2 + E ^ 2 = x ^ 2 + y ^ 2) (hBid : (x ^ 2 + y ^ 2) * B = 2 * x * y * A + (x ^ 2 - y ^ 2) * E)
    (hR2 : R ^ 2 = x ^ 2 + y ^ 2 - s ^ 2) :
    min x ((2 * x * y * s + (x ^ 2 - y ^ 2) * R) / (x ^ 2 + y ^ 2)) ≤ B := by
  obtain ⟨r2, hr2⟩ : ∃ r2, r2 = x ^ 2 + y ^ 2 := ⟨_, rfl⟩
  rw [← hr2] at hAE hBid hR2 ⊢
  have hr : 0 < r2 := by rw [hr2]; positivity
  obtain ⟨T, hT⟩ : ∃ T, T = (2 * x * y * s + (x ^ 2 - y ^ 2) * R) / r2 := ⟨_, rfl⟩
  rw [← hT]
  have hTr : T * r2 = 2 * x * y * s + (x ^ 2 - y ^ 2) * R := by rw [hT]; exact div_mul_cancel₀ _ hr.ne'
  have hxy2 : 0 ≤ x ^ 2 - y ^ 2 := by nlinarith
  have hA0 : 0 ≤ A := le_trans hy hyA
  -- `E ≥ R` because `A ≤ s`
  have hER : R ≤ E := by
    refine (sq_le_sq₀ hR0 hE0).1 ?_
    nlinarith [mul_le_mul hAs hAs hA0 hs]
  obtain ⟨a, ha⟩ : ∃ a, a = s - A := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = A - y := ⟨_, rfl⟩
  have ha0 : 0 ≤ a := by rw [ha]; linarith
  have hb0 : 0 ≤ b := by rw [hb]; linarith
  rcases eq_or_lt_of_le (add_nonneg ha0 hb0) with hD | hD
  · -- `A = s`: then `B ≥ T`
    have hAs' : A = s := by linarith
    refine le_trans (min_le_right _ _) ?_
    have h1 : T * r2 ≤ B * r2 := by
      rw [hTr, mul_comm B, hBid, hAs']
      linarith [mul_le_mul_of_nonneg_left hER hxy2]
    exact le_of_mul_le_mul_right h1 hr
  -- the chord: `(a+b) E ≥ a x + b R`
  obtain ⟨D, hDdef⟩ : ∃ D, D = a + b := ⟨_, rfl⟩
  rw [← hDdef] at hD
  have hDA : D * A = a * y + b * s := by rw [hDdef, ha, hb]; ring
  have hCS0 : 0 ≤ y * s + x * R := add_nonneg (mul_nonneg hy hs) (mul_nonneg hx.le hR0)
  have hCS : y * s + x * R ≤ r2 := by
    have e : r2 ^ 2 - (y * s + x * R) ^ 2 = (y * R - x * s) ^ 2 := by
      linear_combination (-(x ^ 2 + y ^ 2)) * hR2 + (r2 - x ^ 2 - y ^ 2 + x ^ 2 + y ^ 2) * hr2
    exact (sq_le_sq₀ hCS0 hr.le).1 (by linarith [e, sq_nonneg (y * R - x * s)])
  have hL : (a * x + b * R) ^ 2 ≤ (D * E) ^ 2 := by
    have hab : 0 ≤ 2 * (a * b) := by positivity
    have e2 : (a * y + b * s) ^ 2 + (a * x + b * R) ^ 2 = (a ^ 2 + b ^ 2) * r2 + 2 * (a * b) * (y * s + x * R) := by
      linear_combination b ^ 2 * hR2 - a ^ 2 * hr2
    have e3 : D ^ 2 * r2 = (a ^ 2 + b ^ 2) * r2 + 2 * (a * b) * r2 := by rw [hDdef]; ring
    have hDE : (D * E) ^ 2 = D ^ 2 * r2 - (D * A) ^ 2 := by
      have : E ^ 2 = r2 - A ^ 2 := by linarith
      rw [mul_pow, mul_pow, this]; ring
    rw [hDE, hDA]
    linarith [mul_le_mul_of_nonneg_left hCS hab]
  have hchord : a * x + b * R ≤ D * E :=
    (sq_le_sq₀ (add_nonneg (mul_nonneg ha0 hx.le) (mul_nonneg hb0 hR0))
      (mul_nonneg hD.le hE0)).1 hL
  have hm1 : min x T ≤ x := min_le_left _ _
  have hm2 : min x T ≤ T := min_le_right _ _
  have key : (a * x + b * T) * r2 ≤ D * B * r2 := by
    have e1 : D * B * r2 = 2 * x * y * (D * A) + (x ^ 2 - y ^ 2) * (D * E) := by
      rw [mul_assoc, mul_comm B, hBid]; ring
    have e2 : (a * x + b * T) * r2 = a * x * r2 + b * (T * r2) := by ring
    have e4 : a * x * r2 = a * (2 * x * y * y + (x ^ 2 - y ^ 2) * x) := by rw [hr2]; ring
    rw [e1, e2, hTr, hDA, e4]
    nlinarith [mul_le_mul_of_nonneg_left hchord hxy2]
  have key' : a * x + b * T ≤ D * B := le_of_mul_le_mul_right key hr
  have : D * min x T ≤ D * B := by
    have e : D * min x T = a * min x T + b * min x T := by rw [hDdef]; ring
    linarith [mul_le_mul_of_nonneg_left hm1 ha0, mul_le_mul_of_nonneg_left hm2 hb0]
  exact le_of_mul_le_mul_left this hD

/-- Lemma 1, minimality, for `y ≤ x`. -/
lemma strip_min_aux {x y s c d : ℝ} (hy : 0 ≤ y) (hyx : y ≤ x) (hs : 0 ≤ s)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hcd : c ^ 2 + d ^ 2 = 1) (h : x * c + y * d ≤ s) :
    y ≤ s ∧ (if x ≤ s then y
        else min x ((2 * x * y * s + (x ^ 2 - y ^ 2) * √(x ^ 2 + y ^ 2 - s ^ 2)) / (x ^ 2 + y ^ 2)))
      ≤ x * d + y * c := by
  have hcd1 : 1 ≤ c + d := by nlinarith [mul_nonneg hc hd]
  have hc1 : c ≤ 1 := by nlinarith [sq_nonneg d]
  have hyA : y ≤ x * c + y * d := by nlinarith [mul_le_mul_of_nonneg_right hyx hc]
  refine ⟨le_trans hyA h, ?_⟩
  split_ifs with hxs
  · nlinarith [mul_le_mul_of_nonneg_right hyx hd]
  push Not at hxs
  have hx : 0 < x := lt_of_le_of_lt hs hxs
  have hA0 : 0 ≤ x * c + y * d := le_trans hy hyA
  have hAE : (x * c + y * d) ^ 2 + (x * d - y * c) ^ 2 = x ^ 2 + y ^ 2 := by
    linear_combination (x ^ 2 + y ^ 2) * hcd
  -- `E ≥ 0`: otherwise `A ≥ x > s`
  have hE0 : 0 ≤ x * d - y * c := by
    by_contra hneg
    push Not at hneg
    have h1 : y * c - x * d ≤ y := by nlinarith [mul_nonneg hx.le hd, mul_le_mul_of_nonneg_left hc1 hy]
    have h1' : 0 ≤ y * c - x * d := by linarith
    have h2 : x ^ 2 ≤ (x * c + y * d) ^ 2 := by nlinarith [mul_le_mul h1 h1 h1' hy]
    have h3 : x ≤ x * c + y * d := (sq_le_sq₀ hx.le hA0).1 h2
    linarith
  exact chord_core hy hyx hx hs hyA h hE0 (sqrt_nonneg _) hAE (by ring)
    (sq_sqrt (by nlinarith))

/-- Lemma 1, minimality: if the `u × v` rectangle with direction `(c, d)` stands in the strip of
width `s`, then `stripOK` holds and its extent along the strip is at least `stripH`. -/
lemma strip_min {u v s c d : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hs : 0 ≤ s)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hcd : c ^ 2 + d ^ 2 = 1) (h : u * c + v * d ≤ s) :
    stripOK u v s ∧ stripH u v s ≤ u * d + v * c := by
  unfold stripOK
  simp only [stripH]
  rcases le_total v u with huv | huv
  · rw [max_eq_left huv, min_eq_right huv]
    exact strip_min_aux hv huv hs hc hd hcd h
  · rw [max_eq_right huv, min_eq_left huv]
    have := strip_min_aux hu huv hs hd hc (by linarith) (by linarith)
    exact ⟨this.1, by linarith [this.2]⟩

/-- For an orthogonal matrix `adj R = det R • Rᵀ` and `(det R)² = 1`. -/
lemma adjugate_of_orth {R : Matrix (Fin 3) (Fin 3) ℝ} (hR : R ∈ orthogonalGroup (Fin 3) ℝ) :
    adjugate R = R.det • Rᵀ ∧ R.det * R.det = 1 := by
  have h1 : Rᵀ * R = 1 := (mem_orthogonalGroup_iff' (Fin 3) ℝ).1 hR
  refine ⟨?_, ?_⟩
  · calc adjugate R = (Rᵀ * R) * adjugate R := by rw [h1, Matrix.one_mul]
      _ = Rᵀ * (R * adjugate R) := by rw [Matrix.mul_assoc]
      _ = R.det • Rᵀ := by rw [mul_adjugate, Matrix.mul_smul, Matrix.mul_one]
  · have := congrArg det h1
    rwa [det_mul, det_transpose, det_one] at this

/-- The absolute value of an entry of an orthogonal matrix equals that of its cofactor. -/
lemma abs_eq_abs_adjugate {R : Matrix (Fin 3) (Fin 3) ℝ} (hR : R ∈ orthogonalGroup (Fin 3) ℝ)
    (a b : Fin 3) : |R a b| = |adjugate R b a| := by
  obtain ⟨hadj, hdet⟩ := adjugate_of_orth hR
  have hd1 : |R.det| = 1 := by
    have : |R.det| * |R.det| = 1 := by rw [← abs_mul, hdet, abs_one]
    nlinarith [abs_nonneg R.det]
  rw [hadj, Matrix.smul_apply, transpose_apply, smul_eq_mul, abs_mul, hd1, one_mul]

/-- Lemma 2 (⇒) for `i = j = 0`: edge 0 is horizontal with respect to axis 0. -/
lemma NCcase_of_zero (p q : Fin 3 → ℝ) (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 ≤ q i)
    (R : Matrix (Fin 3) (Fin 3) ℝ) (hR : R ∈ orthogonalGroup (Fin 3) ℝ)
    (hw : ∀ i, ∑ j, q j * |R i j| ≤ p i) (h0 : R 0 0 = 0) :
    stripOK (q 1) (q 2) (p 0) ∧ Fit2 (p 1) (p 2) (q 0) (stripH (q 1) (q 2) (p 0)) := by
  -- the floor entries are expressed through row 0 and column 0
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
  -- the vertical strip of height `p 0`
  obtain ⟨hOK, hH1⟩ := strip_min (hq 1) (hq 2) (hp 0).le (abs_nonneg (R 0 1)) (abs_nonneg (R 0 2))
    hrow w0
  have hH : 0 ≤ stripH (q 1) (q 2) (p 0) := by
    obtain ⟨c, d, hc, hd, -, -, hB⟩ := strip_exists (hq 1) (hq 2) (hp 0).le hOK
    exact le_trans (add_nonneg (mul_nonneg (hq 1) hd) (mul_nonneg (hq 2) hc)) hB
  -- the floor `p 1 × p 2`
  have k1 := mul_le_mul_of_nonneg_right hH1 (abs_nonneg (R 2 0))
  have k2 := mul_le_mul_of_nonneg_right hH1 (abs_nonneg (R 1 0))
  obtain ⟨hOK2, hH2⟩ := strip_min (hq 0) hH (hp 1).le (abs_nonneg (R 1 0)) (abs_nonneg (R 2 0))
    hcol (by nlinarith)
  exact ⟨hOK, hOK2, by nlinarith⟩

/-- **Lemma 2 (⇒).** A position with a zero entry `R i j = 0` yields a check of `NC`. -/
theorem NC_of_zero (p q : Fin 3 → ℝ) (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 ≤ q i)
    (R : Matrix (Fin 3) (Fin 3) ℝ) (hR : R ∈ orthogonalGroup (Fin 3) ℝ)
    (hw : ∀ i, ∑ j, q j * |R i j| ≤ p i) (i j : Fin 3) (h0 : R i j = 0) : NC p q := by
  refine ⟨Equiv.swap 0 i, Equiv.swap 0 j, ?_⟩
  have hR' : R.submatrix (Equiv.swap 0 i) (Equiv.swap 0 j) ∈ orthogonalGroup (Fin 3) ℝ := by
    rw [mem_orthogonalGroup_iff] at hR ⊢
    rw [transpose_submatrix, submatrix_mul_equiv, hR, submatrix_one_equiv]
  exact NCcase_of_zero (fun a => p (Equiv.swap 0 i a)) (fun b => q (Equiv.swap 0 j b))
    (fun _ => hp _) (fun _ => hq _) _ hR'
    (fun a => (Equiv.sum_comp (Equiv.swap 0 j)
      (fun b => q b * |R (Equiv.swap 0 i a) b|)).trans_le (hw _))
    (by simp [h0])

end Boxes
