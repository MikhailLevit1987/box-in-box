import Mathlib

/-!
# Theorem of the alternative (Motzkin) for three inequalities in `ℝ³`

Either the system `bᵢ · z < cᵢ` (`i ∈ S`) is solvable, or there is a nonzero `μ ≥ 0` supported on
`S` with `∑ μᵢ bᵢ = 0` and `∑ μᵢ cᵢ ≤ 0`.

Proof: separation of the origin from the image of the standard simplex (Hahn–Banach,
`geometric_hahn_banach_compact_closed`) for the points `(bᵢ, −cᵢ)` and `(0, −1)` in `ℝ³ × ℝ`.
-/

namespace Boxes

open Matrix

theorem motzkin (b : Fin 3 → (Fin 3 → ℝ)) (c : Fin 3 → ℝ) :
    (∃ z, ∀ i, b i ⬝ᵥ z < c i) ∨
    (∃ μ : Fin 3 → ℝ, (∀ i, 0 ≤ μ i) ∧ (∃ i, 0 < μ i) ∧ ∑ i, μ i • b i = 0 ∧
      ∑ i, μ i * c i ≤ 0) := by
  classical
  let u : Option (Fin 3) → (Fin 3 → ℝ) × ℝ := fun k => Option.elim k (0, -1) (fun i => (b i, -c i))
  let L := Fintype.linearCombination ℝ u
  have hL : ∀ w, L w = ∑ k, w k • u k := fun w => Fintype.linearCombination_apply ℝ u w
  set K := L '' stdSimplex ℝ (Option (Fin 3)) with hK
  by_cases h0 : ((0 : (Fin 3 → ℝ) × ℝ)) ∈ K
  · right
    obtain ⟨w, ⟨hw0, hw1⟩, hw⟩ := h0
    rw [hL, Fintype.sum_option] at hw
    have h1 := congrArg Prod.fst hw
    have h2 := congrArg Prod.snd hw
    simp only [u, Option.elim, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      Prod.fst_sum, Prod.snd_sum, Prod.fst_zero, Prod.snd_zero, smul_zero, zero_add,
      smul_eq_mul] at h1 h2
    rw [Fintype.sum_option] at hw1
    have hsum : ∑ i, w (some i) * c i = -w none := by
      have : ∑ i, w (some i) * -c i = -(∑ i, w (some i) * c i) := by
        rw [← Finset.sum_neg_distrib]; simp [mul_neg]
      linarith
    refine ⟨fun i => w (some i), fun i => hw0 _, ?_, h1, ?_⟩
    · by_contra hcon
      push Not at hcon
      have hz : ∀ i, w (some i) = 0 := fun i => le_antisymm (hcon i) (hw0 _)
      simp only [hz, Finset.sum_const_zero, add_zero, zero_mul] at hw1 hsum
      linarith
    · linarith [hw0 none]
  · left
    have hLc : Continuous L := L.continuous_of_finiteDimensional
    have hKc : IsCompact K := (isCompact_stdSimplex ℝ (Option (Fin 3))).image hLc
    have hKv : Convex ℝ K := (convex_stdSimplex ℝ (Option (Fin 3))).linear_image L
    obtain ⟨f, s1, s2, hs1, hs12, hs2⟩ := geometric_hahn_banach_compact_closed hKv hKc
      (convex_singleton 0) isClosed_singleton (Set.disjoint_singleton_right.2 h0)
    have hf0 : s2 < 0 := by simpa using hs2 0 rfl
    have hneg : ∀ k, f (u k) < 0 := by
      intro k
      have hk : u k ∈ K := ⟨Pi.single k 1, single_mem_stdSimplex ℝ k, by
        rw [hL]; simp [Pi.single_apply]⟩
      linarith [hs1 _ hk]
    set τ := f (0, 1) with hτdef
    set z : Fin 3 → ℝ := fun m => f (Pi.single m 1, 0) with hz
    have hf : ∀ x σ, f (x, σ) = x ⬝ᵥ z + σ * τ := by
      intro x σ
      have hx : (x, σ) = ∑ m, x m • ((Pi.single m 1 : Fin 3 → ℝ), (0 : ℝ)) +
          σ • ((0 : Fin 3 → ℝ), (1 : ℝ)) := by
        refine Prod.ext ?_ ?_
        · ext m
          simp [Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
        · simp [Prod.snd_sum]
      rw [hx, map_add, map_sum]
      simp only [map_smul, smul_eq_mul]
      simp [dotProduct, z, τ]
    have hτ : 0 < τ := by
      have := hneg none
      simp only [u, Option.elim, hf, zero_dotProduct, zero_add] at this
      linarith
    refine ⟨τ⁻¹ • z, fun i => ?_⟩
    have := hneg (some i)
    simp only [u, Option.elim, hf] at this
    rw [dotProduct_smul, smul_eq_mul, inv_mul_lt_iff₀ hτ]
    linarith

/-- Motzkin's alternative for a subset `S` of indices. -/
theorem motzkinS (S : Finset (Fin 3)) (b : Fin 3 → (Fin 3 → ℝ)) (c : Fin 3 → ℝ) :
    (∃ z, ∀ i ∈ S, b i ⬝ᵥ z < c i) ∨
    (∃ μ : Fin 3 → ℝ, (∀ i, 0 ≤ μ i) ∧ (∀ i ∉ S, μ i = 0) ∧ (∃ i, 0 < μ i) ∧
      ∑ i, μ i • b i = 0 ∧ ∑ i, μ i * c i ≤ 0) := by
  classical
  rcases motzkin (fun i => if i ∈ S then b i else 0) (fun i => if i ∈ S then c i else 1) with
    ⟨z, hz⟩ | ⟨μ, hμ0, ⟨i0, hi0⟩, hμb, hμc⟩
  · left
    exact ⟨z, fun i hi => by simpa [hi] using hz i⟩
  · right
    refine ⟨fun i => if i ∈ S then μ i else 0, fun i => ?_, fun i hi => by simp [hi], ?_, ?_, ?_⟩
    · show 0 ≤ (if i ∈ S then μ i else 0)
      split_ifs
      · exact hμ0 i
      · exact le_refl 0
    · -- outside `S` the contribution to `∑ μ c'` is positive, so some `μᵢ` with `i ∈ S` is positive
      have split : ∑ i, μ i * (if i ∈ S then c i else 1) =
          ∑ i, (if i ∈ S then μ i else 0) * c i + ∑ i, (if i ∈ S then 0 else μ i) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        split_ifs <;> simp
      by_contra hcon
      push Not at hcon
      have hS : ∀ i ∈ S, μ i = 0 := fun i hi => le_antisymm (by simpa [hi] using hcon i) (hμ0 i)
      have h1 : ∑ i, (if i ∈ S then μ i else 0) * c i = 0 :=
        Finset.sum_eq_zero fun i _ => by split_ifs with h <;> simp [hS i, h]
      have h2 : ∑ i, (if i ∈ S then 0 else μ i) ≤ 0 := by linarith
      have h3 : ∀ i, (if i ∈ S then 0 else μ i) = 0 := by
        intro i
        refine le_antisymm ?_ (by split_ifs <;> simp [hμ0 i])
        have hnn : ∀ j ∈ Finset.univ, 0 ≤ (if j ∈ S then 0 else μ j) := by
          intro j _; split_ifs <;> simp [hμ0 j]
        have := Finset.single_le_sum hnn (Finset.mem_univ i)
        linarith
      have := h3 i0
      by_cases h : i0 ∈ S
      · linarith [hS i0 h]
      · simp [h] at this; linarith
    · rw [← hμb]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases h : i ∈ S <;> simp [h]
    · have split : ∑ i, μ i * (if i ∈ S then c i else 1) =
          ∑ i, (if i ∈ S then μ i else 0) * c i + ∑ i, (if i ∈ S then 0 else μ i) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        split_ifs <;> simp
      have hnn : 0 ≤ ∑ i, (if i ∈ S then 0 else μ i) :=
        Finset.sum_nonneg fun j _ => by split_ifs <;> simp [hμ0 j]
      linarith

end Boxes
