import MOC.Blocks
import Mathlib.LinearAlgebra.Matrix.Trace

/-! A common spectral shift and inversion transport convex witnesses.
The trace-of-product inclusion uses the same Birkhoff law as in order three. -/

open BigOperators Matrix Finset

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem hull_of_common_factor {z z' : ℂ} {p q : Equiv.Perm ι → ℂ} {k : ℂ}
    (hz : z' = k * z) (hp : ∀ σ, q σ = k * p σ)
    (h : z ∈ convexHull ℝ (Set.range p)) : z' ∈ convexHull ℝ (Set.range q) := by
  have hset : LinearMap.mulLeft ℝ k '' Set.range p = Set.range q := by
    ext w
    constructor
    · rintro ⟨_, ⟨σ, rfl⟩, rfl⟩
      exact ⟨σ, hp σ⟩
    · rintro ⟨σ, rfl⟩
      exact ⟨p σ, ⟨σ, rfl⟩, (hp σ).symm⟩
  rw [← hset, ← LinearMap.image_convexHull]
  exact ⟨z, h, hz.symm⟩

omit [Fintype ι] [DecidableEq ι] in
theorem hull_common_factor_iff {z z' : ℂ} {p q : Equiv.Perm ι → ℂ} {k : ℂ}
    (hk : k ≠ 0) (hz : z' = k * z) (hp : ∀ σ, q σ = k * p σ) :
    z' ∈ convexHull ℝ (Set.range q) ↔ z ∈ convexHull ℝ (Set.range p) := by
  constructor
  · apply hull_of_common_factor (k := k⁻¹)
    · rw [hz, ← mul_assoc, inv_mul_cancel₀ hk, one_mul]
    · intro σ
      rw [hp, ← mul_assoc, inv_mul_cancel₀ hk, one_mul]
  · exact hull_of_common_factor hz hp

/-- Shared inversion in the difference convention. Opposite shifts permit any finite pole. -/
theorem holds_inv_iff (a c : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (ha : ∀ i, a i ≠ 0) (hc : ∀ i, c i ≠ 0) :
    Holds (fun i => (a i)⁻¹) (fun i => -(c i)⁻¹) U ↔ Holds a (fun i => -c i) U := by
  let A := diagonal a
  let C := U * diagonal c * Uᴴ
  let Ai := diagonal (fun i => (a i)⁻¹)
  let Ci := U * diagonal (fun i => (c i)⁻¹) * Uᴴ
  have hA : A * Ai = 1 := by
    simp [A, Ai, Matrix.diagonal_mul_diagonal, mul_inv_cancel₀, ha]
  have hcdiag : diagonal (fun i => (c i)⁻¹) * diagonal c = 1 := by
    simp [Matrix.diagonal_mul_diagonal, inv_mul_cancel₀, hc]
  have hC : Ci * C = 1 := by
    unfold C Ci
    calc
      _ = U * (diagonal (fun i => (c i)⁻¹) * (Uᴴ * U) * diagonal c) * Uᴴ := by
        simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hU.2, Matrix.mul_one, hcdiag, Matrix.mul_one, hU.1]
  have he : A * (Ai - Ci) * C = -(A - C) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hA, Matrix.one_mul, Matrix.mul_assoc A Ci, hC,
      Matrix.mul_one, neg_sub]
  have had : A.det = ∏ i, a i := Matrix.det_diagonal
  have hcd : C.det = ∏ i, c i := by
    rw [det_unitary_conjugation U _ hU, Matrix.det_diagonal]
  have hk : (∏ i, a i) * (∏ i, c i) ≠ 0 := mul_ne_zero (prod_ne_zero_iff.mpr fun i _ => ha i)
    (prod_ne_zero_iff.mpr fun i _ => hc i)
  let k : ℂ := (-1) ^ Fintype.card ι / ((∏ i, a i) * ∏ i, c i)
  have hk' : k ≠ 0 := div_ne_zero (pow_ne_zero _ (by norm_num)) hk
  apply hull_common_factor_iff hk'
  · have hd := congrArg Matrix.det he
    rw [Matrix.det_mul, Matrix.det_mul, had, hcd, ← neg_one_smul ℂ (A - C), Matrix.det_smul] at hd
    have hda : (Ai - Ci).det = k * (A - C).det := by
      dsimp [k]
      rw [div_mul_eq_mul_div]
      apply (eq_div_iff hk).mpr
      convert hd using 1
      ring
    simpa [A, C, Ai, Ci, determinantValue, sub_eq_add_neg, ← Matrix.diagonal_neg,
      Matrix.mul_neg, Matrix.neg_mul] using hda
  · intro σ
    unfold matchingProduct
    change (∏ j, ((a (σ j))⁻¹ + -(c j)⁻¹)) = k * ∏ j, (a (σ j) + -c j)
    have hterm (j : ι) :
        (a (σ j))⁻¹ + -(c j)⁻¹ = (-1) * (a (σ j) + -c j) / (a (σ j) * c j) := by
      field_simp [ha (σ j), hc j]
    simp_rw [hterm, Finset.prod_div_distrib, Finset.prod_mul_distrib]
    rw [Finset.prod_const, Finset.card_univ, Equiv.prod_comp σ a]
    dsimp [k]
    ring

/-- The trace case recorded in de Oliveira's research problem (bibliography entry 3). -/
theorem trace_mul_mem_hull (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U) :
    (diagonal a * (U * diagonal b * Uᴴ)).trace ∈
      convexHull ℝ (Set.range (fun σ : Equiv.Perm ι => ∑ j, a (σ j) * b j)) := by
  let vertex (σ : Equiv.Perm ι) := ∑ j, a (σ j) * b j
  change _ ∈ convexHull ℝ (Set.range vertex)
  obtain ⟨w, hw, hs, hm⟩ := exists_singleton_weights U hU
  refine mem_convexHull_of_exists_fintype w vertex hw hs (fun σ => ⟨σ, rfl⟩) ?_
  simp only [Complex.real_smul, vertex, mul_sum]
  rw [Finset.sum_comm]
  have hj (j : ι) :
      ∑ σ, (w σ : ℂ) * (a (σ j) * b j) = ∑ i, (Complex.normSq (U i j) : ℂ) * (a i * b j) := by
    rw [sum_weighted_evaluation (fun σ => (w σ : ℂ)) j (fun i => a i * b j)]
    simp only [hm]
  simp only [hj]
  rw [Finset.sum_comm]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, Complex.normSq_eq_conj_mul_self, mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [starRingEnd_apply]
  ring

/-- Attained determinant values for fixed ordered spectra. -/
def determinantRange (a b : ι → ℂ) : Set ℂ :=
  { z | ∃ U : Matrix ι ι ℂ, IsUnitary U ∧ determinantValue a b U = z }

end

end MOC
