import MOC.Reformulations.FirstHermitian
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Determinant and log-determinant bounds for Hermitian sums. The real log
is used only on a strictly positive determinant. -/

open BigOperators Matrix
open scoped ComplexOrder

namespace MOC.Reformulations
noncomputable section

/-- The objective is the product of the Hermitian sum's real
eigenvalues, in any ordering. -/
theorem nativeHermitianSumEigenvalueHull {n : ℕ} (A B U : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hU : IsUnitary U) :
    let hD := hA.add (Matrix.isHermitian_mul_mul_conjTranspose U hB)
    (∏ i, (hD.eigenvalues i : ℂ)) ∈ convexHull ℝ
      (Set.range (matchingProduct
        (fun i => (hA.eigenvalues i : ℂ)) (fun i => (hB.eigenvalues i : ℂ)))) := by
  intro hD
  have he : (A + U * B * Uᴴ).det = ∏ i, (hD.eigenvalues i : ℂ) :=
    hD.det_eq_prod_eigenvalues
  rw [← he]
  exact hermitianMatrixHull A B U hA hB hU

private theorem real_part_matching {n : ℕ} (a b : Fin n → ℝ)
    (σ : Equiv.Perm (Fin n)) :
    (matchingProduct (fun i => (a i : ℂ)) (fun i => (b i : ℂ)) σ).re =
      ∏ i, (a (σ i) + b i) := by
  unfold matchingProduct
  simp only [← Complex.ofReal_add, ← Complex.ofReal_prod, Complex.ofReal_re]

/-- The lower and upper bounds with witnessing permutations.
They are equivalent to the minimum/maximum formulation because the
permutation set is finite. -/
theorem nativeDeterminantBarrier {n : ℕ} (A B U : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.PosDef) (hB : B.PosDef) (hU : IsUnitary U) :
    let a := hA.isHermitian.eigenvalues
    let b := hB.isHermitian.eigenvalues
    let d := (A + U * B * Uᴴ).det.re
    0 < d ∧ ∃ σ τ : Equiv.Perm (Fin n),
      -(∑ i, Real.log (a (τ i) + b i)) ≤ -Real.log d ∧
        -Real.log d ≤ -(∑ i, Real.log (a (σ i) + b i)) := by
  classical
  intro a b d
  let p (σ : Equiv.Perm (Fin n)) := ∏ i, (a (σ i) + b i)
  have hp (σ : Equiv.Perm (Fin n)) : 0 < p σ := by
    exact Finset.prod_pos (fun i _ => add_pos (hA.eigenvalues_pos _) (hB.eigenvalues_pos _))
  have hd : d ∈ convexHull ℝ (Set.range p) := by
    have hm := hermitianMatrixHull A B U hA.isHermitian hB.isHermitian hU
    have hset : Complex.reLm '' (Set.range (matchingProduct
        (fun i => (a i : ℂ)) (fun i => (b i : ℂ)))) = Set.range p := by
      have he : Complex.reLm ∘ matchingProduct (fun i => (a i : ℂ))
          (fun i => (b i : ℂ)) = p := funext (real_part_matching a b)
      rw [← Set.range_comp, he]
    rw [← hset, ← Complex.reLm.image_convexHull]
    exact ⟨_, hm, rfl⟩
  obtain ⟨σ, _, hσ⟩ := Finset.exists_min_image Finset.univ p Finset.univ_nonempty
  obtain ⟨τ, _, hτ⟩ := Finset.exists_max_image Finset.univ p Finset.univ_nonempty
  have hlow : p σ ≤ d := by
    apply convexHull_min _ (convex_Ici (𝕜 := ℝ) (p σ)) hd
    rintro z ⟨ρ, rfl⟩
    exact hσ ρ (Finset.mem_univ _)
  have hhigh : d ≤ p τ := by
    apply convexHull_min _ (convex_Iic (𝕜 := ℝ) (p τ)) hd
    rintro z ⟨ρ, rfl⟩
    exact hτ ρ (Finset.mem_univ _)
  have hpos : 0 < d := (hp σ).trans_le hlow
  have hlog (ρ : Equiv.Perm (Fin n)) : Real.log (p ρ) = ∑ i, Real.log (a (ρ i) + b i) :=
    Real.log_prod _ _ (fun i _ => (add_pos (hA.eigenvalues_pos _) (hB.eigenvalues_pos _)).ne')
  refine ⟨hpos, σ, τ, ?_, ?_⟩
  · rw [← hlog]
    exact neg_le_neg (Real.log_le_log hpos hhigh)
  · rw [← hlog]
    exact neg_le_neg (Real.log_le_log (hp σ) hlow)

end
end MOC.Reformulations
