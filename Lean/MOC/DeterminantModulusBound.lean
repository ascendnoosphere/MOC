import MOC.MatchingPotential
import MOC.ModulusOrderTransfer
import MOC.Normal
import MOC.UnitaryPhaseCuts

/-! Drury's modulus bound for entrywise products and sums of normal matrices.
See S. W. Drury, Linear Algebra Appl. 199 (1994), 329–338, DOI 10.1016/0024-3795(94)90356-5. -/

open BigOperators Matrix

namespace MOC

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Positive row and column bounds on the entrywise factors give a product bound
on the determinant modulus. -/
private theorem norm_det_hadamard_le_assignment_scaling (U C : Matrix ι ι ℂ)
    (hU : IsUnitary U) (r c : ι → ℝ) (hr : ∀ i, 0 < r i) (hc : ∀ j, 0 < c j)
    (hw : ∀ i j, ‖C i j‖ ≤ r i * c j) :
    ‖(Matrix.of (fun i j => C i j * U i j)).det‖ ≤ (∏ i, r i) * (∏ j, c j) := by
  let z (i j : ι) : ℂ := C i j / (↑(r i * c j) : ℂ)
  let V : Matrix ι ι ℂ := Matrix.of fun i j => U i j * z i j
  have hz (i j : ι) : Complex.normSq (z i j) ≤ 1 := by
    have h : ‖z i j‖ ≤ 1 := by
      change ‖C i j / (↑(r i * c j) : ℂ)‖ ≤ 1
      rw [norm_div, Complex.norm_of_nonneg (mul_pos (hr i) (hc j)).le]
      exact (div_le_one (mul_pos (hr i) (hc j))).2 (hw i j)
    simpa only [Complex.normSq_eq_norm_sq, one_pow] using
      pow_le_pow_left₀ (norm_nonneg (z i j)) h 2
  have hdet : ‖V.det‖ ≤ 1 := by
    apply (sq_le_sq₀ (norm_nonneg V.det) zero_le_one).1
    simpa only [V, ← Complex.normSq_eq_norm_sq, one_pow] using
      unitary_entrywise_polydisc_det_normSq_le_one U hU z hz
  have hV : Matrix.of (fun i j => C i j * U i j) =
      diagonal (fun i => (r i : ℂ)) * V * diagonal (fun j => (c j : ℂ)) := by
    ext i j : 1
    simp only [Matrix.of_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
    change C i j * U i j = (r i : ℂ) * (U i j * z i j) * (c j : ℂ)
    have hs : (↑(r i * c j) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (mul_pos (hr i) (hc j)).ne'
    calc
      _ = (z i j * (↑(r i * c j) : ℂ)) * U i j := by
        rw [z, div_mul_cancel₀ _ hs]
      _ = _ := by rw [Complex.ofReal_mul]; ring
  have hR : 0 ≤ ∏ i, r i := Finset.prod_nonneg fun i _ => (hr i).le
  have hC : 0 ≤ ∏ j, c j := Finset.prod_nonneg fun j _ => (hc j).le
  rw [hV, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal,
    ← Complex.ofReal_prod _ r, ← Complex.ofReal_prod _ c, norm_mul, norm_mul,
    Complex.norm_of_nonneg hR, Complex.norm_of_nonneg hC, mul_right_comm]
  exact mul_le_of_le_one_right (mul_nonneg hR hC) hdet

/-- Some matching product of a complex entry matrix bounds the modulus of
its entrywise product determinant with a unitary matrix. -/
theorem norm_det_weighted_entries_le_matching (C U : Matrix ι ι ℂ) (hU : IsUnitary U) :
    ∃ σ : Equiv.Perm ι, ‖(Matrix.of fun i j => C i j * U i j).det‖ ≤
      ‖∏ j, C (σ j) j‖ := by
  classical
  let w (i j : ι) : ℝ := ‖C i j‖
  have hnorm (σ : Equiv.Perm ι) : ‖∏ j, C (σ j) j‖ = ∏ j, w (σ j) j :=
    norm_prod _ _
  by_cases hp : ∃ σ : Equiv.Perm ι, 0 < ∏ j, w (σ j) j
  · obtain ⟨r, c, hr, hc, hw, σ, hprod⟩ :=
      exists_assignment_product_scaling w (fun i j => norm_nonneg (C i j)) hp
    refine ⟨σ, ?_⟩
    rw [hnorm, ← hprod]
    exact norm_det_hadamard_le_assignment_scaling U C hU r c hr hc hw
  · have hz (σ : Equiv.Perm ι) : (∏ j, C (σ j) j) = 0 := by
      apply norm_eq_zero.mp
      refine le_antisymm ?_ (norm_nonneg _)
      rw [hnorm]
      exact le_of_not_gt (fun h => hp ⟨σ, h⟩)
    have hd : (Matrix.of fun i j => C i j * U i j).det = 0 := by
      rw [Matrix.det_apply']
      simp only [Matrix.of_apply, Finset.prod_mul_distrib, hz, zero_mul, mul_zero,
        Finset.sum_const_zero]
    refine ⟨Equiv.refl ι, ?_⟩
    simp only [hd, hz, norm_zero, le_refl]

private theorem modulus_unitary_det (U : Matrix ι ι ℂ) (hU : IsUnitary U) :
    ‖U.det‖ = 1 := by
  have h := congrArg Matrix.det hU.1
  rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at h
  have hs : Complex.normSq U.det = 1 := by
    rw [← Complex.ofReal_inj, Complex.ofReal_one, ← Complex.mul_conj]
    exact h
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  simpa only [Complex.sq_norm, one_pow] using hs

/-- In every finite order, the determinant of the sum in the spectral
coordinates has modulus at most that of some matching product. -/
theorem modulusConjecture_all_orders : ModulusConjecture ι := by
  intro a b U hU
  obtain ⟨σ, hσ⟩ := norm_det_weighted_entries_le_matching
    (Matrix.of fun i j => a i + b j) U hU
  refine ⟨σ, ?_⟩
  rw [determinantValue_eq_weightedEntryDet_div a b U hU, norm_div,
    modulus_unitary_det U hU, div_one]
  simpa only [Matrix.of_apply, matchingProduct] using hσ

/-- The same bound for two normal matrices and any enumerations of their eigenvalues. -/
theorem norm_det_add_le_matching_of_normal (A B : Matrix ι ι ℂ) (a b : ι → ℂ)
    (hA : IsStarNormal A) (hB : IsStarNormal B)
    (ha : A.charpoly.roots = (Finset.univ : Finset ι).val.map a)
    (hb : B.charpoly.roots = (Finset.univ : Finset ι).val.map b) :
    ∃ σ : Equiv.Perm ι, ‖(A + B).det‖ ≤ ‖matchingProduct a b σ‖ := by
  obtain ⟨a', V, hV, rfl⟩ := exists_unitary_diagonalization A hA
  obtain ⟨b', W, hW, rfl⟩ := exists_unitary_diagonalization B hB
  rw [roots_unitary_diagonalization a' hV] at ha
  rw [roots_unitary_diagonalization b' hW] at hb
  obtain ⟨e, rfl⟩ := exists_perm_of_equal_multisets a a' ha.symm
  obtain ⟨f, rfl⟩ := exists_perm_of_equal_multisets b b' hb.symm
  obtain ⟨σ, hσ⟩ := modulusConjecture_all_orders a' b' (Vᴴ * W) (relative_unitary V W hV hW)
  have hm : matchingProduct a' b' σ ∈ Set.range (matchingProduct (a' ∘ e) (b' ∘ f)) := by
    rw [matchingRange_relabel]
    exact Set.mem_range_self σ
  obtain ⟨τ, hτ⟩ := hm
  refine ⟨τ, ?_⟩
  rwa [hτ, determinantValue_relative a' b' V W hV]

end MOC
