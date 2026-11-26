import MOC.PfaffianSkewCongruence
import MOC.PfaffianStandardSkewBlocks
import MOC.SkewUnitaryDeterminant

/-! The Pfaffian square identity and the modulus bound on the support graph. -/

open BigOperators Matrix

namespace MOC

noncomputable section

private theorem symplecticMatrix_eq_standardSkewBlocks (n : ℕ) :
    standardSymplecticMatrix n = standardSkewBlocks n := rfl

/-- The square of the permutation Pfaffian is the determinant of a
complex skew-symmetric matrix. The matrix may be singular. -/
theorem complexPfaffian_sq {n : ℕ} (K : Matrix (PfaffianIndex n) (PfaffianIndex n) ℂ)
    (hskew : ∀ i j, K j i = -K i j) : complexPfaffian K ^ 2 = K.det := by
  by_cases hK : K.det = 0
  · rw [complexPfaffian_eq_zero_of_det_eq_zero K hskew hK, hK]
    norm_num
  · obtain ⟨S, hS, he⟩ := exists_congr_standardSymplecticMatrix K hskew hK
    have hpf : S.det * complexPfaffian K = 1 := calc
      _ = complexPfaffian (Sᵀ * K * S) := (complexPfaffian_congr K S).symm
      _ = 1 := by rw [he, symplecticMatrix_eq_standardSkewBlocks,
        complexPfaffian_standardSkewBlocks]
    have hd : S.det ^ 2 * K.det = 1 := by
      have h := congrArg Matrix.det he
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, standardSymplecticMatrix_det] at h
      linear_combination h
    apply mul_left_cancel₀ (pow_ne_zero 2 hS)
    rw [← mul_pow, hpf, one_pow, hd]

/-- The normalized Pfaffian with an arbitrary symmetric edge kernel is
bounded in modulus by a matching supported on the skew unitary. -/
theorem pfaffian_norm_le_supported_matching {n : ℕ}
    (J Z : Matrix (PfaffianIndex n) (PfaffianIndex n) ℂ) (hJ : IsUnitary J)
    (hskew : ∀ i j, J j i = -J i j) (hZ : ∀ i j, Z i j = Z j i) :
    ∃ σ : Equiv.Perm (PfaffianIndex n),
      (∀ i : Fin n, J (σ (i, 0)) (σ (i, 1)) ≠ 0) ∧
      ‖complexPfaffian (Matrix.of fun i j => J i j * Z i j) / complexPfaffian J‖ ≤
        ‖∏ i : Fin n, Z (σ (i, 0)) (σ (i, 1))‖ :=
  pfaffian_norm_le_supported_matching_of_det_sq J Z hJ hskew hZ complexPfaffian_sq

/-- For additive edge labels the graph bound applies to the skew pencil. -/
theorem pfaffian_additive_pencil_norm_le_matching {n : ℕ}
    (J : Matrix (PfaffianIndex n) (PfaffianIndex n) ℂ) (hJ : IsUnitary J)
    (hskew : ∀ i j, J j i = -J i j) (z : PfaffianIndex n → ℂ) :
    ∃ σ : Equiv.Perm (PfaffianIndex n),
      (∀ i : Fin n, J (σ (i, 0)) (σ (i, 1)) ≠ 0) ∧
      ‖complexPfaffian (J * Matrix.diagonal z + Matrix.diagonal z * J) / complexPfaffian J‖ ≤
        ‖∏ i : Fin n, (z (σ (i, 0)) + z (σ (i, 1)))‖ := by
  let Z : Matrix (PfaffianIndex n) (PfaffianIndex n) ℂ := Matrix.of fun i j => z i + z j
  have hmat : (Matrix.of fun i j => J i j * Z i j) =
      J * Matrix.diagonal z + Matrix.diagonal z * J := by
    ext i j : 1
    simp only [Z, Matrix.of_apply, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
    ring
  obtain ⟨σ, hs, hb⟩ := pfaffian_norm_le_supported_matching J Z hJ hskew
    (fun i j => add_comm (z i) (z j))
  exact ⟨σ, hs, by simpa only [hmat, Z, Matrix.of_apply] using hb⟩

/-- The normalized skew pencil is stable on the product of open upper
half-planes. -/
theorem normalized_complexPfaffian_ne_zero_of_im_pos {n : ℕ}
    (J : Matrix (PfaffianIndex n) (PfaffianIndex n) ℂ) (hJ : IsUnitary J)
    (hskew : Jᵀ = -J) (z : PfaffianIndex n → ℂ) (hz : ∀ i, 0 < (z i).im) :
    complexPfaffian (J * Matrix.diagonal z + Matrix.diagonal z * J) / complexPfaffian J ≠ 0 :=
  normalizedPfaffian_ne_zero_of_im_pos complexPfaffian
    (fun K hK => complexPfaffian_sq K fun i j =>
      congrArg (fun A : Matrix _ _ ℂ => A i j) hK) J hJ hskew z hz

end

end MOC
