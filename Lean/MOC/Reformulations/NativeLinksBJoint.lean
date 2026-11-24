import MOC.Reformulations.NativeLinksB

open Matrix Polynomial Module.End
open scoped ComplexStarModule
namespace MOC.Reformulations.NativeLinksB
noncomputable section

private theorem exists_joint_basis {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] {r n : ℕ}
    (T : Fin r → Module.End ℂ E) (hT : ∀ k, (T k).IsSymmetric)
    (hTC : Pairwise (Function.onFun Commute T)) (hn : Module.finrank ℂ E = n) :
    ∃ (v : OrthonormalBasis (Fin n) ℂ E) (μ : Fin n → Fin r → ℂ),
      ∀ j k, v j ∈ eigenspace (T k) (μ j k) := by
  classical
  let D := (k : Fin r) → (T k).Eigenvalues
  let ζ (μ : D) (k : Fin r) : ℂ := (μ k).val
  have hζ : Function.Injective ζ := fun p q h => funext fun k =>
    Subtype.ext (congrFun h k)
  let V (μ : D) := ⨅ k, eigenspace (T k) (ζ μ k)
  have ho : OrthogonalFamily ℂ (fun μ => V μ) (fun μ => (V μ).subtypeₗᵢ) :=
    (LinearMap.IsSymmetric.orthogonalFamily_iInf_eigenspaces (T := T) hT).comp hζ
  have hTop : (⨆ μ, V μ) = ⊤ := by
    apply top_unique
    rw [← LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hT hTC]
    refine iSup_le fun μ => ?_
    by_cases hμ : ∀ k, (T k).HasEigenvalue (μ k)
    · exact le_iSup V (fun k => ⟨μ k, hμ k⟩)
    · obtain ⟨k, hk⟩ := not_forall.mp hμ
      have hbot : eigenspace (T k) (μ k) = ⊥ := by
        simpa only [hasEigenvalue_iff, not_ne_iff] using hk
      exact (iInf_le _ k).trans (by rw [hbot]; exact bot_le)
  have hSum : DirectSum.IsInternal V :=
    ho.isInternal_iff.mpr (by rw [Submodule.orthogonal_eq_bot_iff, hTop])
  exact ⟨hSum.subordinateOrthonormalBasis hn ho,
    (fun j => ζ (hSum.subordinateOrthonormalBasisIndex hn j ho)),
    (fun j k => (Submodule.mem_iInf _).mp (hSum.subordinateOrthonormalBasis_subordinate hn j ho) k)⟩

/-- Commuting Hermitian matrix tuples have actual real joint spectra. -/
theorem exists_realJointSpectrum {n r : ℕ} (A : Fin r → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ k, (A k).IsHermitian) (hC : ∀ k l, Commute (A k) (A l)) :
    ∃ a, HasRealJointSpectrum A a := by
  classical
  let E := EuclideanSpace ℂ (Fin n)
  let T (k : Fin r) : Module.End ℂ E := toEuclideanLin (A k)
  have hT (k : Fin r) : (T k).IsSymmetric := isHermitian_iff_isSymmetric.mp (hA k)
  have hTC : Pairwise (Function.onFun Commute T) := by
    intro k l _
    exact (hC k l).map (Matrix.toLinAlgEquiv (EuclideanSpace.basisFun (Fin n) ℂ).toBasis)
  have hn : Module.finrank ℂ E = n := by rw [finrank_euclideanSpace, Fintype.card_fin]
  obtain ⟨v, μ, hv⟩ := exists_joint_basis T hT hTC hn
  let U := (EuclideanSpace.basisFun (Fin n) ℂ).toBasis.toMatrix v.toBasis
  have hU₀ := (EuclideanSpace.basisFun (Fin n) ℂ).toMatrix_orthonormalBasis_mem_unitary v
  have hU : IsUnitary U :=
    ⟨Matrix.mem_unitaryGroup_iff.mp hU₀, Matrix.mem_unitaryGroup_iff'.mp hU₀⟩
  refine ⟨fun j k => (μ j k).re, U, hU, ?_⟩
  intro k
  have hr (j : Fin n) : (((μ j k).re : ℝ) : ℂ) = μ j k := by
    have hEig : (T k).HasEigenvalue (μ j k) :=
      hasEigenvalue_of_hasEigenvector ⟨hv j k, v.toBasis.ne_zero j⟩
    have hConj : (starRingEnd ℂ) (μ j k) = μ j k :=
      (hT k).conj_eigenvalue_eq_self hEig
    apply Complex.ext
    · simp
    · have hIm := congrArg Complex.im hConj
      simp only [Complex.conj_im] at hIm
      simp only [Complex.ofReal_im]
      linarith only [hIm]
  have hEq : A k * U = U * diagonal (fun j => ((μ j k).re : ℂ)) := by
    ext i j : 1
    have h := congrArg (fun x : E => WithLp.equiv 2 (Fin n → ℂ) x i)
      (mem_eigenspace_iff.mp (hv j k))
    change WithLp.equiv 2 (Fin n → ℂ) (toEuclideanLin (A k) (v j)) i = _ at h
    rw [Matrix.piLp_equiv_toEuclideanLin_apply] at h
    change (A k *ᵥ (fun l => v j l)) i = (μ j k • v j) i at h
    change (A k *ᵥ (fun l => v j l)) i = μ j k * v j i at h
    rw [Matrix.mul_diagonal, Matrix.mul_apply, hr]
    simpa only [U, Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_repr, Matrix.mulVec, dotProduct,
      PiLp.smul_apply, smul_eq_mul, mul_comm (μ j k)] using h
  rw [← hEq, Matrix.mul_assoc, hU.1, Matrix.mul_one]

/-- Having real joint eigenvalue data is exactly self-adjointness and
internal commutation of the tuple. -/
theorem exists_realJointSpectrum_iff {n r : ℕ} (A : Fin r → Matrix (Fin n) (Fin n) ℂ) :
    (∃ a, HasRealJointSpectrum A a) ↔
      (∀ k, (A k).IsHermitian) ∧ ∀ k l, Commute (A k) (A l) := by
  constructor
  · rintro ⟨a, V, hV, h⟩
    let D (k : Fin r) := diagonal (fun j => (a j k : ℂ))
    have he (k : Fin r) : A k = V * D k * Vᴴ := h k
    constructor
    · intro k
      have hd : (D k).IsHermitian := by
        apply Matrix.isHermitian_diagonal_of_self_adjoint
        change star (fun j : Fin n => (a j k : ℂ)) = _
        funext j
        simp
      rw [he k]
      change (V * D k * Vᴴ)ᴴ = V * D k * Vᴴ
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        hd.eq, Matrix.mul_assoc]
    · intro k l
      have hd : Commute (D k) (D l) := by
        unfold D Commute SemiconjBy
        rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
        exact congrArg Matrix.diagonal (funext fun _ => mul_comm _ _)
      have hv (X Y : Matrix (Fin n) (Fin n) ℂ) :
          (V * X * Vᴴ) * (V * Y * Vᴴ) = V * (X * Y) * Vᴴ := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc Vᴴ V, hV.2, Matrix.one_mul]
      change A k * A l = A l * A k
      rw [he k, he l, hv, hv, hd.eq]
  · rintro ⟨hA, hC⟩
    exact exists_realJointSpectrum A hA hC

end
end MOC.Reformulations.NativeLinksB
