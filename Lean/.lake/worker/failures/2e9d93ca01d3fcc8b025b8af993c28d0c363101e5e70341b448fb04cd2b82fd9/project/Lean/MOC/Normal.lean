import MOC.Core
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-! The normal-matrix formulation, with eigenvalues counted with algebraic multiplicity. -/

open Matrix Polynomial Module.End
open scoped ComplexStarModule

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

set_option maxHeartbeats 1200000 in
/-- The commuting Hermitian parts of a complex normal matrix give a common eigenbasis. -/
theorem exists_unitary_diagonalization (M : Matrix ι ι ℂ) (hM : IsStarNormal M) :
    ∃ (a : ι → ℂ) (U : Matrix ι ι ℂ), IsUnitary U ∧ M = U * diagonal a * Uᴴ := by
  classical
  let R := (ℜ M : Matrix ι ι ℂ)
  let J := (ℑ M : Matrix ι ι ℂ)
  let A : Module.End ℂ (EuclideanSpace ℂ ι) := toEuclideanLin R
  let B : Module.End ℂ (EuclideanSpace ℂ ι) := toEuclideanLin J
  have hA : A.IsSymmetric :=
    isHermitian_iff_isSymmetric.mp (show R.IsHermitian from (ℜ M).property)
  have hB : B.IsSymmetric :=
    isHermitian_iff_isSymmetric.mp (show J.IsHermitian from (ℑ M).property)
  have hRJs : Commute R J := by
    have h : Commute (star M) M := hM.star_comm_self
    have hs : Commute (M + star M) (M - star M) :=
      ((Commute.refl M).sub_right h.symm).add_left (h.sub_right (Commute.refl (star M)))
    simpa only [R, J, realPart_apply_coe, imaginaryPart_apply_coe] using
      (((hs.smul_left (2⁻¹ : ℝ)).smul_right (2⁻¹ : ℝ)).smul_right (-Complex.I))
  have hAB : Commute A B := by
    exact hRJs.map (Matrix.toLinAlgEquiv (EuclideanSpace.basisFun ι ℂ).toBasis)
  let ζ (p : B.Eigenvalues × A.Eigenvalues) : ℂ × ℂ := (p.1.val, p.2.val)
  have hζ : Function.Injective ζ := fun p q h =>
    Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))
  let V (p : B.Eigenvalues × A.Eigenvalues) := eigenspace A (ζ p).2 ⊓ eigenspace B (ζ p).1
  have hOrth : OrthogonalFamily ℂ (fun p => V p) (fun p => (V p).subtypeₗᵢ) :=
    (hA.orthogonalFamily_eigenspace_inf_eigenspace hB).comp hζ
  have hTop : (⨆ p, V p) = ⊤ := by
    apply top_unique
    rw [← hA.iSup_iSup_eigenspace_inf_eigenspace_eq_top_of_commute hB hAB]
    refine iSup_le fun x => iSup_le fun y => ?_
    by_cases hx : A.HasEigenvalue x
    · by_cases hy : B.HasEigenvalue y
      · exact le_iSup V (⟨⟨y, hy⟩, ⟨x, hx⟩⟩ : B.Eigenvalues × A.Eigenvalues)
      · rw [hasEigenvalue_iff, not_ne_iff] at hy
        simp [hy]
    · rw [hasEigenvalue_iff, not_ne_iff] at hx
      simp [hx]
  have hSum : DirectSum.IsInternal V :=
    hOrth.isInternal_iff.mpr (by rw [Submodule.orthogonal_eq_bot_iff, hTop])
  let e : Fin (Fintype.card ι) ≃ ι := Fintype.equivOfCardEq (Fintype.card_fin _)
  let v := (hSum.subordinateOrthonormalBasis finrank_euclideanSpace hOrth).reindex e
  let μ (j : ι) := ζ (hSum.subordinateOrthonormalBasisIndex finrank_euclideanSpace (e.symm j) hOrth)
  let a (j : ι) : ℂ := (μ j).2 + Complex.I * (μ j).1
  let U := (EuclideanSpace.basisFun ι ℂ).toBasis.toMatrix v.toBasis
  have hU₀ := (EuclideanSpace.basisFun ι ℂ).toMatrix_orthonormalBasis_mem_unitary v
  have hU : IsUnitary U :=
    ⟨Matrix.mem_unitaryGroup_iff.mp hU₀, Matrix.mem_unitaryGroup_iff'.mp hU₀⟩
  refine ⟨a, U, hU, ?_⟩
  have hsplit : toEuclideanLin M = A + Complex.I • B := by
    have hs : R + Complex.I • J = M := realPart_add_I_smul_imaginaryPart M
    change toEuclideanLin M = toEuclideanLin R + Complex.I • toEuclideanLin J
    rw [← map_smul, ← map_add, hs]
  have hv (j : ι) : toEuclideanLin M (v j) = a j • v j := by
    have hm : v j ∈ eigenspace A (μ j).2 ⊓ eigenspace B (μ j).1 := by
      simpa only [v, μ, OrthonormalBasis.reindex_apply] using
        hSum.subordinateOrthonormalBasis_subordinate finrank_euclideanSpace (e.symm j) hOrth
    rw [hsplit, LinearMap.add_apply, LinearMap.smul_apply, mem_eigenspace_iff.mp hm.1,
      mem_eigenspace_iff.mp hm.2, a, add_smul, mul_smul]
  have hMU : M * U = U * diagonal a := by
    ext i j : 1
    have h := congrArg (fun x : EuclideanSpace ℂ ι => x i) (hv j)
    simpa only [Matrix.mul_apply, Matrix.mul_diagonal, U, Basis.toMatrix_apply,
      OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.coe_toBasis,
      EuclideanSpace.basisFun_repr, Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct,
      PiLp.smul_apply, smul_eq_mul, mul_comm (a j)] using h
  rw [← hMU, Matrix.mul_assoc, hU.1, Matrix.mul_one]

/-- Eigenvalues of a diagonalization, including repetitions, are the characteristic roots. -/
theorem roots_unitary_diagonalization (a : ι → ℂ) {U : Matrix ι ι ℂ} (hU : IsUnitary U) :
    (U * diagonal a * Uᴴ).charpoly.roots = (Finset.univ : Finset ι).val.map a := by
  classical
  let Cmap : Matrix ι ι ℂ →+* Matrix ι ι ℂ[X] := (Polynomial.C : ℂ →+* ℂ[X]).mapMatrix
  have hc : Commute (Matrix.scalar ι (X : ℂ[X])) (Cmap U) :=
    Matrix.scalar_commute _ (Commute.all _) _
  have hUU : Cmap U * Cmap Uᴴ = 1 := by rw [← Cmap.map_mul, hU.1, Cmap.map_one]
  have hm : (U * diagonal a * Uᴴ).charmatrix = Cmap U * (diagonal a).charmatrix * Cmap Uᴴ := by
    change Matrix.scalar ι X - Cmap (U * diagonal a * Uᴴ) =
      Cmap U * (Matrix.scalar ι X - Cmap (diagonal a)) * Cmap Uᴴ
    rw [Cmap.map_mul, Cmap.map_mul, Matrix.mul_sub, Matrix.sub_mul,
      ← hc.eq, Matrix.mul_assoc (Matrix.scalar ι X), hUU, Matrix.mul_one]
  have hd : (diagonal a).charmatrix = diagonal (fun j => X - C (a j)) := by
    ext i j : 1
    by_cases h : i = j
    · subst j
      simp
    · simp [h, Matrix.diagonal_apply_ne]
  have hd' : ((Cmap U).det * (Cmap Uᴴ).det) = 1 := by
    rw [← Matrix.det_mul, hUU, Matrix.det_one]
  rw [Matrix.charpoly, hm, Matrix.det_mul, Matrix.det_mul, mul_right_comm, hd', one_mul,
    hd, Matrix.det_diagonal]
  change ((Finset.univ : Finset ι).val.map ((fun z : ℂ => X - C z) ∘ a)).prod.roots = _
  rw [← Multiset.map_map, Polynomial.roots_multiset_prod_X_sub_C]

omit [DecidableEq ι] in
/-- Equal eigenvalue multisets admit a bijection of their index sets preserving the values. -/
private theorem exists_perm_of_equal_multisets (a a' : ι → ℂ)
    (h : (Finset.univ : Finset ι).val.map a = Finset.univ.val.map a') :
    ∃ e : Equiv.Perm ι, a = a' ∘ e := by
  classical
  have hr (z : ℂ) : Fintype.card {i // a i = z} = Fintype.card {i // a' i = z} := by
    have hc := congrArg (Multiset.count z) h
    rw [Multiset.count_map, Multiset.count_map] at hc
    simpa [← Finset.filter_val, Fintype.card_subtype, eq_comm] using hc
  let e (z : ℂ) : {i // a i = z} ≃ {i // a' i = z} := Fintype.equivOfCardEq (hr z)
  exact ⟨Equiv.ofFiberEquiv e, funext fun i => (Equiv.ofFiberEquiv_map e i).symm⟩

omit [DecidableEq ι] in
/-- Independent relabelings of the two spectra preserve the set of matching products. -/
theorem matchingRange_relabel (a b : ι → ℂ) (e f : Equiv.Perm ι) :
    Set.range (matchingProduct (a ∘ e) (b ∘ f)) = Set.range (matchingProduct a b) := by
  have hp (σ : Equiv.Perm ι) : matchingProduct (a ∘ e) (b ∘ f) σ =
      matchingProduct a b ((f.symm.trans σ).trans e) := by
    unfold matchingProduct
    rw [← Equiv.prod_comp f (fun j => a (((f.symm.trans σ).trans e) j) + b j)]
    simp
  ext z
  constructor
  · rintro ⟨σ, rfl⟩
    exact ⟨_, (hp σ).symm⟩
  · rintro ⟨σ, rfl⟩
    refine ⟨(f.trans σ).trans e.symm, ?_⟩
    rw [hp]
    congr 1
    ext j
    simp

/-- MOC for two arbitrary normal matrices and any enumerations of their characteristic roots. -/
def NormalConjecture (ι : Type*) [Fintype ι] [DecidableEq ι] : Prop :=
  ∀ (A B : Matrix ι ι ℂ) (a b : ι → ℂ), IsStarNormal A → IsStarNormal B →
    A.charpoly.roots = (Finset.univ : Finset ι).val.map a →
    B.charpoly.roots = (Finset.univ : Finset ι).val.map b →
    (A + B).det ∈ convexHull ℝ (Set.range (matchingProduct a b))

private theorem isStarNormal_unitary_diagonalization (a : ι → ℂ)
    {U : Matrix ι ι ℂ} (hU : IsUnitary U) : IsStarNormal (U * diagonal a * Uᴴ) := by
  have hc : Commute (diagonal a) (diagonal (star ∘ a)) := by
    rw [Commute, SemiconjBy, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    exact congrArg Matrix.diagonal (funext fun i => mul_comm (a i) (star (a i)))
  have hm (X Y : Matrix ι ι ℂ) :
      (U * X * Uᴴ) * (U * Y * Uᴴ) = U * (X * Y) * Uᴴ := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᴴ U, hU.2, Matrix.one_mul]
  constructor
  change Commute (U * diagonal a * Uᴴ)ᴴ (U * diagonal a * Uᴴ)
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.diagonal_conjTranspose]
  change (U * (diagonal (star ∘ a) * Uᴴ)) * (U * diagonal a * Uᴴ) =
    (U * diagonal a * Uᴴ) * (U * (diagonal (star ∘ a) * Uᴴ))
  rw [← Matrix.mul_assoc U (diagonal (star ∘ a)), hm, hm, hc.eq]

/-- The spectral formulation covers exactly the assertion for arbitrary normal summands. -/
theorem conjecture_iff_normalConjecture : Conjecture ι ↔ NormalConjecture ι := by
  constructor
  · intro h A B a b hA hB ha hb
    obtain ⟨a', V, hV, rfl⟩ := exists_unitary_diagonalization A hA
    obtain ⟨b', W, hW, rfl⟩ := exists_unitary_diagonalization B hB
    rw [roots_unitary_diagonalization a' hV] at ha
    rw [roots_unitary_diagonalization b' hW] at hb
    obtain ⟨e, rfl⟩ := exists_perm_of_equal_multisets a a' ha.symm
    obtain ⟨f, rfl⟩ := exists_perm_of_equal_multisets b b' hb.symm
    rw [matchingRange_relabel]
    rw [determinantValue_relative a' b' V W hV]
    exact h a' b' (Vᴴ * W) (relative_unitary V W hV hW)
  · intro h a b U hU
    let V : Matrix ι ι ℂ := 1
    have hV : IsUnitary V := by simp [V, IsUnitary]
    have hv := h (V * diagonal a * Vᴴ) (U * diagonal b * Uᴴ) a b
      (isStarNormal_unitary_diagonalization a hV) (isStarNormal_unitary_diagonalization b hU)
      (roots_unitary_diagonalization a hV) (roots_unitary_diagonalization b hU)
    simpa [V, Holds, determinantValue] using hv

end

end MOC
