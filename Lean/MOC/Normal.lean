import MOC.Core
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-! The normal-matrix formulation, with eigenvalues counted with algebraic multiplicity. -/

open Matrix Polynomial Module.End
open scoped ComplexStarModule

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem exists_joint_eigenbasis {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] (A B : Module.End ℂ E)
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) (hAB : Commute A B) :
    ∃ (v : OrthonormalBasis (Fin (Module.finrank ℂ E)) ℂ E) (μ : Fin (Module.finrank ℂ E) → ℂ × ℂ),
      ∀ j, v j ∈ eigenspace A (μ j).2 ⊓ eigenspace B (μ j).1 := by
  classical
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
      · let p : B.Eigenvalues × A.Eigenvalues := (⟨y, hy⟩, ⟨x, hx⟩)
        change V p ≤ _
        exact le_iSup V p
      · rw [hasEigenvalue_iff, not_ne_iff] at hy
        rw [hy, inf_bot_eq]
        exact bot_le
    · rw [hasEigenvalue_iff, not_ne_iff] at hx
      rw [hx, bot_inf_eq]
      exact bot_le
  have hSum : DirectSum.IsInternal V :=
    hOrth.isInternal_iff.mpr (by rw [Submodule.orthogonal_eq_bot_iff, hTop])
  let hn : Module.finrank ℂ E = Module.finrank ℂ E := rfl
  exact ⟨hSum.subordinateOrthonormalBasis hn hOrth,
    (fun j => ζ (hSum.subordinateOrthonormalBasisIndex hn j hOrth)),
    fun j => hSum.subordinateOrthonormalBasis_subordinate hn j hOrth⟩

/-- The commuting Hermitian parts of a complex normal matrix give a common eigenbasis. -/
theorem exists_unitary_diagonalization (M : Matrix ι ι ℂ) (hM : IsStarNormal M) :
    ∃ (a : ι → ℂ) (U : Matrix ι ι ℂ), IsUnitary U ∧ M = U * diagonal a * Uᴴ := by
  classical
  let R := (ℜ M : Matrix ι ι ℂ)
  let J := (ℑ M : Matrix ι ι ℂ)
  let A := toEuclideanLin R
  let B := toEuclideanLin J
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
  obtain ⟨v₀, μ₀, hm⟩ := exists_joint_eigenbasis A B hA hB hAB
  let e : Fin (Module.finrank ℂ (EuclideanSpace ℂ ι)) ≃ ι :=
    Fintype.equivOfCardEq (by rw [Fintype.card_fin, finrank_euclideanSpace])
  let v := v₀.reindex e
  let μ (j : ι) := μ₀ (e.symm j)
  let a (j : ι) : ℂ := (μ j).2 + Complex.I * (μ j).1
  let U := (EuclideanSpace.basisFun ι ℂ).toBasis.toMatrix v.toBasis
  have hU₀ := (EuclideanSpace.basisFun ι ℂ).toMatrix_orthonormalBasis_mem_unitary v
  have hU : IsUnitary U :=
    ⟨Matrix.mem_unitaryGroup_iff.mp hU₀, Matrix.mem_unitaryGroup_iff'.mp hU₀⟩
  refine ⟨a, U, hU, ?_⟩
  have hsplit : toEuclideanLin M = A + Complex.I • B := by
    have hs : R + Complex.I • J = M := realPart_add_I_smul_imaginaryPart M
    change toEuclideanLin M = toEuclideanLin R + Complex.I • toEuclideanLin J
    simpa only [map_add, LinearEquiv.map_smul] using
      congrArg (toEuclideanLin : Matrix ι ι ℂ → _) hs.symm
  have hv (j : ι) : toEuclideanLin M (v j) = a j • v j := by
    have hs : v j ∈ eigenspace A (μ j).2 ⊓ eigenspace B (μ j).1 := by
      simpa only [v, μ, OrthonormalBasis.reindex_apply] using hm (e.symm j)
    have hmj := Submodule.mem_inf.mp hs
    rw [hsplit, LinearMap.add_apply, LinearMap.smul_apply, mem_eigenspace_iff.mp hmj.1,
      mem_eigenspace_iff.mp hmj.2]
    change _ = ((μ j).2 + Complex.I * (μ j).1) • v j
    rw [add_smul, MulAction.mul_smul]
  have hMU : M * U = U * diagonal a := by
    ext i j : 1
    have h := congrArg (fun x : EuclideanSpace ℂ ι => WithLp.equiv 2 (ι → ℂ) x i) (hv j)
    change WithLp.equiv 2 (ι → ℂ) (toEuclideanLin M (v j)) i = _ at h
    rw [Matrix.piLp_equiv_toEuclideanLin_apply] at h
    change (M *ᵥ (fun k => v j k)) i = (a j • v j) i at h
    rw [Matrix.mul_diagonal, Matrix.mul_apply]
    simpa only [U, Basis.toMatrix_apply,
      OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.coe_toBasis,
      EuclideanSpace.basisFun_repr, Matrix.mulVec, dotProduct,
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

/-- The real and imaginary parts of one normal diagonalization give a common
unitary eigenbasis for two commuting Hermitian matrices. -/
theorem exists_joint_hermitian_diagonalization (A B : Matrix ι ι ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hAB : Commute A B) :
    ∃ (a b : ι → ℂ) (W : Matrix ι ι ℂ), IsUnitary W ∧
      A = W * diagonal a * Wᴴ ∧ B = W * diagonal b * Wᴴ := by
  have hstar : (A + Complex.I • B)ᴴ = A - Complex.I • B := by
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hA.eq, hB.eq,
      Complex.star_def, Complex.conj_I, neg_smul, sub_eq_add_neg]
  have hcomm := hAB.smul_right Complex.I
  have hnormal : IsStarNormal (A + Complex.I • B) := by
    constructor
    change Commute (A + Complex.I • B)ᴴ (A + Complex.I • B)
    rw [hstar]
    exact ((Commute.refl A).add_right hcomm).sub_left
      (hcomm.symm.add_right (Commute.refl (Complex.I • B)))
  obtain ⟨d, W, hW, hd⟩ := exists_unitary_diagonalization _ hnormal
  have hd' : A - Complex.I • B = W * diagonal (star d) * Wᴴ := by
    rw [← hstar, hd, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.mul_assoc]
  let a (i : ι) : ℂ := (d i).re
  let b (i : ι) : ℂ := (d i).im
  have hadd : diagonal d + diagonal (star d) = (2 : ℂ) • diagonal a := by
    rw [Matrix.diagonal_add, ← Matrix.diagonal_smul]
    apply congrArg Matrix.diagonal
    funext i
    apply Complex.ext <;> simp [a, Pi.star_apply, Complex.star_def, Complex.mul_re, Complex.mul_im] <;> ring
  have hsub : diagonal d - diagonal (star d) = (2 * Complex.I) • diagonal b := by
    rw [Matrix.diagonal_sub, ← Matrix.diagonal_smul]
    apply congrArg Matrix.diagonal
    funext i
    apply Complex.ext <;> simp [b, Pi.star_apply, Complex.star_def, Complex.mul_re, Complex.mul_im] <;> ring
  have htwo : (2 : ℂ) ≠ 0 := by norm_num
  have htwoI : (2 : ℂ) * Complex.I ≠ 0 := mul_ne_zero htwo Complex.I_ne_zero
  refine ⟨a, b, W, hW, smul_right_injective _ htwo ?_, smul_right_injective _ htwoI ?_⟩
  · calc
      (2 : ℂ) • A = (A + Complex.I • B) + (A - Complex.I • B) := by rw [two_smul]; abel
      _ = W * (diagonal d + diagonal (star d)) * Wᴴ := by
        rw [hd, hd', Matrix.mul_add, Matrix.add_mul]
      _ = _ := by rw [hadd, Matrix.mul_smul, Matrix.smul_mul]
  · calc
      (2 * Complex.I) • B = (A + Complex.I • B) - (A - Complex.I • B) := by
        rw [MulAction.mul_smul, two_smul]
        abel
      _ = W * (diagonal d - diagonal (star d)) * Wᴴ := by
        rw [hd, hd', Matrix.mul_sub, Matrix.sub_mul]
      _ = _ := by rw [hsub, Matrix.mul_smul, Matrix.smul_mul]

/-- Independently chosen eigenbases preserve the hull condition, with eigenvalues
counted with their multiplicities. -/
theorem holds_iff_relative_to_diagonalizations (a b a' b' : ι → ℂ)
    {U V W : Matrix ι ι ℂ} (hU : IsUnitary U) (hV : IsUnitary V) (hW : IsUnitary W)
    (ha : diagonal a = V * diagonal a' * Vᴴ)
    (hb : U * diagonal b * Uᴴ = W * diagonal b' * Wᴴ) :
    Holds a b U ↔ Holds a' b' (Vᴴ * W) := by
  have hdet : determinantValue a b U = determinantValue a' b' (Vᴴ * W) := by
    unfold determinantValue at ⊢
    rw [ha, hb]
    exact determinantValue_relative a' b' V W hV
  have h1 : IsUnitary (1 : Matrix ι ι ℂ) := by simp [IsUnitary]
  have har := roots_unitary_diagonalization a h1
  simp only [Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one] at har
  rw [ha, roots_unitary_diagonalization a' hV] at har
  have hbr := roots_unitary_diagonalization b hU
  rw [hb, roots_unitary_diagonalization b' hW] at hbr
  obtain ⟨e, he⟩ := exists_perm_of_equal_multisets a a' har.symm
  obtain ⟨f, hf⟩ := exists_perm_of_equal_multisets b b' hbr.symm
  unfold Holds
  rw [hdet, he, hf, matchingRange_relabel]

/-- A common unitary eigenbasis realizes a permutation vertex, including repeated eigenvalues. -/
theorem holds_of_joint_unitary_diagonalization (a b a' b' : ι → ℂ) {U W : Matrix ι ι ℂ}
    (hU : IsUnitary U) (hW : IsUnitary W)
    (ha : diagonal a = W * diagonal a' * Wᴴ)
    (hb : U * diagonal b * Uᴴ = W * diagonal b' * Wᴴ) : Holds a b U := by
  apply (holds_iff_relative_to_diagonalizations a b a' b' hU hW hW ha hb).mpr
  rw [hW.2]
  exact holds_identity a' b'

/-- Commuting Hermitian summands give one permutation vertex, including repeated eigenvalues. -/
theorem holds_of_commuting_hermitian (a b : ι → ℂ) {U : Matrix ι ι ℂ}
    (hU : IsUnitary U) (hA : (diagonal a).IsHermitian) (hB : (U * diagonal b * Uᴴ).IsHermitian)
    (hAB : Commute (diagonal a) (U * diagonal b * Uᴴ)) : Holds a b U := by
  obtain ⟨a', b', W, hW, ha, hb⟩ := exists_joint_hermitian_diagonalization _ _ hA hB hAB
  exact holds_of_joint_unitary_diagonalization a b a' b' hU hW ha hb

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
