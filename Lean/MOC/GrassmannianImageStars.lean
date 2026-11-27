import MOC.GrassmannianBivectorLift
import Mathlib.Data.Real.Sqrt

/-! Orthogonal axes for the image stars of a bivector cone preserver. -/

open BigOperators Matrix

namespace MOC

abbrev GrassmannianVector := Fin 5 → ℂ
abbrev GrassmannianMatrix := Matrix (Fin 5) (Fin 5) ℂ

/-- Skew matrices represent bivectors in five coordinates. -/
noncomputable def bivectorSkewSpace : Submodule ℂ GrassmannianMatrix where
  carrier := {A | ∀ i j, A j i = -A i j}
  zero_mem' := by simp
  add_mem' := by
    intro A B hA hB i j
    change A j i + B j i = -(A i j + B i j)
    rw [hA i j, hB i j, neg_add]
  smul_mem' := by
    intro c A hA i j
    change c * A j i = -(c * A i j)
    rw [hA i j, mul_neg]

/-- The skew matrix of a decomposable bivector. -/
def bivectorSkew (x y : GrassmannianVector) : bivectorSkewSpace :=
  ⟨bivectorMatrix x y, ((pluckerBivector_iff_decomposable _).mpr ⟨x, y, rfl⟩).1⟩

/-- The coordinate vector at the specified label. -/
def grassmannianBasisVector (i : Fin 5) : GrassmannianVector := Pi.single i 1

/-- The Hermitian pairing on the underlying coordinate vectors. -/
noncomputable def bivectorPair (x y : GrassmannianVector) : ℂ := ∑ i, star (x i) * y i

/-- The Frobenius pairing of the skew coordinate matrices. It is twice
the exterior pairing in the basis of increasing coordinate pairs. -/
noncomputable def bivectorMatrixPair (A B : GrassmannianMatrix) : ℂ := ∑ i, ∑ j, star (A i j) * B i j

theorem bivectorMatrixPair_wedges (x y z w : GrassmannianVector) :
    bivectorMatrixPair (bivectorMatrix x y) (bivectorMatrix z w) =
      2 * (bivectorPair x z * bivectorPair y w - bivectorPair x w * bivectorPair y z) := by
  have h (a b c d : GrassmannianVector) :
      (∑ i, ∑ j, (star (a i) * star (b j)) * (c i * d j)) =
        bivectorPair a c * bivectorPair b d := by
    rw [bivectorPair, bivectorPair, Fintype.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp only [bivectorMatrixPair, bivectorMatrix, star_sub, star_mul', sub_mul, mul_sub,
    Finset.sum_sub_distrib, h]
  ring

theorem bivectorMatrixPair_smul_left (c : ℂ) (A B : GrassmannianMatrix) :
    bivectorMatrixPair (c • A) B = star c * bivectorMatrixPair A B := by
  simp only [bivectorMatrixPair, Matrix.smul_apply, smul_eq_mul, star_mul', mul_assoc,
    Finset.mul_sum]

theorem bivectorMatrixPair_smul_right (c : ℂ) (A B : GrassmannianMatrix) :
    bivectorMatrixPair A (c • B) = c * bivectorMatrixPair A B := by
  simp only [bivectorMatrixPair, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem bivectorPair_smul_left (c : ℂ) (x y : GrassmannianVector) :
    bivectorPair (c • x) y = star c * bivectorPair x y := by
  simp only [bivectorPair, Pi.smul_apply, smul_eq_mul, star_mul', mul_assoc, Finset.mul_sum]

private theorem bivectorPair_smul_right (c : ℂ) (x y : GrassmannianVector) :
    bivectorPair x (c • y) = c * bivectorPair x y := by
  simp only [bivectorPair, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem bivectorPair_self (x : GrassmannianVector) :
    bivectorPair x x = ((∑ i, Complex.normSq (x i) : ℝ) : ℂ) := by
  rw [bivectorPair, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm]
  exact Complex.mul_conj _

private theorem bivectorPair_self_pos {x : GrassmannianVector} (hx : x ≠ 0) :
    0 < ∑ i, Complex.normSq (x i) := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra! h
    exact hx (funext h)
  exact Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _) ⟨i, Finset.mem_univ i,
    (Complex.normSq_pos).mpr hi⟩

private theorem bivectorPair_self_ne_zero {x : GrassmannianVector} (hx : x ≠ 0) :
    bivectorPair x x ≠ 0 := by
  rw [bivectorPair_self]
  exact Complex.ofReal_ne_zero.mpr (bivectorPair_self_pos hx).ne'

theorem bivectorPair_basis_left (i : Fin 5) (x : GrassmannianVector) :
    bivectorPair (grassmannianBasisVector i) x = x i := by
  classical
  simp [bivectorPair, grassmannianBasisVector, Pi.single_apply, apply_ite, ite_mul]

private theorem bivectorPair_basis_right (x : GrassmannianVector) (i : Fin 5) :
    bivectorPair x (grassmannianBasisVector i) = star (x i) := by
  classical
  simp [bivectorPair, grassmannianBasisVector, Pi.single_apply, mul_ite]

private theorem basis_wedge_ne_zero {i j : Fin 5} (hij : i ≠ j) :
    bivectorMatrix (grassmannianBasisVector i) (grassmannianBasisVector j) ≠ 0 := by
  intro h
  have he := congrArg (fun A : GrassmannianMatrix => A i j) h
  simpa [bivectorMatrix, grassmannianBasisVector, Pi.single_apply, hij, Ne.symm hij] using he

private theorem bivectorMatrix_neg_swap (x y : GrassmannianVector) :
    bivectorMatrix y (-x) = bivectorMatrix x y := by
  ext i j
  simp only [bivectorMatrix, Pi.neg_apply]
  ring

private theorem bivectorMatrix_smul_transfer (c : ℂ) (x y : GrassmannianVector) :
    bivectorMatrix (c • x) y = bivectorMatrix x (c • y) := by
  ext i j
  simp only [bivectorMatrix, Pi.smul_apply, smul_eq_mul]
  ring

private theorem bivectorStar_scaling (c : ℂ) (hc : c ≠ 0) (x : GrassmannianVector) :
    bivectorStar (c • x) = bivectorStar x := by
  ext A
  simp only [mem_bivectorStar_iff, bivectorMatrix_smul_transfer]
  constructor
  · rintro ⟨y, h⟩
    exact ⟨c • y, h⟩
  · rintro ⟨y, h⟩
    exact ⟨c⁻¹ • y, by simpa [smul_smul, hc] using h⟩

private theorem normalized_star_axis (x : GrassmannianVector) (hx : x ≠ 0) :
    ∃ v : GrassmannianVector, v ≠ 0 ∧ bivectorPair v v = 1 ∧ bivectorStar v = bivectorStar x := by
  let r := Real.sqrt (∑ i, Complex.normSq (x i))
  have hr : r ≠ 0 := (Real.sqrt_pos.2 (bivectorPair_self_pos hx)).ne'
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
  let c : ℂ := (r : ℂ)⁻¹
  have hc : c ≠ 0 := inv_ne_zero hrC
  refine ⟨c • x, smul_ne_zero hc hx, ?_, bivectorStar_scaling c hc x⟩
  have hsq : (r : ℂ) ^ 2 = ((∑ i, Complex.normSq (x i) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (bivectorPair_self_pos hx).le]
  rw [bivectorPair_smul_left, bivectorPair_smul_right, bivectorPair_self, ← hsq]
  simp only [c, star_inv, Complex.star_def, Complex.conj_ofReal]
  field_simp [hrC] <;> ring

private noncomputable def bivectorImageStarMap (W : bivectorSkewSpace ≃ₗ[ℂ] bivectorSkewSpace)
    (x : GrassmannianVector) : GrassmannianVector →ₗ[ℂ] GrassmannianMatrix :=
  (bivectorSkewSpace.subtype.comp W.toLinearMap).comp
    ((bivectorStarMap x).codRestrict bivectorSkewSpace (fun y => (bivectorSkew x y).property))

private theorem imageStarMap_apply (W : bivectorSkewSpace ≃ₗ[ℂ] bivectorSkewSpace)
    (x y : GrassmannianVector) :
    bivectorImageStarMap W x y = (W (bivectorSkew x y) : GrassmannianMatrix) := rfl

private theorem imageStarMap_ker (W : bivectorSkewSpace ≃ₗ[ℂ] bivectorSkewSpace)
    (x : GrassmannianVector) : LinearMap.ker (bivectorImageStarMap W x) = LinearMap.ker (bivectorStarMap x) := by
  ext y
  simp only [LinearMap.mem_ker, imageStarMap_apply]
  change (W (bivectorSkew x y) : GrassmannianMatrix) = 0 ↔ bivectorMatrix x y = 0
  constructor
  · intro h
    have he : W (bivectorSkew x y) = W 0 := by
      rw [map_zero]
      exact Subtype.ext h
    exact congrArg Subtype.val (W.injective he)
  · intro h
    have he : bivectorSkew x y = 0 := Subtype.ext h
    rw [he, map_zero]
    rfl

private theorem exists_imageStar_axis (W : bivectorSkewSpace ≃ₗ[ℂ] bivectorSkewSpace)
    (hP : ∀ A : bivectorSkewSpace, PluckerBivector (A : GrassmannianMatrix) →
      PluckerBivector (W A : GrassmannianMatrix)) (i : Fin 5) :
    ∃ v : GrassmannianVector, v ≠ 0 ∧ bivectorPair v v = 1 ∧
      LinearMap.range (bivectorImageStarMap W (grassmannianBasisVector i)) = bivectorStar v := by
  let x := grassmannianBasisVector i
  have hx : x ≠ 0 := by
    intro h
    have he := congrFun h i
    simpa [x, grassmannianBasisVector] using he
  let F := bivectorImageStarMap W x
  have hr := LinearMap.finrank_range_add_finrank_ker F
  have hs := LinearMap.finrank_range_add_finrank_ker (bivectorStarMap x)
  rw [show LinearMap.ker F = LinearMap.ker (bivectorStarMap x) from imageStarMap_ker W x] at hr
  have hdim : Module.finrank ℂ (LinearMap.range F) = 4 := calc
    _ = Module.finrank ℂ (bivectorStar x) := Nat.add_right_cancel (hr.trans hs.symm)
    _ = 4 := by rw [finrank_bivectorStar x hx, Fintype.card_fin]
  obtain ⟨u, hu, he⟩ := decomposable_finrank_four_eq_bivectorStar (LinearMap.range F)
    (by
      rintro _ ⟨y, rfl⟩
      change PluckerBivector (W (bivectorSkew x y) : GrassmannianMatrix)
      apply hP
      exact (pluckerBivector_iff_decomposable _).mpr ⟨x, y, rfl⟩) hdim
  obtain ⟨v, hv, hp, he'⟩ := normalized_star_axis u hu
  exact ⟨v, hv, hp, he.trans he'.symm⟩

private theorem mem_imageStar (W : bivectorSkewSpace ≃ₗ[ℂ] bivectorSkewSpace)
    (x y : GrassmannianVector) :
    (W (bivectorSkew x y) : GrassmannianMatrix) ∈ LinearMap.range (bivectorImageStarMap W x) :=
  ⟨y, rfl⟩

private theorem exists_preimage_in_star (W : bivectorSkewSpace ≃ₗ[ℂ] bivectorSkewSpace)
    (x : GrassmannianVector) (A : bivectorSkewSpace)
    (hA : (A : GrassmannianMatrix) ∈ LinearMap.range (bivectorImageStarMap W x)) :
    ∃ y, W (bivectorSkew x y) = A := by
  obtain ⟨y, hy⟩ := hA
  exact ⟨y, Subtype.ext hy⟩

private theorem imageStar_axes_independent (W : bivectorSkewSpace ≃ₗ[ℂ] bivectorSkewSpace)
    (v : Fin 5 → GrassmannianVector)
    (hstar : ∀ i, LinearMap.range (bivectorImageStarMap W (grassmannianBasisVector i)) =
      bivectorStar (v i))
    {i j : Fin 5} (hij : i ≠ j) (c : ℂ) : c • v i ≠ v j := by
  intro h
  obtain ⟨k, hki, hkj⟩ : ∃ k : Fin 5, k ≠ i ∧ k ≠ j :=
    (by decide +kernel : ∀ i j : Fin 5, ∃ k : Fin 5, k ≠ i ∧ k ≠ j) i j
  let A := W (bivectorSkew (grassmannianBasisVector j) (grassmannianBasisVector k))
  have hj := mem_imageStar W (grassmannianBasisVector j) (grassmannianBasisVector k)
  rw [hstar j] at hj
  obtain ⟨y, hy⟩ := (mem_bivectorStar_iff (v j) (A : GrassmannianMatrix)).mp hj
  have hi : (A : GrassmannianMatrix) ∈ bivectorStar (v i) := by
    apply (mem_bivectorStar_iff _ _).mpr
    refine ⟨c • y, ?_⟩
    rw [hy, ← h, bivectorMatrix_smul_transfer]
  rw [← hstar i] at hi
  obtain ⟨x, hx⟩ := exists_preimage_in_star W (grassmannianBasisVector i) A hi
  have he := congrArg (fun B : bivectorSkewSpace => B.val j k) (W.injective hx)
  simpa [bivectorSkew, bivectorMatrix, grassmannianBasisVector, Pi.single_apply,
    hij, Ne.symm hij, hki, Ne.symm hki, hkj, Ne.symm hkj] using he

private theorem span_pair_finrank_of_not_smul {x y : GrassmannianVector}
    (hx : x ≠ 0) (hy : ∀ c : ℂ, c • x ≠ y) :
    Module.finrank ℂ (Submodule.span ℂ ({x, y} : Set GrassmannianVector)) = 2 := by
  have hi : LinearIndependent ℂ (![y, x] : Fin 2 → GrassmannianVector) :=
    linearIndependent_fin2.mpr ⟨hx, hy⟩
  have hr : Set.range (![y, x] : Fin 2 → GrassmannianVector) = {x, y} := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · intro hz
      rcases (show z = x ∨ z = y by simpa using hz) with rfl | rfl
      · exact ⟨1, rfl⟩
      · exact ⟨0, rfl⟩
  rw [← hr, finrank_span_eq_card hi, Fintype.card_fin]

private theorem exists_image_basis_amplitude (W : bivectorSkewSpace ≃ₗ[ℂ] bivectorSkewSpace)
    (v : Fin 5 → GrassmannianVector) (hv : ∀ i, v i ≠ 0)
    (hstar : ∀ i, LinearMap.range (bivectorImageStarMap W (grassmannianBasisVector i)) =
      bivectorStar (v i))
    {i j : Fin 5} (hij : i ≠ j) :
    ∃ c : ℂ, (W (bivectorSkew (grassmannianBasisVector i) (grassmannianBasisVector j)) :
      GrassmannianMatrix) = c • bivectorMatrix (v i) (v j) := by
  let E := bivectorSkew (grassmannianBasisVector i) (grassmannianBasisVector j)
  let A : GrassmannianMatrix := W E
  have hA : A ≠ 0 := by
    intro hz
    have hW : W E = W 0 := by
      rw [map_zero]
      exact Subtype.ext hz
    exact basis_wedge_ne_zero hij (congrArg Subtype.val (W.injective hW))
  have hi : A ∈ LinearMap.range (bivectorImageStarMap W (grassmannianBasisVector i)) :=
    mem_imageStar W (grassmannianBasisVector i) (grassmannianBasisVector j)
  have hj : A ∈ LinearMap.range (bivectorImageStarMap W (grassmannianBasisVector j)) := by
    have he : E = bivectorSkew (grassmannianBasisVector j) (-grassmannianBasisVector i) :=
      Subtype.ext (bivectorMatrix_neg_swap _ _).symm
    exact ⟨-grassmannianBasisVector i, congrArg (fun X : bivectorSkewSpace =>
      (W X : GrassmannianMatrix)) he.symm⟩
  rw [hstar i] at hi
  rw [hstar j] at hj
  obtain ⟨x, hx⟩ := (mem_bivectorStar_iff _ _).mp hi
  obtain ⟨y, hy⟩ := (mem_bivectorStar_iff _ _).mp hj
  have hvi : v i ∈ bivectorCarrier A := by
    rw [hx, bivectorCarrier_matrix_eq_span _ _ (hx ▸ hA)]
    exact Submodule.subset_span (by simp)
  have hvj : v j ∈ bivectorCarrier A := by
    rw [hy, bivectorCarrier_matrix_eq_span _ _ (hy ▸ hA)]
    exact Submodule.subset_span (by simp)
  have hspan : Submodule.span ℂ ({v i, v j} : Set GrassmannianVector) ≤ bivectorCarrier A := by
    apply Submodule.span_le.mpr
    intro z hz
    rcases (show z = v i ∨ z = v j by simpa using hz) with rfl | rfl
    · exact hvi
    · exact hvj
  have hd := span_pair_finrank_of_not_smul (hv i) (imageStar_axes_independent W v hstar hij)
  have hcar := bivectorCarrier_finrank ((pluckerBivector_iff_decomposable A).mpr ⟨v i, x, hx⟩) hA
  have hEq : Submodule.span ℂ ({v i, v j} : Set GrassmannianVector) = bivectorCarrier A :=
    Submodule.eq_of_le_of_finrank_le hspan (by rw [hd, hcar])
  have hxmem : x ∈ Submodule.span ℂ ({v i, v j} : Set GrassmannianVector) := by
    rw [hEq, hx, bivectorCarrier_matrix_eq_span _ _ (hx ▸ hA)]
    exact Submodule.subset_span (by simp)
  obtain ⟨a, c, he⟩ := Submodule.mem_span_pair.mp hxmem
  refine ⟨c, ?_⟩
  change A = _
  rw [hx, ← he]
  ext s t
  simp only [bivectorMatrix, Matrix.smul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

private theorem exists_common_orthogonal_vector (u v : GrassmannianVector) :
    ∃ z : GrassmannianVector, z ≠ 0 ∧ bivectorPair u z = 0 ∧ bivectorPair v z = 0 := by
  let M : Matrix (Fin 2) (Fin 5) ℂ := fun i j => if i = 0 then star (u j) else star (v j)
  have hk := LinearMap.ker_ne_bot_of_finrank_lt (f := M.mulVecLin)
    (by rw [Module.finrank_pi, Module.finrank_pi, Fintype.card_fin, Fintype.card_fin]; decide)
  have hp := Submodule.one_le_finrank_iff.mpr hk
  obtain ⟨z, hz⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hp
  have hzn : (z : GrassmannianVector) ≠ 0 := fun h => hz (Subtype.ext h)
  have h : M *ᵥ (z : GrassmannianVector) = 0 := LinearMap.mem_ker.mp z.property
  refine ⟨z, hzn, ?_, ?_⟩
  · simpa only [Matrix.mulVec, dotProduct, M, if_pos rfl, Pi.zero_apply, bivectorPair]
      using congrFun h (0 : Fin 2)
  · have h₁ : (1 : Fin 2) ≠ 0 := by decide
    simpa only [Matrix.mulVec, dotProduct, M, if_neg h₁, Pi.zero_apply, bivectorPair]
      using congrFun h (1 : Fin 2)

private theorem imageStar_axes_orthogonal (W : bivectorSkewSpace ≃ₗ[ℂ] bivectorSkewSpace)
    (hPair : ∀ A B : bivectorSkewSpace,
      bivectorMatrixPair (W A : GrassmannianMatrix) (W B : GrassmannianMatrix) =
        bivectorMatrixPair (A : GrassmannianMatrix) (B : GrassmannianMatrix))
    (v : Fin 5 → GrassmannianVector) (hv : ∀ i, v i ≠ 0)
    (hstar : ∀ i, LinearMap.range (bivectorImageStarMap W (grassmannianBasisVector i)) =
      bivectorStar (v i)) {i j : Fin 5} (hij : i ≠ j) : bivectorPair (v i) (v j) = 0 := by
  obtain ⟨z, hzn, hiz, hjz⟩ := exists_common_orthogonal_vector (v i) (v j)
  let X := bivectorSkew (v i) z
  let Y := bivectorSkew (v j) z
  have hX : (X : GrassmannianMatrix) ∈ LinearMap.range
      (bivectorImageStarMap W (grassmannianBasisVector i)) := by
    rw [hstar i]
    exact (mem_bivectorStar_iff _ _).mpr ⟨z, rfl⟩
  have hY : (Y : GrassmannianMatrix) ∈ LinearMap.range
      (bivectorImageStarMap W (grassmannianBasisVector j)) := by
    rw [hstar j]
    exact (mem_bivectorStar_iff _ _).mpr ⟨z, rfl⟩
  obtain ⟨x, hx⟩ := exists_preimage_in_star W (grassmannianBasisVector i) X hX
  obtain ⟨y, hy⟩ := exists_preimage_in_star W (grassmannianBasisVector j) Y hY
  let E := bivectorSkew (grassmannianBasisVector i) (grassmannianBasisVector j)
  obtain ⟨c, hE⟩ := exists_image_basis_amplitude W v hv hstar hij
  have hEX : bivectorMatrixPair (W E : GrassmannianMatrix) (X : GrassmannianMatrix) = 0 := by
    change bivectorMatrixPair (W E : GrassmannianMatrix) (bivectorMatrix (v i) z) = 0
    rw [show (W E : GrassmannianMatrix) = c • bivectorMatrix (v i) (v j) from hE,
      bivectorMatrixPair_smul_left, bivectorMatrixPair_wedges, hiz, hjz]
    ring
  have he := hPair E (bivectorSkew (grassmannianBasisVector i) x)
  rw [hx, hEX] at he
  have hxj : x j = 0 := by
    have h : (2 : ℂ) * x j = 0 := by
      change 0 = bivectorMatrixPair (bivectorMatrix (grassmannianBasisVector i)
        (grassmannianBasisVector j)) (bivectorMatrix (grassmannianBasisVector i) x) at he
      simp only [bivectorMatrixPair_wedges, bivectorPair_basis_left] at he
      simpa only [grassmannianBasisVector, Pi.single_eq_same, Pi.single_eq_of_ne hij,
        Pi.single_eq_of_ne (Ne.symm hij), one_mul, mul_zero, sub_zero] using he.symm
    exact (mul_eq_zero.mp h).resolve_left two_ne_zero
  have hxy : bivectorMatrixPair (bivectorMatrix (grassmannianBasisVector i) x)
      (bivectorMatrix (grassmannianBasisVector j) y) = 0 := by
    rw [bivectorMatrixPair_wedges, bivectorPair_basis_left, bivectorPair_basis_left,
      bivectorPair_basis_right, hxj]
    simp [grassmannianBasisVector, Pi.single_apply, hij, Ne.symm hij]
  have h := hPair (bivectorSkew (grassmannianBasisVector i) x)
    (bivectorSkew (grassmannianBasisVector j) y)
  rw [hx, hy] at h
  have hEq : bivectorMatrixPair (bivectorMatrix (v i) z) (bivectorMatrix (v j) z) = 0 :=
    h.trans hxy
  rw [bivectorMatrixPair_wedges, hiz, zero_mul, sub_zero] at hEq
  have hzero := (mul_eq_zero.mp hEq).resolve_left two_ne_zero
  exact (mul_eq_zero.mp hzero).resolve_right (bivectorPair_self_ne_zero hzn)

/-- A unitary cone preserver in order five sends each coordinate star to
the star of an orthonormal axis. Each coordinate bivector goes to the
corresponding axis wedge times a scalar of modulus one. -/
theorem grassmannian_image_star_axes (W : bivectorSkewSpace ≃ₗ[ℂ] bivectorSkewSpace)
    (hP : ∀ A : bivectorSkewSpace, PluckerBivector (A : GrassmannianMatrix) →
      PluckerBivector (W A : GrassmannianMatrix))
    (hPair : ∀ A B : bivectorSkewSpace,
      bivectorMatrixPair (W A : GrassmannianMatrix) (W B : GrassmannianMatrix) =
        bivectorMatrixPair (A : GrassmannianMatrix) (B : GrassmannianMatrix)) :
    ∃ (v : Fin 5 → GrassmannianVector) (l : Fin 5 → Fin 5 → ℂ),
      (∀ i j, bivectorPair (v i) (v j) = if i = j then 1 else 0) ∧
      ∀ i j, i ≠ j →
        (W (bivectorSkew (grassmannianBasisVector i) (grassmannianBasisVector j)) :
          GrassmannianMatrix) = l i j • bivectorMatrix (v i) (v j) ∧ Complex.normSq (l i j) = 1 := by
  classical
  choose v hv hunit hstar using exists_imageStar_axis W hP
  have horth (i j : Fin 5) (hij : i ≠ j) : bivectorPair (v i) (v j) = 0 :=
    imageStar_axes_orthogonal W hPair v hv hstar hij
  have hamp (i j : Fin 5) (hij : i ≠ j) : ∃ c : ℂ,
      (W (bivectorSkew (grassmannianBasisVector i) (grassmannianBasisVector j)) :
        GrassmannianMatrix) = c • bivectorMatrix (v i) (v j) ∧ Complex.normSq c = 1 := by
    obtain ⟨c, hc⟩ := exists_image_basis_amplitude W v hv hstar hij
    refine ⟨c, hc, ?_⟩
    let E := bivectorSkew (grassmannianBasisVector i) (grassmannianBasisVector j)
    have h := hPair E E
    change bivectorMatrixPair (W E : GrassmannianMatrix) (W E : GrassmannianMatrix) =
      bivectorMatrixPair (bivectorMatrix (grassmannianBasisVector i) (grassmannianBasisVector j))
        (bivectorMatrix (grassmannianBasisVector i) (grassmannianBasisVector j)) at h
    rw [show (W E : GrassmannianMatrix) = c • bivectorMatrix (v i) (v j) from hc,
      bivectorMatrixPair_smul_left, bivectorMatrixPair_smul_right, bivectorMatrixPair_wedges,
      bivectorMatrixPair_wedges] at h
    have he : star c * (c * 2) = 2 := by
      simp only [hunit, horth i j hij, horth j i (Ne.symm hij), bivectorPair_basis_left] at h
      simpa only [grassmannianBasisVector, Pi.single_eq_same, Pi.single_eq_of_ne hij,
        Pi.single_eq_of_ne (Ne.symm hij), mul_one, zero_mul, sub_zero] using h
    have hc' : star c * c = 1 := by linear_combination (1 / 2 : ℂ) * he
    apply Complex.ofReal_injective
    rw [← Complex.mul_conj, mul_comm]
    simpa only [Complex.ofReal_one] using hc'
  let l (i j : Fin 5) : ℂ := if hij : i ≠ j then Classical.choose (hamp i j hij) else 0
  refine ⟨v, l, ?_, ?_⟩
  · intro i j
    by_cases hij : i = j
    · subst j
      simpa only [if_pos rfl] using hunit i
    · rw [if_neg hij]
      exact horth i j hij
  · intro i j hij
    simpa only [l, dif_pos hij] using Classical.choose_spec (hamp i j hij)

end MOC
