import MOC.BivectorPhaseFactorization
import MOC.GrassmannianImageStars
import MOC.Core

/-! The phase relations from four labels lift an isometric cone
preserver on bivectors to a unitary matrix on vectors. -/

open BigOperators Matrix

namespace MOC

noncomputable section

private def bivectorCongruenceLinear (U : GrassmannianMatrix) :
    GrassmannianMatrix →ₗ[ℂ] GrassmannianMatrix where
  toFun A := U * A * Uᵀ
  map_add' A B := by simp only [Matrix.mul_add, Matrix.add_mul]
  map_smul' c A := by simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]

private def wedgeLeft (y : GrassmannianVector) : GrassmannianVector →ₗ[ℂ] bivectorSkewSpace where
  toFun x := bivectorSkew x y
  map_add' x z := by
    apply Subtype.ext
    ext i j : 1
    simp only [bivectorSkew, bivectorMatrix, Pi.add_apply, Submodule.coe_add, Matrix.add_apply]
    ring
  map_smul' c x := by
    apply Subtype.ext
    ext i j : 1
    simp only [bivectorSkew, bivectorMatrix, Pi.smul_apply, Submodule.coe_smul,
      Matrix.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

private def wedgeRight (x : GrassmannianVector) : GrassmannianVector →ₗ[ℂ] bivectorSkewSpace where
  toFun y := bivectorSkew x y
  map_add' y z := by
    apply Subtype.ext
    ext i j : 1
    simp only [bivectorSkew, bivectorMatrix, Pi.add_apply, Submodule.coe_add, Matrix.add_apply]
    ring
  map_smul' c y := by
    apply Subtype.ext
    ext i j : 1
    simp only [bivectorSkew, bivectorMatrix, Pi.smul_apply, Submodule.coe_smul,
      Matrix.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

private theorem wedge_swap (x y : GrassmannianVector) : bivectorSkew y x = -bivectorSkew x y := by
  apply Subtype.ext
  ext i j : 1
  simp only [bivectorSkew, bivectorMatrix, Submodule.coe_neg, Matrix.neg_apply]
  ring

private theorem wedge_self (x : GrassmannianVector) : bivectorSkew x x = 0 := by
  apply Subtype.ext
  ext i j : 1
  simp only [bivectorSkew, bivectorMatrix, sub_self, Submodule.coe_zero, Matrix.zero_apply]

private abbrev coordinateWedge (i j : Fin 5) :=
  bivectorSkew (grassmannianBasisVector i) (grassmannianBasisVector j)

private theorem wedge_expand (x y : GrassmannianVector) :
    bivectorSkew x y = ∑ i, ∑ j, (x i * y j) • coordinateWedge i j := by
  have he (z : GrassmannianVector) : ∑ i, z i • grassmannianBasisVector i = z := by
    funext k
    simp [grassmannianBasisVector, Finset.sum_apply, Pi.single_apply, Pi.smul_apply,
      smul_eq_mul, eq_comm]
  calc
    _ = (wedgeLeft y) (∑ i, x i • grassmannianBasisVector i) := by rw [he]
    _ = ∑ i, x i • bivectorSkew (grassmannianBasisVector i) y := by
      simp only [map_sum, map_smul, wedgeLeft, LinearMap.coe_mk, AddHom.coe_mk]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      have h := (wedgeRight (grassmannianBasisVector i)).map_sum
        (fun j => y j • grassmannianBasisVector j) Finset.univ
      rw [he y] at h
      simp only [map_smul, wedgeRight, LinearMap.coe_mk, AddHom.coe_mk] at h
      rw [h, Finset.smul_sum]
      simp only [smul_smul]

private theorem congruence_of_orthonormal_axes
    (v : Fin 5 → GrassmannianVector)
    (hv : ∀ i j, bivectorPair (v i) (v j) = if i = j then 1 else 0) :
    let V : GrassmannianMatrix := Matrix.of fun r i => v i r
    IsUnitary V ∧ ∀ i, Vᴴ *ᵥ v i = grassmannianBasisVector i := by
  dsimp only
  let V : GrassmannianMatrix := Matrix.of fun r i => v i r
  have hh : Vᴴ * V = 1 := by
    ext i j : 1
    change bivectorPair (v i) (v j) = (1 : GrassmannianMatrix) i j
    rw [hv, Matrix.one_apply]
  refine ⟨⟨Matrix.mul_eq_one_comm.mp hh, hh⟩, fun i => ?_⟩
  ext j
  change bivectorPair (v j) (v i) = grassmannianBasisVector i j
  rw [hv]
  simp [grassmannianBasisVector, Pi.single_apply, eq_comm]

private theorem column_phases_unitary (V : GrassmannianMatrix) (hV : IsUnitary V)
    (t : Fin 5 → ℂ) (ht : ∀ i, Complex.normSq (t i) = 1) :
    IsUnitary (V * Matrix.diagonal t) := by
  let D := Matrix.diagonal t
  have hd : Dᴴ * D = 1 := by
    rw [show Dᴴ = Matrix.diagonal (fun i => star (t i)) by
      ext i j : 1
      by_cases h : i = j
      · subst j; simp [D]
      · simp [D, Matrix.conjTranspose_apply, Matrix.diagonal_apply, h, Ne.symm h],
      Matrix.diagonal_mul_diagonal]
    ext i j : 1
    by_cases h : i = j
    · subst j
      simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
      rw [mul_comm (star (t i)), Complex.star_def, Complex.mul_conj, ht, Complex.ofReal_one]
    · simp [Matrix.diagonal_apply, Matrix.one_apply, h]
  have h : (V * D)ᴴ * (V * D) = 1 := by
    rw [Matrix.conjTranspose_mul, ← Matrix.mul_assoc, Matrix.mul_assoc Dᴴ Vᴴ V,
      hV.2, Matrix.mul_one, hd]
  exact ⟨Matrix.mul_eq_one_comm.mp h, h⟩

private theorem coordinateWedge_apply (i j k l : Fin 5) :
    (coordinateWedge i j : GrassmannianMatrix) k l =
      (if k = i ∧ l = j then 1 else 0) - (if k = j ∧ l = i then 1 else 0) := by
  change bivectorMatrix (grassmannianBasisVector i) (grassmannianBasisVector j) k l = _
  have he (u v : Fin 5) : grassmannianBasisVector u v = if v = u then 1 else 0 := by
    simp [grassmannianBasisVector, Pi.single_apply, eq_comm]
  by_cases hki : k = i <;> by_cases hlj : l = j <;> by_cases hkj : k = j <;>
    by_cases hli : l = i <;> simp [bivectorMatrix, he, hki, hlj, hkj, hli]

private theorem wedge_expand_four (i j k l : Fin 5) :
    bivectorSkew (grassmannianBasisVector i + grassmannianBasisVector k)
        (grassmannianBasisVector j + grassmannianBasisVector l) =
      coordinateWedge i j + coordinateWedge i l +
        (coordinateWedge k j + coordinateWedge k l) := by
  change (wedgeLeft (grassmannianBasisVector j + grassmannianBasisVector l))
    (grassmannianBasisVector i + grassmannianBasisVector k) = _
  rw [map_add]
  change (wedgeRight (grassmannianBasisVector i)) (grassmannianBasisVector j + grassmannianBasisVector l) +
    (wedgeRight (grassmannianBasisVector k)) (grassmannianBasisVector j + grassmannianBasisVector l) = _
  rw [map_add, map_add]

/-- Every isometry of the order-five bivector space that preserves
decomposability acts on exterior products as a unitary matrix. -/
theorem exists_unitary_of_grassmannian_preserver
    (W : bivectorSkewSpace ≃ₗ[ℂ] bivectorSkewSpace)
    (hP : ∀ A : bivectorSkewSpace, PluckerBivector (A : GrassmannianMatrix) →
      PluckerBivector ((W A : bivectorSkewSpace) : GrassmannianMatrix))
    (hW : ∀ A B : bivectorSkewSpace,
      bivectorMatrixPair (W A) (W B) = bivectorMatrixPair A B) :
    ∃ U : GrassmannianMatrix, IsUnitary U ∧ ∀ x y : GrassmannianVector,
      (W (bivectorSkew x y) : GrassmannianMatrix) = bivectorMatrix (U *ᵥ x) (U *ᵥ y) := by
  obtain ⟨v, λ, hv, hλ⟩ := grassmannian_image_star_axes W hP hW
  let V : GrassmannianMatrix := Matrix.of fun r i => v i r
  obtain ⟨hV, hVv⟩ := congruence_of_orthonormal_axes v hv
  let Q := (bivectorCongruenceLinear Vᴴ).comp (bivectorSkewSpace.subtype.comp W.toLinearMap)
  have Qbasis (i j : Fin 5) (hij : i ≠ j) :
      Q (coordinateWedge i j) = λ i j • (coordinateWedge i j : GrassmannianMatrix) := by
    change Vᴴ * ((W (coordinateWedge i j) : bivectorSkewSpace) : GrassmannianMatrix) * (Vᴴ)ᵀ = _
    rw [(hλ i j hij).1, Matrix.mul_smul, Matrix.smul_mul, bivectorMatrix_congr, hVv i, hVv j]
  have hsymm (i j : Fin 5) : λ j i = λ i j := by
    by_cases h : i = j
    · rw [h]
    have he := congrArg Q (wedge_swap (grassmannianBasisVector i) (grassmannianBasisVector j))
    rw [map_neg, Qbasis j i h.symm, Qbasis i j h] at he
    have hij := congrArg (fun A : GrassmannianMatrix => A i j) he
    simpa [Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul, coordinateWedge_apply, h, Ne.symm h]
      using hij
  have hfour (i j k l : Fin 5) (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
      (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) : λ i j * λ k l = λ i l * λ k j := by
    let A := bivectorSkew (grassmannianBasisVector i + grassmannianBasisVector k)
      (grassmannianBasisVector j + grassmannianBasisVector l)
    have hA : PluckerBivector (A : GrassmannianMatrix) :=
      (pluckerBivector_iff_decomposable _).mpr ⟨_, _, rfl⟩
    have hQ : PluckerBivector (Q A) := by
      obtain ⟨x, y, he⟩ := (pluckerBivector_iff_decomposable _).mp (hP A hA)
      change PluckerBivector (Vᴴ * ((W A : bivectorSkewSpace) : GrassmannianMatrix) * (Vᴴ)ᵀ)
      rw [he, bivectorMatrix_congr]
      exact (pluckerBivector_iff_decomposable _).mpr ⟨_, _, rfl⟩
    have he := hQ.2 i j k l
    rw [show A = _ from wedge_expand_four i j k l, map_add, map_add, map_add,
      Qbasis i j hij, Qbasis i l hil, Qbasis k j hjk.symm, Qbasis k l hkl] at he
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, coordinateWedge_apply,
      hij, hik, hil, hjk, hjl, hkl, Ne.symm hij, Ne.symm hik, Ne.symm hil, Ne.symm hjk,
      Ne.symm hjl, Ne.symm hkl, eq_self_iff_true, and_true, true_and, false_and, and_false,
      if_true, if_false, sub_self, sub_zero, zero_sub, zero_mul, mul_zero, add_zero,
      zero_add, mul_one, mul_neg] at he
    exact sub_eq_zero.mp (by linear_combination he)
  obtain ⟨t, ht, hphase⟩ := exists_label_phases_of_four_label_products λ (0 : Fin 5) 1 2
    (by decide) (by decide) (by decide) hsymm (fun i j hij => (hλ i j hij).2) hfour
  let U := V * Matrix.diagonal t
  refine ⟨U, column_phases_unitary V hV t ht, fun x y => ?_⟩
  let L := bivectorSkewSpace.subtype.comp W.toLinearMap
  let R := (bivectorCongruenceLinear U).comp bivectorSkewSpace.subtype
  have hu (i : Fin 5) : U *ᵥ grassmannianBasisVector i = t i • v i := by
    rw [grassmannianBasisVector, Matrix.mulVec_single_one]
    funext r
    change (V * Matrix.diagonal t) r i = t i * v i r
    rw [Matrix.mul_diagonal, mul_comm]
  have hb (i j : Fin 5) : L (coordinateWedge i j) = R (coordinateWedge i j) := by
    by_cases h : i = j
    · subst j
      rw [show coordinateWedge i i = 0 from wedge_self _, map_zero, map_zero]
    change (W (coordinateWedge i j) : GrassmannianMatrix) =
      U * bivectorMatrix (grassmannianBasisVector i) (grassmannianBasisVector j) * Uᵀ
    rw [(hλ i j h).1, hphase i j h, bivectorMatrix_congr, hu i, hu j]
    ext r s : 1
    simp only [Matrix.smul_apply, smul_eq_mul, bivectorMatrix, Pi.smul_apply]
    ring
  have hall : L (bivectorSkew x y) = R (bivectorSkew x y) := by
    rw [wedge_expand]
    simp only [map_sum, map_smul, hb]
  exact hall.trans (bivectorMatrix_congr U x y)

end

end MOC
