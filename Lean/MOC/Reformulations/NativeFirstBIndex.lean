import MOC.Reformulations.NativeFirstBGeometry

/-! 102: the determinant of the actual linearized fixed-point operator.
No topological assertion about the index of a globally defined sum is made. -/

open BigOperators Matrix

namespace MOC.Reformulations.NativeFirstB

noncomputable section

/-- The signed fixed-point determinant comparison for actual normal
operators, not only diagonal spectral lists. -/
theorem fixedPointOperatorHull (h : MOCIsTrue) {n : ℕ}
    (A B U : Mat n) (a b : Fin n → ℂ) (hA : IsStarNormal A) (hB : IsStarNormal B)
    (hU : IsUnitary U) (ha : HasRoots A a) (hb : HasRoots B b) :
    (1 - (A + U * B * Uᴴ)).det ∈ convexHull ℝ
      (Set.range (fun σ : Equiv.Perm (Fin n) => ∏ j, (1 - (a (σ j) + b j)))) := by
  obtain ⟨a', V, hV, rfl⟩ := exists_unitary_diagonalization A hA
  obtain ⟨b', W, hW, rfl⟩ := exists_unitary_diagonalization B hB
  unfold HasRoots at ha hb
  rw [roots_unitary_diagonalization a' hV] at ha
  rw [roots_unitary_diagonalization b' hW] at hb
  obtain ⟨e, rfl⟩ := exists_perm_of_equal_multisets a a' ha.symm
  obtain ⟨f, rfl⟩ := exists_perm_of_equal_multisets b b' hb.symm
  let s : Fin n → ℂ := fun i => 1 - a' i
  let t : Fin n → ℂ := fun i => -b' i
  let T := U * W
  have hT : IsUnitary T := unitaryMul hU hW
  have hs : diagonal s = 1 - diagonal a' := by
    ext i j
    by_cases hij : i = j <;> simp [s, Matrix.diagonal_apply, Matrix.one_apply, hij]
  have ht : diagonal t = -diagonal b' := by
    ext i j
    by_cases hij : i = j <;> simp [t, Matrix.diagonal_apply, hij]
  have h₁ : V * diagonal s * Vᴴ = 1 - V * diagonal a' * Vᴴ := by
    rw [hs, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hV.1]
  have h₂ : T * diagonal t * Tᴴ = -(U * (W * diagonal b' * Wᴴ) * Uᴴ) := by
    rw [ht, Matrix.mul_neg, Matrix.neg_mul]
    simp only [T, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have hD : (1 - (V * diagonal a' * Vᴴ + U * (W * diagonal b' * Wᴴ) * Uᴴ) : Mat n) =
      V * diagonal s * Vᴴ + T * diagonal t * Tᴴ := by rw [h₁, h₂]; abel
  have hp : (fun σ : Equiv.Perm (Fin n) =>
      ∏ j, (1 - ((a' ∘ e) (σ j) + (b' ∘ f) j))) =
      matchingProduct (s ∘ e) (t ∘ f) := by
    funext σ
    unfold matchingProduct
    apply Finset.prod_congr rfl
    intro j _
    simp only [s, t, Function.comp_apply]
    ring
  rw [hD, determinantValue_relative s t V T hV, hp, matchingRange_relabel]
  exact h n s t (Vᴴ * T) (relative_unitary V T hV hT)

/-- 102: derivatives of maps in a real smooth fixed-point chart and an
actual real orthogonal frame change. The complex matrices are the scalar
extension needed to count complex roots. -/
theorem realFixedPointIndexHull (h : MOCIsTrue) {n : ℕ}
    (F G : (Fin n → ℝ) → (Fin n → ℝ)) (x : Fin n → ℝ) (_hF : F x = x) (_hG : G x = x)
    (Q : Matrix.orthogonalGroup (Fin n) ℝ) (a b : Fin n → ℂ)
    (hA : IsStarNormal (complexify (LinearMap.toMatrix' (fderiv ℝ F x).toLinearMap)))
    (hB : IsStarNormal (complexify (LinearMap.toMatrix' (fderiv ℝ G x).toLinearMap)))
    (ha : HasRoots (complexify (LinearMap.toMatrix' (fderiv ℝ F x).toLinearMap)) a)
    (hb : HasRoots (complexify (LinearMap.toMatrix' (fderiv ℝ G x).toLinearMap)) b) :
    let A := complexify (LinearMap.toMatrix' (fderiv ℝ F x).toLinearMap)
    let B := complexify (LinearMap.toMatrix' (fderiv ℝ G x).toLinearMap)
    let U := complexify Q.val
    (1 - (A + U * B * Uᴴ)).det ∈ convexHull ℝ
      (Set.range (fun σ : Equiv.Perm (Fin n) => ∏ j, (1 - (a (σ j) + b j)))) :=
  fixedPointOperatorHull h _ _ _ a b hA hB (isUnitary_ofReal_orthogonal Q) ha hb

end

end MOC.Reformulations.NativeFirstB
