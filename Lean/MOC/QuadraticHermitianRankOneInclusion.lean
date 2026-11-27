import MOC.QuadraticRankOneInclusion
import MOC.Normal
import MOC.TwoByTwoTensorPermutationLaw
import Mathlib.LinearAlgebra.Matrix.Spectrum

/-! Spectral data and diagonal unitary transport for quadratic images of Hermitian rank-one updates. -/

open BigOperators Finset Matrix Polynomial

namespace MOC

noncomputable section

variable {n : ℕ}

private def coordinatePhase (z : ℂ) : ℂ :=
  if z = 0 then 1 else z / (‖z‖ : ℂ)

private theorem coordinatePhase_norm (z : ℂ) : ‖coordinatePhase z‖ = 1 := by
  by_cases hz : z = 0
  · simp [coordinatePhase, hz]
  · rw [coordinatePhase, if_neg hz, norm_div, Complex.norm_real,
      Real.norm_of_nonneg (norm_nonneg _), div_self (norm_ne_zero_iff.mpr hz)]

private theorem coordinatePhase_mul_norm (z : ℂ) : coordinatePhase z * (‖z‖ : ℂ) = z := by
  by_cases hz : z = 0
  · simp [hz]
  · rw [coordinatePhase, if_neg hz, div_mul_cancel₀ _
      (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz))]

private theorem conjugate_rank_one (d : Fin n → ℝ) (w : Fin n → ℂ) :
    let D := diagonal (fun i => coordinatePhase (w i))
    let v := fun i => ‖w i‖
    D * (diagonal d + vecMulVec v v).map Complex.ofRealHom * Dᴴ =
      diagonal (fun i => (d i : ℂ)) + vecMulVec w (star w) := by
  intro D v
  have hD : IsUnitary D := diagonal_phase_unitary _ (fun i => by
    rw [← Complex.norm_mul_self_eq_normSq, coordinatePhase_norm, one_mul])
  have hc : D * diagonal (fun i => (d i : ℂ)) = diagonal (fun i => (d i : ℂ)) * D := by
    simp only [D, Matrix.diagonal_mul_diagonal, funext (fun i => mul_comm (coordinatePhase (w i)) _)]
  have hd : D * diagonal (fun i => (d i : ℂ)) * Dᴴ = diagonal (fun i => (d i : ℂ)) := by
    rw [hc, Matrix.mul_assoc, hD.1, Matrix.mul_one]
  rw [Matrix.map_add _ (map_add _), Matrix.diagonal_map (map_zero Complex.ofRealHom)]
  simp only [Complex.ofRealHom_eq_coe, Matrix.mul_add, Matrix.add_mul, hd]
  congr 1
  ext i j : 1
  simp only [D, Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Matrix.map_apply, Matrix.vecMulVec_apply, map_mul, Pi.star_apply]
  change coordinatePhase (w i) * ((v i : ℂ) * (v j : ℂ)) * star (coordinatePhase (w j)) = _
  have hj : (v j : ℂ) * star (coordinatePhase (w j)) = star (w j) := by
    calc
      _ = star (coordinatePhase (w j) * (v j : ℂ)) := by
        rw [StarMul.star_mul, show star (v j : ℂ) = (v j : ℂ) from Complex.conj_ofReal _]
      _ = _ := by rw [coordinatePhase_mul_norm]
  rw [← mul_assoc (coordinatePhase (w i)), coordinatePhase_mul_norm, mul_assoc, hj]

private def quadraticMatrix (c e : ℂ) (H : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ := H*H+c • H+e • 1

private theorem conjugate_quadratic (D H : Matrix (Fin n) (Fin n) ℂ) (hD : IsUnitary D)
    (s c e : ℂ) (hs : s * s = 1) :
    quadraticMatrix c e (s • (D * H * Dᴴ)) = D * quadraticMatrix (c*s) e H * Dᴴ := by
  have hsq : (D * H * Dᴴ) * (D * H * Dᴴ) = D * (H*H) * Dᴴ := by
    calc
      _ = D * H * (Dᴴ * D) * H * Dᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hD.2, Matrix.mul_one, Matrix.mul_assoc D H H]
  simp only [quadraticMatrix, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    hs, one_smul, hsq, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hD.1]

private theorem quadraticMatrix_diagonal (h : Fin n → ℝ) (c e : ℂ) :
    quadraticMatrix c e (diagonal (fun i => (h i : ℂ))) =
      diagonal (secularQuadraticLabels h c e) := by
  unfold quadraticMatrix
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_smul, ← Matrix.diagonal_one,
    ← Matrix.diagonal_smul, Matrix.diagonal_add, Matrix.diagonal_add]
  apply congrArg Matrix.diagonal
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.one_apply, mul_one, secularQuadraticLabels, pow_two]

private theorem conjugate_charpoly (U H : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitary U) :
    (U * H * Uᴴ).charpoly = H.charpoly := by
  let Cmap : Matrix (Fin n) (Fin n) ℂ →+* Matrix (Fin n) (Fin n) ℂ[X] :=
    (Polynomial.C : ℂ →+* ℂ[X]).mapMatrix
  have hc : Commute (Matrix.scalar (Fin n) (X : ℂ[X])) (Cmap U) :=
    Matrix.scalar_commute _ (Commute.all _) _
  have hUU : Cmap U * Cmap Uᴴ = 1 := by rw [← Cmap.map_mul, hU.1, Cmap.map_one]
  have hm : (U * H * Uᴴ).charmatrix = Cmap U * H.charmatrix * Cmap Uᴴ := by
    change Matrix.scalar (Fin n) X - Cmap (U * H * Uᴴ) =
      Cmap U * (Matrix.scalar (Fin n) X - Cmap H) * Cmap Uᴴ
    rw [Cmap.map_mul, Cmap.map_mul, Matrix.mul_sub, Matrix.sub_mul,
      ← hc.eq, Matrix.mul_assoc (Matrix.scalar (Fin n) X), hUU, Matrix.mul_one]
  have hd : (Cmap U).det * (Cmap Uᴴ).det = 1 := by
    rw [← Matrix.det_mul, hUU, Matrix.det_one]
  rw [Matrix.charpoly, hm, Matrix.det_mul, Matrix.det_mul, mul_right_comm, hd, one_mul]
  rfl

private theorem real_rank_one_charpoly (d v : Fin n → ℝ) :
    ∃ h : Fin n → ℝ, ∃ U : Matrix (Fin n) (Fin n) ℂ,
      IsUnitary U ∧
      (diagonal d + vecMulVec v v).charpoly = ∏ i, (X - C (h i)) ∧
      (diagonal d + vecMulVec v v).map Complex.ofRealHom =
        U * diagonal (fun i => (h i : ℂ)) * Uᴴ := by
  let A : Matrix (Fin n) (Fin n) ℝ := diagonal d + vecMulVec v v
  let H : Matrix (Fin n) (Fin n) ℂ := A.map Complex.ofRealHom
  have hH : H.IsHermitian := by
    ext i j : 1
    simp only [H, A, Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.add_apply, map_add,
      Matrix.vecMulVec_apply, Complex.star_def, Complex.ofRealHom_eq_coe,
      Complex.conj_ofReal, mul_comm (v j)]
    rw [show diagonal d j i = diagonal d i j from congrFun (congrFun (Matrix.diagonal_transpose d) i) j]
  let h := hH.eigenvalues
  let U : Matrix (Fin n) (Fin n) ℂ := hH.eigenvectorUnitary
  have hU : IsUnitary U :=
    ⟨Matrix.mem_unitaryGroup_iff.mp hH.eigenvectorUnitary.property,
      Matrix.mem_unitaryGroup_iff'.mp hH.eigenvectorUnitary.property⟩
  have hspec : H = U * diagonal (fun i => (h i : ℂ)) * Uᴴ := hH.spectral_theorem
  refine ⟨h, U, hU, ?_, hspec⟩
  apply Polynomial.map_injective (f := Complex.ofRealHom) Complex.ofReal_injective
  rw [← Matrix.charpoly_map]
  change H.charpoly = _
  rw [hspec, conjugate_charpoly _ _ hU, Matrix.charpoly_of_upperTriangular
    _ (Matrix.blockTriangular_diagonal _)]
  rw [← Polynomial.coe_mapRingHom, map_prod]
  simp only [Polynomial.coe_mapRingHom, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_C, Complex.ofRealHom_eq_coe, Matrix.diagonal_apply_eq]

/-- The quadratic image in the determinant inclusion theorem is normal,
has the stated characteristic roots, and is a diagonal-plus-rank-two matrix. -/
theorem quadratic_rank_one_hermitian_characteristics
    (d v h : Fin n → ℝ)
    (hh : (diagonal d + vecMulVec v v).charpoly = ∏ i, (X - C (h i)))
    (c e : ℂ) :
    let H := (diagonal d + vecMulVec v v).map Complex.ofRealHom
    let Q := H*H+c • H+e • 1
    IsStarNormal Q ∧
      Q.charpoly.roots = (Finset.univ : Finset (Fin n)).val.map (secularQuadraticLabels h c e) ∧
      (Q - diagonal (secularQuadraticLabels d c e)).rank ≤ 2 := by
  intro H Q
  obtain ⟨k, U, hU, hk, hH⟩ := real_rank_one_charpoly d v
  change H = _ at hH
  have hQ : Q = U * diagonal (secularQuadraticLabels k c e) * Uᴴ := by
    have hconj := conjugate_quadratic U (diagonal (fun i => (k i : ℂ))) hU 1 c e (one_mul 1)
    rw [one_smul, mul_one, quadraticMatrix_diagonal] at hconj
    change quadraticMatrix c e H = _
    rw [hH, hconj]
  refine ⟨hQ.symm ▸ isStarNormal_unitary_diagonalization _ hU, ?_, ?_⟩
  · have hprod (b : Fin n → ℝ) : (∏ i, (X - C (b i))).roots =
        (Finset.univ : Finset (Fin n)).val.map b := by
      change ((Finset.univ : Finset (Fin n)).val.map ((fun x : ℝ => X - C x) ∘ b)).prod.roots = _
      rw [← Multiset.map_map, Polynomial.roots_multiset_prod_X_sub_C]
    have hlabels : (Finset.univ : Finset (Fin n)).val.map h =
        (Finset.univ : Finset (Fin n)).val.map k := by
      rw [← hprod h, ← hprod k, ← hh, ← hk]
    rw [hQ, roots_unitary_diagonalization _ hU]
    let p (x : ℝ) : ℂ := (x : ℂ)^2+c*x+e
    change (Finset.univ : Finset (Fin n)).val.map (p ∘ k) =
      (Finset.univ : Finset (Fin n)).val.map (p ∘ h)
    rw [← Multiset.map_map, ← Multiset.map_map, hlabels]
  · let D := diagonal (fun i => (d i : ℂ))
    let w (i : Fin n) : ℂ := v i
    have hshape : H = D + vecMulVec w w := by
      change (diagonal d + vecMulVec v v).map Complex.ofRealHom = _
      rw [Matrix.map_add _ (map_add _), Matrix.diagonal_map (map_zero Complex.ofRealHom)]
      congr 1
      ext i j : 1
      simp only [Matrix.map_apply, Matrix.vecMulVec_apply, map_mul, Complex.ofRealHom_eq_coe, w]
    have heq : Q - diagonal (secularQuadraticLabels d c e) =
        H*H+c • H-(D*D+c • D) := by
      rw [← quadraticMatrix_diagonal d c e]
      change H*H+c • H+e • 1-(D*D+c • D+e • 1) = _
      abel
    rw [heq, hshape]
    exact rank_quadratic_image_sub_diagonal_le_two (fun i => (d i : ℂ)) w w c

/-- A monic quadratic of a signed Hermitian rank-one perturbation of a real
diagonal matrix satisfies determinant inclusion with every complex diagonal
partner. The spectra in the hull have their algebraic multiplicities. -/
theorem det_quadratic_signed_rank_one_hermitian_mem_hull
    (d : Fin n → ℝ) (w : Fin n → ℂ) (s : ℝ) (hs : s*s = 1) (c e : ℂ)
    (a b : Fin n → ℂ) :
    let H := diagonal (fun i => (d i : ℂ)) + (s : ℂ) • vecMulVec w (star w)
    let Q := H*H+c • H+e • 1
    Q.charpoly.roots = (Finset.univ : Finset (Fin n)).val.map b →
      (Q+diagonal a).det ∈ convexHull ℝ (Set.range (matchingProduct b a)) := by
  intro H Q hroots
  let d' (i : Fin n) : ℝ := s*d i
  let v (i : Fin n) : ℝ := ‖w i‖
  let A := (diagonal d' + vecMulVec v v).map Complex.ofRealHom
  let D := diagonal (fun i => coordinatePhase (w i))
  let c' := c*(s : ℂ)
  have hD : IsUnitary D := diagonal_phase_unitary _ (fun i => by
    rw [← Complex.norm_mul_self_eq_normSq, coordinatePhase_norm, one_mul])
  have hs' : (s : ℂ)*(s : ℂ) = 1 := by exact_mod_cast hs
  have hH : H = (s : ℂ) • (D * A * Dᴴ) := by
    change diagonal _ + (s : ℂ) • vecMulVec w (star w) = _
    rw [conjugate_rank_one d' w, smul_add, ← Matrix.diagonal_smul]
    congr 1
    apply congrArg Matrix.diagonal
    funext i
    change (d i : ℂ) = (s : ℂ)*((s*d i : ℝ) : ℂ)
    rw [Complex.ofReal_mul, ← mul_assoc, hs', one_mul]
  have hQ : Q = D * quadraticMatrix c' e A * Dᴴ := by
    change quadraticMatrix c e H = _
    rw [hH, conjugate_quadratic D A hD (s : ℂ) c e hs']
  have ha : D * diagonal a * Dᴴ = diagonal a := by
    have hc : D * diagonal a = diagonal a * D := by
      simp only [D, Matrix.diagonal_mul_diagonal, funext (fun i => mul_comm (coordinatePhase (w i)) (a i))]
    rw [hc, Matrix.mul_assoc, hD.1, Matrix.mul_one]
  have hdet : (Q + diagonal a).det = (quadraticMatrix c' e A + diagonal a).det := by
    rw [← det_unitary_conjugation D (quadraticMatrix c' e A + diagonal a) hD,
      Matrix.mul_add, Matrix.add_mul, ha, hQ]
  obtain ⟨h, U, hU, hChar, hA⟩ := real_rank_one_charpoly d' v
  let b' := secularQuadraticLabels h c' e
  have hQ' : Q = (D*U) * diagonal b' * (D*U)ᴴ := by
    change A = _ at hA
    rw [hQ, hA]
    have h := conjugate_quadratic U (diagonal (fun i => (h i : ℂ))) hU 1 c' e (one_mul 1)
    rw [one_smul, mul_one, quadraticMatrix_diagonal] at h
    rw [h, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc, b']
  have hDU : IsUnitary (D*U) := by
    have hD' : IsUnitary Dᴴ := ⟨by simpa only [Matrix.conjTranspose_conjTranspose] using hD.2,
      by simpa only [Matrix.conjTranspose_conjTranspose] using hD.1⟩
    simpa only [Matrix.conjTranspose_conjTranspose] using relative_unitary Dᴴ U hD' hU
  have hb : (Finset.univ : Finset (Fin n)).val.map b = (Finset.univ : Finset (Fin n)).val.map b' := by
    rw [← hroots, hQ', roots_unitary_diagonalization _ hDU]
  obtain ⟨σ, rfl⟩ := exists_perm_of_equal_multisets b b' hb
  rw [hdet, show a = a ∘ (Equiv.refl (Fin n)) from rfl, matchingRange_relabel]
  exact det_quadratic_rank_one_hermitian_mem_hull d' v h hChar c' e a

end

end MOC
