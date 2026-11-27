import MOC.SecularCauchyCommonWeights
import MOC.SubsetMarkerTest
import MOC.Normal
import MOC.UniversalMatchingWeights
import Mathlib.Topology.Algebra.Polynomial

/-! A common permutation law for a simple real Hermitian rank-one update. -/

open BigOperators Filter Finset Matrix Polynomial Set
open scoped Topology

namespace MOC

noncomputable section

variable {n : ℕ}

private theorem secularEvaluationDet_eq_update_of_nonneg (d r : Fin n → ℝ)
    (hr : ∀ i, 0 ≤ r i) (p : ℝ[X]) (a : Fin n → ℝ) :
    secularEvaluationDet d r p a =
      (diagonal a + Polynomial.aeval (diagonal d +
        vecMulVec (fun i => Real.sqrt (r i)) (fun i => Real.sqrt (r i))) p).det := by
  let R (t : ℝ) (i : Fin n) := r i + t
  let F (t : ℝ) := secularEvaluationDet d (R t) p a
  let H (t : ℝ) := diagonal d + vecMulVec (fun i => Real.sqrt (R t i)) (fun i => Real.sqrt (R t i))
  let G (t : ℝ) := (diagonal a + Polynomial.aeval (H t) p).det
  have hK : Continuous (fun t : ℝ => secularColumnModel d (R t)) := by
    apply continuous_matrix
    intro i j
    simp only [secularColumnModel, Matrix.add_apply, Matrix.of_apply, R]
    fun_prop
  have hF : Continuous F :=
    (continuous_const.add (p.continuous_aeval.comp hK)).matrix_det
  have hH : Continuous H := by
    apply continuous_matrix
    intro i j
    simp only [H, Matrix.add_apply, Matrix.vecMulVec_apply, R]
    fun_prop
  have hG : Continuous G :=
    (continuous_const.add (p.continuous_aeval.comp hH)).matrix_det
  have hfg : F =ᶠ[𝓝[>] (0 : ℝ)] G := by
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    exact secularEvaluationDet_eq_update_of_pos d (R t) (fun i => add_pos_of_nonneg_of_pos (hr i) ht) p a
  have he := tendsto_nhds_unique_of_eventuallyEq
    (hF.continuousAt (x := (0 : ℝ))).continuousWithinAt
    (hG.continuousAt (x := (0 : ℝ))).continuousWithinAt hfg
  simpa only [F, G, H, R, add_zero] using he

private theorem matrix_aeval_map_real_complex (A : Matrix (Fin n) (Fin n) ℝ) (p : ℝ[X]) :
    (Polynomial.aeval A p).map Complex.ofRealHom =
      Polynomial.aeval (A.map Complex.ofRealHom) (p.map Complex.ofRealHom) := by
  let X : Matrix (Fin n) (Fin n) ℝ →+* Matrix (Fin n) (Fin n) ℂ :=
    Complex.ofRealHom.mapMatrix
  change X (Polynomial.aeval A p) = _
  apply Polynomial.map_aeval_eq_aeval_map (ψ := X)
  ext s i j
  change (algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ) (Complex.ofRealHom s)) i j =
    X (algebraMap ℝ (Matrix (Fin n) (Fin n) ℝ) s) i j
  by_cases hij : i = j
  · subst j
    simp [X, Algebra.algebraMap_eq_smul_one, Matrix.smul_apply, Matrix.one_apply_eq,
      RingHom.mapMatrix_apply, Matrix.map_apply, smul_eq_mul]
  · simp [X, Algebra.algebraMap_eq_smul_one, Matrix.smul_apply,
      Matrix.one_apply_ne hij, RingHom.mapMatrix_apply, Matrix.map_apply, smul_eq_mul]

private theorem matrix_aeval_diagonal_complex (x : Fin n → ℂ) (p : ℂ[X]) :
    Polynomial.aeval (diagonal x) p = diagonal (fun i => p.eval (x i)) := by
  rw [Polynomial.aeval_eq_sum_range]
  ext i j : 1
  simp only [Matrix.sum_apply, Matrix.diagonal_pow, Matrix.smul_apply, smul_eq_mul]
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq, Polynomial.eval_eq_sum_range, Pi.pow_apply]
  · simp only [Matrix.diagonal_apply_ne _ hij, mul_zero, Finset.sum_const_zero]

private theorem secular_polynomial_determinant_transport (A : Matrix (Fin n) (Fin n) ℝ)
    (h : Fin n → ℝ) (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitary U)
    (hA : A.map Complex.ofRealHom = U*diagonal (fun i => (h i : ℂ))*Uᴴ)
    (p : ℝ[X]) (a : Fin n → ℝ) :
    ((diagonal a + Polynomial.aeval A p).det : ℂ) =
      determinantValue (fun i => (a i : ℂ)) (fun i => Complex.ofReal (p.eval (h i))) U := by
  let B := A.map Complex.ofRealHom
  let D := diagonal (fun i => (h i : ℂ))
  let q := p.map Complex.ofRealHom
  have hBU : B*U=U*D := by
    rw [show B=U*D*Uᴴ from hA, Matrix.mul_assoc (U*D), hU.2, Matrix.mul_one]
  have hpol : Polynomial.aeval B q = U*Polynomial.aeval D q*Uᴴ := by
    have h := polynomial_aeval_intertwines hBU q
    rw [← h, Matrix.mul_assoc, hU.1, Matrix.mul_one]
  have hv (z : ℝ) : q.eval (z : ℂ) = Complex.ofReal (p.eval z) := by
    change (p.map Complex.ofRealHom).eval (Complex.ofRealHom z) = Complex.ofRealHom (p.eval z)
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]
  have hmap : (diagonal a + Polynomial.aeval A p).map Complex.ofRealHom =
      diagonal (fun i => (a i : ℂ)) + U*diagonal (fun i => Complex.ofReal (p.eval (h i)))*Uᴴ := by
    have hdiag : (diagonal a).map Complex.ofRealHom = diagonal (fun i => (a i : ℂ)) := by
      ext i j : 1
      by_cases hij : i = j <;> simp [Matrix.map_apply, Matrix.diagonal_apply, hij]
    rw [← RingHom.mapMatrix_apply, map_add, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply,
      hdiag, matrix_aeval_map_real_complex]
    change _ = _
    rw [show Polynomial.aeval (A.map Complex.ofRealHom) (p.map Complex.ofRealHom) =
        U*Polynomial.aeval D q*Uᴴ from hpol, matrix_aeval_diagonal_complex]
    simp only [D, hv]
  calc
    _ = ((diagonal a + Polynomial.aeval A p).map Complex.ofRealHom).det :=
      Complex.ofRealHom.map_det _
    _ = _ := congrArg Matrix.det hmap

private theorem real_characteristic_of_complex_diagonalization (A : Matrix (Fin n) (Fin n) ℝ)
    (h : Fin n → ℝ) (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitary U)
    (hA : A.map Complex.ofRealHom = U * diagonal (fun i => (h i : ℂ)) * Uᴴ) :
    A.charpoly = ∏ i, (X - C (h i)) := by
  let Cmap : Matrix (Fin n) (Fin n) ℂ →+* Matrix (Fin n) (Fin n) ℂ[X] :=
    (Polynomial.C : ℂ →+* ℂ[X]).mapMatrix
  let D := diagonal (fun i => (h i : ℂ))
  have hc : Commute (Matrix.scalar (Fin n) (X : ℂ[X])) (Cmap U) :=
    Matrix.scalar_commute _ (Commute.all _) _
  have hUU : Cmap U * Cmap Uᴴ = 1 := by rw [← Cmap.map_mul, hU.1, Cmap.map_one]
  have hm : (U * D * Uᴴ).charmatrix = Cmap U * D.charmatrix * Cmap Uᴴ := by
    change Matrix.scalar (Fin n) X - Cmap (U * D * Uᴴ) =
      Cmap U * (Matrix.scalar (Fin n) X - Cmap D) * Cmap Uᴴ
    rw [Cmap.map_mul, Cmap.map_mul, Matrix.mul_sub, Matrix.sub_mul,
      ← hc.eq, Matrix.mul_assoc (Matrix.scalar (Fin n) X), hUU, Matrix.mul_one]
  have hd : (Cmap U).det * (Cmap Uᴴ).det = 1 := by
    rw [← Matrix.det_mul, hUU, Matrix.det_one]
  have he : (U*D*Uᴴ).charpoly = D.charpoly := by
    rw [Matrix.charpoly, hm, Matrix.det_mul, Matrix.det_mul, mul_right_comm, hd, one_mul]
    rfl
  apply Polynomial.map_injective (f := Complex.ofRealHom) Complex.ofReal_injective
  rw [← Matrix.charpoly_map, hA, he, Matrix.charpoly_of_upperTriangular _ (Matrix.blockTriangular_diagonal _)]
  rw [← Polynomial.coe_mapRingHom, map_prod]
  simp only [D, Polynomial.coe_mapRingHom, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_C, Complex.ofRealHom_eq_coe, Matrix.diagonal_apply_eq]

/-- The same nonnegative matching weights represent every complex spectral
pair for any eigenbasis of a real Hermitian rank-one update with simple spectrum. -/
theorem hermitian_rankOne_eigenbasis_common_weights
    (d v h : Fin n → ℝ) (hv : ∀ i, 0 ≤ v i) (hh : Function.Injective h)
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitary U)
    (hUd : (diagonal d + vecMulVec v v).map Complex.ofRealHom =
      U*diagonal (fun i => (h i : ℂ))*Uᴴ) :
    ∃ w : Equiv.Perm (Fin n) → ℝ, (∀ σ, 0 ≤ w σ) ∧ (∑ σ, w σ = 1) ∧
      ∀ a b : Fin n → ℂ, weightedMatchingValue a b w = determinantValue a b U := by
  classical
  let ι := Fin n
  let κ := Finset ι × Finset ι
  let r (i : ι) := v i * v i
  let f (k : κ) := secularSelectionPolynomial h k.2
  let x (k : κ) (i : ι) : ℝ := if i ∈ k.1 then 0 else 1
  have hr (i : ι) : 0 ≤ r i := mul_nonneg (hv i) (hv i)
  have hchar := real_characteristic_of_complex_diagonalization _ h U hU hUd
  have hspec : secularCharacteristic d r = ∏ i, (X-C (h i)) := by
    rwa [charpoly_diagonal_add_outer] at hchar
  have hprofile := secularEvaluationProfile_mem_hull f n d r h hh hr hspec x
  obtain ⟨γ, iγ, c, T, hc, hsum, hT, hmix⟩ := mem_convexHull_iff_exists_fintype.mp hprofile
  letI := iγ
  have hπ (k : γ) : ∃ σ : Equiv.Perm ι, secularEvaluationMatching h f x σ = T k := hT k
  choose π hπ using hπ
  let w (σ : Equiv.Perm ι) := ∑ k ∈ (univ : Finset γ).filter (fun k => π k = σ), c k
  have hw (σ : Equiv.Perm ι) : 0 ≤ w σ := Finset.sum_nonneg fun k _ => hc k
  have hws : ∑ σ, w σ=1 := by
    change (∑ σ, ∑ k ∈ (univ : Finset γ).filter (fun k => π k = σ), c k)=1
    rw [Finset.sum_fiberwise, hsum]
  refine ⟨w,hw,hws,?_⟩
  apply (weightedMatchingValue_eq_all_iff_subset_markers U hU w).mpr
  intro I J hIJ _
  let k : κ := (I,J)
  have hcoord := congrArg (fun y : κ → ℝ => y k) hmix
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ← hπ] at hcoord
  have htransfer : (secularEvaluationProfile d r f x k : ℂ) =
      determinantValue (fun i => if i ∈ I then 0 else 1) (fun j => if j ∈ J then 1 else 0) U := by
    have hroot (i : ι) : Real.sqrt (r i) = v i := by
      change Real.sqrt (v i * v i) = v i
      rw [← sq, Real.sqrt_sq_eq_abs, abs_of_nonneg (hv i)]
    rw [secularEvaluationProfile, secularEvaluationDet_eq_update_of_nonneg d r hr,
      show (fun i => Real.sqrt (r i)) = v from funext hroot,
      secular_polynomial_determinant_transport _ h U hU hUd]
    simp only [f, x, k, secularSelectionPolynomial_eval h hh J, apply_ite,
      Complex.ofReal_zero, Complex.ofReal_one]
  have hm (σ : Equiv.Perm ι) : (secularEvaluationMatching h f x σ k : ℂ) =
      matchingProduct (fun i => if i ∈ I then 0 else 1) (fun j => if j ∈ J then 1 else 0) σ := by
    simp only [secularEvaluationMatching, realMatchingProduct, matchingProduct, k, f, x,
      secularSelectionPolynomial_eval h hh J, Complex.ofReal_prod, Complex.ofReal_add,
      apply_ite, Complex.ofReal_zero, Complex.ofReal_one]
  rw [← htransfer]
  have he := congrArg (fun y : ℝ => (y : ℂ)) hcoord
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, hm] at he
  rw [← he, weightedMatchingValue]
  simp only [w, Complex.ofReal_sum, Finset.sum_mul]
  rw [← Finset.sum_fiberwise (s := (univ : Finset γ)) π]
  apply Finset.sum_congr rfl
  intro σ _
  apply Finset.sum_congr rfl
  intro j hj
  rw [(Finset.mem_filter.mp hj).2]

/-- One probability law works for all complex lists in any specified eigenbasis of a
real Hermitian diagonal rank-one update with simple spectrum. -/
theorem hasUniversalMatchingWeights_of_hermitian_rankOne_eigenbasis
    (d v h : Fin n → ℝ) (hv : ∀ i, 0 ≤ v i) (hh : Function.Injective h)
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitary U)
    (hUd : (diagonal d + vecMulVec v v).map Complex.ofRealHom =
      U * diagonal (fun i => (h i : ℂ)) * Uᴴ) :
    HasUniversalMatchingWeights U := by
  obtain ⟨w, hw, hs, hmatch⟩ := hermitian_rankOne_eigenbasis_common_weights d v h hv hh U hU hUd
  exact ⟨w, hw, hs, fun a b => (hmatch a b).symm⟩

/-- A simple Hermitian diagonal rank-one eigenbasis gives determinant inclusion
for arbitrary complex spectral lists. -/
theorem holds_of_hermitian_rankOne_eigenbasis
    (d v h : Fin n → ℝ) (hv : ∀ i, 0 ≤ v i) (hh : Function.Injective h)
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitary U)
    (hUd : (diagonal d + vecMulVec v v).map Complex.ofRealHom =
      U * diagonal (fun i => (h i : ℂ)) * Uᴴ) (a b : Fin n → ℂ) :
    Holds a b U :=
  (hasUniversalMatchingWeights_of_hermitian_rankOne_eigenbasis d v h hv hh U hU hUd).holds a b

end

end MOC
