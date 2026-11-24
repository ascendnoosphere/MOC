import MOC.DeterminantSecondVariation
import MOC.Variational
import MOC.Realification

/-!
# Second-order exclusion test for order-four stationary witnesses

The determinant Hessian below applies to arbitrary complex spectra. Its
restriction to an orthogonal mixer includes every real skew direction and
does not require a contact-set classification.
-/

open Filter Matrix
open scoped Topology

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

set_option maxHeartbeats 500000 in
/-- Nonpositive second variation of the real determinant support under a
unitary conjugation. The two matrix terms are the commutator velocity and
the iterated-commutator acceleration. -/
theorem determinant_orbit_hessian_nonpos
    (A B : Matrix ι ι ℂ) (η : ℂ) (hdet : (A + B).det ≠ 0)
    (hmax : ∀ V : Matrix ι ι ℂ, IsUnitary V →
      (η * (A + V * B * Vᴴ).det).re ≤ (η * (A + B).det).re)
    (K : Matrix ι ι ℂ) (hK : Kᴴ = -K) :
    let C := A + B
    let L := K * B - B * K
    let D := C⁻¹ * L
    (η * C.det *
      ((C⁻¹ * (K * L - L * K)).trace + D.trace ^ 2 - (D * D).trace)).re ≤ 0 := by
  intro C L D
  let E (t : ℝ) := NormedSpace.exp ℝ (t • K)
  let F (t : ℝ) := NormedSpace.exp ℝ (t • (-K))
  let M (t : ℝ) := C⁻¹ * (A + E t * B * F t)
  let V (t : ℝ) := C⁻¹ * (((E t * K) * B) * F t + (E t * B) * (F t * (-K)))
  let J := C⁻¹ * (K * L - L * K)
  let ω := η * C.det
  have hC : IsUnit C.det := isUnit_iff_ne_zero.mpr hdet
  have hunit (t : ℝ) : IsUnitary (E t) := by
    have hs : t • K ∈ skewAdjoint (Matrix ι ι ℂ) := by
      rw [skewAdjoint.mem_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_smul,
        star_trivial, hK, smul_neg]
    have he := unitary.mem_iff.mp (NormedSpace.exp_mem_unitary_of_mem_skewAdjoint ℝ hs)
    exact ⟨he.2, he.1⟩
  have hstar (t : ℝ) : (E t)ᴴ = F t := by
    change (NormedSpace.exp ℝ (t • K))ᴴ = _
    rw [← Matrix.exp_conjTranspose ℝ, Matrix.conjTranspose_smul, star_trivial, hK]
  have hE₀ : E 0 = 1 := by simp [E, NormedSpace.exp_zero]
  have hF₀ : F 0 = 1 := by simp [F, NormedSpace.exp_zero]
  have hM₀ : M 0 = 1 := by
    simpa only [M, hE₀, hF₀, Matrix.one_mul, Matrix.mul_one] using C.nonsing_inv_mul hC
  have hV₀ : V 0 = D := by
    simp only [V, D, L, hE₀, hF₀, Matrix.one_mul, Matrix.mul_one, Matrix.mul_neg, sub_eq_add_neg]
  have he (t : ℝ) : HasDerivAt E (E t * K) t := hasDerivAt_exp_smul_const K t
  have hf (t : ℝ) : HasDerivAt F (F t * (-K)) t := hasDerivAt_exp_smul_const (-K) t
  have hV (t : ℝ) : HasDerivAt M (V t) t :=
    ((((he t).mul_const B).mul (hf t)).const_add A).const_mul C⁻¹
  have he₀ : HasDerivAt E K 0 := by simpa only [hE₀, Matrix.one_mul] using he 0
  have hf₀ : HasDerivAt F (-K) 0 := by simpa only [hF₀, Matrix.one_mul] using hf 0
  have hJ : HasDerivAt V J 0 := by
    have h := ((((he₀.mul_const K).mul_const B).mul hf₀).add
      ((he₀.mul_const B).mul (hf₀.mul_const (-K)))).const_mul C⁻¹
    simp only [hE₀, hF₀, Matrix.one_mul, Matrix.mul_one] at h
    have hacc : K * K * B + K * B * (-K) + (K * B * (-K) + B * ((-K) * (-K))) =
        K * L - L * K := by
      simp only [L, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_neg, Matrix.neg_mul, neg_neg,
        Matrix.mul_assoc]
      abel
    rwa [hacc] at h
  have hSecond := hasDerivAt_deriv_det_of_eq_one (Eventually.of_forall hV) hM₀ hJ
  rw [hV₀] at hSecond
  let f (t : ℝ) := (ω * (M t).det).re
  have hpath (t : ℝ) : C.det * (M t).det = (A + E t * B * (E t)ᴴ).det := by
    rw [hstar, ← Matrix.det_mul]
    congr 1
    change C * (C⁻¹ * (A + E t * B * F t)) = _
    rw [← Matrix.mul_assoc, C.mul_nonsing_inv hC, Matrix.one_mul]
  have hmaxf : IsLocalMax f 0 := by
    apply Eventually.of_forall
    intro t
    have h := hmax (E t) (hunit t)
    rw [← hpath t, ← mul_assoc] at h
    simpa only [f, ω, hM₀, Matrix.det_one, mul_one] using h
  have hn₀ : (M 0).det ≠ 0 := by simp [hM₀]
  have hn : ∀ᶠ t in 𝓝 (0 : ℝ), (M t).det ≠ 0 :=
    (hasDerivAt_det_of_ne_zero (hV 0) hn₀).continuousAt.eventually_ne hn₀
  have hf' : ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt f (ω * deriv (fun s => (M s).det) t).re t := by
    filter_upwards [hn] with t ht
    have h := (hasDerivAt_det_of_ne_zero (hV t) ht).differentiableAt.hasDerivAt
    exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (h.const_mul ω)
  have hProj := Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 (hSecond.const_mul ω)
  have hRealSecond : HasDerivAt (deriv f) (ω * (J.trace + D.trace ^ 2 - (D * D).trace)).re 0 :=
    hProj.congr_of_eventuallyEq (hf'.mono fun _ h => h.deriv)
  exact second_derivative_nonpos_of_local_max hmaxf
    (hf'.mono fun _ h => h.differentiableAt) hRealSecond


omit [DecidableEq ι] in
private theorem symmetric_trace_mul_skew_zero
    (S T : Matrix ι ι ℂ) (hS : Sᵀ = S) (hT : Tᵀ = -T) :
    (S * T).trace = 0 := by
  have h := Matrix.trace_transpose (S * T)
  rw [Matrix.transpose_mul, hS, hT, Matrix.neg_mul, Matrix.trace_neg,
    Matrix.trace_mul_comm T S] at h
  linear_combination (-1 / 2 : ℂ) * h

set_option maxHeartbeats 500000 in
/-- At a real orthogonal support maximizer, purely imaginary symmetric skew
generators give a second-order test whose first trace term is identically
zero. Such generators move off the real orthogonal locus. -/
theorem four_orthogonal_imaginary_hessian_nonpos
    (a b : Fin 4 → ℂ) (η : ℂ) (O : Matrix.orthogonalGroup (Fin 4) ℝ)
    (hdet : determinantValue a b (Complex.ofRealHom.mapMatrix O.val) ≠ 0)
    (hmax : ∀ W : Matrix (Fin 4) (Fin 4) ℂ, IsUnitary W →
      (η * determinantValue a b W).re ≤
        (η * determinantValue a b (Complex.ofRealHom.mapMatrix O.val)).re)
    (S : Matrix (Fin 4) (Fin 4) ℝ) (hS : Sᵀ = S) :
    let U := Complex.ofRealHom.mapMatrix O.val
    let B := U * diagonal b * Uᴴ
    let C := diagonal a + B
    let K := Complex.I • Complex.ofRealHom.mapMatrix S
    let L := K * B - B * K
    let D := C⁻¹ * L
    (η * C.det * ((C⁻¹ * (K * L - L * K)).trace - (D * D).trace)).re ≤ 0 := by
  intro U B C K L D
  let A := diagonal a
  have hU : IsUnitary U := isUnitary_ofReal_orthogonal O
  have hmax' (V : Matrix (Fin 4) (Fin 4) ℂ) (hV : IsUnitary V) :
      (η * (A + V * B * Vᴴ).det).re ≤ (η * (A + B).det).re := by
    have hV' : IsUnitary Vᴴ := by
      simpa only [IsUnitary, Matrix.conjTranspose_conjTranspose] using And.intro hV.2 hV.1
    have hVU : IsUnitary (V * U) := by
      simpa only [Matrix.conjTranspose_conjTranspose] using relative_unitary Vᴴ U hV' hU
    simpa only [determinantValue, A, B, Matrix.conjTranspose_mul, Matrix.mul_assoc] using
      hmax (V * U) hVU
  have hs (i j : Fin 4) : S j i = S i j :=
    congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M i j) hS
  have hK : Kᴴ = -K := by
    ext i j
    change star (Complex.I * (S j i : ℂ)) = -(Complex.I * (S i j : ℂ))
    simp [Complex.star_def, hs]
  have hKT : Kᵀ = K := by
    ext i j
    simp [K, hs]
  have hUT : Uᵀ = Uᴴ := by
    ext i j
    simp [U, Matrix.conjTranspose_apply, Complex.star_def]
  have hUHT : (Uᴴ)ᵀ = U := by rw [← hUT, Matrix.transpose_transpose]
  have hBT : Bᵀ = B := by
    dsimp only [B]
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.diagonal_transpose,
      hUHT, hUT, Matrix.mul_assoc]
  have hCT : Cᵀ = C := by
    simp only [C, Matrix.transpose_add, Matrix.diagonal_transpose, hBT]
  have hCi : (C⁻¹)ᵀ = C⁻¹ := by
    rw [Matrix.inv_def, Matrix.transpose_smul, Matrix.adjugate_transpose, hCT]
  have hLT : Lᵀ = -L := by
    simp only [L, Matrix.transpose_sub, Matrix.transpose_mul, hKT, hBT, neg_sub]
  have hz : D.trace = 0 := symmetric_trace_mul_skew_zero _ _ hCi hLT
  have h := determinant_orbit_hessian_nonpos A B η hdet hmax' K hK
  change (η * C.det * ((C⁻¹ * (K * L - L * K)).trace + D.trace ^ 2 -
    (D * D).trace)).re ≤ 0 at h
  simpa only [hz, zero_pow (Nat.succ_ne_zero 1), add_zero] using h

end

end MOC
