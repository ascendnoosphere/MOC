import MOC.DeterminantSecondVariation
import MOC.Variational

/-! The determinant Hessian in a conjugation direction, written using the
relative product of two unitaries. -/

open Filter Matrix
open scoped Topology

namespace MOC

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

set_option maxHeartbeats 500000 in
/-- The determinant support Hessian at a stationary unitary conjugacy maximum
can be tested with the two conjugates of a skew-Hermitian generator. -/
theorem relative_unitary_trace_hessian_nonpos
    (U W : Matrix ι ι ℂ) (hU : IsUnitary U) (hW : IsUnitary W) (ρ η : ℂ)
    (hT : IsUnit ((1 : Matrix ι ι ℂ) + ρ • W).det)
    (hmax : ∀ V : Matrix ι ι ℂ, IsUnitary V →
      (η * (U + V * (ρ • (U * W)) * Vᴴ).det).re ≤ (η * (U + ρ • (U * W)).det).re)
    (K : Matrix ι ι ℂ) (hK : Kᴴ = -K) :
    let T := (1 : Matrix ι ι ℂ) + ρ • W
    let P := (ρ • W) * T⁻¹
    let R := Uᴴ * K * U
    let S := W * K * Wᴴ
    let D := (R - S) * P
    let A := (R * R + S * S - (R * S + R * S)) * P
    let ω := η * (U + ρ • (U * W)).det
    (ω * (A.trace + D.trace ^ 2 - (D * D).trace)).re ≤ 0 := by
  intro T P R S D A ω
  let V (t : ℝ) := NormedSpace.exp ℝ (t • K)
  let E (t : ℝ) := NormedSpace.exp ℝ (t • R)
  let F (t : ℝ) := NormedSpace.exp ℝ (t • (-S))
  let X (t : ℝ) := E t * F t
  let M (t : ℝ) := (1 : Matrix ι ι ℂ) + (X t - 1) * P
  let Md (t : ℝ) := ((E t * R) * F t + E t * (F t * (-S))) * P
  have hV (t : ℝ) : IsUnitary (V t) := by
    have hs : t • K ∈ skewAdjoint (Matrix ι ι ℂ) := by
      rw [skewAdjoint.mem_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_smul,
        star_trivial, hK, smul_neg]
    have he := unitary.mem_iff.mp (NormedSpace.exp_mem_unitary_of_mem_skewAdjoint ℝ hs)
    exact ⟨he.2, he.1⟩
  have hVstar (t : ℝ) : (V t)ᴴ = NormedSpace.exp ℝ (t • (-K)) := by
    change (NormedSpace.exp ℝ (t • K))ᴴ = _
    rw [← Matrix.exp_conjTranspose ℝ, Matrix.conjTranspose_smul, star_trivial, hK]
  have hunit (Z : Matrix ι ι ℂ) (hZ : IsUnitary Z) : IsUnit Z :=
    (Matrix.isUnit_iff_isUnit_det Z).mpr (isUnit_iff_ne_zero.mpr (det_ne_zero_of_unitary hZ))
  have hE (t : ℝ) : E t = Uᴴ * V t * U := by
    simpa only [E, R, V, Matrix.inv_eq_right_inv hU.1, Matrix.mul_smul, Matrix.smul_mul] using
      Matrix.exp_conj' ℝ U (t • K) (hunit U hU)
  have hF (t : ℝ) : F t = W * (V t)ᴴ * Wᴴ := by
    rw [hVstar]
    simpa only [F, S, Matrix.inv_eq_right_inv hW.1, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_neg, Matrix.neg_mul] using Matrix.exp_conj ℝ W (t • (-K)) (hunit W hW)
  have hX (t : ℝ) : U * X t * W = V t * (U * W) * (V t)ᴴ := by
    calc
      _ = V t * (U * W) * (V t)ᴴ * (Wᴴ * W) := by
        simp only [X, hE, hF, ← Matrix.mul_assoc, hU.1, Matrix.one_mul]
      _ = _ := by rw [hW.2, Matrix.mul_one]
  have hP : P * T = ρ • W := by
    dsimp only [P]
    rw [Matrix.mul_assoc, T.nonsing_inv_mul hT, Matrix.mul_one]
  have hpath (t : ℝ) : U * M t * T = U + V t * (ρ • (U * W)) * (V t)ᴴ := by
    calc
      _ = U * (T + (X t - 1) * (ρ • W)) := by
        simp only [M, Matrix.mul_assoc U, Matrix.add_mul, Matrix.one_mul,
          Matrix.mul_assoc (X t - 1), hP]
      _ = U + ρ • (U * X t * W) := by
        simp only [T, Matrix.mul_add, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
          Matrix.smul_mul, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc,
          smul_add, smul_sub, neg_one_smul, smul_neg]
        abel
      _ = _ := by rw [hX]; simp only [Matrix.mul_smul, Matrix.smul_mul]
  have hconst : U * T = U + ρ • (U * W) := by simp [T, Matrix.mul_add, Matrix.mul_smul]
  have hdet (t : ℝ) : (U + V t * (ρ • (U * W)) * (V t)ᴴ).det =
      (U + ρ • (U * W)).det * (M t).det := by
    rw [← hpath, ← hconst, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul]
    ring
  have hM₀ : M 0 = 1 := by simp [M, X, E, F, NormedSpace.exp_zero]
  have hMd₀ : Md 0 = D := by
    simp [Md, D, E, F, NormedSpace.exp_zero, sub_eq_add_neg]
  have he (t : ℝ) : HasDerivAt E (E t * R) t := hasDerivAt_exp_smul_const R t
  have hf (t : ℝ) : HasDerivAt F (F t * (-S)) t := hasDerivAt_exp_smul_const (-S) t
  have hMd (t : ℝ) : HasDerivAt M (Md t) t :=
    ((((he t).mul (hf t)).sub_const 1).mul_const P).const_add 1
  have he₀ : HasDerivAt E R 0 := by simpa [E, NormedSpace.exp_zero] using he 0
  have hf₀ : HasDerivAt F (-S) 0 := by simpa [F, NormedSpace.exp_zero] using hf 0
  have hMdd : HasDerivAt Md A 0 := by
    let A' := ((R * R) * F 0 + (E 0 * R) * (-S) +
      (R * (F 0 * (-S)) + E 0 * ((-S) * (-S)))) * P
    have hv : HasDerivAt Md A' 0 :=
      (((he₀.mul_const R).mul hf₀).add (he₀.mul (hf₀.mul_const (-S)))).mul_const P
    have hA' : A' = A := by
      simp only [A', A, E, F, zero_smul, NormedSpace.exp_zero, Matrix.one_mul, Matrix.mul_one,
        Matrix.mul_neg, Matrix.neg_mul, neg_neg, sub_eq_add_neg]
      congr 1
      abel
    rwa [hA'] at hv
  have hSecond := hasDerivAt_deriv_det_of_eq_one (Filter.Eventually.of_forall hMd) hM₀ hMdd
  rw [hMd₀] at hSecond
  let f (t : ℝ) : ℝ := (ω * (M t).det).re
  have hmaxf : IsLocalMax f 0 := by
    apply Filter.Eventually.of_forall
    intro t
    have hh := hmax (V t) (hV t)
    rw [hdet t, ← mul_assoc] at hh
    simpa only [f, ω, hM₀, Matrix.det_one, mul_one] using hh
  have hn₀ : (M 0).det ≠ 0 := by simp [hM₀]
  have hn : ∀ᶠ t in 𝓝 (0 : ℝ), (M t).det ≠ 0 :=
    (hasDerivAt_det_of_ne_zero (hMd 0) hn₀).continuousAt.eventually_ne hn₀
  have hf' : ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt f (ω * deriv (fun s => (M s).det) t).re t := by
    filter_upwards [hn] with t ht
    have hdiff := (hasDerivAt_det_of_ne_zero (hMd t) ht).differentiableAt
    exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hdiff.hasDerivAt.const_mul ω)
  have hProj := Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 (hSecond.const_mul ω)
  have hRealSecond : HasDerivAt (deriv f) (ω * (A.trace + D.trace ^ 2 - (D * D).trace)).re 0 :=
    hProj.congr_of_eventuallyEq (hf'.mono fun _ h => h.deriv)
  exact second_derivative_nonpos_of_local_max hmaxf
    (hf'.mono fun _ h => h.differentiableAt) hRealSecond

end MOC
