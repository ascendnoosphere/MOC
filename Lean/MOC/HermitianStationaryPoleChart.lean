import MOC.HermitianStationaryHessian

/-! A regular reciprocal change sends a finite stationary pole to the zero
diagonal condition for the Hermitian part of the scaled inverse. -/

open BigOperators Matrix

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem conjugated_diagonal_mul (U : Matrix ι ι ℂ)
    (hU : IsUnitary U) (a b : ι → ℂ) :
    (U * diagonal a * Uᴴ) * (U * diagonal b * Uᴴ) =
      U * diagonal (fun k => a k * b k) * Uᴴ := by
  calc
    _ = U * (diagonal a * (Uᴴ * U) * diagonal b) * Uᴴ := by
      simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [hU.2, Matrix.mul_one, Matrix.diagonal_mul_diagonal]

private theorem conjugated_diagonal_inv (U : Matrix ι ι ℂ)
    (hU : IsUnitary U) (b : ι → ℂ) (hb : ∀ k, b k ≠ 0) :
    (U * diagonal b * Uᴴ)⁻¹ = U * diagonal (fun k => (b k)⁻¹) * Uᴴ := by
  apply Matrix.inv_eq_right_inv
  rw [conjugated_diagonal_mul U hU]
  rw [show (fun k => b k * (b k)⁻¹) = (fun _ => (1 : ℂ)) from
    funext fun k => mul_inv_cancel₀ (hb k), Matrix.diagonal_one, Matrix.mul_one, hU.1]

private theorem reciprocal_sum_factor (A P : Matrix ι ι ℂ)
    (hA : IsUnit A.det) (hP : IsUnit P.det) :
    A * (A⁻¹ + P⁻¹) * P = A + P := by
  rw [Matrix.mul_add, A.mul_nonsing_inv hA, Matrix.add_mul, Matrix.one_mul,
    Matrix.mul_assoc A P⁻¹ P, P.nonsing_inv_mul hP, Matrix.mul_one, add_comm]

private theorem reciprocal_sum_inverse (A P : Matrix ι ι ℂ)
    (hA : IsUnit A.det) (hP : IsUnit P.det) (hM : IsUnit (A + P).det) :
    (A⁻¹ + P⁻¹)⁻¹ = A - A * (A + P)⁻¹ * A := by
  let M := A + P
  let X := A⁻¹ + P⁻¹
  have hfac := reciprocal_sum_factor A P hA hP
  change A * X * P = M at hfac
  have hXP : X * P = A⁻¹ * M := by
    calc
      _ = A⁻¹ * (A * X * P) := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc A⁻¹ A X, A.nonsing_inv_mul hA, Matrix.one_mul]
      _ = _ := by rw [hfac]
  have hXi : X⁻¹ = P * M⁻¹ * A := by
    apply Matrix.inv_eq_right_inv
    rw [← Matrix.mul_assoc X (P * M⁻¹) A, ← Matrix.mul_assoc X P M⁻¹, hXP,
      Matrix.mul_assoc A⁻¹ M M⁻¹, M.mul_nonsing_inv hM, Matrix.mul_one,
      A.nonsing_inv_mul hA]
  change X⁻¹ = A - A * M⁻¹ * A
  rw [hXi, show P = M - A by dsimp only [M]; abel, Matrix.sub_mul, Matrix.sub_mul,
    M.mul_nonsing_inv hM, Matrix.one_mul]

omit [Fintype ι] in
private theorem real_diagonal_isHermitian (f : ι → ℝ) :
    (diagonal fun k => (f k : ℂ)).IsHermitian := by
  apply Matrix.isHermitian_diagonal_iff.mpr
  intro k
  simp [isSelfAdjoint_iff, Complex.star_def]

set_option maxHeartbeats 800000 in
/-- A real stationary pole not in the Hermitian spectrum has multiplicity
at most two at a positive support maximum against an all-nonreal normal
partner. The pole equation is written without division. -/
theorem hermitian_orbit_no_three_regular_pole_equations
    (h : ι → ℝ) (b : ι → ℂ) (U : Matrix ι ι ℂ) (θ : ℂ)
    (hU : IsUnitary U) (hh : Function.Injective h) (hb : ∀ k, (b k).im ≠ 0)
    (hmax : ∀ V : Matrix ι ι ℂ, IsUnitary V →
      (θ * determinantValue (fun k => (h k : ℂ)) b V).re ≤
        (θ * determinantValue (fun k => (h k : ℂ)) b U).re)
    (p : ℝ) (hp : ∀ k, h k ≠ p) {i j k : ι}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    let H := diagonal fun r => (h r : ℂ)
    let B := U * diagonal b * Uᴴ
    let M := H + B
    let η := θ * M.det
    let x (r : ι) := (η * M⁻¹ r r).re
    0 < η.re →
    (h i - p) * x i = η.re → (h j - p) * x j = η.re → (h k - p) * x k = η.re → False := by
  intro H B M η x ha hi hj hk
  let α (r : ι) : ℂ := (h r - p : ℝ)
  let β (r : ι) : ℂ := b r + (p : ℂ)
  let A := diagonal α
  let P (V : Matrix ι ι ℂ) := V * diagonal β * Vᴴ
  let h' (r : ι) := (h r - p)⁻¹
  let b' (r : ι) := (β r)⁻¹
  let H' := diagonal fun r => (h' r : ℂ)
  let Δ := A.det * ∏ r, β r
  let θ' := θ * Δ
  have hα (r : ι) : α r ≠ 0 := Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr (hp r))
  have hβim (r : ι) : (β r).im ≠ 0 := by simpa only [β, Complex.add_im, Complex.ofReal_im, add_zero] using hb r
  have hβ (r : ι) : β r ≠ 0 := fun he => hβim r (by rw [he, Complex.zero_im])
  have hb' (r : ι) : (b' r).im ≠ 0 := by
    rw [show b' r = (β r)⁻¹ from rfl, Complex.inv_im]
    exact div_ne_zero (neg_ne_zero.mpr (hβim r)) (Complex.normSq_pos.mpr (hβ r)).ne'
  have hA : IsUnit A.det := by
    rw [show A = diagonal α from rfl, Matrix.det_diagonal]
    exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun r _ => hα r)
  have hPdet (V : Matrix ι ι ℂ) (hV : IsUnitary V) : (P V).det = ∏ r, β r := by
    rw [show P V = V * diagonal β * Vᴴ from rfl, det_unitary_conjugation V _ hV, Matrix.det_diagonal]
  have hP (V : Matrix ι ι ℂ) (hV : IsUnitary V) : IsUnit (P V).det := by
    rw [hPdet V hV]
    exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun r _ => hβ r)
  have hAi : A⁻¹ = H' := by
    apply Matrix.inv_eq_right_inv
    change diagonal α * diagonal (fun r => (h' r : ℂ)) = 1
    rw [Matrix.diagonal_mul_diagonal]
    have he (r : ι) : α r * (h' r : ℂ) = 1 := by
      rw [show (h' r : ℂ) = (α r)⁻¹ from Complex.ofReal_inv _]
      exact mul_inv_cancel₀ (hα r)
    simpa only [he, Matrix.diagonal_one]
  have hPi (V : Matrix ι ι ℂ) (hV : IsUnitary V) :
      (P V)⁻¹ = V * diagonal b' * Vᴴ :=
    conjugated_diagonal_inv V hV β hβ
  have hshift (V : Matrix ι ι ℂ) (hV : IsUnitary V) :
      A + P V = H + V * diagonal b * Vᴴ := by
    have hl : A = H - (p : ℂ) • (1 : Matrix ι ι ℂ) := by
      ext r s : 1
      by_cases hrs : r = s <;> simp [A, α, H, Matrix.one_apply, hrs]
    have hdb : diagonal β = diagonal b + (p : ℂ) • (1 : Matrix ι ι ℂ) := by
      ext r s : 1
      by_cases hrs : r = s <;> simp [β, Matrix.one_apply, hrs]
    simp only [hl, P, hdb, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, hV.1]
    abel
  have hscale (V : Matrix ι ι ℂ) (hV : IsUnitary V) :
      θ' * determinantValue (fun r => (h' r : ℂ)) b' V =
        θ * determinantValue (fun r => (h r : ℂ)) b V := by
    have hf := reciprocal_sum_factor A (P V) hA (hP V hV)
    rw [hAi, hPi V hV, hshift V hV] at hf
    have he := congrArg Matrix.det hf
    rw [Matrix.det_mul, Matrix.det_mul, hPdet V hV] at he
    change (θ * Δ) * (H' + V * diagonal b' * Vᴴ).det =
      θ * (H + V * diagonal b * Vᴴ).det
    rw [← he]
    dsimp only [Δ]
    ring
  let R := U * diagonal (fun r => ((b' r).re : ℂ)) * Uᴴ
  let W := U * diagonal (fun r => ((b' r).im : ℂ)) * Uᴴ
  have hR : R.IsHermitian := Matrix.isHermitian_mul_mul_conjTranspose U (real_diagonal_isHermitian _)
  have hW : W.IsHermitian := Matrix.isHermitian_mul_mul_conjTranspose U (real_diagonal_isHermitian _)
  have hRW : Commute R W := by
    change R * W = W * R
    simp only [R, W, conjugated_diagonal_mul U hU]
    exact congrArg (fun d : ι → ℂ => U * diagonal d * Uᴴ) (funext fun r => mul_comm _ _)
  have hWu : IsUnit W.det := by
    dsimp only [W]
    rw [det_unitary_conjugation U _ hU, Matrix.det_diagonal]
    exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun r _ => Complex.ofReal_ne_zero.mpr (hb' r))
  have hB' : R + Complex.I • W = U * diagonal b' * Uᴴ := by
    have hd : diagonal b' =
        diagonal (fun r => ((b' r).re : ℂ)) + Complex.I • diagonal (fun r => ((b' r).im : ℂ)) := by
      rw [← Matrix.diagonal_smul, Matrix.diagonal_add]
      apply congrArg diagonal
      funext r
      change b' r = ((b' r).re : ℂ) + Complex.I * ((b' r).im : ℂ)
      rw [mul_comm Complex.I, Complex.re_add_im]
    simp only [R, W, hd, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  let M' := H' + (R + Complex.I • W)
  have hη : θ' * M'.det = η := by
    simpa only [M', hB', determinantValue, H', H, M, B, η] using hscale U hU
  have hhm : M.det ≠ 0 := fun he => by simp [η, he] at ha
  have hM : IsUnit (A + P U).det := by
    rw [hshift U hU]
    exact isUnit_iff_ne_zero.mpr hhm
  have hN : M'⁻¹ = A - A * M⁻¹ * A := by
    have he := reciprocal_sum_inverse A (P U) hA (hP U hU) hM
    rw [hAi, hPi U hU, hshift U hU] at he
    simpa only [M', hB', M, B] using he
  have hhh : Function.Injective h' := by
    intro r s he
    apply hh
    have he' : h r - p = h s - p := inv_injective he
    linarith only [he']
  have hmax' (V : Matrix ι ι ℂ) (hV : IsUnitary V) :
      (θ' * (V * H' * Vᴴ + (R + Complex.I • W)).det).re ≤ (θ' * M'.det).re := by
    have hv := relative_unitary V U hV hU
    rw [hB', determinantValue_relative _ _ V U hV, hscale (Vᴴ * U) hv, hη]
    exact hmax (Vᴴ * U) hv
  have hz (r : ι) (hr : (h r - p) * x r = η.re) : ((θ' * M'.det) * M'⁻¹ r r).re = 0 := by
    rw [hη, hN]
    have he : (A - A * M⁻¹ * A) r r = α r - α r * M⁻¹ r r * α r := by
      simp only [A, Matrix.sub_apply, Matrix.diagonal_apply_eq, Matrix.mul_diagonal, Matrix.diagonal_mul]
    rw [he]
    have he' : η * (α r - α r * M⁻¹ r r * α r) = α r * (η - α r * (η * M⁻¹ r r)) := by ring
    rw [he']
    simp only [α, Complex.re_ofReal_mul, Complex.sub_re]
    change (h r - p) * (η.re - (h r - p) * x r) = 0
    rw [hr, sub_self, mul_zero]
  exact hermitian_orbit_no_three_zero_inverse_diagonal h' R W θ' hhh hR hW hRW hWu
    hij hjk hik (by rwa [hη]) hmax' (hz i hi) (hz j hj) (hz k hk)

/-- The regular finite poles (h_i-(\Re\eta)/x_i) cannot coincide on three
distinct labels. -/
theorem hermitian_orbit_no_three_regular_stationary_poles
    (h : ι → ℝ) (b : ι → ℂ) (U : Matrix ι ι ℂ) (θ : ℂ)
    (hU : IsUnitary U) (hh : Function.Injective h) (hb : ∀ k, (b k).im ≠ 0)
    (hmax : ∀ V : Matrix ι ι ℂ, IsUnitary V →
      (θ * determinantValue (fun k => (h k : ℂ)) b V).re ≤
        (θ * determinantValue (fun k => (h k : ℂ)) b U).re)
    (p : ℝ) (hp : ∀ k, h k ≠ p) {i j k : ι}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    let M := (diagonal fun r => (h r : ℂ)) + U * diagonal b * Uᴴ
    let η := θ * M.det
    let x (r : ι) := (η * M⁻¹ r r).re
    0 < η.re →
    h i - η.re / x i = p → h j - η.re / x j = p → h k - η.re / x k = p → False := by
  intro M η x ha hi hj hk
  have he (r : ι) (hr : h r - η.re / x r = p) : (h r - p) * x r = η.re := by
    have hn : x r ≠ 0 := fun hx => hp r (by simpa only [hx, div_zero, sub_zero] using hr)
    have hf : h r - p = η.re / x r := by linarith only [hr]
    exact (eq_div_iff hn).mp hf
  exact hermitian_orbit_no_three_regular_pole_equations h b U θ hU hh hb hmax p hp hij hjk hik
    ha (he i hi) (he j hj) (he k hk)

end

end MOC
