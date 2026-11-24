import MOC.OrderFourSecondVariation

/-! Directions commuting with one summand lie in the radical of the
determinant support Hessian at a unitary maximum. -/

open Matrix

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private def velocity (B K : Matrix ι ι ℂ) := K * B - B * K

/-- The real determinant-support quadratic in an orbit generator. -/
def determinantOrbitQuadratic (A B : Matrix ι ι ℂ) (η : ℂ)
    (K : Matrix ι ι ℂ) : ℝ :=
  let C := A + B
  let L := velocity B K
  let D := C⁻¹ * L
  (η * C.det * ((C⁻¹ * (K * L - L * K)).trace + D.trace ^ 2 - (D * D).trace)).re

theorem determinantOrbitQuadratic_nonpos
    (A B : Matrix ι ι ℂ) (η : ℂ) (hdet : (A + B).det ≠ 0)
    (hmax : ∀ V : Matrix ι ι ℂ, IsUnitary V →
      (η * (A + V * B * Vᴴ).det).re ≤ (η * (A + B).det).re)
    (K : Matrix ι ι ℂ) (hK : Kᴴ = -K) :
    determinantOrbitQuadratic A B η K ≤ 0 :=
  determinant_orbit_hessian_nonpos A B η hdet hmax K hK

theorem determinantOrbitQuadratic_zero_of_commute_right
    (A B : Matrix ι ι ℂ) (η : ℂ) {K : Matrix ι ι ℂ} (hK : K * B = B * K) :
    determinantOrbitQuadratic A B η K = 0 := by
  simp [determinantOrbitQuadratic, velocity, hK]

/-- The quadratic is exactly zero for a generator commuting with the
fixed summand. Writing (E=C^{-1}KC), the two trace terms reduce to the
trace of ((E-K)^2). -/
theorem determinantOrbitQuadratic_zero_of_commute_left
    (A B : Matrix ι ι ℂ) (η : ℂ) (hdet : (A + B).det ≠ 0)
    {K : Matrix ι ι ℂ} (hK : K * A = A * K) :
    determinantOrbitQuadratic A B η K = 0 := by
  let C := A + B
  let F := C⁻¹
  let E := F * K * C
  have hC : IsUnit C.det := isUnit_iff_ne_zero.mpr hdet
  have hFC : F * C = 1 := C.nonsing_inv_mul hC
  have hCF : C * F = 1 := C.mul_nonsing_inv hC
  have hV : velocity B K = K * C - C * K := by
    simp only [velocity, C, Matrix.mul_add, Matrix.add_mul, hK]
    abel
  have hD : F * (K * C - C * K) = E - K := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc F C K, hFC, Matrix.one_mul]
    simp only [E, Matrix.mul_assoc]
  have hE : E * E = F * K * K * C := by
    simp only [E, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc C F (K * C), hCF, Matrix.one_mul]
  have htE : E.trace = K.trace := by
    change (F * K * C).trace = K.trace
    rw [Matrix.trace_mul_cycle, hCF, Matrix.one_mul]
  have hJ : F * (K * (K * C - C * K) - (K * C - C * K) * K) =
      E * E - E * K - E * K + K * K := by
    rw [hE]
    simp only [Matrix.mul_sub, Matrix.sub_mul, E, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc F C (K * K), hFC, Matrix.one_mul]
    abel
  unfold determinantOrbitQuadratic
  change ((η * C.det) * ((F * (K * velocity B K - velocity B K * K)).trace +
    (F * velocity B K).trace ^ 2 - ((F * velocity B K) * (F * velocity B K)).trace)).re = 0
  rw [hV, hJ, hD]
  simp only [Matrix.trace_sub, Matrix.trace_add, htE, sub_self, zero_pow (Nat.succ_ne_zero 1),
    add_zero, Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_mul_comm K E]
  have hz : (E * E).trace - (E * K).trace - (E * K).trace + (K * K).trace -
      ((E * E).trace - (E * K).trace - ((E * K).trace - (K * K).trace)) = 0 := by ring
  rw [hz]
  simp

private theorem determinantOrbitQuadratic_line
    (A B : Matrix ι ι ℂ) (η : ℂ) (K T : Matrix ι ι ℂ) :
    ∃ b : ℝ, ∀ r : ℝ,
      determinantOrbitQuadratic A B η (K + r • T) =
        determinantOrbitQuadratic A B η K + r * b + r ^ 2 * determinantOrbitQuadratic A B η T := by
  let C := A + B
  let F := C⁻¹
  let L := velocity B K
  let M := velocity B T
  let D := F * L
  let E := F * M
  let J := K * M + T * L - L * T - M * K
  refine ⟨(η * C.det * ((F * J).trace + 2 * D.trace * E.trace -
    ((D * E).trace + (E * D).trace))).re, fun r => ?_⟩
  have hL : velocity B (K + r • T) = L + r • M := by
    simp [velocity, L, M, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_sub]
    abel
  have hD : F * (L + r • M) = D + r • E := by
    simp [D, E, Matrix.mul_add, Matrix.mul_smul]
  have hJ : (K + r • T) * (L + r • M) - (L + r • M) * (K + r • T) =
      (K * L - L * K) + r • J + r ^ 2 • (T * M - M * T) := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
      smul_smul, J, smul_add, smul_sub, pow_two]
    abel
  let q (X V : Matrix ι ι ℂ) := (F * (X * V - V * X)).trace +
    (F * V).trace ^ 2 - ((F * V) * (F * V)).trace
  let b := (F * J).trace + 2 * D.trace * E.trace - ((D * E).trace + (E * D).trace)
  let ω := η * C.det
  have hq : q (K + r • T) (L + r • M) =
      q K L + (r : ℂ) * b + (r : ℂ) ^ 2 * q T M := by
    dsimp only [q, b]
    rw [hD, hJ]
    simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul,
      Matrix.add_mul, Matrix.smul_mul, smul_smul, Complex.real_smul, Complex.ofReal_pow,
      Complex.ofReal_mul]
    change _ = (F * (K * L - L * K)).trace + D.trace ^ 2 - (D * D).trace +
      (r : ℂ) * _ + (r : ℂ) ^ 2 * ((F * (T * M - M * T)).trace + E.trace ^ 2 - (E * E).trace)
    ring
  change (ω * q (K + r • T) (velocity B (K + r • T))).re =
    (ω * q K L).re + r * (ω * b).re + r ^ 2 * (ω * q T M).re
  rw [hL, hq, mul_add, mul_add, Complex.add_re, Complex.add_re,
    mul_left_comm ω (r : ℂ), Complex.re_ofReal_mul, mul_left_comm ω ((r : ℂ) ^ 2),
    ← Complex.ofReal_pow, Complex.re_ofReal_mul]

private theorem determinantOrbitQuadratic_eq_of_null
    (A B : Matrix ι ι ℂ) (η : ℂ)
    (hQ : ∀ K : Matrix ι ι ℂ, Kᴴ = -K → determinantOrbitQuadratic A B η K ≤ 0)
    (K T : Matrix ι ι ℂ) (hK : Kᴴ = -K) (hT : Tᴴ = -T)
    (h0 : determinantOrbitQuadratic A B η T = 0) :
    determinantOrbitQuadratic A B η (K + T) = determinantOrbitQuadratic A B η K := by
  obtain ⟨b, hb⟩ := determinantOrbitQuadratic_line A B η K T
  have h (r : ℝ) : Kᴴ + (r • T)ᴴ = -(K + r • T) := by
    rw [Matrix.conjTranspose_smul, star_trivial, hK, hT, smul_neg, neg_add]
  have hn (r : ℝ) : determinantOrbitQuadratic A B η K + r * b ≤ 0 := by
    have H := hQ (K + r • T) (by rw [Matrix.conjTranspose_add]; exact h r)
    rwa [hb, h0, mul_zero, add_zero] at H
  have hB : b = 0 := by
    by_contra he
    have H := hn ((1 - determinantOrbitQuadratic A B η K) / b)
    rw [div_mul_cancel₀ _ he] at H
    linarith
  simpa [hB, h0] using hb 1

/-- At a support maximum, adding commuting directions from either summand
does not change the Hessian. This removes the two phase algebras from
the imaginary symmetric test for an orthogonal mixer. -/
theorem determinantOrbitQuadratic_add_commuting
    (A B : Matrix ι ι ℂ) (η : ℂ) (hdet : (A + B).det ≠ 0)
    (hmax : ∀ V : Matrix ι ι ℂ, IsUnitary V →
      (η * (A + V * B * Vᴴ).det).re ≤ (η * (A + B).det).re)
    (K T S : Matrix ι ι ℂ) (hK : Kᴴ = -K) (hT : Tᴴ = -T)
    (hS : Sᴴ = -S) (hTA : T * A = A * T) (hSB : S * B = B * S) :
    determinantOrbitQuadratic A B η (K + T + S) = determinantOrbitQuadratic A B η K := by
  have hQ := determinantOrbitQuadratic_nonpos A B η hdet hmax
  have hKT : (K + T)ᴴ = -(K + T) := by rw [Matrix.conjTranspose_add, hK, hT, neg_add]
  rw [determinantOrbitQuadratic_eq_of_null A B η hQ (K + T) S hKT hS
    (determinantOrbitQuadratic_zero_of_commute_right A B η hSB)]
  exact determinantOrbitQuadratic_eq_of_null A B η hQ K T hK hT
    (determinantOrbitQuadratic_zero_of_commute_left A B η hdet hTA)

/-- One dense row suffices to put a symmetric direction into a gauge
with that column and the entire diagonal zero. In order four the
remaining block has precisely three free off-diagonal entries. -/
theorem exists_symmetric_phase_gauge (O : Matrix.orthogonalGroup ι ℝ)
    (r : ι) (hr : ∀ j, O.val r j ≠ 0)
    (S : Matrix ι ι ℝ) (hS : Sᵀ = S) :
    ∃ (d e : ι → ℝ) (R : Matrix ι ι ℝ),
      Rᵀ = R ∧ (∀ i, R i i = 0) ∧ (∀ i, R i r = 0) ∧
      S = R + diagonal e + O.val * diagonal d * O.valᵀ := by
  let v : ι → ℝ := fun i => S i r
  let w : ι → ℝ := O.valᵀ *ᵥ v
  let d : ι → ℝ := fun j => w j / O.val r j
  let T := O.val * diagonal d * O.valᵀ
  let e : ι → ℝ := fun i => S i i - T i i
  let R := S - T - diagonal e
  have hO : O.val * O.valᵀ = 1 := (Matrix.mem_orthogonalGroup_iff ι ℝ).mp O.property
  let u : ι → ℝ := Pi.single r 1
  have hcol (M : Matrix ι ι ℝ) (i : ι) : (M *ᵥ u) i = M i r := by
    rw [show u = Pi.single r 1 from rfl, Matrix.mulVec_single]
    simp
  have hdiag : diagonal d *ᵥ (O.valᵀ *ᵥ u) = w := by
    ext j
    rw [Matrix.mulVec_diagonal, hcol]
    simp only [d, Matrix.transpose_apply, Pi.mul_apply]
    exact div_mul_cancel₀ _ (hr j)
  have hTv : T *ᵥ u = v := by
    rw [show T = O.val * diagonal d * O.valᵀ from rfl, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, hdiag, show w = O.valᵀ *ᵥ v from rfl,
      Matrix.mulVec_mulVec, hO, Matrix.one_mulVec]
  have hTc (i : ι) : T i r = S i r := by
    rw [← hcol T, hTv]
  have hT : Tᵀ = T := by
    simp [T, Matrix.transpose_mul, Matrix.mul_assoc]
  refine ⟨d, e, R, ?_, ?_, ?_, ?_⟩
  · simp [R, Matrix.transpose_sub, hS, hT]
  · intro i
    simp [R, e]
  · intro i
    by_cases h : i = r
    · subst i
      simp [R, e]
    · simp [R, hTc, Matrix.diagonal_apply_ne, h]
  · change S = S - T - diagonal e + diagonal e + T
    abel

/-- The support Hessian for imaginary symmetric directions at a real
orthogonal mixer can be tested using only zero-diagonal directions
supported off one dense row and its column. -/
theorem orthogonal_phase_hessian_has_reduced_test
    (a b : ι → ℂ) (η : ℂ) (O : Matrix.orthogonalGroup ι ℝ)
    (r : ι) (hr : ∀ j, O.val r j ≠ 0)
    (hdet : determinantValue a b (Complex.ofRealHom.mapMatrix O.val) ≠ 0)
    (hmax : ∀ W : Matrix ι ι ℂ, IsUnitary W →
      (η * determinantValue a b W).re ≤
        (η * determinantValue a b (Complex.ofRealHom.mapMatrix O.val)).re)
    (S : Matrix ι ι ℝ) (hS : Sᵀ = S) :
    let U := Complex.ofRealHom.mapMatrix O.val
    let B := U * diagonal b * Uᴴ
    let Q (X : Matrix ι ι ℝ) :=
      determinantOrbitQuadratic (diagonal a) B η (Complex.I • Complex.ofRealHom.mapMatrix X)
    ∃ R : Matrix ι ι ℝ, Rᵀ = R ∧ (∀ i, R i i = 0) ∧ (∀ i, R i r = 0) ∧ Q S = Q R := by
  intro U B Q
  obtain ⟨d, e, R, hR, hRdiag, hRcol, hsplit⟩ := exists_symmetric_phase_gauge O r hr S hS
  let A := diagonal a
  let T := O.val * diagonal d * O.valᵀ
  let L (X : Matrix ι ι ℝ) := Complex.I • Complex.ofRealHom.mapMatrix X
  have hU : IsUnitary U := isUnitary_ofReal_orthogonal O
  have hUT : Uᵀ = Uᴴ := by
    ext i j
    simp [U, Matrix.conjTranspose_apply, Complex.star_def]
  have hBmax (V : Matrix ι ι ℂ) (hV : IsUnitary V) :
      (η * (A + V * B * Vᴴ).det).re ≤ (η * (A + B).det).re := by
    have hV' : IsUnitary Vᴴ := by
      simpa only [IsUnitary, Matrix.conjTranspose_conjTranspose] using And.intro hV.2 hV.1
    have hVU : IsUnitary (V * U) := by
      simpa only [Matrix.conjTranspose_conjTranspose] using relative_unitary Vᴴ U hV' hU
    simpa only [determinantValue, A, B, Matrix.conjTranspose_mul, Matrix.mul_assoc] using
      hmax (V * U) hVU
  have hskew (X : Matrix ι ι ℝ) (hX : Xᵀ = X) : (L X)ᴴ = -L X := by
    ext i j
    have hx := congrArg (fun M : Matrix ι ι ℝ => M i j) hX
    change X j i = X i j at hx
    change star (Complex.I * (X j i : ℂ)) = -(Complex.I * (X i j : ℂ))
    simp [hx, Complex.star_def]
  have heSym : (diagonal e)ᵀ = diagonal e := Matrix.diagonal_transpose _
  have hTSym : Tᵀ = T := by simp [T, Matrix.transpose_mul, Matrix.mul_assoc]
  have hD (x : ι → ℝ) :
      Complex.ofRealHom.mapMatrix (diagonal x) = diagonal (fun i => (x i : ℂ)) := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.diagonal_apply, h]
  have hLeft : L (diagonal e) * A = A * L (diagonal e) := by
    simp only [L, A, hD, Matrix.smul_mul, Matrix.mul_smul, Matrix.diagonal_mul_diagonal, mul_comm]
  have hTc : Complex.ofRealHom.mapMatrix T = U * diagonal (fun i => (d i : ℂ)) * Uᴴ := by
    have hTrans : Complex.ofRealHom.mapMatrix O.valᵀ = Uᵀ := by ext i j; rfl
    rw [show T = O.val * diagonal d * O.valᵀ from rfl, map_mul, map_mul, hD, hTrans, hUT]
  have hRight : L T * B = B * L T := by
    simp only [L, B, hTc, Matrix.smul_mul, Matrix.mul_smul]
    congr 1
    let F := diagonal (fun i => (d i : ℂ))
    let G := diagonal b
    change (U * F * Uᴴ) * (U * G * Uᴴ) = (U * G * Uᴴ) * (U * F * Uᴴ)
    have hprod (X Y : Matrix ι ι ℂ) :
        (U * X * Uᴴ) * (U * Y * Uᴴ) = U * (X * Y) * Uᴴ := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Uᴴ U (Y * Uᴴ), hU.2, Matrix.one_mul]
    have hFG : F * G = G * F := by
      simp only [F, G, Matrix.diagonal_mul_diagonal]
      exact congrArg diagonal (funext (fun i => mul_comm (d i : ℂ) (b i)))
    rw [hprod, hprod, hFG]
  refine ⟨R, hR, hRdiag, hRcol, ?_⟩
  have hLsplit : L S = L R + L (diagonal e) + L T := by
    change S = R + diagonal e + T at hsplit
    simp only [L, hsplit, map_add, smul_add]
  change determinantOrbitQuadratic A B η (L S) = determinantOrbitQuadratic A B η (L R)
  rw [hLsplit]
  exact determinantOrbitQuadratic_add_commuting A B η hdet hBmax (L R) (L (diagonal e)) (L T)
    (hskew R hR) (hskew _ heSym) (hskew T hTSym) hLeft hRight

end

end MOC
