import MOC.Householder

/-! The determinant on a unitary rank-one phase orbit has two scalar
coefficients obtained from a two-by-two compression. -/

open BigOperators Matrix

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem det_two_rankOne_updates (T : Matrix ι ι ℂ)
    (hT : IsUnit T.det) (L₀ L₁ : Matrix ι Unit ℂ) (R₀ R₁ : Matrix Unit ι ℂ) (w : ℂ) :
    (T + w • (L₀ * R₀ + L₁ * R₁)).det = T.det *
      ((1 + w * (R₀ * T⁻¹ * L₀) () ()) * (1 + w * (R₁ * T⁻¹ * L₁) () ()) -
        w ^ 2 * ((R₀ * T⁻¹ * L₁) () () * (R₁ * T⁻¹ * L₀) () ())) := by
  let L : Matrix ι (Fin 2) ℂ := fun i j => if j = 0 then L₀ i () else L₁ i ()
  let R : Matrix (Fin 2) ι ℂ := fun i j => if i = 0 then R₀ () j else R₁ () j
  have hLR : L * R = L₀ * R₀ + L₁ * R₁ := by
    ext i j : 1
    simp [L, R, Matrix.mul_apply, Fin.sum_univ_two]
  have hRL₀₀ : (R * T⁻¹ * L) 0 0 = (R₀ * T⁻¹ * L₀) () () := by
    simp only [Matrix.mul_apply, L, R, if_true]
  have hRL₀₁ : (R * T⁻¹ * L) 0 1 = (R₀ * T⁻¹ * L₁) () () := by
    simp only [Matrix.mul_apply, L, R, if_true, if_neg (by decide : (1 : Fin 2) ≠ 0)]
  have hRL₁₀ : (R * T⁻¹ * L) 1 0 = (R₁ * T⁻¹ * L₀) () () := by
    simp only [Matrix.mul_apply, L, R, if_true, if_neg (by decide : (1 : Fin 2) ≠ 0)]
  have hRL₁₁ : (R * T⁻¹ * L) 1 1 = (R₁ * T⁻¹ * L₁) () () := by
    simp only [Matrix.mul_apply, L, R, if_neg (by decide : (1 : Fin 2) ≠ 0)]
  rw [← hLR, ← Matrix.smul_mul, Matrix.det_add_mul (w • L) R hT, Matrix.mul_smul]
  simp only [Matrix.det_fin_two, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
    Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), hRL₀₀, hRL₀₁, hRL₁₀, hRL₁₁,
    zero_add]
  ring

/-- Conjugating the first summand by a unitary rank-one phase produces the
exact two-coefficient Laurent determinant formula. -/
theorem det_rankOnePhase_left_conjugation (A B : Matrix ι ι ℂ) (u : ι → ℂ)
    (hu : ∑ i, star (u i) * u i = 1) (z : ℂ) (hz : z * star z = 1) :
    let T := A - B
    let V := rankOnePhase u z
    let L : Matrix ι Unit ℂ := fun i _ => u i
    let α := (Lᴴ * A * T⁻¹ * L) () ()
    let β := (Lᴴ * T⁻¹ * (-(B * L))) () ()
    let γ := (Lᴴ * A * T⁻¹ * (-(B * L))) () ()
    let ε := (Lᴴ * T⁻¹ * L) () ()
    IsUnit T.det → (V * A * Vᴴ - B).det = T.det *
      (1 + (1 - star z) * (α + β - 1) + (z + star z - 2) * (α * β - γ * ε)) := by
  dsimp only
  intro hT
  let T := A - B
  let V := rankOnePhase u z
  let L : Matrix ι Unit ℂ := fun i _ => u i
  let α := (Lᴴ * A * T⁻¹ * L) () ()
  let β := (Lᴴ * T⁻¹ * (-(B * L))) () ()
  let γ := (Lᴴ * A * T⁻¹ * (-(B * L))) () ()
  let ε := (Lᴴ * T⁻¹ * L) () ()
  change IsUnit T.det at hT
  change (V * A * Vᴴ - B).det = T.det *
    (1 + (1 - star z) * (α + β - 1) + (z + star z - 2) * (α * β - γ * ε))
  have hP : L * Lᴴ = vecMulVec u (star ∘ u) := by
    ext i j : 1
    simp [L, Matrix.mul_apply, Matrix.vecMulVec_apply]
  have hV : IsUnitary V := rankOnePhase_unitary u z hu hz
  have hVP : V = 1 + (z - 1) • (L * Lᴴ) := by simp only [V, rankOnePhase, hP]
  have hmat : (V * A * Vᴴ - B) * V =
      T + (z - 1) • (L * (Lᴴ * A) + (-(B * L)) * Lᴴ) := by
    rw [Matrix.sub_mul, Matrix.mul_assoc (V * A) Vᴴ V, hV.2, Matrix.mul_one, hVP]
    simp only [T, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.neg_mul, smul_add, smul_neg, Matrix.mul_assoc]
    abel
  have hdet : (V * A * Vᴴ - B).det * z = T.det *
      ((1 + (z - 1) * α) * (1 + (z - 1) * β) - (z - 1)^2 * (γ * ε)) := by
    calc
      _ = (V * A * Vᴴ - B).det * V.det := by rw [show V.det = z from det_rankOnePhase u z hu]
      _ = _ := by
        rw [← Matrix.det_mul, hmat, det_two_rankOne_updates T hT L (-(B * L)) (Lᴴ * A) Lᴴ (z - 1)]
  have hzn : z ≠ 0 := fun h => by simpa only [h, zero_mul, zero_ne_one] using hz
  apply mul_right_cancel₀ hzn
  rw [hdet]
  linear_combination T.det * ((α + β - 1) - (α * β - γ * ε)) * hz

/-- Moving a unitary conjugation from the first summand to the second
preserves the determinant of the difference. -/
theorem det_sub_unitary_conjugation_left (A B V : Matrix ι ι ℂ) (hV : IsUnitary V) :
    (V * A * Vᴴ - B).det = (A - Vᴴ * B * V).det := by
  have hV' : IsUnitary Vᴴ := by
    simpa only [IsUnitary, Matrix.conjTranspose_conjTranspose] using And.intro hV.2 hV.1
  calc
    _ = (Vᴴ * (V * A * Vᴴ - B) * V).det := by
      simpa only [Matrix.conjTranspose_conjTranspose] using
        (det_unitary_conjugation Vᴴ (V * A * Vᴴ - B) hV').symm
    _ = _ := by
      have hA : Vᴴ * (V * A * Vᴴ) * V = A := by
        simp only [← Matrix.mul_assoc, hV.2, Matrix.one_mul]
        rw [Matrix.mul_assoc A Vᴴ V, hV.2, Matrix.mul_one]
      simp only [Matrix.mul_sub, Matrix.sub_mul, hA]

end

end MOC
