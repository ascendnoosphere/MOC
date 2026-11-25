import MOC.PairRayleigh
import MOC.Variational
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Exact three-coordinate support reduction

Fix the spectator block and eliminate it by a Schur complement
(R. W. Cottle, DOI: 10.1016/0024-3795(74)90066-4). The remaining
three-coordinate objective consists of one expectation for each slot of an
orthonormal frame, with no minor terms of higher degree. Background on
determinantal support stationarity: Mulero-Martínez,
DOI: 10.1016/j.laa.2026.03.019. The tied-swap comparison is proved directly. For support
stationarity in the MOC context, see Mulero-Martínez,
DOI: 10.1016/j.laa.2026.03.019. The cross-cofactor comparison below
uses the checked stationarity theorem and does not assume normality
of the three-coordinate Schur complement.
-/

open BigOperators Matrix

namespace MOC

noncomputable section

/-- The mixed coefficients of the three-by-three determinant are the two
adjugate trace pairings, without any invertibility assumption. -/
theorem det_add_fin_three_mixed (A B : Matrix (Fin 3) (Fin 3) ℂ) :
    (A + B).det = A.det + B.det +
      (A * B.adjugate).trace + (A.adjugate * B).trace := by
  simp only [Matrix.det_fin_three, Matrix.trace, Matrix.diag_apply, Fin.sum_univ_three,
    Matrix.mul_apply, Matrix.adjugate_fin_three, Matrix.add_apply]
  simp [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  ring

private theorem adjugate_unitary_conjugate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V H : Matrix ι ι ℂ) (hV : IsUnitary V) :
    (V * H * Vᴴ).adjugate = V * H.adjugate * Vᴴ := by
  have hVs : IsUnitary Vᴴ := ⟨by simpa using hV.2, by simpa using hV.1⟩
  have hd : V.det * Vᴴ.det = 1 := by rw [← Matrix.det_mul, hV.1, Matrix.det_one]
  simp only [Matrix.adjugate_mul_distrib, adjugate_unitary Vᴴ hVs, adjugate_unitary V hV,
    Matrix.conjTranspose_conjTranspose, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
  rw [smul_smul, hd, one_smul]

private theorem trace_unitary_conjugated_diag (V C : Matrix (Fin 3) (Fin 3) ℂ) (d : Fin 3 → ℂ) :
    (V * diagonal d * Vᴴ * C).trace = ∑ j, d j * (Vᴴ * C * V) j j := by
  calc
    _ = (V * (diagonal d * (Vᴴ * C))).trace := by simp only [Matrix.mul_assoc]
    _ = ((diagonal d * (Vᴴ * C)) * V).trace := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc, Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul]

/-- The three-slot unitary orbit has a determinant formula depending linearly
on the rank-one projectors onto its columns. The partner matrix need not
be normal. -/
theorem det_fin_three_unitary_slot_expansion (a : Fin 3 → ℂ)
    (C V : Matrix (Fin 3) (Fin 3) ℂ) (hV : IsUnitary V) :
    (V * diagonal a * Vᴴ + C).det = (diagonal a).det + C.det +
      ∑ j, (Vᴴ * (a j • C.adjugate +
        (∏ k ∈ Finset.univ.erase j, a k) • C) * V) j j := by
  rw [det_add_fin_three_mixed, det_unitary_conjugation V _ hV,
    adjugate_unitary_conjugate _ _ hV, Matrix.adjugate_diagonal]
  rw [trace_unitary_conjugated_diag, trace_unitary_conjugated_diag, add_assoc]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_add_distrib]


/-- An arbitrary number of inactive coordinates contributes only the
spectator determinant and a fixed Schur complement to the exact three-slot
support objective. No spectral assumption on the Schur complement is made. -/
theorem det_unitary_three_slot_schur_expansion
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (a : Fin 3 → ℂ) (A : Matrix (Fin 3) (Fin 3) ℂ)
    (B : Matrix (Fin 3) κ ℂ) (C : Matrix κ (Fin 3) ℂ)
    (D : Matrix κ κ ℂ) [Invertible D]
    (V : Matrix (Fin 3) (Fin 3) ℂ) (hV : IsUnitary V) :
    let E := A - B * ⅟ D * C
    (Matrix.fromBlocks (V * diagonal a * Vᴴ + A) B C D).det =
      D.det * ((diagonal a).det + E.det +
        ∑ j, (Vᴴ * (a j • E.adjugate +
          (∏ k ∈ Finset.univ.erase j, a k) • E) * V) j j) := by
  intro E
  rw [Matrix.det_fromBlocks₂₂, add_sub_assoc]
  exact congrArg (D.det * ·) (det_fin_three_unitary_slot_expansion a E V hV)

/-- If one summand has real diagonal, stationarity annihilates the
Hermitian part of the determinant-scaled inverse across distinct labels.
This form uses cofactors so the equations are easy to compare at a swap. -/
theorem adjugate_cross_of_real_diagonal_support_max
    {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ℝ)
    (C : Matrix ι ι ℂ) (η : ℂ) {i j : ι} (hij : a i ≠ a j)
    (hdet : (C + diagonal (fun k => (a k : ℂ))).det ≠ 0)
    (hmax : ∀ V : Matrix ι ι ℂ, IsUnitary V →
      (η * (C + V * diagonal (fun k => (a k : ℂ)) * Vᴴ).det).re ≤
        (η * (C + diagonal (fun k => (a k : ℂ))).det).re) :
    let M := C + diagonal (fun k => (a k : ℂ))
    η * M.adjugate i j + star (η * M.adjugate j i) = 0 := by
  let A : Matrix ι ι ℂ := diagonal (fun k => (a k : ℂ))
  let M := C + A
  intro M'
  have hD := support_maximum_inverse_commutator C A η hdet hmax
  change ((η * M.det) • (A * M⁻¹ - M⁻¹ * A))ᴴ =
    (η * M.det) • (A * M⁻¹ - M⁻¹ * A) at hD
  have hscale : (η * M.det) • (A * M⁻¹ - M⁻¹ * A) =
      η • (A * M.adjugate - M.adjugate * A) := by
    have hd : M.det ≠ 0 := hdet
    rw [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.mul_smul, Matrix.smul_mul,
      ← smul_sub, smul_smul, mul_assoc, mul_inv_cancel₀ hd, mul_one]
  rw [hscale] at hD
  have h := congrArg (fun X : Matrix ι ι ℂ => X i j) hD
  simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.sub_apply, A, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Complex.star_def, map_mul, map_sub, Complex.conj_ofReal] at h
  change η * M.adjugate i j + star (η * M.adjugate j i) = 0
  have hdiff : (a i : ℂ) - (a j : ℂ) ≠ 0 :=
    sub_ne_zero.mpr (fun he => hij (Complex.ofReal_injective he))
  apply mul_left_cancel₀ hdiff
  rw [mul_zero]
  simp only [Complex.star_def, map_mul]
  linear_combination -h

/-- A tied swap propagates stationarity across the other coordinate:
for distinct real labels, the Hermitian off-block entries of both the
partner and its adjugate vanish. The hypotheses are the two equal-height
stationary representatives written in their respective diagonal bases. -/
theorem triple_tied_swap_cross_cofactors
    (a : Fin 3 → ℝ) (C : Matrix (Fin 3) (Fin 3) ℂ) (η : ℂ)
    (h01 : a 0 ≠ a 1) (h02 : a 0 ≠ a 2) (h12 : a 1 ≠ a 2)
    (hdet : (C + diagonal (fun k => (a k : ℂ))).det ≠ 0)
    (hdet' : (C + diagonal (fun k => (a (Equiv.swap 0 1 k) : ℂ))).det ≠ 0)
    (hmax : ∀ V : Matrix (Fin 3) (Fin 3) ℂ, IsUnitary V →
      (η * (C + V * diagonal (fun k => (a k : ℂ)) * Vᴴ).det).re ≤
        (η * (C + diagonal (fun k => (a k : ℂ))).det).re)
    (hmax' : ∀ V : Matrix (Fin 3) (Fin 3) ℂ, IsUnitary V →
      (η * (C + V * diagonal (fun k => (a (Equiv.swap 0 1 k) : ℂ)) * Vᴴ).det).re ≤
        (η * (C + diagonal (fun k => (a (Equiv.swap 0 1 k) : ℂ))).det).re) :
    ∀ p : Fin 2, let q := p.castSucc
      η * C q 2 + star (η * C 2 q) = 0 ∧
      η * C.adjugate q 2 + star (η * C.adjugate 2 q) = 0 := by
  intro p q
  have hsw₂ : Equiv.swap (0 : Fin 3) 1 2 = 2 :=
    Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
  have h02' : a (Equiv.swap (0 : Fin 3) 1 0) ≠ a (Equiv.swap 0 1 2) := by
    rwa [Equiv.swap_apply_left, hsw₂]
  have h12' : a (Equiv.swap (0 : Fin 3) 1 1) ≠ a (Equiv.swap 0 1 2) := by
    rwa [Equiv.swap_apply_right, hsw₂]
  have hs0 := adjugate_cross_of_real_diagonal_support_max a C η h02 hdet hmax
  have hs1 := adjugate_cross_of_real_diagonal_support_max a C η h12 hdet hmax
  have ht0 := adjugate_cross_of_real_diagonal_support_max (a ∘ Equiv.swap 0 1) C η h02' hdet' hmax'
  have ht1 := adjugate_cross_of_real_diagonal_support_max (a ∘ Equiv.swap 0 1) C η h12' hdet' hmax'
  have exp0 (u : Fin 3 → ℝ) :
      (C + diagonal (fun k => (u k : ℂ))).adjugate 0 2 =
        C.adjugate 0 2 - (u 1 : ℂ) * C 0 2 := by
    simp [Matrix.adjugate_fin_three, Matrix.add_apply, Matrix.diagonal_apply]
    ring
  have exp1 (u : Fin 3 → ℝ) :
      (C + diagonal (fun k => (u k : ℂ))).adjugate 1 2 =
        C.adjugate 1 2 - (u 0 : ℂ) * C 1 2 := by
    simp [Matrix.adjugate_fin_three, Matrix.add_apply, Matrix.diagonal_apply]
    ring
  have exp2 (u : Fin 3 → ℝ) :
      (C + diagonal (fun k => (u k : ℂ))).adjugate 2 0 =
        C.adjugate 2 0 - (u 1 : ℂ) * C 2 0 := by
    simp [Matrix.adjugate_fin_three, Matrix.add_apply, Matrix.diagonal_apply]
    ring
  have exp3 (u : Fin 3 → ℝ) :
      (C + diagonal (fun k => (u k : ℂ))).adjugate 2 1 =
        C.adjugate 2 1 - (u 0 : ℂ) * C 2 1 := by
    simp [Matrix.adjugate_fin_three, Matrix.add_apply, Matrix.diagonal_apply]
    ring
  dsimp only at hs0 hs1 ht0 ht1
  rw [exp0, exp2] at hs0 ht0
  rw [exp1, exp3] at hs1 ht1
  simp only [Function.comp_apply, Equiv.swap_apply_left, Equiv.swap_apply_right,
    Complex.star_def, map_mul, map_sub, Complex.conj_ofReal] at hs0 hs1 ht0 ht1
  have hdiff : (a 0 : ℂ) - (a 1 : ℂ) ≠ 0 :=
    sub_ne_zero.mpr (fun he => h01 (Complex.ofReal_injective he))
  have hmix0 : η * C 0 2 + star (η * C 2 0) = 0 := by
    apply mul_left_cancel₀ hdiff
    rw [mul_zero]
    simp only [Complex.star_def, map_mul]
    linear_combination hs0 - ht0
  have hmix1 : η * C 1 2 + star (η * C 2 1) = 0 := by
    apply mul_left_cancel₀ hdiff
    rw [mul_zero]
    simp only [Complex.star_def, map_mul]
    linear_combination ht1 - hs1
  have hAdj0 : η * C.adjugate 0 2 + star (η * C.adjugate 2 0) = 0 := by
    simp only [Complex.star_def, map_mul] at hmix0 ⊢
    linear_combination hs0 + (a 1 : ℂ) * hmix0
  have hAdj1 : η * C.adjugate 1 2 + star (η * C.adjugate 2 1) = 0 := by
    simp only [Complex.star_def, map_mul] at hmix1 ⊢
    linear_combination hs1 + (a 0 : ℂ) * hmix1
  fin_cases p
  · exact ⟨hmix0, hAdj0⟩
  · exact ⟨hmix1, hAdj1⟩

/-- If the internal pair's cofactor skew part is nonsingular, the two
cross-cofactor equations force complete reduction of the pair. -/
theorem triple_cross_zero_of_cofactor_skew_nonsingular
    (C : Matrix (Fin 3) (Fin 3) ℂ) (η : ℂ) (hη : η ≠ 0)
    (hcross : ∀ p : Fin 2, let q := p.castSucc
      η * C q 2 + star (η * C 2 q) = 0 ∧
      η * C.adjugate q 2 + star (η * C.adjugate 2 q) = 0)
    (hskew : let T := (C.submatrix Fin.castSucc Fin.castSucc).adjugate
      IsUnit (Tᴴ - T).det) :
    ∀ p : Fin 2, C p.castSucc 2 = 0 ∧ C 2 p.castSucc = 0 := by
  let T := (C.submatrix Fin.castSucc Fin.castSucc).adjugate
  let u : Fin 2 → ℂ := fun p => C p.castSucc 2
  have ht := hskew
  change IsUnit (Tᴴ - T).det at ht
  have hvec : (Tᴴ - T) *ᵥ u = 0 := by
    obtain ⟨hC0, hA0⟩ := hcross 0
    obtain ⟨hC1, hA1⟩ := hcross 1
    change η * C 0 2 + star (η * C 2 0) = 0 at hC0
    change η * C 1 2 + star (η * C 2 1) = 0 at hC1
    change η * C.adjugate 0 2 + star (η * C.adjugate 2 0) = 0 at hA0
    change η * C.adjugate 1 2 + star (η * C.adjugate 2 1) = 0 at hA1
    simp [Matrix.adjugate_fin_three, Complex.star_def] at hA0 hA1
    simp only [Complex.star_def, map_mul] at hC0 hC1
    funext p
    apply mul_left_cancel₀ hη
    simp only [Pi.zero_apply, mul_zero, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.sub_apply, Matrix.conjTranspose_apply]
    change η * ((star (T 0 p) - T p 0) * C 0 2 +
      (star (T 1 p) - T p 1) * C 1 2) = 0
    fin_cases p
    · simp [-mul_eq_zero, T, Matrix.adjugate_fin_two, Matrix.submatrix_apply, Complex.star_def]
      linear_combination hA0 + (starRingEnd ℂ) (C 1 1) * hC0 -
        (starRingEnd ℂ) (C 1 0) * hC1
    · simp [-mul_eq_zero, T, Matrix.adjugate_fin_two, Matrix.submatrix_apply, Complex.star_def]
      linear_combination hA1 - (starRingEnd ℂ) (C 0 1) * hC0 +
        (starRingEnd ℂ) (C 0 0) * hC1
  have hu : u = 0 := by
    have h := congrArg (fun v => (Tᴴ - T)⁻¹ *ᵥ v) hvec
    simpa only [Matrix.mulVec_mulVec, (Tᴴ - T).nonsing_inv_mul ht,
      Matrix.one_mulVec, Matrix.mulVec_zero] using h
  intro p
  have hz : C p.castSucc 2 = 0 := congrFun hu p
  refine ⟨hz, ?_⟩
  have hv := (hcross p).1
  change η * C p.castSucc 2 + star (η * C 2 p.castSucc) = 0 at hv
  rw [hz, mul_zero, zero_add, star_eq_zero] at hv
  exact (mul_eq_zero.mp hv).resolve_left hη

/-- Eliminate the reverse coupling from two flat-pair equations. The result
is a skew-Hermitian quadratic matrix test. Neither linear pencil must be
invertible. The nonzero support phase can be absorbed into the two vectors. -/
theorem flat_pair_cross_kernel {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : Matrix ι ι ℂ) (a b d e : ℂ) (u v : ι → ℂ)
    (h₁ : let Y := T + b • (1 : Matrix ι ι ℂ)
      (d • Y) *ᵥ u + (star d • Yᴴ) *ᵥ v = 0)
    (h₂ : let X := T + a • (1 : Matrix ι ι ℂ)
      (e • X) *ᵥ u + (star e • Xᴴ) *ᵥ v = 0) :
    let X := T + a • (1 : Matrix ι ι ℂ)
    let Y := T + b • (1 : Matrix ι ι ℂ)
    let c := star d * e
    (c • (Yᴴ * X) - star c • (Xᴴ * Y)) *ᵥ u = 0 := by
  intro X Y c
  change (d • Y) *ᵥ u + (star d • Yᴴ) *ᵥ v = 0 at h₁
  change (e • X) *ᵥ u + (star e • Xᴴ) *ᵥ v = 0 at h₂
  have ha : Xᴴ * Yᴴ = Yᴴ * Xᴴ := by
    simp only [X, Y, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_one, Matrix.mul_add, Matrix.add_mul, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_add, smul_smul, mul_comm (star a) (star b)]
    abel
  have s₁ := congrArg (fun k => (star e • Xᴴ) *ᵥ k) h₁
  have s₂ := congrArg (fun k => (star d • Yᴴ) *ᵥ k) h₂
  simp only [Matrix.mulVec_add, Matrix.mulVec_zero, Matrix.mulVec_mulVec,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, ha, mul_comm (star e) (star d)] at s₁ s₂
  have he := add_right_cancel (s₂.trans s₁.symm)
  rw [Matrix.sub_mulVec]
  apply sub_eq_zero.mpr
  simpa only [c, StarMul.star_mul, star_star, mul_comm (star d) e, mul_comm (star e) d] using he

/-- A nonsingular quadratic test rules out both couplings. This is the
linear algebra step for the generalized spectral-circle obstruction. -/
theorem flat_pair_cross_zero_of_circle_test {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : Matrix ι ι ℂ) {a b d e : ℂ} (hab : a ≠ b) (hd : d ≠ 0) (he : e ≠ 0)
    (u v : ι → ℂ)
    (h₁ : let Y := T + b • (1 : Matrix ι ι ℂ)
      (d • Y) *ᵥ u + (star d • Yᴴ) *ᵥ v = 0)
    (h₂ : let X := T + a • (1 : Matrix ι ι ℂ)
      (e • X) *ᵥ u + (star e • Xᴴ) *ᵥ v = 0)
    (hq : let X := T + a • (1 : Matrix ι ι ℂ)
      let Y := T + b • (1 : Matrix ι ι ℂ)
      let c := star d * e
      IsUnit (c • (Yᴴ * X) - star c • (Xᴴ * Y)).det) :
    u = 0 ∧ v = 0 := by
  let X := T + a • (1 : Matrix ι ι ℂ)
  let Y := T + b • (1 : Matrix ι ι ℂ)
  let c := star d * e
  let Q := c • (Yᴴ * X) - star c • (Xᴴ * Y)
  have hQu : Q *ᵥ u = 0 := flat_pair_cross_kernel T a b d e u v h₁ h₂
  have hqu := congrArg (fun k => Q⁻¹ *ᵥ k) hQu
  have hu : u = 0 := by
    simpa only [Matrix.mulVec_mulVec, Q.nonsing_inv_mul hq,
      Matrix.one_mulVec, Matrix.mulVec_zero] using hqu
  refine ⟨hu, ?_⟩
  change (d • Y) *ᵥ u + (star d • Yᴴ) *ᵥ v = 0 at h₁
  change (e • X) *ᵥ u + (star e • Xᴴ) *ᵥ v = 0 at h₂
  simp only [hu, Matrix.mulVec_zero, zero_add, Matrix.smul_mulVec_assoc] at h₁ h₂
  have hv₁ := (smul_eq_zero.mp h₁).resolve_left (star_ne_zero.mpr hd)
  have hv₂ := (smul_eq_zero.mp h₂).resolve_left (star_ne_zero.mpr he)
  have hZ : Xᴴ - Yᴴ = (star a - star b) • (1 : Matrix ι ι ℂ) := by
    simp only [X, Y, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_one, sub_smul]
    abel
  have hv : (Xᴴ - Yᴴ) *ᵥ v = 0 := by
    simp only [Matrix.sub_mulVec, hv₁, hv₂, sub_zero]
  rw [hZ, Matrix.smul_mulVec_assoc, Matrix.one_mulVec] at hv
  exact (smul_eq_zero.mp hv).resolve_left (sub_ne_zero.mpr (fun h => hab (star_injective h)))

end

end MOC
