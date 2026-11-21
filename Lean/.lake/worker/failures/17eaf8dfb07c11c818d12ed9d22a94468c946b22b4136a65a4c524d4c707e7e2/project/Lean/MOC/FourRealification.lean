import MOC.Realification
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.FinCases

/-! Linear algebra for the fixed-row realification in dimension four. -/

open BigOperators Matrix

namespace MOC

noncomputable section

/-- Column phases make a prescribed row real and nonnegative while preserving
the squared modulus of every minor. -/
theorem exists_unitary_with_real_row {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) (r : ι) :
    ∃ V : Matrix ι ι ℂ, IsUnitary V ∧ (∀ j, V r j = (‖U r j‖ : ℂ)) ∧
      ∀ I J : Finset ι, subsetMinorSq V I J = subsetMinorSq U I J := by
  let p (j : ι) : ℂ := if U r j = 0 then 1 else star (U r j) / (‖U r j‖ : ℂ)
  let V := U * diagonal p
  have hp (j : ι) : Complex.normSq (p j) = 1 := by
    by_cases h : U r j = 0
    · simp [p, h]
    · rw [show p j = _ from if_neg h, Complex.normSq_div, Complex.star_def,
        Complex.normSq_conj, Complex.normSq_ofReal, ← pow_two, ← Complex.normSq_eq_norm_sq]
      exact div_self (Complex.normSq_pos.mpr h).ne'
  have hstar (j : ι) : p j * star (p j) = 1 := by
    rw [Complex.star_def, Complex.mul_conj, hp, Complex.ofReal_one]
  have hD : diagonal p * (diagonal p)ᴴ = 1 := by
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    exact congrArg Matrix.diagonal (funext hstar)
  refine ⟨V, ?_, ?_, ?_⟩
  · have hVV : V * Vᴴ = 1 := by
      dsimp only [V]
      rw [Matrix.conjTranspose_mul, Matrix.mul_assoc U, ← Matrix.mul_assoc (diagonal p), hD,
        Matrix.one_mul, hU.1]
    exact ⟨hVV, Matrix.mul_eq_one_comm.mp hVV⟩
  · intro j
    rw [show V r j = (U * diagonal p) r j from rfl, Matrix.mul_diagonal]
    by_cases h : U r j = 0
    · simp [h]
    · have hn : (‖U r j‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr h)
      rw [show p j = _ from if_neg h, mul_div_assoc, Complex.star_def, Complex.mul_conj,
        Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
      exact (div_eq_iff hn).mpr (pow_two _)
  · intro I J
    by_cases h : I.card = J.card
    · simp only [subsetMinorSq, dif_pos h]
      let e : I ≃ J := Fintype.equivOfCardEq (by simpa using h)
      let S := U.submatrix (fun i : I => (i : ι)) (fun i : I => ((e i : J) : ι))
      let q (i : I) := p ((e i : J) : ι)
      have hS : V.submatrix (fun i : I => (i : ι)) (fun i : I => ((e i : J) : ι)) =
          S * diagonal q := by
        ext i j
        simp [V, S, q, Matrix.mul_diagonal]
      change Complex.normSq (V.submatrix _ (fun i : I => ((e i : J) : ι))).det =
        Complex.normSq S.det
      rw [hS, Matrix.det_mul, Complex.normSq_mul, Matrix.det_diagonal, map_prod]
      simp [q, hp]
    · simp [subsetMinorSq, h]

/-- A rank-one positive semidefinite effect of trace one is a projection. -/
theorem effect_rank_one_mul_self {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.PosSemidef) (hrank : A.rank = 1) (htrace : A.trace = 1) :
    A * A = A := by
  classical
  let eig := hA.isHermitian.eigenvalues
  let V := hA.isHermitian.eigenvectorUnitary
  let P : Matrix ι ι ℝ := V
  have hV : star P * P = 1 := Matrix.mem_unitaryGroup_iff'.mp V.property
  have hdiag : A = P * diagonal eig * star P := by
    simpa [P, V, eig, RCLike.ofReal_real_eq_id] using hA.isHermitian.spectral_theorem
  have hsum : ∑ i, eig i = 1 := by
    rw [← htrace, hdiag, Matrix.trace_mul_cycle, hV, Matrix.one_mul, Matrix.trace_diagonal]
  have hcard : Fintype.card {i // eig i ≠ 0} = 1 :=
    hA.isHermitian.rank_eq_card_non_zero_eigs.symm.trans hrank
  obtain ⟨i, hi⟩ := Fintype.card_eq_one_iff.mp hcard
  have hzero (j : ι) (hj : j ≠ i.val) : eig j = 0 := by
    by_contra hn
    exact hj (congrArg Subtype.val (hi ⟨j, hn⟩))
  have hone : eig i.val = 1 := by
    rwa [Finset.sum_eq_single_of_mem i.val (Finset.mem_univ _) (fun j _ hj => hzero j hj)] at hsum
  have hsquare : diagonal eig * diagonal eig = diagonal eig := by
    rw [Matrix.diagonal_mul_diagonal]
    apply congrArg Matrix.diagonal
    funext j
    by_cases hj : j = i.val
    · simp [hj, hone]
    · simp [hzero j hj]
  calc
    A * A = P * diagonal eig * (star P * P) * diagonal eig * star P := by
      rw [hdiag]
      simp only [Matrix.mul_assoc]
    _ = A := by
      rw [hV, Matrix.mul_one, Matrix.mul_assoc P, hsquare, ← hdiag]

/-- The other two positive effects annihilate the range of a projection
in a decomposition of the identity. -/
theorem effects_mul_projection_eq_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B C : Matrix ι ι ℝ) (hProj : A * A = A) (hB : B.PosSemidef) (hC : C.PosSemidef)
    (hsum : A + B + C = 1) : B * A = 0 ∧ C * A = 0 := by
  have hBC : B + C = 1 - A := (eq_sub_iff_add_eq).mpr (by
    simpa [add_comm, add_left_comm, add_assoc] using hsum)
  have hperp (x : ι → ℝ) : B *ᵥ (A *ᵥ x) = 0 ∧ C *ᵥ (A *ᵥ x) = 0 := by
    let y := A *ᵥ x
    have hkill : (B + C) *ᵥ y = 0 := by
      rw [hBC, Matrix.sub_mulVec, Matrix.one_mulVec]
      dsimp only [y]
      rw [Matrix.mulVec_mulVec, hProj, sub_self]
    have hzero := congrArg (dotProduct (star y)) hkill
    rw [Matrix.add_mulVec, dotProduct_add, dotProduct_zero] at hzero
    exact ⟨(hB.dotProduct_mulVec_zero_iff y).mp (by linarith [hC.2 y]),
      (hC.dotProduct_mulVec_zero_iff y).mp (by linarith [hB.2 y])⟩
  constructor <;> apply Matrix.ext_of_mulVec_single <;> intro j
  · rw [← Matrix.mulVec_mulVec, Matrix.zero_mulVec]
    exact (hperp (Pi.single j 1)).1
  · rw [← Matrix.mulVec_mulVec, Matrix.zero_mulVec]
    exact (hperp (Pi.single j 1)).2

/-- Six candidate trace-free perturbations of real symmetric `3 × 3`
matrices have a nontrivial combination with zero total perturbation. -/
theorem exists_zero_sum_trace_free_perturbation
    (A B : Fin 3 → Matrix (Fin 3) (Fin 3) ℝ)
    (hA : ∀ i, (A i)ᵀ = A i ∧ (A i).trace = 0)
    (hB : ∀ i, (B i)ᵀ = B i ∧ (B i).trace = 0) :
    ∃ x : Fin 3 × Fin 2 → ℝ, x ≠ 0 ∧
      (∑ i, (x (i, 0)) • A i + (x (i, 1)) • B i) = 0 := by
  let M : (Fin 3 × Fin 2 → ℝ) →ₗ[ℝ] Matrix (Fin 3) (Fin 3) ℝ :=
    ∑ i : Fin 3, (LinearMap.proj (i, (0 : Fin 2))).smulRight (A i) +
      (LinearMap.proj (i, (1 : Fin 2))).smulRight (B i)
  let slots : Fin 5 → Fin 3 × Fin 3 := ![(0, 0), (0, 1), (0, 2), (1, 1), (1, 2)]
  let entries : Matrix (Fin 3) (Fin 3) ℝ →ₗ[ℝ] (Fin 5 → ℝ) :=
    { toFun := fun H k => H (slots k).1 (slots k).2
      map_add' := by intro X Y; rfl
      map_smul' := by intro c X; rfl }
  let L := entries.comp M
  have hdim : Module.finrank ℝ (Fin 5 → ℝ) < Module.finrank ℝ (Fin 3 × Fin 2 → ℝ) := by
    rw [Module.finrank_pi, Module.finrank_pi, Fintype.card_prod]
    decide
  obtain ⟨x, hx, hne⟩ := (LinearMap.ker L).ne_bot_iff.mp (L.ker_ne_bot_of_finrank_lt hdim)
  have hL := LinearMap.mem_ker.mp hx
  change entries (M x) = 0 at hL
  have h00 : M x 0 0 = 0 := congrFun hL 0
  have h01 : M x 0 1 = 0 := congrFun hL 1
  have h02 : M x 0 2 = 0 := congrFun hL 2
  have h11 : M x 1 1 = 0 := congrFun hL 3
  have h12 : M x 1 2 = 0 := congrFun hL 4
  have hM : M x = ∑ i, (x (i, 0)) • A i + (x (i, 1)) • B i := by
    simp [M, LinearMap.sum_apply, LinearMap.smulRight_apply]
  have hsym : (M x)ᵀ = M x := by
    simp [hM, Matrix.transpose_sum, Matrix.transpose_add, Matrix.transpose_smul,
      fun i => (hA i).1, fun i => (hB i).1]
  have h10 : M x 1 0 = 0 := (congrFun (congrFun hsym 0) 1).trans h01
  have h20 : M x 2 0 = 0 := (congrFun (congrFun hsym 0) 2).trans h02
  have h21 : M x 2 1 = 0 := (congrFun (congrFun hsym 1) 2).trans h12
  have htrace : (M x).trace = 0 := by
    simp [hM, Matrix.trace_sum, Matrix.trace_add, Matrix.trace_smul,
      fun i => (hA i).2, fun i => (hB i).2]
  have h22 : M x 2 2 = 0 := by
    simpa [Matrix.trace, Fin.sum_univ_three, Matrix.diag, h00, h11] using htrace
  refine ⟨x, hne, ?_⟩
  rw [← hM]
  ext i j
  fin_cases i <;> fin_cases j <;> first
    | exact h00
    | exact h01
    | exact h02
    | exact h10
    | exact h11
    | exact h12
    | exact h20
    | exact h21
    | exact h22

end

end MOC
