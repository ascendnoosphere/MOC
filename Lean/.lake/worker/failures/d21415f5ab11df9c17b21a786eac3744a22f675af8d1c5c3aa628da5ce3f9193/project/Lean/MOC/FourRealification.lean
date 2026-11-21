import MOC.Realification
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.FinCases

/-! Linear algebra for the fixed-row realification in dimension four. -/

open BigOperators Matrix

namespace MOC

noncomputable section

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
