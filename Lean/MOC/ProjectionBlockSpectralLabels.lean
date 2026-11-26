import MOC.ProjectionConditioning
import MOC.Small
import Mathlib.LinearAlgebra.Matrix.Spectrum

/-! The labelled spectrum of a projection block with private diagonal entries. -/

open BigOperators Matrix Finset

namespace MOC

noncomputable section

variable {κ ι : Type*} [DecidableEq κ] [Fintype ι] [DecidableEq ι]

/-- A private spectral label has its named value. A level label has value s or s + k. -/
def projectionBlockValue (d : κ → ℂ) (s k : ℂ) : κ ⊕ Bool → ℂ
  | .inl c => d c
  | .inr b => if b then s + k else s

/-- The sum of a private diagonal, the base level on the active coordinates, and k times P. -/
def projectionBlockMatrix (g : ι → Option κ)
    (P : Matrix ι ι ℂ) (d : κ → ℂ) (s k : ℂ) : Matrix ι ι ℂ :=
  diagonal (fun i => (g i).elim s d) + k • P

/-- The number of occurrences of each private or level label. -/
def projectionBlockMass (g : ι → Option κ)
    (P : Matrix ι ι ℂ) : κ ⊕ Bool → ℝ
  | .inl c => ∑ i, if g i = some c then 1 else 0
  | .inr true => P.trace.re
  | .inr false => (∑ i, if g i = none then 1 else 0) - P.trace.re

/-- The spectral labels have the same multiplicities as the projection block. -/
def ProjectionBlockLabels (g : ι → Option κ)
    (P : Matrix ι ι ℂ) (a : ι → κ ⊕ Bool) : Prop :=
  ∀ c, (∑ j, if a j = c then (1 : ℝ) else 0) = projectionBlockMass g P c

/-- A projection supported on the active coordinates has a labelled eigenbasis
that works for every scalar choice on the projection block and its private coordinates. -/
theorem exists_projection_block_spectral_labels (g : ι → Option κ) (P : Matrix ι ι ℂ)
    (hP : P.IsHermitian) (hPP : P * P = P)
    (hsupp : ∀ i c, g i = some c → ∀ j, P i j = 0) :
    ∃ (a : ι → κ ⊕ Bool) (V : Matrix ι ι ℂ), ProjectionBlockLabels g P a ∧ IsUnitary V ∧
      ∀ (d : κ → ℂ) (s k : ℂ), projectionBlockMatrix g P d s k =
        V * diagonal (projectionBlockValue d s k ∘ a) * Vᴴ := by
  classical
  let I := {i : ι // g i = none}
  let K := {i : ι // g i ≠ none}
  let e : I ⊕ K ≃ ι := Equiv.sumCompl (fun i => g i = none)
  let R : Matrix I I ℂ := P.submatrix Subtype.val Subtype.val
  let name (j : K) : κ := (g j).get (Option.isSome_iff_ne_none.mpr j.property)
  have hg (j : K) : g j = some (name j) := by simp [name]
  have heI (i : I) : g (e (Sum.inl i)) = none := i.property
  have heK (j : K) : g (e (Sum.inr j)) = some (name j) := hg j
  have hzero (j : K) (i : ι) : P j i = 0 := hsupp j _ (hg j) i
  have hzero' (i : ι) (j : K) : P i j = 0 := by
    have h := congrFun (congrFun hP.eq i) j.val
    simpa only [conjTranspose_apply, hzero j i, star_zero] using h.symm
  have hsplit : P.submatrix e e = fromBlocks R 0 0 (0 : Matrix K K ℂ) := by
    ext (i | i) (j | j) : 1
    · rfl
    · exact hzero' i j
    · exact hzero i j
    · exact hzero i j
  have hR : R.IsHermitian := hP.submatrix Subtype.val
  have hRR : R * R = R := by
    have hm : P.submatrix e e * P.submatrix e e = P.submatrix e e := by
      rw [submatrix_mul_equiv P P e e e, hPP]
    rw [hsplit, fromBlocks_multiply, fromBlocks_inj] at hm
    simpa using hm.1
  let W : Matrix I I ℂ := hR.eigenvectorUnitary
  have hW : IsUnitary W := ⟨Matrix.mem_unitaryGroup_iff.mp hR.eigenvectorUnitary.2,
    Matrix.mem_unitaryGroup_iff'.mp hR.eigenvectorUnitary.2⟩
  let bit (i : I) : Bool := decide (hR.eigenvalues i = 1)
  have hbit (i : I) : (if bit i then (1 : ℂ) else 0) = hR.eigenvalues i := by
    rcases projection_eigenvalues_zero_or_one hR hRR i with hi | hi <;> simp [bit, hi]
  have hRspec : R = W * diagonal (fun i => if bit i then (1 : ℂ) else 0) * Wᴴ := by
    simp_rw [hbit]
    exact hR.spectral_theorem
  let V' := fromBlocks W 0 0 (1 : Matrix K K ℂ)
  let V := V'.submatrix e.symm e.symm
  let tag : I ⊕ K → κ ⊕ Bool := Sum.elim (Sum.inr ∘ bit) (Sum.inl ∘ name)
  let a := tag ∘ e.symm
  refine ⟨a, V, ?_, unitary_reindex e.symm e.symm (unitary_directSum hW isUnitary_one), ?_⟩
  · intro c
    rw [← Equiv.sum_comp e (fun i => if a i = c then (1 : ℝ) else 0)]
    simp only [a, Function.comp_apply, Equiv.symm_apply_apply, Fintype.sum_sum_type]
    have ht : P.trace = R.trace := by
      rw [← show (P.submatrix e e).trace = P.trace from Equiv.sum_comp e (fun i => P i i), hsplit]
      simp [Matrix.trace, Fintype.sum_sum_type]
    cases c with
    | inl c =>
      simp only [tag, Sum.elim_inl, Sum.elim_inr, Function.comp_apply, Sum.inr_ne_inl,
        Sum.inl.injEq, if_false, Finset.sum_const_zero, zero_add, projectionBlockMass]
      rw [← Equiv.sum_comp e (fun i => if g i = some c then (1 : ℝ) else 0),
        Fintype.sum_sum_type]
      simp [heI, heK]
    | inr b =>
      have htrue : (∑ i : I, if bit i then (1 : ℝ) else 0) = P.trace.re := by
        rw [ht, hRspec, Matrix.trace_mul_cycle, hW.2, Matrix.one_mul, Matrix.trace_diagonal,
          Complex.re_sum]
        simp only [apply_ite Complex.re, Complex.one_re, Complex.zero_re]
      cases b
      · simp only [tag, Sum.elim_inl, Sum.elim_inr, Function.comp_apply, Sum.inr.injEq,
          Sum.inl_ne_inr, if_false, Finset.sum_const_zero, add_zero, projectionBlockMass]
        rw [← Equiv.sum_comp e (fun i => if g i = none then (1 : ℝ) else 0),
          Fintype.sum_sum_type, ← htrue]
        simp only [heI, heK, Option.some_ne_none, ↓reduceIte, if_false, Finset.sum_const_zero,
          add_zero, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        cases bit i <;> simp
      · simpa [tag, projectionBlockMass] using htrue
  · intro d s k
    have haff : s • (1 : Matrix I I ℂ) + k • R =
        W * diagonal (fun i => if bit i then s + k else s) * Wᴴ := by
      let u (i : I) := if bit i then (1 : ℂ) else 0
      have hu : (fun i => if bit i then s + k else s) = fun i => s + (k • u) i := by
        funext i
        cases h : bit i <;> simp [u, h, Pi.smul_apply]
      rw [hu, ← Matrix.diagonal_add (fun _ : I => s) (k • u), Matrix.diagonal_smul,
        Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
        show W * diagonal u * Wᴴ = R from hRspec.symm, ← Matrix.smul_one_eq_diagonal,
        Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hW.1]
    have hdiag : (diagonal (fun i => (g i).elim s d)).submatrix e e =
        fromBlocks (s • (1 : Matrix I I ℂ)) 0 0 (diagonal (d ∘ name)) := by
      rw [Matrix.submatrix_diagonal_equiv, Matrix.smul_one_eq_diagonal, Matrix.fromBlocks_diagonal]
      apply congrArg Matrix.diagonal
      funext i
      rcases i with i | i <;> simp [heI, heK]
    have htag : (diagonal (projectionBlockValue d s k ∘ a)).submatrix e e =
        fromBlocks (diagonal (fun i : I => if bit i then s + k else s)) 0 0
          (diagonal (d ∘ name)) := by
      rw [Matrix.submatrix_diagonal_equiv, Matrix.fromBlocks_diagonal]
      apply congrArg Matrix.diagonal
      funext i
      rcases i with i | i <;> simp [tag, a, projectionBlockValue]
    apply (Matrix.reindex e.symm e.symm).injective
    change (projectionBlockMatrix g P d s k).submatrix e e =
      (V * diagonal (projectionBlockValue d s k ∘ a) * Vᴴ).submatrix e e
    rw [← Matrix.submatrix_mul_equiv (V * diagonal (projectionBlockValue d s k ∘ a)) Vᴴ e e e,
      ← Matrix.submatrix_mul_equiv V (diagonal (projectionBlockValue d s k ∘ a)) e e e,
      ← Matrix.conjTranspose_submatrix, projectionBlockMatrix]
    change (diagonal (fun i => (g i).elim s d)).submatrix e e + k • P.submatrix e e = _
    have hV : V.submatrix e e = V' := by
      ext i j : 1
      simp only [V, Matrix.submatrix_apply, Equiv.symm_apply_apply]
    rw [hdiag, hsplit, hV, htag, Matrix.fromBlocks_smul, Matrix.fromBlocks_add,
      Matrix.fromBlocks_conjTranspose]
    simp only [V', Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj,
      smul_zero, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.one_mul,
      Matrix.mul_one, Matrix.conjTranspose_zero, Matrix.conjTranspose_one, true_and, and_true]
    exact haff

end

end MOC
