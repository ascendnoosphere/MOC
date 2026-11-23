import MOC.AnchorGramCut
import MOC.Core
import MOC.RectangleTransport

/-! Squared minors containing a chosen row and column split into the
anchor-fixing mass and a transport plan for the two opposite anchor edges. -/

open BigOperators Matrix

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The column Gram of the matrix of two-by-two minors adjoining one entry. -/
theorem anchor_minor_column_gram (c : ℂ) (v : Matrix Unit ι ℂ) (u : Matrix ι Unit ℂ)
    (D : Matrix ι ι ℂ) (hU : IsUnitary (fromBlocks (c • (1 : Matrix Unit Unit ℂ)) v u D)) :
    let T := c • D - u * v
    Tᴴ * T = (Complex.normSq c : ℂ) • (1 : Matrix ι ι ℂ) + vᴴ * v := by
  let p := (Complex.normSq c : ℂ)
  have hpc : star c * c = p := by rw [← starRingEnd_apply, ← Complex.normSq_eq_conj_mul_self]
  have hc : c * star c = p := (mul_comm _ _).trans hpc
  have hh := hU.2
  rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one] at hh
  have h11 : p • (1 : Matrix Unit Unit ℂ) + uᴴ * u = 1 := by
    have h := congrArg Matrix.toBlocks₁₁ hh
    simpa only [Matrix.toBlocks_fromBlocks₁₁, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul, Matrix.mul_one, hpc, hc] using h
  have h12 : star c • v + uᴴ * D = 0 := by
    have h := congrArg Matrix.toBlocks₁₂ hh
    simpa only [Matrix.toBlocks_fromBlocks₁₂, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
      Matrix.smul_mul, Matrix.one_mul] using h
  have h21 : c • vᴴ + Dᴴ * u = 0 := by
    have h := congrArg Matrix.toBlocks₂₁ hh
    simpa only [Matrix.toBlocks_fromBlocks₂₁, Matrix.mul_smul, Matrix.mul_one] using h
  have h22 : vᴴ * v + Dᴴ * D = 1 := by
    have h := congrArg Matrix.toBlocks₂₂ hh
    simpa only [Matrix.toBlocks_fromBlocks₂₂] using h
  have hu : uᴴ * u = (1 - p) • (1 : Matrix Unit Unit ℂ) := by
    rw [sub_smul, one_smul]
    exact (eq_sub_iff_add_eq).mpr (by simpa only [add_comm] using h11)
  have huv : uᴴ * D = -(star c • v) :=
    eq_neg_iff_add_eq_zero.mpr (by simpa only [add_comm] using h12)
  have hvu : Dᴴ * u = -(c • vᴴ) :=
    eq_neg_iff_add_eq_zero.mpr (by simpa only [add_comm] using h21)
  have hD : Dᴴ * D = 1 - vᴴ * v :=
    (eq_sub_iff_add_eq).mpr (by simpa only [add_comm] using h22)
  dsimp only
  change _ = p • (1 : Matrix ι ι ℂ) + vᴴ * v
  calc
    _ = p • (Dᴴ * D) - star c • ((Dᴴ * u) * v) - c • (vᴴ * (uᴴ * D)) +
        (vᴴ * (uᴴ * u)) * v := by
      simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
        Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, smul_sub,
        smul_smul, hpc, hc, Matrix.mul_assoc]
      abel
    _ = p • (1 - vᴴ * v) - star c • ((-(c • vᴴ)) * v) - c • (vᴴ * (-(star c • v))) +
        vᴴ * ((1 - p) • (1 : Matrix Unit Unit ℂ)) * v := by
      rw [hu, huv, hvu, hD]
    _ = p • 1 - p • (vᴴ * v) + p • (vᴴ * v) + p • (vᴴ * v) + (1 - p) • (vᴴ * v) := by
      have hscale : vᴴ * ((1 - p) • (1 : Matrix Unit Unit ℂ)) * v = (1 - p) • (vᴴ * v) := by
        simp [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
      have hleft : star c • ((-(c • vᴴ)) * v) = -(p • (vᴴ * v)) := by
        rw [Matrix.neg_mul, Matrix.smul_mul, smul_neg, smul_smul, hpc]
      have hright : c • (vᴴ * (-(star c • v))) = -(p • (vᴴ * v)) := by
        rw [Matrix.mul_neg, Matrix.mul_smul, smul_neg, smul_smul, hc]
      rw [smul_sub, hleft, hright, hscale, sub_neg_eq_add, sub_neg_eq_add]
    _ = p • 1 + vᴴ * v := by
      simp only [sub_smul, one_smul]
      abel

/-- The row Gram follows from the same calculation for the adjoint basis. -/
theorem anchor_minor_row_gram (c : ℂ) (v : Matrix Unit ι ℂ) (u : Matrix ι Unit ℂ)
    (D : Matrix ι ι ℂ) (hU : IsUnitary (fromBlocks (c • (1 : Matrix Unit Unit ℂ)) v u D)) :
    let T := c • D - u * v
    T * Tᴴ = (Complex.normSq c : ℂ) • (1 : Matrix ι ι ℂ) + u * uᴴ := by
  have hadj : IsUnitary (fromBlocks (star c • (1 : Matrix Unit Unit ℂ)) uᴴ vᴴ Dᴴ) := by
    have hh : IsUnitary (fromBlocks (c • (1 : Matrix Unit Unit ℂ)) v u D)ᴴ := by
      simpa only [IsUnitary, Matrix.conjTranspose_conjTranspose] using And.intro hU.2 hU.1
    simpa only [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_one] using hh
  have hg := anchor_minor_column_gram (star c) uᴴ vᴴ Dᴴ hadj
  dsimp only at hg ⊢
  have hT : (c • D - u * v)ᴴ = star c • Dᴴ - vᴴ * uᴴ := by
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul]
  rw [← hT] at hg
  simpa only [Matrix.conjTranspose_conjTranspose, Complex.star_def, Complex.normSq_conj] using hg

/-- The squared anchor minors dominate a nonnegative transport plan with
the unanchored portions of the first column and first row as margins. -/
theorem exists_anchor_minor_margin_split (c : ℂ) (v : Matrix Unit ι ℂ) (u : Matrix ι Unit ℂ)
    (D : Matrix ι ι ℂ) (hU : IsUnitary (fromBlocks (c • (1 : Matrix Unit Unit ℂ)) v u D)) :
    let T := c • D - u * v
    ∃ N : ι → ι → ℝ, (∀ i j, 0 ≤ N i j ∧ N i j ≤ Complex.normSq (T i j)) ∧
      (∀ i, ∑ j, N i j = Complex.normSq (u i ())) ∧
      (∀ j, ∑ i, N i j = Complex.normSq (v () j)) := by
  let T := c • D - u * v
  let p := Complex.normSq c
  have hcol : Tᴴ * T = (p : ℂ) • (1 : Matrix ι ι ℂ) + vᴴ * v :=
    anchor_minor_column_gram c v u D hU
  have hrow : T * Tᴴ = (p : ℂ) • (1 : Matrix ι ι ℂ) + u * uᴴ :=
    anchor_minor_row_gram c v u D hU
  have hr (i : ι) : (∑ j, Complex.normSq (T i j)) = Complex.normSq (u i ()) + p := by
    have he := congrArg (fun M : Matrix ι ι ℂ => (M i i).re) hrow
    simpa only [gram_diagonal_re, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.one_apply_eq, mul_one, Complex.add_re, Complex.ofReal_re, Fintype.sum_unique,
      add_comm] using he
  have hc (j : ι) : (∑ i, Complex.normSq (T i j)) = Complex.normSq (v () j) + p := by
    have he := gram_diagonal_re Tᴴ j
    have hv := gram_diagonal_re vᴴ j
    rw [Matrix.conjTranspose_conjTranspose] at hv
    rw [Matrix.conjTranspose_conjTranspose, hcol] at he
    simpa only [hv, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.one_apply_eq, mul_one, Complex.add_re, Complex.ofReal_re, Fintype.sum_unique,
      Matrix.conjTranspose_apply, Complex.star_def, Complex.normSq_conj, add_comm] using he.symm
  dsimp only
  change ∃ N : ι → ι → ℝ, (∀ i j, 0 ≤ N i j ∧ N i j ≤ Complex.normSq (T i j)) ∧ _ ∧ _
  by_cases hc0 : c = 0
  · have hp0 : p = 0 := by simp [p, hc0]
    exact ⟨fun i j => Complex.normSq (T i j),
      fun i j => ⟨Complex.normSq_nonneg _, le_rfl⟩,
      fun i => by simpa only [hp0, add_zero] using hr i,
      fun j => by simpa only [hp0, add_zero] using hc j⟩
  · have hp : 0 < p := Complex.normSq_pos.mpr hc0
    exact exists_margin_split_of_rectangle_bounds (fun i j => Complex.normSq (T i j))
      (fun i => Complex.normSq (u i ())) (fun j => Complex.normSq (v () j)) p hp.le
      (fun _ _ => Complex.normSq_nonneg _) (fun _ => Complex.normSq_nonneg _)
      (fun _ => Complex.normSq_nonneg _) hr hc (fun I J => by
        simpa only [mul_comm p] using rectangle_normSq_le_of_rankOne_gram T v p hp hcol I J)

end

end MOC
