import MOC.RankTwoKernelInclusion
import MOC.DeletionAndPaddingObstructions

/-! Rank-one kernels, spinor brackets, and a rank-three obstruction. -/

open BigOperators Matrix

namespace MOC.Reformulations

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem rank_le_of_product_factors {κ : Type*} [Fintype κ]
    (L : Matrix ι κ ℂ) (R : Matrix κ ι ℂ) : (L * R).rank ≤ Fintype.card κ :=
  (Matrix.rank_mul_le_left L R).trans (Matrix.rank_le_card_width L)

private theorem row_column_product_holds (x y : ι → ℂ) (U : Matrix ι ι ℂ)
    (hU : IsUnitary U) :
    kernelDeterminantValue (Matrix.of fun i j => x i * y j) U ∈
      convexHull ℝ (Set.range (kernelMatchingProduct (Matrix.of fun i j => x i * y j))) := by
  let K : Matrix ι ι ℂ := Matrix.of fun i j => x i * y j
  let c : ℂ := (∏ i, x i) * ∏ j, y j
  have hp (σ : Equiv.Perm ι) : kernelMatchingProduct K σ = c := by
    simp only [kernelMatchingProduct, K, Matrix.of_apply, Finset.prod_mul_distrib, Equiv.prod_comp, c]
  change kernelDeterminantValue K U ∈ _
  rw [kernelDeterminantValue_eq_sum_signed]
  simp_rw [hp]
  rw [← Finset.sum_mul, sum_signedWeight U (det_ne_zero_of_unitary hU), one_mul]
  exact subset_convexHull ℝ _ ⟨1, hp 1⟩

private theorem rank_submatrix_le_of_selected_indices {κ : Type*} [Fintype κ] [DecidableEq κ]
    (K : Matrix ι ι ℂ) (r c : κ → ι) : (K.submatrix r c).rank ≤ K.rank := by
  have hfin : K.eRank ≠ ⊤ := ne_top_of_le_ne_top (by simp : ENat.card ι ≠ ⊤)
    K.eRank_le_card_width
  simpa only [Matrix.eRank_toNat_eq_rank] using ENat.toNat_le_toNat
    (K.eRank_submatrix_le r c) hfin

private theorem det_two_selection_zero (K : Matrix ι ι ℂ) (hK : K.rank ≤ 1)
    (r c : Fin 2 → ι) : (K.submatrix r c).det = 0 := by
  by_contra hn
  have hu := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hn)
  have hr := (rank_submatrix_le_of_selected_indices K r c).trans hK
  rw [Matrix.rank_of_isUnit _ hu, Fintype.card_fin] at hr
  omega

/-- The universal Hadamard determinant inclusion holds at rank one. -/
theorem rank_kernel_conjecture_one : RankKernelConjecture ι 1 := by
  classical
  intro K U hK hU
  by_cases h : ∃ i j, K i j ≠ 0
  · obtain ⟨p, q, hpq⟩ := h
    let x (i : ι) := K i q
    let y (j : ι) := K p j / K p q
    have hK' : K = Matrix.of fun i j => x i * y j := by
      ext i j : 1
      have hz := det_two_selection_zero K hK ![i, p] ![j, q]
      simp only [Matrix.det_fin_two, Matrix.submatrix_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, sub_eq_zero] at hz
      change K i j = K i q * (K p j / K p q)
      rw [← mul_div_assoc]
      exact (eq_div_iff hpq).mpr hz
    rw [hK']
    exact row_column_product_holds x y U hU
  · have hK' : K = Matrix.of fun (_ _ : ι) => (0 : ℂ) * 0 := by
      ext i j : 1
      have hz : K i j = 0 := by
        by_contra hh
        exact h ⟨i, j, hh⟩
      simpa only [Matrix.of_apply, mul_zero] using hz
    rw [hK']
    exact row_column_product_holds (fun _ => 0) (fun _ => 0) U hU

/-- The alternating bracket matrix of two lists of vectors in `ℂ²`. -/
def spinorBracketKernel (x y : ι → Fin 2 → ℂ) : Matrix ι ι ℂ :=
  Matrix.of fun i j => x i 0 * y j 1 - x i 1 * y j 0

private theorem spinorBracketKernel_rank_le_two (x y : ι → Fin 2 → ℂ) :
    (spinorBracketKernel x y).rank ≤ 2 := by
  simpa only [spinorBracketKernel, mul_neg, sub_eq_add_neg] using
    rank_two_product_kernel_le (fun i => x i 0) (fun i => x i 1)
      (fun j => y j 1) (fun j => -y j 0)

/-- Testing Hadamard determinants on the alternating brackets of two lists of
complex two-vectors is equivalent to the Marcus–de Oliveira conjecture. -/
theorem conjecture_iff_spinor_bracket : Conjecture ι ↔
    ∀ (x y : ι → Fin 2 → ℂ) (U : Matrix ι ι ℂ), IsUnitary U →
      kernelDeterminantValue (spinorBracketKernel x y) U ∈
        convexHull ℝ (Set.range (kernelMatchingProduct (spinorBracketKernel x y))) := by
  rw [← rankTwoKernelInclusion_iff_conjecture]
  constructor
  · intro h x y U hU
    exact h _ U (spinorBracketKernel_rank_le_two x y) hU
  · intro h K U hK hU
    have hminor := (rank_le_two_iff_vanishing_three_minors K).mp hK
    obtain ⟨a, b, u, v, hf⟩ := exists_two_product_factors_of_three_minors_eq_zero K hminor
    let x (i : ι) : Fin 2 → ℂ := ![a i, b i]
    let y (j : ι) : Fin 2 → ℂ := ![-v j, u j]
    have he : K = spinorBracketKernel x y := by
      ext i j : 1
      rw [hf]
      simp only [spinorBracketKernel, Matrix.of_apply, x, y, Matrix.cons_val_zero,
        Matrix.cons_val_one, mul_neg, sub_neg_eq_add]
    rw [he]
    exact h x y U hU

private theorem rank_kernel_conjecture_reindex {κ : Type*} [Fintype κ] [DecidableEq κ]
    (e : κ ≃ ι) (r : ℕ) (h : RankKernelConjecture κ r) : RankKernelConjecture ι r := by
  intro K U hK hU
  have hr : (K.submatrix e e).rank = K.rank := Matrix.rank_submatrix K e e
  have hv : kernelDeterminantValue (K.submatrix e e) (U.submatrix e e) =
      kernelDeterminantValue K U := by
    change (Matrix.of fun i j : κ => K (e i) (e j) * U (e i) (e j)).det /
      (U.submatrix e e).det = (Matrix.of fun i j => K i j * U i j).det / U.det
    rw [show (Matrix.of fun i j : κ => K (e i) (e j) * U (e i) (e j)) =
      (Matrix.of fun i j => K i j * U i j).submatrix e e from rfl]
    rw [Matrix.det_submatrix_equiv_self, Matrix.det_submatrix_equiv_self]
  have hp (σ : Equiv.Perm κ) : kernelMatchingProduct (K.submatrix e e) σ =
      kernelMatchingProduct K ((e.symm.trans σ).trans e) := by
    unfold kernelMatchingProduct
    rw [← Equiv.prod_comp e (fun j => K (((e.symm.trans σ).trans e) j) j)]
    simp only [Matrix.submatrix_apply, Equiv.trans_apply, Equiv.symm_apply_apply]
  have hh := h (K.submatrix e e) (U.submatrix e e) (hr ▸ hK) (unitary_reindex e e hU)
  rw [hv] at hh
  apply convexHull_mono _ hh
  rintro _ ⟨σ, rfl⟩
  exact ⟨_, (hp σ).symm⟩

private theorem not_rank_kernel_conjecture_three_sum {κ : Type*} [Fintype κ] [DecidableEq κ] :
    ¬ RankKernelConjecture (Fin 3 ⊕ κ) 3 := by
  classical
  let color : Fin 3 ⊕ κ → Fin 3 := Sum.elim id (fun _ => 0)
  let K : Matrix (Fin 3 ⊕ κ) (Fin 3 ⊕ κ) ℂ :=
    Matrix.of fun i j => if color i = color j then 1 else 0
  let L : Matrix (Fin 3 ⊕ κ) (Fin 3) ℂ := Matrix.of fun i k => if color i = k then 1 else 0
  have hfac : K = L * Lᵀ := by
    ext i j : 1
    rw [Matrix.mul_apply, Finset.sum_eq_single (color i)]
    · simp [K, L, Matrix.transpose_apply, eq_comm]
    · intro k _ hk
      simp [L, hk.symm]
    · simp
  have hr : K.rank ≤ 3 := by
    rw [hfac]
    simpa only [Fintype.card_fin] using rank_le_of_product_factors L Lᵀ
  let U : Matrix (Fin 3 ⊕ κ) (Fin 3 ⊕ κ) ℂ := fromBlocks deletionObstructionMixer 0 0 1
  have hU : IsUnitary U := unitary_directSum deletionObstructionMixer_unitary isUnitary_one
  have hentry : (Matrix.of fun i j => K i j * U i j) =
      fromBlocks ((1 / 3 : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ)) 0 0 (1 : Matrix κ κ ℂ) := by
    ext (i | i) (j | j) : 1
    · fin_cases i <;> fin_cases j <;>
        norm_num [K, U, color, deletionObstructionMixer, Matrix.one_apply,
          Matrix.smul_apply, smul_eq_mul, Matrix.cons_val]
    · simp [K, U, color]
    · simp [K, U, color]
    · simp [K, U, color]
  have hdet : U.det = -1 := by
    rw [U, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, mul_one]
    norm_num [deletionObstructionMixer, Matrix.det_fin_three, Matrix.cons_val]
  have he : kernelDeterminantValue K U = -(1 / 27) := by
    change (Matrix.of fun i j => K i j * U i j).det / U.det = _
    rw [hentry, hdet, Matrix.det_fromBlocks_zero₁₂, Matrix.det_smul]
    simp only [Matrix.det_one, mul_one, Fintype.card_fin]
    norm_num
  intro hc
  have hh := hc K U hr hU
  have hnonneg : 0 ≤ (kernelDeterminantValue K U).re := by
    apply convexHull_min _ ((convex_Ici (𝕜 := ℝ) (0 : ℝ)).linear_preimage Complex.reLm) hh
    rintro _ ⟨σ, rfl⟩
    change 0 ≤ (kernelMatchingProduct K σ).re
    by_cases hall : ∀ j, color (σ j) = color j
    · simp [kernelMatchingProduct, K, hall]
    · obtain ⟨j, hj⟩ := not_forall.mp hall
      have he : kernelMatchingProduct K σ = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ j) (by simp [K, hj])
      simp [he]
  rw [he] at hnonneg
  norm_num [Complex.div_re, Complex.normSq] at hnonneg

/-- In every order at least three, a rank-at-most-three kernel refutes the
universal Hadamard determinant inclusion. -/
theorem not_rank_kernel_conjecture_three {n : ℕ} (hn : 3 ≤ n) :
    ¬ RankKernelConjecture (Fin n) 3 := by
  intro h
  let e : (Fin 3 ⊕ Fin (n - 3)) ≃ Fin n :=
    finSumFinEquiv.trans (finCongr (by omega))
  exact not_rank_kernel_conjecture_three_sum (rank_kernel_conjecture_reindex e.symm 3 h)

/-- In orders at least three the largest admissible rank is one or two, and
it is two exactly when the unrestricted conjecture holds in that order. -/
theorem conjecture_iff_hadamard_rank_threshold {n : ℕ} (hn : 3 ≤ n) :
    Conjecture (Fin n) ↔ RankKernelConjecture (Fin n) 2 ∧
      ∀ r, RankKernelConjecture (Fin n) r → r ≤ 2 := by
  rw [← rankTwoKernelInclusion_iff_conjecture]
  refine ⟨fun h => ⟨h, ?_⟩, And.left⟩
  intro r hr
  by_contra! hlarge
  exact not_rank_kernel_conjecture_three hn (fun K U hK hU => hr K U (hK.trans (by omega)) hU)

end
end MOC.Reformulations
