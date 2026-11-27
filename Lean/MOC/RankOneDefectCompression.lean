import MOC.PrincipalCoisometry
import MOC.Householder
import MOC.Transfer
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! The compression in the determinant comparison has a square corner
with one defective singular value. The missing column is the Gram factor
of its positive semidefinite defect. -/

open Matrix
open scoped ComplexOrder

namespace MOC

noncomputable section

private theorem exists_columnGram_of_posSemidef_rank_le_one
    {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ)
    (hH : H.PosSemidef) (hrank : H.rank ≤ 1) :
    ∃ u : Matrix ι Unit ℂ, H = u * uᴴ := by
  classical
  let eig := hH.isHermitian.eigenvalues
  let W : Matrix ι ι ℂ := hH.isHermitian.eigenvectorUnitary
  have hH' : H = W * diagonal (fun i => (eig i : ℂ)) * Wᴴ := hH.isHermitian.spectral_theorem
  have hcard : Fintype.card {i // eig i ≠ 0} ≤ 1 :=
    hH.isHermitian.rank_eq_card_non_zero_eigs.symm.trans_le hrank
  letI := Fintype.card_le_one_iff_subsingleton.mp hcard
  by_cases h : ∃ j, eig j ≠ 0
  · obtain ⟨j, hj⟩ := h
    let t : ℂ := (Real.sqrt (eig j) : ℂ)
    let u : Matrix ι Unit ℂ := Matrix.of fun i _ => W i j * t
    have hz (k : ι) (hk : k ≠ j) : eig k = 0 := by
      by_contra hne
      have he : (⟨k, hne⟩ : {i // eig i ≠ 0}) = ⟨j, hj⟩ := Subsingleton.elim _ _
      exact hk (congrArg Subtype.val he)
    have ht : t * star t = (eig j : ℂ) := by
      rw [show star t = t from Complex.conj_ofReal _, ← pow_two]
      dsimp only [t]
      rw [← Complex.ofReal_pow,
        Real.sq_sqrt (hH.eigenvalues_nonneg j)]
    refine ⟨u, ?_⟩
    rw [hH']
    ext i k
    rw [Matrix.mul_apply (N := Wᴴ)]
    simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply]
    rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ j)]
    · simp only [u, Matrix.mul_apply, Fintype.sum_unique, Matrix.conjTranspose_apply,
        Matrix.of_apply, star_mul']
      rw [← ht]
      ring
    · intro l _ hl
      simp only [hz l hl, Complex.ofReal_zero, mul_zero, zero_mul]
  · push_neg at h
    exact ⟨0, by simp [hH', h]⟩

private def defectFrame {n : ℕ} (V : Matrix (Fin n) (Fin n) ℂ) (u : Matrix (Fin n) Unit ℂ) :
    Matrix (Fin n) (Fin (n + 1)) ℂ := Matrix.of fun i => Fin.cons (u i ()) (V i)

private theorem defectFrame_gram {n : ℕ} (V : Matrix (Fin n) (Fin n) ℂ)
    (u : Matrix (Fin n) Unit ℂ) :
    defectFrame V u * (defectFrame V u)ᴴ = u * uᴴ + V * Vᴴ := by
  ext i j
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fin.sum_univ_succ, Fintype.sum_unique, defectFrame, Matrix.of_apply, Fin.cons_zero, Fin.cons_succ]

private theorem defectFrame_compression {n : ℕ} (V : Matrix (Fin n) (Fin n) ℂ)
    (u : Matrix (Fin n) Unit ℂ) (b : Fin n → ℂ) :
    defectFrame V u * diagonal (Fin.cons 0 b) * (defectFrame V u)ᴴ = V * diagonal b * Vᴴ := by
  ext i j
  rw [Matrix.mul_apply (N := (defectFrame V u)ᴴ), Matrix.mul_apply (N := Vᴴ)]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, Fin.sum_univ_succ, defectFrame,
    Matrix.of_apply, Fin.cons_zero, Fin.cons_succ, mul_zero, zero_mul, zero_add]

private theorem right_defect_column {n : ℕ} {V : Matrix (Fin n) (Fin n) ℂ}
    (hV : (1 - V * Vᴴ).PosSemidef) (hr : (1 - V * Vᴴ).rank ≤ 1) :
    ∃ u : Matrix (Fin n) Unit ℂ, defectFrame V u * (defectFrame V u)ᴴ = 1 := by
  obtain ⟨u, hu⟩ := exists_columnGram_of_posSemidef_rank_le_one _ hV hr
  exact ⟨u, by rw [defectFrame_gram, ← hu, sub_add_cancel]⟩

private theorem left_defect_of_right_defect {n : ℕ} (V : Matrix (Fin n) (Fin n) ℂ)
    (hV : (1 - V * Vᴴ).PosSemidef) (hr : (1 - V * Vᴴ).rank ≤ 1) :
    (1 - Vᴴ * V).PosSemidef ∧ (1 - Vᴴ * V).rank ≤ 1 := by
  obtain ⟨u, hu⟩ := right_defect_column hV hr
  obtain ⟨W, hW, htail⟩ := exists_unitary_retained_rows (defectFrame V u) hu 0
  let r : Matrix Unit (Fin n) ℂ := Matrix.of fun _ j => W 0 j.succ
  have hWV (i j : Fin n) : W i.succ j.succ = V i j := by
    have h := congrArg (fun Y : Matrix (Fin n) (Fin (n + 1)) ℂ => Y i j.succ) htail
    simpa only [Matrix.submatrix_apply, Fin.succAbove_zero, id_eq, defectFrame,
      Matrix.of_apply, Fin.cons_succ] using h
  have hsum : rᴴ * r + Vᴴ * V = 1 := by
    ext i j
    have h := congrArg (fun K : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ => K i.succ j.succ) hW.2
    simpa only [Matrix.add_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ, Matrix.one_apply, Fin.succ_inj, hWV, r, Fintype.sum_unique,
      Matrix.of_apply] using h
  have hdef : 1 - Vᴴ * V = rᴴ * r := by rw [← hsum, add_sub_cancel_right]
  rw [hdef]
  exact ⟨Matrix.posSemidef_conjTranspose_mul_self r,
    (Matrix.rank_mul_le_left _ _).trans (by simpa using Matrix.rank_le_card_width rᴴ)⟩

/-- The two Gram defects have the same positivity and rank-one condition. -/
theorem rank_one_defect_left_iff_right {n : ℕ} (V : Matrix (Fin n) (Fin n) ℂ) :
    ((1 - Vᴴ * V).PosSemidef ∧ (1 - Vᴴ * V).rank ≤ 1) ↔
      ((1 - V * Vᴴ).PosSemidef ∧ (1 - V * Vᴴ).rank ≤ 1) := by
  refine ⟨fun h => ?_, fun h => left_defect_of_right_defect V h.1 h.2⟩
  simpa only [Matrix.conjTranspose_conjTranspose] using
    left_defect_of_right_defect Vᴴ (by simpa only [Matrix.conjTranspose_conjTranspose] using h.1)
      (by simpa only [Matrix.conjTranspose_conjTranspose] using h.2)

/-- The square-corner form has one extra partner label, equal to zero. -/
def RankOneDefectConjecture (n : ℕ) : Prop :=
  ∀ (a b : Fin n → ℂ) (V : Matrix (Fin n) (Fin n) ℂ),
    (1 - Vᴴ * V).PosSemidef → (1 - Vᴴ * V).rank ≤ 1 →
    (diagonal a + V * diagonal b * Vᴴ).det ∈
      convexHull ℝ (Set.range (rectangularMatchingProduct a (Fin.cons 0 b)))

/-- The square-corner condition with a positive rank-one Gram defect
is equivalent to the rectangular coisometry comparison. -/
theorem principalCoisometry_iff_rankOneDefect (n : ℕ) :
    PrincipalCoisometryConjecture n ↔ RankOneDefectConjecture n := by
  constructor
  · intro h a b V hV hr
    obtain ⟨hV', hr'⟩ := (rank_one_defect_left_iff_right V).mp ⟨hV, hr⟩
    obtain ⟨u, hu⟩ := right_defect_column hV' hr'
    simpa only [defectFrame_compression] using h a (Fin.cons 0 b) (defectFrame V u) hu
  · intro h a β Y hY
    let c := β 0
    let b : Fin n → ℂ := fun j => β j.succ - c
    let a' : Fin n → ℂ := fun j => a j + c
    let V := Y.submatrix id Fin.succ
    let u : Matrix (Fin n) Unit ℂ := Matrix.of fun i _ => Y i 0
    have hframe : defectFrame V u = Y := by
      ext i j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp only [defectFrame, Matrix.of_apply, Fin.cons_zero, u]
      · simp only [defectFrame, Matrix.of_apply, Fin.cons_succ, V, Matrix.submatrix_apply, id_eq]
    have hdef : 1 - V * Vᴴ = u * uᴴ := by
      have heq : u * uᴴ + V * Vᴴ = 1 := by rwa [← defectFrame_gram, hframe]
      rw [← heq, add_sub_cancel_right]
    have hright : (1 - V * Vᴴ).PosSemidef ∧ (1 - V * Vᴴ).rank ≤ 1 := by
      rw [hdef]
      exact ⟨Matrix.posSemidef_self_mul_conjTranspose u,
        (Matrix.rank_mul_le_left _ _).trans (by simpa using Matrix.rank_le_card_width u)⟩
    obtain ⟨hleft, hleftRank⟩ := (rank_one_defect_left_iff_right V).mpr hright
    have hβ (j : Fin (n + 1)) : β j = c + Fin.cons (α := fun _ => ℂ) 0 b j := by
      refine Fin.cases ?_ (fun j => ?_) j
      · simp only [c, Fin.cons_zero, add_zero]
      · simp only [b, Fin.cons_succ]
        ring
    have hmat {k : ℕ} (x : Fin k → ℂ) :
        diagonal (fun i => c + x i) = c • (1 : Matrix (Fin k) (Fin k) ℂ) + diagonal x := by
      ext i j
      by_cases hij : i = j <;> simp [Matrix.diagonal_apply, Matrix.one_apply, hij]
    have hcomp : diagonal a + Y * diagonal β * Yᴴ = diagonal a' + V * diagonal b * Vᴴ := by
      rw [show β = fun j => c + Fin.cons (α := fun _ => ℂ) 0 b j from funext hβ, hmat, Matrix.mul_add,
        Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hY, ← hframe,
        defectFrame_compression, show a' = fun j => c + a j from funext (fun _ => add_comm _ _), hmat]
      abel
    have hp (e : Fin n ↪ Fin (n + 1)) :
        rectangularMatchingProduct a β e = rectangularMatchingProduct a' (Fin.cons 0 b) e := by
      apply Finset.prod_congr rfl
      intro i _
      rw [hβ (e i)]
      dsimp only [a']
      ring
    rw [hcomp, funext hp]
    exact h a' b V hleft hleftRank

/-- The order-`n+1` conjecture is the order-`n` compression with one
possibly defective singular value and one extra zero partner label. -/
theorem conjecture_iff_rankOneDefect (n : ℕ) :
    Conjecture (Fin (n + 1)) ↔ RankOneDefectConjecture n :=
  (conjecture_iff_principalCoisometry n).trans (principalCoisometry_iff_rankOneDefect n)

private theorem scalar_fin_one_eq_smul (a : ℂ) :
    scalar (Fin 1) a = a • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  ext i j
  have h : i = j := Subsingleton.elim _ _
  subst j
  simp [scalar_apply]

/-- An affine transfer factors into one fixed unitary and a rank-one
phase. The proof uses the unitary block identities at the boundary phase. -/
theorem affineSchurTransfer_rankOnePhase
    {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ℂ) (r : Matrix (Fin 1) ι ℂ)
    (c : Matrix ι (Fin 1) ℂ) (D : Matrix ι ι ℂ)
    (hU : IsUnitary (fromBlocks (scalar (Fin 1) a) r c D)) (ha : Complex.normSq a < 1) :
    ∃ (v : ι → ℂ) (W : Matrix ι ι ℂ), (∑ i, star (v i) * v i = 1) ∧
      IsUnitary W ∧ ∀ z : ℂ, affineSchurTransfer a r c D z = rankOnePhase v z * W := by
  let q : ℝ := 1 - Complex.normSq a
  let t : ℂ := (Real.sqrt q : ℂ)
  let v : ι → ℂ := fun i => c i 0 / t
  let W := affineSchurTransfer a r c D 1
  have hq : 0 < q := sub_pos.mpr ha
  have hqc : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
  have htSq : t * t = (q : ℂ) := by
    dsimp only [t]
    rw [← Complex.ofReal_mul, ← pow_two, Real.sq_sqrt hq.le]
  have htStar : star t = t := by simp only [t, Complex.star_def, Complex.conj_ofReal]
  have hWa : IsUnitary W := affineSchurTransfer_unitary a r c D 1 hU ha Complex.normSq_one
  have hleft := hU.2
  have hright := hU.1
  rw [fromBlocks_conjTranspose, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_inj] at hleft hright
  have hqI : (1 : Matrix (Fin 1) (Fin 1) ℂ) -
      (Complex.normSq a : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ) =
      (q : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
    dsimp only [q]
    rw [Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul]
  have hrr : r * rᴴ = (q : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
    have h := hright.1
    rw [scalar_fin_one_eq_smul, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.one_mul, smul_smul,
      show star a * a = (Complex.normSq a : ℂ) from Complex.normSq_eq_conj_mul_self.symm] at h
    exact (eq_sub_iff_add_eq.mpr (by rwa [add_comm])).trans hqI
  have hcc : cᴴ * c = (q : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
    have h := hleft.1
    rw [scalar_fin_one_eq_smul, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.one_mul, smul_smul,
      show a * star a = (Complex.normSq a : ℂ) from Complex.mul_conj a] at h
    exact (eq_sub_iff_add_eq.mpr (by rwa [add_comm])).trans hqI
  have hrD : r * Dᴴ = (-a) • cᴴ := by
    have h := hright.2.1
    rw [scalar_fin_one_eq_smul, Matrix.smul_mul, Matrix.one_mul, add_comm] at h
    exact (eq_neg_of_add_eq_zero_left h).trans (neg_smul a cᴴ).symm
  have hnorm : ∑ i, star (c i 0) * c i 0 = (q : ℂ) := by
    have h := congrArg (fun X : Matrix (Fin 1) (Fin 1) ℂ => X 0 0) hcc
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.smul_apply,
      smul_eq_mul, Matrix.one_apply_eq, mul_one] using h
  have hv : ∑ i, star (v i) * v i = 1 := by
    calc
      _ = ∑ i, (t⁻¹ * t⁻¹) * (star (c i 0) * c i 0) := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [v, div_eq_mul_inv, star_mul', star_inv₀, htStar]
        ring
      _ = 1 := by rw [← Finset.mul_sum, hnorm, ← _root_.mul_inv_rev, htSq, inv_mul_cancel₀ hqc]
  have hP : (q : ℂ)⁻¹ • (c * cᴴ) = vecMulVec v (star ∘ v) := by
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Fin.sum_univ_one,
      Matrix.conjTranspose_apply, Matrix.vecMulVec_apply, Function.comp_apply,
      v, div_eq_mul_inv, star_mul', star_inv₀, htStar]
    rw [← htSq, _root_.mul_inv_rev]
    ring
  have hW (z : ℂ) : affineSchurTransfer a r c D z =
      D + ((z + star a) / (q : ℂ)) • (c * r) := by
    simp only [affineSchurTransfer, q, Complex.ofReal_sub, Complex.ofReal_one]
  have hrW : r * Wᴴ = cᴴ := by
    have hstar : star ((1 + star a) / (q : ℂ)) = (1 + a) / (q : ℂ) := by
      rw [star_div₀, star_add, star_one, star_star, show star (q : ℂ) = q from Complex.conj_ofReal q]
    change r * (affineSchurTransfer a r c D 1)ᴴ = cᴴ
    rw [hW, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
      Matrix.mul_add, Matrix.mul_smul, ← Matrix.mul_assoc r rᴴ cᴴ, hrD, hrr, hstar,
      Matrix.smul_mul, Matrix.one_mul, smul_smul, div_mul_cancel₀ _ hqc, ← add_smul,
      show -a + (1 + a) = 1 by ring, one_smul]
  refine ⟨v, W, hv, hWa, fun z => ?_⟩
  have hsplit : affineSchurTransfer a r c D z = W + ((z - 1) / (q : ℂ)) • (c * r) := by
    change affineSchurTransfer a r c D z =
      affineSchurTransfer a r c D 1 + ((z - 1) / (q : ℂ)) • (c * r)
    rw [hW z, hW 1, add_assoc, ← add_smul,
      show (z + star a) / (q : ℂ) = (1 + star a) / (q : ℂ) + (z - 1) / (q : ℂ) by ring]
  have hphase : affineSchurTransfer a r c D z * Wᴴ = rankOnePhase v z := by
    rw [hsplit, Matrix.add_mul, hWa.1, Matrix.smul_mul, Matrix.mul_assoc c r Wᴴ,
      hrW, rankOnePhase, ← hP, smul_smul, div_eq_mul_inv]
  calc
    _ = (affineSchurTransfer a r c D z * Wᴴ) * W := by
      rw [Matrix.mul_assoc, hWa.2, Matrix.mul_one]
    _ = _ := by rw [hphase]

/-- A matrix with positive rank-at-most-one Gram defect is unitary or has
one rank-one phase factor of modulus strictly below one. -/
theorem rankOneDefect_unitary_or_rankOnePhase {n : ℕ} (V : Matrix (Fin n) (Fin n) ℂ)
    (hV : (1 - Vᴴ * V).PosSemidef) (hr : (1 - Vᴴ * V).rank ≤ 1) :
    IsUnitary V ∨ ∃ (v : Fin n → ℂ) (z : ℂ) (W : Matrix (Fin n) (Fin n) ℂ),
      (∑ i, star (v i) * v i = 1) ∧ ‖z‖ < 1 ∧ IsUnitary W ∧ V = rankOnePhase v z * W := by
  obtain ⟨hV', hr'⟩ := (rank_one_defect_left_iff_right V).mp ⟨hV, hr⟩
  obtain ⟨u, hu⟩ := right_defect_column hV' hr'
  obtain ⟨U, hU, htail⟩ := exists_unitary_retained_rows (defectFrame V u) hu 0
  let e : (Fin 1 ⊕ Fin n) ≃ Fin (n + 1) :=
    (Equiv.sumCongr (Equiv.ofUnique (Fin 1) Unit) (Equiv.refl (Fin n))).trans
      ((Equiv.sumComm Unit (Fin n)).trans
        ((Equiv.optionEquivSumPUnit (Fin n)).symm.trans
          (finSuccEquiv' (0 : Fin (n + 1))).symm))
  have he0 (i : Fin 1) : e (.inl i) = 0 := by simp [e]
  have he1 (i : Fin n) : e (.inr i) = i.succ := by simp [e]
  let α := U 0 0
  let r : Matrix (Fin 1) (Fin n) ℂ := Matrix.of fun _ j => U 0 j.succ
  let c : Matrix (Fin n) (Fin 1) ℂ := Matrix.of fun i _ => U i.succ 0
  have hsub (i j : Fin n) : U i.succ j.succ = V i j := by
    have h := congrArg (fun Y : Matrix (Fin n) (Fin (n + 1)) ℂ => Y i j.succ) htail
    simpa only [Matrix.submatrix_apply, Fin.succAbove_zero, id_eq, defectFrame,
      Matrix.of_apply, Fin.cons_succ] using h
  have hblock : U.submatrix e e = fromBlocks (scalar (Fin 1) α) r c V := by
    ext (i | i) (j | j)
    · have h : i = j := Subsingleton.elim _ _
      simp [he0, α, h, scalar_apply]
    · simp [he0, he1, r]
    · simp [he0, he1, c]
    · simp [he1, hsub]
  have hW : IsUnitary (fromBlocks (scalar (Fin 1) α) r c V) :=
    hblock ▸ unitary_reindex e e hU
  have hnorm : Complex.normSq α ≤ 1 := by
    have hsum := sum_col_of_mem_doublyStochastic (normSq_transpose_doublyStochastic U hU) 0
    change (∑ i, Complex.normSq (U 0 i)) = 1 at hsum
    rw [← hsum]
    exact Finset.single_le_sum (fun j _ => Complex.normSq_nonneg (U 0 j)) (Finset.mem_univ 0)
  by_cases hα : Complex.normSq α < 1
  · obtain ⟨v, W, hv, hW', heq⟩ := affineSchurTransfer_rankOnePhase α r c V hW hα
    refine Or.inr ⟨v, -star α, W, hv, ?_, hW', ?_⟩
    · rw [norm_neg, Complex.star_def, Complex.norm_conj]
      exact (sq_lt_sq₀ (norm_nonneg _) zero_le_one).mp
        (by simpa only [Complex.normSq_eq_norm_sq, one_pow] using hα)
    · simpa only [affineSchurTransfer, neg_add_cancel, zero_div, zero_smul, add_zero] using heq (-star α)
  · have hn : ‖α‖ = 1 := (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
      (by simpa [Complex.normSq_eq_norm_sq] using hnorm.antisymm (le_of_not_gt hα))
    exact Or.inl (schurTransfer_boundary α r c V hW hn).2.2

end

end MOC
