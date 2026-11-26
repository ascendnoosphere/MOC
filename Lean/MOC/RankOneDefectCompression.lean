import MOC.PrincipalCoisometry
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
      exact hk (congrArg Subtype.val (Subsingleton.elim ⟨k, hne⟩ ⟨j, hj⟩ :
        (⟨k, hne⟩ : {i // eig i ≠ 0}) = ⟨j, hj⟩))
    have ht : t * star t = (eig j : ℂ) := by
      simp only [t, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
        ← pow_two, Real.sq_sqrt (hH.eigenvalues_nonneg j)]
    refine ⟨u, ?_⟩
    rw [hH']
    ext i k
    simp only [Matrix.mul_apply _ Wᴴ, Matrix.mul_diagonal, Matrix.conjTranspose_apply]
    rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ j)]
    · simp only [u, Matrix.mul_apply, Fintype.sum_unique, Matrix.of_apply, star_mul']
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
  simp only [Matrix.mul_apply _ (defectFrame V u)ᴴ, Matrix.mul_apply _ Vᴴ,
    Matrix.mul_diagonal, Matrix.conjTranspose_apply, Fin.sum_univ_succ, defectFrame,
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
    have hβ (j : Fin (n + 1)) : β j = c + Fin.cons 0 b j := by
      refine Fin.cases ?_ (fun j => ?_) j
      · simp only [c, Fin.cons_zero, add_zero]
      · simp only [b, Fin.cons_succ]
        ring
    have hmat {k : ℕ} (x : Fin k → ℂ) :
        diagonal (fun i => c + x i) = c • (1 : Matrix (Fin k) (Fin k) ℂ) + diagonal x := by
      ext i j
      by_cases hij : i = j <;> simp [Matrix.diagonal_apply, Matrix.one_apply, hij]
    have hcomp : diagonal a + Y * diagonal β * Yᴴ = diagonal a' + V * diagonal b * Vᴴ := by
      rw [show β = fun j => c + Fin.cons 0 b j from funext hβ, hmat, Matrix.mul_add,
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

end

end MOC
