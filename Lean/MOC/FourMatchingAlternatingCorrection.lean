import MOC.OrthogonalPrincipalMinorComplement
import MOC.ContactCensus
import Mathlib.Tactic.FinCases
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-! The explicit alternating correction for matching moments of order four. -/

open Matrix BigOperators
open scoped symmDiff

namespace MOC

private abbrev FourReal := Matrix (Fin 4) (Fin 4) ℝ

def secondMinor (A : FourReal) (a b i j : Fin 4) : ℝ :=
  A a i * A b j - A a j * A b i

def principalPair (A : FourReal) (a b : Fin 4) : ℝ := secondMinor A a b a b

private theorem principalPair_comm (A : FourReal) (a b : Fin 4) :
    principalPair A a b = principalPair A b a := by
  unfold principalPair secondMinor
  ring

theorem principalRowDet_singleton (A : FourReal) (a : Fin 4) :
    principalRowDet A {a} = A a a := by
  letI : Unique (↥({a} : Finset (Fin 4))) :=
    ⟨⟨⟨a, Finset.mem_singleton_self a⟩⟩, fun x => Subtype.ext (Finset.mem_singleton.mp x.property)⟩
  rw [principalRowDet_eq_det_submatrix, Matrix.det_unique]
  rfl

theorem principalRowDet_pair (A : FourReal) (a b : Fin 4) (h : a ≠ b) :
    principalRowDet A {a,b} = principalPair A a b := by
  let s : Finset (Fin 4) := {a,b}
  let f : Fin 2 → ↥s := ![⟨a, by simp [s]⟩, ⟨b, by simp [s]⟩]
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      have he := congrArg Subtype.val hij
      fin_cases i <;> fin_cases j <;> simp [f, h, Ne.symm h] at he ⊢
    · rintro ⟨v, hv⟩
      simp only [s, Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  let e : Fin 2 ≃ ↥s := Equiv.ofBijective f hf
  rw [principalRowDet_eq_det_submatrix, ← Matrix.det_submatrix_equiv_self e,
    Matrix.det_fin_two]
  rfl

theorem principalRowDet_three (A : FourReal) : principalRowDet A {0,1,2} =
    A 0 0 * secondMinor A 1 2 1 2 - A 0 1 * secondMinor A 1 2 0 2 +
      A 0 2 * secondMinor A 1 2 0 1 := by
  let s : Finset (Fin 4) := {0,1,2}
  let f : Fin 3 → ↥s := ![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩]
  have hf : Function.Bijective f := by decide +kernel
  let e : Fin 3 ≃ ↥s := Equiv.ofBijective f hf
  rw [principalRowDet_eq_det_submatrix, ← Matrix.det_submatrix_equiv_self e, Matrix.det_fin_three]
  change A 0 0 * A 1 1 * A 2 2 - A 0 0 * A 1 2 * A 2 1 -
    A 0 1 * A 1 0 * A 2 2 + A 0 1 * A 1 2 * A 2 0 +
      A 0 2 * A 1 0 * A 2 1 - A 0 2 * A 1 1 * A 2 0 = _
  unfold secondMinor
  ring

private def starProduct (A : FourReal) (p : Fin 4) : ℝ :=
  ∏ i : Fin 4, if i = p then 1 else principalPair A p i

private theorem starProduct_0 (A : FourReal) : starProduct A 0 =
    principalPair A 0 1 * principalPair A 0 2 * principalPair A 0 3 := by
  rw [starProduct, Fin.prod_univ_four, if_pos rfl, if_neg (by decide : (1 : Fin 4) ≠ 0),
    if_neg (by decide : (2 : Fin 4) ≠ 0),
    if_neg (by decide : (3 : Fin 4) ≠ 0)]
  simp only [one_mul, mul_one]

private theorem starProduct_1 (A : FourReal) : starProduct A 1 =
    principalPair A 1 0 * principalPair A 1 2 * principalPair A 1 3 := by
  rw [starProduct, Fin.prod_univ_four, if_pos rfl, if_neg (by decide : (0 : Fin 4) ≠ 1),
    if_neg (by decide : (2 : Fin 4) ≠ 1),
    if_neg (by decide : (3 : Fin 4) ≠ 1)]
  simp only [one_mul, mul_one]

private theorem starProduct_2 (A : FourReal) : starProduct A 2 =
    principalPair A 2 0 * principalPair A 2 1 * principalPair A 2 3 := by
  rw [starProduct, Fin.prod_univ_four, if_pos rfl, if_neg (by decide : (0 : Fin 4) ≠ 2),
    if_neg (by decide : (1 : Fin 4) ≠ 2),
    if_neg (by decide : (3 : Fin 4) ≠ 2)]
  simp only [one_mul, mul_one]

private theorem starProduct_3 (A : FourReal) : starProduct A 3 =
    principalPair A 3 0 * principalPair A 3 1 * principalPair A 3 2 := by
  rw [starProduct, Fin.prod_univ_four, if_pos rfl, if_neg (by decide : (0 : Fin 4) ≠ 3),
    if_neg (by decide : (1 : Fin 4) ≠ 3),
    if_neg (by decide : (2 : Fin 4) ≠ 3)]
  simp only [one_mul, mul_one]

private def diagonalProduct (A : FourReal) : ℝ := ∏ i, A i i

/-- The correction candidate before multiplying by the determinant. -/
def fourMatchingCorrectionCandidate (A : FourReal) : ℝ :=
  starProduct A 0 - diagonalProduct A

private theorem det_sq_of_orthogonal (A : FourReal) (hA : A * Aᵀ = 1) : A.det ^ 2 = 1 := by
  simpa only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one, pow_two] using
    congrArg Matrix.det hA

private theorem starProduct_eq (A : FourReal) (hA : A * Aᵀ = 1) (p : Fin 4) :
    starProduct A p = starProduct A 0 := by
  have h12 := principalRowDet_compl A hA ({0,3} : Finset (Fin 4))
  have h13 := principalRowDet_compl A hA ({0,2} : Finset (Fin 4))
  have h23 := principalRowDet_compl A hA ({0,1} : Finset (Fin 4))
  have hc12 : ({0,3} : Finset (Fin 4))ᶜ = {1,2} := by decide
  have hc13 : ({0,2} : Finset (Fin 4))ᶜ = {1,3} := by decide
  have hc23 : ({0,1} : Finset (Fin 4))ᶜ = {2,3} := by decide
  rw [hc12, principalRowDet_pair A 1 2 (by decide), principalRowDet_pair A 0 3 (by decide)] at h12
  rw [hc13, principalRowDet_pair A 1 3 (by decide), principalRowDet_pair A 0 2 (by decide)] at h13
  rw [hc23, principalRowDet_pair A 2 3 (by decide), principalRowDet_pair A 0 1 (by decide)] at h23
  have hd := det_sq_of_orthogonal A hA
  fin_cases p
  · rfl
  · change starProduct A (1 : Fin 4) = _
    rw [starProduct_1, starProduct_0, principalPair_comm A 1 0, h12, h13]
    linear_combination principalPair A 0 1 * principalPair A 0 2 * principalPair A 0 3 * hd
  · change starProduct A (2 : Fin 4) = _
    rw [starProduct_2, starProduct_0, principalPair_comm A 2 0,
      principalPair_comm A 2 1, h12, h23]
    linear_combination principalPair A 0 1 * principalPair A 0 2 * principalPair A 0 3 * hd
  · change starProduct A (3 : Fin 4) = _
    rw [starProduct_3, starProduct_0, principalPair_comm A 3 0,
      principalPair_comm A 3 1, principalPair_comm A 3 2, h13, h23]
    linear_combination principalPair A 0 1 * principalPair A 0 2 * principalPair A 0 3 * hd

private theorem principalPair_column_swap (A : FourReal) (hA : A * Aᵀ = 1) :
    fourMatchingCorrectionCandidate (A.submatrix id (Equiv.swap 1 2)) =
      fourMatchingCorrectionCandidate A := by
  let B := A.submatrix id (Equiv.swap 1 2)
  have hthree := principalRowDet_compl A hA ({3} : Finset (Fin 4))
  have hc : ({3} : Finset (Fin 4))ᶜ = {0,1,2} := by decide
  rw [hc, principalRowDet_three, principalRowDet_singleton] at hthree
  have hpair := principalRowDet_compl A hA ({1,2} : Finset (Fin 4))
  have hc' : ({1,2} : Finset (Fin 4))ᶜ = {0,3} := by decide
  rw [hc', principalRowDet_pair A 0 3 (by decide), principalRowDet_pair A 1 2 (by decide)] at hpair
  have hDJ : principalPair A 0 1 * principalPair A 0 2 -
      secondMinor A 0 1 0 2 * secondMinor A 0 2 0 1 = A 0 0 * (A.det * A 3 3) := by
    rw [← hthree]
    simp only [principalPair, secondMinor]
    ring
  change starProduct B 0 - diagonalProduct B = starProduct A 0 - diagonalProduct A
  have h₀ : Equiv.swap (1 : Fin 4) 2 0 = 0 := by decide
  have h₁ : Equiv.swap (1 : Fin 4) 2 1 = 2 := by decide
  have h₂ : Equiv.swap (1 : Fin 4) 2 2 = 1 := by decide
  have h₃ : Equiv.swap (1 : Fin 4) 2 3 = 3 := by decide
  rw [starProduct_0, starProduct_0]
  simp only [diagonalProduct, Fin.prod_univ_four, B, principalPair, secondMinor,
    Matrix.submatrix_apply, id_eq, h₀, h₁, h₂, h₃] at hDJ ⊢
  simp only [principalPair, secondMinor] at hpair
  have hd := det_sq_of_orthogonal A hA
  linear_combination -((A 0 0 * A 3 3 - A 0 3 * A 3 0) * hDJ +
    (A 0 0 * A.det * A 3 3) * hpair +
    (A 0 0 * A 3 3 * (A 1 1 * A 2 2 - A 1 2 * A 2 1)) * hd)

theorem submatrix_mul_transpose_of_orthogonal (A : FourReal) (hA : A * Aᵀ = 1)
    (r c : Equiv.Perm (Fin 4)) : (A.submatrix r c) * (A.submatrix r c)ᵀ = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply]
  rw [Equiv.sum_comp c (fun k => A (r i) k * A (r j) k)]
  change (A * Aᵀ) (r i) (r j) = _
  rw [hA]
  simp only [Matrix.one_apply, r.injective.eq_iff]

private theorem candidate_relabel (A : FourReal) (hA : A * Aᵀ = 1)
    (e : Equiv.Perm (Fin 4)) :
    fourMatchingCorrectionCandidate (A.submatrix e e) = fourMatchingCorrectionCandidate A := by
  have hs : starProduct (A.submatrix e e) 0 = starProduct A (e 0) := by
    unfold starProduct
    simpa only [principalPair, secondMinor, Matrix.submatrix_apply, e.injective.eq_iff] using
      Equiv.prod_comp e (fun j => if j = e 0 then 1 else principalPair A (e 0) j)
  have hd : diagonalProduct (A.submatrix e e) = diagonalProduct A := by
    unfold diagonalProduct
    exact Equiv.prod_comp e (fun j => A j j)
  unfold fourMatchingCorrectionCandidate
  rw [hs, hd, starProduct_eq A hA]

private theorem find_transposition_labels : ∀ a b : Fin 4, a ≠ b →
    ∃ k : Fin 24, fourPerm k 1 = a ∧ fourPerm k 2 = b := by decide +kernel

private theorem candidate_transposition (A : FourReal) (hA : A * Aᵀ = 1)
    (a b : Fin 4) (hab : a ≠ b) :
    fourMatchingCorrectionCandidate (A.submatrix id (Equiv.swap a b)) =
      fourMatchingCorrectionCandidate A := by
  obtain ⟨k, h₁, h₂⟩ := find_transposition_labels a b hab
  let e := fourPerm k
  change e 1 = a at h₁
  change e 2 = b at h₂
  have hcomm (j : Fin 4) : Equiv.swap a b (e j) = e (Equiv.swap 1 2 j) := by
    rw [← h₁, ← h₂]
    simp only [Equiv.swap_apply_def, e.injective.eq_iff]
    split_ifs <;> rfl
  have hind : ((A.submatrix id (Equiv.swap a b)).submatrix e e) =
      ((A.submatrix e e).submatrix id (Equiv.swap 1 2)) := by
    ext i j
    simp only [Matrix.submatrix_apply, id_eq, hcomm]
  have hA' : (A.submatrix id (Equiv.swap a b)) * (A.submatrix id (Equiv.swap a b))ᵀ = 1 :=
    submatrix_mul_transpose_of_orthogonal A hA 1 (Equiv.swap a b)
  rw [← candidate_relabel _ hA' e, ← candidate_relabel A hA e, hind]
  exact principalPair_column_swap _ (submatrix_mul_transpose_of_orthogonal A hA e e)

/-- The correction candidate is invariant under relabelling the columns. -/
theorem fourMatchingCorrectionCandidate_permute (A : FourReal) (hA : A * Aᵀ = 1)
    (σ : Equiv.Perm (Fin 4)) :
    fourMatchingCorrectionCandidate (A.submatrix id σ) = fourMatchingCorrectionCandidate A := by
  refine σ.swap_induction_on' (by simp) ?_
  intro σ a b hab hσ
  change fourMatchingCorrectionCandidate ((A.submatrix id σ).submatrix id (Equiv.swap a b)) = _
  have hA' : (A.submatrix id σ) * (A.submatrix id σ)ᵀ = 1 :=
    submatrix_mul_transpose_of_orthogonal A hA 1 σ
  exact (candidate_transposition _ hA' a b hab).trans hσ

theorem principalRowDet_empty (A : FourReal) : principalRowDet A ∅ = 1 := by
  rw [principalRowDet_eq_det_submatrix]
  exact Matrix.det_isEmpty

/-- The product of principal minors indexed by the two sets and their symmetric difference. -/
def fourPrincipalGram (A : FourReal) (I K : Finset (Fin 4)) : ℝ :=
  principalRowDet A I * principalRowDet A K * principalRowDet A (I ∆ K)

/-- The product of principal minors of the four cells cut out by two subsets. -/
def fourPrincipalCellProduct (A : FourReal) (I K : Finset (Fin 4)) : ℝ :=
  principalRowDet A (I ∩ K) * principalRowDet A (I \ K) *
    principalRowDet A (K \ I) * principalRowDet A ((I ∪ K)ᶜ)

private theorem principalGram_compl_left (A : FourReal) (hA : A * Aᵀ = 1)
    (I K : Finset (Fin 4)) : fourPrincipalGram A Iᶜ K = fourPrincipalGram A I K := by
  have h : Iᶜ ∆ K = (I ∆ K)ᶜ := by
    ext i
    simp only [Finset.mem_symmDiff, Finset.mem_compl]
    tauto
  unfold fourPrincipalGram
  rw [h, principalRowDet_compl A hA I, principalRowDet_compl A hA (I ∆ K)]
  linear_combination principalRowDet A I * principalRowDet A K * principalRowDet A (I ∆ K) *
    det_sq_of_orthogonal A hA

theorem principalGram_comm (A : FourReal) (I K : Finset (Fin 4)) :
    fourPrincipalGram A I K = fourPrincipalGram A K I := by
  simp only [fourPrincipalGram, symmDiff_comm I K, mul_comm (principalRowDet A I)]

private theorem principalCellProduct_compl_left (A : FourReal) (I K : Finset (Fin 4)) :
    fourPrincipalCellProduct A Iᶜ K = fourPrincipalCellProduct A I K := by
  have h₁ : Iᶜ ∩ K = K \ I := by
    ext i
    simp only [Finset.mem_inter, Finset.mem_compl, Finset.mem_sdiff, and_comm]
  have h₂ : Iᶜ \ K = (I ∪ K)ᶜ := by
    ext i
    simp only [Finset.mem_union, Finset.mem_compl, Finset.mem_sdiff]
    tauto
  have h₃ : K \ Iᶜ = I ∩ K := by
    ext i
    simp [and_comm]
  have h₄ : (Iᶜ ∪ K)ᶜ = I \ K := by
    ext i
    simp only [Finset.mem_union, Finset.mem_compl, Finset.mem_sdiff]
    tauto
  rw [fourPrincipalCellProduct, fourPrincipalCellProduct, h₁, h₂, h₃, h₄]
  ring

theorem principalCellProduct_comm (A : FourReal) (I K : Finset (Fin 4)) :
    fourPrincipalCellProduct A I K = fourPrincipalCellProduct A K I := by
  rw [fourPrincipalCellProduct, fourPrincipalCellProduct, Finset.inter_comm I K,
    Finset.union_comm I K]
  ring

private theorem principalGram_eq_cellProduct_of_disjoint (A : FourReal) (hA : A * Aᵀ = 1)
    {I K : Finset (Fin 4)} (h : Disjoint I K) :
    fourPrincipalGram A I K = A.det * fourPrincipalCellProduct A I K := by
  have hS : I ∆ K = I ∪ K := by
    rw [symmDiff, h.sdiff_eq_left, h.symm.sdiff_eq_left]
    rfl
  rw [fourPrincipalGram, hS, fourPrincipalCellProduct, Finset.disjoint_iff_inter_eq_empty.mp h,
    h.sdiff_eq_left, h.symm.sdiff_eq_left, principalRowDet_empty, one_mul,
    principalRowDet_compl A hA (I ∪ K)]
  linear_combination -principalRowDet A I * principalRowDet A K * principalRowDet A (I ∪ K) *
    det_sq_of_orthogonal A hA

/-- An empty cell makes the principal Gram entry equal to the determinant
of the orthogonal matrix times the principal block product. -/
theorem fourPrincipalGram_eq_cellProduct_of_empty (A : FourReal) (hA : A * Aᵀ = 1)
    (I K : Finset (Fin 4))
    (h : I ∩ K = ∅ ∨ I \ K = ∅ ∨ K \ I = ∅ ∨ (I ∪ K)ᶜ = ∅) :
    fourPrincipalGram A I K = A.det * fourPrincipalCellProduct A I K := by
  rcases h with h | h | h | h
  · exact principalGram_eq_cellProduct_of_disjoint A hA (Finset.disjoint_iff_inter_eq_empty.mpr h)
  · rw [principalGram_comm A I K, principalCellProduct_comm A I K,
      ← principalGram_compl_left A hA K I, ← principalCellProduct_compl_left A K I]
    have he : Kᶜ ∩ I = I \ K := by ext i; simp [and_comm]
    exact principalGram_eq_cellProduct_of_disjoint A hA
      (Finset.disjoint_iff_inter_eq_empty.mpr (he.trans h))
  · rw [← principalGram_compl_left A hA I K, ← principalCellProduct_compl_left A I K]
    have he : Iᶜ ∩ K = K \ I := by ext i; simp [and_comm]
    exact principalGram_eq_cellProduct_of_disjoint A hA
      (Finset.disjoint_iff_inter_eq_empty.mpr (he.trans h))
  · rw [← principalGram_compl_left A hA I K, ← principalCellProduct_compl_left A I K,
      principalGram_comm A Iᶜ K, principalCellProduct_comm A Iᶜ K,
      ← principalGram_compl_left A hA K Iᶜ, ← principalCellProduct_compl_left A K Iᶜ]
    have he : Kᶜ ∩ Iᶜ = (I ∪ K)ᶜ := by
      ext i
      simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_compl]
      tauto
    exact principalGram_eq_cellProduct_of_disjoint A hA
      (Finset.disjoint_iff_inter_eq_empty.mpr (he.trans h))

/-- For the two crossing pairs used in the indicator basis, the difference
of the Gram entry and the signed principal block product is the correction. -/
theorem fourPrincipalGram_crossing (A : FourReal) (hA : A * Aᵀ = 1) :
    fourPrincipalGram A {0,1} {0,2} =
      A.det * (fourPrincipalCellProduct A {0,1} {0,2} + fourMatchingCorrectionCandidate A) := by
  have h₁ : ({0,1} : Finset (Fin 4)) ∆ {0,2} = {1,2} := by decide
  have h₂ : ({0,1} : Finset (Fin 4)) ∩ {0,2} = {0} := by decide
  have h₃ : ({0,1} : Finset (Fin 4)) \ {0,2} = {1} := by decide
  have h₄ : ({0,2} : Finset (Fin 4)) \ {0,1} = {2} := by decide
  have h₅ : (({0,1} : Finset (Fin 4)) ∪ {0,2})ᶜ = {3} := by decide
  have hc : ({0,3} : Finset (Fin 4))ᶜ = {1,2} := by decide
  have hs := principalRowDet_compl A hA ({0,3} : Finset (Fin 4))
  rw [hc, principalRowDet_pair A 1 2 (by decide), principalRowDet_pair A 0 3 (by decide)] at hs
  rw [fourPrincipalGram, fourPrincipalCellProduct, h₁, h₂, h₃, h₄, h₅,
    principalRowDet_pair A 0 1 (by decide), principalRowDet_pair A 0 2 (by decide),
    principalRowDet_pair A 1 2 (by decide), hs]
  simp only [principalRowDet_singleton, fourMatchingCorrectionCandidate]
  rw [starProduct_0]
  simp only [diagonalProduct, Fin.prod_univ_four]
  ring

end MOC
