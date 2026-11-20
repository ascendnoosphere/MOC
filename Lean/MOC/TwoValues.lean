import MOC.Weights
import Mathlib.Data.Complex.Order
import Mathlib.LinearAlgebra.Matrix.Block

/-! Squared minors are the exact subset-image marginals of the signed determinant law.
A single subset-image law suffices when either spectrum takes at most two values. -/

open BigOperators Matrix Finset
open scoped ComplexOrder

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem matchingProduct_subset_marker (I J : Finset ι) (hc : I.card = J.card)
    (σ : Equiv.Perm ι) :
    matchingProduct (fun i => if i ∈ I then 0 else 1) (fun j => if j ∈ J then 1 else 0) σ =
      if J.map σ.toEmbedding = I then 1 else 0 := by
  classical
  by_cases h : J.map σ.toEmbedding = I
  · rw [if_pos h]
    unfold matchingProduct
    apply Finset.prod_eq_one
    intro j _
    have hm : σ j ∈ I ↔ j ∈ J := by rw [← h, Finset.mem_map_equiv, Equiv.symm_apply_apply]
    by_cases hj : j ∈ J <;> simp [hj, hm]
  · rw [if_neg h]
    have hns : ¬ I ⊆ J.map σ.toEmbedding := by
      intro hs
      exact h (Finset.eq_of_subset_of_card_le hs (by rw [Finset.card_map, hc])).symm
    obtain ⟨i, hi, hni⟩ := Finset.not_subset.mp hns
    unfold matchingProduct
    apply Finset.prod_eq_zero (Finset.mem_univ (σ.symm i))
    have hj : σ.symm i ∉ J := by rwa [Finset.mem_map_equiv] at hni
    simp [hi, hj]

private theorem sum_signedWeight_image_eq_marker_det (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (I J : Finset ι) (hc : I.card = J.card) :
    (∑ σ ∈ univ.filter (fun σ : Equiv.Perm ι => J.map σ.toEmbedding = I), signedWeight U σ) =
      determinantValue (fun i => if i ∈ I then 0 else 1) (fun j => if j ∈ J then 1 else 0) U := by
  classical
  rw [← signed_determinant _ _ U hU, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro σ _
  rw [matchingProduct_subset_marker I J hc σ]
  split_ifs <;> simp

/-- The signed mass on a subset image equals the squared modulus of the corresponding minor. -/
theorem sum_signedWeight_image_eq_minor (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (I J : Finset ι) (e : I ≃ J) :
    (∑ σ ∈ univ.filter (fun σ : Equiv.Perm ι => J.map σ.toEmbedding = I), signedWeight U σ) =
      (Complex.normSq (U.submatrix (fun i : I => (i : ι)) (fun i : I => ((e i : J) : ι))).det : ℂ) := by
  classical
  have hc : I.card = J.card := by simpa using Fintype.card_congr e
  rw [sum_signedWeight_image_eq_marker_det U hU I J hc]
  let p (i : ι) : ℂ := if i ∈ I then 0 else 1
  let q (i : ι) : ℂ := if i ∈ J then 1 else 0
  let X : Matrix ι ι ℂ := Matrix.of fun i j =>
    if hj : j ∈ I then U i (e ⟨j, hj⟩) else (1 : Matrix ι ι ℂ) i j
  let D := diagonal p
  have hIdem : D * Dᴴ = D := by
    unfold D
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    apply congrArg Matrix.diagonal
    funext j
    by_cases hj : j ∈ I <;> simp [p, hj]
  have hsel (i k : ι) : (∑ j ∈ I, X i j * star (X k j)) =
      ∑ j ∈ J, U i j * star (U k j) := by
    rw [← Finset.sum_coe_sort I, ← Finset.sum_coe_sort J]
    rw [← Equiv.sum_comp e (fun j : J => U i j * star (U k j))]
    apply Finset.sum_congr rfl
    intro j _
    simp [X, j.property]
  have hUU (i k : ι) : (U * diagonal q * Uᴴ) i k =
      ∑ j ∈ J, U i j * star (U k j) := by
    have hf : univ.filter (fun j => j ∈ J) = J := by ext j; simp
    rw [Matrix.mul_apply, ← hf, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : j ∈ J <;> simp [q, h, Matrix.mul_diagonal, Matrix.conjTranspose_apply]
  have hGram : X * Xᴴ = D + U * diagonal q * Uᴴ := by
    ext i k : 1
    rw [Matrix.add_apply, hUU, ← hsel, ← hIdem, Matrix.mul_apply, Matrix.mul_apply]
    simp only [Matrix.conjTranspose_apply]
    have hf : univ.filter (fun j => j ∈ I) = I := by ext j; simp
    rw [← hf, Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j ∈ I
    · have hz (r : ι) : D r j = 0 := by
        by_cases h : r = j <;> simp [D, p, Matrix.diagonal_apply, h, hj]
      simp [hj, hz]
    · have hid (r : ι) : X r j = D r j := by
        by_cases h : r = j <;> simp [X, D, p, Matrix.diagonal_apply, Matrix.one_apply, h, hj]
      simp [hj, hid]
  let K := {j : ι // j ∉ I}
  let f : I ⊕ K ≃ ι := Equiv.sumCompl (fun j => j ∈ I)
  let N := U.submatrix (fun i : I => (i : ι)) (fun i : I => ((e i : J) : ι))
  let Q := U.submatrix (fun i : K => (i : ι)) (fun i : I => ((e i : J) : ι))
  have hBlock : X.submatrix f f = Matrix.fromBlocks N 0 Q 1 := by
    ext (i | i) (j | j) : 1
    · change X i j = N i j
      simp [X, N, j.property, Matrix.submatrix_apply]
    · change X i j = 0
      have h : (i : ι) ≠ (j : ι) := fun hj => j.property (hj ▸ i.property)
      simp [X, j.property, h, Matrix.one_apply]
    · change X i j = Q i j
      simp [X, Q, j.property, Matrix.submatrix_apply]
    · change X i j = (1 : Matrix K K ℂ) i j
      by_cases h : i = j
      · subst j
        simp [X, i.property]
      · have h' : (i : ι) ≠ (j : ι) := fun h' => h (Subtype.ext h')
        simp [X, j.property, Matrix.one_apply, h, h']
  have hdet : X.det = N.det := by
    rw [← Matrix.det_submatrix_equiv_self f X, hBlock, Matrix.det_fromBlocks_zero₁₂,
      Matrix.det_one, mul_one]
  change (D + U * diagonal q * Uᴴ).det = (Complex.normSq N.det : ℂ)
  rw [← hGram, Matrix.det_mul, Matrix.det_conjTranspose, hdet]
  exact Complex.mul_conj N.det

/-- The signed mass of the permutations taking the second subset to the first is nonnegative. -/
theorem sum_signedWeight_image_nonneg (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (I J : Finset ι) (hc : I.card = J.card) :
    0 ≤ ∑ σ ∈ univ.filter (fun σ : Equiv.Perm ι => J.map σ.toEmbedding = I), signedWeight U σ := by
  classical
  let e : I ≃ J := Fintype.equivOfCardEq (by simpa using hc)
  rw [sum_signedWeight_image_eq_minor U hU I J e, Complex.zero_le_real]
  exact Complex.normSq_nonneg _

/-- The squared minor associated to two finite subsets, with value zero for unequal sizes. -/
def subsetMinorSq (U : Matrix ι ι ℂ) (I J : Finset ι) : ℝ :=
  if h : I.card = J.card then
    let e : I ≃ J := Fintype.equivOfCardEq (by simpa using h)
    Complex.normSq (U.submatrix (fun i : I => (i : ι)) (fun i : I => ((e i : J) : ι))).det
  else 0

theorem sum_signedWeight_image_eq_subsetMinorSq (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (I J : Finset ι) :
    (∑ σ ∈ univ.filter (fun σ : Equiv.Perm ι => J.map σ.toEmbedding = I), signedWeight U σ) =
      (subsetMinorSq U I J : ℂ) := by
  classical
  by_cases hc : I.card = J.card
  · simp only [subsetMinorSq, dif_pos hc]
    exact sum_signedWeight_image_eq_minor U hU I J (Fintype.equivOfCardEq (by simpa using hc))
  · have he : (univ : Finset (Equiv.Perm ι)).filter
        (fun σ => J.map σ.toEmbedding = I) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro σ _ hσ
      exact hc (by rw [← hσ, Finset.card_map])
    simp [he, subsetMinorSq, hc]

omit [Fintype ι] in
theorem subsetMinorSq_nonneg (U : Matrix ι ι ℂ) (I J : Finset ι) :
    0 ≤ subsetMinorSq U I J := by
  unfold subsetMinorSq
  split_ifs
  · exact Complex.normSq_nonneg _
  · exact le_rfl

/-- Squared minors over all possible images of a fixed subset have total mass one. -/
theorem sum_subsetMinorSq (U : Matrix ι ι ℂ) (hU : IsUnitary U) (J : Finset ι) :
    ∑ I : Finset ι, subsetMinorSq U I J = 1 := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_sum, Complex.ofReal_one]
  simp_rw [← sum_signedWeight_image_eq_subsetMinorSq U hU]
  rw [Finset.sum_fiberwise, sum_signedWeight U (det_ne_zero_of_unitary hU)]

private theorem matchingProduct_expand_subsets (a b : ι → ℂ) (σ : Equiv.Perm ι) :
    matchingProduct a b σ =
      ∑ J : Finset ι, (∏ i ∈ (J.map σ.toEmbedding)ᶜ, a i) * ∏ j ∈ J, b j := by
  calc
    matchingProduct a b σ = ∏ j, (b j + a (σ j)) := by simp [matchingProduct, add_comm]
    _ = ∑ J : Finset ι, (∏ j ∈ J, b j) * ∏ j ∈ Jᶜ, a (σ j) := Fintype.prod_add _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro J _
      have hprod : (∏ j ∈ Jᶜ, a (σ j)) = ∏ i ∈ (Jᶜ).map σ.toEmbedding, a i := by
        simpa only [Equiv.toEmbedding_apply] using (Finset.prod_map Jᶜ σ.toEmbedding a).symm
      rw [mul_comm, hprod]
      have he : (Jᶜ).map σ.toEmbedding = (J.map σ.toEmbedding)ᶜ := by
        ext i
        simp [Finset.mem_map_equiv]
      rw [he]

/-- Exact squared-minor expansion of the determinant for arbitrary complex spectra. -/
theorem determinantValue_eq_sum_subsetMinors (a b : ι → ℂ) (U : Matrix ι ι ℂ)
    (hU : IsUnitary U) :
    determinantValue a b U = ∑ J : Finset ι, ∑ I : Finset ι, (subsetMinorSq U I J : ℂ) *
      ((∏ i ∈ Iᶜ, a i) * ∏ j ∈ J, b j) := by
  classical
  rw [← signed_determinant a b U hU]
  simp_rw [matchingProduct_expand_subsets, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro J _
  rw [← Finset.sum_fiberwise univ (fun σ : Equiv.Perm ι => J.map σ.toEmbedding)]
  apply Finset.sum_congr rfl
  intro I _
  rw [← sum_signedWeight_image_eq_subsetMinorSq U hU I J, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [(Finset.mem_filter.mp hσ).2]

/-- A two-valued second spectrum needs only the image of one subset under the permutation. -/
theorem holds_two_values (a : ι → ℂ) (J : Finset ι) (c d : ℂ)
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) :
    Holds a (fun j => if j ∈ J then c else d) U := by
  classical
  let b (j : ι) := if j ∈ J then c else d
  let g (σ : Equiv.Perm ι) := J.map σ.toEmbedding
  let T := (univ : Finset (Equiv.Perm ι)).image g
  let m (I : Finset ι) := ∑ σ ∈ univ.filter (fun σ => g σ = I), signedWeight U σ
  let w (I : Finset ι) := (m I).re
  let v (I : Finset ι) := ∏ i, (a i + if i ∈ I then c else d)
  have hmap (σ : Equiv.Perm ι) (_ : σ ∈ univ) : g σ ∈ T := Finset.mem_image_of_mem g (mem_univ σ)
  have hv (σ : Equiv.Perm ι) : matchingProduct a b σ = v (g σ) := by
    unfold matchingProduct v
    rw [← Equiv.prod_comp σ (fun i => a i + if i ∈ g σ then c else d)]
    simp [b, g, Finset.mem_map_equiv]
  have hn (I : Finset ι) (hI : I ∈ T) : 0 ≤ m I := by
    obtain ⟨σ, _, rfl⟩ := Finset.mem_image.mp hI
    apply sum_signedWeight_image_nonneg U hU
    exact card_map _
  have hvtx (I : Finset ι) (hI : I ∈ T) : v I ∈ Set.range (matchingProduct a b) := by
    obtain ⟨σ, _, rfl⟩ := Finset.mem_image.mp hI
    exact ⟨σ, hv σ⟩
  have hsumC : ∑ I ∈ T, m I = 1 := by
    rw [Finset.sum_fiberwise_of_maps_to hmap, sum_signedWeight U (det_ne_zero_of_unitary hU)]
  have hsum : ∑ I ∈ T, w I = 1 := by
    simpa only [Complex.re_sum, Complex.one_re] using congrArg Complex.re hsumC
  have hdet : ∑ I ∈ T, w I • v I = determinantValue a b U := calc
    _ = ∑ I ∈ T, m I * v I := by
      apply Finset.sum_congr rfl
      intro I hI
      have he : (w I : ℂ) = m I := Complex.ext rfl (Complex.nonneg_iff.mp (hn I hI)).2
      rw [Complex.real_smul, he]
    _ = ∑ σ, signedWeight U σ * matchingProduct a b σ := by
      rw [← Finset.sum_fiberwise_of_maps_to hmap]
      apply Finset.sum_congr rfl
      intro I _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro σ hσ
      rw [hv, (Finset.mem_filter.mp hσ).2]
    _ = _ := signed_determinant a b U hU
  change determinantValue a b U ∈ convexHull ℝ (Set.range (matchingProduct a b))
  rw [← hdet, ← T.centerMass_eq_of_sum_1 v hsum]
  exact T.centerMass_mem_convexHull (fun I hI => (Complex.nonneg_iff.mp (hn I hI)).1)
    (hsum.symm ▸ zero_lt_one) hvtx

theorem holds_of_two_values (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (c d : ℂ) (hb : ∀ j, b j = c ∨ b j = d) : Holds a b U := by
  classical
  let J := (univ : Finset ι).filter (fun j => b j = c)
  have h : b = fun j => if j ∈ J then c else d := by
    funext j
    have hm : j ∈ J ↔ b j = c := by simp [J]
    by_cases hj : b j = c
    · rw [if_pos (hm.mpr hj), hj]
    · rw [if_neg (mt hm.mp hj)]
      exact (hb j).resolve_left hj
  rw [h]
  exact holds_two_values a J c d U hU

theorem holds_of_two_values_left (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (c d : ℂ) (ha : ∀ i, a i = c ∨ a i = d) : Holds a b U := by
  have hU' : IsUnitary Uᴴ := ⟨by simpa using hU.2, by simpa using hU.1⟩
  exact (holds_swap_iff a b hU).mp (holds_of_two_values b a Uᴴ hU' c d ha)

end

end MOC
