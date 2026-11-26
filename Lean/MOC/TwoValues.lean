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

/-- Complementary zero-one spectra realize the indicator of a subset image. -/
theorem matchingProduct_subset_marker (I J : Finset ι) (hc : I.card = J.card)
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

omit [Fintype ι] in
/-- A scalar of modulus one leaves every squared minor unchanged. -/
theorem subsetMinorSq_smul_of_normSq_eq_one (U : Matrix ι ι ℂ) (z : ℂ)
    (hz : Complex.normSq z = 1) (I J : Finset ι) :
    subsetMinorSq (z • U) I J = subsetMinorSq U I J := by
  by_cases hc : I.card = J.card
  · simp only [subsetMinorSq, dif_pos hc]
    let e : I ≃ J := Fintype.equivOfCardEq (by simpa using hc)
    let M := U.submatrix (fun i : I => (i : ι)) (fun i : I => ((e i : J) : ι))
    change Complex.normSq (z • M).det = Complex.normSq M.det
    rw [Matrix.det_smul, map_mul, map_pow, hz, one_pow, one_mul]
  · simp only [subsetMinorSq, dif_neg hc]

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

/-- A unitary squared minor may be computed in any common finite index type for
its row and column selections. -/
theorem subsetMinorSq_eq_normSq_det_submatrix {κ : Type*} [Fintype κ] [DecidableEq κ]
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) (I J : Finset ι) (e : κ ≃ I) (f : κ ≃ J) :
    subsetMinorSq U I J = Complex.normSq (U.submatrix (Subtype.val ∘ e) (Subtype.val ∘ f)).det := by
  have h := sum_signedWeight_image_eq_minor U hU I J (e.symm.trans f)
  rw [sum_signedWeight_image_eq_subsetMinorSq U hU I J] at h
  let A := U.submatrix (fun i : I => (i : ι)) (fun i : I => (((e.symm.trans f) i : J) : ι))
  have hdet : A.det = (U.submatrix (Subtype.val ∘ e) (Subtype.val ∘ f)).det := by
    rw [← Matrix.det_submatrix_equiv_self e A]
    congr 1
    ext i j
    simp [A]
  apply Complex.ofReal_injective
  exact h.trans (congrArg (fun z : ℂ => (Complex.normSq z : ℂ)) hdet)

omit [Fintype ι] in
theorem subsetMinorSq_nonneg (U : Matrix ι ι ℂ) (I J : Finset ι) :
    0 ≤ subsetMinorSq U I J := by
  unfold subsetMinorSq
  split_ifs
  · exact Complex.normSq_nonneg _
  · exact le_rfl

/-- An affine decomposition of projected matching gaps into subset-image
indicators evaluates at a unitary by replacing indicators with squared minors. -/
theorem gap_eq_minor_decomposition {κ : Type*} [Fintype κ]
    (a b : ι → ℂ) (η : ℂ) (H : ℝ) (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (I J : κ → Finset ι) (w : κ → ℝ)
    (hdecomp : ∀ σ : Equiv.Perm ι, (η * matchingProduct a b σ).re - H =
      ∑ k, if (J k).map σ.toEmbedding = I k then w k else 0) :
    (η * determinantValue a b U).re - H = ∑ k, w k * subsetMinorSq U (I k) (J k) := by
  have hdet : (η * determinantValue a b U).re =
      ∑ σ, realSignedWeight U σ * (η * matchingProduct a b σ).re := by
    rw [← real_signed_determinant a b U hU, Finset.mul_sum, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro σ _
    rw [mul_left_comm η, Complex.re_ofReal_mul]
  have hmass (k : κ) : (∑ σ : Equiv.Perm ι,
      if (J k).map σ.toEmbedding = I k then realSignedWeight U σ else 0) =
      subsetMinorSq U (I k) (J k) := by
    have hs := congrArg Complex.re (sum_signedWeight_image_eq_subsetMinorSq U hU (I k) (J k))
    simpa only [Finset.sum_filter, Complex.re_sum, apply_ite, Complex.zero_re,
      Complex.ofReal_re, realSignedWeight] using hs
  calc
    _ = ∑ σ, realSignedWeight U σ * ((η * matchingProduct a b σ).re - H) := by
      simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, sum_realSignedWeight U hU,
        one_mul, hdet]
    _ = _ := by
      simp_rw [hdecomp, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      rw [← hmass k, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ _
      split_ifs <;> simp [mul_comm]

/-- Nonnegative subset-image budgets give a support bound in every order. -/
theorem support_of_minor_gap_decomposition {κ : Type*} [Fintype κ]
    (a b : ι → ℂ) (η : ℂ) (H : ℝ) (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (I J : κ → Finset ι) (w : κ → ℝ) (hw : ∀ k, 0 ≤ w k)
    (hdecomp : ∀ σ : Equiv.Perm ι, (η * matchingProduct a b σ).re - H =
      ∑ k, if (J k).map σ.toEmbedding = I k then w k else 0) :
    H ≤ (η * determinantValue a b U).re := by
  apply sub_nonneg.mp
  rw [gap_eq_minor_decomposition a b η H U hU I J w hdecomp]
  exact Finset.sum_nonneg (fun k _ => mul_nonneg (hw k) (subsetMinorSq_nonneg U _ _))

/-- Squared minors over all possible images of a fixed subset have total mass one. -/
theorem sum_subsetMinorSq (U : Matrix ι ι ℂ) (hU : IsUnitary U) (J : Finset ι) :
    ∑ I : Finset ι, subsetMinorSq U I J = 1 := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_sum, Complex.ofReal_one]
  simp_rw [← sum_signedWeight_image_eq_subsetMinorSq U hU]
  rw [Finset.sum_fiberwise, sum_signedWeight U (det_ne_zero_of_unitary hU)]

/-- Expanding each selected second-spectrum factor records its image under the matching. -/
theorem matchingProduct_expand_subsets (a b : ι → ℂ) (σ : Equiv.Perm ι) :
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

/-- For a fixed unitary matrix and a fixed two-value partition of the second
list, one probability law works for every choice of both spectra. -/
theorem exists_two_values_matching_law (J : Finset ι) (U : Matrix ι ι ℂ)
    (hU : IsUnitary U) :
    ∃ w : Equiv.Perm ι → ℝ, (∀ σ, 0 ≤ w σ) ∧ (∑ σ, w σ) = 1 ∧
      ∀ (a : ι → ℂ) (c d : ℂ),
        determinantValue a (fun j => if j ∈ J then c else d) U =
          ∑ σ, (w σ : ℂ) * matchingProduct a (fun j => if j ∈ J then c else d) σ := by
  classical
  let g (σ : Equiv.Perm ι) := J.map σ.toEmbedding
  let T := (univ : Finset (Equiv.Perm ι)).image g
  have hmap (σ : Equiv.Perm ι) (_ : σ ∈ univ) : g σ ∈ T :=
    Finset.mem_image_of_mem g (mem_univ σ)
  have hrep' (I : Finset ι) : ∃ σ, I ∈ T → g σ = I := by
    by_cases hI : I ∈ T
    · obtain ⟨σ, _, hσ⟩ := Finset.mem_image.mp hI
      exact ⟨σ, fun _ => hσ⟩
    · exact ⟨Equiv.refl ι, fun h => False.elim (hI h)⟩
  choose rep hrep using hrep'
  let w (σ : Equiv.Perm ι) := ∑ I ∈ T, if rep I = σ then subsetMinorSq U I J else 0
  have hw (σ : Equiv.Perm ι) : 0 ≤ w σ :=
    Finset.sum_nonneg (fun I _ => ite_nonneg (subsetMinorSq_nonneg U I J) le_rfl)
  have hsum : ∑ σ, w σ = 1 := by
    unfold w
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    apply Complex.ofReal_injective
    rw [Complex.ofReal_sum, Complex.ofReal_one]
    simp_rw [← sum_signedWeight_image_eq_subsetMinorSq U hU]
    rw [Finset.sum_fiberwise_of_maps_to hmap, sum_signedWeight U (det_ne_zero_of_unitary hU)]
  refine ⟨w, hw, hsum, ?_⟩
  intro a c d
  let b (j : ι) := if j ∈ J then c else d
  let v (I : Finset ι) := ∏ i, (a i + if i ∈ I then c else d)
  have hv (σ : Equiv.Perm ι) : matchingProduct a b σ = v (g σ) := by
    unfold matchingProduct v
    rw [← Equiv.prod_comp σ (fun i => a i + if i ∈ g σ then c else d)]
    simp [b, g, Finset.mem_map_equiv]
  change determinantValue a b U = ∑ σ, (w σ : ℂ) * matchingProduct a b σ
  calc
    _ = ∑ σ, signedWeight U σ * v (g σ) := by
      simpa only [hv] using (signed_determinant a b U hU).symm
    _ = ∑ I ∈ T, (subsetMinorSq U I J : ℂ) * v I := by
      rw [← Finset.sum_fiberwise_of_maps_to hmap]
      apply Finset.sum_congr rfl
      intro I _
      rw [← sum_signedWeight_image_eq_subsetMinorSq U hU, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro σ hσ
      rw [(Finset.mem_filter.mp hσ).2]
    _ = _ := by
      simp only [w, Complex.ofReal_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro I hI
      simp only [apply_ite Complex.ofReal, Complex.ofReal_zero, ite_mul, zero_mul,
        Finset.sum_ite_eq, Finset.mem_univ, if_true, hv, hrep I hI]

/-- A two-valued second spectrum needs only the image of one subset under the permutation. -/
theorem holds_two_values (a : ι → ℂ) (J : Finset ι) (c d : ℂ)
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) :
    Holds a (fun j => if j ∈ J then c else d) U := by
  obtain ⟨w, hw, hs, hd⟩ := exists_two_values_matching_law J U hU
  exact holds_of_weights w hw hs (hd a c d).symm

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
