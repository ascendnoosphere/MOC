import MOC.Support
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Topology.Algebra.Polynomial

/-! A small second spectrum under generic first-order assignment data.
We use the common singleton marginals of the signed determinant law and
a Birkhoff law. Near a two-vertex assignment face, their total variation
is controlled by the Birkhoff mass outside that face. -/

open BigOperators Finset Matrix Polynomial
open scoped Topology

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private def offAssignmentFace (σ τ : Equiv.Perm ι) : Finset (Equiv.Perm ι) :=
  univ.filter fun π => π ≠ σ ∧ π ≠ τ

private theorem mem_offAssignmentFace (σ τ π : Equiv.Perm ι) :
    π ∈ offAssignmentFace σ τ ↔ π ≠ σ ∧ π ≠ τ := by
  simp [offAssignmentFace]

private theorem sum_split_twoAssignments (σ τ : Equiv.Perm ι) (hστ : σ ≠ τ)
    (f : Equiv.Perm ι → ℝ) :
    (∑ π, f π) = (∑ π ∈ offAssignmentFace σ τ, f π) + f τ + f σ := by
  have ho : offAssignmentFace σ τ = (univ.erase σ).erase τ := by
    ext π
    simp [offAssignmentFace, and_comm]
  rw [ho, sum_erase_add _ f (mem_erase.mpr ⟨Ne.symm hστ, mem_univ _⟩),
    sum_erase_add _ f (mem_univ _)]

private theorem sum_split_oneAssignment (σ : Equiv.Perm ι) (f : Equiv.Perm ι → ℝ) :
    (∑ π, f π) = (∑ π ∈ offAssignmentFace σ σ, f π) + f σ := by
  have ho : offAssignmentFace σ σ = univ.erase σ := by
    ext π
    simp [offAssignmentFace]
  rw [ho, sum_erase_add _ f (mem_univ _)]

private theorem real_birkhoff_weights (U : Matrix ι ι ℂ) (hU : IsUnitary U) :
    ∃ w : Equiv.Perm ι → ℝ, (∀ π, 0 ≤ w π) ∧ (∑ π, w π) = 1 ∧
      ∀ i j, (∑ π, if π j = i then w π else 0) = Complex.normSq (U i j) := by
  obtain ⟨w, hw, hs, hm⟩ := exists_singleton_weights U hU
  refine ⟨w, hw, hs, fun i j => ?_⟩
  simpa only [marginal, Complex.re_sum, apply_ite, Complex.zero_re, Complex.ofReal_re]
    using congrArg Complex.re (hm i j)

private theorem norm_unitary_det_eq_one (U : Matrix ι ι ℂ) (hU : IsUnitary U) :
    ‖U.det‖ = 1 := by
  have he : U.det * star U.det = 1 := by
    rw [← Matrix.det_conjTranspose, ← Matrix.det_mul, hU.1, Matrix.det_one]
  have hn := congrArg norm he
  simp only [norm_mul, Complex.star_def, Complex.norm_conj, norm_one] at hn
  have hp : 0 < ‖U.det‖ + 1 := by positivity
  have hz : (‖U.det‖ - 1) * (‖U.det‖ + 1) = 0 := by nlinarith only [hn]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right hp.ne')

private theorem realSignedWeight_abs_le_entry_product (U : Matrix ι ι ℂ)
    (hU : IsUnitary U) (π : Equiv.Perm ι) :
    |realSignedWeight U π| ≤ ∏ j, ‖U (π j) j‖ := by
  refine (Complex.abs_re_le_norm (signedWeight U π)).trans ?_
  rw [signedWeight, leibnizTerm, norm_div, norm_unitary_det_eq_one U hU, div_one,
    norm_mul, norm_prod]
  rcases Int.units_eq_one_or (Equiv.Perm.sign π) with hp | hp
  · simp [hp]
  · simp [hp]

private theorem perm_differs_in_two_columns (π σ : Equiv.Perm ι) (h : π ≠ σ) :
    ∃ j k : ι, j ≠ k ∧ π j ≠ σ j ∧ π k ≠ σ k := by
  have hex : ∃ j, π j ≠ σ j := by
    by_contra hn
    push_neg at hn
    exact h (Equiv.ext hn)
  obtain ⟨j, hj⟩ := hex
  let k := σ.symm (π j)
  have hk : σ k = π j := σ.apply_symm_apply _
  have hjk : j ≠ k := by
    intro e
    exact hj (by simpa only [← e] using hk.symm)
  exact ⟨j, k, hjk, hj, fun e => hjk (π.injective (hk.symm.trans e.symm))⟩

private theorem two_entries_bound_realSignedWeight (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (hentry : ∀ i j, ‖U i j‖ ≤ 1) (π : Equiv.Perm ι) {j k : ι}
    (hjk : j ≠ k) (r : ℝ) (hr : 0 ≤ r)
    (hj : ‖U (π j) j‖ ^ 2 ≤ r) (hk : ‖U (π k) k‖ ^ 2 ≤ r) :
    |realSignedWeight U π| ≤ r := by
  let f (i : ι) := ‖U (π i) i‖
  have hprod : (∏ i ∈ (univ.erase j).erase k, f i) ≤ 1 :=
    prod_le_one (fun i _ => norm_nonneg _) (fun i _ => hentry _ _)
  have hpair : f j * f k ≤ r := by
    have hnon : 0 ≤ f j * f k := mul_nonneg (norm_nonneg _) (norm_nonneg _)
    have hsq : 0 ≤ (f j - f k)^2 := sq_nonneg _
    change f j ^ 2 ≤ r at hj
    change f k ^ 2 ≤ r at hk
    linarith [show 2 * (f j * f k) ≤ f j^2 + f k^2 by nlinarith]
  refine (realSignedWeight_abs_le_entry_product U hU π).trans ?_
  change (∏ i, f i) ≤ r
  rw [← prod_erase_mul univ f (mem_univ j),
    ← prod_erase_mul (univ.erase j) f (mem_erase.mpr ⟨Ne.symm hjk, mem_univ k⟩),
    mul_assoc, mul_comm (f k) (f j)]
  exact (mul_le_of_le_one_left (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hprod).trans hpair

/-- If a permutation uses only edges from two assignments, choosing the
other edge at each column gives a permutation with the complementary score. -/
private theorem supportedAssignment_has_complement (σ τ π : Equiv.Perm ι)
    (h : ∀ j, π j = σ j ∨ π j = τ j) :
    ∃ ρ : Equiv.Perm ι, ∀ (c : ι → ι → ℝ) j,
      c (π j) j + c (ρ j) j = c (σ j) j + c (τ j) j := by
  let q (j : ι) := if π j = σ j then τ j else σ j
  have hq (j : ι) :
      (π j = σ j ∧ q j = τ j) ∨ (π j = τ j ∧ q j = σ j) := by
    by_cases hj : π j = σ j
    · exact Or.inl ⟨hj, if_pos hj⟩
    · exact Or.inr ⟨(h j).resolve_left hj, if_neg hj⟩
  have hinj : Function.Injective q := by
    intro j k he
    by_contra hne
    have hcross {j k : ι} (hne : j ≠ k)
        (hj : π j = σ j ∧ q j = τ j) (hk : π k = τ k ∧ q k = σ k)
        (he : q j = q k) : False := by
      have hc : τ j = σ k := hj.2.symm.trans (he.trans hk.2)
      obtain ⟨l, hl⟩ := π.surjective (τ j)
      rcases h l with hls | hlt
      · have hlk : l = k := σ.injective (hls.symm.trans (hl.trans hc))
        subst l
        exact hne (τ.injective (hl.symm.trans hk.1))
      · have hlj : l = j := τ.injective (hlt.symm.trans hl)
        subst l
        exact hne (σ.injective (hj.1.symm.trans (hl.trans hc)))
    rcases hq j with hj | hj
    · rcases hq k with hk | hk
      · exact hne (τ.injective (hj.2.symm.trans (he.trans hk.2)))
      · exact hcross hne hj hk he
    · rcases hq k with hk | hk
      · exact hcross (Ne.symm hne) hk hj he.symm
      · exact hne (σ.injective (hj.2.symm.trans (he.trans hk.2)))
  let ρ := Equiv.ofBijective q ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩
  refine ⟨ρ, fun c j => ?_⟩
  change c (π j) j + c (q j) j = _
  rcases hq j with ⟨hj, hqj⟩ | ⟨hj, hqj⟩
  · rw [hj, hqj]
  · rw [hj, hqj, add_comm (c (τ j) j)]

private theorem involutiveAssignments_two_forbidden_edges (σ τ π : Equiv.Perm ι)
    (hinv : ∀ j, τ (σ.symm (τ j)) = σ j) (j : ι)
    (hjσ : π j ≠ σ j) (hjτ : π j ≠ τ j) :
    ∃ k, j ≠ k ∧ π k ≠ σ k ∧ π k ≠ τ k := by
  by_contra hnone
  push_neg at hnone
  let k := σ.symm (π j)
  let l := σ.symm (τ k)
  have hk : σ k = π j := σ.apply_symm_apply _
  have hl : σ l = τ k := σ.apply_symm_apply _
  have hl' : τ l = σ k := hinv k
  have hjk : j ≠ k := by
    intro e
    exact hjσ (by simpa only [← e] using hk.symm)
  have hjl : j ≠ l := by
    intro e
    exact hjτ (by simpa only [← e] using hk.symm.trans hl'.symm)
  have hkk : π k = τ k := hnone k hjk (fun e => hjk (π.injective (hk.symm.trans e.symm)))
  have hkl : k ≠ l := by
    intro e
    have hkτ : σ k = τ k := by simpa only [← e] using hl
    exact hjk (π.injective (hk.symm.trans (hkτ.trans hkk.symm)))
  have hll := hnone l hjl (fun e => hkl (π.injective (hkk.trans (hl.symm.trans e.symm))))
  exact hjl (π.injective (hk.symm.trans (hl'.symm.trans hll.symm)))

private theorem assignmentFace_offWeight_bound (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (σ τ : Equiv.Perm ι) (w : Equiv.Perm ι → ℝ) (hw : ∀ π, 0 ≤ w π)
    (hs : ∑ π, w π = 1)
    (hm : ∀ i j, (∑ π, if π j = i then w π else 0) = Complex.normSq (U i j))
    (hforbidden : ∀ π ∈ offAssignmentFace σ τ, ∃ j, π j ≠ σ j ∧ π j ≠ τ j) :
    let mass := ∑ π ∈ offAssignmentFace σ τ, w π
    ∀ π ∈ offAssignmentFace σ τ,
      |realSignedWeight U π| ≤ (4 * (Fintype.card ι : ℝ)^2 + 3) * mass := by
  let T := offAssignmentFace σ τ
  let mass := ∑ π ∈ T, w π
  let n : ℝ := Fintype.card ι
  let C : ℝ := 4 * n ^ 2 + 3
  have hm0 : 0 ≤ mass := sum_nonneg (fun π _ => hw π)
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have hC : mass ≤ C * mass := by
    have hc : 1 ≤ C := by dsimp [C]; nlinarith
    simpa using mul_le_mul_of_nonneg_right hc hm0
  let e (i j : ι) (π : Equiv.Perm ι) := if π j = i then w π else 0
  have he0 (i j : ι) (π : Equiv.Perm ι) : 0 ≤ e i j π := by
    dsimp [e]
    split_ifs
    · exact hw π
    · exact le_rfl
  have he (i j : ι) (π : Equiv.Perm ι) : e i j π ≤ w π := by
    dsimp [e]
    split_ifs
    · exact le_rfl
    · exact hw π
  have hmass (i j : ι) : (∑ π ∈ T, e i j π) ≤ mass :=
    sum_le_sum fun π _ => he i j π
  have hnorm (i j : ι) : ‖U i j‖ ≤ 1 := by
    have hl : Complex.normSq (U i j) ≤ 1 := by
      rw [← hm i j, ← hs]
      exact sum_le_sum fun π _ => he i j π
    rw [Complex.normSq_eq_norm_sq] at hl
    nlinarith only [hl, sq_nonneg (‖U i j‖ - 1)]
  have hoff (i j : ι) (hiσ : σ j ≠ i) (hiτ : τ j ≠ i) :
      ‖U i j‖ ^ 2 ≤ mass := by
    rw [← Complex.normSq_eq_norm_sq, ← hm i j]
    change (∑ π, e i j π) ≤ mass
    by_cases hστ : σ = τ
    · subst τ
      rw [sum_split_oneAssignment σ (e i j)]
      simpa only [e, if_neg hiσ, add_zero] using hmass i j
    · rw [sum_split_twoAssignments σ τ hστ (e i j)]
      simpa only [e, if_neg hiσ, if_neg hiτ, add_zero] using hmass i j
  change ∀ π ∈ T, |realSignedWeight U π| ≤ C * mass
  by_cases hinv : ∀ j, τ (σ.symm (τ j)) = σ j
  · intro π hπ
    obtain ⟨j, hjσ, hjτ⟩ := hforbidden π hπ
    obtain ⟨k, hjk, hkσ, hkτ⟩ :=
      involutiveAssignments_two_forbidden_edges σ τ π hinv j hjσ hjτ
    exact (two_entries_bound_realSignedWeight U hU hnorm π hjk mass hm0
      (hoff (π j) j (Ne.symm hjσ) (Ne.symm hjτ))
      (hoff (π k) k (Ne.symm hkσ) (Ne.symm hkτ))).trans hC
  · push_neg at hinv
    obtain ⟨j, hj⟩ := hinv
    let k := σ.symm (τ j)
    let p := τ j
    have hk : σ k = p := σ.apply_symm_apply _
    have hjk : j ≠ k := by
      intro e
      apply hj
      change τ k = σ j
      exact (congrArg τ e.symm).trans (hk.symm.trans (congrArg σ e.symm))
    have hστ : σ ≠ τ := by
      intro he
      apply hj
      simp [he]
    have hnot : ∀ i : ι, i ≠ p →
        (σ j ≠ i ∧ τ j ≠ i) ∨ (σ k ≠ i ∧ τ k ≠ i) := by
      intro i hi
      by_cases h : σ j = i
      · exact Or.inr ⟨fun q => hi (q.symm.trans hk), fun q => hj (q.trans h.symm)⟩
      · exact Or.inl ⟨h, Ne.symm hi⟩
    have hsum : (∑ i, star (U i j) * U i k) = 0 := by
      have h := congrArg (fun V : Matrix ι ι ℂ => V j k) hU.2
      simpa only [mul_apply, conjTranspose_apply, one_apply_ne hjk] using h
    have hsplit := sum_erase_add univ (fun i => star (U i j) * U i k) (mem_univ p)
    have hprod := add_eq_zero_iff_eq_neg.mp (hsplit.trans hsum)
    have hsqrt0 : 0 ≤ Real.sqrt mass := Real.sqrt_nonneg _
    have hsqrt : (Real.sqrt mass)^2 = mass := Real.sq_sqrt hm0
    have hnormOff (i l : ι) (ha : σ l ≠ i) (hb : τ l ≠ i) :
        ‖U i l‖ ≤ Real.sqrt mass := by
      have hp := hoff i l ha hb
      apply (sq_le_sq₀ (norm_nonneg _) hsqrt0).mp
      rwa [hsqrt]
    have hprodBounds (i : ι) (hi : i ∈ univ.erase p) :
        ‖star (U i j) * U i k‖ ≤ Real.sqrt mass := by
      rw [norm_mul, Complex.star_def, Complex.norm_conj]
      rcases hnot i (mem_erase.mp hi).1 with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact (mul_le_mul_of_nonneg_right (hnormOff i j ha hb) (norm_nonneg _)).trans
          (mul_le_of_le_one_right hsqrt0 (hnorm i k))
      · exact (mul_le_mul_of_nonneg_left (hnormOff i k ha hb) (norm_nonneg _)).trans
          (mul_le_of_le_one_left hsqrt0 (hnorm i j))
    have hcard : ((univ.erase p : Finset ι).card : ℝ) ≤ n := by
      dsimp [n]
      exact_mod_cast card_le_univ (univ.erase p : Finset ι)
    have hnormProd : ‖star (U p j) * U p k‖ ≤ n * Real.sqrt mass := by
      rw [← norm_neg (star (U p j) * U p k), ← hprod]
      calc
        _ ≤ ∑ i ∈ univ.erase p, ‖star (U i j) * U i k‖ := norm_sum_le _ _
        _ ≤ ∑ _i ∈ univ.erase p, Real.sqrt mass := sum_le_sum hprodBounds
        _ ≤ _ := by
          simpa only [sum_const, nsmul_eq_mul] using
            mul_le_mul_of_nonneg_right hcard hsqrt0
    have hsingle (i l : ι) (π : Equiv.Perm ι) (h : π l = i) :
        w π ≤ Complex.normSq (U i l) := by
      rw [← hm i l, ← show e i l π = w π from if_pos h]
      exact single_le_sum (fun π _ => he0 i l π) (mem_univ π)
    have hprodSq : ‖star (U p j) * U p k‖^2 ≤ n^2 * mass := by
      have hp := mul_nonneg (sub_nonneg.mpr hnormProd)
        (add_nonneg (mul_nonneg hn0 hsqrt0) (norm_nonneg (star (U p j) * U p k)))
      calc
        ‖star (U p j) * U p k‖^2 ≤ (n * Real.sqrt mass)^2 := by nlinarith
        _ = n^2 * mass := by rw [mul_pow, hsqrt]
    have hweights : w σ * w τ ≤ n^2 * mass := by
      calc
        w σ * w τ ≤ Complex.normSq (U p k) * Complex.normSq (U p j) :=
          mul_le_mul (hsingle p k σ hk) (hsingle p j τ rfl) (hw τ) (Complex.normSq_nonneg _)
        _ = ‖star (U p j) * U p k‖^2 := by
          rw [norm_mul, Complex.star_def, Complex.norm_conj, mul_pow,
            Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, mul_comm]
        _ ≤ _ := hprodSq
    have ht : mass + w τ + w σ = 1 := (sum_split_twoAssignments σ τ hστ w).symm.trans hs
    have hsmall (u v : ℝ) (hu : 0 ≤ u) (hv : u ≤ v)
        (hadd : mass + u + v = 1) (hmul : u * v ≤ n^2 * mass) :
        u ≤ (4 * n^2 + 2) * mass := by
      by_cases hm : mass ≤ 1 / 2
      · have hquarter : 1 / 4 ≤ v := by linarith
        have hh := mul_le_mul_of_nonneg_left hquarter hu
        nlinarith [mul_nonneg (sq_nonneg n) hm0]
      · have hhalf : 1 / 2 ≤ mass := le_of_lt (lt_of_not_ge hm)
        have hv0 : 0 ≤ v := hu.trans hv
        nlinarith [mul_nonneg (sq_nonneg n) hm0]
    have hdom : ∃ ρ : Equiv.Perm ι, (ρ = σ ∨ ρ = τ) ∧
        ∀ i l, ρ l ≠ i → ‖U i l‖^2 ≤ C * mass := by
      rcases le_total (w τ) (w σ) with hw' | hw'
      · refine ⟨σ, Or.inl rfl, fun i l hi => ?_⟩
        have hτ := hsmall (w τ) (w σ) (hw τ) hw' ht
          (by simpa only [mul_comm (w τ) (w σ)] using hweights)
        rw [← Complex.normSq_eq_norm_sq, ← hm i l]
        change (∑ π, e i l π) ≤ C * mass
        rw [sum_split_twoAssignments σ τ hστ (e i l)]
        have hzero : e i l σ = 0 := if_neg hi
        rw [hzero, add_zero]
        have hb := add_le_add (hmass i l) (he i l τ)
        dsimp [C]
        nlinarith only [hb, hτ]
      · refine ⟨τ, Or.inr rfl, fun i l hi => ?_⟩
        have hσ := hsmall (w σ) (w τ) (hw σ) hw' (by linarith) hweights
        rw [← Complex.normSq_eq_norm_sq, ← hm i l]
        change (∑ π, e i l π) ≤ C * mass
        rw [sum_split_twoAssignments σ τ hστ (e i l)]
        have hzero : e i l τ = 0 := if_neg hi
        rw [hzero, add_zero]
        have hb := add_le_add (hmass i l) (he i l σ)
        dsimp [C]
        nlinarith only [hb, hσ]
    obtain ⟨ρ, hρ, hsmallEntries⟩ := hdom
    intro π hπ
    have hne : π ≠ ρ := by
      have hh := (mem_offAssignmentFace σ τ π).mp hπ
      rcases hρ with rfl | rfl
      · exact hh.1
      · exact hh.2
    obtain ⟨j', k', hjk', hj', hk'⟩ := perm_differs_in_two_columns π ρ hne
    exact two_entries_bound_realSignedWeight U hU hnorm π hjk' (C * mass)
      (hm0.trans hC) (hsmallEntries _ _ hj'.symm) (hsmallEntries _ _ hk'.symm)

private def assignmentFaceVariationConstant (ι : Type*) [Fintype ι] [DecidableEq ι] : ℝ :=
  let p : ℝ := Fintype.card (Equiv.Perm ι)
  p * (p + 1) * (4 * (Fintype.card ι : ℝ)^2 + 4)

private theorem assignmentFaceVariationConstant_nonneg :
    0 ≤ assignmentFaceVariationConstant ι := by
  unfold assignmentFaceVariationConstant
  positivity

private theorem signedLaw_sub_birkhoff_singleton (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (w : Equiv.Perm ι → ℝ)
    (hm : ∀ i j, (∑ π, if π j = i then w π else 0) = Complex.normSq (U i j))
    (i j : ι) : (∑ π, if π j = i then realSignedWeight U π - w π else 0) = 0 := by
  calc
    _ = (∑ π, if π j = i then realSignedWeight U π else 0) -
        ∑ π, if π j = i then w π else 0 := by
      rw [← sum_sub_distrib]
      apply sum_congr rfl
      intro π _
      split_ifs <;> simp
    _ = 0 := by rw [marginal_realSignedWeight U hU i j, hm i j, sub_self]

private theorem assignmentFace_variation_bound (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (σ τ : Equiv.Perm ι) (w : Equiv.Perm ι → ℝ) (hw : ∀ π, 0 ≤ w π)
    (hs : ∑ π, w π = 1)
    (hm : ∀ i j, (∑ π, if π j = i then w π else 0) = Complex.normSq (U i j))
    (hforbidden : ∀ π ∈ offAssignmentFace σ τ, ∃ j, π j ≠ σ j ∧ π j ≠ τ j) :
    (∑ π, |realSignedWeight U π - w π|) ≤
      assignmentFaceVariationConstant ι * ∑ π ∈ offAssignmentFace σ τ, w π := by
  let T := offAssignmentFace σ τ
  let mass := ∑ π ∈ T, w π
  let p : ℝ := Fintype.card (Equiv.Perm ι)
  let C : ℝ := 4 * (Fintype.card ι : ℝ)^2 + 3
  let B : ℝ := (C + 1) * mass
  let d (π : Equiv.Perm ι) := realSignedWeight U π - w π
  have hmass : 0 ≤ mass := sum_nonneg (fun π _ => hw π)
  have hB : 0 ≤ B := by dsimp [B, C]; positivity
  have hp : 0 ≤ p := Nat.cast_nonneg _
  have hoff (π : Equiv.Perm ι) (hπ : π ∈ T) : |d π| ≤ B := by
    have hsign : |realSignedWeight U π| ≤ C * mass :=
      assignmentFace_offWeight_bound U hU σ τ w hw hs hm hforbidden π hπ
    have hweight : w π ≤ mass := single_le_sum (fun q _ => hw q) hπ
    change |realSignedWeight U π - w π| ≤ B
    rw [sub_eq_add_neg]
    refine (abs_add_le _ _).trans ?_
    rw [abs_neg, abs_of_nonneg (hw π)]
    dsimp [B]
    nlinarith only [hsign, hweight]
  have hoffSum (g : Equiv.Perm ι → ℝ) (hg : ∀ π ∈ T, |g π| ≤ B) :
      |∑ π ∈ T, g π| ≤ p * B := by
    calc
      _ ≤ ∑ π ∈ T, |g π| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _π ∈ T, B := sum_le_sum hg
      _ ≤ p * B := by
        have hc : (T.card : ℝ) ≤ p := by
          dsimp [p]
          exact_mod_cast card_le_univ T
        simpa only [sum_const, nsmul_eq_mul] using mul_le_mul_of_nonneg_right hc hB
  have hface (q : Equiv.Perm ι) (hq : q = σ ∨ q = τ) : |d q| ≤ p * B := by
    by_cases he : σ = τ
    · subst τ
      have hq' := hq.elim id id
      subst q
      have hz : ∑ π, d π = 0 := by
        simp only [d, sum_sub_distrib, sum_realSignedWeight U hU, hs, sub_self]
      rw [sum_split_oneAssignment σ d] at hz
      have heq : d σ = -(∑ π ∈ T, d π) := by linarith
      rw [heq, abs_neg]
      exact hoffSum d hoff
    · obtain ⟨j, k, hjk, hj, hk⟩ := perm_differs_in_two_columns σ τ he
      let g (π : Equiv.Perm ι) := if π j = q j then d π else 0
      have hz : ∑ π, g π = 0 :=
        signedLaw_sub_birkhoff_singleton U hU w hm (q j) j
      have hgb : ∀ π ∈ T, |g π| ≤ B := by
        intro π hπ
        dsimp [g]
        split_ifs
        · exact hoff π hπ
        · simpa only [abs_zero] using hB
      rw [sum_split_twoAssignments σ τ he g] at hz
      have heq : d q = -(∑ π ∈ T, g π) := by
        rcases hq with heq | heq
        · subst q
          have hgσ : g σ = d σ := if_pos rfl
          have hgτ : g τ = 0 := if_neg (Ne.symm hj)
          rw [hgσ, hgτ, add_zero] at hz
          exact eq_neg_of_add_eq_zero_right hz
        · subst q
          have hgσ : g σ = 0 := if_neg hj
          have hgτ : g τ = d τ := if_pos rfl
          rw [hgσ, hgτ, add_zero] at hz
          exact eq_neg_of_add_eq_zero_right hz
      rw [heq, abs_neg]
      exact hoffSum g hgb
  have hall (π : Equiv.Perm ι) : |d π| ≤ (p + 1) * B := by
    by_cases hπ : π ∈ T
    · have hle := hoff π hπ
      nlinarith [mul_nonneg hp hB]
    · have hface' : π = σ ∨ π = τ := by
        by_cases h : π = σ
        · exact Or.inl h
        · apply Or.inr
          by_contra h'
          exact hπ ((mem_offAssignmentFace σ τ π).mpr ⟨h, h'⟩)
      have hle := hface π hface'
      nlinarith
  change (∑ π, |d π|) ≤ _
  calc
    _ ≤ ∑ _π : Equiv.Perm ι, (p + 1) * B := sum_le_sum fun π _ => hall π
    _ = _ := by
      simp only [assignmentFaceVariationConstant, sum_const, card_univ, nsmul_eq_mul, B, C, p]
      change (Fintype.card (Equiv.Perm ι) : ℝ) * _ =
        _ * (∑ π ∈ T, w π)
      dsimp [mass]
      ring

private theorem signedLaw_sub_birkhoff_assignment_score (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (w : Equiv.Perm ι → ℝ)
    (hm : ∀ i j, (∑ π, if π j = i then w π else 0) = Complex.normSq (U i j))
    (c : ι → ι → ℝ) :
    (∑ π, (realSignedWeight U π - w π) * (∑ j, c (π j) j)) = 0 := by
  simp only [mul_sum]
  rw [sum_comm]
  apply sum_eq_zero
  intro j _
  calc
    _ = ∑ i, (∑ π, if π j = i then realSignedWeight U π - w π else 0) * c i j := by
      symm
      simp only [sum_mul]
      rw [sum_comm]
      apply sum_congr rfl
      intro π _
      simp [ite_mul, eq_comm]
    _ = 0 := by
      simp only [signedLaw_sub_birkhoff_singleton U hU w hm, zero_mul, sum_const_zero]

private theorem offAssignmentFace_has_forbidden_edge (c : ι → ι → ℝ)
    (σ τ : Equiv.Perm ι) {δ : ℝ} (hδ : 0 < δ)
    (hmax : ∀ π : Equiv.Perm ι, (∑ j, c (π j) j) ≤ ∑ j, c (σ j) j)
    (htie : (∑ j, c (τ j) j) = ∑ j, c (σ j) j)
    (hgap : ∀ π ∈ offAssignmentFace σ τ, δ ≤ (∑ j, c (σ j) j) - ∑ j, c (π j) j) :
    ∀ π ∈ offAssignmentFace σ τ, ∃ j, π j ≠ σ j ∧ π j ≠ τ j := by
  intro π hπ
  by_contra! h
  have hallowed (j : ι) : π j = σ j ∨ π j = τ j := by
    by_cases he : π j = σ j
    · exact Or.inl he
    · exact Or.inr (h j he)
  obtain ⟨ρ, hρ⟩ := supportedAssignment_has_complement σ τ π hallowed
  have hadd : (∑ j, c (π j) j) + ∑ j, c (ρ j) j =
      (∑ j, c (σ j) j) + ∑ j, c (τ j) j := by
    rw [← sum_add_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun j _ => hρ c j
  rw [htie] at hadd
  linarith [hmax ρ, hgap π hπ]

private theorem stable_assignment_support (c : ι → ι → ℝ) (q : Equiv.Perm ι → ℝ)
    (σ τ : Equiv.Perm ι) (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 ≤ ε)
    (hmax : ∀ π : Equiv.Perm ι, (∑ j, c (π j) j) ≤ ∑ j, c (σ j) j)
    (htie : (∑ j, c (τ j) j) = ∑ j, c (σ j) j)
    (hgap : ∀ π ∈ offAssignmentFace σ τ, δ ≤ (∑ j, c (σ j) j) - ∑ j, c (π j) j)
    (herr : ∀ π : Equiv.Perm ι, |q π - ∑ j, c (π j) j| ≤ ε)
    (hsmall : (assignmentFaceVariationConstant ι + 2) * ε ≤ δ)
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) :
    ∃ ρ : Equiv.Perm ι, (∑ π, realSignedWeight U π * q π) ≤ q ρ := by
  let T := offAssignmentFace σ τ
  let b (π : Equiv.Perm ι) := ∑ j, c (π j) j
  let L := assignmentFaceVariationConstant ι
  obtain ⟨w, hw, hs, hm⟩ := real_birkhoff_weights U hU
  let mass := ∑ π ∈ T, w π
  let d (π : Equiv.Perm ι) := realSignedWeight U π - w π
  have hmass : 0 ≤ mass := sum_nonneg (fun π _ => hw π)
  have hvar : (∑ π, |d π|) ≤ L * mass :=
    assignmentFace_variation_bound U hU σ τ w hw hs hm
      (offAssignmentFace_has_forbidden_edge c σ τ hδ hmax htie hgap)
  have hbase : ∑ π, d π * b π = 0 := signedLaw_sub_birkhoff_assignment_score U hU w hm c
  obtain ⟨ρ, _, hρ⟩ := exists_max_image univ q ⟨σ, mem_univ _⟩
  have hρ' (π : Equiv.Perm ι) : q π ≤ q ρ := hρ π (mem_univ _)
  have hlocalGap (π : Equiv.Perm ι) (hπ : π ∈ T) : δ - 2 * ε ≤ q ρ - q π := by
    have h₁ := (abs_le.mp (herr σ)).1
    have h₂ := (abs_le.mp (herr π)).2
    have hd := hgap π hπ
    change -ε ≤ q σ - b σ at h₁
    change q π - b π ≤ ε at h₂
    change δ ≤ b σ - b π at hd
    linarith [hρ' σ]
  have hgapSum : (δ - 2 * ε) * mass ≤ q ρ - ∑ π, w π * q π := by
    have he : q ρ - (∑ π, w π * q π) = ∑ π, w π * (q ρ - q π) := by
      simp only [mul_sub, sum_sub_distrib, ← sum_mul, hs, one_mul]
    rw [he]
    calc
      _ = ∑ π ∈ T, w π * (δ - 2 * ε) := by
        rw [← sum_mul, mul_comm]
      _ ≤ ∑ π ∈ T, w π * (q ρ - q π) :=
        sum_le_sum fun π hπ => mul_le_mul_of_nonneg_left (hlocalGap π hπ) (hw π)
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ T)
        (fun π _ _ => mul_nonneg (hw π) (sub_nonneg.mpr (hρ' π)))
  have hcorrection : (∑ π, d π * q π) ≤ ε * (L * mass) := by
    have he : (∑ π, d π * q π) = ∑ π, d π * (q π - b π) := by
      simp only [mul_sub, sum_sub_distrib, hbase, sub_zero]
    rw [he]
    calc
      _ ≤ ∑ π, |d π * (q π - b π)| := sum_le_sum fun π _ => le_abs_self _
      _ ≤ ∑ π, |d π| * ε := by
        apply sum_le_sum
        intro π _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (herr π) (abs_nonneg _)
      _ ≤ _ := by
        rw [← sum_mul]
        exact (mul_le_mul_of_nonneg_right hvar hε).trans_eq (mul_comm _ _)
  have hle : ε * (L * mass) ≤ (δ - 2 * ε) * mass := by
    have hs' : ε * L ≤ δ - 2 * ε := by
      change (L + 2) * ε ≤ δ at hsmall
      nlinarith
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right hs' hmass
  have hsplit : (∑ π, realSignedWeight U π * q π) =
      (∑ π, w π * q π) + ∑ π, d π * q π := by
    simp only [d, sub_mul, sum_sub_distrib]
    ring
  refine ⟨ρ, ?_⟩
  rw [hsplit]
  linarith [hcorrection.trans hle]

/-- The linear assignment value for reciprocal first spectrum `x`. -/
def reciprocalAssignmentSum (x b : ι → ℂ) (π : Equiv.Perm ι) : ℂ :=
  ∑ j, x (π j) * b j

/-- Distinct values and no three values on one real affine line. A nonzero
complex direction tests a line by equality of the real projections. -/
def ReciprocalAssignmentsInGeneralPosition (x b : ι → ℂ) : Prop :=
  Function.Injective (reciprocalAssignmentSum x b) ∧
    ∀ (η : ℂ), η ≠ 0 → ∀ σ τ ρ : Equiv.Perm ι, σ ≠ τ → σ ≠ ρ → τ ≠ ρ →
      (η * reciprocalAssignmentSum x b σ).re = (η * reciprocalAssignmentSum x b τ).re →
      (η * reciprocalAssignmentSum x b σ).re ≠ (η * reciprocalAssignmentSum x b ρ).re

private theorem unitDirection_assignment_face (x b : ι → ℂ)
    (h : ReciprocalAssignmentsInGeneralPosition x b) (η : ℂ) (hη : η ≠ 0) :
    ∃ (σ τ : Equiv.Perm ι) (δ : ℝ), 0 < δ ∧
      (∀ π, (η * reciprocalAssignmentSum x b π).re ≤ (η * reciprocalAssignmentSum x b σ).re) ∧
      (η * reciprocalAssignmentSum x b τ).re = (η * reciprocalAssignmentSum x b σ).re ∧
      ∀ π ∈ offAssignmentFace σ τ,
        δ ≤ (η * reciprocalAssignmentSum x b σ).re - (η * reciprocalAssignmentSum x b π).re := by
  let f (π : Equiv.Perm ι) := (η * reciprocalAssignmentSum x b π).re
  obtain ⟨σ, _, hσ⟩ := exists_max_image univ f ⟨Equiv.refl ι, mem_univ _⟩
  have hmax (π : Equiv.Perm ι) : f π ≤ f σ := hσ π (mem_univ _)
  have hface : ∃ τ : Equiv.Perm ι, f τ = f σ ∧
      ∀ π ∈ offAssignmentFace σ τ, f π < f σ := by
    by_cases htwo : ∃ τ : Equiv.Perm ι, τ ≠ σ ∧ f τ = f σ
    · obtain ⟨τ, hτ, ht⟩ := htwo
      refine ⟨τ, ht, fun π hπ => lt_of_le_of_ne (hmax π) ?_⟩
      have hp := (mem_offAssignmentFace σ τ π).mp hπ
      exact fun he => h.2 η hη σ τ π hτ.symm hp.1.symm hp.2.symm ht.symm he.symm
    · refine ⟨σ, rfl, fun π hπ => lt_of_le_of_ne (hmax π) ?_⟩
      exact fun he => htwo ⟨π, ((mem_offAssignmentFace σ σ π).mp hπ).1, he⟩
  obtain ⟨τ, ht, hgap⟩ := hface
  let g (π : Equiv.Perm ι) := f σ - f π
  let T := offAssignmentFace σ τ
  let S := insert (1 : ℝ) (T.image g)
  obtain ⟨δ, hδ, hmin⟩ := exists_min_image S id ⟨1, mem_insert_self _ _⟩
  have hδpos : 0 < δ := by
    have hmem : δ = 1 ∨ δ ∈ T.image g := mem_insert.mp hδ
    rcases hmem with rfl | hmem
    · exact zero_lt_one
    · obtain ⟨π, hπ, hπδ⟩ := mem_image.mp hmem
      exact hπδ ▸ sub_pos.mpr (hgap π hπ)
  refine ⟨σ, τ, δ, hδpos, hmax, ht, fun π hπ => ?_⟩
  exact hmin (g π) (mem_insert_of_mem (mem_image.mpr ⟨π, hπ, rfl⟩))

private theorem assignmentAffineProduct_coeff (x : ι → ℂ) (s : Finset ι) :
    let p : ℂ[X] := ∏ j ∈ s, (1 + C (x j) * X)
    p.coeff 0 = 1 ∧ p.coeff 1 = ∑ j ∈ s, x j := by
  have h₀ (z : ℂ) : (1 + C z * X).coeff 0 = 1 := by
    norm_num [coeff_add, coeff_one, coeff_C_mul_X]
  have h₁ (z : ℂ) : (1 + C z * X).coeff 1 = z := by
    norm_num [coeff_add, coeff_one, coeff_C_mul_X]
  induction s using Finset.induction_on with
  | empty => norm_num [coeff_one]
  | @insert j s hj ih =>
    obtain ⟨hs₀, hs₁⟩ := ih
    constructor
    · rw [prod_insert hj, mul_coeff_zero, h₀, hs₀, one_mul]
    · rw [prod_insert hj, sum_insert hj, mul_coeff_one, h₀, h₁, hs₀, hs₁,
        one_mul, mul_one, add_comm]

private theorem assignment_matching_polynomials (a b : ι → ℂ) (ha : ∀ i, a i ≠ 0) :
    ∃ Q : Equiv.Perm ι → ℂ[X], ∀ π : Equiv.Perm ι,
      (Q π).eval 0 = reciprocalAssignmentSum (fun i => (a i)⁻¹) b π ∧
      ∀ t : ℂ, matchingProduct a (fun j => t * b j) π =
        (∏ i, a i) * (1 + t * (Q π).eval t) := by
  let x (π : Equiv.Perm ι) (j : ι) := (a (π j))⁻¹ * b j
  let P (π : Equiv.Perm ι) : ℂ[X] := ∏ j, (1 + C (x π j) * X)
  have hc (π : Equiv.Perm ι) :
      (P π).coeff 0 = 1 ∧ (P π).coeff 1 = ∑ j, x π j :=
    assignmentAffineProduct_coeff (x π) univ
  have hdiv (π : Equiv.Perm ι) : X ∣ P π - 1 := by
    rw [X_dvd_iff, coeff_sub, (hc π).1] <;> simp
  choose Q hQ using hdiv
  refine ⟨Q, fun π => ⟨?_, fun t => ?_⟩⟩
  · change (Q π).eval 0 = ∑ j, x π j
    calc
      _ = (Q π).coeff 0 := (coeff_zero_eq_eval_zero _).symm
      _ = (X * Q π).coeff 1 := by rw [mul_comm X (Q π), coeff_mul_X] <;> rfl
      _ = (P π - 1).coeff 1 := by rw [← hQ π]
      _ = _ := by simp [(hc π).2, coeff_one]
  · have hPeval : (P π).eval t = 1 + t * (Q π).eval t := by
      have hv := congrArg (eval t) (hQ π)
      simp only [eval_sub, eval_one, eval_mul, eval_X] at hv
      linear_combination hv
    rw [← hPeval]
    unfold matchingProduct
    simp only [P, eval_prod, eval_add, eval_one, eval_mul, eval_C, eval_X]
    rw [← Equiv.prod_comp π a, ← prod_mul_distrib]
    apply prod_congr rfl
    intro j _
    dsimp [x]
    calc
      _ = a (π j) * 1 + t * (a (π j) * (a (π j))⁻¹) * b j := by
        simp only [mul_inv_cancel₀ (ha (π j)), mul_one]
      _ = _ := by ring

private theorem supported_polynomial_near_zero (x b : ι → ℂ)
    (h : ReciprocalAssignmentsInGeneralPosition x b)
    (Q : Equiv.Perm ι → ℂ[X])
    (hQ : ∀ π, (Q π).eval 0 = reciprocalAssignmentSum x b π) :
    ∃ r : ℝ, 0 < r ∧ ∀ (t : ℂ), ‖t‖ < r → ∀ (η : ℂ), ‖η‖ = 1 →
      ∀ (U : Matrix ι ι ℂ), IsUnitary U → ∃ ρ : Equiv.Perm ι,
        (∑ π, realSignedWeight U π * (η * (Q π).eval t).re) ≤ (η * (Q ρ).eval t).re := by
  let S := Metric.sphere (0 : ℂ) 1
  let q (z : ℂ × ℂ) (π : Equiv.Perm ι) := (z.1 * (Q π).eval z.2).re
  let Good : Set (ℂ × ℂ) := {z | ∀ (U : Matrix ι ι ℂ), IsUnitary U →
    ∃ ρ : Equiv.Perm ι, (∑ π, realSignedWeight U π * q z π) ≤ q z ρ}
  have hlocal (η : ℂ) (hη : η ∈ S) : Good ∈ 𝓝 (η, (0 : ℂ)) := by
    have hηne : η ≠ 0 := by
      intro he
      simp [S, he, Metric.mem_sphere] at hη
    obtain ⟨σ, τ, δ, hδ, hmax, htie, hgap⟩ := unitDirection_assignment_face x b h η hηne
    let L := assignmentFaceVariationConstant ι
    have hL : 0 ≤ L := assignmentFaceVariationConstant_nonneg
    let ε := δ / (L + 2)
    have hε : 0 < ε := div_pos hδ (by linarith)
    have hsmall : (L + 2) * ε ≤ δ := by
      have hne : L + 2 ≠ 0 := ne_of_gt (by linarith)
      apply le_of_eq
      dsimp [ε]
      field_simp [hne] <;> ring
    let c (i j : ι) := (η * (x i * b j)).re
    have hc (π : Equiv.Perm ι) : (∑ j, c (π j) j) = (η * reciprocalAssignmentSum x b π).re := by
      simp only [c, reciprocalAssignmentSum, mul_sum, Complex.re_sum]
    have hc₀ (π : Equiv.Perm ι) : q (η, (0 : ℂ)) π = ∑ j, c (π j) j := by
      simp only [q, hQ, hc]
    have hnear : ∀ᶠ z in 𝓝 (η, (0 : ℂ)), ∀ π : Equiv.Perm ι,
        |q z π - ∑ j, c (π j) j| < ε := by
      apply Filter.eventually_all.mpr
      intro π
      have hcont : Continuous (fun z : ℂ × ℂ => q z π) :=
        Complex.continuous_re.comp (continuous_fst.mul ((Q π).continuous.comp continuous_snd))
      have hd : Continuous (fun z : ℂ × ℂ => |q z π - ∑ j, c (π j) j|) :=
        (hcont.sub continuous_const).abs
      have hp : |q (η, (0 : ℂ)) π - ∑ j, c (π j) j| < ε := by
        rw [hc₀, sub_self, abs_zero]
        exact hε
      exact hd.continuousAt.eventually (gt_mem_nhds hp)
    filter_upwards [hnear] with z hz
    intro U hU
    exact stable_assignment_support c (q z) σ τ δ ε hδ hε.le
      (fun π => by simpa only [hc] using hmax π)
      (by simpa only [hc] using htie)
      (fun π hp => by simpa only [hc] using hgap π hp)
      (fun π => (hz π).le) hsmall U hU
  have hGood : Good ∈ 𝓝ˢ (S ×ˢ ({0} : Set ℂ)) := by
    apply mem_nhdsSet_iff_forall.mpr
    rintro ⟨η, t⟩ ⟨hη, ht⟩
    have he : t = 0 := ht
    subst t
    exact hlocal η hη
  have hcompact : IsCompact S := isCompact_sphere _ _
  rw [hcompact.nhdsSet_prod_eq isCompact_singleton] at hGood
  obtain ⟨A, hA, B, hB, hAB⟩ := Filter.mem_prod_iff.mp hGood
  have hB₀ : B ∈ 𝓝 (0 : ℂ) := mem_nhdsSet_iff_forall.mp hB 0 rfl
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hB₀
  refine ⟨r, hr, fun t ht η hη => ?_⟩
  have hηS : η ∈ S := by simpa only [S, Metric.mem_sphere, dist_zero_right] using hη
  have hηA : η ∈ A := mem_of_mem_nhds (mem_nhdsSet_iff_forall.mp hA η hηS)
  have htB : t ∈ B := hball (by simpa only [Metric.mem_ball, dist_zero_right] using ht)
  exact hAB (show (η, t) ∈ A ×ˢ B from ⟨hηA, htB⟩)

private theorem signed_spectral_sum_real_part (w : Equiv.Perm ι → ℝ)
    (z : Equiv.Perm ι → ℂ) (η : ℂ) :
    (η * ∑ π, (w π : ℂ) * z π).re = ∑ π, w π * (η * z π).re := by
  rw [mul_sum, Complex.re_sum]
  apply sum_congr rfl
  intro π _
  rw [mul_left_comm η (w π : ℂ), Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

private theorem normalize_support_direction {η : ℂ} (hη : η ≠ 0) :
    ∃ k : ℂ, ‖k‖ = 1 ∧ ∀ z : ℂ, (η * z).re = ‖η‖ * (k * z).re := by
  let k := η / (‖η‖ : ℂ)
  have hpos : 0 < ‖η‖ := norm_pos_iff.mpr hη
  have hnorm : ‖k‖ = 1 := by
    rw [show k = η / (‖η‖ : ℂ) from rfl, norm_div, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hpos.le, div_self hpos.ne']
  refine ⟨k, hnorm, fun z => ?_⟩
  have hk : (‖η‖ : ℂ) * k = η := by
    have hne : (‖η‖ : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
    dsimp [k]
    field_simp [hne] <;> ring
  rw [show η * z = (‖η‖ : ℂ) * (k * z) by rw [← mul_assoc, hk],
    Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- The small-spectrum theorem in every finite order. The radius depends on
the two fixed lists. It works for every relative unitary and every complex
parameter in its open disk, with the center included. -/
theorem holds_small_spectral_parameter (a b : ι → ℂ) (ha : ∀ i, a i ≠ 0)
    (hgeneric : ReciprocalAssignmentsInGeneralPosition (fun i => (a i)⁻¹) b) :
    ∃ r : ℝ, 0 < r ∧ ∀ (t : ℂ), ‖t‖ < r →
      ∀ (U : Matrix ι ι ℂ), IsUnitary U → Holds a (fun j => t * b j) U := by
  obtain ⟨Q, hQ⟩ := assignment_matching_polynomials a b ha
  obtain ⟨r, hr, hnear⟩ := supported_polynomial_near_zero
    (fun i => (a i)⁻¹) b hgeneric Q (fun π => (hQ π).1)
  refine ⟨r, hr, fun t ht U hU => ?_⟩
  let D := ∏ i, a i
  let w := realSignedWeight U
  let P (π : Equiv.Perm ι) := (Q π).eval t
  let V := ∑ π, (w π : ℂ) * P π
  have hmatch (π : Equiv.Perm ι) :
      matchingProduct a (fun j => t * b j) π = D * (1 + t * P π) := (hQ π).2 t
  have hcast : (∑ π, (w π : ℂ)) = 1 := by
    exact_mod_cast sum_realSignedWeight U hU
  have hdet : determinantValue a (fun j => t * b j) U = D * (1 + t * V) := by
    rw [← real_signed_determinant a (fun j => t * b j) U hU]
    change (∑ π, (w π : ℂ) * matchingProduct a (fun j => t * b j) π) = _
    calc
      _ = ∑ π, D * ((w π : ℂ) + t * ((w π : ℂ) * P π)) := by
        apply sum_congr rfl
        intro π _
        rw [hmatch π]
        ring
      _ = _ := by
        rw [← mul_sum, sum_add_distrib, ← mul_sum, hcast] <;> rfl
  have hproject (η : ℂ) : ∃ π : Equiv.Perm ι, (η * V).re ≤ (η * P π).re := by
    by_cases he : η = 0
    · exact ⟨Equiv.refl ι, by simp [he]⟩
    obtain ⟨k, hk, hscale⟩ := normalize_support_direction he
    obtain ⟨π, hp⟩ := hnear t ht k hk U hU
    change (∑ q, w q * (k * P q).re) ≤ (k * P π).re at hp
    have hp' : (k * V).re ≤ (k * P π).re := by
      change (k * ∑ q, (w q : ℂ) * P q).re ≤ (k * P π).re
      rw [signed_spectral_sum_real_part w P k]
      exact hp
    refine ⟨π, ?_⟩
    rw [hscale V, hscale (P π)]
    exact mul_le_mul_of_nonneg_left hp' (norm_nonneg η)
  apply (holds_iff_directional a (fun j => t * b j) U).mpr
  intro η
  obtain ⟨π, hp⟩ := hproject (η * D * t)
  refine ⟨π, ?_⟩
  rw [hdet, hmatch π]
  have hf (z : ℂ) : (η * (D * (1 + t * z))).re =
      (η * D).re + ((η * D * t) * z).re := by
    rw [show η * (D * (1 + t * z)) = η * D + (η * D * t) * z by ring, Complex.add_re]
  rw [hf V, hf (P π)]
  exact add_le_add_left hp _

end

end MOC
