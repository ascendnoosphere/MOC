import MOC.CommonWeights
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.EquivFin

/-! Two unitary layers can compose their determinant laws if each full
assignment through their nonzero entries uses each intermediate label once. -/

open BigOperators Matrix

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Every choice of intermediate labels for a full matching is a permutation,
provided each of the chosen two-step paths has nonzero weight. -/
def BijectivePermutationPaths (U V : Matrix ι ι ℂ) : Prop :=
  ∀ (p : Equiv.Perm ι) (f : ι → ι),
    (∀ j, U (p j) (f j) * V (f j) j ≠ 0) → Function.Bijective f

/-- To test the intermediate-label condition, look for two assignments that
use the same intermediate label and extend to a full supported matching.
For each pair, extension is a perfect matching test on the remaining labels. -/
theorem bijectivePermutationPaths_iff_no_repeated_label (U V : Matrix ι ι ℂ) :
    BijectivePermutationPaths U V ↔
      ∀ p : Equiv.Perm ι, (∀ j, ∃ k, U (p j) k * V k j ≠ 0) →
        ∀ j l k, U (p j) k * V k j ≠ 0 → U (p l) k * V k l ≠ 0 → j = l := by
  classical
  constructor
  · intro h p hex j l k hj hl
    let f (m : ι) := if m = j ∨ m = l then k else (hex m).choose
    have hvalid (m : ι) : U (p m) (f m) * V (f m) m ≠ 0 := by
      by_cases hm : m = j ∨ m = l
      · rw [show f m = k from if_pos hm]
        rcases hm with rfl | rfl
        · exact hj
        · exact hl
      · rw [show f m = (hex m).choose from if_neg hm]
        exact (hex m).choose_spec
    exact (h p f hvalid).1 (by simp [f])
  · intro h p f hf
    refine (Fintype.bijective_iff_injective_and_card f).mpr ⟨?_, rfl⟩
    intro j l he
    exact h p (fun m => ⟨f m, hf m⟩) j l (f j) (hf j)
      (by simpa only [he] using hf l)

/-- Additive cut labels can certify the intermediate-label condition. For two
block layers, each intermediate label gives an edge between its two blocks.
If this graph is a forest, remove the edge for `k`. On the component containing
its left endpoint use the left block indicator and the negative right block
indicator. Their sum on intermediate labels is the indicator of `k`. -/
theorem bijectivePermutationPaths_of_cut_labels (U V : Matrix ι ι ℂ)
    (hcut : ∀ k : ι, ∃ x y : ι → ℝ,
      (∀ i j, U i j ≠ 0 → x i = x j) ∧
      (∀ i j, V i j ≠ 0 → y i = y j) ∧
      (∀ i, x i + y i = if i = k then 1 else 0)) : BijectivePermutationPaths U V := by
  intro p f hf
  refine (Fintype.bijective_iff_surjective_and_card f).mpr ⟨?_, rfl⟩
  intro k
  obtain ⟨x, y, hx, hy, hk⟩ := hcut k
  by_contra hmissing
  have hne (j : ι) : f j ≠ k := fun hj => hmissing ⟨j, hj⟩
  have hsx : (∑ j, x (f j)) = ∑ j, x j := calc
    _ = ∑ j, x (p j) :=
      Finset.sum_congr rfl fun j _ => (hx (p j) (f j) (left_ne_zero_of_mul (hf j))).symm
    _ = _ := Equiv.sum_comp p x
  have hsy : (∑ j, y (f j)) = ∑ j, y j :=
    Finset.sum_congr rfl fun j _ => hy (f j) j (right_ne_zero_of_mul (hf j))
  have hzero : (∑ j, (x (f j) + y (f j))) = 0 := by
    simp only [hk, hne, if_false, Finset.sum_const_zero]
  have hone : (∑ j, (x j + y j)) = 1 := by
    simp only [hk, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_add_distrib, hsx, hsy, ← Finset.sum_add_distrib, hone] at hzero
  exact one_ne_zero hzero

/-- If two layers act on single blocks meeting in at most one label and
are diagonal elsewhere, every supported full assignment uses each
intermediate label exactly once. -/
theorem bijectivePermutationPaths_of_single_overlap (U V : Matrix ι ι ℂ)
    (A B : Finset ι) (k : ι) (hAB : ∀ i, i ∈ A → i ∈ B → i = k)
    (hUA : ∀ i j, U i j ≠ 0 → (i ∈ A ↔ j ∈ A) ∧ (i ∉ A → i = j))
    (hVB : ∀ i j, V i j ≠ 0 → (i ∈ B ↔ j ∈ B) ∧ (i ∉ B → i = j)) :
    BijectivePermutationPaths U V := by
  apply bijectivePermutationPaths_of_cut_labels
  intro l
  let δ (i : ι) : ℝ := if i = l then 1 else 0
  have hδ {S : Finset ι} (hl : l ∉ S) {i j : ι}
      (hij : (i ∈ S ↔ j ∈ S) ∧ (i ∉ S → i = j)) : δ i = δ j := by
    by_cases hi : i ∈ S
    · have hj := hij.1.mp hi
      have hil : i ≠ l := fun h => hl (h ▸ hi)
      have hjl : j ≠ l := fun h => hl (h ▸ hj)
      simp [δ, hil, hjl]
    · rw [hij.2 hi]
  by_cases hlA : l ∈ A
  · by_cases hlB : l ∈ B
    · let x (i : ι) : ℝ := if i ∈ A then 1 else 0
      let y (i : ι) : ℝ := if i ∈ A ∧ i ≠ l then -1 else 0
      refine ⟨x, y, ?_, ?_, ?_⟩
      · intro i j hij
        simp only [x, (hUA i j hij).1]
      · intro i j hij
        obtain ⟨hm, he⟩ := hVB i j hij
        by_cases hi : i ∈ B
        · have hj : j ∈ B := hm.mp hi
          have hz (m : ι) (hm : m ∈ B) : ¬(m ∈ A ∧ m ≠ l) :=
            fun ⟨hA, hne⟩ => hne ((hAB m hA hm).trans (hAB l hlA hlB).symm)
          simp [y, hz i hi, hz j hj]
        · rw [he hi]
      · intro i
        by_cases hi : i = l
        · simp [x, y, hi, hlA]
        · by_cases ha : i ∈ A <;> simp [x, y, hi, ha]
    · exact ⟨0, δ, fun _ _ _ => rfl, fun i j h => hδ hlB (hVB i j h),
        fun i => zero_add (δ i)⟩
  · exact ⟨δ, 0, fun i j h => hδ hlA (hUA i j h), fun _ _ _ => rfl,
      fun i => add_zero (δ i)⟩

private theorem leibnizTerm_mul_of_bijective_paths (U V : Matrix ι ι ℂ)
    (hpaths : BijectivePermutationPaths U V) (p : Equiv.Perm ι) :
    leibnizTerm (U * V) p = ∑ q, leibnizTerm U (p * q⁻¹) * leibnizTerm V q := by
  classical
  let F (f : ι → ι) := ∏ j, U (p j) (f j) * V (f j) j
  let e : Equiv.Perm ι ↪ (ι → ι) :=
    ⟨fun q => q, fun _ _ he => Equiv.ext (congrFun he)⟩
  have hprod : (∏ j, (U * V) (p j) j) = ∑ q : Equiv.Perm ι, F (e q) := by
    simp only [Matrix.mul_apply, Fintype.prod_sum]
    change (∑ f : ι → ι, F f) = ∑ q : Equiv.Perm ι, F (e q)
    rw [← Finset.sum_map (Finset.univ : Finset (Equiv.Perm ι)) e F]
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro f _ hf
    by_contra hn
    have hnonzero (j : ι) : U (p j) (f j) * V (f j) j ≠ 0 :=
      fun hj => hn (Finset.prod_eq_zero (Finset.mem_univ j) hj)
    let q := Equiv.ofBijective f (hpaths p f hnonzero)
    exact hf (Finset.mem_map.mpr ⟨q, Finset.mem_univ _, rfl⟩)
  rw [leibnizTerm, hprod, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  let r := p * q⁻¹
  have hr : r * q = p := by simp [r, mul_assoc]
  have hsign : ((Equiv.Perm.sign p : ℤ) : ℂ) =
      ((Equiv.Perm.sign r : ℤ) : ℂ) * ((Equiv.Perm.sign q : ℤ) : ℂ) := by
    rw [← hr]
    simp only [Equiv.Perm.sign_mul, Units.val_mul, Int.cast_mul]
  have hcomp (j : ι) : r (q j) = p j := by rw [← Equiv.Perm.mul_apply, hr]
  have hF : F (e q) = (∏ j, U (r j) j) * (∏ j, V (q j) j) := by
    change (∏ j, U (p j) (q j) * V (q j) j) = _
    rw [Finset.prod_mul_distrib, ← Equiv.prod_comp q (fun j => U (r j) j)]
    simp only [hcomp]
  change ((Equiv.Perm.sign p : ℤ) : ℂ) * F (e q) =
    leibnizTerm U r * leibnizTerm V q
  rw [hsign, hF, leibnizTerm, leibnizTerm]
  ring

/-- The complex signed weights of two layers satisfy the permutation
convolution when every supported intermediate assignment is bijective. -/
theorem signedWeight_mul_of_bijective_paths (U V : Matrix ι ι ℂ)
    (hpaths : BijectivePermutationPaths U V) (p : Equiv.Perm ι) :
    signedWeight (U * V) p = ∑ q, signedWeight U (p * q⁻¹) * signedWeight V q := by
  rw [signedWeight, Matrix.det_mul, leibnizTerm_mul_of_bijective_paths U V hpaths, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro q _
  simp only [signedWeight, div_mul_div_comm]

omit [DecidableEq ι] in
private theorem matchingProduct_mul_reindex (a b : ι → ℂ) (p q : Equiv.Perm ι) :
    matchingProduct a b (p * q) = matchingProduct a (b ∘ q.symm) p := by
  unfold matchingProduct
  rw [← Equiv.prod_comp q (fun j => a (p j) + (b ∘ q.symm) j)]
  simp only [Equiv.Perm.mul_apply, Function.comp_apply, Equiv.symm_apply_apply]

/-- The left layer only needs one law for the second spectra obtained
from permutations in the signed support of the right layer. -/
theorem determinantValue_mul_of_bijective_paths_on_support {κ : Type*} [Fintype κ]
    (a b : ι → ℂ) (U V : Matrix ι ι ℂ)
    (hU : IsUnitary U) (hV : IsUnitary V) (hpaths : BijectivePermutationPaths U V)
    (P : κ → Equiv.Perm ι) (w : κ → ℝ) (hw : ∀ q, signedWeight V q ≠ 0 →
      (∑ t, (w t : ℂ) * matchingProduct a (b ∘ q.symm) (P t)) =
        determinantValue a (b ∘ q.symm) U) :
    determinantValue a b (U * V) = ∑ t, (w t : ℂ) * determinantValue (a ∘ P t) b V := by
  have hUadj : IsUnitary Uᴴ := ⟨by simpa only [Matrix.conjTranspose_conjTranspose] using hU.2,
    by simpa only [Matrix.conjTranspose_conjTranspose] using hU.1⟩
  have hUV : IsUnitary (U * V) := by
    simpa only [Matrix.conjTranspose_conjTranspose] using relative_unitary Uᴴ V hUadj hV
  calc
    _ = ∑ p : Equiv.Perm ι, ∑ q : Equiv.Perm ι,
        (signedWeight U (p * q⁻¹) * signedWeight V q) * matchingProduct a b p := by
      rw [← signed_determinant a b (U * V) hUV]
      simp_rw [signedWeight_mul_of_bijective_paths U V hpaths, Finset.sum_mul]
    _ = ∑ q : Equiv.Perm ι, signedWeight V q * determinantValue a (b ∘ q.symm) U := by
      simp_rw [← signed_determinant a _ U hU, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q _
      rw [← Equiv.sum_comp (Equiv.mulRight q)
        (fun p => (signedWeight U (p * q⁻¹) * signedWeight V q) * matchingProduct a b p)]
      apply Finset.sum_congr rfl
      intro p _
      change (signedWeight U ((p * q) * q⁻¹) * signedWeight V q) * matchingProduct a b (p * q) = _
      rw [show (p * q) * q⁻¹ = p by simp [mul_assoc], matchingProduct_mul_reindex]
      ring
    _ = ∑ q : Equiv.Perm ι, signedWeight V q *
        (∑ t, (w t : ℂ) * matchingProduct a (b ∘ q.symm) (P t)) := by
      apply Finset.sum_congr rfl
      intro q _
      by_cases hq : signedWeight V q = 0
      · simp [hq]
      · rw [hw q hq]
    _ = _ := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t _
      rw [← signed_determinant (a ∘ P t) b V hV, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      rw [← matchingProduct_mul_reindex a b (P t) q]
      change signedWeight V q * ((w t : ℂ) * matchingProduct a b (P t * q)) =
        (w t : ℂ) * (signedWeight V q * matchingProduct a b (P t * q))
      ring

/-- A law for the left layer at a fixed first spectrum expresses the product
determinant as an average of determinants for the right layer. -/
theorem determinantValue_mul_of_bijective_paths (a b : ι → ℂ) (U V : Matrix ι ι ℂ)
    (hU : IsUnitary U) (hV : IsUnitary V) (hpaths : BijectivePermutationPaths U V)
    (w : Equiv.Perm ι → ℝ) (hw : ∀ c, weightedMatchingValue a c w = determinantValue a c U) :
    determinantValue a b (U * V) = ∑ p, (w p : ℂ) * determinantValue (a ∘ p) b V :=
  determinantValue_mul_of_bijective_paths_on_support a b U V hU hV hpaths id w
    (fun q _ => hw (b ∘ q.symm))

/-- It suffices that the left layer has one law for all second spectra and
that the right layer satisfies inclusion for each first spectrum in that law. -/
theorem holds_mul_of_bijective_paths (a b : ι → ℂ) (U V : Matrix ι ι ℂ)
    (hU : IsUnitary U) (hV : IsUnitary V) (hpaths : BijectivePermutationPaths U V)
    (hcommon : HasCommonWeights a U) (hright : ∀ p : Equiv.Perm ι, Holds (a ∘ p) b V) :
    Holds a b (U * V) := by
  obtain ⟨w, hw, hsum, hvalue⟩ := hcommon
  unfold Holds
  rw [determinantValue_mul_of_bijective_paths a b U V hU hV hpaths w hvalue]
  simp_rw [← Complex.real_smul]
  apply (convex_convexHull ℝ _).sum_mem (fun p _ => hw p) hsum
  intro p _
  have h := hright p
  unfold Holds at h
  apply convexHull_mono _ h
  rintro _ ⟨q, rfl⟩
  exact ⟨p * q, rfl⟩

/-- When both layers have partner-independent laws at the required first
spectra, the product also has one. The right law may depend on the left
permutation. A right law valid for every first spectrum can be used unchanged. -/
theorem commonWeights_mul_of_bijective_paths (a : ι → ℂ) (U V : Matrix ι ι ℂ)
    (hU : IsUnitary U) (hV : IsUnitary V) (hpaths : BijectivePermutationPaths U V)
    (hcommon : HasCommonWeights a U) (hright : ∀ p : Equiv.Perm ι, HasCommonWeights (a ∘ p) V) :
    HasCommonWeights a (U * V) := by
  obtain ⟨w, hw, hsum, hvalue⟩ := hcommon
  choose v hv hvs hve using hright
  refine ⟨fun r => ∑ p, w p * v p (p⁻¹ * r),
    fun r => Finset.sum_nonneg fun p _ => mul_nonneg (hw p) (hv p _), ?_, ?_⟩
  · rw [Finset.sum_comm]
    calc
      _ = ∑ p : Equiv.Perm ι, w p * (∑ q, v p q) := by
        simp_rw [← Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p _
        congr 1
        exact Equiv.sum_comp (Equiv.mulLeft p⁻¹) (v p)
      _ = 1 := by simpa only [hvs, mul_one] using hsum
  intro b
  rw [determinantValue_mul_of_bijective_paths a b U V hU hV hpaths w hvalue]
  unfold weightedMatchingValue
  simp_rw [Complex.ofReal_sum, Finset.sum_mul, Complex.ofReal_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  rw [← hve p b, weightedMatchingValue, Finset.mul_sum,
    ← Equiv.sum_comp (Equiv.mulLeft p)
      (fun r => ((w p : ℂ) * (v p (p⁻¹ * r) : ℂ)) * matchingProduct a b r)]
  apply Finset.sum_congr rfl
  intro q _
  change ((w p : ℂ) * (v p (p⁻¹ * (p * q)) : ℂ)) * matchingProduct a b (p * q) =
    (w p : ℂ) * ((v p q : ℂ) * matchingProduct a b (p * q))
  rw [show p⁻¹ * (p * q) = q by simp [← mul_assoc], mul_assoc]

end

end MOC
