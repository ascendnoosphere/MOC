import MOC.SubsetMarkerTest
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Roots

/-! Pair subset-image coordinates determine singleton coordinates in every
order greater than two. In order five these and normalization determine all
spectral objectives by complementary minors. -/

open Finset BigOperators Matrix

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private def imageIndicator (I J : Finset ι) (σ : Equiv.Perm ι) : ℝ :=
  if J.map σ.toEmbedding = I then 1 else 0

private theorem sum_imageIndicator (w : Equiv.Perm ι → ℝ) (I J : Finset ι) :
    (∑ σ, w σ * imageIndicator I J σ) =
    ∑ σ ∈ univ.filter (fun σ : Equiv.Perm ι => J.map σ.toEmbedding = I), w σ := by
  classical
  simp only [imageIndicator, Finset.sum_filter, mul_ite, mul_one, mul_zero]

/-- Count unordered source pairs containing `j` whose images contain `i`.
There are all possible companions when `σ j = i`, and exactly the one
companion `σ⁻¹ i` otherwise. The summation over companions lists each
unordered pair containing `j` exactly once. -/
theorem count_incident_pair_images (hcard : 2 ≤ Fintype.card ι) (i j : ι)
    (σ : Equiv.Perm ι) :
    (∑ l ∈ (univ : Finset ι).erase j,
      ∑ I ∈ (univ : Finset (Finset ι)).filter (fun I => I.card = 2 ∧ i ∈ I),
        (if ({j,l} : Finset ι).map σ.toEmbedding = I then (1 : ℝ) else 0)) =
      1 + ((Fintype.card ι : ℝ) - 2) * (if σ j = i then 1 else 0) := by
  classical
  have hinner (l : ι) (hl : l ∈ (univ : Finset ι).erase j) :
      (∑ I ∈ (univ : Finset (Finset ι)).filter (fun I => I.card = 2 ∧ i ∈ I),
        (if ({j,l} : Finset ι).map σ.toEmbedding = I then (1 : ℝ) else 0)) =
        if i = σ j ∨ i = σ l then 1 else 0 := by
    let S := (univ : Finset (Finset ι)).filter (fun I => I.card = 2 ∧ i ∈ I)
    let T := ({j,l} : Finset ι).map σ.toEmbedding
    have hcardT : T.card = 2 := by
      rw [show T = ({j,l} : Finset ι).map σ.toEmbedding from rfl, card_map]
      exact card_pair (Finset.mem_erase.mp hl).1.symm
    have he : T ∈ S ↔ i = σ j ∨ i = σ l := by
      change T ∈ univ.filter (fun I : Finset ι => I.card = 2 ∧ i ∈ I) ↔ _
      rw [Finset.mem_filter, hcardT]
      simp [T, Finset.map_insert, Finset.map_singleton]
    change (∑ I ∈ S, if T = I then (1 : ℝ) else 0) = _
    simp_rw [eq_comm (a := T)]
    simp only [Finset.sum_ite_eq', he]
  rw [Finset.sum_congr rfl (fun l hl => hinner l hl)]
  by_cases hij : σ j = i
  · simp only [hij, true_or, ite_true, mul_one, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ,
      Nat.cast_sub (by omega : 1 ≤ Fintype.card ι)]
    ring
  · have hne : σ.symm i ≠ j := by
      intro he
      apply hij
      rw [← he, σ.apply_symm_apply]
    have hfun (l : ι) : (if i = σ j ∨ i = σ l then (1 : ℝ) else 0) =
        if l = σ.symm i then 1 else 0 := by
      have hie : i = σ l ↔ l = σ.symm i := by
        constructor
        · intro h
          rw [h, σ.symm_apply_apply]
        · intro h
          rw [h, σ.apply_symm_apply]
      simp [Ne.symm hij, hie]
    simp_rw [hfun]
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ _⟩)]
    simp [hij]

/-- Summing the squared pair minors incident to a row and a column gives
one plus the squared entry times the matrix order minus two. The index
`l` lists the column pairs containing `j` exactly once. -/
theorem sum_incident_pair_minorSq (hcard : 2 ≤ Fintype.card ι)
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) (i j : ι) :
    (∑ l ∈ (univ : Finset ι).erase j,
      ∑ I ∈ (univ : Finset (Finset ι)).filter (fun I => I.card = 2 ∧ i ∈ I),
        subsetMinorSq U I {j,l}) =
      1 + ((Fintype.card ι : ℝ) - 2) * Complex.normSq (U i j) := by
  classical
  let js := (univ : Finset ι).erase j
  let Is := (univ : Finset (Finset ι)).filter (fun I => I.card = 2 ∧ i ∈ I)
  let w := realSignedWeight U
  have hminor (I J : Finset ι) : subsetMinorSq U I J = ∑ σ, w σ * imageIndicator I J σ := by
    rw [sum_imageIndicator]
    have h := congrArg Complex.re (sum_signedWeight_image_eq_subsetMinorSq U hU I J)
    simpa only [w, realSignedWeight, Complex.re_sum, Complex.ofReal_re] using h.symm
  have hcount (σ : Equiv.Perm ι) :
      (∑ l ∈ js, ∑ I ∈ Is, imageIndicator I {j,l} σ) =
        1 + ((Fintype.card ι : ℝ) - 2) * (if σ j = i then 1 else 0) :=
    count_incident_pair_images hcard i j σ
  change (∑ l ∈ js, ∑ I ∈ Is, subsetMinorSq U I {j,l}) = _
  calc
    _ = ∑ σ, w σ * (∑ l ∈ js, ∑ I ∈ Is, imageIndicator I {j,l} σ) := by
      simp_rw [hminor, Finset.mul_sum]
      rw [Finset.sum_comm (s := univ) (t := js) (f := fun σ l =>
        ∑ I ∈ Is, w σ * imageIndicator I {j,l} σ)]
      apply Finset.sum_congr rfl
      intro l _
      exact Finset.sum_comm
    _ = _ := by
      simp_rw [hcount, mul_add, mul_one, Finset.sum_add_distrib]
      rw [show (∑ σ, w σ) = 1 from sum_realSignedWeight U hU]
      congr 1
      rw [← marginal_realSignedWeight U hU i j, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ _
      by_cases hσ : σ j = i <;> simp [w, hσ, mul_comm]

omit [Fintype ι] in
private theorem indicator_singleton (i j : ι) (σ : Equiv.Perm ι) :
    imageIndicator {i} {j} σ = if σ j = i then 1 else 0 := by
  simp [imageIndicator]

/-- In order greater than two, matching pair subset-image masses and the
total mass forces matching every singleton mass. The weights may be signed. -/
theorem singleton_image_mass_eq_of_pair_image_mass_eq (hcard : 2 < Fintype.card ι)
    (w v : Equiv.Perm ι → ℝ) (hMass : ∑ σ, w σ = ∑ σ, v σ)
    (hPair : ∀ I J : Finset ι, I.card = 2 → J.card = 2 →
      ∑ σ ∈ univ.filter (fun σ : Equiv.Perm ι => J.map σ.toEmbedding = I), w σ =
      ∑ σ ∈ univ.filter (fun σ : Equiv.Perm ι => J.map σ.toEmbedding = I), v σ)
    (i j : ι) :
    ∑ σ ∈ univ.filter (fun σ : Equiv.Perm ι => ({j} : Finset ι).map σ.toEmbedding = {i}), w σ =
    ∑ σ ∈ univ.filter (fun σ : Equiv.Perm ι => ({j} : Finset ι).map σ.toEmbedding = {i}), v σ := by
  classical
  let js := (univ : Finset ι).erase j
  let Is := (univ : Finset (Finset ι)).filter (fun I => I.card = 2 ∧ i ∈ I)
  let c := (Fintype.card ι : ℝ) - 2
  have hc : c ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hcard.ne')
  have hEq : (∑ σ, w σ * ∑ l ∈ js, ∑ I ∈ Is, imageIndicator I {j,l} σ) =
      ∑ σ, v σ * ∑ l ∈ js, ∑ I ∈ Is, imageIndicator I {j,l} σ := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm (s := univ) (t := js) (f := fun σ l =>
      ∑ I ∈ Is, w σ * imageIndicator I {j,l} σ),
      Finset.sum_comm (s := univ) (t := js) (f := fun σ l =>
      ∑ I ∈ Is, v σ * imageIndicator I {j,l} σ)]
    apply Finset.sum_congr rfl
    intro l hl
    rw [Finset.sum_comm (s := univ) (t := Is) (f := fun σ I => w σ * imageIndicator I {j,l} σ),
      Finset.sum_comm (s := univ) (t := Is) (f := fun σ I => v σ * imageIndicator I {j,l} σ)]
    apply Finset.sum_congr rfl
    intro I hI
    rw [sum_imageIndicator, sum_imageIndicator]
    exact hPair I {j,l} (Finset.mem_filter.mp hI).2.1
      (card_pair (Finset.mem_erase.mp hl).1.symm)
  have hFor (σ : Equiv.Perm ι) :
      (∑ l ∈ js, ∑ I ∈ Is, imageIndicator I {j,l} σ) =
        1 + c * imageIndicator {i} {j} σ := by
    rw [indicator_singleton]
    exact count_incident_pair_images hcard.le i j σ
  simp_rw [hFor, mul_add, mul_one, mul_left_comm _ c, Finset.sum_add_distrib, ← Finset.mul_sum] at hEq
  rw [hMass, add_right_inj] at hEq
  have hsingle := mul_left_cancel₀ hc hEq
  rw [sum_imageIndicator, sum_imageIndicator] at hsingle
  exact hsingle

/-- Pair-image coordinates already encode normalization, by summing the
target pairs for any one source pair. -/
theorem mass_eq_of_pair_image_mass_eq (hcard : 2 ≤ Fintype.card ι)
    (w v : Equiv.Perm ι → ℝ)
    (hPair : ∀ I J : Finset ι, I.card = 2 → J.card = 2 →
      ∑ σ ∈ univ.filter (fun σ : Equiv.Perm ι => J.map σ.toEmbedding = I), w σ =
      ∑ σ ∈ univ.filter (fun σ : Equiv.Perm ι => J.map σ.toEmbedding = I), v σ) :
    ∑ σ, w σ = ∑ σ, v σ := by
  classical
  obtain ⟨J, _, hj⟩ := exists_subset_card_eq
    (by simpa using hcard : 2 ≤ (univ : Finset ι).card)
  let Is := (univ : Finset (Finset ι)).filter fun I => I.card = 2
  have hOne (σ : Equiv.Perm ι) :
      ∑ I ∈ Is, imageIndicator I J σ = 1 := by
    unfold imageIndicator
    simp_rw [eq_comm (a := J.map σ.toEmbedding)]
    simp [Finset.sum_ite_eq', Is, Finset.card_map, hj]
  have hSum (a : Equiv.Perm ι → ℝ) :
      (∑ I ∈ Is,
        ∑ σ ∈ univ.filter (fun σ : Equiv.Perm ι => J.map σ.toEmbedding = I), a σ) =
        ∑ σ, a σ := by
    simp_rw [← sum_imageIndicator]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hOne, mul_one]
  rw [← hSum w, ← hSum v]
  apply Finset.sum_congr rfl
  intro I hi
  exact hPair I J (Finset.mem_filter.mp hi).2 hj

/-- In orders three through five, two unitary matrices with the same
squared pair minors have the same squared minors in every size. -/
theorem subsetMinorSq_eq_of_pair_tables_eq (hmin : 2 < Fintype.card ι)
    (hmax : Fintype.card ι ≤ 5) (U V : Matrix ι ι ℂ) (hU : IsUnitary U) (hV : IsUnitary V)
    (hpair : ∀ I J : Finset ι, I.card = 2 → J.card = 2 →
      subsetMinorSq U I J = subsetMinorSq V I J) (I J : Finset ι) :
    subsetMinorSq U I J = subsetMinorSq V I J := by
  classical
  have hsingle (i j : ι) : Complex.normSq (U i j) = Complex.normSq (V i j) := by
    have hU' := sum_incident_pair_minorSq hmin.le U hU i j
    have hV' := sum_incident_pair_minorSq hmin.le V hV i j
    have hsum : (∑ l ∈ (univ : Finset ι).erase j,
        ∑ K ∈ (univ : Finset (Finset ι)).filter (fun K => K.card = 2 ∧ i ∈ K),
          subsetMinorSq U K {j,l}) =
        ∑ l ∈ (univ : Finset ι).erase j,
          ∑ K ∈ (univ : Finset (Finset ι)).filter (fun K => K.card = 2 ∧ i ∈ K),
            subsetMinorSq V K {j,l} := by
      apply Finset.sum_congr rfl
      intro l hl
      apply Finset.sum_congr rfl
      intro K hK
      exact hpair K {j,l} (Finset.mem_filter.mp hK).2.1
        (Finset.card_pair (Finset.mem_erase.mp hl).1.symm)
    rw [hsum, hV'] at hU'
    have hpos : (2 : ℝ) < Fintype.card ι := by exact_mod_cast hmin
    exact mul_left_cancel₀ (sub_ne_zero.mpr hpos.ne') (add_left_cancel hU'.symm)
  have hempty (W : Matrix ι ι ℂ) (hW : IsUnitary W) : subsetMinorSq W ∅ ∅ = 1 := by
    apply Complex.ofReal_injective
    rw [← sum_signedWeight_image_eq_subsetMinorSq W hW]
    simpa using sum_signedWeight W (det_ne_zero_of_unitary hW)
  have hsmall (K L : Finset ι) (hKL : K.card = L.card) (hK : K.card ≤ 2) :
      subsetMinorSq U K L = subsetMinorSq V K L := by
    rcases (show K.card = 0 ∨ K.card = 1 ∨ K.card = 2 by omega) with hk | hk | hk
    · obtain rfl := Finset.card_eq_zero.mp hk
      obtain rfl := Finset.card_eq_zero.mp (hKL.symm.trans hk)
      rw [hempty U hU, hempty V hV]
    · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hk
      obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp (hKL.symm.trans hk)
      rw [subsetMinorSq_singleton U hU, subsetMinorSq_singleton V hV, hsingle]
    · exact hpair K L hk (hKL.symm.trans hk)
  by_cases hIJ : I.card = J.card
  · by_cases hI : I.card ≤ 2
    · exact hsmall I J hIJ hI
    · rw [← subsetMinorSq_compl U hU I J, ← subsetMinorSq_compl V hV I J]
      exact hsmall Iᶜ Jᶜ (by rw [Finset.card_compl, Finset.card_compl, hIJ])
        (by rw [Finset.card_compl]; omega)
  · simp [subsetMinorSq, hIJ]

/-- The squared pair minors determine the determinant for all pairs of
complex spectra in orders three through five. -/
theorem determinantValue_eq_of_pair_tables_eq (hmin : 2 < Fintype.card ι)
    (hmax : Fintype.card ι ≤ 5) (a b : ι → ℂ) (U V : Matrix ι ι ℂ)
    (hU : IsUnitary U) (hV : IsUnitary V)
    (hpair : ∀ I J : Finset ι, I.card = 2 → J.card = 2 →
      subsetMinorSq U I J = subsetMinorSq V I J) :
    determinantValue a b U = determinantValue a b V := by
  rw [determinantValue_eq_sum_subsetMinors a b U hU,
    determinantValue_eq_sum_subsetMinors a b V hV]
  simp_rw [subsetMinorSq_eq_of_pair_tables_eq hmin hmax U V hU hV hpair]

/-- For order five, normalization and doubleton image coordinates suffice
for the complete squared-minor table, for a fixed arbitrary real law. -/
theorem orderFive_all_minors_of_pair_images (U : Matrix (Fin 5) (Fin 5) ℂ) (hU : IsUnitary U)
    (w : Equiv.Perm (Fin 5) → ℝ) (hMass : ∑ σ, w σ = 1)
    (hPair : ∀ I J : Finset (Fin 5), I.card = 2 → J.card = 2 →
      (∑ σ ∈ univ.filter (fun σ : Equiv.Perm (Fin 5) => J.map σ.toEmbedding = I), w σ) =
        subsetMinorSq U I J) :
    ∀ I J : Finset (Fin 5),
      (∑ σ ∈ univ.filter (fun σ : Equiv.Perm (Fin 5) => J.map σ.toEmbedding = I), w σ) =
        subsetMinorSq U I J := by
  classical
  let v := realSignedWeight U
  have hV : ∀ I J : Finset (Fin 5),
      (∑ σ ∈ univ.filter (fun σ : Equiv.Perm (Fin 5) => J.map σ.toEmbedding = I), v σ) =
        subsetMinorSq U I J := by
    intro I J
    simpa only [v, realSignedWeight, Complex.re_sum, Complex.ofReal_re] using
      congrArg Complex.re (sum_signedWeight_image_eq_subsetMinorSq U hU I J)
  have hP : ∀ I J : Finset (Fin 5), I.card = 2 → J.card = 2 →
      (∑ σ ∈ univ.filter (fun σ : Equiv.Perm (Fin 5) => J.map σ.toEmbedding = I), w σ) =
      ∑ σ ∈ univ.filter (fun σ : Equiv.Perm (Fin 5) => J.map σ.toEmbedding = I), v σ := by
    intro I J hi hj
    rw [hV]
    exact hPair I J hi hj
  have hM : ∑ σ, w σ = ∑ σ, v σ := hMass.trans (sum_realSignedWeight U hU).symm
  have hsmall : ∀ I J : Finset (Fin 5), I.card = J.card →
      I.card ≤ Fintype.card (Fin 5) / 2 →
      subsetMinorSq U I J =
      ∑ σ ∈ univ.filter (fun σ : Equiv.Perm (Fin 5) => J.map σ.toEmbedding = I), w σ := by
    intro I J hij hi
    have hc : I.card ≤ 2 := by simpa using hi
    rcases (show I.card = 0 ∨ I.card = 1 ∨ I.card = 2 by omega) with h | h | h
    · have hI : I = ∅ := Finset.card_eq_zero.mp h
      have hJ : J = ∅ := Finset.card_eq_zero.mp (hij.symm.trans h)
      rw [← hV, hI, hJ]
      simpa using hM.symm
    · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp h
      obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp (hij.symm.trans h)
      rw [← hV]
      exact (singleton_image_mass_eq_of_pair_image_mass_eq (by simp) w v hM hP i j).symm
    · exact (hPair I J h (hij.symm.trans h)).symm
  intro I J
  exact (indexed_minor_law_of_small U hU id w (by simpa using hsmall) I J).symm

/-- The projection on pair markers alone, together with normalization, is
equivalent to preserving every complex spectral objective in order five. -/
theorem orderFive_weighted_spectra_eq_all_iff_pair_images
    (U : Matrix (Fin 5) (Fin 5) ℂ) (hU : IsUnitary U) (w : Equiv.Perm (Fin 5) → ℝ) :
    (∀ a b : Fin 5 → ℂ, weightedMatchingValue a b w = determinantValue a b U) ↔
    (∑ σ, w σ = 1) ∧
      ∀ I J : Finset (Fin 5), I.card = 2 → J.card = 2 →
        (∑ σ ∈ univ.filter (fun σ : Equiv.Perm (Fin 5) => J.map σ.toEmbedding = I), w σ) =
          subsetMinorSq U I J := by
  classical
  constructor
  · intro h
    constructor
    · have he := h (fun _ => 1) (fun _ => 0)
      apply Complex.ofReal_injective
      simpa [weightedMatchingValue, matchingProduct, determinantValue, Matrix.diagonal_one,
        Complex.ofReal_sum] using he
    · intro I J hi hj
      have he := h (fun i => if i ∈ I then 0 else 1) (fun j => if j ∈ J then 1 else 0)
      rw [weightedMatchingValue_subset_marker w I J (hi.trans hj.symm),
        determinantValue_subset_marker U hU I J (hi.trans hj.symm)] at he
      exact Complex.ofReal_injective he
  · rintro ⟨hMass, hPair⟩ a b
    have hAll := orderFive_all_minors_of_pair_images U hU w hMass hPair
    exact determinantValue_eq_sum_of_indexed_minor_law a b U hU id w
      (fun I J => (hAll I J).symm)

/-- In order five, the doubleton image tests alone are equivalent to
preserving all spectral objectives with the same signed or unsigned weights. -/
theorem orderFive_weighted_spectra_eq_all_iff_doubleton_images
    (U : Matrix (Fin 5) (Fin 5) ℂ) (hU : IsUnitary U) (w : Equiv.Perm (Fin 5) → ℝ) :
    (∀ a b : Fin 5 → ℂ, weightedMatchingValue a b w = determinantValue a b U) ↔
      ∀ I J : Finset (Fin 5), I.card = 2 → J.card = 2 →
        (∑ σ ∈ univ.filter (fun σ : Equiv.Perm (Fin 5) => J.map σ.toEmbedding = I), w σ) =
          subsetMinorSq U I J := by
  classical
  rw [orderFive_weighted_spectra_eq_all_iff_pair_images U hU w]
  constructor
  · exact And.right
  · intro hPair
    refine ⟨?_, hPair⟩
    rw [← sum_realSignedWeight U hU]
    apply mass_eq_of_pair_image_mass_eq (by simp)
    intro I J hi hj
    rw [hPair I J hi hj]
    have hterm := congrArg Complex.re (sum_signedWeight_image_eq_subsetMinorSq U hU I J)
    simpa only [realSignedWeight, Complex.re_sum, Complex.ofReal_re] using hterm.symm

set_option maxRecDepth 1500 in
/-- Exact equality as a complex polynomial, not only pointwise equality:
pair images prescribe the whole determinant whenever each spectral entry
is any polynomial in a common parameter. -/
theorem orderFive_weighted_polynomial_identity
    (U : Matrix (Fin 5) (Fin 5) ℂ) (hU : IsUnitary U) (w : Equiv.Perm (Fin 5) → ℝ)
    (hPair : ∀ I J : Finset (Fin 5), I.card = 2 → J.card = 2 →
      (∑ σ ∈ univ.filter (fun σ : Equiv.Perm (Fin 5) => J.map σ.toEmbedding = I), w σ) =
        subsetMinorSq U I J)
    (a b : Fin 5 → Polynomial ℂ) :
    (∑ σ : Equiv.Perm (Fin 5), Polynomial.C (w σ : ℂ) * ∏ j, (a (σ j) + b j)) =
      (diagonal a + U.map Polynomial.C * diagonal b * Uᴴ.map Polynomial.C).det := by
  letI : Infinite ℂ := Infinite.of_injective (fun n : ℕ => (n : ℂ)) Nat.cast_injective
  apply Polynomial.funext
  intro t
  let f : Polynomial ℂ →+* ℂ := Polynomial.evalRingHom t
  change f _ = f _
  rw [map_sum, RingHom.map_det]
  simp_rw [map_mul, map_prod, map_add]
  have hf (z : ℂ) : f (Polynomial.C z) = z := Polynomial.eval_C
  have hd (s : Fin 5 → Polynomial ℂ) :
      f.mapMatrix (diagonal s) = diagonal (fun i => f (s i)) :=
    Matrix.diagonal_map (map_zero f)
  have hc (M : Matrix (Fin 5) (Fin 5) ℂ) : f.mapMatrix (M.map Polynomial.C) = M := by
    ext i j
    exact hf _
  simp only [map_add, map_mul, hf, hd, hc]
  simpa only [weightedMatchingValue, matchingProduct, determinantValue] using
    (orderFive_weighted_spectra_eq_all_iff_doubleton_images U hU w).mpr hPair
    (fun i => f (a i)) (fun i => f (b i))

end

end MOC
