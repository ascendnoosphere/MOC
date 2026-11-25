import MOC.FourCoincidence
import MOC.PolynomialContact
import MOC.RankSum
import MOC.Support
import Mathlib.LinearAlgebra.Matrix.Polynomial

/-! The quartic term of a paired two-by-two spectral shift has a positive
coefficient law. A full-rank shift grows a fully crossing matching on any
determinant component that maps onto a horizontal ray. -/

open BigOperators Filter Matrix Polynomial
open scoped Convex Topology

namespace MOC

noncomputable section

/-- The entries selected for a simultaneous spectral shift. -/
def pairedShiftMask (I : Finset (Fin 4)) (k : Fin 4) : ℂ :=
  if k ∈ I then 1 else 0

/-- Shift each selected entry by the same complex amount. -/
def pairedShiftSpectrum (a : Fin 4 → ℂ) (I : Finset (Fin 4)) (z : ℂ) (k : Fin 4) : ℂ :=
  a k + z * pairedShiftMask I k

@[simp] theorem pairedShiftSpectrum_zero (a : Fin 4 → ℂ) (I : Finset (Fin 4)) :
    pairedShiftSpectrum a I 0 = a := by
  funext k
  simp [pairedShiftSpectrum]

private theorem matchingProduct_mask_eq_zero_or_one (I J : Finset (Fin 4)) (hJ : J.card = 2)
    (σ : Equiv.Perm (Fin 4)) :
    matchingProduct (pairedShiftMask I) (fun k => -pairedShiftMask J k) σ = 0 ∨
      matchingProduct (pairedShiftMask I) (fun k => -pairedShiftMask J k) σ = 1 := by
  by_cases h : ∃ k, (σ k ∈ I ↔ k ∈ J)
  · obtain ⟨k, hk⟩ := h
    apply Or.inl
    unfold matchingProduct
    apply Finset.prod_eq_zero (Finset.mem_univ k)
    by_cases hj : k ∈ J
    · simp [pairedShiftMask, hj, hk.mpr hj]
    · have hi : σ k ∉ I := fun hi => hj (hk.mp hi)
      simp [pairedShiftMask, hj, hi]
  · apply Or.inr
    unfold matchingProduct
    have hf (k : Fin 4) :
        pairedShiftMask I (σ k) + -pairedShiftMask J k = if k ∈ J then -1 else 1 := by
      have hk : ¬ (σ k ∈ I ↔ k ∈ J) := fun he => h ⟨k, he⟩
      by_cases hj : k ∈ J
      · have hi : σ k ∉ I := fun hi => hk ⟨fun _ => hj, fun _ => hi⟩
        simp [pairedShiftMask, hj, hi]
      · have hi : σ k ∈ I := by
          by_contra hi
          exact hk ⟨fun hi' => (hi hi').elim, fun hj' => (hj hj').elim⟩
        simp [pairedShiftMask, hj, hi]
    simp_rw [hf]
    rw [Fintype.prod_ite_mem, Finset.prod_const, hJ]
    norm_num

private theorem holds_mask (I J : Finset (Fin 4)) (hI : I.card = 2) (hJ : J.card = 2)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    Holds (pairedShiftMask I) (fun k => -pairedShiftMask J k) U := by
  apply holds_of_support_balance _ _ U hU
  have hsI : spectralSupport (pairedShiftMask I) = I := by
    ext k
    by_cases hk : k ∈ I <;> simp [spectralSupport, pairedShiftMask, hk]
  have hsJ : spectralSupport (fun k => -pairedShiftMask J k) = J := by
    ext k
    by_cases hk : k ∈ J <;> simp [spectralSupport, pairedShiftMask, hk]
  simp only [hsI, hsJ, hI, hJ, Fintype.card_fin]

/-- The quartic coefficient of a balanced paired shift is real and in `[0,1]`. -/
theorem paired_shift_coefficient_mem_unit_interval (I J : Finset (Fin 4))
    (hI : I.card = 2) (hJ : J.card = 2) (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    ∃ c ∈ Set.Icc (0 : ℝ) 1,
      determinantValue (pairedShiftMask I) (fun k => -pairedShiftMask J k) U = (c : ℂ) := by
  have hsub : Set.range (matchingProduct (pairedShiftMask I) (fun k => -pairedShiftMask J k)) ⊆
      segment ℝ (0 : ℂ) 1 := by
    rintro _ ⟨σ, rfl⟩
    rcases matchingProduct_mask_eq_zero_or_one I J hJ σ with h | h
    · rw [h]
      exact left_mem_segment ℝ 0 1
    · rw [h]
      exact right_mem_segment ℝ 0 1
  have hmem := convexHull_min hsub (convex_segment (𝕜 := ℝ) (0 : ℂ) 1)
    (holds_mask I J hI hJ U hU)
  rw [segment_eq_image] at hmem
  obtain ⟨c, hc, he⟩ := hmem
  exact ⟨c, hc, by simpa only [smul_zero, zero_add, Complex.real_smul, mul_one] using he.symm⟩

/-- The support determinant as a polynomial of the paired shift amplitude. -/
def pairedShiftDetPolynomial (a b : Fin 4 → ℂ) (U : Matrix (Fin 4) (Fin 4) ℂ)
    (I J : Finset (Fin 4)) (η : ℂ) : ℂ[X] :=
  let A := diagonal (pairedShiftMask I) + U * diagonal (fun k => -pairedShiftMask J k) * Uᴴ
  let B := diagonal a + U * diagonal b * Uᴴ
  C η * ((X : ℂ[X]) • A.map C + B.map C).det

/-- A matching product as a polynomial of the paired shift amplitude. -/
def pairedShiftMatchingPolynomial (a b : Fin 4 → ℂ) (I J : Finset (Fin 4))
    (η : ℂ) (σ : Equiv.Perm (Fin 4)) : ℂ[X] :=
  C η * ∏ k, (X * C (pairedShiftMask I (σ k) + -pairedShiftMask J k) + C (a (σ k) + b k))

theorem pairedShiftDetPolynomial_degree_le (a b : Fin 4 → ℂ) (U : Matrix (Fin 4) (Fin 4) ℂ)
    (I J : Finset (Fin 4)) (η : ℂ) :
    (pairedShiftDetPolynomial a b U I J η).natDegree ≤ 4 := by
  let A := diagonal (pairedShiftMask I) + U * diagonal (fun k => -pairedShiftMask J k) * Uᴴ
  let B := diagonal a + U * diagonal b * Uᴴ
  change (C η * ((X : ℂ[X]) • A.map C + B.map C).det).natDegree ≤ 4
  exact natDegree_mul_le.trans (by
    simpa only [natDegree_C, zero_add, Fintype.card_fin] using (natDegree_det_X_add_C_le A B))

theorem pairedShiftDetPolynomial_coeff_four (a b : Fin 4 → ℂ) (U : Matrix (Fin 4) (Fin 4) ℂ)
    (I J : Finset (Fin 4)) (η : ℂ) :
    (pairedShiftDetPolynomial a b U I J η).coeff 4 =
      η * determinantValue (pairedShiftMask I) (fun k => -pairedShiftMask J k) U := by
  let A := diagonal (pairedShiftMask I) + U * diagonal (fun k => -pairedShiftMask J k) * Uᴴ
  let B := diagonal a + U * diagonal b * Uᴴ
  have hc := coeff_det_X_add_C_card A B
  simp only [Fintype.card_fin] at hc
  change (C η * ((X : ℂ[X]) • A.map C + B.map C).det).coeff 4 = η * A.det
  rw [coeff_C_mul, hc]

private theorem matching_linear_natDegree_le (x y : ℂ) :
    (X * C x + C y).natDegree ≤ 1 := by
  compute_degree

theorem pairedShiftMatchingPolynomial_degree_le (a b : Fin 4 → ℂ) (I J : Finset (Fin 4))
    (η : ℂ) (σ : Equiv.Perm (Fin 4)) :
    (pairedShiftMatchingPolynomial a b I J η σ).natDegree ≤ 4 := by
  let f (k : Fin 4) := X * C (pairedShiftMask I (σ k) + -pairedShiftMask J k) + C (a (σ k) + b k)
  have hf (k : Fin 4) : (f k).natDegree ≤ 1 := matching_linear_natDegree_le _ _
  change (C η * ∏ k, f k).natDegree ≤ 4
  apply natDegree_mul_le.trans
  simp only [natDegree_C, zero_add]
  exact (natDegree_prod_le Finset.univ f).trans (by
    calc
      _ ≤ ∑ _ : Fin 4, (1 : ℕ) := Finset.sum_le_sum fun k _ => hf k
      _ = 4 := by simp)

theorem pairedShiftMatchingPolynomial_coeff_four (a b : Fin 4 → ℂ) (I J : Finset (Fin 4))
    (η : ℂ) (σ : Equiv.Perm (Fin 4)) :
    (pairedShiftMatchingPolynomial a b I J η σ).coeff 4 =
      η * matchingProduct (pairedShiftMask I) (fun k => -pairedShiftMask J k) σ := by
  let f (k : Fin 4) := X * C (pairedShiftMask I (σ k) + -pairedShiftMask J k) + C (a (σ k) + b k)
  have he := coeff_prod_of_natDegree_le (s := Finset.univ) f 1
    (fun k _ => matching_linear_natDegree_le _ _)
  have hf (k : Fin 4) : (f k).coeff 1 = pairedShiftMask I (σ k) + -pairedShiftMask J k := by
    simp [f, coeff_add, coeff_mul_C]
  simp only [Finset.card_univ, Fintype.card_fin, mul_one, hf] at he
  change (C η * ∏ k, f k).coeff 4 = _
  rw [coeff_C_mul, he]
  rfl

theorem eval_pairedShiftMatchingPolynomial (a b : Fin 4 → ℂ) (I J : Finset (Fin 4))
    (η z : ℂ) (σ : Equiv.Perm (Fin 4)) :
    (pairedShiftMatchingPolynomial a b I J η σ).eval z =
      η * matchingProduct (pairedShiftSpectrum a I z) (pairedShiftSpectrum b J (-z)) σ := by
  simp only [pairedShiftMatchingPolynomial, eval_mul, eval_C, eval_prod, matchingProduct,
    pairedShiftSpectrum, eval_add, eval_X]
  congr 1
  apply Finset.prod_congr rfl
  intro k _
  ring

private theorem diagonal_pairedShiftSpectrum (a : Fin 4 → ℂ) (I : Finset (Fin 4)) (z : ℂ) :
    diagonal (pairedShiftSpectrum a I z) = diagonal a + z • diagonal (pairedShiftMask I) := by
  ext i j : 1
  by_cases h : i = j <;> simp [Matrix.diagonal_apply, pairedShiftSpectrum, h]

theorem eval_pairedShiftDetPolynomial (a b : Fin 4 → ℂ) (U : Matrix (Fin 4) (Fin 4) ℂ)
    (I J : Finset (Fin 4)) (η z : ℂ) :
    (pairedShiftDetPolynomial a b U I J η).eval z =
      η * determinantValue (pairedShiftSpectrum a I z) (pairedShiftSpectrum b J (-z)) U := by
  let A := diagonal (pairedShiftMask I) + U * diagonal (fun k => -pairedShiftMask J k) * Uᴴ
  let B := diagonal a + U * diagonal b * Uᴴ
  have hmat : ((((X : ℂ[X]) • A.map C + B.map C) : Matrix (Fin 4) (Fin 4) ℂ[X]).map
      (fun p => p.eval z)) = z • A + B := by
    ext i j : 1
    simp [Matrix.smul_apply]
    exact mul_comm _ _
  change (C η * ((X : ℂ[X]) • A.map C + B.map C).det).eval z = _
  rw [eval_mul, eval_C, Matrix.eval_det, Matrix.matPolyEquiv_eval_eq_map, hmat]
  unfold determinantValue
  rw [diagonal_pairedShiftSpectrum, diagonal_pairedShiftSpectrum]
  have hdiag : diagonal (fun k => -pairedShiftMask J k) = -diagonal (pairedShiftMask J) := by
    rw [Matrix.diagonal_neg]
  congr 1
  apply congrArg Matrix.det
  simp only [A, B, hdiag, smul_add, Matrix.mul_add, Matrix.add_mul, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.mul_neg, Matrix.neg_mul, smul_neg, neg_smul]
  abel

/-- Along a full-rank paired shift, an escaping determinant component grows a
fully crossing matching beyond any prescribed real support level. -/
theorem exists_large_crossing_matching_on_paired_component
    (a b : Fin 4 → ℂ) (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) (η : ℂ) (hη : η ≠ 0)
    (I J : Finset (Fin 4)) (hI : I.card = 2) (hJ : J.card = 2)
    (hD : determinantValue (pairedShiftMask I) (fun k => -pairedShiftMask J k) U ≠ 0)
    {V : Set ℂ} (hV : IsOpen V) (hVc : IsPreconnected V) {x : ℂ}
    (hx : (pairedShiftDetPolynomial a b U I J η).eval x ∈ V)
    (d T₀ H : ℝ) (hRay : ∀ t ≥ T₀, (t : ℂ) + (d : ℂ) * Complex.I ∈ V) :
    ∃ σ : Equiv.Perm (Fin 4), (∀ k, ¬ (σ k ∈ I ↔ k ∈ J)) ∧
      ∃ z ∈ connectedComponentIn
          ((fun w => (pairedShiftDetPolynomial a b U I J η).eval w) ⁻¹' V) x,
        H < (η * matchingProduct (pairedShiftSpectrum a I z) (pairedShiftSpectrum b J (-z)) σ).re := by
  let α := pairedShiftMask I
  let β := fun k => -pairedShiftMask J k
  obtain ⟨c, hc, hce⟩ := paired_shift_coefficient_mem_unit_interval I J hI hJ U hU
  have hcpos : 0 < c := lt_of_le_of_ne hc.1 fun h => hD (hce.trans (by rw [← h]; simp))
  obtain ⟨σ, hσ⟩ := (holds_iff_directional α β U).mp (holds_mask I J hI hJ U hU) 1
  have hσval : matchingProduct α β σ = 1 := by
    apply (matchingProduct_mask_eq_zero_or_one I J hJ σ).resolve_left
    intro h
    have hzero : matchingProduct α β σ = 0 := h
    have hcαβ : determinantValue α β U = (c : ℂ) := hce
    simp only [one_mul, hzero, hcαβ, Complex.ofReal_re, Complex.zero_re] at hσ
    exact not_le_of_gt hcpos hσ
  have hσcross (k : Fin 4) : ¬ (σ k ∈ I ↔ k ∈ J) := by
    intro hk
    have hz : α (σ k) + β k = 0 := by
      by_cases hj : k ∈ J
      · simp [α, β, pairedShiftMask, hj, hk.mpr hj]
      · have hi : σ k ∉ I := fun hi => hj (hk.mp hi)
        simp [α, β, pairedShiftMask, hj, hi]
    exact one_ne_zero (hσval.symm.trans (Finset.prod_eq_zero (Finset.mem_univ k) hz))
  let p := pairedShiftDetPolynomial a b U I J η
  let q := pairedShiftMatchingPolynomial a b I J η σ
  have hp₄ : p.coeff 4 = η * (c : ℂ) := by
    rw [pairedShiftDetPolynomial_coeff_four, hce]
  have hq₄ : q.coeff 4 = η := by
    rw [pairedShiftMatchingPolynomial_coeff_four, hσval, mul_one]
  have hc₀ : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hcpos.ne'
  have hpne : p.coeff 4 ≠ 0 := by
    rw [hp₄]
    exact mul_ne_zero hη hc₀
  have hpd : p.natDegree = 4 := le_antisymm (pairedShiftDetPolynomial_degree_le a b U I J η)
    (le_natDegree_of_ne_zero hpne)
  have hp : 0 < p.degree := by
    have hn : p ≠ 0 := by
      intro hn
      exact hpne (by rw [hn, coeff_zero])
    rw [degree_eq_natDegree hn, hpd]
    norm_num
  let r := q - C ((c⁻¹ : ℝ) : ℂ) * p
  have hr₄ : r.coeff 4 = 0 := by
    simp only [r, coeff_sub, coeff_C_mul, hq₄, hp₄, Complex.ofReal_inv]
    field_simp [hc₀] <;> ring
  have hrd : r.natDegree < p.natDegree := by
    rw [hpd]
    have hmul : (C ((c⁻¹ : ℝ) : ℂ) * p).natDegree ≤ 4 :=
      natDegree_mul_le.trans (by rw [natDegree_C, zero_add, hpd])
    have hrle : r.natDegree ≤ 4 := (natDegree_sub_le _ _).trans
      (max_le (pairedShiftMatchingPolynomial_degree_le a b I J η σ) hmul)
    apply lt_of_le_of_ne hrle
    intro h
    have hn : r.leadingCoeff = 0 := by rwa [leadingCoeff, h]
    have hz : r = 0 := leadingCoeff_eq_zero.mp hn
    rw [hz, natDegree_zero] at h
    norm_num at h
  obtain ⟨z, hz, hineq⟩ := exists_large_real_part_on_polynomial_component p q hp c⁻¹
    (inv_pos.mpr hcpos) hrd hV hVc hx d T₀ H hRay
  exact ⟨σ, hσcross, z, hz, by simpa only [q, eval_pairedShiftMatchingPolynomial] using hineq⟩

/-- A full-rank paired two-by-two shift adds a support contact across the
cut, preserving the strict violation and every initially distinct pair of
matching products. -/
theorem exists_new_contact_of_full_rank_paired_block
    (a b : Fin 4 → ℂ) (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) (η : ℂ)
    (I J : Finset (Fin 4)) (hI : I.card = 2) (hJ : J.card = 2)
    (hD : determinantValue (pairedShiftMask I) (fun k => -pairedShiftMask J k) U ≠ 0)
    (H : ℝ) (hmax : ∀ σ : Equiv.Perm (Fin 4), (η * matchingProduct a b σ).re ≤ H)
    (hattain : ∃ σ : Equiv.Perm (Fin 4), (η * matchingProduct a b σ).re = H)
    (hgap : H < (η * determinantValue a b U).re)
    (hcut : ∀ σ : Equiv.Perm (Fin 4), (η * matchingProduct a b σ).re = H →
      ∀ k, σ k ∈ I ↔ k ∈ J) :
    ∃ (z : ℂ) (τ : Equiv.Perm (Fin 4)), ¬ (∀ k, τ k ∈ I ↔ k ∈ J) ∧
      let c := pairedShiftSpectrum a I z
      let d := pairedShiftSpectrum b J (-z)
      (η * matchingProduct c d τ).re = H ∧
      (∀ σ : Equiv.Perm (Fin 4), (η * matchingProduct c d σ).re ≤ H) ∧
      (∀ σ : Equiv.Perm (Fin 4), (η * matchingProduct a b σ).re = H →
        matchingProduct c d σ = matchingProduct a b σ) ∧
      H < (η * determinantValue c d U).re ∧
      (∀ k l, c k + d l ≠ 0) ∧
      ∀ π τ : Equiv.Perm (Fin 4), matchingProduct a b π ≠ matchingProduct a b τ →
        matchingProduct c d π ≠ matchingProduct c d τ := by
  classical
  have hη : η ≠ 0 := by
    intro h
    obtain ⟨σ, hσ⟩ := hattain
    simp only [h, zero_mul, Complex.zero_re] at hσ hgap
    linarith only [hσ, hgap]
  let p := pairedShiftDetPolynomial a b U I J η
  let Q := pairedShiftMatchingPolynomial a b I J η
  have hp₄ : p.coeff 4 ≠ 0 := by
    rw [pairedShiftDetPolynomial_coeff_four]
    exact mul_ne_zero hη hD
  have hp : 0 < p.degree := by
    have hpne : p ≠ 0 := by rintro h; exact hp₄ (by rw [h, coeff_zero])
    have hpd : p.natDegree = 4 :=
      le_antisymm (pairedShiftDetPolynomial_degree_le a b U I J η) (le_natDegree_of_ne_zero hp₄)
    rw [degree_eq_natDegree hpne, hpd]
    norm_num
  have hQ₀ (σ : Equiv.Perm (Fin 4)) : (Q σ).eval 0 = η * matchingProduct a b σ := by
    simp only [Q, eval_pairedShiftMatchingPolynomial, neg_zero, pairedShiftSpectrum_zero]
  have hp₀ : p.eval 0 = η * determinantValue a b U := by
    simp only [p, eval_pairedShiftDetPolynomial, neg_zero, pairedShiftSpectrum_zero]
  have hfixed (σ : Equiv.Perm (Fin 4)) (hσ : ∀ k, σ k ∈ I ↔ k ∈ J) (z : ℂ) :
      matchingProduct (pairedShiftSpectrum a I z) (pairedShiftSpectrum b J (-z)) σ =
        matchingProduct a b σ := by
    unfold matchingProduct
    apply Finset.prod_congr rfl
    intro k _
    by_cases hj : k ∈ J
    · simp [pairedShiftSpectrum, pairedShiftMask, hj, (hσ k).mpr hj] <;> ring
    · have hi : σ k ∉ I := fun h => hj ((hσ k).mp h)
      simp [pairedShiftSpectrum, pairedShiftMask, hj, hi]
  let S := Finset.univ.filter (fun σ : Equiv.Perm (Fin 4) => ¬ (∀ k, σ k ∈ I ↔ k ∈ J))
  have hS : S.Nonempty := by
    obtain ⟨k, hk⟩ : J.Nonempty := Finset.card_pos.mp (by rw [hJ]; decide)
    have hi : ∃ i : Fin 4, i ∉ I := by
      by_contra h
      have hall (i : Fin 4) : i ∈ I := Classical.byContradiction fun hi => h ⟨i, hi⟩
      have hI' : I = Finset.univ := Finset.eq_univ_iff_forall.mpr hall
      simp [hI'] at hI
    obtain ⟨i, hi⟩ := hi
    let σ := Equiv.swap k i
    exact ⟨σ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun e => hi (by
      simpa only [σ, Equiv.swap_apply_left] using (e k).mpr hk)⟩⟩
  let G (z : ℂ) := S.sup' hS (fun σ => ((Q σ).eval z).re)
  have hGc : Continuous G := Continuous.finset_sup'_apply hS
    (fun σ _ => Complex.continuous_re.comp (Q σ).continuous)
  have hG (σ : Equiv.Perm (Fin 4)) (hσ : σ ∈ S) (z : ℂ) : ((Q σ).eval z).re ≤ G z :=
    Finset.le_sup' (fun σ => ((Q σ).eval z).re) hσ
  have hG₀ : G 0 < H := by
    obtain ⟨σ, hσS, he⟩ := Finset.exists_mem_eq_sup' hS (fun σ => ((Q σ).eval 0).re)
    change G 0 = ((Q σ).eval 0).re at he
    rw [he, hQ₀]
    exact lt_of_le_of_ne (hmax σ) fun h => (Finset.mem_filter.mp hσS).2 (hcut σ h)
  let E : Set ℂ := ⋃ π : Equiv.Perm (Fin 4), ⋃ τ : Equiv.Perm (Fin 4),
    {z | (Q π).eval 0 ≠ (Q τ).eval 0 ∧ (Q π).eval z = (Q τ).eval z}
  have hE : E.Finite := by
    refine Set.finite_iUnion fun π => Set.finite_iUnion fun τ => ?_
    by_cases h : (Q π).eval 0 = (Q τ).eval 0
    · simp [h]
    · have hn : Q π - Q τ ≠ 0 := by
        intro he
        apply h
        simpa [eval_sub, sub_eq_zero] using congrArg (fun R : ℂ[X] => R.eval 0) he
      refine (Polynomial.finite_setOf_isRoot hn).subset fun z hz => ?_
      change (Q π - Q τ).eval z = 0
      rw [eval_sub, (show (Q π).eval z = (Q τ).eval z from hz.2), sub_self]
  let W : Set ℂ := {z | H < (p.eval z).re} ∩ {z | G z < H}
  have hpRe : Continuous (fun z => (p.eval z).re) := Complex.continuous_re.comp p.continuous
  have hW : IsOpen W := (isOpen_lt continuous_const hpRe).inter (isOpen_lt hGc continuous_const)
  have hWne : W.Nonempty := by
    refine ⟨0, ?_, hG₀⟩
    change H < (p.eval 0).re
    rwa [hp₀]
  obtain ⟨x, hx, r, hr, hband⟩ := exists_polynomial_imaginary_band_avoiding_finite p hp hW hWne hE
  let d := (p.eval x).im
  let V : Set ℂ := {w | H < w.re} ∩ Complex.im ⁻¹' Metric.ball d r
  have hV : IsOpen V :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (Metric.isOpen_ball.preimage Complex.continuous_im)
  have hVconv : Convex ℝ V :=
    (convex_halfSpace_gt Complex.reLm.isLinear H).inter
      ((convex_ball d r).linear_preimage Complex.imLm)
  have hxV : p.eval x ∈ V := ⟨hx.1, Metric.mem_ball_self hr⟩
  have hRay (t : ℝ) (ht : H + 1 ≤ t) : (t : ℂ) + (d : ℂ) * Complex.I ∈ V := by
    have ht' : H < t := by linarith only [ht]
    have hre : ((t : ℂ) + (d : ℂ) * Complex.I).re = t := by simp [Complex.mul_re]
    have him : ((t : ℂ) + (d : ℂ) * Complex.I).im = d := by simp [Complex.mul_im]
    have hmem : d ∈ Metric.ball d r := Metric.mem_ball_self hr
    refine ⟨?_, ?_⟩
    · change H < ((t : ℂ) + (d : ℂ) * Complex.I).re
      rwa [hre]
    · simpa only [Set.mem_preimage, him] using hmem
  let K := connectedComponentIn ((fun z => p.eval z) ⁻¹' V) x
  have hxK : x ∈ K := mem_connectedComponentIn hxV
  obtain ⟨σ, hσ, y, hyK, hy⟩ := exists_large_crossing_matching_on_paired_component
    a b U hU η hη I J hI hJ hD hV hVconv.isPreconnected hxV d (H + 1) H hRay
  have hσS : σ ∈ S := Finset.mem_filter.mpr
    ⟨Finset.mem_univ σ, fun h => hσ 0 (h 0)⟩
  have hy' : H < ((Q σ).eval y).re := by
    simpa only [Q, eval_pairedShiftMatchingPolynomial] using hy
  have hGy : H < G y := hy'.trans_le (hG σ hσS y)
  obtain ⟨z, hzK, hzG⟩ := isPreconnected_connectedComponentIn.intermediate_value
    hxK hyK hGc.continuousOn (show H ∈ Set.Icc (G x) (G y) from ⟨hx.2.le, hGy.le⟩)
  have hzV : p.eval z ∈ V :=
    connectedComponentIn_subset ((fun w => p.eval w) ⁻¹' V) x hzK
  have hzE : z ∉ E := by
    intro he
    exact hband hzV.2 ⟨z, he, rfl⟩
  obtain ⟨τ, hτS, hτ⟩ := Finset.exists_mem_eq_sup' hS (fun σ => ((Q σ).eval z).re)
  change G z = ((Q τ).eval z).re at hτ
  let c' := pairedShiftSpectrum a I z
  let d' := pairedShiftSpectrum b J (-z)
  have hdet : H < (η * determinantValue c' d' U).re := by
    simpa only [p, eval_pairedShiftDetPolynomial, c', d'] using hzV.1
  have hnew (π : Equiv.Perm (Fin 4)) : (η * matchingProduct c' d' π).re ≤ H := by
    by_cases h : ∀ k, π k ∈ I ↔ k ∈ J
    · rw [hfixed π h z]
      exact hmax π
    · have hπS : π ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ π, h⟩
      simpa only [Q, eval_pairedShiftMatchingPolynomial] using (hG π hπS z).trans_eq hzG
  refine ⟨z, τ, (Finset.mem_filter.mp hτS).2, ?_, hnew,
    fun π hπ => hfixed π (hcut π hπ) z, hdet, ?_, ?_⟩
  · simpa only [Q, eval_pairedShiftMatchingPolynomial] using hτ.symm.trans hzG
  · intro k l hkl
    obtain ⟨π, hπ⟩ := (holds_iff_directional c' d' U).mp
      (holds_four_of_opposite_entries c' d' U hU hkl) η
    exact (not_le_of_gt hdet) (hπ.trans (hnew π))
  · intro π κ hne he
    apply hzE
    refine Set.mem_iUnion.mpr ⟨π, Set.mem_iUnion.mpr ⟨κ, ?_⟩⟩
    refine ⟨fun h => hne (mul_left_cancel₀ hη (by simpa only [hQ₀] using h)), ?_⟩
    simp only [Q, eval_pairedShiftMatchingPolynomial, c', d', he]

end

end MOC
