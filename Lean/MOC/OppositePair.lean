import MOC.Geometry
import MOC.RankTwoOverlap

/-! The shifted supports determine the order of the reciprocal compression
at an opposite pair. -/

open BigOperators Matrix Finset

namespace MOC

noncomputable section

section Overlap

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
private theorem support_card_add_zero_card (a : ι → ℂ) :
    (spectralSupport a).card + (Finset.univ.filter fun i => a i = 0).card = Fintype.card ι := by
  simpa [spectralSupport] using
    (Finset.filter_card_add_filter_neg_card_eq_card (s := Finset.univ) (fun i => a i ≠ 0))

/-- At a marked opposite pair, the determinant inclusion holds when the two
marked eigenvalues have total multiplicity at least the order minus two. -/
theorem holds_of_opposite_pair_multiplicities (a b : ι → ℂ) (U : Matrix ι ι ℂ)
    (hU : IsUnitary U) {i j : ι} (hij : a i + b j = 0)
    (hcard : Fintype.card ι ≤ (Finset.univ.filter fun k => a k = a i).card +
      (Finset.univ.filter fun k => b k = b j).card + 2) : Holds a b U := by
  let x (k : ι) := a k + b j
  let y (k : ι) := b k - b j
  have hx (k : ι) : x k = 0 ↔ a k = a i := by
    change a k + b j = 0 ↔ a k = a i
    rw [← hij, add_right_cancel_iff]
  have hy (k : ι) : y k = 0 ↔ b k = b j := sub_eq_zero
  have hleft := support_card_add_zero_card x
  have hright := support_card_add_zero_card y
  simp_rw [hx] at hleft
  simp_rw [hy] at hright
  apply holds_of_shifted_support_le_card_add_two a b U hU (b j)
  change (spectralSupport x).card + (spectralSupport y).card ≤ Fintype.card ι + 2
  omega

/-- A covering permutation keeps the reciprocal factors on its edges inside
both nonzero supports. Other permutations have value zero. -/
def reciprocalOverlapProduct (a b : ι → ℂ) (τ : Equiv.Perm ι) : ℂ :=
  if CoversSupports a b τ then
    ∏ j, if a (τ j) ≠ 0 ∧ b j ≠ 0 then (a (τ j))⁻¹ + (b j)⁻¹ else 1
  else 0

omit [DecidableEq ι] in
private theorem matchingProduct_eq_mul_reciprocalOverlapProduct (a b : ι → ℂ)
    (τ : Equiv.Perm ι) :
    matchingProduct a b τ =
      ((∏ i : {i // a i ≠ 0}, a i) * ∏ j : {j // b j ≠ 0}, b j) *
        reciprocalOverlapProduct a b τ := by
  classical
  by_cases hcov : CoversSupports a b τ
  · rw [reciprocalOverlapProduct, if_pos hcov]
    have hp (c : ι → ℂ) :
        (∏ i, if c i = 0 then 1 else c i) = ∏ i : {i // c i ≠ 0}, c i := by
      apply Finset.prod_congr_set {i | c i ≠ 0}
      · intro i hi
        exact if_neg hi
      · intro i hi
        apply if_pos
        simpa using hi
    rw [← hp a, ← hp b, ← Equiv.prod_comp τ (fun i => if a i = 0 then (1 : ℂ) else a i),
      ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    unfold matchingProduct
    apply Finset.prod_congr rfl
    intro j _
    by_cases ha : a (τ j) = 0 <;> by_cases hb : b j = 0
    · exact ((hcov j).elim (fun h => h ha) (fun h => h hb)).elim
    · simp [ha, hb]
    · simp [ha, hb]
    · simp [ha, hb]
      field_simp
      ring
  · rw [reciprocalOverlapProduct, if_neg hcov, mul_zero]
    obtain ⟨j, hj⟩ := not_forall.mp (show ¬ ∀ j, a (τ j) ≠ 0 ∨ b j ≠ 0 from hcov)
    have hz : a (τ j) = 0 ∧ b j = 0 := by simpa using hj
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hz.1, hz.2])

/-- The support count fixes the order of the reciprocal compression. When
the two supports span the ambient space, the hull inclusion is equivalent
to inclusion of the compressed determinant multiplied by a real contraction. -/
theorem exists_supportOverlap_hull_reduction (a b : ι → ℂ) (U : Matrix ι ι ℂ)
    (hU : IsUnitary U) (k : ℕ)
    (hcard : (spectralSupport a).card + (spectralSupport b).card = Fintype.card ι + k) :
    let X := (1 : Matrix ι ι ℂ).submatrix id (Subtype.val : {i // a i ≠ 0} → ι)
    let Y := U.submatrix id (Subtype.val : {j // b j ≠ 0} → ι)
    let G := X * Xᴴ + Y * Yᴴ
    G.det ≠ 0 →
      ∃ (E : Matrix {i // a i ≠ 0} (Fin k) ℂ) (F : Matrix {j // b j ≠ 0} (Fin k) ℂ) (q : ℝ),
        Eᴴ * E = 1 ∧ Fᴴ * F = 1 ∧ X * E = Y * F ∧ 0 ≤ q ∧ q ≤ 1 ∧
        (Holds a b U ↔
          q • (Eᴴ * diagonal (fun i : {i // a i ≠ 0} => (a i)⁻¹) * E +
              Fᴴ * diagonal (fun j : {j // b j ≠ 0} => (b j)⁻¹) * F).det ∈
            convexHull ℝ (Set.range (reciprocalOverlapProduct a b))) := by
  classical
  intro X Y G hG
  let ρ := {i // a i ≠ 0}
  let σ := {j // b j ≠ 0}
  let a' : ρ → ℂ := fun i => a i
  let b' : σ → ℂ := fun j => b j
  let D := (∏ i, a' i) * ∏ j, b' j
  have hD : D ≠ 0 := mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => i.property)
    (Finset.prod_ne_zero_iff.mpr fun j _ => j.property)
  have hdet : determinantValue a b U = (X * diagonal a' * Xᴴ + Y * diagonal b' * Yᴴ).det := by
    change determinantValue a b U =
      ((1 : Matrix ι ι ℂ).submatrix id Subtype.val * diagonal a' *
        ((1 : Matrix ι ι ℂ).submatrix id Subtype.val)ᴴ +
        U.submatrix id Subtype.val * diagonal b' * (U.submatrix id Subtype.val)ᴴ).det
    unfold determinantValue
    rw [weighted_support_columns 1 a a (fun _ h => h),
      weighted_support_columns U b b (fun _ h => h), Matrix.one_mul,
      Matrix.conjTranspose_one, Matrix.mul_one]
  have hflag (c : ι → ℂ) : diagonal (fun i : {i // c i ≠ 0} => supportIndicator c i) = 1 := by
    rw [← Matrix.diagonal_one]
    apply congrArg Matrix.diagonal
    funext i
    simp [supportIndicator, i.property]
  have hGram : G = diagonal (supportIndicator a) + U * diagonal (supportIndicator b) * Uᴴ := by
    calc
      _ = X * diagonal (fun i : ρ => supportIndicator a i) * Xᴴ +
          Y * diagonal (fun j : σ => supportIndicator b j) * Yᴴ := by
        change X * Xᴴ + Y * Yᴴ = _
        rw [hflag, hflag, Matrix.mul_one, Matrix.mul_one]
      _ = _ := by
        change (1 : Matrix ι ι ℂ).submatrix id Subtype.val *
          diagonal (fun i : ρ => supportIndicator a i) *
            ((1 : Matrix ι ι ℂ).submatrix id Subtype.val)ᴴ +
          U.submatrix id Subtype.val * diagonal (fun j : σ => supportIndicator b j) *
            (U.submatrix id Subtype.val)ᴴ = _
        rw [weighted_support_columns 1 a (supportIndicator a) (by simp [supportIndicator]),
          weighted_support_columns U b (supportIndicator b) (by simp [supportIndicator]),
          Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one]
  obtain ⟨q, hq₀, hq₁, _, hq⟩ := determinantValue_supportIndicator a b U hU k hcard
  have hGdet : G.det = (2 : ℂ) ^ k * (q : ℂ) := by rw [hGram]; exact hq
  have hρ : Fintype.card ρ = (spectralSupport a).card := Fintype.card_of_subtype _ (by
    simp [spectralSupport])
  have hσ : Fintype.card σ = (spectralSupport b).card := Fintype.card_of_subtype _ (by
    simp [spectralSupport])
  let e : ι ⊕ Fin k ≃ ρ ⊕ σ := Fintype.equivOfCardEq (by
    rw [Fintype.card_sum, Fintype.card_sum, Fintype.card_fin, hρ, hσ, hcard])
  have hX : Xᴴ * X = 1 := support_columns_isometry 1 isUnitary_one a
  have hY : Yᴴ * Y = 1 := support_columns_isometry U hU b
  have hGun : IsUnit G.det := isUnit_iff_ne_zero.mpr hG
  obtain ⟨E, F, hE, hF, hcommon⟩ := exists_overlap_frames e X Y hX hY hGun
  let z := (Eᴴ * diagonal (fun i => (a' i)⁻¹) * E + Fᴴ * diagonal (fun j => (b' j)⁻¹) * F).det
  have hprod := det_support_frames e X Y E F hE hF hcommon hGun a' b'
    (fun i => i.property) (fun j => j.property)
  change (X * diagonal a' * Xᴴ + Y * diagonal b' * Yᴴ).det =
    D * (G.det / (2 : ℂ) ^ Fintype.card (Fin k)) * z at hprod
  have hscaled : determinantValue a b U = D * (q • z) := by
    rw [hdet, hprod, hGdet, Fintype.card_fin, Complex.real_smul,
      mul_div_cancel_left₀ (q : ℂ) (pow_ne_zero k (by norm_num : (2 : ℂ) ≠ 0))]
    ring
  exact ⟨E, F, q, hE, hF, hcommon, hq₀, hq₁,
    hull_common_factor_iff hD hscaled (matchingProduct_eq_mul_reciprocalOverlapProduct a b)⟩

/-- A rectangular inclusion for the reciprocal spectra suffices to cover the
ordinary hull at a marked zero pair. The singular support Gram case is automatic. -/
theorem holds_of_zero_pair_of_supportOverlap (a b : ι → ℂ) (U : Matrix ι ι ℂ)
    (hU : IsUnitary U) {i j : ι} (hi : a i = 0) (hj : b j = 0) (k : ℕ)
    (hcard : (spectralSupport a).card + (spectralSupport b).card = Fintype.card ι + k)
    (hrect : ∀ (E : Matrix {i // a i ≠ 0} (Fin k) ℂ) (F : Matrix {j // b j ≠ 0} (Fin k) ℂ),
      Eᴴ * E = 1 → Fᴴ * F = 1 →
      (Eᴴ * diagonal (fun i : {i // a i ≠ 0} => (a i)⁻¹) * E +
        Fᴴ * diagonal (fun j : {j // b j ≠ 0} => (b j)⁻¹) * F).det ∈
        convexHull ℝ (Set.range (reciprocalOverlapProduct a b))) : Holds a b U := by
  classical
  let X := (1 : Matrix ι ι ℂ).submatrix id (Subtype.val : {i // a i ≠ 0} → ι)
  let Y := U.submatrix id (Subtype.val : {j // b j ≠ 0} → ι)
  by_cases hG : (X * Xᴴ + Y * Yᴴ).det = 0
  · have hdet := det_support_sum_eq_zero_of_gram X Y (fun i => a i) (fun j => b j) hG
    dsimp only [X, Y] at hdet
    rw [weighted_support_columns 1 a a (fun _ h => h),
      weighted_support_columns U b b (fun _ h => h), Matrix.one_mul,
      Matrix.conjTranspose_one, Matrix.mul_one] at hdet
    exact holds_of_singular_of_opposite_entries a b U hdet (by rw [hi, hj, add_zero])
  · obtain ⟨E, F, q, hE, hF, _, hq₀, hq₁, hequiv⟩ :=
      exists_supportOverlap_hull_reduction a b U hU k hcard hG
    have hzero : (0 : ℂ) ∈ Set.range (reciprocalOverlapProduct a b) := by
      let τ := Equiv.swap j i
      refine ⟨τ, if_neg ?_⟩
      intro hcov
      simpa [τ, hi, hj] using hcov j
    apply hequiv.mpr
    simpa using (convex_convexHull ℝ (Set.range (reciprocalOverlapProduct a b)))
      (subset_convexHull ℝ _ hzero) (hrect E F hE hF)
      (sub_nonneg.mpr hq₁) hq₀ (sub_add_cancel 1 q)

end Overlap

end

end MOC
