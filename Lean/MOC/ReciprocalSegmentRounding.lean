import MOC.ThreeValues
import MOC.EndpointRematching

/-! Independent rounding of shifted reciprocals to two endpoint values. -/

open BigOperators Finset Matrix

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private def reciprocalMatching (a q : ι → ℂ) (α t : ℂ) (j₀ : ι) (σ : Equiv.Perm ι) : ℂ :=
  ∏ j, if j = j₀ then a (σ j) + t else 1 + (a (σ j) - α) * q j

private theorem matchingProduct_eq_reciprocal (a b q : ι → ℂ) (α t : ℂ) (j₀ : ι)
    (hq : ∀ j, j ≠ j₀ → q j = (α + b j)⁻¹)
    (hb : ∀ j, j ≠ j₀ → α + b j ≠ 0) (σ : Equiv.Perm ι) :
    matchingProduct a (Function.update b j₀ t) σ =
      (∏ j, if j = j₀ then 1 else α + b j) * reciprocalMatching a q α t j₀ σ := by
  rw [matchingProduct, reciprocalMatching, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  by_cases hj : j = j₀
  · subst j
    simp only [Function.update_self, if_pos rfl, if_true, one_mul]
  · rw [if_neg hj, if_neg hj, Function.update_of_ne hj, hq j hj]
    field_simp [hb j hj]; ring

private theorem weightedMatching_eq_iff_reciprocal (a b q : ι → ℂ) (α t : ℂ)
    (j₀ : ι) (U : Matrix ι ι ℂ) (hU : IsUnitary U) (w : Equiv.Perm ι → ℝ)
    (hq : ∀ j, j ≠ j₀ → q j = (α + b j)⁻¹)
    (hb : ∀ j, j ≠ j₀ → α + b j ≠ 0) :
    weightedMatchingValue a (Function.update b j₀ t) w =
      determinantValue a (Function.update b j₀ t) U ↔
    (∑ σ, (w σ : ℂ) * reciprocalMatching a q α t j₀ σ) =
      ∑ σ, (realSignedWeight U σ : ℂ) * reciprocalMatching a q α t j₀ σ := by
  let D := ∏ j, if j = j₀ then 1 else α + b j
  have hD : D ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    by_cases hj : j = j₀
    · rw [if_pos hj]
      exact one_ne_zero
    · exact (if_neg hj).symm ▸ hb j hj
  rw [weightedMatchingValue, ← real_signed_determinant _ _ U hU]
  simp_rw [matchingProduct_eq_reciprocal a b q α t j₀ hq hb]
  change (∑ σ, (w σ : ℂ) * (D * reciprocalMatching a q α t j₀ σ)) =
      (∑ σ, (realSignedWeight U σ : ℂ) * (D * reciprocalMatching a q α t j₀ σ)) ↔ _
  simp_rw [mul_left_comm _ D, ← Finset.mul_sum]
  exact mul_right_inj' hD

private def roundedReciprocal (p s : ℂ) (J : Finset ι) (j : ι) : ℂ :=
  if j ∈ J then p else s

private def roundingMass (θ : ι → ℝ) (J : Finset ι) : ℝ :=
  (∏ j ∈ J, θ j) * ∏ j ∈ Jᶜ, (1 - θ j)

private theorem roundingMass_nonneg (θ : ι → ℝ) (hθ : ∀ j, θ j ∈ Set.Icc 0 1)
    (J : Finset ι) : 0 ≤ roundingMass θ J :=
  mul_nonneg (Finset.prod_nonneg fun j _ => (hθ j).1)
    (Finset.prod_nonneg fun j _ => sub_nonneg.mpr (hθ j).2)

private theorem roundingMass_sum (θ : ι → ℝ) : ∑ J, roundingMass θ J = 1 := by
  have h (j : ι) : θ j + (1 - θ j) = 1 := by ring
  simp only [roundingMass, ← Fintype.prod_add, h, Finset.prod_const_one]

private theorem reciprocalMatching_eq_rounding (a q : ι → ℂ) (α t p s : ℂ)
    (j₀ : ι) (θ : ι → ℝ)
    (hq : ∀ j, j ≠ j₀ → q j = (θ j : ℂ) * p + (1 - (θ j : ℂ)) * s)
    (σ : Equiv.Perm ι) :
    reciprocalMatching a q α t j₀ σ =
      ∑ J, (roundingMass θ J : ℂ) *
        reciprocalMatching a (roundedReciprocal p s J) α t j₀ σ := by
  let F (qj : ℂ) (j : ι) :=
    if j = j₀ then a (σ j) + t else 1 + (a (σ j) - α) * qj
  have hfactor (j : ι) : F (q j) j =
      (θ j : ℂ) * F p j + ((1 - θ j : ℝ) : ℂ) * F s j := by
    by_cases hj : j = j₀
    · simp only [F, if_pos hj, Complex.ofReal_sub, Complex.ofReal_one]
      ring
    · simp only [F, if_neg hj, hq j hj, Complex.ofReal_sub, Complex.ofReal_one]
      ring
  have hrounded (J : Finset ι) :
      reciprocalMatching a (roundedReciprocal p s J) α t j₀ σ =
        (∏ j ∈ J, F p j) * ∏ j ∈ Jᶜ, F s j := by
    have h (j : ι) : F (roundedReciprocal p s J j) j =
        if j ∈ J then F p j else F s j := by
      by_cases hj : j ∈ J
      · simp only [roundedReciprocal, if_pos hj]
      · simp only [roundedReciprocal, if_neg hj]
    change (∏ j, F (roundedReciprocal p s J j) j) = _
    simp_rw [h, Finset.prod_ite]
    have h₁ : (univ.filter fun j : ι => j ∈ J) = J := by ext; simp
    have h₂ : (univ.filter fun j : ι => j ∉ J) = Jᶜ := by ext; simp
    rw [h₁, h₂]
  change (∏ j, F (q j) j) = _
  simp_rw [hfactor]
  rw [Fintype.prod_add]
  apply Finset.sum_congr rfl
  intro J _
  simp only [hrounded, roundingMass, Complex.ofReal_mul, Complex.ofReal_prod,
    Finset.prod_mul_distrib]
  ring

private theorem reciprocalMatching_eq_rematch (a q q' : ι → ℂ) (α t : ℂ)
    (E : Finset ι) (j₀ : ι) (σ τ : Equiv.Perm ι)
    (ha : ∀ i, i ∉ E → a i = α) (ht : τ j₀ = σ j₀)
    (h : ∀ i ∈ E, i ≠ σ j₀ → q (τ.symm i) = q' (σ.symm i)) :
    reciprocalMatching a q α t j₀ τ = reciprocalMatching a q' α t j₀ σ := by
  have orient (r : ι → ℂ) (ρ : Equiv.Perm ι) : reciprocalMatching a r α t j₀ ρ =
      ∏ i, if ρ.symm i = j₀ then a i + t else 1 + (a i - α) * r (ρ.symm i) := by
    simpa only [reciprocalMatching, Function.comp_apply, Equiv.apply_symm_apply] using
      (Equiv.prod_comp ρ.symm
        (fun j => if j = j₀ then a (ρ j) + t else 1 + (a (ρ j) - α) * r j)).symm
  rw [orient q τ, orient q' σ]
  apply Finset.prod_congr rfl
  intro i _
  have hτ : τ.symm i = j₀ ↔ i = σ j₀ := by rw [Equiv.symm_apply_eq, ht]
  have hσ : σ.symm i = j₀ ↔ i = σ j₀ := Equiv.symm_apply_eq σ
  by_cases hi : i = σ j₀
  · rw [if_pos (hτ.mpr hi), if_pos (hσ.mpr hi)]
  · rw [if_neg (fun h => hi (hτ.mp h)), if_neg (fun h => hi (hσ.mp h))]
    by_cases hE : i ∈ E
    · rw [h i hE hi]
    · rw [ha i hE, sub_self, zero_mul, zero_mul]

private theorem exists_rounding_endpoint_weights {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : IsUnitary U) (J : Finset (Fin n)) (j₀ : Fin n) (α p s : ℂ)
    (hp₀ : p ≠ 0) (hs₀ : s ≠ 0) :
    ∃ w : Equiv.Perm (Fin n) → ℝ, (∀ σ, 0 ≤ w σ) ∧ (∑ σ, w σ = 1) ∧
      ∀ (a : Fin n → ℂ) (t : ℂ),
        (∑ σ, (w σ : ℂ) * reciprocalMatching a (roundedReciprocal p s J) α t j₀ σ) =
        ∑ σ, (realSignedWeight U σ : ℂ) *
          reciprocalMatching a (roundedReciprocal p s J) α t j₀ σ := by
  let b := fun j => if j ∈ J.erase j₀ then p⁻¹ - α else s⁻¹ - α
  obtain ⟨w, hw, hsum, heq⟩ :=
    exists_commonWeights_three_values_one_singleton U hU (J.erase j₀) j₀ (not_mem_erase _ _)
  refine ⟨w, hw, hsum, fun a t => ?_⟩
  have hb (j : Fin n) (hj : j ≠ j₀) :
      α + b j = (roundedReciprocal p s J j)⁻¹ := by
    by_cases hJ : j ∈ J
    · have hj' : j ∈ J.erase j₀ := Finset.mem_erase.mpr ⟨hj, hJ⟩
      simp only [b, roundedReciprocal, if_pos hJ, if_pos hj']
      ring
    · have hj' : j ∉ J.erase j₀ := fun h => hJ (Finset.mem_erase.mp h).2
      simp only [b, roundedReciprocal, if_neg hJ, if_neg hj']
      ring
  apply (weightedMatching_eq_iff_reciprocal a b _ α t j₀ U hU w ?_ ?_).mp
  · exact heq a (p⁻¹ - α) (s⁻¹ - α) t
  · intro j hj
    rw [hb j hj, inv_inv]
  · intro j hj
    rw [hb j hj]
    apply inv_ne_zero
    by_cases hJ : j ∈ J
    · rwa [roundedReciprocal, if_pos hJ]
    · rwa [roundedReciprocal, if_neg hJ]

/-- Let the first spectrum equal `α` outside `E`. Suppose the shifted
reciprocals of the second spectrum off `j₀` lie in the segment with endpoints
`p` and `s`, each of which occurs at least `E.card` times off `j₀`.
One permutation law works for every first spectrum with this constraint and
every value of the second spectrum at `j₀`. -/
theorem exists_commonWeights_reciprocal_segment_one_exception {n : ℕ}
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitary U)
    (E : Finset (Fin n)) (α : ℂ) (b : Fin n → ℂ) (j₀ : Fin n)
    (p s : ℂ) (θ : Fin n → ℝ)
    (hb : ∀ j, j ≠ j₀ → α + b j ≠ 0)
    (hp₀ : p ≠ 0) (hs₀ : s ≠ 0) (hps : p ≠ s)
    (hp : E.card ≤ (univ.filter fun j => j ≠ j₀ ∧ (α + b j)⁻¹ = p).card)
    (hs : E.card ≤ (univ.filter fun j => j ≠ j₀ ∧ (α + b j)⁻¹ = s).card)
    (hθ : ∀ j, θ j ∈ Set.Icc 0 1)
    (hq : ∀ j, j ≠ j₀ → (α + b j)⁻¹ = (θ j : ℂ) * p + (1 - (θ j : ℂ)) * s) :
    ∃ w : Equiv.Perm (Fin n) → ℝ, (∀ σ, 0 ≤ w σ) ∧ (∑ σ, w σ = 1) ∧
      ∀ (a : Fin n → ℂ), (∀ i, i ∉ E → a i = α) → ∀ t : ℂ,
        weightedMatchingValue a (Function.update b j₀ t) w =
          determinantValue a (Function.update b j₀ t) U := by
  classical
  let q (j : Fin n) := (α + b j)⁻¹
  choose w hw hsum heq using fun J : Finset (Fin n) =>
    exists_rounding_endpoint_weights U hU J j₀ α p s hp₀ hs₀
  have hrematch (J : Finset (Fin n)) (σ : Equiv.Perm (Fin n)) :
      ∃ τ : Equiv.Perm (Fin n), τ j₀ = σ j₀ ∧
        ∀ i ∈ E, i ≠ σ j₀ → q (τ.symm i) = roundedReciprocal p s J (σ.symm i) := by
    apply exists_perm_reciprocal_segment_rematch E j₀ q (roundedReciprocal p s J) p s hps hp hs
    intro j _
    by_cases hJ : j ∈ J
    · exact Or.inl (if_pos hJ)
    · exact Or.inr (if_neg hJ)
  choose τ hτ using hrematch
  let mass (k : Finset (Fin n) × Equiv.Perm (Fin n)) := roundingMass θ k.1 * w k.1 k.2
  let pick (k : Finset (Fin n) × Equiv.Perm (Fin n)) := τ k.1 k.2
  let v (ω : Equiv.Perm (Fin n)) := ∑ k ∈ univ.filter (fun k => pick k = ω), mass k
  have hv (ω : Equiv.Perm (Fin n)) : 0 ≤ v ω :=
    Finset.sum_nonneg fun k _ => mul_nonneg (roundingMass_nonneg θ hθ k.1) (hw k.1 k.2)
  have hvsum : ∑ ω, v ω = 1 := calc
    _ = ∑ k, mass k := Finset.sum_fiberwise univ pick mass
    _ = ∑ J, roundingMass θ J := by
      rw [Fintype.sum_prod_type]
      simp only [mass, ← Finset.mul_sum, hsum, mul_one]
    _ = 1 := roundingMass_sum θ
  refine ⟨v, hv, hvsum, fun a ha t => ?_⟩
  apply (weightedMatching_eq_iff_reciprocal a b q α t j₀ U hU v (fun _ _ => rfl) hb).mpr
  have hpush (f : Equiv.Perm (Fin n) → ℂ) :
      (∑ ω, (v ω : ℂ) * f ω) = ∑ k, (mass k : ℂ) * f (pick k) := by
    rw [← Finset.sum_fiberwise univ pick]
    apply Finset.sum_congr rfl
    intro ω _
    dsimp only [v]
    rw [Complex.ofReal_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    rw [(Finset.mem_filter.mp hk).2]
  calc
    _ = ∑ k, (mass k : ℂ) * reciprocalMatching a q α t j₀ (pick k) := hpush _
    _ = ∑ J, (roundingMass θ J : ℂ) *
        ∑ σ, (w J σ : ℂ) * reciprocalMatching a (roundedReciprocal p s J) α t j₀ σ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro J _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ _
      rw [show pick (J, σ) = τ J σ from rfl,
        reciprocalMatching_eq_rematch a q _ α t E j₀ σ (τ J σ) ha (hτ J σ).1 (hτ J σ).2]
      simp only [mass, Complex.ofReal_mul, mul_assoc]
    _ = ∑ σ, (realSignedWeight U σ : ℂ) * reciprocalMatching a q α t j₀ σ := by
      simp_rw [heq, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro σ _
      simp_rw [mul_left_comm (roundingMass θ _ : ℂ), ← Finset.mul_sum]
      rw [← reciprocalMatching_eq_rounding a q α t p s j₀ θ hq σ]

/-- The reciprocal segment condition implies determinant inclusion in each order. -/
theorem holds_reciprocal_segment_one_exception {n : ℕ}
    (a b : Fin n → ℂ) (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitary U)
    (E : Finset (Fin n)) (α : ℂ) (j₀ : Fin n) (p s : ℂ) (θ : Fin n → ℝ)
    (ha : ∀ i, i ∉ E → a i = α)
    (hb : ∀ j, j ≠ j₀ → α + b j ≠ 0)
    (hp₀ : p ≠ 0) (hs₀ : s ≠ 0) (hps : p ≠ s)
    (hp : E.card ≤ (univ.filter fun j => j ≠ j₀ ∧ (α + b j)⁻¹ = p).card)
    (hs : E.card ≤ (univ.filter fun j => j ≠ j₀ ∧ (α + b j)⁻¹ = s).card)
    (hθ : ∀ j, θ j ∈ Set.Icc 0 1)
    (hq : ∀ j, j ≠ j₀ → (α + b j)⁻¹ = (θ j : ℂ) * p + (1 - (θ j : ℂ)) * s) :
    Holds a b U := by
  obtain ⟨w, hw, hsum, heq⟩ :=
    exists_commonWeights_reciprocal_segment_one_exception U hU E α b j₀ p s θ hb hp₀ hs₀
      hps hp hs hθ hq
  apply holds_of_weights w hw hsum
  simpa only [Function.update_eq_self] using heq a ha (b j₀)

end

end MOC
