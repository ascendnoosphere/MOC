import MOC.SubsetContraction
import MOC.NestedContactObjective

/-! Two-sided transport for exterior coefficient masses.

The upper-shadow step is the finite projection-measure argument of
R. Lyons, *Determinantal probability measures*,
DOI: 10.1007/s10240-003-0016-0. Here both conditional transports use the
same unnormalized intermediate coefficient array. -/

open BigOperators Finset Matrix
open scoped Classical

namespace MOC

noncomputable section

variable {α β : Type*} [Fintype α] [Fintype β]

/-- Weighted Hall transport does not require a unit total mass. -/
theorem exists_equal_mass_transport_of_weighted_hall
    (R : α → β → Prop) (p : α → ℝ) (q : β → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hq : ∀ b, 0 ≤ q b)
    (he : ∑ a, p a = ∑ b, q b)
    (hall : ∀ S : Finset α, ∑ a ∈ S, p a ≤
      ∑ b ∈ univ.filter (fun b => ∃ a ∈ S, R a b), q b) :
    ∃ μ : α → β → ℝ, (∀ a b, 0 ≤ μ a b) ∧ (∀ a b, μ a b ≠ 0 → R a b) ∧
      (∀ a, ∑ b, μ a b = p a) ∧ (∀ b, ∑ a, μ a b = q b) := by
  classical
  let m := ∑ a, p a
  have hm : 0 ≤ m := sum_nonneg fun a _ => hp a
  by_cases hz : m = 0
  · have pe (a) : p a = 0 :=
      (sum_eq_zero_iff_of_nonneg (fun a _ => hp a)).mp hz _ (mem_univ a)
    have qe (b) : q b = 0 :=
      (sum_eq_zero_iff_of_nonneg (fun b _ => hq b)).mp (he.symm.trans hz) _ (mem_univ b)
    exact ⟨fun _ _ => 0, fun _ _ => le_rfl, fun _ _ h => (h rfl).elim,
      fun a => by simp [pe a], fun b => by simp [qe b]⟩
  have pos : 0 < m := lt_of_le_of_ne hm (Ne.symm hz)
  obtain ⟨w, hw, hR, hr, hc⟩ := exists_transport_of_weighted_hall R
    (fun a => p a / m) (fun b => q b / m)
    (fun a => div_nonneg (hp a) hm) (fun b => div_nonneg (hq b) hm)
    (by rw [← sum_div]; exact div_self hz)
    (by rw [← sum_div, ← he]; exact div_self hz)
    (fun S => by simp only [← sum_div]; exact div_le_div_of_nonneg_right (hall S) hm)
  refine ⟨fun a b => w a b * m, fun a b => mul_nonneg (hw a b) hm, ?_, ?_, ?_⟩
  · intro a b h
    exact hR a b (fun ha => h (by simp [ha]))
  · intro a
    rw [← sum_mul, hr, div_mul_cancel₀ _ pos.ne']
  · intro b
    rw [← sum_mul, hc, div_mul_cancel₀ _ pos.ne']

private theorem exterior_coeff_mass_eq
    (n : ℕ) (u : Fin n → ℂ) (hu : ∑ i, Complex.normSq (u i) = 1)
    (v : SubsetCube n → ℂ) (hv : subsetContraction n u *ᵥ v = 0) :
    ∑ I, Complex.normSq (((subsetContraction n u)ᴴ *ᵥ v) I) =
      ∑ I, Complex.normSq (v I) := by
  let C := subsetContraction n u
  have hCC : C * Cᴴ + Cᴴ * C = 1 := by
    rw [subsetContraction_anticommutator n u, ← Complex.ofReal_sum, hu,
      Complex.ofReal_one, one_smul]
  have ha : C *ᵥ (Cᴴ *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec]
    calc
      (C * Cᴴ) *ᵥ v = (C * Cᴴ + Cᴴ * C) *ᵥ v := by
        rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec v Cᴴ C, show C *ᵥ v = 0 from hv, Matrix.mulVec_zero, add_zero]
      _ = v := by rw [hCC, Matrix.one_mulVec]
  have hs (w : SubsetCube n → ℂ) :
      ((∑ j, Complex.normSq (w j) : ℝ) : ℂ) = star w ⬝ᵥ w := by
    rw [Complex.ofReal_sum]
    unfold dotProduct
    apply Finset.sum_congr rfl
    intro j _
    simpa only [Pi.star_apply, mul_comm] using (Complex.mul_conj (w j)).symm
  apply Complex.ofReal_injective
  rw [hs, hs]
  change star (Cᴴ *ᵥ v) ⬝ᵥ (Cᴴ *ᵥ v) = star v ⬝ᵥ v
  rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose, ← Matrix.dotProduct_mulVec, ha]

/-- Creation in an empty unit mode admits an inclusion-supported transport
of the squared coefficients. No decomposability or normalization of the
remaining exterior state is required. -/
theorem exists_exterior_creation_transport
    (n : ℕ) (u : Fin n → ℂ) (hu : ∑ i, Complex.normSq (u i) = 1)
    (v : SubsetCube n → ℂ) (hv : subsetContraction n u *ᵥ v = 0) :
    ∃ μ : SubsetCube n → SubsetCube n → ℝ,
      (∀ I J, 0 ≤ μ I J) ∧
      (∀ I J, μ I J ≠ 0 → subsetCubeLabels n I ⊆ subsetCubeLabels n J) ∧
      (∀ I, ∑ J, μ I J = Complex.normSq (v I)) ∧
      (∀ J, ∑ I, μ I J = Complex.normSq (((subsetContraction n u)ᴴ *ᵥ v) J)) := by
  let C := subsetContraction n u
  have hCC : C * Cᴴ + Cᴴ * C = 1 := by
    rw [subsetContraction_anticommutator n u, ← Complex.ofReal_sum, hu,
      Complex.ofReal_one, one_smul]
  have ha : C *ᵥ (Cᴴ *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec]
    calc
      (C * Cᴴ) *ᵥ v = (C * Cᴴ + Cᴴ * C) *ᵥ v := by
        rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec v Cᴴ C, show C *ᵥ v = 0 from hv, Matrix.mulVec_zero, add_zero]
      _ = v := by rw [hCC, Matrix.one_mulVec]
  apply exists_equal_mass_transport_of_weighted_hall
    (fun I J => subsetCubeLabels n I ⊆ subsetCubeLabels n J)
    (fun I => Complex.normSq (v I))
    (fun J => Complex.normSq ((Cᴴ *ᵥ v) J))
    (fun _ => Complex.normSq_nonneg _) (fun _ => Complex.normSq_nonneg _)
    (exterior_coeff_mass_eq n u hu v hv).symm
  intro S
  have hb := subsetContraction_shadow_bound n u hu (Cᴴ *ᵥ v) S
  change (∑ I ∈ S, Complex.normSq ((C *ᵥ (Cᴴ *ᵥ v)) I)) ≤ _ at hb
  rw [ha] at hb
  convert hb using 2
  ext I
  simp only [mem_filter, mem_univ, true_and]


/-- A pair of one-mode creations in opposite coordinates of a common
exterior coefficient array gives a joint transport between the two
crossed squared-coefficient arrays. In the transport one label-set
shrinks and the other grows. Its marginals are not restricted to
decomposable tensors. -/
theorem exists_crossed_exterior_transport
    (n m : ℕ) (x : Fin m → ℂ) (y : Fin n → ℂ)
    (hx : ∑ i, Complex.normSq (x i) = 1) (hy : ∑ i, Complex.normSq (y i) = 1)
    (w : SubsetCube n → SubsetCube m → ℂ)
    (hrow : ∀ I, subsetContraction m x *ᵥ w I = 0)
    (hcol : ∀ J, subsetContraction n y *ᵥ (fun I => w I J) = 0) :
    let L (I : SubsetCube n) (J : SubsetCube m) :=
      ((subsetContraction m x)ᴴ *ᵥ w I) J
    let R (K : SubsetCube n) (L : SubsetCube m) :=
      ((subsetContraction n y)ᴴ *ᵥ (fun I => w I L)) K
    ∃ μ : (SubsetCube n × SubsetCube m) → (SubsetCube n × SubsetCube m) → ℝ,
      (∀ a b, 0 ≤ μ a b) ∧
      (∀ a b, μ a b ≠ 0 →
        subsetCubeLabels n a.1 ⊆ subsetCubeLabels n b.1 ∧
        subsetCubeLabels m b.2 ⊆ subsetCubeLabels m a.2) ∧
      (∀ a, ∑ b, μ a b = Complex.normSq (L a.1 a.2)) ∧
      (∀ b, ∑ a, μ a b = Complex.normSq (R b.1 b.2)) := by
  classical
  intro L R
  choose p hp hpS hpR hpC using fun I => exists_exterior_creation_transport m x hx (w I) (hrow I)
  choose q hq hqS hqR hqC using fun J => exists_exterior_creation_transport n y hy
    (fun I => w I J) (hcol J)
  let mass (I : SubsetCube n) (J : SubsetCube m) := Complex.normSq (w I J)
  let μ (a b : SubsetCube n × SubsetCube m) := p a.1 b.2 a.2 * q b.2 a.1 b.1 / mass a.1 b.2
  have hpzero {I L} (h : mass I L = 0) (J) : p I L J = 0 :=
    (sum_eq_zero_iff_of_nonneg (fun J _ => hp I L J)).mp ((hpR I L).trans h) _ (mem_univ J)
  have hqzero {I L} (h : mass I L = 0) (K) : q L I K = 0 :=
    (sum_eq_zero_iff_of_nonneg (fun K _ => hq L I K)).mp ((hqR L I).trans h) _ (mem_univ K)
  refine ⟨μ, fun a b => div_nonneg (mul_nonneg (hp a.1 b.2 a.2) (hq b.2 a.1 b.1))
    (Complex.normSq_nonneg _), ?_, ?_, ?_⟩
  · intro a b h
    exact ⟨hqS b.2 a.1 b.1 (fun hz => h (by simp [μ, hz])), hpS a.1 b.2 a.2 (fun hz => h (by simp [μ, hz]))⟩
  · rintro ⟨I,J⟩
    rw [Fintype.sum_prod_type, ← sum_comm]
    calc
      _ = ∑ L, p I L J := by
        apply sum_congr rfl
        intro L _
        change (∑ K, p I L J * q L I K / mass I L) = _
        rw [← sum_div, ← mul_sum, hqR]
        by_cases hz : mass I L = 0
        · simp [hz, hpzero hz]
        · exact mul_div_cancel_right₀ _ hz
      _ = _ := hpC I J
  · rintro ⟨K,L₀⟩
    rw [Fintype.sum_prod_type]
    calc
      _ = ∑ I, q L₀ I K := by
        apply sum_congr rfl
        intro I _
        change (∑ J, p I L₀ J * q L₀ I K / mass I L₀) = _
        rw [← sum_div, ← sum_mul, hpR, mul_comm]
        by_cases hz : mass I L₀ = 0
        · simp [hz, hqzero hz]
        · exact mul_div_cancel_right₀ _ hz
      _ = _ := hqC L₀ K


end

end MOC
