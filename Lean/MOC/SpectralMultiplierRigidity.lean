import MOC.SpectralKKT
import MOC.StationaryPivot

/-! The spectral and unitary stationarity equations can use one normalized
maximizer. Erased products express their common matrix even at zero pair sums. -/

open BigOperators Matrix
open scoped ComplexConjugate

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem matchingProduct_update_add_one (a b : ι → ℂ)
    (σ : Equiv.Perm ι) (k : ι ⊕ ι) :
    let a' (i : ι) := a i + if k = Sum.inl i then 1 else 0
    let b' (j : ι) := b j + if k = Sum.inr j then 1 else 0
    matchingProduct a' b' σ - matchingProduct a b σ =
      matchingCoordinateCoefficient a b σ k := by
  intro a' b'
  let j := Sum.elim σ.symm id k
  let f (l : ι) := a (σ l) + b l
  have he (l : ι) : a' (σ l) + b' l = f l + if l = j then 1 else 0 := by
    cases k with
    | inl i =>
      have h : i = σ l ↔ l = σ.symm i := by
        constructor
        · intro hi
          rw [hi, σ.symm_apply_apply]
        · intro hi
          rw [hi, σ.apply_symm_apply]
      simp only [a', b', Sum.inl.injEq, reduceCtorEq, if_false, add_zero, f, j,
        Sum.elim_inl, h]
      ring
    | inr i =>
      simp only [a', b', reduceCtorEq, if_false, add_zero, Sum.inr.injEq, f, j,
        Sum.elim_inr, id_eq, eq_comm]
      ring
  have hp : (∏ l ∈ Finset.univ.erase j, (f l + if l = j then 1 else 0)) =
      ∏ l ∈ Finset.univ.erase j, f l := by
    exact Finset.prod_congr rfl fun l hl => by simp [(Finset.mem_erase.mp hl).1]
  have hc : matchingCoordinateCoefficient a b σ k = ∏ l ∈ Finset.univ.erase j, f l := by
    cases k <;> rfl
  unfold matchingProduct
  simp_rw [he]
  change (∏ l, (f l + if l = j then 1 else 0)) - (∏ l, f l) = _
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j), hp,
    if_pos rfl, ← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ j), hc]
  ring

private theorem real_signed_coordinate_coefficient (a b : ι → ℂ) (U : Matrix ι ι ℂ)
    (hU : IsUnitary U) (k : ι ⊕ ι) :
    ∑ σ, (realSignedWeight U σ : ℂ) * matchingCoordinateCoefficient a b σ k =
      determinantCoordinateCoefficient a b U k := by
  let a' (i : ι) := a i + if k = Sum.inl i then 1 else 0
  let b' (j : ι) := b j + if k = Sum.inr j then 1 else 0
  have hc (σ : Equiv.Perm ι) : matchingProduct a' b' σ - matchingProduct a b σ =
      matchingCoordinateCoefficient a b σ k := matchingProduct_update_add_one a b σ k
  simp_rw [← hc, mul_sub, Finset.sum_sub_distrib]
  rw [real_signed_determinant a' b' U hU, real_signed_determinant a b U hU,
    ← signed_determinant a' b' U hU, ← signed_determinant a b U hU,
    ← Finset.sum_sub_distrib]
  unfold determinantCoordinateCoefficient
  apply Finset.sum_congr rfl
  intro σ _
  rw [← mul_sub, hc]

/-- Cofactor marginal of the signed law minus an active matching law. -/
def spectralMultiplierStress (a b : ι → ℂ) (U : Matrix ι ι ℂ) (η : ℂ)
    (activeWeight : Equiv.Perm ι → ℝ) (i j : ι) : ℂ :=
  ∑ σ : Equiv.Perm ι, if σ j = i then
    η * ((realSignedWeight U σ - activeWeight σ : ℝ) : ℂ) *
      matchingCoordinateCoefficient a b σ (.inr j) else 0

private theorem sum_spectralMultiplierStress_row (a b : ι → ℂ) (U : Matrix ι ι ℂ)
    (η : ℂ) (activeWeight : Equiv.Perm ι → ℝ) (i : ι) :
    ∑ j, spectralMultiplierStress a b U η activeWeight i j =
      ∑ σ : Equiv.Perm ι, η * ((realSignedWeight U σ - activeWeight σ : ℝ) : ℂ) *
        matchingCoordinateCoefficient a b σ (.inl i) := by
  unfold spectralMultiplierStress
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  have hx (j : ι) : σ j = i ↔ j = σ.symm i := by
    constructor
    · intro hj
      rw [← hj, σ.symm_apply_apply]
    · intro hj
      rw [hj, σ.apply_symm_apply]
  simp only [hx, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    matchingCoordinateCoefficient]

private theorem sum_spectralMultiplierStress_col (a b : ι → ℂ) (U : Matrix ι ι ℂ)
    (η : ℂ) (activeWeight : Equiv.Perm ι → ℝ) (j : ι) :
    ∑ i, spectralMultiplierStress a b U η activeWeight i j =
      ∑ σ : Equiv.Perm ι, η * ((realSignedWeight U σ - activeWeight σ : ℝ) : ℂ) *
        matchingCoordinateCoefficient a b σ (.inr j) := by
  unfold spectralMultiplierStress
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]

private theorem stress_sum_eq_coordinate_balance (a b : ι → ℂ) (U : Matrix ι ι ℂ)
    (hU : IsUnitary U) (η : ℂ) (activeWeight : Equiv.Perm ι → ℝ) (k : ι ⊕ ι) :
    (∑ σ : Equiv.Perm ι, η * ((realSignedWeight U σ - activeWeight σ : ℝ) : ℂ) *
      matchingCoordinateCoefficient a b σ k) =
    η * (determinantCoordinateCoefficient a b U k -
      ∑ σ : Equiv.Perm ι, (activeWeight σ : ℂ) * matchingCoordinateCoefficient a b σ k) := by
  simp only [Complex.ofReal_sub, mul_assoc η, sub_mul, ← Finset.mul_sum,
    Finset.sum_sub_distrib, real_signed_coordinate_coefficient a b U hU k]

/-- The three stress equations are valid even when a sum `a i + b j` is
zero. The row and column equations use the spectral multiplier. The entry
equation uses the same mixer's directional maximum. -/
theorem spectralMultiplierStress_equations (a b : ι → ℂ) (U : Matrix ι ι ℂ)
    (hU : IsUnitary U) (η : ℂ) (g H : ℝ) (activeWeight : Equiv.Perm ι → ℝ)
    (hactive : ∀ σ, activeWeight σ ≠ 0 → (η * matchingProduct a b σ).re = H)
    (hmax : ∀ V : Matrix ι ι ℂ, IsUnitary V →
      (η * determinantValue a b V).re ≤ (η * determinantValue a b U).re)
    (hcoord : ∀ k : ι ⊕ ι, η * (determinantCoordinateCoefficient a b U k -
      ∑ σ : Equiv.Perm ι, (activeWeight σ : ℂ) * matchingCoordinateCoefficient a b σ k) =
      (((Fintype.card ι : ℝ) * g : ℝ) : ℂ) * conj (Sum.elim a b k)) :
    (∀ i, (∑ j, spectralMultiplierStress a b U η activeWeight i j) =
      (((Fintype.card ι : ℝ) * g : ℝ) : ℂ) * conj (a i)) ∧
    (∀ j, (∑ i, spectralMultiplierStress a b U η activeWeight i j) =
      (((Fintype.card ι : ℝ) * g : ℝ) : ℂ) * conj (b j)) ∧
    (∀ i j, ((a i + b j) * spectralMultiplierStress a b U η activeWeight i j).re =
      Complex.normSq (U i j) * (η * determinantValue a b U).re -
      H * (∑ σ : Equiv.Perm ι, if σ j = i then activeWeight σ else 0)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    rw [sum_spectralMultiplierStress_row, stress_sum_eq_coordinate_balance a b U hU]
    exact hcoord (.inl i)
  · intro j
    rw [sum_spectralMultiplierStress_col, stress_sum_eq_coordinate_balance a b U hU]
    exact hcoord (.inr j)
  · intro i j
    have he (σ : Equiv.Perm ι) (hσ : σ j = i) :
        (a i + b j) * matchingCoordinateCoefficient a b σ (.inr j) =
          matchingProduct a b σ := by
      unfold matchingCoordinateCoefficient matchingProduct
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j), hσ]
    have hterm (σ : Equiv.Perm ι) :
        ((a i + b j) * (if σ j = i then
          η * ((realSignedWeight U σ - activeWeight σ : ℝ) : ℂ) *
            matchingCoordinateCoefficient a b σ (.inr j) else 0)).re =
        (if σ j = i then realSignedWeight U σ * (η * matchingProduct a b σ).re else 0) -
        H * (if σ j = i then activeWeight σ else 0) := by
      by_cases hσ : σ j = i
      · simp only [if_pos hσ]
        rw [show (a i + b j) * (η * ((realSignedWeight U σ - activeWeight σ : ℝ) : ℂ) *
            matchingCoordinateCoefficient a b σ (.inr j)) =
          ((realSignedWeight U σ - activeWeight σ : ℝ) : ℂ) *
            (η * ((a i + b j) * matchingCoordinateCoefficient a b σ (.inr j))) by ring,
          he σ hσ, Complex.re_ofReal_mul]
        by_cases hActiveWeight : activeWeight σ = 0
        · simp only [hActiveWeight, sub_zero, mul_zero]
        · rw [hactive σ hActiveWeight]
          ring
      · simp only [if_neg hσ, mul_zero, Complex.zero_re, sub_zero]
    unfold spectralMultiplierStress
    rw [Finset.mul_sum, Complex.re_sum]
    simp only [hterm, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [stationary_realSignedWeight_pivot a b U hU η hmax]

/-- The global gap bound implies a directional unitary maximum for the
same spectra, mixer, and direction used in spectral stationarity. -/
theorem orbit_support_maximum_of_global_spectral_gap (a b : ι → ℂ)
    (U : Matrix ι ι ℂ) (η : ℂ) (g : ℝ)
    (henergy : spectralEnergy a b ≤ 1) (hη : Complex.normSq η = 1)
    (hgap : ∀ σ : Equiv.Perm ι, g ≤ (η * (determinantValue a b U - matchingProduct a b σ)).re)
    (hglobal : ∀ (c d : ι → ℂ) (V : Matrix ι ι ℂ) (κ : ℂ),
      spectralEnergy c d ≤ 1 → IsUnitary V → Complex.normSq κ = 1 →
      ∃ σ : Equiv.Perm ι, (κ * (determinantValue c d V - matchingProduct c d σ)).re ≤ g)
    (V : Matrix ι ι ℂ) (hV : IsUnitary V) :
    (η * determinantValue a b V).re ≤ (η * determinantValue a b U).re := by
  obtain ⟨σ, hσ⟩ := hglobal a b V η henergy hV hη
  have hu := hgap σ
  simp only [mul_sub, Complex.sub_re] at hσ hu
  linarith only [hσ, hu]

/-- A cancelling pair of spectral labels forces a zero mixer entry at a
strict directional maximum. -/
theorem zero_pivot_of_zero_pair_sum_at_strict_support_max (a b : ι → ℂ)
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) (η : ℂ)
    (hmax : ∀ V : Matrix ι ι ℂ, IsUnitary V →
      (η * determinantValue a b V).re ≤ (η * determinantValue a b U).re)
    (hstrict : ∀ σ : Equiv.Perm ι,
      (η * matchingProduct a b σ).re < (η * determinantValue a b U).re)
    (i j : ι) (hzero : a i + b j = 0) : U i j = 0 := by
  have hm (σ : Equiv.Perm ι) (hσ : σ j = i) : matchingProduct a b σ = 0 := by
    unfold matchingProduct
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    rwa [hσ]
  have hd : 0 < (η * determinantValue a b U).re := by
    simpa only [hm (Equiv.swap j i) (Equiv.swap_apply_left j i), mul_zero, Complex.zero_re]
      using hstrict (Equiv.swap j i)
  have hs : (∑ σ : Equiv.Perm ι, if σ j = i then
      realSignedWeight U σ * (η * matchingProduct a b σ).re else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro σ _
    by_cases hσ : σ j = i
    · simp only [if_pos hσ, hm σ hσ, mul_zero, Complex.zero_re]
    · simp only [if_neg hσ]
  rw [stationary_realSignedWeight_pivot a b U hU η hmax] at hs
  exact Complex.normSq_eq_zero.mp ((mul_eq_zero.mp hs).resolve_right hd.ne')

/-- A strict violation yields one normalized witness with spectral and
unitary stationarity. The active matching law gives the same matrix in
all three stress equations. -/
theorem exists_spectralMultiplierStress_of_not_holds [Nonempty ι]
    (a₀ b₀ : ι → ℂ) (U₀ : Matrix ι ι ℂ) (hU₀ : IsUnitary U₀) (hbad : ¬ Holds a₀ b₀ U₀) :
    ∃ (a b : ι → ℂ) (U : Matrix ι ι ℂ) (η : ℂ) (g H : ℝ) (activeWeight : Equiv.Perm ι → ℝ),
      IsUnitary U ∧ spectralEnergy a b = 1 ∧ Complex.normSq η = 1 ∧ 0 < g ∧
      (∑ i, a i) = (∑ i, b i) ∧
      (∑ i, (Complex.normSq (a i) : ℂ) * a i) =
        (∑ i, (Complex.normSq (b i) : ℂ) * b i) ∧
      ¬ IsStarNormal (diagonal a + U * diagonal b * Uᴴ) ∧
      (η * determinantValue a b U).re = H + g ∧
      (∀ σ, (η * matchingProduct a b σ).re ≤ H) ∧
      (∀ σ, 0 ≤ activeWeight σ) ∧ (∑ σ, activeWeight σ) = 1 ∧
      (∀ σ, activeWeight σ ≠ 0 → (η * matchingProduct a b σ).re = H) ∧
      (∀ i, (∑ j, spectralMultiplierStress a b U η activeWeight i j) =
        (((Fintype.card ι : ℝ) * g : ℝ) : ℂ) * conj (a i)) ∧
      (∀ j, (∑ i, spectralMultiplierStress a b U η activeWeight i j) =
        (((Fintype.card ι : ℝ) * g : ℝ) : ℂ) * conj (b j)) ∧
      (∀ i j, ((a i + b j) * spectralMultiplierStress a b U η activeWeight i j).re =
        Complex.normSq (U i j) * (η * determinantValue a b U).re -
        H * (∑ σ : Equiv.Perm ι, if σ j = i then activeWeight σ else 0)) := by
  classical
  obtain ⟨a, b, U, η, g, hU, hE, hη, hg, htrace, hcubic, hnormal, hgap, hglobal⟩ :=
    exists_balanced_support_gap_maximizer a₀ b₀ U₀ hU₀ hbad
  obtain ⟨s, w, hw, hw₁, _, hcoord⟩ := exists_active_matching_coordinate_balance a b U hU η g
    hE hgap (fun c d he => hglobal c d U η he hU hη)
  let H := (η * determinantValue a b U).re - g
  let activeWeight (σ : Equiv.Perm ι) : ℝ := ∑ τ ∈ s, if τ.val = σ then w τ else 0
  have hActiveWeight (σ : Equiv.Perm ι) : 0 ≤ activeWeight σ := by
    unfold activeWeight
    apply Finset.sum_nonneg
    intro τ hτ
    split_ifs
    · exact hw τ hτ
    · exact le_rfl
  have hActiveWeight₁ : (∑ σ, activeWeight σ) = 1 := by
    unfold activeWeight
    rw [Finset.sum_comm]
    simpa only [Finset.sum_ite_eq, Finset.mem_univ, if_true] using hw₁
  have hActiveWeightsum (F : Equiv.Perm ι → ℂ) :
      (∑ σ, (activeWeight σ : ℂ) * F σ) = ∑ τ ∈ s, (w τ : ℂ) * F τ.val := by
    simp only [activeWeight, Complex.ofReal_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro τ _
    simp only [apply_ite, Complex.ofReal_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
  have ha (σ : Equiv.Perm ι) (hActiveWeightσ : activeWeight σ ≠ 0) : (η * matchingProduct a b σ).re = H := by
    by_contra hσ
    apply hActiveWeightσ
    unfold activeWeight
    apply Finset.sum_eq_zero
    intro τ _
    split_ifs with he
    · have ht := τ.property
      simp only [mul_sub, Complex.sub_re] at ht
      rw [← he] at hσ
      exact False.elim (hσ (by dsimp only [H]; linarith only [ht]))
    · rfl
  have hbalance (k : ι ⊕ ι) :
      η * (determinantCoordinateCoefficient a b U k -
        ∑ σ : Equiv.Perm ι, (activeWeight σ : ℂ) * matchingCoordinateCoefficient a b σ k) =
        (((Fintype.card ι : ℝ) * g : ℝ) : ℂ) * conj (Sum.elim a b k) := by
    have hk := hcoord k
    have hterm (τ : _) :
        (w τ : ℂ) * (η * (determinantCoordinateCoefficient a b U k -
          matchingCoordinateCoefficient a b τ.val k)) =
        η * ((w τ : ℂ) * determinantCoordinateCoefficient a b U k -
          (w τ : ℂ) * matchingCoordinateCoefficient a b τ.val k) := by ring
    simp only [hterm, ← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.sum_mul,
      ← Complex.ofReal_sum, hw₁, Complex.ofReal_one, one_mul] at hk
    rw [hActiveWeightsum]
    exact hk
  have hmax := orbit_support_maximum_of_global_spectral_gap a b U η g hE.le hη hgap hglobal
  refine ⟨a, b, U, η, g, H, activeWeight, hU, hE, hη, hg, htrace, hcubic, hnormal, ?_, ?_, hActiveWeight, hActiveWeight₁, ha,
    spectralMultiplierStress_equations a b U hU η g H activeWeight ha hmax hbalance⟩
  · dsimp only [H]
    ring
  · intro σ
    have hs := hgap σ
    simp only [mul_sub, Complex.sub_re] at hs
    dsimp only [H]
    linarith only [hs]

end

end MOC
