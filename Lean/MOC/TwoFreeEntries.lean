import MOC.CommonWeights

/-! A common permutation law for one free entry on each side can be checked at four pairs. -/

open BigOperators Matrix

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Exchanging the spectra sends each matching to its inverse. -/
theorem weightedMatchingValue_swap (a b : ι → ℂ) (w : Equiv.Perm ι → ℝ) :
    weightedMatchingValue b a (fun σ => w σ.symm) = weightedMatchingValue a b w := by
  let e : Equiv.Perm (Equiv.Perm ι) :=
    ⟨fun σ => σ.symm, fun σ => σ.symm, fun _ => rfl, fun _ => rfl⟩
  have hp (σ : Equiv.Perm ι) : matchingProduct b a σ = matchingProduct a b σ.symm := by
    rw [matchingProduct_inverse]
    simp [matchingProduct, add_comm]
  unfold weightedMatchingValue
  simp only [hp]
  exact Equiv.sum_comp e (fun σ => (w σ : ℂ) * matchingProduct a b σ)

private theorem weight_agreement_swap (a b : ι → ℂ) (U : Matrix ι ι ℂ)
    (hU : IsUnitary U) (w : Equiv.Perm ι → ℝ) :
    weightedMatchingValue b a (fun σ => w σ.symm) = determinantValue b a Uᴴ ↔
      weightedMatchingValue a b w = determinantValue a b U := by
  have hd : determinantValue b a Uᴴ = determinantValue a b U := by
    simpa [determinantValue, add_comm] using
      (determinantValue_relative b a U (1 : Matrix ι ι ℂ) hU).symm
  rw [weightedMatchingValue_swap, hd]

/-- Agreement at two distinct values of the first entry implies agreement at
all values of that entry for the same weights. -/
theorem weightedMatchingValue_eq_of_two_left_updates (a b : ι → ℂ) (U : Matrix ι ι ℂ)
    (hU : IsUnitary U) (w : Equiv.Perm ι → ℝ) (i : ι) {s t : ℂ} (hst : s ≠ t)
    (hs : weightedMatchingValue (Function.update a i s) b w =
      determinantValue (Function.update a i s) b U)
    (ht : weightedMatchingValue (Function.update a i t) b w =
      determinantValue (Function.update a i t) b U) (x : ℂ) :
    weightedMatchingValue (Function.update a i x) b w =
      determinantValue (Function.update a i x) b U := by
  have hV : IsUnitary Uᴴ := ⟨by simpa using hU.2, by simpa using hU.1⟩
  exact (weight_agreement_swap _ _ _ hU w).mp <|
    weightedMatchingValue_eq_of_two_updates b a Uᴴ hV (fun σ => w σ.symm) i hst
      ((weight_agreement_swap _ _ _ hU w).mpr hs)
      ((weight_agreement_swap _ _ _ hU w).mpr ht) x

/-- For one designated entry in each spectrum, one fixed law works everywhere
if it works at the four pairs formed from two distinct values on each side. -/
theorem weightedMatchingValue_eq_iff_four_corners (a b : ι → ℂ) (U : Matrix ι ι ℂ)
    (hU : IsUnitary U) (w : Equiv.Perm ι → ℝ) (i j : ι)
    {s t u v : ℂ} (hst : s ≠ t) (huv : u ≠ v) :
    (∀ x y : ℂ, weightedMatchingValue (Function.update a i x) (Function.update b j y) w =
      determinantValue (Function.update a i x) (Function.update b j y) U) ↔
    ∀ x ∈ ({s, t} : Set ℂ), ∀ y ∈ ({u, v} : Set ℂ),
      weightedMatchingValue (Function.update a i x) (Function.update b j y) w =
        determinantValue (Function.update a i x) (Function.update b j y) U := by
  constructor
  · exact fun h x _ y _ => h x y
  · intro h x y
    have hrow (z : ℂ) (hz : z ∈ ({s, t} : Set ℂ)) :
        weightedMatchingValue (Function.update a i z) (Function.update b j y) w =
          determinantValue (Function.update a i z) (Function.update b j y) U :=
      weightedMatchingValue_eq_of_two_updates _ b U hU w j huv
        (h z hz u (by simp)) (h z hz v (by simp)) y
    exact weightedMatchingValue_eq_of_two_left_updates a _ U hU w i hst
      (hrow s (by simp)) (hrow t (by simp)) x

/-- A probability law that passes all four tests proves the hull inclusion
for every choice of the two free entries. -/
theorem holds_of_four_corner_weights (a b : ι → ℂ) (U : Matrix ι ι ℂ)
    (hU : IsUnitary U) (i j : ι) {s t u v : ℂ} (hst : s ≠ t) (huv : u ≠ v)
    (w : Equiv.Perm ι → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hs : ∑ σ, w σ = 1)
    (h : ∀ x ∈ ({s, t} : Set ℂ), ∀ y ∈ ({u, v} : Set ℂ),
      weightedMatchingValue (Function.update a i x) (Function.update b j y) w =
        determinantValue (Function.update a i x) (Function.update b j y) U)
    (x y : ℂ) : Holds (Function.update a i x) (Function.update b j y) U :=
  holds_of_weights w hw hs
    ((weightedMatchingValue_eq_iff_four_corners a b U hU w i j hst huv).mpr h x y)

end

end MOC
