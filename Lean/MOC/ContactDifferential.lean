import MOC.SpectralKKT
import MOC.SharpContactImaginaryShifts
import MOC.ProjectiveTransport

/-! The polynomial contact differential in the raw spectral coordinates, with
the two geometric gauge directions. Unlike the logarithmic formula the sum of
omitted-factor products also applies at vanishing cross sums. The contact
setting is from Zheng, DOI: 10.13140/RG.2.2.36790.25923. -/

open Matrix BigOperators

namespace MOC

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Directional derivative of an exact matching product in spectral
velocities `a'`, `b'`. -/
noncomputable def matchingProductVelocity (a b a' b' : ι → ℂ) (σ : Equiv.Perm ι) : ℂ :=
  ∑ j, (∏ k ∈ Finset.univ.erase j, (a (σ k) + b k)) * (a' (σ j) + b' j)

/-- The raw polynomial formula remains valid where any matching products vanish. -/
theorem hasDerivAt_matchingProduct_affine_spectra (a b a' b' : ι → ℂ) (σ : Equiv.Perm ι) :
    HasDerivAt (fun z : ℂ => matchingProduct (fun i => a i + z * a' i)
      (fun i => b i + z * b' i) σ) (matchingProductVelocity a b a' b' σ) 0 := by
  have hd (j : ι) :
      HasDerivAt (fun z : ℂ => (a (σ j) + z * a' (σ j)) + (b j + z * b' j))
      (a' (σ j) + b' j) 0 := by
    have h1 := (((hasDerivAt_id (0 : ℂ)).mul_const (a' (σ j))).const_add (a (σ j)))
    have h2 := (((hasDerivAt_id (0 : ℂ)).mul_const (b' j)).const_add (b j))
    simpa using h1.add h2
  simpa [matchingProduct, matchingProductVelocity] using
    (HasDerivAt.finset_prod (u := Finset.univ) (fun j _ => hd j))

/-- Difference-Jacobian test for two matching labels. -/
theorem hasDerivAt_matchingDifference_affine_spectra (a b a' b' : ι → ℂ)
    (r q : Equiv.Perm ι) :
    HasDerivAt (fun z : ℂ =>
      matchingProduct (fun i => a i + z * a' i) (fun i => b i + z * b' i) r -
      matchingProduct (fun i => a i + z * a' i) (fun i => b i + z * b' i) q)
      (matchingProductVelocity a b a' b' r - matchingProductVelocity a b a' b' q) 0 :=
  (hasDerivAt_matchingProduct_affine_spectra a b a' b' r).sub
    (hasDerivAt_matchingProduct_affine_spectra a b a' b' q)

/-- Where there is no zero denominator, one can read the same derivative
as the matching product times its logarithmic derivative. -/
theorem matchingProductVelocity_eq_mul_sum_div (a b a' b' : ι → ℂ)
    (σ : Equiv.Perm ι) (hn : ∀ j, a (σ j) + b j ≠ 0) :
    matchingProductVelocity a b a' b' σ = matchingProduct a b σ *
      ∑ j, (a' (σ j) + b' j) / (a (σ j) + b j) := by
  rw [matchingProductVelocity, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [matchingProduct, ← Finset.prod_erase_mul _ _ (Finset.mem_univ j), mul_assoc]
  congr 1
  field_simp [hn j]

/-- Opposite translation belongs to the kernel of every matching
coordinate, not just the selected differences. -/
theorem matchingProductVelocity_opposite_translation (a b : ι → ℂ) (c : ℂ)
    (σ : Equiv.Perm ι) :
    matchingProductVelocity a b (fun _ => c) (fun _ => -c) σ = 0 := by
  simp [matchingProductVelocity]

/-- The infinitesimal common fractional motion has the same logarithmic
scale factor in every matching, including those with zero factors.
Here `c` is the simultaneous infinitesimal scaling compensation. -/
theorem matchingProductVelocity_fractional_scaled (a b : ι → ℂ) (c : ℂ)
    (σ : Equiv.Perm ι) :
    matchingProductVelocity a b (fun i => a i ^ 2 - c * a i)
      (fun j => -(b j ^ 2) - c * b j) σ =
      matchingProduct a b σ *
        ((∑ i, a i) - (∑ j, b j) - (Fintype.card ι : ℂ) * c) := by
  have h (j : ι) : a (σ j) ^ 2 - c * a (σ j) + (-(b j ^ 2) - c * b j) =
      (a (σ j) + b j) * (a (σ j) - b j - c) := by ring
  unfold matchingProductVelocity
  simp only [h, ← mul_assoc, Finset.prod_erase_mul _ _ (Finset.mem_univ _)]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    Equiv.sum_comp σ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rfl

/-- The corrected fractional motion lies in the kernel with arbitrary
spectra; no division by a cross sum is needed. -/
theorem matchingProductVelocity_fractional_gauge [Nonempty ι] (a b : ι → ℂ)
    (σ : Equiv.Perm ι) :
    let c : ℂ := ((∑ i, a i) - ∑ j, b j) / (Fintype.card ι : ℂ)
    matchingProductVelocity a b (fun i => a i ^ 2 - c * a i)
      (fun j => -(b j ^ 2) - c * b j) σ = 0 := by
  intro c
  have hn : (Fintype.card ι : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [matchingProductVelocity_fractional_scaled]
  have h : (Fintype.card ι : ℂ) * c = (∑ i, a i) - ∑ j, b j := by
    dsimp only [c]
    exact mul_div_cancel₀ _ hn
  rw [h, sub_self, mul_zero]

end MOC
