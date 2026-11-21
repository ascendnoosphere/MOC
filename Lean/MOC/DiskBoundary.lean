import MOC.Support
import MOC.Wielandt

/-! The matching products certify a quantitative margin for zero in a support disk. -/

open Matrix
open scoped ComplexConjugate

namespace MOC

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- If zero is attained, at least one matching product has squared modulus at
most the difference between the squared radius of the support disk and the
squared distance of its center from zero. -/
theorem exists_matching_normSq_le_disk_margin_of_singular (a b : ι → ℂ)
    {W : Matrix ι ι ℂ} (hW : IsUnitary W) (hzero : determinantValue a b W = 0)
    (z ξ : ℂ)
    (hdisk : ∀ σ : Equiv.Perm ι, (ξ * (matchingProduct a b σ - z)).re ≤
      -Complex.normSq (matchingProduct a b σ - z) / 2) :
    ∃ σ : Equiv.Perm ι,
      Complex.normSq (matchingProduct a b σ) ≤ 2 * (ξ * z).re - Complex.normSq z := by
  obtain ⟨σ, hσ⟩ := (holds_iff_directional a b W).mp
    (holds_of_singular a b hW hzero) (ξ - conj z)
  rw [hzero, mul_zero, Complex.zero_re, sub_mul, Complex.sub_re, mul_comm (conj z)] at hσ
  have h := hdisk σ
  rw [mul_sub, Complex.sub_re, Complex.normSq_sub] at h
  exact ⟨σ, by linarith only [h, hσ]⟩

/-- A support disk with margin below every squared matching modulus requires
strict circle-or-line separation of the signed spectra. -/
theorem strictlySeparatedByCircleOrLine_of_matching_disk_margin (a b : ι → ℂ) (z ξ : ℂ)
    (hdisk : ∀ σ : Equiv.Perm ι, (ξ * (matchingProduct a b σ - z)).re ≤
      -Complex.normSq (matchingProduct a b σ - z) / 2)
    (hmargin : ∀ σ : Equiv.Perm ι,
      2 * (ξ * z).re - Complex.normSq z < Complex.normSq (matchingProduct a b σ)) :
    StrictlySeparatedByCircleOrLine a (fun i => -b i) := by
  apply (not_exists_singular_iff_circle_or_line a b).mp
  rintro ⟨W, hW, hzero⟩
  obtain ⟨σ, hσ⟩ := exists_matching_normSq_le_disk_margin_of_singular a b hW hzero z ξ hdisk
  exact (not_lt_of_ge hσ) (hmargin σ)

/-- When no pair sums to zero, it suffices that zero lie on or outside a
support disk containing the matching products. -/
theorem strictlySeparatedByCircleOrLine_of_disk_boundary (a b : ι → ℂ) (z ξ : ℂ)
    (hregular : ∀ i j, a i + b j ≠ 0)
    (hdisk : ∀ σ : Equiv.Perm ι, (ξ * (matchingProduct a b σ - z)).re ≤
      -Complex.normSq (matchingProduct a b σ - z) / 2)
    (hprojected : (ξ * z).re ≤ Complex.normSq z / 2) :
    StrictlySeparatedByCircleOrLine a (fun i => -b i) := by
  refine strictlySeparatedByCircleOrLine_of_matching_disk_margin a b z ξ hdisk ?_
  intro σ
  have hnonzero : matchingProduct a b σ ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ => hregular (σ j) j
  exact lt_of_le_of_lt (by linarith only [hprojected]) (Complex.normSq_pos.mpr hnonzero)

end MOC
