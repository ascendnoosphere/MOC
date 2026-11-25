import MOC.CollinearKernelSupport
import MOC.MatchingProfileClosed
import MOC.Support

/-! A finite limit of normalized matching profiles cannot give a positive
deficit once the limiting gaps are nonnegative real numbers. -/

open BigOperators Filter Matrix
open scoped Topology

namespace MOC

/-- An exact additive matching profile with collinear limit and a normalized
positive deficit contradicts the collinear matching theorem. -/
theorem no_positive_deficit_of_finite_profile_limit {n : ℕ} {α : Type*}
    (l : Filter α) [NeBot l]
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitary U)
    (p : α → Equiv.Perm (Fin n) → ℂ) (q : Equiv.Perm (Fin n) → ℂ)
    (hp : ∀ᶠ t in l, ∃ a b : Fin n → ℂ, matchingProduct a b = p t)
    (hq : Tendsto p l (𝓝 q)) (γ : ℂ)
    (hline : ∀ σ, (q σ).im = γ.im)
    (hmax : ∀ σ, (q σ).re ≤ γ.re)
    (hgap : (∑ σ, signedWeight U σ * q σ) = γ + 1) : False := by
  obtain ⟨a, b, hab⟩ := (isClosed_additive_matching_profiles (ι := Fin n)).mem_of_tendsto hq hp
  have hl (σ : Equiv.Perm (Fin n)) : (Complex.I * matchingProduct a b σ).re = -γ.im := by
    rw [Complex.I_mul_re, congrFun hab σ, hline]
  have h := holds_of_all_collinear_matching_products a b Complex.I Complex.I_ne_zero (-γ.im) hl U hU
  obtain ⟨σ, hσ⟩ := (holds_iff_directional a b U).mp h 1
  simp only [one_mul, congrFun hab σ] at hσ
  have hd : determinantValue a b U = γ + 1 := by rwa [← hab, signed_determinant a b U hU] at hgap
  rw [hd, Complex.add_re, Complex.one_re] at hσ
  linarith only [hσ, hmax σ]

end MOC
