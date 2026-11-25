import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! Positivity on a pole sector bounds the order of a Laurent term.
The real and imaginary parts of its leading coefficient are kept
explicit so the result applies after taking limits along rays. -/

open Set

namespace MOC

/-- On a sector of angle `π/m`, a nonzero Laurent leading term with
nonnegative real part has order at most `m`. At order `m` its leading
coefficient along the central ray is a positive real number. -/
theorem positive_laurent_sector (m k x y : ℝ) (hm : 0 < m) (hk : 0 < k)
    (hnz : x ≠ 0 ∨ y ≠ 0)
    (h : ∀ θ, |θ| < Real.pi / (2 * m) →
      0 ≤ x * Real.cos (k * θ) + y * Real.sin (k * θ)) :
    k ≤ m ∧ (k = m → 0 < x ∧ y = 0) := by
  let R := Real.pi / (2 * m)
  let S := Real.pi / (2 * k)
  have hR : 0 < R := div_pos Real.pi_pos (mul_pos two_pos hm)
  have hS : 0 < S := div_pos Real.pi_pos (mul_pos two_pos hk)
  have hx : 0 ≤ x := by simpa using h 0 (by simpa using hR)
  have hclosed : IsClosed {θ : ℝ | 0 ≤ x * Real.cos (k * θ) + y * Real.sin (k * θ)} :=
    isClosed_le continuous_const (by fun_prop)
  have hbound (θ : ℝ) (hθ : |θ| ≤ R) :
      0 ≤ x * Real.cos (k * θ) + y * Real.sin (k * θ) := by
    have hsub : Ioo (-R) R ⊆ {θ : ℝ | 0 ≤ x * Real.cos (k * θ) + y * Real.sin (k * θ)} :=
      fun t ht => h t (abs_lt.mpr ht)
    have ht : θ ∈ closure (Ioo (-R) R) := by
      rw [closure_Ioo (ne_of_lt (neg_lt_self hR))]
      exact abs_le.mp hθ
    exact hclosed.closure_subset_iff.mpr hsub ht
  have hSθ : k * S = Real.pi / 2 := by
    dsimp only [S]
    field_simp [hk.ne']
    ring
  have hb (hkm : m ≤ k) : 0 < x ∧ y = 0 := by
    have hSR : S ≤ R := div_le_div_of_nonneg_left Real.pi_pos.le (mul_pos two_pos hm)
      (by linarith only [hkm])
    have h₁ := hbound S (by rwa [abs_of_pos hS])
    have h₂ := hbound (-S) (by rwa [abs_neg, abs_of_pos hS])
    rw [hSθ, Real.cos_pi_div_two, Real.sin_pi_div_two, mul_zero, mul_one, zero_add] at h₁
    rw [mul_neg, hSθ, Real.cos_neg, Real.sin_neg, Real.cos_pi_div_two, Real.sin_pi_div_two,
      mul_zero, mul_neg, mul_one, zero_add] at h₂
    have hy : y = 0 := le_antisymm (by linarith only [h₂]) h₁
    exact ⟨lt_of_le_of_ne hx ((hnz.resolve_right (by simp [hy])).symm),hy⟩
  have hke : k ≤ m := by
    by_contra! hbad
    obtain ⟨hx',hy⟩ := hb hbad.le
    have hSR : S < R := div_lt_div_of_pos_left Real.pi_pos (mul_pos two_pos hm)
      (by linarith only [hbad])
    have hpi : Real.pi / 2 < Real.pi := by linarith only [Real.pi_pos]
    have hT : S < Real.pi / k := by
      apply (mul_lt_mul_right hk).mp
      rw [mul_comm S k, hSθ, div_mul_cancel₀ _ hk.ne']
      exact hpi
    let T := min R (Real.pi / k)
    have hsT : S < T := lt_min hSR hT
    let θ := (S + T) / 2
    have hS' : S < θ := by dsimp only [θ]; linarith only [hsT]
    have hT' : θ < T := by dsimp only [θ]; linarith only [hsT]
    have hp := h θ (by
      rw [abs_of_pos (hS.trans hS')]
      exact hT'.trans_le (min_le_left ..))
    have hlow : Real.pi / 2 < k * θ := by rw [← hSθ]; exact mul_lt_mul_of_pos_left hS' hk
    have hhigh : k * θ < Real.pi + Real.pi / 2 := by
      have he := mul_lt_mul_of_pos_left (hT'.trans_le (min_le_right R (Real.pi / k))) hk
      rw [mul_comm k (Real.pi / k), div_mul_cancel₀ _ hk.ne'] at he
      linarith only [he, Real.pi_pos]
    have hneg := mul_neg_of_pos_of_neg hx' (Real.cos_neg_of_pi_div_two_lt_of_lt hlow hhigh)
    exact (not_lt_of_ge (by simpa [hy] using hp)) hneg
  exact ⟨hke, fun he => hb he.ge⟩

end MOC
