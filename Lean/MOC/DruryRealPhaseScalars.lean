import MOC.DruryNonreal

/-! The scalar cancellation in a rank-one deformation for two distinct
real roots of a Hermitian pencil. -/

namespace MOC

noncomputable section

/-- The two real root contributions make the quadratic coefficient differ
from its conjugate by the linear coefficient. -/
theorem drury_distinct_real_phase_coefficients (r s h k : ℝ) (hr : r ≠ s)
    (a b : ℂ) (ha : a ≠ star a) (hb : b ≠ star b)
    (hsum : a * (h : ℂ) + b * (k : ℂ) = 1) :
    let L := ((r : ℂ) - (s : ℂ)) * (star a * (h : ℂ) - a * (h : ℂ))
    let K := (h : ℂ) * (k : ℂ) * ((s : ℂ) * (b * star b - star a * b) +
      (r : ℂ) * (a * star a - star b * a))
    L ≠ 0 ∧ K - star K = L := by
  let L := ((r : ℂ) - (s : ℂ)) * (star a * (h : ℂ) - a * (h : ℂ))
  let K := (h : ℂ) * (k : ℂ) * ((s : ℂ) * (b * star b - star a * b) +
    (r : ℂ) * (a * star a - star b * a))
  have hsum' : star a * (h : ℂ) + star b * (k : ℂ) = 1 := by
    simpa only [star_add, star_mul', star_one, Complex.star_def, Complex.conj_ofReal, mul_comm]
      using congrArg star hsum
  have hhn : (h : ℂ) ≠ 0 := by
    intro hh
    have he : b * (k : ℂ) = 1 := by simpa only [hh, mul_zero, zero_add] using hsum
    have he' : star b * (k : ℂ) = 1 := by simpa only [hh, mul_zero, zero_add] using hsum'
    have hkn : (k : ℂ) ≠ 0 := by
      intro hz
      rw [hz, mul_zero] at he
      exact zero_ne_one he
    exact hb (mul_right_cancel₀ hkn (he.trans he'.symm))
  have hL : L ≠ 0 := by
    dsimp only [L]
    rw [← sub_mul]
    exact mul_ne_zero (sub_ne_zero.mpr (Complex.ofReal_injective.ne hr))
      (mul_ne_zero (sub_ne_zero.mpr (Ne.symm ha)) hhn)
  have ha' : (k : ℂ) * (star a * b - star b * a) = star a - a := by
    linear_combination star a * hsum - a * hsum'
  refine ⟨hL, ?_⟩
  change K - star K = L
  calc
    _ = (h : ℂ) * ((r : ℂ) - (s : ℂ)) * ((k : ℂ) * (star a * b - star b * a)) := by
      simp only [K, star_mul', star_add, star_sub, star_star, Complex.star_def, Complex.conj_ofReal,
        Complex.conj_conj]
      ring
    _ = _ := by rw [ha']; dsimp only [L]; ring

set_option maxHeartbeats 1000000 in
/-- Substitution of the two resolvent factors into the rank-one compression
gives the linear and quadratic coefficients used in the phase-line argument. -/
theorem drury_distinct_real_resolvent_phase_coefficients (r s h k : ℝ)
    (a b κ : ℂ) (ha : 1 - κ * (r : ℂ) ≠ 0) (hb : 1 - κ * (s : ℂ) ≠ 0)
    (hsum : a * (h : ℂ) + b * (k : ℂ) = 1) :
    let R := (1 - κ * (r : ℂ))⁻¹
    let S := (1 - κ * (s : ℂ))⁻¹
    let p := star a * (h : ℂ)
    let q := star b * (k : ℂ)
    let α := R * p + S * q
    let β := (1 - R) * (a * (h : ℂ)) + (1 - S) * (b * (k : ℂ))
    let γ := (1 - R) * (a * p) + (1 - S) * (b * q)
    let ε := R * (h : ℂ) + S * (k : ℂ)
    let t := κ * R * S
    let L := ((r : ℂ) - (s : ℂ)) * (p - a * (h : ℂ))
    let K := (h : ℂ) * (k : ℂ) * ((s : ℂ) * (b * star b - star a * b) +
      (r : ℂ) * (a * star a - star b * a))
    α + β - 1 = t * L ∧ α * β - γ * ε = t * K := by
  let R := (1 - κ * (r : ℂ))⁻¹
  let S := (1 - κ * (s : ℂ))⁻¹
  let t := κ * R * S
  have hR : (1 - κ * (r : ℂ)) * R = 1 := mul_inv_cancel₀ ha
  have hS : (1 - κ * (s : ℂ)) * S = 1 := mul_inv_cancel₀ hb
  have hpq : star a * (h : ℂ) + star b * (k : ℂ) = 1 := by
    simpa only [star_add, star_mul', star_one, Complex.star_def, Complex.conj_ofReal, mul_comm]
      using congrArg star hsum
  have hdiff : R - S = t * ((r : ℂ) - (s : ℂ)) := by
    dsimp only [t]
    linear_combination S * hR - R * hS
  have hRS : R * (1 - S) = -t * (s : ℂ) := by
    dsimp only [t]
    linear_combination -R * hS
  have hSR : S * (1 - R) = -t * (r : ℂ) := by
    dsimp only [t]
    linear_combination -S * hR
  constructor
  · change (R * (star a * (h : ℂ)) + S * (star b * (k : ℂ))) +
      ((1 - R) * (a * (h : ℂ)) + (1 - S) * (b * (k : ℂ))) - 1 =
      t * (((r : ℂ) - (s : ℂ)) * (star a * (h : ℂ) - a * (h : ℂ)))
    linear_combination S * hpq + (1 - S) * hsum +
      (star a * (h : ℂ) - a * (h : ℂ)) * hdiff
  · change (R * (star a * (h : ℂ)) + S * (star b * (k : ℂ))) *
      ((1 - R) * (a * (h : ℂ)) + (1 - S) * (b * (k : ℂ))) -
      ((1 - R) * (a * (star a * (h : ℂ))) + (1 - S) * (b * (star b * (k : ℂ)))) *
      (R * (h : ℂ) + S * (k : ℂ)) =
      t * ((h : ℂ) * (k : ℂ) * ((s : ℂ) * (b * star b - star a * b) +
        (r : ℂ) * (a * star a - star b * a)))
    calc
      _ = (h : ℂ) * (k : ℂ) * (R * (1 - S) * (star a * b - b * star b) +
          S * (1 - R) * (star b * a - a * star a)) := by ring
      _ = _ := by rw [hRS, hSR]; ring

/-- A nonzero linear coefficient whose conjugate defect is the defect of
the quadratic coefficient forces a forbidden phase line. -/
theorem no_quadratic_support_of_laurent_phase_line (ξ D L K : ℂ) (hD : D ≠ 0)
    (hL : L ≠ 0) (hK : K - star K = L)
    (hpenalty : ∀ z : ℂ, z * star z = 1 →
      let d := ((1 - star z) * L + (z + star z - 2) * K) * D
      (ξ * d).re ≤ -Complex.normSq d / 2) : False := by
  have hk : star K ≠ star (star K) := by
    intro h
    apply hL
    rw [star_star] at h
    rw [← hK, h, sub_self]
  apply no_quadratic_support_of_phase_line ξ D (star K) hD hk
  intro z hz
  have he : (z - 1) * K + (star z - 1) * star K =
      (1 - star z) * L + (z + star z - 2) * K := by
    linear_combination -(star z - 1) * hK
  simpa only [star_star, he] using hpenalty z hz

/-- In the repeated real-root case the nilpotent correction gives the same
phase-line cancellation for a nonreal auxiliary pencil eigenvalue. -/
theorem drury_repeated_real_phase_coefficients (ρ c h : ℝ) (a b : ℂ)
    (ha : a ≠ star a) (hsum : a * (c : ℂ) + b * (h : ℂ) = 1) :
    let p := star a * (h : ℂ)
    let L := p - star p
    let K := (p * (c : ℂ) - (h : ℂ)) * ((ρ : ℂ) * b + a)
    L ≠ 0 ∧ K - star K = L := by
  let p := star a * (h : ℂ)
  let L := p - star p
  let K := (p * (c : ℂ) - (h : ℂ)) * ((ρ : ℂ) * b + a)
  have hstar : star a * (c : ℂ) + star b * (h : ℂ) = 1 := by
    simpa only [star_add, star_mul', star_one, Complex.star_def, Complex.conj_ofReal, mul_comm]
      using congrArg star hsum
  have hp : star p = a * (h : ℂ) := by
    simp only [p, star_mul', star_star, Complex.star_def, Complex.conj_ofReal, Complex.conj_conj]
  have hhn : (h : ℂ) ≠ 0 := by
    intro hh
    have he : a * (c : ℂ) = 1 := by simpa only [hh, mul_zero, add_zero] using hsum
    have he' : star a * (c : ℂ) = 1 := by simpa only [hh, mul_zero, add_zero] using hstar
    have hcn : (c : ℂ) ≠ 0 := by
      intro hc
      rw [hc, mul_zero] at he
      exact zero_ne_one he
    exact ha (mul_right_cancel₀ hcn (he.trans he'.symm))
  have hL : L ≠ 0 := by
    dsimp only [L]
    rw [hp, show p = star a * (h : ℂ) from rfl, ← sub_mul]
    exact mul_ne_zero (sub_ne_zero.mpr (Ne.symm ha)) hhn
  have hpc : p * (c : ℂ) - (h : ℂ) = -star b * (h : ℂ) ^ 2 := by
    dsimp only [p]
    linear_combination (h : ℂ) * hstar
  have hKa : K = -star b * (h : ℂ) ^ 2 * ((ρ : ℂ) * b + a) := by
    dsimp only [K]
    rw [hpc]
  have hKa' : star K = -b * (h : ℂ) ^ 2 * ((ρ : ℂ) * star b + star a) := by
    rw [hKa]
    simp only [star_mul', star_neg, star_pow, star_add, star_star, Complex.star_def,
      Complex.conj_ofReal, Complex.conj_conj]
  have hab : (h : ℂ) * (a * star b - star a * b) = a - star a := by
    linear_combination a * hstar - star a * hsum
  refine ⟨hL, ?_⟩
  change K - star K = L
  rw [hKa', hKa]
  dsimp only [L]
  rw [hp]
  dsimp only [p]
  linear_combination -(h : ℂ) * hab

set_option maxHeartbeats 1000000 in
/-- The two compression coefficients for a repeated real resolvent root
both factor by the same nonzero resolvent correction. -/
theorem drury_repeated_real_resolvent_phase_coefficients (ρ c h : ℝ) (a b κ : ℂ)
    (hρ : 1 - κ * (ρ : ℂ) ≠ 0)
    (hsum : a * (c : ℂ) + b * (h : ℂ) = 1) :
    let R := (1 - κ * (ρ : ℂ))⁻¹
    let t := κ * R ^ 2
    let p := star a * (h : ℂ)
    let α := R + t * p
    let β := 1 - R - t * (a * (h : ℂ))
    let γ := (1 - R) * (a + b * p) - t * (a * p)
    let ε := R * (c : ℂ) + t * (h : ℂ)
    let L := p - star p
    let K := (p * (c : ℂ) - (h : ℂ)) * ((ρ : ℂ) * b + a)
    α + β - 1 = t * L ∧ α * β - γ * ε = t * K := by
  let R := (1 - κ * (ρ : ℂ))⁻¹
  let t := κ * R ^ 2
  let p := star a * (h : ℂ)
  have hp : star p = a * (h : ℂ) := by
    simp only [p, star_mul', star_star, Complex.star_def, Complex.conj_ofReal, Complex.conj_conj]
  have hR : R * (R - 1) = (ρ : ℂ) * t := by
    have he : (1 - κ * (ρ : ℂ)) * R = 1 := mul_inv_cancel₀ hρ
    dsimp only [t]
    linear_combination R * he
  constructor
  · change (R + t * p) + (1 - R - t * (a * (h : ℂ))) - 1 = t * (p - star p)
    rw [hp]
    ring
  · change (R + t * p) * (1 - R - t * (a * (h : ℂ))) -
      ((1 - R) * (a + b * p) - t * (a * p)) * (R * (c : ℂ) + t * (h : ℂ)) =
      t * ((p * (c : ℂ) - (h : ℂ)) * ((ρ : ℂ) * b + a))
    linear_combination (R * (R - 1) + t * (R - 1) * p) * hsum +
      b * (p * (c : ℂ) - (h : ℂ)) * hR

end

end MOC
