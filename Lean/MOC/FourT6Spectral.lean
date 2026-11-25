import MOC.FourT6Source
import MOC.FourCoincidence
import MOC.TwoExceptions
import Mathlib.Tactic.Lift

/-! The T6 chart in the coordinates of the original spectral gaps. -/

namespace MOC

set_option maxHeartbeats 2000000 in
/-- Regular spectral data with the six T6 contacts satisfy the real
projective gap equations, also when the remaining parameter is real. -/
theorem exists_fourT6_spectral_gap_chart (a b : Fin 4 → ℂ) (η : ℂ) (H : ℝ)
    (ha : Function.Injective a) (hb : Function.Injective b) (hab : ∀ i j, a i + b j ≠ 0)
    (hη : η ≠ 0)
    (hc : ∀ i ∈ fourT6ContactIndices, (η * matchingProduct a b (fourPerm i).symm).re = H) :
    let g : Fin 24 → ℝ := fun i => (η * matchingProduct a b (fourPerm i).symm).re - H
    ∃ (h r s p : ℝ) (v : ℂ) (ρ : ℝ),
      h ≠ 0 ∧ h ≠ 1 ∧ r ≠ 0 ∧ r ≠ 1 ∧ s ≠ 0 ∧ s ≠ 1 ∧ p ≠ 0 ∧ p ≠ 1 ∧
      v ≠ 0 ∧ v ≠ 1 ∧ 1 + ((h : ℂ) - 1) * v ≠ 0 ∧ (ρ = 0 ↔ v.im = 0) ∧
      let A := h * r - h - r
      let N := Complex.normSq v
      let O := Complex.normSq (v - 1)
      let D := Complex.normSq ((A : ℂ) * v + r)
      let K := h * r * (r - 1) / D
      let J := (A * N + r * (2 * v.re - 1)) / D
      let L := r / ((h - 1) * N)
      let M := h * (r - 1) / ((h - 1) * O)
      let E := ρ * s * (p - 1)
      0 < D ∧ g 3 = ρ * K * (p - 1) ∧ g 7 = ρ * L * p * (s - 1) ∧
      g 10 = ρ * M * p * (s - 1) ∧ g 12 = -ρ * s ∧ g 9 = g 7 + s * g 3 ∧
      g 18 = g 7 + E ∧ g 19 = g 3 + E * (1 + J - K) ∧ g 22 = g 3 + E * (1 + h * J - K) := by
  dsimp only
  obtain ⟨k, z, C, hk, hz₀, hz₁, hC, hsep, hprod⟩ := exists_fourT7_projective_products a b ha hb hab
  let w := C 0
  let v := C 1
  let r := C 2
  let c := C 3
  have hvec : C = ![w, v, r, c] := by
    funext j
    fin_cases j <;> rfl
  rw [hvec] at hC hsep hprod
  let κ := η * k
  let F := fourT7ProjectiveProduct z ![w, v, r, c]
  have hproj (i : Fin 24) : (η * matchingProduct a b (fourPerm i).symm).re = (κ * F i).re := by
    rw [hprod]
    dsimp only [κ, F]
    rw [mul_assoc]
  have hcontact (i : Fin 24) (hi : i ∈ fourT6ContactIndices) : (κ * F i).re = H :=
    (hproj i).symm.trans (hc i hi)
  have hκ : κ ≠ 0 := mul_ne_zero hη hk
  obtain ⟨hri, hdir, h, t, s, hhi, hti, hsi, hh₀, hh₁, ht₀, ht₁, hs₀, hs₁,
    hw, hG, hden, hz, hc'⟩ :=
    fourT6_chart_real_parameters z w v r c κ H hκ hz₀ hz₁ hC hsep hcontact
  lift h to ℝ using hhi
  lift t to ℝ using hti
  lift s to ℝ using hsi
  let R := r.re
  have hr : (R : ℂ) = r := Complex.ext (by simp [R]) (by simpa using hri.symm)
  rw [← hr] at hC hsep hdir hw hden hc'
  let p : ℝ := t⁻¹
  have hpc : (p : ℂ) = (t : ℂ)⁻¹ := by simp [p]
  have htc : (t : ℂ) * (p : ℂ) = 1 := by rw [hpc, mul_inv_cancel₀ ht₀]
  have hp₀ : p ≠ 0 := inv_ne_zero (by exact_mod_cast ht₀)
  have hp₁ : p ≠ 1 := by
    intro hp
    apply ht₁
    simpa only [hp, Complex.ofReal_one, mul_one] using htc
  have hP' : (p : ℂ) * (v - R) - (v - z) =
      (p : ℂ) * (v - R - (t : ℂ) * (v - z)) := by
    linear_combination (v - z) * htc
  have hP : (p : ℂ) * (v - R) - (v - z) ≠ 0 := by
    rw [hP']
    exact mul_ne_zero (by exact_mod_cast hp₀) hden
  have hcsol : c = ((p : ℂ) * z * (v - R) - (R : ℂ) * (v - z)) /
      ((p : ℂ) * (v - R) - (v - z)) := by
    apply (eq_div_iff hP).mpr
    have hh := (eq_div_iff hden).mp hc'
    rw [hP']
    linear_combination (p : ℂ) * hh - (R : ℂ) * (v - z) * htc
  have hv₀ : v ≠ 0 := (hsep 1).1
  have hv₁ : v ≠ 1 := (hsep 1).2.1
  have hvr : v ≠ (R : ℂ) := hC.ne (by decide : (1 : Fin 4) ≠ 2)
  have hvz : v ≠ z := (hsep 1).2.2
  have hrz : (R : ℂ) ≠ z := (hsep 2).2.2
  have hzc : z ≠ c := (hsep 3).2.2.symm
  have hh₁' : h ≠ 1 := by exact_mod_cast hh₁
  let Z := (z - c) * (v - (R : ℂ))
  let ρ := (κ * Z).im * v.im
  have hμ : (κ * Z).im ≠ 0 := fun he =>
    (mul_ne_zero hκ (mul_ne_zero (sub_ne_zero.mpr hzc) (sub_ne_zero.mpr hvr)))
      (Complex.ext hdir he)
  have hρ : ρ = 0 ↔ v.im = 0 := by
    dsimp only [ρ]
    simp only [mul_eq_zero, hμ, false_or]
  have hg (i : Fin 24) :
      (η * matchingProduct a b (fourPerm i).symm).re - H =
        (κ * (fourT7ProjectiveProduct z ![w, v, (R : ℂ), c] i -
          fourT7ProjectiveProduct z ![w, v, (R : ℂ), c] 0)).re := by
    rw [hr, mul_sub, Complex.sub_re, hproj i, ← hproj 0, hc 0 (by decide)]
  have hchart := fourT6_projective_gap_identities h R s p z w v c κ
    hv₀ hv₁ hh₁' hvr hvz hrz hzc hG hP hz hw hcsol hdir
  refine ⟨h, R, s, p, v, ρ, by exact_mod_cast hh₀, hh₁', ?_, ?_,
    by exact_mod_cast hs₀, by exact_mod_cast hs₁, hp₀, hp₁, hv₀, hv₁, hG, hρ, ?_⟩
  · exact_mod_cast (hsep 2).1
  · exact_mod_cast (hsep 2).2.1
  · simpa only [hg, ρ, Z] using hchart

/-- At a T6 contact at index 12, the regular projective chart is real.
Both ordinary-minor defects vanish. Collisions have their own order-four bounds. -/
theorem fourT6_support_of_contact_twelve (a b : Fin 4 → ℂ) (η : ℂ) (H : ℝ)
    (hn : ∀ i, H ≤ (η * matchingProduct a b (fourPerm i).symm).re)
    (hc : ∀ i ∈ fourT6ContactIndices, (η * matchingProduct a b (fourPerm i).symm).re = H)
    (h12 : (η * matchingProduct a b (fourPerm 12).symm).re = H)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    H ≤ (η * determinantValue a b U).re := by
  have hbound (hh : Holds a b U) := four_lower_support_of_holds a b η H U hh hn
  by_cases ha : Function.Injective a
  swap
  · exact hbound (holds_four_of_repeated_spectrum a b U hU (Or.inl ha))
  by_cases hb : Function.Injective b
  swap
  · exact hbound (holds_four_of_repeated_spectrum a b U hU (Or.inr hb))
  by_cases hzero : ∃ i j, a i + b j = 0
  · obtain ⟨i, j, hij⟩ := hzero
    exact hbound (holds_four_of_opposite_entries a b U hU hij)
  by_cases hη : η = 0
  · simpa [hη] using hn 0
  have hab (i j : Fin 4) : a i + b j ≠ 0 := fun hij => hzero ⟨i, j, hij⟩
  obtain ⟨h, r, s, p, v, ρ, _, _, _, _, hs₀, _, _, _, _, _, _, _, _,
    hg3, hg7, hg10, hg12, hg9, hg18, hg19, hg22⟩ :=
    exists_fourT6_spectral_gap_chart a b η H ha hb hab hη hc
  let g : Fin 24 → ℝ := fun i => (η * matchingProduct a b (fourPerm i).symm).re - H
  have h12' : g 12 = 0 := sub_eq_zero.mpr h12
  have hρ : ρ = 0 := by
    rw [hg12] at h12'
    exact neg_eq_zero.mp ((mul_eq_zero.mp h12').resolve_right hs₀)
  simp only [hρ, zero_mul, neg_zero, add_zero] at hg3 hg7 hg10 hg19 hg22
  have hg9' : g 9 = 0 := by simpa only [hg7, hg3, mul_zero, add_zero] using hg9
  have hg18' : g 18 = 0 := by simpa only [hg7, hρ, zero_mul, add_zero] using hg18
  obtain ⟨_, _, _, hr19, _, _, hr22, _⟩ := fourT6_gap_relations a b η H hc
  have hg13 : g 13 = 0 := by
    linarith only [hr19, hg19, hg3, hg7, h12', hg18']
  have hg16 : g 16 = 0 := by
    linarith only [hr22, hg22, hg3, hg7, h12', hg18']
  apply fourT6_support_of_nonnegative_defects a b η H hn hc U hU
  change 0 ≤ fourT6DefectA g ∧ 0 ≤ fourT6DefectB g
  simp [fourT6DefectA, fourT6DefectB, hg3, hg7, hg10, hg9', h12', hg13, hg16, hg18']

end MOC
