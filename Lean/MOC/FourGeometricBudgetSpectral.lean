import MOC.FourGeometricBudgetSpectralGaps
import MOC.FourCoincidence
import MOC.TwoExceptions
import Mathlib.Tactic.Lift

/-! The geometric-budget pattern chart in the coordinates of the original spectral gaps. -/

namespace MOC

set_option maxHeartbeats 2000000 in
/-- Regular spectral data with the six geometric-budget pattern contacts satisfy the real
projective gap equations, also when the remaining parameter is real. -/
theorem exists_fourGeometricBudget_spectral_gap_chart (a b : Fin 4 → ℂ) (η : ℂ) (H : ℝ)
    (ha : Function.Injective a) (hb : Function.Injective b) (hab : ∀ i j, a i + b j ≠ 0)
    (hη : η ≠ 0)
    (hc : ∀ i ∈ fourGeometricBudgetContactIndices, (η * matchingProduct a b (fourPerm i).symm).re = H) :
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
  have hcontact (i : Fin 24) (hi : i ∈ fourGeometricBudgetContactIndices) : (κ * F i).re = H :=
    (hproj i).symm.trans (hc i hi)
  have hκ : κ ≠ 0 := mul_ne_zero hη hk
  obtain ⟨hri, hdir, h, t, s, hhi, hti, hsi, hh₀, hh₁, ht₀, ht₁, hs₀, hs₁,
    hw, hG, hden, hz, hc'⟩ :=
    fourGeometricBudget_chart_real_parameters z w v r c κ H hκ hz₀ hz₁ hC hsep hcontact
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
  have hchart := fourGeometricBudget_projective_gap_identities h R s p z w v c κ
    hv₀ hv₁ hh₁' hvr hvz hrz hzc hG hP hz hw hcsol hdir
  refine ⟨h, R, s, p, v, ρ, by exact_mod_cast hh₀, hh₁', ?_, ?_,
    by exact_mod_cast hs₀, by exact_mod_cast hs₁, hp₀, hp₁, hv₀, hv₁, hG, hρ, ?_⟩
  · exact_mod_cast (hsep 2).1
  · exact_mod_cast (hsep 2).2.1
  · simpa only [hg, ρ, Z] using hchart

/-- At a geometric-budget pattern contact at index 12, the regular projective chart is real.
Both ordinary-minor defects vanish. Collisions have their own order-four bounds. -/
theorem fourGeometricBudget_support_of_contact_twelve (a b : Fin 4 → ℂ) (η : ℂ) (H : ℝ)
    (hn : ∀ i, H ≤ (η * matchingProduct a b (fourPerm i).symm).re)
    (hc : ∀ i ∈ fourGeometricBudgetContactIndices, (η * matchingProduct a b (fourPerm i).symm).re = H)
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
    exists_fourGeometricBudget_spectral_gap_chart a b η H ha hb hab hη hc
  let g : Fin 24 → ℝ := fun i => (η * matchingProduct a b (fourPerm i).symm).re - H
  have h12' : g 12 = 0 := sub_eq_zero.mpr h12
  have hρ : ρ = 0 := by
    rw [hg12] at h12'
    exact neg_eq_zero.mp ((mul_eq_zero.mp h12').resolve_right hs₀)
  simp only [hρ, zero_mul, neg_zero, add_zero] at hg3 hg7 hg10 hg19 hg22
  have hg9' : g 9 = 0 := by simpa only [hg7, hg3, mul_zero, add_zero] using hg9
  have hg18' : g 18 = 0 := by simpa only [hg7, hρ, zero_mul, add_zero] using hg18
  obtain ⟨_, _, _, hr19, _, _, hr22, _⟩ := fourGeometricBudget_gap_relations a b η H hc
  have hg13 : g 13 = 0 := by
    linarith only [hr19, hg19, hg3, hg7, h12', hg18']
  have hg16 : g 16 = 0 := by
    linarith only [hr22, hg22, hg3, hg7, h12', hg18']
  apply fourGeometricBudget_support_of_nonnegative_defects a b η H hn hc U hU
  change 0 ≤ fourGeometricBudgetDefectA g ∧ 0 ≤ fourGeometricBudgetDefectB g
  simp [fourGeometricBudgetDefectA, fourGeometricBudgetDefectB, hg3, hg7, hg10, hg9', h12', hg13, hg16, hg18']

end MOC

/-! Sign splits for the supported geometric-budget pattern projective gap profile. -/

namespace MOC

/-- The second set of projected gap equations follows by linear
reconstruction from the eight geometric-budget pattern source equations. -/
theorem fourGeometricBudget_gap_equations_of_chart (a b : Fin 4 → ℂ) (η : ℂ) (H : ℝ)
    (hc : ∀ i ∈ fourGeometricBudgetContactIndices, (η * matchingProduct a b (fourPerm i).symm).re = H)
    (h J K s E : ℝ) :
    let g : Fin 24 → ℝ := fun i => (η * matchingProduct a b (fourPerm i).symm).re - H
    g 9 = g 7 + s * g 3 → s * g 3 = E * K →
    g 18 = g 7 + E → g 19 = g 3 + E * (1 + J - K) →
    g 22 = g 3 + E * (1 + h * J - K) →
    g 11 = g 10 + s * g 3 ∧ g 15 = g 12 + E * J ∧ g 17 = g 12 + E * (h * J) ∧
    g 20 = g 10 + E ∧ g 21 = g 10 + E * (1 + J) ∧ g 23 = g 7 + E * (1 + h * J) ∧
    fourGeometricBudgetDefectA g = g 10 + E * (1 + h * J) ∧
    fourGeometricBudgetDefectB g = g 7 + E * (1 + J) := by
  intro g h9 hK h18 h19 h22
  obtain ⟨hr11, hr15, hr17, hr19, hr20, hr21, hr22, hr23⟩ := fourGeometricBudget_gap_relations a b η H hc
  unfold fourGeometricBudgetDefectA fourGeometricBudgetDefectB
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination hr11 + h9
  · linear_combination hr15 - hr19 + h9 + h19 - h18 + hK
  · linear_combination hr17 - hr22 + h9 + h22 - h18 + hK
  · linear_combination hr20 + h18
  · linear_combination hr21 - hr19 + h9 + h19 + hK
  · linear_combination hr23 - hr22 + h9 + h22 + hK
  · linear_combination -hr22 + h9 + h22 + hK
  · linear_combination -hr19 + h9 + h19 + hK

/-- Both defects are nonnegative when the sign of the chart cross product
allows comparison with the supported gaps at indices 21 and 23. -/
theorem fourGeometricBudget_minor_defects_of_chart_sign {J h E L M N O D x : ℝ}
    (hN : 0 < N) (hO : 0 < O) (hD : 0 < D)
    (hL : L ≠ 0) (hEL : E * L ≤ 0) (hx : 0 ≤ x * L)
    (hgeom : (M - L) * ((h - 1) * N * O) = J * D)
    (h21 : 0 ≤ x * M + E * (1 + J)) (h23 : 0 ≤ x * L + E * (1 + h * J)) :
    0 ≤ x * M + E * (1 + h * J) ∧ 0 ≤ x * L + E * (1 + J) := by
  let A := x * M + E * (1 + h * J)
  let B := x * L + E * (1 + J)
  let u := x * M + E * (1 + J)
  let v := x * L + E * (1 + h * J)
  let W := x * L * J ^ 2 * D / (N * O)
  have hW : 0 ≤ W := by
    dsimp only [W]
    exact div_nonneg (mul_nonneg (mul_nonneg hx (sq_nonneg _)) hD.le) (mul_pos hN hO).le
  change 0 ≤ A ∧ 0 ≤ B
  apply fourGeometricBudget_minor_defects_of_sign h21 h23 hL hEL hW
  · dsimp only [A, B, u, v]
    ring
  · dsimp only [A, B, u, v, W]
    field_simp [hN.ne', hO.ne']
    linear_combination -E * x * L ^ 2 * J * hgeom

/-- A positive cross product leaves three possible sign patterns. -/
theorem fourGeometricBudget_positive_cross_cases {ρ s p K L : ℝ}
    (hK : 0 < K) (hg3 : 0 < ρ * K * (p - 1))
    (hg7 : 0 < ρ * L * p * (s - 1)) (hg12 : 0 < -ρ * s)
    (hEL : 0 < (ρ * s * (p - 1)) * L) :
    (s < 0 ∧ 1 < p ∧ L < 0 ∧ 0 < ρ) ∨
    (0 < s ∧ s < 1 ∧ 0 < p ∧ p < 1 ∧ 0 < L ∧ ρ < 0) ∨
    (1 < s ∧ p < 0 ∧ 0 < L ∧ ρ < 0) := by
  have hρp : 0 < ρ * (p - 1) := by
    apply (mul_pos_iff_of_pos_right hK).mp
    convert hg3 using 1 <;> ring
  have hρs : ρ * s < 0 := by linarith only [hg12]
  rcases mul_pos_iff.mp hρp with ⟨hρ, hp⟩ | ⟨hρ, hp⟩
  · have hs : s < 0 := neg_of_mul_neg_right hρs hρ.le
    have hE : ρ * s * (p - 1) < 0 := mul_neg_of_neg_of_pos hρs hp
    have hL := ((mul_pos_iff.mp hEL).resolve_left (fun h => hE.not_gt h.1)).2
    exact Or.inl ⟨hs, sub_pos.mp hp, hL, hρ⟩
  · have hs : 0 < s := pos_of_mul_neg_right hρs hρ.le
    have hE : 0 < ρ * s * (p - 1) := mul_pos_of_neg_of_neg hρs hp
    have hL : 0 < L := (mul_pos_iff_of_pos_left hE).mp hEL
    have hpS : p * (s - 1) < 0 := by
      have hprod : 0 < (ρ * L) * (p * (s - 1)) := by simpa only [mul_assoc] using hg7
      exact ((mul_pos_iff.mp hprod).resolve_left
        (fun h => (mul_neg_of_neg_of_pos hρ hL).not_gt h.1)).2
    rcases mul_neg_iff.mp hpS with ⟨hp₀, hs₁⟩ | ⟨hp₀, hs₁⟩
    · exact Or.inr (Or.inl ⟨hs, sub_neg.mp hs₁, hp₀, sub_neg.mp hp, hL, hρ⟩)
    · exact Or.inr (Or.inr ⟨sub_pos.mp hs₁, hp₀, hL, hρ⟩)

/-- The third positive-cross chart already has positive ordinary defects. -/
theorem fourGeometricBudget_case_three_defects {ρ s p K J h g₇ g₁₀ : ℝ}
    (hρ : ρ < 0) (hs : 1 < s) (hp : p < 0) (hK : 0 < K)
    (hg₇ : 0 ≤ g₇) (hg₁₀ : 0 ≤ g₁₀)
    (h19 : 0 ≤ ρ * K * (p - 1) + ρ * s * (p - 1) * (1 + J - K))
    (h22 : 0 ≤ ρ * K * (p - 1) + ρ * s * (p - 1) * (1 + h * J - K)) :
    0 ≤ g₁₀ + ρ * s * (p - 1) * (1 + h * J) ∧
      0 ≤ g₇ + ρ * s * (p - 1) * (1 + J) := by
  have hp₁ : p - 1 < 0 := by linarith only [hp]
  have hg : 0 < ρ * K * (p - 1) := mul_pos_of_neg_of_neg (mul_neg_of_neg_of_pos hρ hK) hp₁
  have hbase : ρ * K * (p - 1) * (1 - s) < 0 :=
    mul_neg_of_pos_of_neg hg (sub_neg.mpr hs)
  constructor
  · have hsplit : ρ * K * (p - 1) + ρ * s * (p - 1) * (1 + h * J - K) =
        ρ * K * (p - 1) * (1 - s) + ρ * s * (p - 1) * (1 + h * J) := by ring
    rw [hsplit] at h22
    have hpos : 0 < ρ * s * (p - 1) * (1 + h * J) := by linarith only [hbase, h22]
    exact add_nonneg hg₁₀ hpos.le
  · have hsplit : ρ * K * (p - 1) + ρ * s * (p - 1) * (1 + J - K) =
        ρ * K * (p - 1) * (1 - s) + ρ * s * (p - 1) * (1 + J) := by ring
    rw [hsplit] at h19
    have hpos : 0 < ρ * s * (p - 1) * (1 + J) := by linarith only [hbase, h19]
    exact add_nonneg hg₇ hpos.le

end MOC

/-! The capacity bounds in the two nonminor geometric-budget pattern cases. -/

namespace MOC

/-- In the outer chart, the positive capacities give the ordinary minor
inequalities. -/
theorem fourGeometricBudget_outer_capacity {p q K α l : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hK : 0 < K) (hl : 0 < l)
    (hA : α ≤ 1 + p) (hQ : α ≤ K * (1 + q)) (hL : K ≤ l * α) :
    α ≤ l * ((1 + p) * (1 + q)) := by
  have hα : 0 < α := by
    have h := hK.trans_le hL
    rw [mul_comm] at h
    exact pos_of_mul_pos_left h hl.le
  have hq' : 0 ≤ 1 + q := by positivity
  have hkq := hQ.trans (mul_le_mul_of_nonneg_right hL hq')
  have hlq : 1 ≤ l * (1 + q) := by
    apply (mul_le_mul_right hα).mp
    calc
      1 * α = α := one_mul _
      _ ≤ l * α * (1 + q) := hkq
      _ = l * (1 + q) * α := by ring
  calc
    α ≤ 1 + p := hA
    _ = (1 + p) * 1 := (mul_one _).symm
    _ ≤ (1 + p) * (l * (1 + q)) := mul_le_mul_of_nonneg_left hlq (by positivity)
    _ = _ := by ring

/-- The inner chart of case I satisfies the single quadratic capacity
required by the geometric-budget pattern remainder. -/
theorem fourGeometricBudget_case_one_capacity_of_gaps {h J K p q l m : ℝ}
    (hh : h < 0) (hJ : 0 < J) (hK : 0 < K) (hp : 0 < p) (hq : 0 < q)
    (hl : 0 < l) (hlm : l ≤ m)
    (hpJ : J ≤ p) (hqJ : 1 + J - K ≤ K * q)
    (hmJ : 1 + J ≤ m * ((1 + p) * (1 + q)))
    (hI : m * (K - l * (1 + (2 - h) * J)) = l * (K - m * (1 + J))) :
    (1 + J) ^ 2 / (1 + (2 - h) * J) ≤ l * ((1 + p) * (1 + q)) := by
  let R := (1 + p) * (1 + q)
  let α := 1 + J
  let T := 1 + (2 - h) * J
  have hα : 0 ≤ α := by dsimp only [α]; positivity
  have hT : 0 < T := by
    have hh' : 0 < 2 - h := by linarith only [hh]
    dsimp only [T]
    positivity
  have hq' : α ≤ K * (1 + q) := by dsimp only [α]; linarith only [hqJ]
  have hp' : α ≤ 1 + p := by dsimp only [α]; linarith only [hpJ]
  have hbound : α ^ 2 ≤ K * R := by
    calc
      _ = α * α := pow_two _
      _ ≤ (1 + p) * (K * (1 + q)) :=
        mul_le_mul hp' hq' hα (by positivity)
      _ = K * R := by dsimp only [R]; ring
  exact fourGeometricBudget_geometric_budget hK hl hlm hα hT hbound hmJ hI

/-- The two positive gap constraints in case II furnish both inputs to
the geometric budget bound. -/
theorem fourGeometricBudget_case_two_capacity_of_gaps {P α K L M p q : ℝ}
    (hP : 0 < P) (hα : 0 < P + α) (hK : 0 < K) (hM : 0 < M)
    (hML : M ≤ L) (hq : 0 < q) (hp : P ≤ p) (hKP : q * P ≤ K)
    (hL : q * P ≤ L * p)
    (hI : L * (K - M * (2 * P + α)) = M * (K - L * P)) :
    P ^ 2 / (2 * P + α) ≤ (M * p) / q := by
  let R := p / q
  have hT : 0 < 2 * P + α := by linarith only [hP, hα]
  have hKR : P ^ 2 ≤ K * R := by
    dsimp only [R]
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hq).mpr
    calc
      P ^ 2 * q = (q * P) * P := by ring
      _ ≤ K * P := mul_le_mul_of_nonneg_right hKP hP.le
      _ ≤ K * p := mul_le_mul_of_nonneg_left hp hK.le
  have hLR : P ≤ L * R := by
    dsimp only [R]
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hq).mpr
    simpa only [mul_comm P q] using hL
  simpa only [R, mul_div_assoc] using
    fourGeometricBudget_geometric_budget hK hM hML hP.le hT hKR hLR hI

/-- The negative-`L` geometric-budget pattern chart has either two outer donor bounds or an
inner chart with negative `h` and `r` between zero and one. -/
theorem fourGeometricBudget_negative_L_region {h r N O D G : ℝ}
    (hr : r ≠ 1) (hN : 0 < N) (hO : 0 < O) (hD : 0 < D) (hG : 0 ≤ G) :
    let K := h * r * (r - 1) / D
    let L := r / ((h - 1) * N)
    0 < K → L < 0 →
    (r ^ 2 * (r - 1) * G / ((h - 1) * N * D) ≤ 0 ∧
      h * r * (r - 1) ^ 2 * G / ((h - 1) * O * D) ≤ 0) ∨
    (h < 0 ∧ 0 < r ∧ r < 1) := by
  intro K L hK hL
  have hKr : 0 < h * r * (r - 1) := (div_pos_iff_of_pos_right hD).mp hK
  rcases div_neg_iff.mp hL with ⟨hr₀, hd⟩ | ⟨hr₀, hd⟩
  · have hh₁ := sub_neg.mp (neg_of_mul_neg_left hd hN.le)
    rcases lt_or_gt_of_ne hr with hr₁ | hr₁
    · have hh₀ : h < 0 := by
        have hx := ((mul_pos_iff.mp hKr).resolve_left (fun h => (sub_neg.mpr hr₁).not_gt h.2)).1
        exact neg_of_mul_neg_left hx hr₀.le
      exact Or.inr ⟨hh₀, hr₀, hr₁⟩
    · have hx := ((mul_pos_iff.mp hKr).resolve_right (fun h => (sub_pos.mpr hr₁).not_lt h.2)).1
      apply Or.inl
      exact ⟨div_nonpos_of_nonneg_of_nonpos
        (mul_nonneg (mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hr₁.le)) hG)
        (mul_nonpos_of_nonpos_of_nonneg hd.le hD.le),
        div_nonpos_of_nonneg_of_nonpos (mul_nonneg (mul_nonneg hx.le (sq_nonneg _)) hG)
          (mul_nonpos_of_nonpos_of_nonneg
            (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hh₁.le) hO.le) hD.le)⟩
  · have hh₁ := sub_pos.mp ((mul_pos_iff_of_pos_right hN).mp hd)
    have hh₀ : 0 < h := zero_lt_one.trans hh₁
    have hr₁ : r - 1 ≤ 0 := by linarith only [hr₀]
    apply Or.inl
    exact ⟨div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hr₁) hG)
      (mul_nonneg hd.le hD.le),
      div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hh₀.le hr₀.le) (sq_nonneg _)) hG)
        (mul_nonneg (mul_nonneg (sub_nonneg.mpr hh₁.le) hO.le) hD.le)⟩

/-- A positive `L` chart has a positive `h`. Swapping the anchors
therefore makes either `h` or its reciprocal greater than one. -/
theorem fourGeometricBudget_positive_L_region {h r N D : ℝ} (hN : 0 < N) (hD : 0 < D)
    (hK : 0 < h * r * (r - 1) / D) (hL : 0 < r / ((h - 1) * N)) :
    1 < h ∨ (0 < h ∧ h < 1) := by
  have hKr := (div_pos_iff_of_pos_right hD).mp hK
  rcases div_pos_iff.mp hL with ⟨_, hd⟩ | ⟨hr, hd⟩
  · exact Or.inl (sub_pos.mp ((mul_pos_iff_of_pos_right hN).mp hd))
  · have hr₁ : r - 1 < 0 := by linarith only [hr]
    have hx := ((mul_pos_iff.mp hKr).resolve_left (fun h => hr₁.not_gt h.2)).1
    exact Or.inr ⟨pos_of_mul_neg_left hx hr.le, sub_neg.mp (neg_of_mul_neg_left hd hN.le)⟩

/-- Rescaling case I replaces the cross coefficient by minus one. -/
theorem fourGeometricBudget_case_one_rescaling (ρ s p K L M : ℝ) (hρ : 0 < ρ) (hs : s < 0) (hp : 1 < p) :
    let P := (p - 1)⁻¹
    let Q := (-s)⁻¹
    let z := P * Q / ρ
    let R := (1 + P) * (1 + Q)
    0 < P ∧ 0 < Q ∧ 0 < z ∧
    z * (ρ * K * (p - 1)) = K * Q ∧ z * (ρ * L * p * (s - 1)) = (-L) * R ∧
    z * (ρ * M * p * (s - 1)) = (-M) * R ∧ z * (-ρ * s) = P ∧
    z * (ρ * s * (p - 1)) = -1 := by
  intro P Q z R
  have hP : 0 < P := inv_pos.mpr (sub_pos.mpr hp)
  have hQ : 0 < Q := inv_pos.mpr (neg_pos.mpr hs)
  have hz : 0 < z := div_pos (mul_pos hP hQ) hρ
  have hp₀ : p - 1 ≠ 0 := sub_ne_zero.mpr hp.ne'
  have hs₀ : -s ≠ 0 := neg_ne_zero.mpr hs.ne
  refine ⟨hP, hQ, hz, ?_, ?_, ?_, ?_, ?_⟩ <;>
    dsimp only [P, Q, z, R] <;>
    field_simp [hp₀, hs₀, hs.ne, hρ.ne'] <;> ring

/-- Rescaling case II replaces the cross coefficient by a positive split
ratio and preserves the two donor scales. -/
theorem fourGeometricBudget_case_two_rescaling (ρ s p K L M : ℝ) (hρ : ρ < 0)
    (hs : 0 < s) (hs₁ : s < 1) (hp : 0 < p) (hp₁ : p < 1) :
    let P := p / (1 - p)
    let Q := s / (1 - s)
    let z := (1 + P) * (1 + Q) / (-ρ)
    0 < P ∧ 0 < Q ∧ 0 < z ∧
    z * (ρ * K * (p - 1)) = K * (1 + Q) ∧ z * (ρ * L * p * (s - 1)) = L * P ∧
    z * (ρ * M * p * (s - 1)) = M * P ∧ z * (-ρ * s) = Q * (1 + P) ∧
    z * (ρ * s * (p - 1)) = Q := by
  intro P Q z
  have hP : 0 < P := div_pos hp (sub_pos.mpr hp₁)
  have hQ : 0 < Q := div_pos hs (sub_pos.mpr hs₁)
  have hz : 0 < z := div_pos (mul_pos (by positivity) (by positivity)) (neg_pos.mpr hρ)
  have hp₀ : 1 - p ≠ 0 := sub_ne_zero.mpr hp₁.ne'
  have hs₀ : 1 - s ≠ 0 := sub_ne_zero.mpr hs₁.ne'
  refine ⟨hP, hQ, hz, ?_, ?_, ?_, ?_, ?_⟩ <;>
    dsimp only [P, Q, z] <;>
    field_simp [hp₀, hs₀, hρ.ne] <;> ring

/-- The anchors may be interchanged in the cross-product identity without
recomputing the projective chart. -/
theorem fourGeometricBudget_swap_geometry {h J K L M : ℝ} (hh : h ≠ 0)
    (hI : (M - L) * K = (h - 1) * J * L * M) :
    (L - M) * K = (h⁻¹ - 1) * (h * J) * M * L := by
  field_simp [hh]
  linear_combination -h * hI

/-- The sign of the cross product orders the two donors. -/
theorem fourGeometricBudget_donor_order {h J K L M : ℝ} (hK : 0 < K) (hLM : 0 ≤ L * M)
    (hcross : (h - 1) * J ≤ 0)
    (hI : (M - L) * K = (h - 1) * J * L * M) : M ≤ L := by
  have hnonpos : (M - L) * K ≤ 0 := by
    rw [hI, mul_assoc]
    exact mul_nonpos_of_nonpos_of_nonneg hcross hLM
  exact sub_nonpos.mp (nonpos_of_mul_nonpos_left hnonpos hK)

end MOC
