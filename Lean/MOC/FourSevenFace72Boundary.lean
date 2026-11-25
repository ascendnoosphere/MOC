import MOC.FourSevenFace72

/-! A second face-72 certificate using the two pair minors as donors. -/

open BigOperators Matrix

namespace MOC

noncomputable section

set_option maxHeartbeats 1000000 in
private theorem face72_quaternion_boundary_budget (p q : Fin 4 → ℝ)
    (hp : p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2 = 1)
    (hq : q 0 ^ 2 + q 1 ^ 2 + q 2 ^ 2 + q 3 ^ 2 = 1)
    (L k : ℝ) (hL : 0 < L) (hk : 0 ≤ k) (hk₁ : k ≤ 1) :
    let a := -p 0 * q 3 + p 1 * q 2 - p 2 * q 1 - p 3 * q 0
    let b := p 0 * q 3 + p 1 * q 2 - p 2 * q 1 + p 3 * q 0
    let D := p 0 ^ 2 + p 2 ^ 2 - (q 0 ^ 2 + q 2 ^ 2)
    let s := p 0 ^ 2 + p 2 ^ 2 + q 0 ^ 2 + q 2 ^ 2 - 1
    let t := q 2 ^ 2 + q 3 ^ 2 - (p 2 ^ 2 + p 3 ^ 2)
    let F := 1 - p 1 ^ 2 - p 2 ^ 2 - q 1 ^ 2 - q 2 ^ 2
    0 ≤ (1 + k) * (a ^ 2 + b ^ 2 + s ^ 2) - t ^ 2 + L * D ^ 2 +
      ((1 - k) / (1 + k) + 1 / L) * F ^ 2 := by
  intro a b D s t F
  let X := p 0 * q 3 + p 1 * q 2 + p 2 * q 1 - p 3 * q 0
  let Y := p 0 * q 3 - p 1 * q 2 - p 2 * q 1 - p 3 * q 0
  let J := p 0 ^ 2 + p 3 ^ 2 - (q 0 ^ 2 + q 3 ^ 2)
  let S := a ^ 2 + b ^ 2 + s ^ 2
  have ht : t + D * F = X * b - Y * a + J * s := by
    dsimp only [t, D, F, X, Y, a, b, J, s]
    linear_combination (1 - p 0 ^ 2 - p 2 ^ 2 - q 1 ^ 2 - 2 * q 2 ^ 2 - q 3 ^ 2) * hp +
      (p 1 ^ 2 + 2 * p 2 ^ 2 + p 3 ^ 2 + q 0 ^ 2 + q 2 ^ 2 - 1) * hq
  have hnorm : X ^ 2 + Y ^ 2 + J ^ 2 ≤ 1 + F ^ 2 := by
    have heq : 1 + F ^ 2 - (X ^ 2 + Y ^ 2 + J ^ 2) =
        2 * (p 0 * q 0 + p 3 * q 3) ^ 2 + 2 * (p 1 * q 1 - p 2 * q 2) ^ 2 := by
      dsimp only [F, X, Y, J]
      linear_combination (-p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 - p 3 ^ 2 - 1) * hp +
        (-q 0 ^ 2 + q 1 ^ 2 + q 2 ^ 2 - q 3 ^ 2 - 1) * hq
    apply sub_nonneg.mp
    rw [heq]
    positivity
  have hCS : (X * b - Y * a + J * s) ^ 2 ≤ (X ^ 2 + Y ^ 2 + J ^ 2) * S := by
    dsimp only [S]
    nlinarith only [sq_nonneg (X * a + Y * b), sq_nonneg (X * s - J * b),
      sq_nonneg (Y * s + J * a)]
  have hmain : (t + D * F) ^ 2 ≤ (1 + F ^ 2) * S := by
    rw [ht]
    exact hCS.trans (mul_le_mul_of_nonneg_right hnorm (by positivity))
  have h1k : 0 < 1 + k := by positivity
  have h1k' : 0 ≤ 1 - k := sub_nonneg.mpr hk₁
  change 0 ≤ (1 + k) * S - t ^ 2 + L * D ^ 2 + ((1 - k) / (1 + k) + 1 / L) * F ^ 2
  by_cases hbase : t ^ 2 ≤ (1 + k) * S
  · exact add_nonneg (add_nonneg (sub_nonneg.mpr hbase) (by positivity)) (by positivity)
  have ht₀ : -1 ≤ t := by
    dsimp only [t]
    nlinarith only [hp, sq_nonneg (p 0), sq_nonneg (p 1), sq_nonneg (q 2), sq_nonneg (q 3)]
  have ht₁ : t ≤ 1 := by
    dsimp only [t]
    nlinarith only [hq, sq_nonneg (q 0), sq_nonneg (q 1), sq_nonneg (p 2), sq_nonneg (p 3)]
  have htadd : 0 ≤ 1 + t := by linarith only [ht₀]
  have htSq : t ^ 2 ≤ 1 := by
    nlinarith only [mul_nonneg htadd (sub_nonneg.mpr ht₁)]
  have hF₀ : -1 ≤ F := by
    dsimp only [F]
    nlinarith only [hp, hq, sq_nonneg (p 0), sq_nonneg (p 3), sq_nonneg (q 0), sq_nonneg (q 3)]
  have hF₁ : F ≤ 1 := by
    dsimp only [F]
    nlinarith only [sq_nonneg (p 1), sq_nonneg (p 2), sq_nonneg (q 1), sq_nonneg (q 2)]
  have hFadd : 0 ≤ 1 + F := by linarith only [hF₀]
  have hFSq : F ^ 2 ≤ 1 := by
    nlinarith only [mul_nonneg hFadd (sub_nonneg.mpr hF₁)]
  have hS : S ≤ 1 / (1 + k) :=
    (le_div_iff₀ h1k).mpr (by
      rw [mul_comm]
      exact (le_of_lt (lt_of_not_ge hbase)).trans htSq)
  have hshift : F ^ 2 - k ≤ (1 - k) * F ^ 2 := by
    nlinarith only [mul_nonneg hk (sub_nonneg.mpr hFSq)]
  have hFS : (1 + F ^ 2) * S ≤ (1 + k) * S + (1 - k) / (1 + k) * F ^ 2 := by
    have h₀ := mul_le_mul_of_nonneg_right hshift (by positivity : 0 ≤ S)
    have h₁ := mul_le_mul_of_nonneg_left hS (mul_nonneg h1k' (sq_nonneg F))
    calc
      _ = (1 + k) * S + (F ^ 2 - k) * S := by ring
      _ ≤ (1 + k) * S + ((1 - k) * F ^ 2) * S := add_le_add_left h₀ _
      _ ≤ (1 + k) * S + ((1 - k) * F ^ 2) * (1 / (1 + k)) := add_le_add_left h₁ _
      _ = _ := by simp only [div_eq_mul_inv, one_mul]; ring
  have hYoung : -(2 * D * F * t) ≤ L * D ^ 2 + F ^ 2 / L := by
    have heq : L * (D + F * t / L) ^ 2 =
        L * D ^ 2 + 2 * D * F * t + (F ^ 2 / L) * t ^ 2 := by
      field_simp [hL.ne'] <;> ring
    have hsquare := mul_nonneg hL.le (sq_nonneg (D + F * t / L))
    rw [heq] at hsquare
    have htF : (F ^ 2 / L) * t ^ 2 ≤ F ^ 2 / L := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left htSq (div_nonneg (sq_nonneg F) hL.le)
    calc
      _ ≤ L * D ^ 2 + (F ^ 2 / L) * t ^ 2 := by
        apply sub_nonneg.mp
        convert hsquare using 1 <;> ring
      _ ≤ _ := add_le_add_left htF _
  have htotal : t ^ 2 ≤ (1 + k) * S + L * D ^ 2 + ((1 - k) / (1 + k) + 1 / L) * F ^ 2 := by
    calc
      _ = (t + D * F) ^ 2 + (-(2 * D * F * t)) - (D * F) ^ 2 := by ring
      _ ≤ ((1 + k) * S + (1 - k) / (1 + k) * F ^ 2) + (L * D ^ 2 + F ^ 2 / L) :=
        (sub_le_self _ (sq_nonneg _)).trans (add_le_add (hmain.trans hFS) hYoung)
      _ = _ := by simp only [div_eq_mul_inv, one_mul]; ring
  convert sub_nonneg.mpr htotal using 1 <;> ring

private theorem face72_vector_zero {α : Type*} (a b c d : α) : ![a, b, c, d] 0 = a := rfl
private theorem face72_vector_one {α : Type*} (a b c d : α) : ![a, b, c, d] 1 = b := rfl
private theorem face72_vector_two {α : Type*} (a b c d : α) : ![a, b, c, d] 2 = c := rfl
private theorem face72_vector_three {α : Type*} (a b c d : α) : ![a, b, c, d] 3 = d := rfl

set_option maxHeartbeats 1500000 in
private theorem face72_boundary_budget_on_rotation (p q : Fin 4 → ℝ)
    (hp : p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2 = 1)
    (hq : q 0 ^ 2 + q 1 ^ 2 + q 2 ^ 2 + q 3 ^ 2 = 1)
    (L k : ℝ) (hL : 0 < L) (hk : 0 ≤ k) (hk₁ : k ≤ 1) :
    let O := quaternionRotation p q
    0 ≤ (1 + k) * (O 0 3 ^ 2 + O 3 0 ^ 2 + (O 0 0 * O 2 2 - O 0 2 * O 2 0) ^ 2) -
      (O 0 2 * O 1 3 - O 0 3 * O 1 2) ^ 2 +
      L * (O 0 1 * O 2 3 - O 0 3 * O 2 1) ^ 2 +
      ((1 - k) / (1 + k) + 1 / L) * (O 1 1 * O 2 2 - O 1 2 * O 2 1) ^ 2 := by
  let O := quaternionRotation p q
  change 0 ≤ (1 + k) * (O 0 3 ^ 2 + O 3 0 ^ 2 + (O 0 0 * O 2 2 - O 0 2 * O 2 0) ^ 2) -
      (O 0 2 * O 1 3 - O 0 3 * O 1 2) ^ 2 +
      L * (O 0 1 * O 2 3 - O 0 3 * O 2 1) ^ 2 +
      ((1 - k) / (1 + k) + 1 / L) * (O 1 1 * O 2 2 - O 1 2 * O 2 1) ^ 2
  have ha : O 0 3 = -p 0 * q 3 + p 1 * q 2 - p 2 * q 1 - p 3 * q 0 := by
    simp only [O, quaternionRotation, Matrix.mul_apply, Fin.sum_univ_four, Matrix.of_apply,
      face72_vector_zero, face72_vector_one, face72_vector_two, face72_vector_three]
    ring
  have hb : O 3 0 = p 0 * q 3 + p 1 * q 2 - p 2 * q 1 + p 3 * q 0 := by
    simp only [O, quaternionRotation, Matrix.mul_apply, Fin.sum_univ_four, Matrix.of_apply,
      face72_vector_zero, face72_vector_one, face72_vector_two, face72_vector_three]
    ring
  have hs : O 0 0 * O 2 2 - O 0 2 * O 2 0 =
      p 0 ^ 2 + p 2 ^ 2 + q 0 ^ 2 + q 2 ^ 2 - 1 := by
    simp only [O, quaternionRotation, Matrix.mul_apply, Fin.sum_univ_four, Matrix.of_apply,
      face72_vector_zero, face72_vector_one, face72_vector_two, face72_vector_three]
    linear_combination (q 0 ^ 2 + q 2 ^ 2 - 1) * hp - (p 1 ^ 2 + p 3 ^ 2) * hq
  have ht : O 0 2 * O 1 3 - O 0 3 * O 1 2 =
      q 2 ^ 2 + q 3 ^ 2 - (p 2 ^ 2 + p 3 ^ 2) := by
    simp only [O, quaternionRotation, Matrix.mul_apply, Fin.sum_univ_four, Matrix.of_apply,
      face72_vector_zero, face72_vector_one, face72_vector_two, face72_vector_three]
    linear_combination (q 2 ^ 2 + q 3 ^ 2) * hp - (p 2 ^ 2 + p 3 ^ 2) * hq
  have hD : O 0 1 * O 2 3 - O 0 3 * O 2 1 =
      -(p 0 ^ 2 + p 2 ^ 2 - (q 0 ^ 2 + q 2 ^ 2)) := by
    simp only [O, quaternionRotation, Matrix.mul_apply, Fin.sum_univ_four, Matrix.of_apply,
      face72_vector_zero, face72_vector_one, face72_vector_two, face72_vector_three]
    linear_combination (q 0 ^ 2 + q 2 ^ 2) * hp - (p 0 ^ 2 + p 2 ^ 2) * hq
  have hF : O 1 1 * O 2 2 - O 1 2 * O 2 1 =
      1 - p 1 ^ 2 - p 2 ^ 2 - q 1 ^ 2 - q 2 ^ 2 := by
    simp only [O, quaternionRotation, Matrix.mul_apply, Fin.sum_univ_four, Matrix.of_apply,
      face72_vector_zero, face72_vector_one, face72_vector_two, face72_vector_three]
    linear_combination (q 0 ^ 2 + q 3 ^ 2) * hp + (1 - p 1 ^ 2 - p 2 ^ 2) * hq
  rw [hs, ht, hD, hF, ha, hb, neg_sq]
  exact face72_quaternion_boundary_budget p q hp hq L k hL hk hk₁

private theorem face72_boundary_budget_canonical (L k : ℝ) (hL : 0 < L) (hk : 0 ≤ k) (hk₁ : k ≤ 1)
    (V : Matrix (Fin 4) (Fin 4) ℂ) (hV : IsUnitary V) :
    let m := subsetMinorSq V
    0 ≤ (1 + k) * (m {0} {3} + m {3} {0} + m {0, 2} {0, 2}) - m {0, 1} {2, 3} +
      L * m {0, 2} {1, 3} + ((1 - k) / (1 + k) + 1 / L) * m {1, 2} {1, 2} := by
  obtain ⟨κ, inst, w, O, hw, _, hm⟩ := four_minor_mixture V hV
  letI : Fintype κ := inst
  let m (k : κ) := subsetMinorSq (Complex.ofRealHom.mapMatrix (O k).val)
  dsimp only
  simp_rw [hm]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_nonneg
  intro j _
  have h : 0 ≤ (1 + k) * (m j {0} {3} + m j {3} {0} + m j {0, 2} {0, 2}) - m j {0, 1} {2, 3} +
      L * m j {0, 2} {1, 3} + ((1 - k) / (1 + k) + 1 / L) * m j {1, 2} {1, 2} := by
    obtain ⟨p, q, hp, hq, hsingle, hpair⟩ := exists_quaternionRotation_same_squaredMinors (O j)
    dsimp only [m]
    rw [hsingle 0 3, hsingle 3 0,
      hpair 0 2 0 2 (by decide) (by decide), hpair 0 1 2 3 (by decide) (by decide),
      hpair 0 2 1 3 (by decide) (by decide), hpair 1 2 1 2 (by decide) (by decide)]
    exact face72_boundary_budget_on_rotation p q (by simpa only [Fin.sum_univ_four] using hp)
      (by simpa only [Fin.sum_univ_four] using hq) L k hL hk hk₁
  have h' := mul_nonneg (hw j) h
  dsimp only [m] at h'
  nlinarith only [h']

/-- Increasing the three positive coefficients of the mixed ray reduces
the required coefficient of the second pair minor. -/
theorem fourSevenFace72_weighted_budget_nonneg (L k : ℝ) (hL : 0 < L) (hk : 0 ≤ k) (hk₁ : k ≤ 1)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    let m := subsetMinorSq U
    0 ≤ (1 + k) * (m {1} {1} + m {2} {2} + m {0, 1} {2, 3}) - m {0, 2} {0, 2} +
      L * m {0, 1} {0, 1} + ((1 - k) / (1 + k) + 1 / L) * m {0, 3} {0, 3} := by
  let r := fourPerm 10
  let s := fourPerm 13
  let V := U.submatrix r s
  have hV : IsUnitary V := unitary_reindex r s hU
  have hsingle (i j : Fin 4) :
      subsetMinorSq V {i} {j} = subsetMinorSq U {r i} {s j} := by
    rw [subsetMinorSq_singleton V hV, subsetMinorSq_singleton U hU] <;> rfl
  have hpair {i k j l : Fin 4} (hi : i ≠ k) (hj : j ≠ l) :
      subsetMinorSq V {i, k} {j, l} = subsetMinorSq U {r i, r k} {s j, s l} := by
    rw [subsetMinorSq_pair V hV hi hj, subsetMinorSq_pair U hU
      (fun h => hi (r.injective h)) (fun h => hj (s.injective h))] <;> rfl
  have hm₁ : subsetMinorSq V {0} {3} = subsetMinorSq U {1} {1} := by
    rw [hsingle, show r 0 = 1 by decide +kernel, show s 3 = 1 by decide +kernel]
  have hm₂ : subsetMinorSq V {3} {0} = subsetMinorSq U {2} {2} := by
    rw [hsingle, show r 3 = 2 by decide +kernel, show s 0 = 2 by decide +kernel]
  have hm₃ : subsetMinorSq V {0, 2} {1, 3} = subsetMinorSq U {0, 1} {0, 1} := by
    rw [hpair (i := 0) (k := 2) (j := 1) (l := 3) (by decide) (by decide),
      show ({r 0, r 2} : Finset (Fin 4)) = {0, 1} by decide +kernel,
      show ({s 1, s 3} : Finset (Fin 4)) = {0, 1} by decide +kernel]
  have hm₄ : subsetMinorSq V {0, 2} {0, 2} = subsetMinorSq U {0, 1} {2, 3} := by
    rw [hpair (i := 0) (k := 2) (j := 0) (l := 2) (by decide) (by decide),
      show ({r 0, r 2} : Finset (Fin 4)) = {0, 1} by decide +kernel,
      show ({s 0, s 2} : Finset (Fin 4)) = {2, 3} by decide +kernel]
  have hm₅ : subsetMinorSq V {0, 1} {2, 3} = subsetMinorSq U {0, 2} {0, 2} := by
    rw [hpair (i := 0) (k := 1) (j := 2) (l := 3) (by decide) (by decide),
      ← subsetMinorSq_compl U hU {0, 2} {0, 2},
      show ({r 0, r 1} : Finset (Fin 4)) = ({0, 2} : Finset (Fin 4))ᶜ by decide +kernel,
      show ({s 2, s 3} : Finset (Fin 4)) = ({0, 2} : Finset (Fin 4))ᶜ by decide +kernel]
  have hm₆ : subsetMinorSq V {1, 2} {1, 2} = subsetMinorSq U {0, 3} {0, 3} := by
    rw [hpair (i := 1) (k := 2) (j := 1) (l := 2) (by decide) (by decide),
      show ({r 1, r 2} : Finset (Fin 4)) = {0, 3} by decide +kernel,
      show ({s 1, s 2} : Finset (Fin 4)) = {0, 3} by decide +kernel]
  have h := face72_boundary_budget_canonical L k hL hk hk₁ V hV
  dsimp only at h ⊢
  rwa [hm₁, hm₂, hm₃, hm₄, hm₅, hm₆] at h

/-- The mixed face-72 ray can be paid for with the two pair minors alone. -/
theorem fourSevenFace72_boundary_budget_nonneg (L : ℝ) (hL : 0 < L)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    let m := subsetMinorSq U
    0 ≤ m {1} {1} + m {2} {2} + m {0, 1} {2, 3} - m {0, 2} {0, 2} +
      L * m {0, 1} {0, 1} + (1 + 1 / L) * m {0, 3} {0, 3} := by
  simpa only [add_zero, sub_zero, div_one, one_mul] using
    fourSevenFace72_weighted_budget_nonneg L 0 hL le_rfl zero_le_one U hU

set_option maxHeartbeats 1500000 in
/-- If the three positive terms of the mixed ray each have at least
`k * β` in additional weight, the last donor only needs to cover
`β * (1 - k) / (1 + k)` and the Young inequality contribution. -/
theorem fourSevenFace72_support_of_weighted_budget (a b : Fin 4 → ℂ) (η : ℂ) (H : ℝ)
    (hn : ∀ i, H ≤ (η * matchingProduct a b (fourPerm i).symm).re)
    (hc : ∀ i ∈ fourSevenFace72ContactIndices, (η * matchingProduct a b (fourPerm i).symm).re = H)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U)
    (k : ℝ) (hk : 0 ≤ k) (hk₁ : k ≤ 1)
    (hcap :
      let g (i : Fin 24) := (η * matchingProduct a b (fourPerm i).symm).re - H
      let d := fourSevenFace72Mixed g
      0 < d → d * k ≤ g 14 ∧ d * k ≤ g 5 ∧ d * k ≤ g 16 ∧ 0 < g 7 ∧
        d ^ 2 ≤ g 7 * (g 2 - d * ((1 - k) / (1 + k)))) :
    H ≤ (η * determinantValue a b U).re := by
  let g (i : Fin 24) := (η * matchingProduct a b (fourPerm i).symm).re - H
  let d := fourSevenFace72Mixed g
  have hg (i : Fin 24) : 0 ≤ g i := sub_nonneg.mpr (hn i)
  by_cases hd : 0 < d
  · obtain ⟨hB, hC, hE, hD, hprod⟩ := hcap hd
    let c := (1 - k) / (1 + k)
    change d * k ≤ g 14 at hB
    change d * k ≤ g 5 at hC
    change d * k ≤ g 16 at hE
    change 0 < g 7 at hD
    change d ^ 2 ≤ g 7 * (g 2 - d * c) at hprod
    let L := g 7 / d
    have hL : 0 < L := div_pos hD hd
    have hDL : d * L = g 7 := by
      dsimp only [L]
      field_simp [hd.ne'] <;> ring
    have hFL : d * (c + 1 / L) ≤ g 2 := by
      have heq : d * (c + 1 / L) = d * c + d ^ 2 / g 7 := by
        dsimp only [L]
        field_simp [hd.ne', hD.ne'] <;> ring
      rw [heq]
      have h : d ^ 2 / g 7 ≤ g 2 - d * c :=
        (div_le_iff₀ hD).mpr (by simpa only [mul_comm] using hprod)
      linarith only [h]
    let m := subsetMinorSq U
    have hm (I J : Finset (Fin 4)) : 0 ≤ m I J := subsetMinorSq_nonneg U I J
    have h := fourSevenFace72_weighted_budget_nonneg L k hL hk hk₁ U hU
    dsimp only at h
    have hbudget : 0 ≤ d * ((1 + k) * (m {1} {1} + m {2} {2} + m {0, 1} {2, 3}) -
        m {0, 2} {0, 2}) + g 7 * m {0, 1} {0, 1} + (d * (c + 1 / L)) * m {0, 3} {0, 3} := by
      rw [← hDL]
      convert mul_nonneg hd.le h using 1 <;> dsimp only [m, c] <;> ring
    have hrest := mul_le_mul_of_nonneg_right hFL (hm {0, 3} {0, 3})
    have h₀ := mul_nonneg (hg 18) (hm {0} {3})
    have h₁ := mul_nonneg (sub_nonneg.mpr hB) (hm {1} {1})
    have h₂ := mul_nonneg (sub_nonneg.mpr hC) (hm {2} {2})
    have h₄ := mul_nonneg (sub_nonneg.mpr hE) (hm {0, 1} {2, 3})
    obtain ⟨h15, h11, h17⟩ := fourSevenFace72_donor_gaps a b η H hc
    change g 15 = g 14 + d at h15
    change g 11 = g 5 + d at h11
    change g 17 = g 16 + d at h17
    apply sub_nonneg.mp
    rw [fourSevenFace72_gap_eq_minors a b η H hc U hU]
    change 0 ≤ g 18 * m {0} {3} + g 15 * m {1} {1} + g 11 * m {2} {2} +
      g 7 * m {0, 1} {0, 1} + g 17 * m {0, 1} {2, 3} + (-d) * m {0, 2} {0, 2} +
      g 2 * m {0, 3} {0, 3}
    rw [h15, h11, h17]
    calc
      0 ≤ d * ((1 + k) * (m {1} {1} + m {2} {2} + m {0, 1} {2, 3}) - m {0, 2} {0, 2}) +
          g 7 * m {0, 1} {0, 1} + (d * (c + 1 / L)) * m {0, 3} {0, 3} +
          g 18 * m {0} {3} + (g 14 - d * k) * m {1} {1} + (g 5 - d * k) * m {2} {2} +
          (g 16 - d * k) * m {0, 1} {2, 3} +
          (g 2 * m {0, 3} {0, 3} - (d * (c + 1 / L)) * m {0, 3} {0, 3}) :=
        add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg hbudget h₀) h₁) h₂) h₄)
          (sub_nonneg.mpr hrest)
      _ = _ := by ring
  · apply fourSevenFace72_support_of_budget a b η H hn hc U hU
    dsimp only
    exact fun hh => (hd hh).elim

/-- The two pair-minor budget bounds the face-72 determinant whenever
`g 7 * (g 2 - β) ≥ β²` and `g 2 > β` on the positive mixed branch. -/
theorem fourSevenFace72_support_of_pair_budget (a b : Fin 4 → ℂ) (η : ℂ) (H : ℝ)
    (hn : ∀ i, H ≤ (η * matchingProduct a b (fourPerm i).symm).re)
    (hc : ∀ i ∈ fourSevenFace72ContactIndices, (η * matchingProduct a b (fourPerm i).symm).re = H)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U)
    (hcap :
      let g (i : Fin 24) := (η * matchingProduct a b (fourPerm i).symm).re - H
      let d := fourSevenFace72Mixed g
      0 < d → d < g 2 ∧ d ^ 2 ≤ g 7 * (g 2 - d)) :
    H ≤ (η * determinantValue a b U).re := by
  apply fourSevenFace72_support_of_weighted_budget a b η H hn hc U hU 0 le_rfl zero_le_one
  let g (i : Fin 24) := (η * matchingProduct a b (fourPerm i).symm).re - H
  let d := fourSevenFace72Mixed g
  have hg (i : Fin 24) : 0 ≤ g i := sub_nonneg.mpr (hn i)
  change 0 < d → d * 0 ≤ g 14 ∧ d * 0 ≤ g 5 ∧ d * 0 ≤ g 16 ∧ 0 < g 7 ∧
    d ^ 2 ≤ g 7 * (g 2 - d * ((1 - 0) / (1 + 0)))
  simp only [mul_zero, sub_zero, add_zero, div_one, mul_one]
  intro hd
  obtain ⟨hF, hprod⟩ := hcap hd
  change d < g 2 at hF
  change d ^ 2 ≤ g 7 * (g 2 - d) at hprod
  have hD : 0 < g 7 :=
    pos_of_mul_pos_left ((pow_pos hd 2).trans_le hprod) (sub_nonneg.mpr hF.le)
  exact ⟨hg 14, hg 5, hg 16, hD, hprod⟩

private theorem face72_cubic_lower_bound (A B C D E d H : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hd : 0 ≤ d) :
    (E + d + H) * d ^ 2 ≤
      (A + E + d) * (B + d) * (C + d) + D * d * (A + d) + H * d ^ 2 := by
  have hBC : d ^ 2 ≤ (B + d) * (C + d) := by
    simpa only [pow_two] using mul_le_mul
      (le_add_of_nonneg_left hB) (le_add_of_nonneg_left hC) hd (add_nonneg hB hd)
  have hE' : E + d ≤ A + E + d := by linarith only [hA]
  have hfirst := mul_le_mul hE' hBC (sq_nonneg d) (by positivity : 0 ≤ A + E + d)
  have hterm : 0 ≤ D * d * (A + d) := by positivity
  nlinarith only [hfirst, hterm]

/-- With positive opposite-corner gap sum, the cubic coefficient and the
thirteenth quadratic derivative of the real lift have the same strict sign. -/
theorem fourSevenFace72_cubic_coefficient_mul_gradient_pos (a b : Fin 4 → ℂ) (η : ℂ) (H : ℝ)
    (hn : ∀ i, H ≤ (η * matchingProduct a b (fourPerm i).symm).re)
    (hc : ∀ i ∈ fourSevenFace72ContactIndices, (η * matchingProduct a b (fourPerm i).symm).re = H) :
    let g (i : Fin 24) := (η * matchingProduct a b (fourPerm i).symm).re - H
    let d := fourSevenFace72Mixed g
    0 < d → 0 < g 7 + g 16 →
      0 < (g 7 * g 16 + H * (g 7 + g 16)) * ((g 7 + g 16) * (g 2 - d) - d ^ 2) := by
  intro g d hd hsum
  have hg (i : Fin 24) : 0 ≤ g i := sub_nonneg.mpr (hn i)
  have hbound := face72_cubic_lower_bound (g 18) (g 14) (g 5) (g 7) (g 16) d H
    (hg 18) (hg 14) (hg 5) (hg 7) (hg 16) hd.le
  have heq : (g 7 * g 16 + H * (g 7 + g 16)) * (g 2 - d) =
      (g 18 + g 16 + d) * (g 14 + d) * (g 5 + d) + g 7 * d * (g 18 + d) + H * d ^ 2 :=
    fourSevenFace72_cubic a b η H hc
  rw [← heq] at hbound
  have h := mul_le_mul_of_nonneg_left hbound hsum.le
  have hpos : 0 < ((g 16) ^ 2 + (g 7 + g 16) * d) * d ^ 2 :=
    mul_pos (add_pos_of_nonneg_of_pos (sq_nonneg _) (mul_pos hsum hd)) (pow_pos hd 2)
  nlinarith only [h, hpos]

/-- The cubic coefficient is nonzero under the strict mixed and corner gaps. -/
theorem fourSevenFace72_cubic_coefficient_ne_zero (a b : Fin 4 → ℂ) (η : ℂ) (H : ℝ)
    (hn : ∀ i, H ≤ (η * matchingProduct a b (fourPerm i).symm).re)
    (hc : ∀ i ∈ fourSevenFace72ContactIndices, (η * matchingProduct a b (fourPerm i).symm).re = H) :
    let g (i : Fin 24) := (η * matchingProduct a b (fourPerm i).symm).re - H
    0 < fourSevenFace72Mixed g → 0 < g 7 + g 16 →
      g 7 * g 16 + H * (g 7 + g 16) ≠ 0 := by
  intro g hd hsum hzero
  have h := fourSevenFace72_cubic_coefficient_mul_gradient_pos a b η H hn hc hd hsum
  change 0 < (g 7 * g 16 + H * (g 7 + g 16)) * _ at h
  rw [hzero, zero_mul] at h
  exact (lt_irrefl 0) h

/-- The positive cubic coefficient at nonpositive height provides both
donors for the weighted pair-minor certificate. -/
theorem fourSevenFace72_support_of_nonpos_height_cubic (a b : Fin 4 → ℂ) (η : ℂ) (H : ℝ)
    (hH : H ≤ 0)
    (hn : ∀ i, H ≤ (η * matchingProduct a b (fourPerm i).symm).re)
    (hc : ∀ i ∈ fourSevenFace72ContactIndices, (η * matchingProduct a b (fourPerm i).symm).re = H)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U)
    (hcoeff :
      let g (i : Fin 24) := (η * matchingProduct a b (fourPerm i).symm).re - H
      0 < fourSevenFace72Mixed g → 0 < g 7 * g 16 + H * (g 7 + g 16)) :
    H ≤ (η * determinantValue a b U).re := by
  apply fourSevenFace72_support_of_pair_budget a b η H hn hc U hU
  let g (i : Fin 24) := (η * matchingProduct a b (fourPerm i).symm).re - H
  let d := fourSevenFace72Mixed g
  change 0 < d → d < g 2 ∧ d ^ 2 ≤ g 7 * (g 2 - d)
  intro hd
  have hg (i : Fin 24) : 0 ≤ g i := sub_nonneg.mpr (hn i)
  let N := g 7 * g 16 + H * (g 7 + g 16)
  have hN : 0 < N := hcoeff hd
  have heq : N * (g 2 - d) =
      (g 18 + g 16 + d) * (g 14 + d) * (g 5 + d) + g 7 * d * (g 18 + d) + H * d ^ 2 :=
    fourSevenFace72_cubic a b η H hc
  have hA := hg 18
  have hB := hg 14
  have hC := hg 5
  have hD := hg 7
  have hE := hg 16
  have hHE : 0 ≤ (-H) * g 16 := mul_nonneg (neg_nonneg.mpr hH) hE
  have hEp : 0 < g 16 + H := by
    apply pos_of_mul_pos_right _ hD
    dsimp only [N] at hN
    nlinarith only [hN, hHE]
  have hbound := face72_cubic_lower_bound (g 18) (g 14) (g 5) (g 7) (g 16) d H
    hA hB hC hD hE hd.le
  have hmain : (g 16 + H) * d ^ 2 ≤ N * (g 2 - d) := by
    nlinarith only [heq, hbound, mul_nonneg hd.le (sq_nonneg d)]
  have hF : 0 < g 2 - d :=
    pos_of_mul_pos_right ((mul_pos hEp (pow_pos hd 2)).trans_le hmain) hN.le
  refine ⟨sub_pos.mp hF, (mul_le_mul_left hEp).mp ?_⟩
  have hrest := mul_nonneg hHE hF.le
  dsimp only [N] at hmain
  nlinarith only [hmain, hrest]

/-- Zero-height face 72 satisfies the determinant support inequality. -/
theorem fourSevenFace72_support_zero_height (a b : Fin 4 → ℂ) (η : ℂ)
    (hn : ∀ i, 0 ≤ (η * matchingProduct a b (fourPerm i).symm).re)
    (hc : ∀ i ∈ fourSevenFace72ContactIndices, (η * matchingProduct a b (fourPerm i).symm).re = 0)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    0 ≤ (η * determinantValue a b U).re := by
  apply fourSevenFace72_support_of_nonpos_height_cubic a b η 0 le_rfl hn hc U hU
  let g (i : Fin 24) := (η * matchingProduct a b (fourPerm i).symm).re - 0
  let d := fourSevenFace72Mixed g
  change 0 < d → 0 < g 7 * g 16 + 0 * (g 7 + g 16)
  intro hd
  rw [zero_mul, add_zero]
  have hg (i : Fin 24) : 0 ≤ g i := sub_nonneg.mpr (hn i)
  have hA := hg 18
  have hB := hg 14
  have hC := hg 5
  have hD := hg 7
  have hE := hg 16
  have heq : (g 7 * g 16 + 0 * (g 7 + g 16)) * (g 2 - d) =
      (g 18 + g 16 + d) * (g 14 + d) * (g 5 + d) + g 7 * d * (g 18 + d) + 0 * d ^ 2 :=
    fourSevenFace72_cubic a b η 0 hc
  simp only [zero_mul, add_zero] at heq
  have hpos : 0 < g 7 * g 16 * (g 2 - d) := by rw [heq]; positivity
  have hF := pos_of_mul_pos_right hpos (mul_nonneg hD hE)
  exact pos_of_mul_pos_left hpos hF.le

end

end MOC
