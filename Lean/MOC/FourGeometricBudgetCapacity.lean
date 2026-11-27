import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! The rational two-budget capacities in the two nonminor geometric-budget pattern charts. -/

namespace MOC

private theorem geometricBudget_chart_geometry_algebra
    (h r x y A N O D G : ℝ) (hh : h - 1 ≠ 0)
    (hNnz : N ≠ 0) (hOnz : O ≠ 0) (hDnz : D ≠ 0)
    (hA : A = h * r - h - r) (hN : N = x ^ 2 + y ^ 2)
    (hO : O = (x - 1) ^ 2 + y ^ 2)
    (hD : D = (A * x + r) ^ 2 + (A * y) ^ 2)
    (hG : G = (1 + (h - 1) * x) ^ 2 + ((h - 1) * y) ^ 2) :
    let K := h * r * (r - 1) / D
    let J := (A * N + r * (2 * x - 1)) / D
    let L := r / ((h - 1) * N)
    let M := h * (r - 1) / ((h - 1) * O)
    K + A * J = 1 ∧ (M - L) * ((h - 1) * N * O) = J * D ∧
    K * D = (h - 1) ^ 2 * N * O * (L * M) ∧
    (M - L) * K = (h - 1) * J * L * M ∧
    K + L * (1 + J) = r ^ 2 * (r - 1) * G / ((h - 1) * N * D) ∧
    K + M * (1 + h * J) = h * r * (r - 1) ^ 2 * G / ((h - 1) * O * D) := by
  intro K J L M
  have hLN : (h - 1) * N ≠ 0 := mul_ne_zero hh hNnz
  have hMO : (h - 1) * O ≠ 0 := mul_ne_zero hh hOnz
  have hK : K * D = h * r * (r - 1) := div_mul_cancel₀ _ hDnz
  have hJ : J * D = A * N + r * (2 * x - 1) := div_mul_cancel₀ _ hDnz
  have hL : L * ((h - 1) * N) = r := div_mul_cancel₀ _ hLN
  have hM : M * ((h - 1) * O) = h * (r - 1) := div_mul_cancel₀ _ hMO
  have hDpoly : D = h * r * (r - 1) + A * (A * N + r * (2 * x - 1)) := by
    rw [hD, hN, hA]
    ring
  have hJpoly : h * (r - 1) * N - r * O = A * N + r * (2 * x - 1) := by
    rw [hN, hO, hA]
    ring
  have hleft : h * r * (r - 1) * ((h - 1) * N) +
      r * (D + (A * N + r * (2 * x - 1))) = r ^ 2 * (r - 1) * G := by
    rw [hD, hG, hN, hA]
    ring
  have hright : h * r * (r - 1) * ((h - 1) * O) +
      h * (r - 1) * (D + h * (A * N + r * (2 * x - 1))) =
        h * r * (r - 1) ^ 2 * G := by
    rw [hD, hG, hN, hO, hA]
    ring
  have htwo : (M - L) * ((h - 1) * N * O) = J * D := by
    calc
      _ = (M * ((h - 1) * O)) * N - (L * ((h - 1) * N)) * O := by ring
      _ = A * N + r * (2 * x - 1) := by rw [hM, hL]; exact hJpoly
      _ = J * D := hJ.symm
  have hthree : K * D = (h - 1) ^ 2 * N * O * (L * M) := by
    calc
      _ = h * r * (r - 1) := hK
      _ = (L * ((h - 1) * N)) * (M * ((h - 1) * O)) := by rw [hL, hM]; ring
      _ = _ := by ring
  refine ⟨?_, htwo, hthree, ?_, ?_, ?_⟩
  · apply mul_right_cancel₀ hDnz
    calc
      (K + A * J) * D = K * D + A * (J * D) := by ring
      _ = D := by rw [hK, hJ]; exact hDpoly.symm
      _ = 1 * D := (one_mul D).symm
  · apply mul_right_cancel₀ hDnz
    calc
      ((M - L) * K) * D = (M - L) * (K * D) := by ring
      _ = (h - 1) * ((M - L) * ((h - 1) * N * O)) * (L * M) := by rw [hthree]; ring
      _ = ((h - 1) * J * L * M) * D := by rw [htwo]; ring
  · have hden : (h - 1) * N * D ≠ 0 := mul_ne_zero hLN hDnz
    apply mul_right_cancel₀ hden
    calc
      (K + L * (1 + J)) * ((h - 1) * N * D) =
          (K * D) * ((h - 1) * N) + (L * ((h - 1) * N)) * (D + J * D) := by ring
      _ = r ^ 2 * (r - 1) * G := by rw [hK, hL, hJ]; exact hleft
      _ = (r ^ 2 * (r - 1) * G / ((h - 1) * N * D)) * ((h - 1) * N * D) :=
        (div_mul_cancel₀ _ hden).symm
  · have hden : (h - 1) * O * D ≠ 0 := mul_ne_zero hMO hDnz
    apply mul_right_cancel₀ hden
    calc
      (K + M * (1 + h * J)) * ((h - 1) * O * D) =
          (K * D) * ((h - 1) * O) + (M * ((h - 1) * O)) * (D + h * (J * D)) := by ring
      _ = h * r * (r - 1) ^ 2 * G := by rw [hK, hM, hJ]; exact hright
      _ = (h * r * (r - 1) ^ 2 * G / ((h - 1) * O * D)) * ((h - 1) * O * D) :=
        (div_mul_cancel₀ _ hden).symm

/-- The same geometric capacity identity governs both geometric-budget pattern charts. This
form clears the positive divisors in the geometric identity. -/
theorem fourGeometricBudget_geometric_budget {K L M A T R : ℝ}
    (hK : 0 < K) (hM : 0 < M) (hML : M ≤ L) (hA : 0 ≤ A) (hT : 0 < T)
    (hKR : A ^ 2 ≤ K * R) (hLR : A ≤ L * R)
    (hId : L * (K - M * T) = M * (K - L * A)) : A ^ 2 / T ≤ M * R := by
  have hL : 0 < L := hM.trans_le hML
  have hR : 0 ≤ R := (mul_nonneg_iff_of_pos_left hK).mp ((sq_nonneg A).trans hKR)
  apply (div_le_iff₀ hT).mpr
  by_cases h : K ≤ M * T
  · calc
      _ ≤ K * R := hKR
      _ ≤ (M * T) * R := mul_le_mul_of_nonneg_right h hR
      _ = _ := by ring
  · have hpos : 0 < L * (K - M * T) := mul_pos hL (sub_pos.mpr (lt_of_not_ge h))
    have hK' : 0 ≤ K - L * A := ((mul_pos_iff_of_pos_left hM).mp (hId ▸ hpos)).le
    have he : L * (M * T - L * A) = (L - M) * (K - L * A) := by
      linear_combination -hId
    have hprod : L * A ≤ M * T := sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hL).mp
      (he.symm ▸ mul_nonneg (sub_nonneg.mpr hML) hK'))
    calc
      A ^ 2 = A * A := pow_two A
      _ ≤ A * (L * R) := mul_le_mul_of_nonneg_left hLR hA
      _ = (L * A) * R := by ring
      _ ≤ (M * T) * R := mul_le_mul_of_nonneg_right hprod hR
      _ = _ := by ring

/-- In case I the exact coefficient `η` is feasible and gives the
nonnegative two-budget determinant. -/
theorem fourGeometricBudget_case_one_budget {K J h b : ℝ}
    (hJ : 0 < J) (hh : h < 0) (hK : K ≤ 1 + J)
    (hb₁ : 1 ≤ b) (hbK : K ≤ b) (hbA : (1 + J) ^ 2 / (1 + (2 - h) * J) ≤ b) :
    let T := 1 + (2 - h) * J
    let η := max 0 (max (K - 1) (J * (J + h) / T))
    0 ≤ η ∧ η ≤ J ∧ η + 1 ≤ b ∧ K ≤ η + 1 ∧
      0 ≤ η - h * J ∧ (J - η) ^ 2 ≤ (η - h * J) * (η + 1) := by
  intro T η
  have hT : 0 < T := by
    have hh' : 0 < 2 - h := by linarith only [hh]
    dsimp only [T]
    linarith only [mul_pos hh' hJ]
  have hη₀ : 0 ≤ η := le_max_left _ _
  have hηK : K - 1 ≤ η := (le_max_left _ _).trans (le_max_right _ _)
  have hηT : J * (J + h) / T ≤ η := (le_max_right _ _).trans (le_max_right _ _)
  have hJT : J + h ≤ T := by
    have he : T - (J + h) = (1 - h) * (1 + J) := by dsimp only [T]; ring
    have hp := mul_nonneg (show 0 ≤ 1 - h by linarith only [hh]) (show 0 ≤ 1 + J by linarith only [hJ])
    linarith only [he, hp]
  have hηJ : η ≤ J := max_le hJ.le (max_le (by linarith only [hK])
    ((div_le_iff₀ hT).mpr (mul_le_mul_of_nonneg_left hJT hJ.le)))
  have hEq : (1 + J) ^ 2 = T + J * (J + h) := by dsimp only [T]; ring
  have hbA' : J * (J + h) / T ≤ b - 1 := by
    have hb' : (1 + J) ^ 2 ≤ b * T := (div_le_iff₀ hT).mp hbA
    exact (div_le_iff₀ hT).mpr (by linarith only [hb', hEq])
  have hηb : η ≤ b - 1 := max_le (sub_nonneg.mpr hb₁) (max_le (by linarith only [hbK]) hbA')
  have hcoef := mul_nonpos_of_nonpos_of_nonneg hh.le hJ.le
  have hcap := (div_le_iff₀ hT).mp hηT
  refine ⟨hη₀, hηJ, by linarith only [hηb], by linarith only [hηK], ?_, ?_⟩
  · linarith only [hη₀, hcoef]
  · have he : (η - h * J) * (η + 1) - (J - η) ^ 2 = η * T - J * (J + h) := by
      dsimp only [T]
      ring
    linarith only [he, hcap]

/-- In case II the endpoint coefficient saturates the two-budget bound
and all its displayed ordinary coefficients are nonnegative. -/
theorem fourGeometricBudget_case_two_budget {P α B : ℝ} (hP : 0 < P) (hα : 0 < P + α)
    (hB : P ^ 2 / (2 * P + α) ≤ B) :
    let T := 2 * P + α
    let η := P ^ 2 / T
    0 ≤ η ∧ 0 ≤ η + α ∧ η ≤ P ∧ η ≤ B ∧ (P - η) ^ 2 = η * (η + α) := by
  intro T η
  have hT : 0 < T := by dsimp only [T]; linarith only [hP, hα]
  have hη₀ : 0 ≤ η := div_nonneg (sq_nonneg _) hT.le
  have he : η * T = P ^ 2 := div_mul_cancel₀ _ hT.ne'
  have hpT : P ≤ T := by dsimp only [T]; linarith only [hα]
  have hηP : η ≤ P := by
    apply (div_le_iff₀ hT).mpr
    rw [pow_two]
    exact mul_le_mul_of_nonneg_left hpT hP.le
  have hηα : 0 ≤ η + α := by
    apply (mul_nonneg_iff_of_pos_right hT).mp
    have h : (η + α) * T = (P + α) ^ 2 := by
      dsimp only [T] at he ⊢
      linear_combination he
    rw [h]
    exact sq_nonneg _
  refine ⟨hη₀, hηα, hηP, hB, ?_⟩
  dsimp only [T] at he
  linear_combination -he

end MOC

/-! The polynomial identities behind the geometric-budget pattern chart sign and capacity tests. -/

namespace MOC

/-- The two geometric capacity identities share one cross product. The
outer-chart inequalities follow from the two displayed squared factors. -/
theorem fourGeometricBudget_chart_geometry (h r x y : ℝ) (hh : h - 1 ≠ 0) :
    let A := h * r - h - r
    let N := x ^ 2 + y ^ 2
    let O := (x - 1) ^ 2 + y ^ 2
    let D := (A * x + r) ^ 2 + (A * y) ^ 2
    let G := (1 + (h - 1) * x) ^ 2 + ((h - 1) * y) ^ 2
    let K := h * r * (r - 1) / D
    let J := (A * N + r * (2 * x - 1)) / D
    let L := r / ((h - 1) * N)
    let M := h * (r - 1) / ((h - 1) * O)
    N ≠ 0 → O ≠ 0 → D ≠ 0 →
    K + A * J = 1 ∧ (M - L) * ((h - 1) * N * O) = J * D ∧
    K * D = (h - 1) ^ 2 * N * O * (L * M) ∧
    (M - L) * K = (h - 1) * J * L * M ∧
    K + L * (1 + J) = r ^ 2 * (r - 1) * G / ((h - 1) * N * D) ∧
    K + M * (1 + h * J) = h * r * (r - 1) ^ 2 * G / ((h - 1) * O * D) := by
  intro A N O D G K J L M hN hO hD
  exact geometricBudget_chart_geometry_algebra h r x y A N O D G hh hN hO hD
    rfl rfl rfl rfl rfl

/-- The two normalized geometric budget identities use the same
cross product, with the donors interchanged in the second chart. -/
theorem fourGeometricBudget_geometric_budget_identities {h J K L M : ℝ}
    (hI : (M - L) * K = (h - 1) * J * L * M) :
    let α := 1 + J
    let P := -(1 + h * J)
    let T₁ := 1 + (2 - h) * J
    let T₂ := 2 * P + α
    (-M) * (K - (-L) * T₁) = (-L) * (K - (-M) * α) ∧
      L * (K - M * T₂) = M * (K - L * P) := by
  intro α P T₁ T₂
  constructor <;> dsimp only [α, P, T₁, T₂] <;> linear_combination -hI

/-- In the geometric-budget pattern chart the two unmatched defects are nonnegative when the
cross product has the ordinary-minor sign. -/
theorem fourGeometricBudget_minor_defects_of_sign {A B u v E L W : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hL : L ≠ 0) (hEL : E * L ≤ 0) (hW : 0 ≤ W)
    (hs : A + B = u + v) (hp : (A * B - u * v) * L ^ 2 = -(E * L) * W) :
    0 ≤ A ∧ 0 ≤ B := by
  have hprod : 0 ≤ (A * B - u * v) * L ^ 2 := by
    rw [hp]
    exact mul_nonneg (neg_nonneg.mpr hEL) hW
  have hAB : 0 ≤ A * B := (mul_nonneg hu hv).trans
    (sub_nonneg.mp ((mul_nonneg_iff_of_pos_right (sq_pos_of_ne_zero hL)).mp hprod))
  have hsum : 0 ≤ A + B := hs.symm ▸ add_nonneg hu hv
  constructor
  · by_contra! h
    have hp' : 0 < B := by linarith only [hsum, h]
    exact (not_lt_of_ge hAB) (mul_neg_of_neg_of_pos h hp')
  · by_contra! h
    have hp' : 0 < A := by linarith only [hsum, h]
    exact (not_lt_of_ge hAB) (mul_neg_of_pos_of_neg hp' h)

end MOC
