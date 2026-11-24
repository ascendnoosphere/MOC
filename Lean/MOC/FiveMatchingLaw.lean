import MOC.Weights
import Mathlib.Data.Fintype.Perm
import MOC.WeightedDiamondAdjacency

open BigOperators Matrix

namespace MOC.FiveMatchingLaw

noncomputable section

private theorem linear_score {d : ℕ} (L : (Fin d → ℝ) →ₗ[ℝ] ℝ) (v : Fin d → ℝ) :
    L v = ∑ k, L (Pi.single k 1) * v k := by
  have he : v = ∑ k, v k • (Pi.single k 1 : Fin d → ℝ) := by
    funext j
    simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite]
  conv_lhs => rw [he]
  simp only [map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k _
  exact mul_comm _ _

set_option maxRecDepth 24000
set_option maxHeartbeats 8000000

private theorem exists_coordinate_law {κ : Type*} [Fintype κ] {n m d : ℕ} (base : Fin d)
    (point : Fin n → Fin d → ℤ) (labelPoint : κ → Fin n)
    (finalRay : Fin m → Fin n → ℤ) (hbase : ∀ i, point i base = 1)
    (hsurj : Function.Surjective labelPoint)
    (hrays : ∀ (c : Fin d → ℝ), (∀ i, 0 ≤ ∑ k, c k * (point i k : ℝ)) →
      ∃ μ : Fin m → ℝ, (∀ r, 0 ≤ μ r) ∧ ∀ i,
        (∑ k, c k * (point i k : ℝ)) = ∑ r, μ r * (finalRay r i : ℝ))
    (v : κ → ℝ) (hv : ∑ p, v p = 1)
    (hnonneg : ∀ r, 0 ≤ ∑ p, v p * (finalRay r (labelPoint p) : ℝ)) :
    ∃ w : κ → ℝ, (∀ p, 0 ≤ w p) ∧ (∑ p, w p = 1) ∧ ∀ k,
      (∑ p, w p * (point (labelPoint p) k : ℝ)) = ∑ p, v p * (point (labelPoint p) k : ℝ) := by
  classical
  let b (p : κ) (k : Fin d) : ℝ := point (labelPoint p) k
  let x : Fin d → ℝ := ∑ p, v p • b p
  have hb₀ (p : κ) : b p base = 1 := by simp [b, hbase]
  have hx₀ : x base = 1 := by
    simpa only [x, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hb₀, mul_one] using hv
  have htest (L : (Fin d → ℝ) →ₗ[ℝ] ℝ) (hL : ∀ p, 0 ≤ L (b p)) : 0 ≤ L x := by
    let c (k : Fin d) := L (Pi.single k 1)
    have hc : ∀ i : Fin n, 0 ≤ ∑ k, c k * (point i k : ℝ) := by
      intro i
      obtain ⟨p, rfl⟩ := hsurj i
      exact (linear_score L (b p)) ▸ hL p
    obtain ⟨μ, hμ, hsum⟩ := hrays c hc
    have he (p : κ) :
        L (b p) = ∑ r, μ r * (finalRay r (labelPoint p) : ℝ) :=
      (linear_score L (b p)).trans (hsum (labelPoint p))
    simp only [x, map_sum, map_smul, smul_eq_mul, he, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_nonneg
    intro r _
    calc
      0 ≤ μ r * ∑ p, v p * (finalRay r (labelPoint p) : ℝ) :=
        mul_nonneg (hμ r) (hnonneg r)
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p _
        ring
  let A : (Fin d → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj base
  have hA (p : κ) : 0 < A (b p) := by
    change 0 < b p base
    rw [hb₀]
    exact zero_lt_one
  have hAx : 0 < A x := by
    change 0 < x base
    rw [hx₀]
    exact zero_lt_one
  obtain ⟨w, hw, hvec⟩ := exists_conic_weights_of_linear_tests b A x hA hAx htest
  have hwc (k : Fin d) : ∑ p, w p * b p k = ∑ p, v p * b p k := by
    simpa only [x, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using congrFun hvec.symm k
  have hw₁ : ∑ p, w p = 1 := by
    simpa only [hb₀, mul_one, hv] using hwc base
  exact ⟨w, hw, hw₁, hwc⟩

/-- A cone of nonnegative coefficient tests gives a single law for all evaluations
of the matching polynomials. Each final ray must have nonnegative signed expectation. -/
theorem exists_common_law {ι P : Type*} [Fintype ι] [DecidableEq ι]
    {n m d : ℕ} (base : Fin d)
    (point : Fin n → Fin d → ℤ) (labelPoint : Equiv.Perm ι → Fin n)
    (finalRay : Fin m → Fin n → ℤ) (hbase : ∀ i, point i base = 1)
    (hsurj : Function.Surjective labelPoint)
    (hrays : ∀ (c : Fin d → ℝ), (∀ i, 0 ≤ ∑ k, c k * (point i k : ℝ)) →
      ∃ μ : Fin m → ℝ, (∀ r, 0 ≤ μ r) ∧ ∀ i,
        (∑ k, c k * (point i k : ℝ)) = ∑ r, μ r * (finalRay r i : ℝ))
    (left right : P → ι → ℂ) (basis : P → Fin d → ℂ)
    (matching_eq : ∀ z p, matchingProduct (left z) (right z) p =
      ∑ k, (point (labelPoint p) k : ℂ) * basis z k)
    (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (hnonneg : ∀ r, 0 ≤ ∑ p, realSignedWeight U p *
      (finalRay r (labelPoint p) : ℝ)) :
    ∃ w : Equiv.Perm ι → ℝ, (∀ p, 0 ≤ w p) ∧ (∑ p, w p = 1) ∧
      ∀ z : P, ∑ p, (w p : ℂ) *
        matchingProduct (left z) (right z) p =
          determinantValue (left z) (right z) U := by
  classical
  let v (p : Equiv.Perm ι) := realSignedWeight U p
  have hv : ∑ p, v p = 1 := sum_realSignedWeight U hU
  obtain ⟨w, hw, hw₁, hwc⟩ :=
    exists_coordinate_law base point labelPoint finalRay hbase hsurj hrays v hv hnonneg
  refine ⟨w, hw, hw₁, ?_⟩
  intro z
  calc
    _ = ∑ p, (v p : ℂ) * matchingProduct (left z) (right z) p := by
      simp_rw [matching_eq, Finset.mul_sum]
      conv_lhs => rw [Finset.sum_comm]
      conv_rhs => rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      simp_rw [← mul_assoc, ← Finset.sum_mul]
      congr 1
      have he := congrArg (fun t : ℝ => (t : ℂ)) (hwc k)
      simpa using he
    _ = _ := real_signed_determinant (left z) (right z) U hU

end
end MOC.FiveMatchingLaw
