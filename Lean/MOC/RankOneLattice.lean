import MOC.RankOneVariance
import MOC.ThresholdVariance

/-! Integral rank-one scores on nested column thresholds. The design of
the threshold law uses squared projection minors (Lyons, DOI
10.1007/s10240-003-0016-0), but no joint flag moment theorem. -/

open Matrix Finset BigOperators

namespace MOC
noncomputable section

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Fintype K]

/-- The signed variance of any rank-one assignment score built from
integer row scores and a nested family of integral column thresholds
dominates the sharp lattice lower bound. Arbitrary integral column
scores have this representation by their increasing superlevel sets. -/
theorem rankOne_threshold_lattice_bound (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (x : ι → ℤ) (base : ℤ) (D : K → Finset ι) (d : K → ℕ)
    (hchain : ∀ i j : ι, (∀ t, i ∈ D t → j ∈ D t) ∨
      (∀ t, j ∈ D t → i ∈ D t)) :
    let X := Uᴴ * diagonal (fun i => (x i : ℂ)) * U
    let y (j : ι) : ℝ := base + ∑ t : K, if j ∈ D t then (d t : ℝ) else 0
    let m := ∑ j, y j * (X j j).re
    latticeVariancePenalty m ≤ ∑ σ : Equiv.Perm ι, realSignedWeight U σ *
      ((∑ j, y j * (x (σ j) : ℝ)) - m)^2 := by
  classical
  intro X y m
  let S (ij : ι × ι) : Finset K := univ.filter fun t => ¬ (ij.1 ∈ D t ↔ ij.2 ∈ D t)
  let c (ij : ι × ι) := Complex.normSq (X ij.1 ij.2) / 2
  let μ (t : K) := (d t : ℝ) * ∑ j ∈ D t, (X j j).re
  let w (t : K) (I : Finset ι) := subsetMinorSq U I (D t)
  let s (t : K) (I : Finset ι) : ℤ := (d t : ℤ) * ∑ i ∈ I, x i
  have hX : Uᴴ * diagonal (fun i => ((x i : ℝ) : ℂ)) * U = X := by
    simp [X]
  have hmom (t : K) := subset_minor_score_mean_variance U hU (fun i => (x i : ℝ)) (D t)
  simp only [hX] at hmom
  have hm (t : K) : μ t = ∑ I : Finset ι, w t I * (s t I : ℝ) := by
    dsimp [μ,w,s]
    rw [← (hmom t).1,mul_sum]
    push_cast
    apply sum_congr rfl
    intro I _
    ring
  have hvar (t : K) : (∑ I : Finset ι, w t I * ((s t I : ℝ) - μ t)^2) =
      ∑ e : ι × ι, if t ∈ S e then c e * (d t : ℝ)^2 else 0 := by
    have hpt (I : Finset ι) :
        w t I * ((s t I : ℝ) - μ t)^2 =
        (d t : ℝ)^2 * (w t I * ((∑ i ∈ I, (x i : ℝ)) - ∑ j ∈ D t, (X j j).re)^2) := by
      dsimp [s,μ]
      push_cast
      ring
    simp_rw [hpt,← mul_sum]
    change _ * (∑ I : Finset ι, subsetMinorSq U I (D t) *
      ((∑ i ∈ I, (x i : ℝ)) - ∑ j ∈ D t, (X j j).re)^2) = _
    rw [(hmom t).2, Fintype.sum_prod_type, ← mul_div_assoc, mul_sum, sum_div]
    apply sum_congr rfl
    intro i _
    rw [mul_sum, sum_div]
    apply sum_congr rfl
    intro j _
    by_cases he : i ∈ D t ↔ j ∈ D t <;> simp [S,c,he] <;> ring
  have hscore (i j : ι) : (y i - y j)^2 = (∑ t ∈ S (i,j), (d t : ℝ))^2 := by
    have hc₁ (i j : ι) (h : ∀ t, j ∈ D t → i ∈ D t) :
        y i - y j = ∑ t ∈ S (i,j), (d t : ℝ) := by
      simp only [y,add_sub_add_left_eq_sub,← sum_sub_distrib,S,sum_filter]
      apply sum_congr rfl
      intro t _
      by_cases hi : i ∈ D t <;> by_cases hj : j ∈ D t <;> simp_all
    rcases hchain i j with hi | hj
    · rw [show y i - y j = -(y j - y i) by ring, neg_sq, hc₁ j i hi]
      congr 1
      simp [S,iff_comm]
    · rw [hc₁ i j hj]
  have htrace : ∑ j, (X j j).re = ∑ i : ι, (x i : ℝ) := by
    have hx (j : ι) := signed_single_assignment_moment U hU (fun i => (x i : ℝ)) j
    simp only [hX] at hx
    simp_rw [← hx]
    rw [sum_comm]
    simp_rw [← mul_sum]
    have hperm (σ : Equiv.Perm ι) : (∑ j, (x (σ j) : ℝ)) = ∑ i, (x i : ℝ) :=
      Equiv.sum_comp σ (fun i => (x i : ℝ))
    simp only [hperm]
    rw [← sum_mul, sum_realSignedWeight U hU, one_mul]
  have hmfull : m = (∑ t, μ t) + ((base * ∑ i : ι, x i : ℤ) : ℝ) := by
    dsimp [m,y]
    simp only [add_mul,sum_add_distrib,← mul_sum,htrace,Int.cast_mul,Int.cast_sum]
    simp_rw [sum_mul]
    rw [sum_comm (s := (univ : Finset ι)) (t := (univ : Finset K))]
    rw [add_comm]
    congr 1
    apply sum_congr rfl
    intro t _
    simp [μ,sum_filter,ite_mul, mul_sum]
  have h := independent_threshold_variance_lower_bound S c (fun t => (d t : ℝ))
      (fun e => div_nonneg (Complex.normSq_nonneg _) (by norm_num)) (fun _ => Nat.cast_nonneg _)
      w s (fun _ _ => subsetMinorSq_nonneg _ _ _) (fun t => sum_subsetMinorSq _ hU _)
      μ hm hvar (base * ∑ i : ι, x i)
  rw [← hmfull] at h
  apply h.trans_eq
  have hv := rankOne_signed_variance U hU (fun i => (x i : ℝ)) y
  simp only [hX] at hv
  rw [hv, Fintype.sum_prod_type,sum_div]
  apply sum_congr rfl
  intro i _
  rw [sum_div]
  apply sum_congr rfl
  intro j _
  rw [hscore]
  dsimp [c]
  ring

end
end MOC
