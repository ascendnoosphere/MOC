import MOC.SignedPairMoments

/-! Signed variance of the rank-one assignment score as a norm-square
over unordered pairs (written as half of a double sum). Related
projection determinantal convention: R. Lyons,
DOI 10.1007/s10240-003-0016-0. -/

open Matrix Finset BigOperators

namespace MOC

noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The signed covariance of two different assignment slots is negative
squared Gram entry. On the diagonal it is the sum of all the other
squared Gram entries in that row. -/
theorem signed_assignment_covariance (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (x : ι → ℝ) (j k : ι) :
    let X := Uᴴ * diagonal (fun i => (x i : ℂ)) * U
    (∑ σ : Equiv.Perm ι, realSignedWeight U σ *
      ((x (σ j) - (X j j).re) * (x (σ k) - (X k k).re))) =
      if j = k then (∑ l : ι, Complex.normSq (X j l)) - Complex.normSq (X j j)
      else -Complex.normSq (X j k) := by
  intro X
  let w := realSignedWeight U
  let m (j : ι) := (X j j).re
  have hlin (i : ι) : (∑ σ : Equiv.Perm ι, w σ * x (σ i)) = m i :=
    signed_single_assignment_moment U hU x i
  have hsw : ∑ σ : Equiv.Perm ι, w σ = 1 := sum_realSignedWeight U hU
  have hcalc (σ : Equiv.Perm ι) :
      w σ * ((x (σ j) - m j) * (x (σ k) - m k)) =
        w σ * (x (σ j) * x (σ k)) -
          (w σ * x (σ j)) * m k - (w σ * x (σ k)) * m j + w σ * (m j * m k) := by
    ring
  change ∑ σ : Equiv.Perm ι, w σ * ((x (σ j) - m j) * (x (σ k) - m k)) = _
  simp_rw [hcalc]
  rw [sum_add_distrib, sum_sub_distrib, sum_sub_distrib, ← sum_mul, ← sum_mul,
    ← sum_mul, hlin, hlin, hsw, one_mul]
  by_cases h : j = k
  · subst k
    rw [if_pos rfl]
    have hHerm : X.IsHermitian := by
      unfold X Matrix.IsHermitian
      simp [Matrix.conjTranspose_mul, Matrix.diagonal_conjTranspose, mul_assoc,
        Pi.star_def, Complex.star_def]
    have hd : (X j j).im = 0 := by
      have he := congrArg Complex.im (show star (X j j) = X j j by
        simpa using congrArg (fun M : Matrix ι ι ℂ => M j j) hHerm)
      simp [Complex.star_def] at he
      linarith
    have hnorm : Complex.normSq (X j j) = (m j)^2 := by
      rw [Complex.normSq_apply, hd]
      simp [m, pow_two]
    have hX2 : X * X = Uᴴ * diagonal (fun i => ((x i * x i : ℝ) : ℂ)) * U := by
      dsimp [X]
      simp only [mul_assoc,← mul_assoc U Uᴴ, hU.1, one_mul,
        ← mul_assoc (diagonal _) (diagonal _), Matrix.diagonal_mul_diagonal,
        Complex.ofReal_mul]
    have hG : ((X * X) j j).re = ∑ l : ι, Complex.normSq (X j l) := by
      rw [Matrix.mul_apply, Complex.re_sum]
      apply sum_congr rfl
      intro i _
      have ht : star (X j i) = X i j := by
        simpa using congrArg (fun M : Matrix ι ι ℂ => M i j) hHerm
      rw [← ht, mul_comm (X j i), ← starRingEnd_apply, ← Complex.normSq_eq_conj_mul_self,
        Complex.ofReal_re]
    have hm2 := signed_single_assignment_moment U hU (fun i => x i * x i) j
    rw [← hX2,hG] at hm2
    rw [hm2,hnorm]
    ring
  · rw [if_neg h, signed_pair_assignment_moment U hU x h]
    unfold m
    ring

/-- The mean-subtracted signed second moment of a rank-one cost is
the sum of squared weighted commutator entries, divided by two. -/
theorem rankOne_signed_variance (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (x y : ι → ℝ) :
    let X := Uᴴ * diagonal (fun i => (x i : ℂ)) * U
    let m := ∑ j : ι, y j * (X j j).re
    (∑ σ : Equiv.Perm ι, realSignedWeight U σ *
        ((∑ j : ι, y j * x (σ j)) - m)^2) =
      (∑ j : ι, ∑ k : ι, Complex.normSq (X j k) * (y j - y k)^2) / 2 := by
  intro X m
  let w := realSignedWeight U
  let r (σ : Equiv.Perm ι) (j : ι) := x (σ j) - (X j j).re
  let c (j k : ι) := Complex.normSq (X j k)
  have hHerm : X.IsHermitian := by
    unfold X Matrix.IsHermitian
    simp [Matrix.conjTranspose_mul, Matrix.diagonal_conjTranspose, mul_assoc,
      Pi.star_def, Complex.star_def]
  have hc (j k : ι) : c j k = c k j := by
    have hh : star (X j k) = X k j := by
      simpa using congrArg (fun M : Matrix ι ι ℂ => M k j) hHerm
    dsimp [c]
    rw [← hh]
    simp [Complex.star_def, Complex.normSq_conj]
  have hσ (σ : Equiv.Perm ι) :
      w σ * ((∑ j, y j * x (σ j)) - m)^2 =
        ∑ j, ∑ k, (y j * y k) * (w σ * (r σ j * r σ k)) := by
    have hm : (∑ j, y j * x (σ j)) - m = ∑ j, y j * r σ j := by
      simp [r,m,mul_sub,sum_sub_distrib]
    rw [hm,pow_two,sum_mul, mul_sum]
    apply sum_congr rfl
    intro j _
    simp only [mul_sum]
    apply sum_congr rfl
    intro k _
    ring
  have he (j k : ι) :
      (∑ σ : Equiv.Perm ι, w σ * (r σ j * r σ k)) =
      (if j = k then ∑ l, c j l else 0) - c j k := by
    have h := signed_assignment_covariance U hU x j k
    by_cases h' : j = k
    · subst k; simpa [X,w,r,c] using h
    · simpa [X,w,r,c,h'] using h
  have hcomm (f : ι → ι → Equiv.Perm ι → ℝ) :
      ∑ j, ∑ k, ∑ σ, f j k σ = ∑ σ, ∑ j, ∑ k, f j k σ := by
    calc
      _ = ∑ j, ∑ σ, ∑ k, f j k σ := by
        apply sum_congr rfl
        intro j _
        rw [sum_comm]
      _ = _ := sum_comm
  have hform :
      (∑ j, ∑ k, (y j * y k) * ((if j = k then ∑ l, c j l else 0) - c j k)) =
        (∑ j, ∑ k, c j k * y j ^ 2) - ∑ j, ∑ k, c j k * (y j * y k) := by
    simp only [mul_sub, sum_sub_distrib]
    congr 1
    · apply sum_congr rfl
      intro j _
      rw [sum_eq_single j]
      · rw [if_pos rfl]
        simp_rw [mul_comm (c j _), ← mul_sum, pow_two]
      · intro k _ h'
        rw [if_neg h'.symm,mul_zero]
      · simp
    · apply sum_congr rfl
      intro j _
      apply sum_congr rfl
      intro k _
      ring
  have hsymmetric : ∑ j, ∑ k, c j k * y k^2 = ∑ j, ∑ k, c j k * y j^2 := by
    rw [sum_comm]
    apply sum_congr rfl
    intro j _
    apply sum_congr rfl
    intro k _
    rw [hc k j]
  change (∑ σ, w σ * ((∑ j, y j * x (σ j)) - m)^2) = _
  simp_rw [hσ]
  rw [← hcomm]
  simp_rw [← mul_sum, he]
  rw [hform]
  change _ = (∑ j, ∑ k, c j k * (y j - y k)^2)/2
  have ht : (∑ j, ∑ k, c j k * (2 * y j * y k)) =
      2 * ∑ j, ∑ k, c j k * (y j * y k) := by
    simp only [mul_sum]
    apply sum_congr rfl
    intro j _
    apply sum_congr rfl
    intro k _
    ring
  simp only [sub_sq, mul_sub, mul_add, sum_add_distrib, sum_sub_distrib, hsymmetric, ht]
  ring

private theorem subsetImage_expectation (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (J : Finset ι) (f : Finset ι → ℝ) :
    (∑ I : Finset ι, subsetMinorSq U I J * f I) =
      ∑ σ : Equiv.Perm ι, realSignedWeight U σ * f (J.map σ.toEmbedding) := by
  classical
  rw [← Finset.sum_fiberwise univ (fun σ : Equiv.Perm ι => J.map σ.toEmbedding)]
  apply sum_congr rfl
  intro I _
  have hm : (∑ σ ∈ univ.filter (fun σ : Equiv.Perm ι => J.map σ.toEmbedding = I),
      realSignedWeight U σ) = subsetMinorSq U I J := by
    simpa only [Complex.re_sum, Complex.ofReal_re, realSignedWeight] using
      congrArg Complex.re (sum_signedWeight_image_eq_subsetMinorSq U hU I J)
  rw [← hm,sum_mul]
  apply sum_congr rfl
  intro σ hσ
  rw [(mem_filter.mp hσ).2]

/-- The finite law of a fixed column subset (in particular, a prefix)
has the exact mean and variance prescribed by the unitary edge weights. -/
theorem subset_minor_score_mean_variance (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (x : ι → ℝ) (J : Finset ι) :
    let X := Uᴴ * diagonal (fun i => (x i : ℂ)) * U
    let m := ∑ j ∈ J, (X j j).re
    (∑ I : Finset ι, subsetMinorSq U I J * (∑ i ∈ I, x i)) = m ∧
      (∑ I : Finset ι, subsetMinorSq U I J * ((∑ i ∈ I, x i) - m)^2) =
        (∑ j : ι, ∑ k : ι, if (j ∈ J) ↔ (k ∈ J)
          then 0 else Complex.normSq (X j k)) / 2 := by
  classical
  intro X m
  have hmap (σ : Equiv.Perm ι) :
      (∑ i ∈ J.map σ.toEmbedding, x i) = ∑ j ∈ J, x (σ j) := by
    simp [sum_map]
  constructor
  · rw [subsetImage_expectation _ hU]
    simp only [hmap, mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro j _
    exact signed_single_assignment_moment U hU x j
  · let y (j : ι) : ℝ := if j ∈ J then 1 else 0
    have hmean : ∑ j : ι, y j * (X j j).re = m := by
      simp [y,m,sum_filter,ite_mul]
    have hscore (σ : Equiv.Perm ι) :
        (∑ j : ι, y j * x (σ j)) = ∑ j ∈ J, x (σ j) := by
      simp [y,sum_filter,ite_mul]
    have hv := rankOne_signed_variance U hU x y
    dsimp only at hv
    change (∑ σ : Equiv.Perm ι, realSignedWeight U σ *
        ((∑ j, y j * x (σ j)) - ∑ j, y j * (X j j).re)^2) =
      (∑ j, ∑ k, Complex.normSq (X j k) * (y j - y k)^2) / 2 at hv
    rw [hmean] at hv
    simp_rw [hscore] at hv
    rw [subsetImage_expectation _ hU]
    simp_rw [hmap]
    rw [hv]
    congr 1
    apply sum_congr rfl
    intro j _
    apply sum_congr rfl
    intro k _
    by_cases hj : j ∈ J <;> by_cases hk : k ∈ J <;> simp [y,hj,hk]

end
end MOC
