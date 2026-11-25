import MOC.TwoFrame
import MOC.FiniteMinorLaw

/-! The signed first and second assignment moments come from one- and
two-column Gram minors, not from conditioning a signed probability.
Projection determinantal background: R. Lyons, DOI
10.1007/s10240-003-0016-0. -/

open Matrix Finset BigOperators

namespace MOC

noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem signed_single_assignment_moment (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (x : ι → ℝ) (j : ι) :
    (∑ σ : Equiv.Perm ι, realSignedWeight U σ * x (σ j)) =
      ((Uᴴ * diagonal (fun i => (x i : ℂ)) * U) j j).re := by
  classical
  have h (σ : Equiv.Perm ι) : realSignedWeight U σ * x (σ j) =
      ∑ i : ι, (if σ j = i then realSignedWeight U σ else 0) * x i := by
    rw [sum_eq_single (σ j)]
    · simp
    · intro i _ hi
      simp [Ne.symm hi]
    · simp
  simp_rw [h]
  rw [sum_comm]
  simp only [← sum_mul, marginal_realSignedWeight U hU]
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, Complex.re_sum]
  apply sum_congr rfl
  intro i _
  rw [mul_comm (star (U i j)) _, mul_assoc, ← starRingEnd_apply, ← Complex.normSq_eq_conj_mul_self, Complex.re_ofReal_mul, Complex.ofReal_re, mul_comm]

omit [Fintype ι] in
private theorem pair_event_iff (σ : Equiv.Perm ι) {i l j k : ι} (hj : j ≠ k) :
    (i ≠ l ∧ ({j,k} : Finset ι).map σ.toEmbedding = {i,l}) ↔
      (σ j = i ∧ σ k = l) ∨ (σ j = l ∧ σ k = i) := by
  have hn := σ.injective.ne hj
  simp only [map_insert, map_singleton, Equiv.toEmbedding_apply]
  constructor
  · rintro ⟨hil, h⟩
    have ha : σ j = i ∨ σ j = l := by
      have he : σ j ∈ ({i,l} : Finset ι) := h ▸ (by simp)
      simpa using he
    have hb : σ k = i ∨ σ k = l := by
      have he : σ k ∈ ({i,l} : Finset ι) := h ▸ (by simp)
      simpa using he
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact (hn (ha.trans hb.symm)).elim
    · exact Or.inl ⟨ha,hb⟩
    · exact Or.inr ⟨ha,hb⟩
    · exact (hn (ha.trans hb.symm)).elim
  · rintro (⟨h₁,h₂⟩ | ⟨h₁,h₂⟩)
    · subst i; subst l; exact ⟨hn,rfl⟩
    · subst i; subst l; exact ⟨hn.symm,Finset.pair_comm _ _⟩

private theorem pair_weight_sum (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (x : ι → ℝ) {j k : ι} (hjk : j ≠ k) :
    2 * (∑ σ : Equiv.Perm ι, realSignedWeight U σ * (x (σ j) * x (σ k))) =
      ∑ i, ∑ l, (x i * x l) *
        Complex.normSq (U i j * U l k - U i k * U l j) := by
  classical
  let C (σ : Equiv.Perm ι) (i l : ι) :=
    if i ≠ l ∧ ({j,k} : Finset ι).map σ.toEmbedding = {i,l}
      then realSignedWeight U σ * (x i * x l) else 0
  have hC (σ : Equiv.Perm ι) (i l : ι) :
      C σ i l =
        (if σ j = i ∧ σ k = l then realSignedWeight U σ * (x i * x l) else 0) +
        (if σ j = l ∧ σ k = i then realSignedWeight U σ * (x i * x l) else 0) := by
    dsimp only [C]
    rw [if_congr (pair_event_iff σ hjk) rfl rfl]
    by_cases h₁ : σ j = i ∧ σ k = l
    · have h₂ : ¬ (σ j = l ∧ σ k = i) := fun he =>
        (σ.injective.ne hjk) (h₁.1.trans he.2.symm)
      rw [if_pos (Or.inl h₁), if_pos h₁, if_neg h₂, add_zero]
    · simp only [h₁, false_or, if_false, zero_add]
  have hσ (σ : Equiv.Perm ι) :
      2 * (realSignedWeight U σ * (x (σ j) * x (σ k))) = ∑ i, ∑ l, C σ i l := by
    simp only [hC,sum_add_distrib]
    have hs (a b : ι) : ∑ i : ι, ∑ l : ι,
        (if a = i ∧ b = l then realSignedWeight U σ * (x i * x l) else 0) =
          realSignedWeight U σ * (x a * x b) := by
      simp only [ite_and]
      simp [sum_ite_eq', eq_comm]
    rw [hs (σ j) (σ k)]
    have ht : (∑ i : ι, ∑ l : ι,
        (if σ j = l ∧ σ k = i then realSignedWeight U σ * (x i * x l) else 0)) =
        realSignedWeight U σ * (x (σ k) * x (σ j)) := by
      simpa only [and_comm] using hs (σ k) (σ j)
    rw [ht]
    ring
  rw [mul_sum]
  simp_rw [hσ]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  rw [sum_comm]
  apply sum_congr rfl
  intro l _
  by_cases hil : i = l
  · subst l
    simp [C,mul_comm]
  · have hc (σ : Equiv.Perm ι) : C σ i l =
        (if ({j,k} : Finset ι).map σ.toEmbedding = {i,l} then realSignedWeight U σ else 0) *
          (x i * x l) := by
      dsimp only [C]
      by_cases h : ({j,k} : Finset ι).map σ.toEmbedding = {i,l} <;> simp [hil,h]
    simp_rw [hc, ← sum_mul]
    have he : (∑ σ : Equiv.Perm ι,
        if ({j,k} : Finset ι).map σ.toEmbedding = {i,l} then realSignedWeight U σ else 0) =
          subsetMinorSq U {i,l} {j,k} := by
      simpa only [Complex.re_sum,Complex.ofReal_re,sum_filter,apply_ite,
        Complex.zero_re,realSignedWeight] using congrArg Complex.re
          (sum_signedWeight_image_eq_subsetMinorSq U hU {i,l} {j,k})
    rw [he,subsetMinorSq_pair U hU hil hjk]
    ring

/-- The genuine signed second assignment moment is the Gram determinant
on two distinguished columns. This statement does not use positivity
of the signed weights. -/
theorem signed_pair_assignment_moment (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (x : ι → ℝ) {j k : ι} (hjk : j ≠ k) :
    let X := Uᴴ * diagonal (fun i => (x i : ℂ)) * U
    (∑ σ : Equiv.Perm ι, realSignedWeight U σ * (x (σ j) * x (σ k))) =
      (X j j).re * (X k k).re - Complex.normSq (X j k) := by
  intro X
  let f : Fin 2 → ι := ![j,k]
  let W : Matrix ι (Fin 2) ℂ := U.submatrix id f
  have hentry (u v : Fin 2) : (Wᴴ * diagonal (fun i => (x i : ℂ)) * W) u v = X (f u) (f v) := by
    simp [W,X,Matrix.mul_apply,Matrix.mul_diagonal, Matrix.conjTranspose_apply]
  have hG := det_weighted_gram_two W (fun i => (x i : ℂ))
  rw [Matrix.det_fin_two] at hG
  simp only [hentry,f,Matrix.cons_val_zero,Matrix.cons_val_one, W,
    Matrix.submatrix_apply, id_eq] at hG
  have hHerm : X.IsHermitian := by
    unfold X Matrix.IsHermitian
    simp [Matrix.conjTranspose_mul, Matrix.diagonal_conjTranspose, mul_assoc, Pi.star_def, Complex.star_def]
  have hjk' : star (X j k) = X k j := by
    simpa using congrArg (fun M : Matrix ι ι ℂ => M k j) hHerm
  have hdreal (p : ι) : (X p p).im = 0 := by
    have he := congrArg Complex.im (show star (X p p) = X p p by
      simpa using congrArg (fun M : Matrix ι ι ℂ => M p p) hHerm)
    simp [Complex.star_def] at he
    linarith
  rw [← hjk',mul_comm (X j k), ← starRingEnd_apply, ← Complex.normSq_eq_conj_mul_self] at hG
  have hreal := congrArg Complex.re hG
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, hdreal,
    mul_zero, sub_zero] at hreal
  rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.div_ofReal_re] at hreal
  simp only [Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,
    mul_zero,sub_zero] at hreal
  linarith only [hreal, pair_weight_sum U hU x hjk]

end
end MOC
