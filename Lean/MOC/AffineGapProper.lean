import MOC.FiniteCurveCofiniteImage
import MOC.FiniteCurveProperProjection
import MOC.FiniteCurveAffineConnected

/-! Properness of a polynomial coordinate away from finitely many
values on an affine curve. A finite projection alone need not make a
different polynomial coordinate globally proper. -/

open Matrix Set MvPolynomial
open scoped BigOperators Topology

namespace MOC

private noncomputable def reverseCoeff (P : Polynomial (Polynomial ℂ)) (k : ℕ) : Polynomial ℂ :=
  ∑ j ∈ Finset.range (P.natDegree+1), Polynomial.monomial j ((P.coeff j).coeff k)

private noncomputable def reverseSpecialize (P : Polynomial (Polynomial ℂ)) (w : ℂ) : Polynomial ℂ :=
  ∑ j ∈ Finset.range (P.natDegree+1), P.coeff j * Polynomial.C (w^j)

private theorem coeff_reverseSpecialize (P : Polynomial (Polynomial ℂ)) (w : ℂ) (k : ℕ) :
    (reverseSpecialize P w).coeff k = (reverseCoeff P k).eval w := by
  simp only [reverseSpecialize, reverseCoeff, Polynomial.finset_sum_coeff, Polynomial.coeff_mul_C,
    Polynomial.eval_finset_sum, Polynomial.eval_monomial]

private theorem reverseSpecialize_eval (P : Polynomial (Polynomial ℂ)) (a w : ℂ) :
    (reverseSpecialize P w).eval a = (P.map (Polynomial.evalRingHom a)).eval w := by
  rw [Polynomial.eval_map, Polynomial.eval₂_eq_sum_range]
  simp only [reverseSpecialize, Polynomial.eval_finset_sum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.coe_evalRingHom]

private theorem reverseLeadingCoefficient (P : Polynomial (Polynomial ℂ)) (hP : P ≠ 0) :
    ∃ d, reverseCoeff P d ≠ 0 ∧ ∀ w : ℂ, (reverseSpecialize P w).natDegree ≤ d := by
  classical
  let J := Finset.range (P.natDegree+1)
  have hJ : J.Nonempty := ⟨0, Finset.mem_range.mpr (Nat.succ_pos _)⟩
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image J (fun j => (P.coeff j).natDegree) hJ
  let d := (P.coeff j).natDegree
  have hmax' : ∀ i ∈ J, (P.coeff i).natDegree ≤ d := hmax
  have hd : reverseCoeff P d ≠ 0 := by
    by_cases hj' : P.coeff j = 0
    · have hd₀ : d = 0 := by simp [d, hj']
      have hm : P.natDegree ∈ J := Finset.mem_range.mpr (Nat.lt_succ_self _)
      have hnd : (P.coeff P.natDegree).natDegree = 0 := by
        have h := hmax' _ hm
        omega
      have hn : (P.coeff P.natDegree).coeff d ≠ 0 := by
        rw [hd₀, ← hnd, Polynomial.coeff_natDegree]
        exact Polynomial.leadingCoeff_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr hP)
      intro h
      have he := congrArg (fun p : Polynomial ℂ => p.coeff P.natDegree) h
      exact hn (by simpa [reverseCoeff, Polynomial.finset_sum_coeff, Polynomial.coeff_monomial] using he)
    · have hn : (P.coeff j).coeff d ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hj'
      intro h
      have he := congrArg (fun p : Polynomial ℂ => p.coeff j) h
      have hjrange : j < P.natDegree + 1 := Finset.mem_range.mp hj
      exact hn (by simpa [reverseCoeff, Polynomial.finset_sum_coeff, Polynomial.coeff_monomial, hjrange] using he)
  refine ⟨d, hd, fun w => ?_⟩
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [coeff_reverseSpecialize]
  simp only [reverseCoeff, Polynomial.eval_finset_sum, Polynomial.eval_monomial]
  apply Finset.sum_eq_zero
  intro i hi
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt ((hmax' i hi).trans_lt hk), zero_mul]

/-- Reversing a monic plane equation gives a uniform bound for the old
base coordinate on compact sets of the new one away from a finite set. -/
theorem exists_uniform_reverse_specialization_bound (P : Polynomial (Polynomial ℂ)) (hP : P ≠ 0) :
    ∃ D : Polynomial ℂ, D ≠ 0 ∧ ∀ K : Set ℂ, IsCompact K → (∀ w ∈ K, D.eval w ≠ 0) →
      ∃ R : ℝ, ∀ a w : ℂ, w ∈ K →
        (P.map (Polynomial.evalRingHom a)).IsRoot w → ‖a‖ ≤ R := by
  classical
  obtain ⟨d, hd, hle⟩ := reverseLeadingCoefficient P hP
  let D := reverseCoeff P d
  refine ⟨D, hd, fun K hK havoid => ?_⟩
  let S := Finset.range (d+1)
  let F (w : ℂ) : ℝ := ∑ k ∈ S, ‖(reverseCoeff P k).eval w‖ / ‖D.eval w‖
  have hF : ContinuousOn F K := by
    apply continuousOn_finset_sum S
    intro k hk
    apply ((reverseCoeff P k).continuous.norm).continuousOn.div D.continuous.norm.continuousOn
    exact fun w hw => norm_ne_zero_iff.mpr (havoid w hw)
  obtain ⟨C, hC⟩ := (hK.image_of_continuousOn hF).bddAbove
  refine ⟨C+1, fun a w hw hroot => ?_⟩
  let Q := reverseSpecialize P w
  have hQd : Q.coeff d ≠ 0 := (coeff_reverseSpecialize P w d).trans_ne (havoid w hw)
  have hQ : Q ≠ 0 := fun h => hQd (h ▸ Polynomial.coeff_zero _)
  have hdeg : Q.natDegree = d := (hle w).antisymm (Polynomial.le_natDegree_of_ne_zero hQd)
  have hld : Q.leadingCoeff = D.eval w := by
    change Q.coeff Q.natDegree = D.eval w
    rw [hdeg]
    exact coeff_reverseSpecialize P w d
  have hqroot : Q.IsRoot a := (reverseSpecialize_eval P a w).trans hroot
  have hF₀ : 0 ≤ F w := Finset.sum_nonneg fun _ _ => div_nonneg (norm_nonneg _) (norm_nonneg _)
  have hsup : (Finset.range Q.natDegree).sup (fun k => ‖Q.coeff k‖₊) / ‖Q.leadingCoeff‖₊ ≤
      ⟨F w, hF₀⟩ := by
    rw [div_le_iff₀ (nnnorm_pos.mpr (Polynomial.leadingCoeff_ne_zero.mpr hQ))]
    apply Finset.sup_le
    intro k hk
    change ‖Q.coeff k‖ ≤ F w * ‖Q.leadingCoeff‖
    apply (div_le_iff₀ (norm_pos_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hQ))).mp
    rw [hld, coeff_reverseSpecialize]
    apply Finset.single_le_sum (f := fun k => ‖(reverseCoeff P k).eval w‖ / ‖D.eval w‖)
      (fun i _ => div_nonneg (norm_nonneg _) (norm_nonneg _))
    apply Finset.mem_range.mpr
    have hk' := Finset.mem_range.mp hk
    omega
  have hb : Q.cauchyBound ≤ ⟨F w, hF₀⟩ + 1 := add_le_add_right hsup 1
  have hra : ‖a‖ ≤ F w + 1 := by
    exact ((hqroot.norm_lt_cauchyBound hQ).le.trans hb : ‖a‖₊ ≤ _)
  exact hra.trans (add_le_add_right (hC ⟨w, hw, rfl⟩) _)

/-- A coordinate different from the original finite projection is proper
over the complement of one finite subset of its own parameter line. -/
theorem affine_varying_coordinate_proper_off_finite
    {σ : Type*} [Fintype σ] (Q : Ideal (MvPolynomial σ ℂ)) [Q.IsPrime]
    (f : Polynomial ℂ →ₐ[ℂ] (MvPolynomial σ ℂ ⧸ Q)) (hf : f.Finite)
    (hfi : Function.Injective f) (t g : MvPolynomial σ ℂ)
    (ht : Ideal.Quotient.mk Q t = f Polynomial.X) :
    ∃ E : Set ℂ, E.Finite ∧ ∀ K : Set ℂ, IsCompact K → K ⊆ Eᶜ →
      IsCompact ((fun x : zeroLocus Q => eval x.val g) ⁻¹' K) := by
  obtain ⟨P, hP, hplane⟩ := exists_monic_plane_image_of_finite_projection Q f hf hfi t g ht
  obtain ⟨D, hD, hbound⟩ := exists_uniform_reverse_specialization_bound P hP.ne_zero
  let E : Set ℂ := {w | D.IsRoot w}
  refine ⟨E, Polynomial.finite_setOf_isRoot hD, fun K hK hgood => ?_⟩
  obtain ⟨R, hR⟩ := hbound K hK (fun w hw => hgood hw)
  apply Subtype.isCompact_iff.mpr
  have heq : Subtype.val '' ((fun x : zeroLocus Q => eval x.val g) ⁻¹' K) =
      {x : σ → ℂ | x ∈ zeroLocus Q ∧ eval x g ∈ K} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.property, hy⟩
    · intro hx
      exact ⟨⟨x,hx.1⟩, hx.2, rfl⟩
  rw [heq]
  have hc : IsCompact {x : σ → ℂ | x ∈ zeroLocus Q ∧ eval x t ∈ Metric.closedBall 0 R} :=
    isCompact_affine_finite_projection_over_compact Q f hf t ht (isCompact_closedBall _ _)
  have hsub : {x : σ → ℂ | x ∈ zeroLocus Q ∧ eval x g ∈ K} =
      {x : σ → ℂ | x ∈ zeroLocus Q ∧ eval x t ∈ Metric.closedBall 0 R} ∩ (fun x => eval x g) ⁻¹' K := by
    ext x
    constructor
    · rintro ⟨hx, hg⟩
      have hroot := (hplane (eval x t) (eval x g)).mpr ⟨x, hx, rfl, rfl⟩
      have hab := hR (eval x t) (eval x g) hg hroot
      exact ⟨⟨hx, by simpa [Metric.mem_closedBall, dist_zero_right] using hab⟩, hg⟩
    · rintro ⟨⟨hx, _⟩, hg⟩
      exact ⟨hx, hg⟩
  rw [hsub]
  exact hc.inter_right (hK.isClosed.preimage g.continuous_eval)


/-- Every fiber of a varying polynomial coordinate on a prime finite
affine curve is finite, even over the exceptional values of properness. -/
theorem finite_points_over_varying_affine_coordinate
    {σ : Type*} [Fintype σ] (Q : Ideal (MvPolynomial σ ℂ)) [Q.IsPrime]
    (f : Polynomial ℂ →ₐ[ℂ] (MvPolynomial σ ℂ ⧸ Q)) (hf : f.Finite)
    (hfi : Function.Injective f) (t g : MvPolynomial σ ℂ)
    (ht : Ideal.Quotient.mk Q t = f Polynomial.X)
    (hvar : ∃ x y : zeroLocus Q, eval x.val g ≠ eval y.val g)
    (b : ℂ) : Set.Finite {x : zeroLocus Q | eval x.val g = b} := by
  classical
  obtain ⟨P, hP, hi, hplane⟩ :=
    exists_monic_irreducible_plane_image_of_finite_projection Q f hf hfi t g ht
  have hR : reverseSpecialize P b ≠ 0 := by
    intro hz
    have hv : P.eval (Polynomial.C b) = 0 := by
      rw [← hz, Polynomial.eval_eq_sum_range, reverseSpecialize]
      exact Finset.sum_congr rfl fun j _ => by rw [map_pow, mul_comm]
    let L : Polynomial (Polynomial ℂ) := Polynomial.X - Polynomial.C (Polynomial.C b)
    have hL : L ∣ P := Polynomial.dvd_iff_isRoot.mpr hv
    have hass : Associated L P := by
      apply Classical.byContradiction
      intro h
      exact (Polynomial.not_isUnit_X_sub_C _) ((hi.isUnit_iff_not_associated_of_dvd hL).2 (fun h' => h h'.symm))
    have hEq : L = P := Polynomial.eq_of_monic_of_associated (Polynomial.monic_X_sub_C _) hP hass
    have hg (x : zeroLocus Q) : eval x.val g = b := by
      have he := (hplane (eval x.val t) (eval x.val g)).2 ⟨x.val, x.property, rfl, rfl⟩
      rw [← hEq] at he
      simpa [L, Polynomial.IsRoot, sub_eq_zero] using he
    obtain ⟨x,y,hn⟩ := hvar
    exact hn ((hg x).trans (hg y).symm)
  have hsub : {x : zeroLocus Q | eval x.val g = b} ⊆
      ⋃ a ∈ {a : ℂ | (reverseSpecialize P b).IsRoot a}, {x : zeroLocus Q | eval x.val t = a} := by
    intro x hx
    refine Set.mem_iUnion₂.mpr ⟨eval x.val t, ?_, rfl⟩
    change eval x.val g = b at hx
    have he := (hplane (eval x.val t) (eval x.val g)).2 ⟨x.val, x.property, rfl, rfl⟩
    change (P.map (Polynomial.evalRingHom (eval x.val t))).eval (eval x.val g) = 0 at he
    rw [hx, ← reverseSpecialize_eval] at he
    exact he
  apply Set.Finite.subset ?_ hsub
  apply Set.Finite.biUnion (Polynomial.finite_setOf_isRoot hR)
  intro a _
  apply Set.Finite.of_finite_image (f := Subtype.val) ?_ Subtype.val_injective.injOn
  apply (finite_points_over_finite_projection Q f hf t ht a).subset
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x.property, hx⟩

/-- Removing finitely many values of the varying coordinate is dense even
at singular points of the original curve. A strict contact witness can
therefore enter the regular gap cover without changing its contact data. -/
theorem dense_affine_varying_coordinate_off_finite
    {σ : Type*} [Fintype σ] (Q : Ideal (MvPolynomial σ ℂ)) [Q.IsPrime]
    (f : Polynomial ℂ →ₐ[ℂ] (MvPolynomial σ ℂ ⧸ Q)) (hf : f.Finite)
    (hfi : Function.Injective f) (t g : MvPolynomial σ ℂ)
    (ht : Ideal.Quotient.mk Q t = f Polynomial.X)
    (hvar : ∃ x y : zeroLocus Q, eval x.val g ≠ eval y.val g)
    {S : Set ℂ} (hS : S.Finite) :
    Dense {x : zeroLocus Q | eval x.val g ∈ Sᶜ} := by
  let T := (fun x : zeroLocus Q => eval x.val t) ''
    ⋃ b ∈ S, {x : zeroLocus Q | eval x.val g = b}
  have hT : T.Finite := (hS.biUnion (fun b _ =>
    finite_points_over_varying_affine_coordinate Q f hf hfi t g ht hvar b)).image _
  apply (dense_affine_finite_projection_off_finite Q f hf hfi t ht hT).mono
  intro x hx h
  exact hx ⟨x, Set.mem_iUnion₂.mpr ⟨eval x.val g, h, rfl⟩, rfl⟩

end MOC
