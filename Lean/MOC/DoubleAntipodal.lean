import MOC.DoubleAntipodalCertificate
import MOC.TwoValues

/-! A common law for two centrally symmetric complex spectra when the second
spectrum is twice the first. The certificate uses five matching products. -/

open BigOperators Matrix

namespace MOC

/-- Two pairs of opposite points in the complex plane. -/
def antipodalQuadruple (x y : ℂ) : Fin 4 → ℂ := ![x, -x, y, -y]

namespace DoubleAntipodalCertificate

noncomputable section

private def monomial (x y : ℂ) : Fin 5 → ℂ := ![x^4, x^3*y, x^2*y^2, x*y^3, y^4]

private theorem product_eq (x y : ℂ) (p : Label) :
    matchingProduct (antipodalQuadruple x y) (fun i => 2 * antipodalQuadruple x y i)
      (fourPerm p) = ∑ k, (coeff p k : ℂ) * monomial x y k := by
  fin_cases p <;> simp only [matchingProduct, Fin.prod_univ_four, Fin.sum_univ_succ,
    Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  · change (x + 2 * x) * ((-x) + 2 * (-x)) * (y + 2 * y) * ((-y) + 2 * (-y)) =
      ((0 : ℤ) : ℂ) * x^4 + (((0 : ℤ) : ℂ) * (x^3*y) + (((81 : ℤ) : ℂ) * (x^2*y^2) + (((0 : ℤ) : ℂ) * (x*y^3) + (((0 : ℤ) : ℂ) * y^4))))
    push_cast
    ring
  · change (x + 2 * x) * ((-x) + 2 * (-x)) * ((-y) + 2 * y) * (y + 2 * (-y)) =
      ((0 : ℤ) : ℂ) * x^4 + (((0 : ℤ) : ℂ) * (x^3*y) + (((9 : ℤ) : ℂ) * (x^2*y^2) + (((0 : ℤ) : ℂ) * (x*y^3) + (((0 : ℤ) : ℂ) * y^4))))
    push_cast
    ring
  · change (x + 2 * x) * (y + 2 * (-x)) * ((-x) + 2 * y) * ((-y) + 2 * (-y)) =
      ((0 : ℤ) : ℂ) * x^4 + (((-18 : ℤ) : ℂ) * (x^3*y) + (((45 : ℤ) : ℂ) * (x^2*y^2) + (((-18 : ℤ) : ℂ) * (x*y^3) + (((0 : ℤ) : ℂ) * y^4))))
    push_cast
    ring
  · change (x + 2 * x) * (y + 2 * (-x)) * ((-y) + 2 * y) * ((-x) + 2 * (-y)) =
      ((0 : ℤ) : ℂ) * x^4 + (((6 : ℤ) : ℂ) * (x^3*y) + (((9 : ℤ) : ℂ) * (x^2*y^2) + (((-6 : ℤ) : ℂ) * (x*y^3) + (((0 : ℤ) : ℂ) * y^4))))
    push_cast
    ring
  · change (x + 2 * x) * ((-y) + 2 * (-x)) * ((-x) + 2 * y) * (y + 2 * (-y)) =
      ((0 : ℤ) : ℂ) * x^4 + (((-6 : ℤ) : ℂ) * (x^3*y) + (((9 : ℤ) : ℂ) * (x^2*y^2) + (((6 : ℤ) : ℂ) * (x*y^3) + (((0 : ℤ) : ℂ) * y^4))))
    push_cast
    ring
  · change (x + 2 * x) * ((-y) + 2 * (-x)) * (y + 2 * y) * ((-x) + 2 * (-y)) =
      ((0 : ℤ) : ℂ) * x^4 + (((18 : ℤ) : ℂ) * (x^3*y) + (((45 : ℤ) : ℂ) * (x^2*y^2) + (((18 : ℤ) : ℂ) * (x*y^3) + (((0 : ℤ) : ℂ) * y^4))))
    push_cast
    ring
  · change ((-x) + 2 * x) * (x + 2 * (-x)) * (y + 2 * y) * ((-y) + 2 * (-y)) =
      ((0 : ℤ) : ℂ) * x^4 + (((0 : ℤ) : ℂ) * (x^3*y) + (((9 : ℤ) : ℂ) * (x^2*y^2) + (((0 : ℤ) : ℂ) * (x*y^3) + (((0 : ℤ) : ℂ) * y^4))))
    push_cast
    ring
  · change ((-x) + 2 * x) * (x + 2 * (-x)) * ((-y) + 2 * y) * (y + 2 * (-y)) =
      ((0 : ℤ) : ℂ) * x^4 + (((0 : ℤ) : ℂ) * (x^3*y) + (((1 : ℤ) : ℂ) * (x^2*y^2) + (((0 : ℤ) : ℂ) * (x*y^3) + (((0 : ℤ) : ℂ) * y^4))))
    push_cast
    ring
  · change ((-x) + 2 * x) * (y + 2 * (-x)) * (x + 2 * y) * ((-y) + 2 * (-y)) =
      ((0 : ℤ) : ℂ) * x^4 + (((6 : ℤ) : ℂ) * (x^3*y) + (((9 : ℤ) : ℂ) * (x^2*y^2) + (((-6 : ℤ) : ℂ) * (x*y^3) + (((0 : ℤ) : ℂ) * y^4))))
    push_cast
    ring
  · change ((-x) + 2 * x) * (y + 2 * (-x)) * ((-y) + 2 * y) * (x + 2 * (-y)) =
      ((0 : ℤ) : ℂ) * x^4 + (((-2 : ℤ) : ℂ) * (x^3*y) + (((5 : ℤ) : ℂ) * (x^2*y^2) + (((-2 : ℤ) : ℂ) * (x*y^3) + (((0 : ℤ) : ℂ) * y^4))))
    push_cast
    ring
  · change ((-x) + 2 * x) * ((-y) + 2 * (-x)) * (x + 2 * y) * (y + 2 * (-y)) =
      ((0 : ℤ) : ℂ) * x^4 + (((2 : ℤ) : ℂ) * (x^3*y) + (((5 : ℤ) : ℂ) * (x^2*y^2) + (((2 : ℤ) : ℂ) * (x*y^3) + (((0 : ℤ) : ℂ) * y^4))))
    push_cast
    ring
  · change ((-x) + 2 * x) * ((-y) + 2 * (-x)) * (y + 2 * y) * (x + 2 * (-y)) =
      ((0 : ℤ) : ℂ) * x^4 + (((-6 : ℤ) : ℂ) * (x^3*y) + (((9 : ℤ) : ℂ) * (x^2*y^2) + (((6 : ℤ) : ℂ) * (x*y^3) + (((0 : ℤ) : ℂ) * y^4))))
    push_cast
    ring
  · change (y + 2 * x) * (x + 2 * (-x)) * ((-x) + 2 * y) * ((-y) + 2 * (-y)) =
      ((0 : ℤ) : ℂ) * x^4 + (((-6 : ℤ) : ℂ) * (x^3*y) + (((9 : ℤ) : ℂ) * (x^2*y^2) + (((6 : ℤ) : ℂ) * (x*y^3) + (((0 : ℤ) : ℂ) * y^4))))
    push_cast
    ring
  · change (y + 2 * x) * (x + 2 * (-x)) * ((-y) + 2 * y) * ((-x) + 2 * (-y)) =
      ((0 : ℤ) : ℂ) * x^4 + (((2 : ℤ) : ℂ) * (x^3*y) + (((5 : ℤ) : ℂ) * (x^2*y^2) + (((2 : ℤ) : ℂ) * (x*y^3) + (((0 : ℤ) : ℂ) * y^4))))
    push_cast
    ring
  · change (y + 2 * x) * ((-x) + 2 * (-x)) * (x + 2 * y) * ((-y) + 2 * (-y)) =
      ((0 : ℤ) : ℂ) * x^4 + (((18 : ℤ) : ℂ) * (x^3*y) + (((45 : ℤ) : ℂ) * (x^2*y^2) + (((18 : ℤ) : ℂ) * (x*y^3) + (((0 : ℤ) : ℂ) * y^4))))
    push_cast
    ring
  · change (y + 2 * x) * ((-x) + 2 * (-x)) * ((-y) + 2 * y) * (x + 2 * (-y)) =
      ((0 : ℤ) : ℂ) * x^4 + (((-6 : ℤ) : ℂ) * (x^3*y) + (((9 : ℤ) : ℂ) * (x^2*y^2) + (((6 : ℤ) : ℂ) * (x*y^3) + (((0 : ℤ) : ℂ) * y^4))))
    push_cast
    ring
  · change (y + 2 * x) * ((-y) + 2 * (-x)) * (x + 2 * y) * ((-x) + 2 * (-y)) =
      ((4 : ℤ) : ℂ) * x^4 + (((20 : ℤ) : ℂ) * (x^3*y) + (((33 : ℤ) : ℂ) * (x^2*y^2) + (((20 : ℤ) : ℂ) * (x*y^3) + (((4 : ℤ) : ℂ) * y^4))))
    push_cast
    ring
  · change (y + 2 * x) * ((-y) + 2 * (-x)) * ((-x) + 2 * y) * (x + 2 * (-y)) =
      ((4 : ℤ) : ℂ) * x^4 + (((-12 : ℤ) : ℂ) * (x^3*y) + (((1 : ℤ) : ℂ) * (x^2*y^2) + (((12 : ℤ) : ℂ) * (x*y^3) + (((4 : ℤ) : ℂ) * y^4))))
    push_cast
    ring
  · change ((-y) + 2 * x) * (x + 2 * (-x)) * ((-x) + 2 * y) * (y + 2 * (-y)) =
      ((0 : ℤ) : ℂ) * x^4 + (((-2 : ℤ) : ℂ) * (x^3*y) + (((5 : ℤ) : ℂ) * (x^2*y^2) + (((-2 : ℤ) : ℂ) * (x*y^3) + (((0 : ℤ) : ℂ) * y^4))))
    push_cast
    ring
  · change ((-y) + 2 * x) * (x + 2 * (-x)) * (y + 2 * y) * ((-x) + 2 * (-y)) =
      ((0 : ℤ) : ℂ) * x^4 + (((6 : ℤ) : ℂ) * (x^3*y) + (((9 : ℤ) : ℂ) * (x^2*y^2) + (((-6 : ℤ) : ℂ) * (x*y^3) + (((0 : ℤ) : ℂ) * y^4))))
    push_cast
    ring
  · change ((-y) + 2 * x) * ((-x) + 2 * (-x)) * (x + 2 * y) * (y + 2 * (-y)) =
      ((0 : ℤ) : ℂ) * x^4 + (((6 : ℤ) : ℂ) * (x^3*y) + (((9 : ℤ) : ℂ) * (x^2*y^2) + (((-6 : ℤ) : ℂ) * (x*y^3) + (((0 : ℤ) : ℂ) * y^4))))
    push_cast
    ring
  · change ((-y) + 2 * x) * ((-x) + 2 * (-x)) * (y + 2 * y) * (x + 2 * (-y)) =
      ((0 : ℤ) : ℂ) * x^4 + (((-18 : ℤ) : ℂ) * (x^3*y) + (((45 : ℤ) : ℂ) * (x^2*y^2) + (((-18 : ℤ) : ℂ) * (x*y^3) + (((0 : ℤ) : ℂ) * y^4))))
    push_cast
    ring
  · change ((-y) + 2 * x) * (y + 2 * (-x)) * (x + 2 * y) * ((-x) + 2 * (-y)) =
      ((4 : ℤ) : ℂ) * x^4 + (((12 : ℤ) : ℂ) * (x^3*y) + (((1 : ℤ) : ℂ) * (x^2*y^2) + (((-12 : ℤ) : ℂ) * (x*y^3) + (((4 : ℤ) : ℂ) * y^4))))
    push_cast
    ring
  · change ((-y) + 2 * x) * (y + 2 * (-x)) * ((-x) + 2 * y) * (x + 2 * (-y)) =
      ((4 : ℤ) : ℂ) * x^4 + (((-20 : ℤ) : ℂ) * (x^3*y) + (((33 : ℤ) : ℂ) * (x^2*y^2) + (((-20 : ℤ) : ℂ) * (x*y^3) + (((4 : ℤ) : ℂ) * y^4))))
    push_cast
    ring

private def mean (U : Matrix (Fin 4) (Fin 4) ℂ) : (Label → ℝ) →ₗ[ℝ] ℝ where
  toFun v := ∑ p, realSignedWeight U (fourPerm p) * v p
  map_add' v w := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' a v := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => mul_left_comm _ _ _

private def row (v : Label → ℤ) (p : Label) : ℝ := v p

private def event (I J : Finset (Fin 4)) (p : Label) : ℝ :=
  if J.map (fourPerm p).toEmbedding = I then 1 else 0

private theorem mean_event (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U)
    (I J : Finset (Fin 4)) : mean U (event I J) = subsetMinorSq U I J := by
  have h := congrArg Complex.re (sum_signedWeight_image_eq_subsetMinorSq U hU I J)
  have hm : (∑ σ : FourPerm, if J.map σ.toEmbedding = I then realSignedWeight U σ else 0) =
      subsetMinorSq U I J := by
    simpa only [Finset.sum_filter, Complex.re_sum, apply_ite, Complex.zero_re,
      Complex.ofReal_re, realSignedWeight] using h
  rw [← Equiv.sum_comp fourPermEquiv] at hm
  simpa only [mean, LinearMap.coe_mk, AddHom.coe_mk, event, mul_ite, mul_one, mul_zero,
    fourPermEquiv] using hm

private theorem mean_slack_nonneg (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U)
    (f : Facet) : 0 ≤ mean U (row (slack f)) := by
  have h : (facetDen f : ℝ) • row (slack f) =
      ∑ e : Term, ((term f e).2.2 : ℝ) • event (term f e).1 (term f e).2.1 := by
    funext p
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, row, event, mul_ite, mul_one, mul_zero]
    exact_mod_cast minor_decomposition f p
  have hh := congrArg (mean U) h
  simp only [map_smul, map_sum, smul_eq_mul, mean_event U hU] at hh
  have hpos : (0 : ℝ) < facetDen f := by exact_mod_cast facetDen_pos f
  apply nonneg_of_mul_nonneg_right _ hpos
  rw [hh]
  exact Finset.sum_nonneg fun e _ => mul_nonneg (by exact_mod_cast term_nonneg f e)
    (subsetMinorSq_nonneg _ _ _)

private theorem mean_bary_nonneg (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U)
    (t : Cell) (ht : ∀ s, mean U (row (liftValue s)) ≤ mean U (row (liftValue t)))
    (j : Fin 5) : 0 ≤ mean U (row (bary t j)) := by
  have h : (aScale t j : ℝ) • row (bary t j) =
      (bScale t j : ℝ) • (row (liftValue t) - row (liftValue (neighbor t j))) +
      (cScale t j : ℝ) • row (slack (face t j)) := by
    funext p
    simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul, row]
    exact_mod_cast transition t j p
  have hh := congrArg (mean U) h
  simp only [map_smul, map_add, map_sub, smul_eq_mul] at hh
  obtain ⟨ha, hb, hc⟩ := scales_ok t j
  have hpos : (0 : ℝ) < aScale t j := by exact_mod_cast ha
  apply nonneg_of_mul_nonneg_right _ hpos
  rw [hh]
  exact add_nonneg (mul_nonneg (by exact_mod_cast hb) (sub_nonneg.mpr (ht _)))
    (mul_nonneg (by exact_mod_cast hc) (mean_slack_nonneg U hU _))

private theorem row_match (x y : ℂ) (t : Cell) (p : Label) :
    let F := fun q => matchingProduct (antipodalQuadruple x y)
      (fun i => 2 * antipodalQuadruple x y i) (fourPerm q)
    ∑ j, (bary t j p : ℂ) * F (vertex t j) = (denominator t : ℂ) * F p := by
  dsimp only
  simp_rw [product_eq, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp_rw [← mul_assoc, ← Finset.sum_mul]
  congr 1
  exact_mod_cast reconstruct t p k

/-- At each unitary a single simplex gives a common law for all complex axes. -/
theorem exists_doubled_law (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    ∃ (σ : Fin 5 → FourPerm) (w : Fin 5 → ℝ), (∀ j, 0 ≤ w j) ∧ ∑ j, w j = 1 ∧
      ∀ x y : ℂ, ∑ j, (w j : ℂ) * matchingProduct (antipodalQuadruple x y)
        (fun i => 2 * antipodalQuadruple x y i) (σ j) =
          determinantValue (antipodalQuadruple x y) (fun i => 2 * antipodalQuadruple x y i) U := by
  classical
  obtain ⟨t, _, ht⟩ := Finset.exists_max_image Finset.univ
    (fun s : Cell => mean U (row (liftValue s))) ⟨0, Finset.mem_univ _⟩
  let w (j : Fin 5) := mean U (row (bary t j)) / (denominator t : ℝ)
  have hd : (0 : ℝ) < denominator t := by exact_mod_cast den_pos t
  have hm : ∑ p : Label, realSignedWeight U (fourPerm p) = 1 := by
    exact (Equiv.sum_comp fourPermEquiv (realSignedWeight U)).trans (sum_realSignedWeight U hU)
  refine ⟨fun j => fourPerm (vertex t j), w,
    fun j => div_nonneg (mean_bary_nonneg U hU t (fun s => ht s (Finset.mem_univ s)) j) hd.le,
    ?_, ?_⟩
  · change ∑ j, (∑ p, realSignedWeight U (fourPerm p) * (bary t j p : ℝ)) / _ = 1
    rw [← Finset.sum_div, div_eq_iff hd.ne', one_mul, Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    have hm' (p : Label) : ∑ j, (bary t j p : ℝ) = (denominator t : ℝ) := by
      exact_mod_cast bary_mass t p
    simp_rw [hm', ← Finset.sum_mul, hm, one_mul]
  · intro x y
    let F (p : Label) := matchingProduct (antipodalQuadruple x y)
      (fun i => 2 * antipodalQuadruple x y i) (fourPerm p)
    have hF : ∑ p : Label, (realSignedWeight U (fourPerm p) : ℂ) * F p =
        determinantValue (antipodalQuadruple x y) (fun i => 2 * antipodalQuadruple x y i) U := by
      exact (Equiv.sum_comp fourPermEquiv _).trans (real_signed_determinant _ _ U hU)
    rw [← hF]
    change ∑ j, (((∑ p, realSignedWeight U (fourPerm p) * (bary t j p : ℝ)) /
      (denominator t : ℝ) : ℝ) : ℂ) * F (vertex t j) = _
    push_cast
    have hd' : (denominator t : ℂ) ≠ 0 := by exact_mod_cast (den_pos t).ne'
    simp_rw [div_mul_eq_mul_div, ← Finset.sum_div]
    apply (div_eq_iff hd').mpr
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    simp_rw [mul_assoc, ← Finset.mul_sum]
    rw [show ∑ j, (bary t j p : ℂ) * F (vertex t j) = (denominator t : ℂ) * F p
      from row_match x y t p]
    ring

end
end DoubleAntipodalCertificate

/-- Doubling both antipodal pairs gives MOC for arbitrary complex axes and every unitary. -/
theorem holds_four_doubled_antipodal (x y : ℂ) (U : Matrix (Fin 4) (Fin 4) ℂ)
    (hU : IsUnitary U) : Holds (antipodalQuadruple x y) (fun i => 2 * antipodalQuadruple x y i) U := by
  obtain ⟨σ, w, hw, hsum, h⟩ := DoubleAntipodalCertificate.exists_doubled_law U hU
  unfold Holds
  refine mem_convexHull_of_exists_fintype w _ hw hsum (fun j => ⟨σ j, rfl⟩) ?_
  simpa only [Complex.real_smul] using h x y

end MOC
