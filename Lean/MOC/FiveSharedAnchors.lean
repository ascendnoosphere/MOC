import MOC.FiveSharedAnchorsCertificate
import MOC.CommonWeights
import MOC.TwoValues

/-! Four shared signed eigenvalues have harmonic cross ratio.
The two remaining complex eigenvalues vary independently. -/

open BigOperators Matrix

namespace MOC.FiveSharedAnchors

noncomputable section

/-- The first four marks are 0, 2, 3 and 6. -/
def left (x : ℂ) : Fin 5 → ℂ := Function.update (fun i => (firstMarks i : ℂ)) 4 x

/-- The first four entries are the negatives of the shared marks. -/
def right (y : ℂ) : Fin 5 → ℂ := Function.update (fun i => (secondMarks i : ℂ)) 4 y

private def basis (x y : ℂ) : Fin 5 → ℂ :=
  ![0, (1-x)*(1-y), (1-x)*y, x*(1-y), x*y]

private theorem corner_eq (p : Label) (x y : ℤ) :
    (corner p x y : ℂ) = matchingProduct (left x) (right y) p := by
  simp only [corner, matchingProduct, Int.cast_prod, Int.cast_add]
  apply Finset.prod_congr rfl
  intro j _
  by_cases h : p j = 4 <;> by_cases k : j = 4 <;> simp [left, right, h, k]

private theorem swap_product (a b : Fin 5 → ℂ) (p : Label) :
    matchingProduct b a p.symm = matchingProduct a b p := by
  rw [matchingProduct_inverse]
  simp [matchingProduct, add_comm]

private theorem product_eq (x y : ℂ) (p : Label) :
    matchingProduct (left x) (right y) p =
      ∑ k, (point p k : ℂ) * basis x y k := by
  have hu (v : ℂ) : matchingProduct (left x) (right v) p =
      matchingProduct (left 0) (right v) p +
      (matchingProduct (left 1) (right v) p - matchingProduct (left 0) (right v) p) * x := by
    have h := matching_update_interp (right v) (fun i => (firstMarks i : ℂ)) 4 p.symm x
    change matchingProduct (right v) (left x) p.symm =
      matchingProduct (right v) (left 0) p.symm +
      (matchingProduct (right v) (left 1) p.symm -
        matchingProduct (right v) (left 0) p.symm) * x at h
    simpa only [swap_product] using h
  have hy := matching_update_interp (left x) (fun i => (secondMarks i : ℂ)) 4 p y
  change matchingProduct (left x) (right y) p = matchingProduct (left x) (right 0) p +
    (matchingProduct (left x) (right 1) p - matchingProduct (left x) (right 0) p) * y at hy
  rw [hy, hu 0, hu 1]
  simp [Fin.sum_univ_succ, point, basis, corner_eq]
  ring

private def mean (U : Matrix (Fin 5) (Fin 5) ℂ) : (Label → ℝ) →ₗ[ℝ] ℝ where
  toFun v := ∑ p, realSignedWeight U p * v p
  map_add' v w := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' a v := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => mul_left_comm _ _ _

private def row (v : Label → ℤ) (p : Label) : ℝ := v p

private def event (I J : Finset (Fin 5)) (p : Label) : ℝ :=
  if J.map p.toEmbedding = I then 1 else 0

private theorem mean_event (U : Matrix (Fin 5) (Fin 5) ℂ) (hU : IsUnitary U)
    (I J : Finset (Fin 5)) : mean U (event I J) = subsetMinorSq U I J := by
  have h := congrArg Complex.re (sum_signedWeight_image_eq_subsetMinorSq U hU I J)
  have hm : (∑ σ : Label, if J.map σ.toEmbedding = I then realSignedWeight U σ else 0) =
      subsetMinorSq U I J := by
    simpa only [Finset.sum_filter, Complex.re_sum, apply_ite, Complex.zero_re,
      Complex.ofReal_re, realSignedWeight] using h
  simpa only [mean, LinearMap.coe_mk, AddHom.coe_mk, event, mul_ite, mul_one, mul_zero] using hm

private theorem mean_slack_nonneg (U : Matrix (Fin 5) (Fin 5) ℂ) (hU : IsUnitary U)
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

private theorem mean_bary_nonneg (U : Matrix (Fin 5) (Fin 5) ℂ) (hU : IsUnitary U)
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
    let F := fun q => matchingProduct (left x)
      (right y) (q)
    ∑ j, (bary t j p : ℂ) * F (vertex t j) = (denominator t : ℂ) * F p := by
  dsimp only
  simp_rw [product_eq, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp_rw [← mul_assoc, ← Finset.sum_mul]
  congr 1
  exact_mod_cast reconstruct t p k

/-- One probability law works for every pair of free entries at a fixed unitary. -/
theorem exists_common_law (U : Matrix (Fin 5) (Fin 5) ℂ) (hU : IsUnitary U) :
    ∃ (σ : Fin 5 → Label) (w : Fin 5 → ℝ), (∀ j, 0 ≤ w j) ∧ ∑ j, w j = 1 ∧
      ∀ x y : ℂ, ∑ j, (w j : ℂ) * matchingProduct (left x)
        (right y) (σ j) =
          determinantValue (left x) (right y) U := by
  classical
  obtain ⟨t, _, ht⟩ := Finset.exists_max_image Finset.univ
    (fun s : Cell => mean U (row (liftValue s))) ⟨0, Finset.mem_univ _⟩
  let w (j : Fin 5) := mean U (row (bary t j)) / (denominator t : ℝ)
  have hd : (0 : ℝ) < denominator t := by exact_mod_cast den_pos t
  have hm : ∑ p : Label, realSignedWeight U p = 1 := by
    exact sum_realSignedWeight U hU
  refine ⟨fun j => vertex t j, w,
    fun j => div_nonneg (mean_bary_nonneg U hU t (fun s => ht s (Finset.mem_univ s)) j) hd.le,
    ?_, ?_⟩
  · change ∑ j, (∑ p, realSignedWeight U p * (bary t j p : ℝ)) / _ = 1
    rw [← Finset.sum_div, div_eq_iff hd.ne', one_mul, Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    have hm' (p : Label) : ∑ j, (bary t j p : ℝ) = (denominator t : ℝ) := by
      exact_mod_cast bary_mass t p
    simp_rw [hm', ← Finset.sum_mul, hm, one_mul]
  · intro x y
    let F (p : Label) := matchingProduct (left x)
      (right y) p
    have hF : ∑ p : Label, (realSignedWeight U p : ℂ) * F p =
        determinantValue (left x) (right y) U := by
      exact real_signed_determinant _ _ U hU
    rw [← hF]
    change ∑ j, (((∑ p, realSignedWeight U p * (bary t j p : ℝ)) /
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

/-- Four shared harmonic marks give the determinant hull inclusion for all
relative unitaries and all choices of the last two eigenvalues. -/
theorem holds (x y : ℂ) (U : Matrix (Fin 5) (Fin 5) ℂ)
    (hU : IsUnitary U) : Holds (left x) (right y) U := by
  obtain ⟨σ, w, hw, hsum, h⟩ := exists_common_law U hU
  unfold Holds
  refine mem_convexHull_of_exists_fintype w _ hw hsum (fun j => ⟨σ j, rfl⟩) ?_
  simpa only [Complex.real_smul] using h x y

end
end MOC.FiveSharedAnchors
