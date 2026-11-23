import MOC.TwoValues

/-! A finite certificate transfers a signed permutation law to one simplex.
The simplex is selected at the largest lifting score for the given unitary. -/

open BigOperators Matrix

namespace MOC

structure LiftedSimplexGeometry (ι Label J Cell Facet : Type*) [Fintype J] where
  index : Label ≃ Equiv.Perm ι
  vertex : Cell → J → Label
  denominator : Cell → ℤ
  bary : Cell → J → Label → ℤ
  liftValue : Cell → Label → ℤ
  neighbor : Cell → J → Cell
  face : Cell → J → Facet
  aScale : Cell → J → ℤ
  bScale : Cell → J → ℤ
  cScale : Cell → J → ℤ
  slack : Facet → Label → ℤ
  den_pos : ∀ t, 0 < denominator t
  scales_ok : ∀ t j, 0 < aScale t j ∧ 0 ≤ bScale t j ∧ 0 ≤ cScale t j
  transition : ∀ t j p, aScale t j * bary t j p =
    bScale t j * (liftValue t p - liftValue (neighbor t j) p) + cScale t j * slack (face t j) p
  bary_mass : ∀ t p, ∑ j, bary t j p = denominator t

structure LiftedSimplexCertificate (ι Label J Cell Facet Term : Type*)
    [DecidableEq ι] [Fintype J] [Fintype Term] extends LiftedSimplexGeometry ι Label J Cell Facet where
  facetDen : Facet → ℤ
  term : Facet → Term → Finset ι × Finset ι × ℤ
  facetDen_pos : ∀ f, 0 < facetDen f
  term_nonneg : ∀ f e, 0 ≤ (term f e).2.2
  minor_decomposition : ∀ f p, facetDen f * slack f p = ∑ e : Term,
    if (term f e).2.1.map (index p).toEmbedding = (term f e).1 then (term f e).2.2 else 0

namespace LiftedSimplexCertificate
noncomputable section
variable {ι Label : Type*} [Fintype ι] [DecidableEq ι] [Fintype Label]
variable (index : Label ≃ Equiv.Perm ι)
def mean (U : Matrix (ι) (ι) ℂ) : (Label → ℝ) →ₗ[ℝ] ℝ where
  toFun v := ∑ p, realSignedWeight U (index p) * v p
  map_add' v w := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' a v := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => mul_left_comm _ _ _

def row (v : Label → ℤ) (p : Label) : ℝ := v p

private def event (I J : Finset (ι)) (p : Label) : ℝ :=
  if J.map (index p).toEmbedding = I then 1 else 0

private theorem mean_event (U : Matrix (ι) (ι) ℂ) (hU : IsUnitary U)
    (I J : Finset (ι)) : mean index U (event index I J) = subsetMinorSq U I J := by
  have h := congrArg Complex.re (sum_signedWeight_image_eq_subsetMinorSq U hU I J)
  have hm : (∑ σ : Equiv.Perm ι, if J.map σ.toEmbedding = I then realSignedWeight U σ else 0) =
      subsetMinorSq U I J := by
    simpa only [Finset.sum_filter, Complex.re_sum, apply_ite, Complex.zero_re,
      Complex.ofReal_re, realSignedWeight] using h
  rw [← Equiv.sum_comp index] at hm
  simpa only [mean, LinearMap.coe_mk, AddHom.coe_mk, event, mul_ite, mul_one, mul_zero] using hm

variable {Cell Facet Term J : Type*} [Fintype J] [Fintype Term]
variable (C : LiftedSimplexCertificate ι Label J Cell Facet Term)

private theorem mean_slack_nonneg (U : Matrix (ι) (ι) ℂ) (hU : IsUnitary U)
    (f : Facet) : 0 ≤ mean C.index U (row (C.slack f)) := by
  have h : (C.facetDen f : ℝ) • row (C.slack f) =
      ∑ e : Term, ((C.term f e).2.2 : ℝ) • event C.index (C.term f e).1 (C.term f e).2.1 := by
    funext p
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, row, event, mul_ite, mul_one, mul_zero]
    exact_mod_cast C.minor_decomposition f p
  have hh := congrArg (mean C.index U) h
  simp only [map_smul, map_sum, smul_eq_mul, mean_event C.index U hU] at hh
  have hpos : (0 : ℝ) < C.facetDen f := by exact_mod_cast C.facetDen_pos f
  apply nonneg_of_mul_nonneg_right _ hpos
  rw [hh]
  exact Finset.sum_nonneg fun e _ => mul_nonneg (by exact_mod_cast C.term_nonneg f e)
    (subsetMinorSq_nonneg _ _ _)

variable (G : LiftedSimplexGeometry ι Label J Cell Facet)

private theorem mean_bary_nonneg (U : Matrix (ι) (ι) ℂ) (hU : IsUnitary U)
    (hf : ∀ f, 0 ≤ mean G.index U (row (G.slack f)))
    (t : Cell) (ht : ∀ s, mean G.index U (row (G.liftValue s)) ≤ mean G.index U (row (G.liftValue t)))
    (j : J) : 0 ≤ mean G.index U (row (G.bary t j)) := by
  have h : (G.aScale t j : ℝ) • row (G.bary t j) =
      (G.bScale t j : ℝ) • (row (G.liftValue t) - row (G.liftValue (G.neighbor t j))) +
      (G.cScale t j : ℝ) • row (G.slack (G.face t j)) := by
    funext p
    simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul, row]
    exact_mod_cast G.transition t j p
  have hh := congrArg (mean G.index U) h
  simp only [map_smul, map_add, map_sub, smul_eq_mul] at hh
  obtain ⟨ha, hb, hc⟩ := G.scales_ok t j
  have hpos : (0 : ℝ) < G.aScale t j := by exact_mod_cast ha
  apply nonneg_of_mul_nonneg_right _ hpos
  rw [hh]
  exact add_nonneg (mul_nonneg (by exact_mod_cast hb) (sub_nonneg.mpr (ht _)))
    (mul_nonneg (by exact_mod_cast hc) (hf _))



/-- Select one simplex at a unitary. The weights apply to every complex
observable reproduced by the barycentric rows of that simplex. -/
theorem exists_law_of_nonneg [Fintype Cell] [Nonempty Cell] (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (hf : ∀ f, 0 ≤ mean G.index U (row (G.slack f))) :
    ∃ (t : Cell) (w : J → ℝ), (∀ j, 0 ≤ w j) ∧ ∑ j, w j = 1 ∧
      ∀ F : Label → ℂ, (∀ p, ∑ j, (G.bary t j p : ℂ) * F (G.vertex t j) =
        (G.denominator t : ℂ) * F p) →
        ∑ j, (w j : ℂ) * F (G.vertex t j) =
          ∑ p, (realSignedWeight U (G.index p) : ℂ) * F p := by
  classical
  obtain ⟨t, _, ht⟩ := Finset.exists_max_image Finset.univ
    (fun s : Cell => mean G.index U (row (G.liftValue s))) Finset.univ_nonempty
  let w (j : J) := mean G.index U (row (G.bary t j)) / (G.denominator t : ℝ)
  have hd : (0 : ℝ) < G.denominator t := by exact_mod_cast G.den_pos t
  have hm : ∑ p : Label, realSignedWeight U (G.index p) = 1 :=
    (Equiv.sum_comp G.index (realSignedWeight U)).trans (sum_realSignedWeight U hU)
  refine ⟨t, w, fun j => div_nonneg
    (mean_bary_nonneg G U hU hf t (fun s => ht s (Finset.mem_univ s)) j) hd.le, ?_, ?_⟩
  · change ∑ j, (∑ p, realSignedWeight U (G.index p) * (G.bary t j p : ℝ)) / _ = 1
    rw [← Finset.sum_div, div_eq_iff hd.ne', one_mul, Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    have hm' (p : Label) : ∑ j, (G.bary t j p : ℝ) = (G.denominator t : ℝ) := by
      exact_mod_cast G.bary_mass t p
    simp_rw [hm', ← Finset.sum_mul, hm, one_mul]
  · intro F hF
    change ∑ j, (((∑ p, realSignedWeight U (G.index p) * (G.bary t j p : ℝ)) /
      (G.denominator t : ℝ) : ℝ) : ℂ) * F (G.vertex t j) = _
    push_cast
    have hd' : (G.denominator t : ℂ) ≠ 0 := by exact_mod_cast (G.den_pos t).ne'
    simp_rw [div_mul_eq_mul_div, ← Finset.sum_div]
    apply (div_eq_iff hd').mpr
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    simp_rw [mul_assoc, ← Finset.mul_sum]
    rw [hF p]
    ring

/-- A decomposition into nonnegative squared minors gives the required boundary bounds. -/
theorem exists_law [Fintype Cell] [Nonempty Cell] (U : Matrix ι ι ℂ) (hU : IsUnitary U) :
    ∃ (t : Cell) (w : J → ℝ), (∀ j, 0 ≤ w j) ∧ ∑ j, w j = 1 ∧
      ∀ F : Label → ℂ, (∀ p, ∑ j, (C.bary t j p : ℂ) * F (C.vertex t j) =
        (C.denominator t : ℂ) * F p) →
        ∑ j, (w j : ℂ) * F (C.vertex t j) =
          ∑ p, (realSignedWeight U (C.index p) : ℂ) * F p :=
  exists_law_of_nonneg C.toLiftedSimplexGeometry U hU (mean_slack_nonneg C U hU)

end
end LiftedSimplexCertificate
end MOC
