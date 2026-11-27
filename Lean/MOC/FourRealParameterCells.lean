import MOC.FourRealParameterFacetCertificate
import MOC.FourRealParameterPolygonCertificate
import MOC.FourRealParameterBandCertificate
import MOC.FourRealParameterSignCertificate

/-! Compact polygon certificates for the order-four real-parameter family.
Each rational band selects a polygon by the sign of one polynomial. -/

set_option Elab.async false

open BigOperators Matrix Polynomial
open scoped Polynomial MOC.RealParameterCertificate.Univariate
open MOC.RealParameterCertificate (Univariate)

namespace MOC

open MOC.FourRealParameterCellCertificate

private theorem compactGuardReal_nonzero (i : Fin 173) :
    compactGuardReal (compactBandData i) ≠ 0 := by
  obtain ⟨j, hj⟩ := (compactBand_check i false).2.2
  intro h
  have hc := congrArg (fun p : ℝ[X] => p.coeff j.val) h
  simp only [compactGuardReal, Polynomial.finset_sum_coeff, Polynomial.coeff_monomial,
    Fin.val_inj, Finset.sum_ite_eq', Finset.mem_univ, if_true, Polynomial.coeff_zero] at hc
  exact hj (by exact_mod_cast hc)

private def compactCellCuts : Set ℝ :=
  ((Set.range fun i : Fin 173 => ((compactBandData i).left : ℝ)) ∪
    (Set.range fun i : Fin 173 => ((compactBandData i).right : ℝ))) ∪
    ⋃ i : Fin 173, {x : ℝ | (compactGuardReal (compactBandData i)).IsRoot x}

private theorem compactCellCuts_finite : compactCellCuts.Finite :=
  ((Set.finite_range _).union (Set.finite_range _)).union
    (Set.finite_iUnion fun i => Polynomial.finite_setOf_isRoot (compactGuardReal_nonzero i))

private theorem exists_compactBand (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1)
    (hcut : x ∉ compactCellCuts) :
    ∃ i : Fin 173, ((compactBandData i).left : ℝ) < x ∧ x < ((compactBandData i).right : ℝ) := by
  let S : Finset (Fin 173) := Finset.univ.filter fun i => ((compactBandData i).left : ℝ) < x
  have hzero : (0 : Fin 173) ∈ S := by simpa [S, compactBand_zero] using hx0
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image S Fin.val ⟨0, hzero⟩
  have hleft : ((compactBandData i).left : ℝ) < x := (Finset.mem_filter.mp hi).2
  refine ⟨i, hleft, ?_⟩
  by_contra h
  have hright : ((compactBandData i).right : ℝ) < x := by
    refine lt_of_le_of_ne (le_of_not_gt h) ?_
    intro he
    exact hcut (Or.inl (Or.inr ⟨i, he⟩))
  have hi172 : i.val < 172 := by
    by_contra hlarge
    have hlast : i = (172 : Fin 173) := Fin.ext (by omega)
    rw [hlast, compactBand_one, Rat.cast_one] at hright
    exact (lt_asymm hright hx1).elim
  let j : Fin 172 := ⟨i.val, hi172⟩
  have e : j.castSucc = i := Fin.ext rfl
  have hnext : j.succ ∈ S := by
    have he : ((compactBandData j.castSucc).right : ℝ) =
        ((compactBandData j.succ).left : ℝ) :=
      congrArg (fun q : ℚ => (q : ℝ)) (compactBands_adjacent j)
    rw [e] at he
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [← he]
    exact hright
  have he := hmax j.succ hnext
  change i.val + 1 ≤ i.val at he
  omega

private theorem compactGuard_eval_ne (x : ℝ) (hcut : x ∉ compactCellCuts) (i : Fin 173) :
    cellEval x (compactGuardPolynomial (compactBandData i)) ≠ 0 := by
  intro h
  apply hcut
  right
  apply Set.mem_iUnion.mpr
  refine ⟨i, ?_⟩
  change (compactGuardReal (compactBandData i)).eval x = 0
  simpa only [compactGuardReal, Polynomial.eval_finset_sum, Polynomial.eval_monomial,
    compactGuardPolynomial, cellEval_quartic, mul_comm] using h

set_option maxHeartbeats 1000000 in
private theorem compactMinorChart (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1)
    (hcut : x ∉ compactCellCuts) : Nonempty (FourRealParameterMinorChart x) := by
  obtain ⟨j, hl, hr⟩ := exists_compactBand x hx0 hx1 hcut
  let b := compactBandData j
  let g := cellEval x (compactGuardPolynomial b)
  let negative := decide (g < 0)
  have hg : if negative then g < 0 else 0 < g := by
    dsimp only [negative]
    by_cases h : g < 0
    · simpa [h]
    · have hpos : 0 < g :=
        lt_of_le_of_ne (le_of_not_gt h) (compactGuard_eval_ne x hcut j).symm
      simpa [h] using hpos
  obtain ⟨hd, hindex, _⟩ := compactBand_check j negative
  let k : Fin 89 := ⟨b.chart negative, hindex⟩
  let p := compactPolygon k.val
  have facts := compactPolygon_check k
  have hsign := compactBand_signs j negative
  have hfactor (w : CellWeight) (hw : compactWeightValid b negative w = true) :
      ∀ f ∈ w.signed, 0 < cellEval x (cellQuartic (signedFactorQuartic compactFactorData f)) := by
    intro f hf
    have hvalid : cellFactorValid compactFactorData b negative f :=
      of_decide_eq_true (List.all_eq_true.mp hw f hf)
    exact cellFactor_positive compactFactorData b negative f x hd hl hr hg hvalid
  refine ⟨{
    vertices := p.size
    vertices_pos := facts.1
    label := fun i => (fourPerm (p.label i)).symm
    prev := p.prev
    next := p.next
    incident := fun i => (facts.2 i).1
    terms := 12
    rows := fun i t => ((compactFacet (p.facets i)).terms t).rows
    columns := fun i t => ((compactFacet (p.facets i)).terms t).columns
    weights := fun i t => cellEval x (cellWeightPolynomial compactFactorData ((compactFacet (p.facets i)).terms t).weight)
    weights_nonneg := ?_
    turn_pos := ?_
    edge_identity := ?_ }⟩
  · intro i t
    exact cellWeight_nonneg compactFactorData _ x (hfactor _ ((hsign i).2 t))
  · intro i
    obtain ⟨_, _, _, _, hc, hsq, hid⟩ := facts.2 i
    have ht := cellWeight_positive compactFactorData (p.turns i) x hc hsq (hfactor _ ((hsign i).1))
    have heq : cellEval x (compactTurnPolynomial p i) =
        cellEval x (cellWeightPolynomial compactFactorData (p.turns i)) :=
      Univariate.eval_eq x hid
    have hturn : 0 < cellEval x (compactTurnPolynomial p i) := ht.trans_eq heq.symm
    simpa only [compactTurnPolynomial, cellPlaneCross_eval, cellPlaneEval_sub,
      compactVertexByIndex, cellVertex_eval x hx1] using hturn
  · intro i σ
    obtain ⟨_, hidx, hlab, hrab, _⟩ := facts.2 i
    change (compactFacet (p.facets i)).left = p.label i at hlab
    change (compactFacet (p.facets i)).right = p.label (p.next i) at hrab
    have he := compactFacet_check x ⟨p.facets i, hidx⟩ σ
    simp only [Fin.val_mk, compactFacetPolynomial, hlab, hrab, cellPlaneCross_eval, cellPlaneEval_sub,
      compactVertexByIndex, cellVertex_eval x hx1, compactFacetMinorPolynomial,
      Univariate.eval_sum, apply_ite, Univariate.eval_zero] at he
    exact he

/-- Every real parameter in the order-four family satisfies the matching
hull inclusion for every relative unitary. -/
theorem holds_fourRealParameter_all (t : ℝ) (U : Matrix (Fin 4) (Fin 4) ℂ)
    (hU : IsUnitary U) : Holds (fourRealParameterLeft t) fourRealParameterRight U :=
  holds_fourRealParameter_of_compact_minor_cells compactCellCuts compactCellCuts_finite
    compactMinorChart t U hU

end MOC
