import MOC.FiniteCurveFibers
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Polynomial.CauchyBound
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.MetricSpace.ProperSpace.Real

/-! A finite affine projection over the complex numbers keeps compact
parameter sets in compact subsets of the curve. -/

open Finset MvPolynomial Set
open scoped NNReal

namespace MOC

variable {σ : Type*}

private theorem isClosed_zeroLocus_complex (Q : Ideal (MvPolynomial σ ℂ)) :
    IsClosed (zeroLocus Q) := by
  have heq : zeroLocus Q = ⋂ p : Q, {z | eval z p.val = 0} := by
    ext z
    simp only [mem_zeroLocus_iff, mem_iInter, mem_setOf_eq, Subtype.forall]
  rw [heq]
  exact isClosed_iInter fun p => isClosed_eq (MvPolynomial.continuous_eval p.val) continuous_const

/-- The inverse image of a compact set under a finite complex affine
projection is compact. Monicity gives a uniform bound on each coordinate. -/
theorem isCompact_preimage_of_finite_curve_projection
    (Q : Ideal (MvPolynomial σ ℂ)) (f : Polynomial ℂ →ₐ[ℂ] (MvPolynomial σ ℂ ⧸ Q))
    (hf : f.Finite) (t : MvPolynomial σ ℂ) (ht : Ideal.Quotient.mk Q t = f Polynomial.X)
    {S : Set ℂ} (hS : IsCompact S) :
    IsCompact (zeroLocus Q ∩ (fun z => eval z t) ⁻¹' S) := by
  classical
  obtain ⟨P, hm, hP⟩ := exists_monic_coordinate_equations_of_finite_projection Q f hf t ht
  let bound (i : σ) (a : ℂ) : ℝ≥0 := 1 + ∑ j ∈ range (P i).natDegree, ‖((P i).coeff j).eval a‖₊
  have hcont (i : σ) : Continuous (bound i) := by
    apply continuous_const.add
    exact continuous_finset_sum _ fun j _ => continuous_nnnorm.comp ((P i).coeff j).continuous
  have hpt (i : σ) : ∃ M : ℝ≥0, ∀ a ∈ S, bound i a ≤ M := by
    obtain ⟨M, hM⟩ := hS.bddAbove_image (hcont i).continuousOn
    exact ⟨M, fun a ha => hM (mem_image_of_mem _ ha)⟩
  choose M hM using hpt
  let C := Set.pi Set.univ (fun i : σ => Metric.closedBall (0 : ℂ) (M i : ℝ))
  have hC : IsCompact C := isCompact_univ_pi fun i => isCompact_closedBall (0 : ℂ) (M i : ℝ)
  refine hC.of_isClosed_subset
    ((isClosed_zeroLocus_complex Q).inter (hS.isClosed.preimage (MvPolynomial.continuous_eval t))) ?_
  intro z hz
  refine Set.mem_pi.mpr fun i _ => ?_
  let p := (P i).map (Polynomial.evalRingHom (eval z t))
  have hp : p.Monic := (hm i).map _
  have hpd : p.natDegree = (P i).natDegree := (hm i).natDegree_map _
  have hb : p.cauchyBound ≤ bound i (eval z t) := by
    rw [Polynomial.cauchyBound, hp.leadingCoeff, nnnorm_one, div_one, hpd, add_comm]
    apply add_le_add_left
    refine Finset.sup_le fun j hj => ?_
    simp only [p, Polynomial.coeff_map, Polynomial.coe_evalRingHom]
    exact Finset.single_le_sum (f := fun k => ‖((P i).coeff k).eval (eval z t)‖₊)
      (fun _ _ => zero_le _) hj
  have hnorm : ‖z i‖₊ ≤ M i :=
    ((hP z hz.1 i).norm_lt_cauchyBound hp.ne_zero).le.trans (hb.trans (hM i _ hz.2))
  simpa only [Metric.mem_closedBall, dist_zero_right] using (NNReal.coe_le_coe.mpr hnorm)

end MOC
