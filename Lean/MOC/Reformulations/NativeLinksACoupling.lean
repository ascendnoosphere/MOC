import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

open MeasureTheory

namespace MOC.Reformulations

noncomputable section

/-- Couplings with the actual two pushforward marginals, not arbitrary
unitary conjugations of multiplication operators. -/
def additiveLogCouplingValues (μ ν : Measure ℝ) : Set ℝ :=
  {z | ∃ γ : Measure (ℝ × ℝ), γ.map Prod.fst = μ ∧ γ.map Prod.snd = ν ∧
    z = Real.exp (∫ p, Real.log (p.1 + p.2) ∂γ)}

/-- For two real measurable functions, the determinant defined by the integral of the
logarithm is itself a coupling value: use the joint law of the two
functions. This works on any measure space, not just on a finite lift. -/
theorem commutativeLogDet_mem_couplings {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (f g : X → ℝ) (hf : Measurable f) (hg : Measurable g) :
    Real.exp (∫ x, Real.log (f x + g x) ∂ν) ∈
      additiveLogCouplingValues (ν.map f) (ν.map g) := by
  let F : X → ℝ × ℝ := fun x => (f x, g x)
  have hF : Measurable F := hf.prodMk hg
  refine ⟨ν.map F, Measure.map_map measurable_fst hF, Measure.map_map measurable_snd hF, ?_⟩
  have hm : Measurable (fun p : ℝ × ℝ => Real.log (p.1 + p.2)) :=
    Real.measurable_log.comp (measurable_fst.add measurable_snd)
  rw [integral_map hF.aemeasurable hm.aestronglyMeasurable]

/-- The native comparison with the extrema, whenever the extremal
coupling values are bounded. -/
theorem commutativeLogDet_bounds {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (f g : X → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hl : BddBelow (additiveLogCouplingValues (ν.map f) (ν.map g)))
    (hu : BddAbove (additiveLogCouplingValues (ν.map f) (ν.map g))) :
    sInf (additiveLogCouplingValues (ν.map f) (ν.map g)) ≤
      Real.exp (∫ x, Real.log (f x + g x) ∂ν) ∧
    Real.exp (∫ x, Real.log (f x + g x) ∂ν) ≤
      sSup (additiveLogCouplingValues (ν.map f) (ν.map g)) :=
  ⟨csInf_le hl (commutativeLogDet_mem_couplings ν f g hf hg),
    le_csSup hu (commutativeLogDet_mem_couplings ν f g hf hg)⟩

end

end MOC.Reformulations
