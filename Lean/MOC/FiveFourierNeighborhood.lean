import MOC.FourierProfiles
import Mathlib.Analysis.CStarAlgebra.Matrix

/-! The positive order-five Fourier law persists on an open ball of
unitary mixers by correcting its signed permutation weights. -/

open BigOperators Finset Filter Matrix
open scoped Matrix.L2OpNorm Topology

namespace MOC

noncomputable section

private theorem continuousAt_realSignedWeight {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : Matrix ι ι ℂ) (hF : IsUnitary F) (σ : Equiv.Perm ι) :
    ContinuousAt (fun U => realSignedWeight U σ) F := by
  have hterm : Continuous (fun U : Matrix ι ι ℂ => leibnizTerm U σ) := by
    unfold leibnizTerm
    exact continuous_const.mul
      (continuous_finset_prod _ fun j _ => continuous_id.matrix_elem (σ j) j)
  exact Complex.continuous_re.continuousAt.comp
    (hterm.continuousAt.div continuous_id.matrix_det.continuousAt
      (det_ne_zero_of_unitary hF))

/-- Every unitary in some operator-norm ball about the normalized order-five Fourier
matrix has a common probability law for all squared minors. Each of the 120
permutations receives at least half the weight floor at the center. -/
theorem cyclicFourier_five_minor_law_on_ball :
    ∃ ε : ℝ, 0 < ε ∧ ∀ U : Matrix (ZMod 5) (ZMod 5) ℂ, IsUnitary U →
      dist U (cyclicFourier 5) < ε →
      ∃ w : Equiv.Perm (ZMod 5) → ℝ, (∀ σ, fourierFiveWeightFloor / 2 ≤ w σ) ∧
        (∑ σ, w σ) = 1 ∧
        ∀ I J : Finset (ZMod 5), subsetMinorSq U I J =
          ∑ σ ∈ univ.filter (fun σ => J.map σ.toEmbedding = I), w σ := by
  classical
  let F := cyclicFourier 5
  have hF : IsUnitary F := cyclicFourier_unitary 5
  obtain ⟨w, hw, hsum, hminor⟩ := cyclicFourier_five_positive_minor_law
  let c (U : Matrix (ZMod 5) (ZMod 5) ℂ) (σ : Equiv.Perm (ZMod 5)) :=
    w σ + realSignedWeight U σ - realSignedWeight F σ
  have hfloor (σ : Equiv.Perm (ZMod 5)) :
      ∀ᶠ U in 𝓝 F, fourierFiveWeightFloor / 2 < c U σ := by
    have hc : ContinuousAt (fun U => c U σ) F :=
      (continuousAt_const.add (continuousAt_realSignedWeight F hF σ)).sub continuousAt_const
    have hcenter : fourierFiveWeightFloor / 2 < c F σ := by
      rw [show c F σ = w σ by exact add_sub_cancel_right _ _]
      exact (half_lt_self fourierFiveWeightFloor_pos).trans_le (hw σ)
    exact hc.eventually (lt_mem_nhds hcenter)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (Filter.eventually_all.mpr hfloor)
  refine ⟨ε, hε, fun U hU hdist => ⟨c U, fun σ => (hball hdist σ).le, ?_, ?_⟩⟩
  · rw [show (∑ σ, c U σ) = (∑ σ, w σ) + (∑ σ, realSignedWeight U σ) -
        (∑ σ, realSignedWeight F σ) by simp only [c, Finset.sum_sub_distrib, Finset.sum_add_distrib],
      hsum, sum_realSignedWeight U hU, sum_realSignedWeight F hF, add_sub_cancel_right]
  · intro I J
    have hreal (V : Matrix (ZMod 5) (ZMod 5) ℂ) (hV : IsUnitary V) :
        (∑ σ ∈ univ.filter (fun σ => J.map σ.toEmbedding = I), realSignedWeight V σ) =
          subsetMinorSq V I J := by
      simpa only [Complex.re_sum, Complex.ofReal_re, realSignedWeight] using
        congrArg Complex.re (sum_signedWeight_image_eq_subsetMinorSq V hV I J)
    have hcenter : subsetMinorSq F I J =
        (∑ σ ∈ univ.filter (fun σ => J.map σ.toEmbedding = I), w σ) := hminor I J
    simp only [c, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← hcenter, hreal U hU, hreal F hF]
    rw [add_comm, add_sub_cancel_right]

/-- An open ball of order-five unitary mixers satisfies determinant inclusion
for every pair of complex spectra. -/
theorem holds_on_cyclicFourier_five_ball :
    ∃ ε : ℝ, 0 < ε ∧ ∀ U : Matrix (ZMod 5) (ZMod 5) ℂ, IsUnitary U →
      dist U (cyclicFourier 5) < ε → ∀ a b : ZMod 5 → ℂ, Holds a b U := by
  obtain ⟨ε, hε, hball⟩ := cyclicFourier_five_minor_law_on_ball
  refine ⟨ε, hε, fun U hU hdist a b => ?_⟩
  obtain ⟨w, hw, hsum, hminor⟩ := hball U hU hdist
  exact holds_of_indexed_minor_law a b U hU id w
    (fun σ => (half_pos fourierFiveWeightFloor_pos).le.trans (hw σ)) hsum hminor

end

end MOC
