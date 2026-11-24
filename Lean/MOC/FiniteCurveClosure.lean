import MOC.FiniteCurveBranchValues
import Mathlib.Topology.Algebra.Polynomial

/-! The whole finite plane curve is the closure of its simple-root cover. -/

open Filter Set Polynomial
open scoped BigOperators Topology

namespace MOC

private theorem continuous_specialized_plane_eval (P : ℂ[X][X]) :
    Continuous (fun p : ℂ × ℂ => (P.map (evalRingHom p.1)).eval p.2) := by
  have he (p : ℂ × ℂ) :
      (P.map (evalRingHom p.1)).eval p.2 =
        ∑ k ∈ Finset.range (P.natDegree + 1), (P.coeff k).eval p.1 * p.2 ^ k := by
    rw [Polynomial.eval_map, Polynomial.eval₂_eq_sum_range]
    rfl
  rw [funext he]
  exact continuous_finset_sum _ fun k _ =>
    ((P.coeff k).continuous.comp continuous_fst).mul (continuous_snd.pow k)

/-- Every plane root, including a root over an exceptional value, is
approximated by roots over the regular base. Otherwise evaluating at that
root would have a positive lower bound from the product over nearby roots. -/
theorem closure_simple_root_cover_eq_plane_curve
    (P : ℂ[X][X]) (hP : P.Monic) {S : Set ℂ} (hS : S.Finite)
    (hsep : ∀ z ∈ Sᶜ, (P.map (evalRingHom z)).Separable) :
    closure {p : ℂ × ℂ | p.1 ∈ Sᶜ ∧ (P.map (evalRingHom p.1)).IsRoot p.2} =
      {p : ℂ × ℂ | (P.map (evalRingHom p.1)).IsRoot p.2} := by
  classical
  apply Set.Subset.antisymm
  · have hc : IsClosed {p : ℂ × ℂ | (P.map (evalRingHom p.1)).IsRoot p.2} :=
      isClosed_eq (continuous_specialized_plane_eval P) continuous_const
    exact hc.closure_subset_iff.mpr (fun _ hp => hp.2)
  · rintro ⟨z₀,w₀⟩ h₀
    change (P.map (evalRingHom z₀)).eval w₀ = 0 at h₀
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    have hb : Continuous (fun z : ℂ => (P.map (evalRingHom z)).eval w₀) :=
      (continuous_specialized_plane_eval P).comp (continuous_id.prodMk continuous_const)
    have hsmall : ∀ᶠ z in 𝓝 z₀,
        ‖(P.map (evalRingHom z)).eval w₀‖ < ε ^ P.natDegree :=
      (isOpen_lt hb.norm continuous_const).mem_nhds (by
        change ‖(P.map (evalRingHom z₀)).eval w₀‖ < _
        rw [h₀, norm_zero]
        positivity)
    have hdense : Dense Sᶜ := hS.countable.dense_compl ℂ
    have hfreq : ∃ᶠ z in 𝓝 z₀, z ∈ Sᶜ := mem_closure_iff_frequently.mp (hdense z₀)
    have hdist : ∀ᶠ z in 𝓝 z₀, dist z₀ z < ε := by
      filter_upwards [Metric.ball_mem_nhds z₀ hε] with z hz
      exact (dist_comm _ _).trans_lt (Metric.mem_ball.mp hz)
    obtain ⟨z, hz, hval, hzdist⟩ := (hfreq.and_eventually (hsmall.and hdist)).exists
    let Q := P.map (evalRingHom z)
    have hm : Q.Monic := hP.map _
    let R := Q.roots.toFinset
    have hn : Q.roots.Nodup := Polynomial.nodup_roots (hsep z hz)
    have hcard : R.card = P.natDegree := by
      dsimp [R]
      rw [Multiset.toFinset_card_of_nodup hn,
        splits_iff_card_roots.mp (IsAlgClosed.splits Q), hP.natDegree_map]
    have hprod : Q.eval w₀ = ∏ w ∈ R, (w₀ - w) := by
      calc
        _ = (Q.roots.map (fun w => w₀ - w)).prod :=
          eval_eq_prod_roots_sub_of_monic_of_splits_id hm (IsAlgClosed.splits Q) w₀
        _ = _ := by
          change _ = ((Q.roots.toFinset.val).map (fun w => w₀ - w)).prod
          rw [Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hn]
    obtain ⟨w, hw, hwd⟩ : ∃ w ∈ R, dist w₀ w < ε := by
      apply Classical.byContradiction
      intro H
      have he : ε ^ P.natDegree ≤ ‖Q.eval w₀‖ := by
        rw [hprod, norm_prod, ← hcard, ← Finset.prod_const]
        apply Finset.prod_le_prod (fun _ _ => hε.le)
        intro w hw
        exact (not_lt.mp (fun h => H ⟨w, hw, h⟩)).trans_eq (dist_eq_norm _ _)
      exact (not_lt_of_ge he) hval
    have hr : Q.IsRoot w := (mem_roots hm.ne_zero).mp (Multiset.mem_toFinset.mp hw)
    exact ⟨(z,w), ⟨hz, hr⟩, by rw [Prod.dist_eq]; exact max_lt hzdist hwd⟩

/-- The full plane zero set of a monic irreducible polynomial is connected,
including all fibers where the specialized polynomial has a repeated root. -/
theorem isConnected_plane_curve_of_monic_irreducible
    (P : ℂ[X][X]) (hP : P.Monic) (hirr : Irreducible P) :
    IsConnected {p : ℂ × ℂ | (P.map (evalRingHom p.1)).IsRoot p.2} := by
  let S : Set ℂ := {z | ¬ (P.map (evalRingHom z)).Separable}
  have hS : S.Finite := finite_nonseparable_specializations_of_irreducible P hP hirr
  have hs : ∀ z ∈ Sᶜ, (P.map (evalRingHom z)).Separable := fun _ hz => not_not.mp hz
  rw [← closure_simple_root_cover_eq_plane_curve P hP hS hs]
  exact (isConnected_simple_root_cover_of_irreducible P hP hirr hS hs).closure

end MOC
