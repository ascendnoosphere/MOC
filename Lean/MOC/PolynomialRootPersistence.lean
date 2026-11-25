import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! A root of a monic complex polynomial persists under continuous
specialization, including when the initial root is multiple. -/

open Filter Polynomial Set
open scoped NNReal Topology

namespace MOC

/-- The value of a monic polynomial controls the distance to its nearest root. -/
theorem exists_root_nnnorm_sub_lt_of_eval_lt {p : ℂ[X]} (hp : p.Monic)
    {z : ℂ} {ε : ℝ≥0} (hε : ‖p.eval z‖₊ < ε ^ p.natDegree) :
    ∃ w : ℂ, p.eval w = 0 ∧ ‖z - w‖₊ < ε := by
  classical
  by_contra! h
  have hs := IsAlgClosed.splits p
  have hc : p.natDegree = p.roots.card := by
    simpa only [Polynomial.map_id] using Polynomial.natDegree_eq_card_roots hs
  let s := p.roots.map (fun w => ‖z - w‖₊)
  have hprod : ε ^ s.card ≤ s.prod := by
    apply Multiset.pow_card_le_prod
    intro a ha
    obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp ha
    exact h w ((Polynomial.mem_roots hp.ne_zero).mp hw)
  have heval : ‖p.eval z‖₊ = s.prod := by
    rw [Polynomial.eval_eq_prod_roots_sub_of_monic_of_splits_id hp hs]
    simpa only [s, Multiset.map_map, Function.comp_def] using
      (map_multiset_prod (nnnormHom : ℂ →*₀ ℝ≥0) (p.roots.map fun w => z - w))
  rw [heval, hc] at hε
  exact (not_lt_of_ge (by simpa only [s, Multiset.card_map] using hprod)) hε

/-- A root can be found in each chosen neighborhood for all sufficiently
nearby parameters. Continuity of evaluation at the initial root suffices. -/
theorem eventually_exists_root_mem_nhds {X : Type*} [TopologicalSpace X]
    (p : X → ℂ[X]) {x₀ : X} {z₀ : ℂ} {d : ℕ}
    (hm : ∀ x, (p x).Monic) (hd : ∀ x, (p x).natDegree = d)
    (hcont : ContinuousAt (fun x => (p x).eval z₀) x₀)
    (hroot : (p x₀).eval z₀ = 0) {V : Set ℂ} (hV : V ∈ 𝓝 z₀) :
    ∀ᶠ x in 𝓝 x₀, ∃ z ∈ V, (p x).eval z = 0 := by
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hV
  let ε : ℝ≥0 := ⟨r, hr.le⟩
  have hε : 0 < ε := hr
  have ht : ∀ᶠ x in 𝓝 x₀, ‖(p x).eval z₀‖₊ < ε ^ d :=
    (continuous_nnnorm.continuousAt.comp hcont) (Iio_mem_nhds (by
      change ‖(p x₀).eval z₀‖₊ < ε ^ d
      rw [hroot, nnnorm_zero]
      exact pow_pos hε d))
  filter_upwards [ht] with x hx
  rw [← hd x] at hx
  obtain ⟨z, hz, hzlt⟩ := exists_root_nnnorm_sub_lt_of_eval_lt (hm x) hx
  refine ⟨z, hsub ?_, hz⟩
  rw [Metric.mem_ball, dist_comm, dist_eq_norm]
  exact hzlt

end MOC
