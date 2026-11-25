import MOC.FiniteCurveCompactness
import MOC.FiniteCurvePlaneImage
import MOC.PolynomialRootPersistence
import Mathlib.Topology.Algebra.Module.Cardinality

/-! Nearby parameters lift near a chosen point even if it lies over a branch value. -/

open Filter Finset MvPolynomial Set
open scoped Topology

namespace MOC

variable {σ : Type*} [Fintype σ]

private theorem exists_polynomial_separating_point_from_finite_set
    {S : Set (σ → ℂ)} (hS : S.Finite) (z : σ → ℂ) :
    ∃ u : MvPolynomial σ ℂ, ∀ w ∈ S, eval w u = eval z u → w = z := by
  classical
  let W := S \ {z}
  have hwf : W.Finite := hS.subset Set.diff_subset
  letI : Fintype W := hwf.fintype
  have hdiff (w : W) : ∃ i, z i ≠ w.val i := by
    by_contra! h
    exact w.property.2 (mem_singleton_iff.mpr (funext h).symm)
  choose i hi using hdiff
  let u := ∏ w : W, X (i w) - C (w.val (i w))
  refine ⟨u, fun w hw hwu => ?_⟩
  by_contra hne
  let w' : W := ⟨w, hw, Set.not_mem_singleton_iff.mpr hne⟩
  have hz : eval z u ≠ 0 := by
    simp only [u, map_prod, map_sub, eval_X, eval_C]
    exact Finset.prod_ne_zero_iff.mpr fun v _ => sub_ne_zero.mpr (hi v)
  have hw' : eval w u = 0 := by
    simp only [u, map_prod, map_sub, eval_X, eval_C]
    exact Finset.prod_eq_zero (Finset.mem_univ w') (sub_self _)
  exact hz (hwu.symm.trans hw')

/-- A finite affine projection maps every open neighborhood of a point
onto a neighborhood of its projected value, allowing a multiple root at
the original point. -/
theorem eventually_lift_near_point_of_finite_projection
    (Q : Ideal (MvPolynomial σ ℂ)) [Q.IsPrime]
    (f : Polynomial ℂ →ₐ[ℂ] (MvPolynomial σ ℂ ⧸ Q)) (hf : f.Finite)
    (hfi : Function.Injective f)
    (t : MvPolynomial σ ℂ) (ht : Ideal.Quotient.mk Q t = f Polynomial.X)
    {z : σ → ℂ} (hz : z ∈ zeroLocus Q) {V : Set (σ → ℂ)} (hV : IsOpen V) (hzV : z ∈ V) :
    ∀ᶠ a in 𝓝 (eval z t), ∃ w ∈ V, w ∈ zeroLocus Q ∧ eval w t = a := by
  let a₀ := eval z t
  have hfiber := finite_points_over_finite_projection Q f hf t ht a₀
  obtain ⟨u, hu⟩ := exists_polynomial_separating_point_from_finite_set hfiber z
  let b₀ := eval z u
  let D := Metric.closedBall a₀ 1
  let E := (zeroLocus Q ∩ (fun w => eval w t) ⁻¹' D) ∩ Vᶜ
  let F : (σ → ℂ) → ℂ × ℂ := fun w => (eval w t, eval w u)
  have hE : IsCompact E :=
    (isCompact_preimage_of_finite_curve_projection Q f hf t ht (isCompact_closedBall a₀ 1)).inter_right
      hV.isClosed_compl
  have hF : IsCompact (F '' E) :=
    hE.image ((MvPolynomial.continuous_eval t).prodMk (MvPolynomial.continuous_eval u))
  have hsep : (a₀, b₀) ∉ F '' E := by
    rintro ⟨w, hw, hwF⟩
    have ht' : eval w t = a₀ := congrArg Prod.fst hwF
    have hu' : eval w u = b₀ := congrArg Prod.snd hwF
    have h := hu w ⟨hw.1.1, ht'⟩ hu'
    exact hw.2 (h.symm ▸ hzV)
  obtain ⟨U, hU, W, hW, hUW⟩ := mem_nhds_prod_iff.mp
    (hF.isClosed.isOpen_compl.mem_nhds hsep)
  obtain ⟨P, hP, hplane⟩ := exists_monic_plane_image_of_finite_projection Q f hf hfi t u ht
  let p (a : ℂ) := P.map (Polynomial.evalRingHom a)
  have hcont : Continuous fun a => (p a).eval b₀ := by
    simp only [p, Polynomial.eval_map, Polynomial.eval₂_eq_sum, Polynomial.sum_def,
      Polynomial.coe_evalRingHom]
    exact continuous_finset_sum _ fun j _ => (P.coeff j).continuous.mul continuous_const
  have hroot : (p a₀).eval b₀ = 0 := (hplane a₀ b₀).mpr ⟨z, hz, rfl, rfl⟩
  have hb := eventually_exists_root_mem_nhds p (fun _ => hP.map _)
    (fun _ => hP.natDegree_map _) hcont.continuousAt hroot hW
  have hD : D ∈ 𝓝 a₀ := Metric.closedBall_mem_nhds _ zero_lt_one
  filter_upwards [hb, hU, hD] with a ha haU haD
  obtain ⟨b, hbW, hab⟩ := ha
  obtain ⟨w, hw, hwt, hwu⟩ := (hplane a b).mp hab
  refine ⟨w, ?_, hw, hwt⟩
  by_contra hwV
  apply hUW (show (a, b) ∈ U ×ˢ W from ⟨haU, hbW⟩)
  exact ⟨w, ⟨⟨hw, hwt.symm ▸ haD⟩, hwV⟩, Prod.ext hwt hwu⟩

/-- Every open neighborhood of a point on a finite affine curve contains a
point whose value under a nonscalar polynomial avoids any finite set. -/
theorem exists_near_curve_point_avoiding_finite_values
    (Q : Ideal (MvPolynomial σ ℂ)) [Q.IsPrime]
    (f : Polynomial ℂ →ₐ[ℂ] (MvPolynomial σ ℂ ⧸ Q)) (hf : f.Finite)
    (hfi : Function.Injective f)
    (t u : MvPolynomial σ ℂ) (ht : Ideal.Quotient.mk Q t = f Polynomial.X)
    (hu : ∀ c : ℂ, Ideal.Quotient.mk Q (u - C c) ≠ 0)
    {z : σ → ℂ} (hz : z ∈ zeroLocus Q) {V : Set (σ → ℂ)} (hV : IsOpen V) (hzV : z ∈ V)
    {S : Set ℂ} (hS : S.Finite) :
    ∃ w ∈ V, w ∈ zeroLocus Q ∧ eval w u ∉ S := by
  let B := MvPolynomial σ ℂ ⧸ Q
  let T (c : S) := {a : ℂ | ∃ φ : B →ₐ[ℂ] ℂ, φ (f Polynomial.X) = a ∧
    φ (Ideal.Quotient.mk Q (u - C c.val)) = 0}
  letI : Finite S := hS
  have hT : (⋃ c : S, T c).Finite := finite_iUnion fun c =>
    finite_exceptional_values_of_finite_projection f hf _ (hu c.val)
  have hd : Dense (⋃ c : S, T c)ᶜ := Set.Countable.dense_compl ℂ hT.countable
  have hfreq := mem_closure_iff_frequently.mp (hd (eval z t))
  have hlift := eventually_lift_near_point_of_finite_projection Q f hf hfi t ht hz hV hzV
  obtain ⟨a, ha, w, hwV, hw, hwt⟩ := (hfreq.and_eventually hlift).exists
  refine ⟨w, hwV, hw, fun huw => ha ?_⟩
  let c : S := ⟨eval w u, huw⟩
  apply mem_iUnion.mpr
  refine ⟨c, ?_⟩
  let φ : B →ₐ[ℂ] ℂ := Ideal.Quotient.liftₐ Q (MvPolynomial.aeval w) fun p hp => hw p hp
  refine ⟨φ, ?_, ?_⟩
  · rw [← ht]
    exact hwt
  · change eval w (u - C (eval w u)) = 0
    simp

end MOC
