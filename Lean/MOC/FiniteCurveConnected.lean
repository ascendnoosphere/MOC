import MOC.FiniteCurveGrowth
import MOC.FiniteCurveRootCover
import Mathlib.Algebra.Polynomial.BigOperators

/-! An irreducible monic plane curve remains connected above the cofinite simple-root base. -/

open Filter Set Polynomial
open scoped BigOperators Topology

namespace MOC

private theorem differentiableAt_coeff_finset_prod {ι : Type*}
    (s : Finset ι) (f : ι → ℂ → ℂ[X]) (z : ℂ)
    (hf : ∀ i ∈ s, ∀ k, DifferentiableAt ℂ (fun t => (f i t).coeff k) z) (k : ℕ) :
    DifferentiableAt ℂ (fun t => (∏ i ∈ s, f i t).coeff k) z := by
  classical
  induction s using Finset.induction_on generalizing k with
  | empty => simp
  | insert i s hi ih =>
    have h₁ := hf i (Finset.mem_insert_self i s)
    have h₂ (m : ℕ) := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)) m
    simp_rw [Finset.prod_insert hi, coeff_mul]
    exact DifferentiableAt.sum (fun a _ => (h₁ a.1).mul (h₂ a.2))

private noncomputable def selectedRootFactor
    (P : ℂ[X][X]) (U : Set (ℂ × ℂ)) (z : ℂ) : ℂ[X] := by
  classical
  exact ∏ w ∈ (P.map (evalRingHom z)).roots.toFinset.filter (fun w => (z, w) ∈ U), (X - C w)

private theorem selectedRootFactor_monic (P : ℂ[X][X]) (U : Set (ℂ × ℂ)) (z : ℂ) :
    (selectedRootFactor P U z).Monic := by
  classical
  unfold selectedRootFactor
  exact monic_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)

private theorem selectedRootFactor_pos
    (P : ℂ[X][X]) (hP : P.Monic) {U : Set (ℂ × ℂ)} {z w : ℂ}
    (hr : (P.map (evalRingHom z)).IsRoot w) (hu : (z, w) ∈ U) :
    0 < (selectedRootFactor P U z).natDegree := by
  classical
  unfold selectedRootFactor
  rw [natDegree_finset_prod_X_sub_C_eq_card]
  exact Finset.card_pos.mpr ⟨w, Finset.mem_filter.mpr
    ⟨Multiset.mem_toFinset.mpr ((mem_roots (hP.map _).ne_zero).mpr hr), hu⟩⟩

private theorem selectedRootFactor_coeff_holomorphic
    (P : ℂ[X][X]) (hP : P.Monic)
    {S : Set ℂ} (hS : S.Finite)
    (hsep : ∀ z ∈ Sᶜ, (P.map (evalRingHom z)).Separable)
    {U V : Set (ℂ × ℂ)} (hU : IsOpen U) (hV : IsOpen V)
    (hcover : ∀ z ∈ Sᶜ, ∀ w, (P.map (evalRingHom z)).IsRoot w → (z,w) ∈ U ∪ V)
    (hdis : ∀ z ∈ Sᶜ, ∀ w, (P.map (evalRingHom z)).IsRoot w → (z,w) ∈ U → (z,w) ∉ V)
    (k : ℕ) : DifferentiableOn ℂ (fun z => (selectedRootFactor P U z).coeff k) Sᶜ := by
  classical
  intro z₀ hz₀
  let Q (z : ℂ) := P.map (evalRingHom z)
  let R := (Q z₀).roots.toFinset
  obtain ⟨g, hval, hlocal⟩ := exists_local_holomorphic_root_cover P hP z₀ (hsep z₀ hz₀)
  change ∀ r : (↑R : Type), g r z₀ = r.val at hval
  let J : Finset (↑R : Type) := Finset.univ.filter (fun r => (z₀, r.val) ∈ U)
  have hdiff (r : (↑R : Type)) : DifferentiableAt ℂ (g r) z₀ :=
    hlocal.self_of_nhds.1 r
  have hroot₀ (r : (↑R : Type)) : (Q z₀).IsRoot r.val :=
    (mem_roots (hP.map _).ne_zero).mp (Multiset.mem_toFinset.mp r.property)
  have hbase : ∀ᶠ z : ℂ in 𝓝 z₀, z ∈ Sᶜ :=
    hS.isClosed.isOpen_compl.mem_nhds hz₀
  have hflag (r : (↑R : Type)) : ∀ᶠ z in 𝓝 z₀, (z, g r z) ∈ U ↔ (z₀, r.val) ∈ U := by
    have hc : ContinuousAt (fun z : ℂ => (z, g r z)) z₀ :=
      continuousAt_id.prodMk (hdiff r).continuousAt
    by_cases hru : (z₀, r.val) ∈ U
    · have hsrc : (z₀, g r z₀) ∈ U := by simpa only [hval] using hru
      filter_upwards [hc (hU.mem_nhds hsrc)] with z hz
      exact iff_of_true hz hru
    · have hrv := (hcover z₀ hz₀ _ (hroot₀ r)).resolve_left hru
      have hsrc : (z₀, g r z₀) ∈ V := by simpa only [hval] using hrv
      filter_upwards [hc (hV.mem_nhds hsrc), hbase, hlocal] with z hV' hZ hloc
      have hrz : (Q z).IsRoot (g r z) := (hloc.2.2 _).mpr ⟨r, rfl⟩
      exact iff_of_false (fun h => hdis z hZ _ hrz h hV') hru
  have hflags : ∀ᶠ z in 𝓝 z₀, ∀ r : (↑R : Type), (z, g r z) ∈ U ↔ (z₀, r.val) ∈ U :=
    Filter.eventually_all.mpr hflag
  have hEq : ∀ᶠ z in 𝓝 z₀, selectedRootFactor P U z =
      ∏ r ∈ J, ((X : ℂ[X]) - C (g r z)) := by
    filter_upwards [hflags, hlocal] with z hflags hloc
    have hq0 : Q z ≠ 0 := (hP.map _).ne_zero
    have he : (Q z).roots.toFinset.filter (fun w => (z, w) ∈ U) = J.image (fun r => g r z) := by
      ext w
      simp only [Finset.mem_filter, Multiset.mem_toFinset, mem_roots hq0,
        Finset.mem_image, J, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hw, hwu⟩
        obtain ⟨r, rfl⟩ := (hloc.2.2 _).mp hw
        exact ⟨r, (hflags r).mp hwu, rfl⟩
      · rintro ⟨r, hr, rfl⟩
        exact ⟨(hloc.2.2 _).mpr ⟨r, rfl⟩, (hflags r).mpr hr⟩
    unfold selectedRootFactor
    change (∏ w ∈ (Q z).roots.toFinset.filter (fun w => (z,w) ∈ U), _) = _
    rw [he, Finset.prod_image]
    exact hloc.2.1.injOn
  apply DifferentiableAt.differentiableWithinAt
  apply DifferentiableAt.congr_of_eventuallyEq
    (differentiableAt_coeff_finset_prod J (fun r z => (X : ℂ[X]) - C (g r z)) z₀ ?_ k)
  · exact hEq.mono (fun _ h => congrArg (fun p : ℂ[X] => p.coeff k) h)
  · intro r _ m
    simp only [coeff_sub, coeff_C]
    by_cases hm : m = 0
    · simp only [hm, if_true, coeff_X_zero]
      simpa only [zero_sub] using (hdiff r).neg
    · simp only [hm, if_false, sub_zero]
      exact differentiableAt_const _

/-- The total simple-root cover of a monic irreducible plane curve is
preconnected after removing any finite set of parameters containing all
nonsimple fibers. A separating pair of open sets would produce two monic
factor families. Their coefficients are holomorphic on the regular base
and hence polynomial by the uniform root bounds. -/
theorem isPreconnected_simple_root_cover_of_irreducible
    (P : ℂ[X][X]) (hP : P.Monic) (hirr : Irreducible P)
    {S : Set ℂ} (hS : S.Finite)
    (hsep : ∀ z ∈ Sᶜ, (P.map (evalRingHom z)).Separable) :
    IsPreconnected {p : ℂ × ℂ | p.1 ∈ Sᶜ ∧ (P.map (evalRingHom p.1)).IsRoot p.2} := by
  classical
  let Y : Set (ℂ × ℂ) := {p | p.1 ∈ Sᶜ ∧ (P.map (evalRingHom p.1)).IsRoot p.2}
  change IsPreconnected Y
  intro U V hU hV hcover hYU hYV
  by_contra hnone
  have hc (z : ℂ) (hz : z ∈ Sᶜ) (w : ℂ) (hw : (P.map (evalRingHom z)).IsRoot w) :
      (z, w) ∈ U ∪ V :=
    hcover (show (z,w) ∈ Y from ⟨hz, hw⟩)
  have hdis (z : ℂ) (hz : z ∈ Sᶜ) (w : ℂ) (hw : (P.map (evalRingHom z)).IsRoot w)
      (hu : (z,w) ∈ U) (hv : (z,w) ∈ V) : False :=
    hnone ⟨(z,w), ⟨hz,hw⟩, hu, hv⟩
  let F := selectedRootFactor P U
  let G := selectedRootFactor P V
  have hmF (z : ℂ) (_ : z ∈ Sᶜ) : (F z).Monic := selectedRootFactor_monic P U z
  have hmG (z : ℂ) (_ : z ∈ Sᶜ) : (G z).Monic := selectedRootFactor_monic P V z
  have hhF (k : ℕ) (_ : k ≤ P.natDegree) : DifferentiableOn ℂ (fun z => (F z).coeff k) Sᶜ :=
    selectedRootFactor_coeff_holomorphic P hP hS hsep hU hV hc hdis k
  have hhG (k : ℕ) (_ : k ≤ P.natDegree) : DifferentiableOn ℂ (fun z => (G z).coeff k) Sᶜ :=
    selectedRootFactor_coeff_holomorphic P hP hS hsep hV hU
      (fun z hz w hw => by
        rcases hc z hz w hw with h | h
        · exact Or.inr h
        · exact Or.inl h)
      (fun z hz w hw hv hu => hdis z hz w hw hu hv) k
  have hfg (z : ℂ) (hz : z ∈ Sᶜ) : P.map (evalRingHom z) = F z * G z := by
    let Q := P.map (evalRingHom z)
    have hq : Q.Monic := hP.map _
    have hn : Q.roots.Nodup := Polynomial.nodup_roots (hsep z hz)
    have hfilt : Q.roots.toFinset.filter (fun w => (z,w) ∈ V) =
        Q.roots.toFinset.filter (fun w => ¬(z,w) ∈ U) := by
      ext w
      simp only [Finset.mem_filter, Multiset.mem_toFinset, mem_roots hq.ne_zero]
      exact and_congr_right fun hw => ⟨fun hv hu => hdis z hz w hw hu hv,
        fun hu => (hc z hz w hw).resolve_left hu⟩
    change Q = selectedRootFactor P U z * selectedRootFactor P V z
    unfold selectedRootFactor
    change Q = (∏ w ∈ Q.roots.toFinset.filter (fun w => (z,w) ∈ U), (X - C w)) *
      (∏ w ∈ Q.roots.toFinset.filter (fun w => (z,w) ∈ V), (X - C w))
    rw [hfilt, Finset.prod_filter_mul_prod_filter_not]
    calc
      Q = (Q.roots.map (fun w => (X : ℂ[X]) - C w)).prod :=
        eq_prod_roots_of_monic_of_splits_id hq (IsAlgClosed.splits Q)
      _ = _ := by
        change (Q.roots.map (fun w => (X : ℂ[X]) - C w)).prod =
          ((Q.roots.toFinset.val).map (fun w => (X : ℂ[X]) - C w)).prod
        rw [Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hn]
  obtain ⟨q, hq⟩ := exists_polynomial_family_of_holomorphic_monic_factors P hP hS F hmF
    (fun z hz => ⟨G z, hfg z hz⟩) hhF
  obtain ⟨r, hr⟩ := exists_polynomial_family_of_holomorphic_monic_factors P hP hS G hmG
    (fun z hz => ⟨F z, (hfg z hz).trans (mul_comm _ _)⟩) hhG
  have hp : P = q * r := by
    apply Polynomial.ext
    intro k
    apply eq_of_infinite_eval_eq
    have hi : Sᶜ.Infinite := (Set.infinite_univ.diff hS).mono (fun _ hz => hz.2)
    apply hi.mono
    intro z hz
    have he : P.map (evalRingHom z) = (q * r).map (evalRingHom z) := by
      rw [Polynomial.map_mul, hq z hz, hr z hz, hfg z hz]
    simpa only [coeff_map, coe_evalRingHom]
      using congrArg (fun V : ℂ[X] => V.coeff k) he
  rcases hirr.isUnit_or_isUnit hp with hunit | hunit
  · obtain ⟨⟨z,w⟩, ⟨hz, hw⟩, hu⟩ := hYU
    have hd := selectedRootFactor_pos P hP hw hu
    have he : IsUnit (F z) := (hq z hz) ▸ hunit.map (Polynomial.mapRingHom (evalRingHom z))
    exact (Nat.ne_of_gt hd) (natDegree_eq_zero_of_isUnit he)
  · obtain ⟨⟨z,w⟩, ⟨hz, hw⟩, hv⟩ := hYV
    have hd := selectedRootFactor_pos P hP hw hv
    have he : IsUnit (G z) := (hr z hz) ▸ hunit.map (Polynomial.mapRingHom (evalRingHom z))
    exact (Nat.ne_of_gt hd) (natDegree_eq_zero_of_isUnit he)

/-- The preconnected simple-root cover is nonempty, since an irreducible
monic plane polynomial has positive vertical degree. -/
theorem isConnected_simple_root_cover_of_irreducible
    (P : ℂ[X][X]) (hP : P.Monic) (hirr : Irreducible P)
    {S : Set ℂ} (hS : S.Finite)
    (hsep : ∀ z ∈ Sᶜ, (P.map (evalRingHom z)).Separable) :
    IsConnected {p : ℂ × ℂ | p.1 ∈ Sᶜ ∧ (P.map (evalRingHom p.1)).IsRoot p.2} := by
  refine ⟨?_, isPreconnected_simple_root_cover_of_irreducible P hP hirr hS hsep⟩
  have hdeg : 0 < P.natDegree := Nat.pos_of_ne_zero fun he => by
    have h := hP.natDegree_eq_zero_iff_eq_one.mp he
    exact hirr.not_isUnit (h ▸ isUnit_one)
  obtain ⟨z, hz⟩ := hS.exists_not_mem
  let Q := P.map (evalRingHom z)
  have hm : Q.Monic := hP.map _
  have hd : Q.degree ≠ 0 := by
    rw [degree_eq_natDegree hm.ne_zero, hP.natDegree_map]
    exact ne_of_gt (by exact_mod_cast hdeg)
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_root Q hd
  exact ⟨(z,w), hz, hw⟩

end MOC
