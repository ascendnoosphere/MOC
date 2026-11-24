import MOC.ContactCurveGeometry
import MOC.PolynomialContactChart
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import MOC.GlobalContactSlice

open Set MvPolynomial Cardinal
open scoped BigOperators
namespace MOC

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nontrivial ι]

open PolynomialContactChart

private theorem exists_chart_for_nonzero_profile (o : ι)
    (p : Equiv.Perm ι → ℂ) (hp : ∃ a b : ι → ℂ, matchingProduct a b = p)
    (hnz : ∀ σ, p σ ≠ 0) :
    ∃ i : {i : ι // i ≠ o}, ∃ x : Point o i.val, profile o i.val x = p := by
  classical
  by_cases hc : ∀ σ, p σ = p 1
  · obtain ⟨i, hi⟩ := exists_ne o
    let u : ι → ℂ := fun j => if j = i then 1 else 0
    let v : ι → ℂ := 0
    have hu : u o = 0 := by simp [u, hi.symm]
    have hv : v o = 0 := rfl
    have hui : u i = 1 := by simp [u]
    refine ⟨⟨i, hi⟩, encode o i (p 1) u v, funext fun σ => ?_⟩
    rw [profile_encode (p 1) u v hu hv hui σ, hc σ]
    simp [v]
  · obtain ⟨i, _, hi, x, _, hx⟩ := exists_point_of_nonconstant_profile o p hp hnz hc
    exact ⟨⟨i, hi⟩, x, hx⟩

/-- Every injective polynomial normalization has no more variables than
a normalized rank-one matching chart. Use the finite cover by all pivot
charts: a product of nonzero kernel elements vanishes on every chart if
none of the chart pullbacks is injective. Density and the prime profile
ideal give a contradiction. -/
theorem profile_normalization_upper_bound {d : ℕ}
    (f : MvPolynomial (Fin d) ℂ →ₐ[ℂ]
      (MvPolynomial (Equiv.Perm ι) ℂ ⧸ RingHom.ker (aeval (R := ℂ) (matchingProfile_coordinate (ι := ι)))))
    (hfi : Function.Injective f) :
    d ≤ 2 * Fintype.card ι - 2 := by
  classical
  let R := MvPolynomial (Equiv.Perm ι) ℂ
  let I : Ideal R := RingHom.ker (aeval (R := ℂ) (matchingProfile_coordinate (ι := ι)))
  letI : I.IsPrime := RingHom.ker_isPrime _
  let q : R →ₐ[ℂ] R ⧸ I := Ideal.Quotient.mkₐ ℂ I
  have hsurj : Function.Surjective q := Ideal.Quotient.mkₐ_surjective _ _
  obtain ⟨rs, hrs⟩ := Classical.axiomOfChoice (fun j : Fin d => hsurj (f (X j)))
  let F : MvPolynomial (Fin d) ℂ →ₐ[ℂ] R := aeval rs
  have hF : q.comp F = f := by
    ext j
    simpa [F] using hrs j
  obtain ⟨o⟩ := (inferInstance : Nonempty ι)
  let J := {i : ι // i ≠ o}
  let G (i : J) : MvPolynomial (Fin d) ℂ →ₐ[ℂ] Poly o i.val :=
    (aeval (profilePolynomial o i.val)).comp F
  have hinj : ∃ i : J, Function.Injective (G i) := by
    by_contra! h
    have hp (i : J) : ∃ g, g ≠ 0 ∧ G i g = 0 := by
      obtain ⟨a, b, hab, hne⟩ := Function.not_injective_iff.mp (h i)
      exact ⟨a - b, sub_ne_zero.mpr hne, by rw [map_sub, hab, sub_self]⟩
    choose g hg hzero using hp
    let P := ∏ i : J, g i
    have hP : P ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hg i
    have hGP (i : J) : G i P = 0 := by
      unfold P
      rw [map_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (hzero i)
    have hE (p : Equiv.Perm ι → ℂ)
        (hp : ∃ a b : ι → ℂ, matchingProduct a b = p) (hn : ∀ σ, p σ ≠ 0) :
        eval p (F P) = 0 := by
      obtain ⟨i, x, rfl⟩ := exists_chart_for_nonzero_profile o p hp hn
      have H := congrArg (fun e => eval x e) (hGP i)
      let e : Poly o i.val →ₐ[ℂ] ℂ := aeval x
      change e ((aeval (profilePolynomial o i.val)) (F P)) = e 0 at H
      rw [MvPolynomial.comp_aeval_apply (profilePolynomial o i.val) e, map_zero] at H
      simpa only [e, profile, MvPolynomial.coe_aeval_eq_eval] using H
    have hVan : F P ∈ vanishingIdeal (zeroLocus I) := by
      rw [← exact_matching_profiles_eq_prime_zeroLocus]
      intro p hp
      have hclosed : IsClosed {r : Equiv.Perm ι → ℂ | eval r (F P) = 0} :=
        isClosed_eq (F P).continuous_eval continuous_const
      have hm : p ∈ closure {r : Equiv.Perm ι → ℂ |
          (∃ a b : ι → ℂ, matchingProduct a b = r) ∧ ∀ σ, r σ ≠ 0} := by
        rwa [closure_nonzero_matching_profiles]
      exact hclosed.closure_subset_iff.mpr (fun r hr => hE r hr.1 hr.2) hm
    have hmem : F P ∈ I := by
      rwa [IsPrime.vanishingIdeal_zeroLocus I] at hVan
    have hzero' : (q.comp F) P = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    rw [hF] at hzero'
    exact hP (hfi (hzero'.trans (map_zero f).symm))
  obtain ⟨i, hi⟩ := hinj
  have hd := lift_trdeg_le_of_injective (G i) hi
  simp only [MvPolynomial.trdeg_of_isDomain, Cardinal.mk_fintype, Fintype.card_fin,
    Cardinal.lift_natCast, PolynomialContactChart.card_var i.property] at hd
  exact_mod_cast hd

/-- Each finite injective polynomial normalization of the exact profile
ring has exactly $2n-2$ variables, when the index type has at least two elements. -/
theorem profile_normalization_dimension {d : ℕ}
    (f : MvPolynomial (Fin d) ℂ →ₐ[ℂ] (ProfileRing ι ⧸ profileIdeal ι))
    (hf : f.Finite) (hfi : Function.Injective f) : d = 2 * Fintype.card ι - 2 :=
  le_antisymm (profile_normalization_upper_bound f hfi) (profile_normalization_lower_bound f hf)

end MOC
