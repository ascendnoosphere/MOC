import MOC.FiniteCurveAtPinnedPrime
import MOC.FiniteCurveAffineConnected
import Mathlib.RingTheory.Spectrum.Prime.Chevalley
import MOC.MatchingProfileClosed

/-! The algebraic image step uses Chevalley constructibility (Stacks Project,
Tag 054K, https://stacks.math.columbia.edu/tag/054K). -/

open Set MvPolynomial Topology
namespace MOC
variable {σ : Type*} [Fintype σ]

omit [Fintype σ] in
/-- On a finite prime affine curve, the zeros of a nonzero quotient
polynomial project into finitely many base values. -/
theorem finite_projection_values_of_zero_on_prime_curve
    (Q : Ideal (MvPolynomial σ ℂ)) [Q.IsPrime]
    (f : Polynomial ℂ →ₐ[ℂ] MvPolynomial σ ℂ ⧸ Q) (hf : f.Finite)
    (t : MvPolynomial σ ℂ) (ht : Ideal.Quotient.mk Q t = f Polynomial.X)
    (g : MvPolynomial σ ℂ) (hg : g ∉ Q) :
    {z : ℂ | ∃ x : zeroLocus Q, eval x.val t = z ∧ eval x.val g = 0}.Finite := by
  let B := MvPolynomial σ ℂ ⧸ Q
  letI : Algebra (Polynomial ℂ) B := f.toRingHom.toAlgebra
  letI : Module.Finite (Polynomial ℂ) B := hf
  let v : B := Ideal.Quotient.mk Q g
  let I : Ideal B := Ideal.span {v}
  have hv : v ≠ 0 := mt Ideal.Quotient.eq_zero_iff_mem.mp hg
  have hI : I.comap (algebraMap (Polynomial ℂ) B) ≠ ⊥ :=
    Ideal.comap_ne_bot_of_integral_mem hv (Ideal.subset_span (Set.mem_singleton v))
      (Algebra.IsIntegral.isIntegral v)
  obtain ⟨p, hp, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  refine (Polynomial.finite_setOf_isRoot hp0).subset ?_
  rintro z ⟨x, rfl, hxg⟩
  let φ : B →ₐ[ℂ] ℂ := Ideal.Quotient.liftₐ Q (aeval x.val) (fun a ha => x.property a ha)
  have hφg : φ v = 0 := hxg
  have hp' : f p ∈ I := hp
  let J := RingHom.ker φ
  have hIJ : I ≤ J := Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hφg)
  have hφp : φ (f p) = 0 := hIJ hp'
  have hm : φ.comp f = Polynomial.aeval (eval x.val t) := by
    apply Polynomial.algHom_ext
    change φ (f Polynomial.X) = Polynomial.aeval (eval x.val t) Polynomial.X
    rw [← ht, Polynomial.aeval_X]
    rfl
  change p.eval (eval x.val t) = 0
  rw [← Polynomial.coe_aeval_eq_eval, ← hm]
  exact hφp

/-- A principal Zariski-open subset of a prime affine complex set is
Euclidean dense whenever its polynomial is not in the prime. -/
theorem dense_principal_open_of_prime_complex_affine
    (I : Ideal (MvPolynomial σ ℂ)) [I.IsPrime]
    (g : MvPolynomial σ ℂ) (hg : g ∉ I) :
    Dense {z : zeroLocus I | eval z.val g ≠ 0} := by
  intro x
  by_cases hx : eval x.val g = 0
  · have hxI : I ≤ RingHom.ker (eval x.val) := fun a ha => x.property a ha
    have hxI' : I < RingHom.ker (eval x.val) :=
      lt_of_le_of_ne hxI (fun h => hg (h ▸ hx))
    obtain ⟨Q, hIQ, hQx, hQ, hgQ, f, hf, hfi, t, ht⟩ :=
      exists_finite_affine_curve_from_prime_below_point x.val I hxI' g hg
    letI : Q.IsPrime := hQ
    let S : Set ℂ := {z : ℂ | ∃ y : zeroLocus Q, eval y.val t = z ∧ eval y.val g = 0}
    have hS : S.Finite := finite_projection_values_of_zero_on_prime_curve Q f hf t ht g hgQ
    let X : zeroLocus Q := ⟨x.val, fun a ha => hQx ha⟩
    let inc : zeroLocus Q → zeroLocus I := fun y =>
      ⟨y.val, fun a ha => y.property a (hIQ ha)⟩
    have hcont : Continuous inc := Continuous.subtype_mk continuous_subtype_val _
    have hX := dense_affine_finite_projection_off_finite Q f hf hfi t ht hS X
    have hinc : inc X = x := rfl
    rw [← hinc]
    apply closure_mono ?_ (mem_closure_image hcont.continuousAt hX)
    rintro _ ⟨y, hy, rfl⟩
    exact fun hy0 => hy ⟨y, rfl, hy0⟩
  · exact subset_closure hx


/-- A constructible subset of a prime spectrum containing a given prime
contains a principal open of its closure. -/
theorem exists_principal_open_above_of_constructible_mem
    {R : Type*} [CommRing R] (S : Set (PrimeSpectrum R))
    (hS : IsConstructible S) (p : PrimeSpectrum R) (hp : p ∈ S) :
    ∃ g : R, g ∉ p.asIdeal ∧ ∀ q : PrimeSpectrum R,
      p.asIdeal ≤ q.asIdeal → g ∉ q.asIdeal → q ∈ S := by
  obtain ⟨data, rfl⟩ := PrimeSpectrum.exists_constructibleSetData_iff.mpr hS
  obtain ⟨D, hD, hpD⟩ := Set.mem_iUnion₂.mp hp
  have hDg := (PrimeSpectrum.mem_zeroLocus p _).mp hpD.1
  refine ⟨D.f, ?_, fun q hqp hqf => Set.mem_iUnion₂.mpr ⟨D, hD, ?_⟩⟩
  · intro hg
    exact hpD.2 ((PrimeSpectrum.mem_zeroLocus p _).mpr (Set.singleton_subset_iff.mpr hg))
  · refine ⟨(PrimeSpectrum.mem_zeroLocus q _).mpr (hDg.trans hqp), ?_⟩
    intro hq
    exact hqf ((PrimeSpectrum.mem_zeroLocus q _).mp hq (Set.mem_singleton _))

/-- An ordinarily closed image of a polynomial map between finite complex
affine spaces is exactly the zero locus of the kernel of its pullback. -/
theorem polynomial_map_range_eq_zeroLocus_of_isClosed
    {τ : Type*} [Fintype τ] (F : σ → MvPolynomial τ ℂ)
    (hclosed : IsClosed (Set.range fun x : τ → ℂ => fun i => eval x (F i))) :
    Set.range (fun x : τ → ℂ => fun i => eval x (F i)) =
      zeroLocus (RingHom.ker (aeval F)) := by
  let f : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial τ ℂ := aeval F
  let I := RingHom.ker f
  letI : I.IsPrime := RingHom.ker_isPrime f
  let p : PrimeSpectrum (MvPolynomial σ ℂ) := ⟨I, inferInstance⟩
  have hF : f.toRingHom.FinitePresentation := by
    apply RingHom.FinitePresentation.of_finiteType.mp
    apply RingHom.FiniteType.of_comp_finiteType (f := algebraMap ℂ (MvPolynomial σ ℂ))
    rw [show f.toRingHom.comp (algebraMap ℂ (MvPolynomial σ ℂ)) =
        algebraMap ℂ (MvPolynomial τ ℂ) from RingHom.ext f.commutes]
    exact algebraMap_finiteType_iff_algebra_finiteType.mpr inferInstance
  have hp : p ∈ Set.range (PrimeSpectrum.comap f.toRingHom) := by
    let q : PrimeSpectrum (MvPolynomial τ ℂ) := ⟨RingHom.ker (RingHom.id _), RingHom.ker_isPrime (RingHom.id _)⟩
    refine ⟨q, PrimeSpectrum.ext ?_⟩
    change Ideal.comap f (RingHom.ker (RingHom.id _)) = I
    rfl
  obtain ⟨g, hg, himage⟩ := exists_principal_open_above_of_constructible_mem _
    (PrimeSpectrum.isConstructible_range_comap hF) p hp
  show Set.range (fun x : τ → ℂ => fun i => eval x (F i)) = zeroLocus I
  apply Subset.antisymm
  · rintro _ ⟨x, rfl⟩
    intro r hr
    have h : (aeval (fun i => eval x (F i))).comp (AlgHom.id ℂ _) =
        (aeval x).comp f := by
      ext i
      simp [f]
      rfl
    have hr' : f r = 0 := hr
    have h' := DFunLike.congr_fun h r
    simp only [AlgHom.comp_apply, AlgHom.id_apply, hr', map_zero] at h'
    exact h'
  · intro x hx
    let X : zeroLocus I := ⟨x, hx⟩
    have hd := dense_principal_open_of_prime_complex_affine I g hg X
    let S := {z : zeroLocus I | eval z.val g ≠ 0}
    have hsub : Subtype.val '' S ⊆ Set.range (fun y : τ → ℂ => fun i => eval y (F i)) := by
      rintro _ ⟨z, hz, rfl⟩
      let m := RingHom.ker (eval z.val)
      letI : m.IsMaximal := RingHom.ker_isMaximal_of_surjective _
        (fun c => ⟨C c, eval_C c⟩)
      let Z : PrimeSpectrum (MvPolynomial σ ℂ) := ⟨m, inferInstance⟩
      obtain ⟨q, hq⟩ := himage Z (fun r hr => z.property r hr) hz
      have hq' : Ideal.comap f.toRingHom q.asIdeal = m := congrArg PrimeSpectrum.asIdeal hq
      obtain ⟨M, hM, hqM⟩ := Ideal.exists_le_maximal q.asIdeal q.isPrime.ne_top
      have hmax : Ideal.comap f.toRingHom M = m := by
        have hh : m ≤ Ideal.comap f.toRingHom M := hq' ▸ Ideal.comap_mono hqM
        have hne : Ideal.comap f.toRingHom M ≠ ⊤ := Ideal.IsMaximal.ne_top hM |> Ideal.comap_ne_top _
        exact (Ideal.IsMaximal.eq_of_le inferInstance hne hh).symm
      obtain ⟨y, hy⟩ := (isMaximal_iff_eq_vanishingIdeal_singleton M).mp hM
      refine ⟨y, funext fun i => ?_⟩
      have hm : MvPolynomial.X i - C (z.val i) ∈ m := by
        change eval z.val (MvPolynomial.X i - C (z.val i)) = 0
        simp
      rw [← hmax] at hm
      have hm' : f (MvPolynomial.X i - C (z.val i)) ∈ M := hm
      rw [hy, mem_vanishingIdeal_singleton_iff] at hm'
      exact sub_eq_zero.mp (by simpa [f] using hm')
    have H := mem_closure_image continuous_subtype_val.continuousAt hd
    exact hclosed.closure_subset_iff.mpr hsub H


section Profile
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A symbolic polynomial for each matching product. -/
noncomputable def matchingProfile_coordinate (π : Equiv.Perm ι) : MvPolynomial (ι ⊕ ι) ℂ :=
  ∏ j, (MvPolynomial.X (Sum.inl (π j)) + MvPolynomial.X (Sum.inr j))

/-- The exact matching-profile locus, including every degenerate spectral
profile, is the prime affine set defined by the kernel of polynomial
pullback. Nothing in this equality requires a nonzero matching product. -/
theorem exact_matching_profiles_eq_prime_zeroLocus :
    {p : Equiv.Perm ι → ℂ | ∃ a b : ι → ℂ, matchingProduct a b = p} =
      zeroLocus (RingHom.ker (aeval matchingProfile_coordinate)) := by
  classical
  have he : Set.range (fun x : ι ⊕ ι → ℂ => fun i => eval x (matchingProfile_coordinate i)) =
      {p : Equiv.Perm ι → ℂ | ∃ a b : ι → ℂ, matchingProduct a b = p} := by
    apply Subset.antisymm
    · rintro p ⟨x, rfl⟩
      refine ⟨x ∘ Sum.inl, x ∘ Sum.inr, ?_⟩
      funext i
      simp [matchingProfile_coordinate, matchingProduct]
    · rintro p ⟨a,b,rfl⟩
      refine ⟨Sum.elim a b, ?_⟩
      funext i
      simp [matchingProfile_coordinate, matchingProduct]
  rw [← he]
  apply polynomial_map_range_eq_zeroLocus_of_isClosed
  rw [he]
  exact isClosed_additive_matching_profiles

end Profile

end MOC
