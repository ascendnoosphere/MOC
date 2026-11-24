import MOC.FiniteCurveAtPinnedPrime
import MOC.PolynomialEvaluationHeight
import MOC.KrullHeightChain

/-! Pinned affine dimension via generalized height (Stacks Project, Tag 00KD)
and going down over a normal domain (Tag 00H8). -/

open Set MvPolynomial
namespace MOC

/-- Going down lifts the length of a prescribed prime chain through
any chosen prime over its endpoint. -/
theorem exists_prime_chain_of_goingDown
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [Algebra.HasGoingDown A B]
    (s : LTSeries (PrimeSpectrum A)) (q : PrimeSpectrum B)
    (hq : PrimeSpectrum.comap (algebraMap A B) q = s.last) :
    ∃ t : LTSeries (PrimeSpectrum B), t.last = q ∧ t.length = s.length := by
  have H (n : ℕ) (p : LTSeries (PrimeSpectrum A)) (hn : p.length = n)
      (Q : PrimeSpectrum B) (hQ : PrimeSpectrum.comap (algebraMap A B) Q = p.last) :
      ∃ t : LTSeries (PrimeSpectrum B), t.last = Q ∧ t.length = p.length := by
    induction n using Nat.strong_induction_on generalizing p Q with
    | h n ih =>
      by_cases h₀ : n = 0
      · exact ⟨RelSeries.singleton (· < ·) Q, rfl, (hn.trans h₀).symm⟩
      · let u := p.eraseLast
        have hu : u.last < p.last := p.eraseLast_last_rel_last (hn.trans_ne h₀)
        letI : Q.asIdeal.LiesOver p.last.asIdeal := ⟨(congrArg PrimeSpectrum.asIdeal hQ).symm⟩
        obtain ⟨P, hPQ, hP, hPu⟩ := Q.asIdeal.exists_ideal_lt_liesOver_of_lt
          (p := u.last.asIdeal) (q := p.last.asIdeal) hu
        let P' : PrimeSpectrum B := ⟨P, hP⟩
        have hPt : PrimeSpectrum.comap (algebraMap A B) P' = u.last :=
          PrimeSpectrum.ext hPu.over.symm
        have hl : u.length < n := by
          dsimp [u]
          omega
        obtain ⟨t, ht, htl⟩ := ih u.length hl u rfl P' hPt
        have htQ : t.last < Q := ht.symm ▸ hPQ
        refine ⟨t.snoc Q htQ, by simp, ?_⟩
        rw [RelSeries.snoc_length, htl]
        dsimp [u]
        omega
  exact H s.length s rfl q hq

/-- For one prescribed finite injective normalization of a complex
affine domain, every maximal point admits as many strict prime edges
below it as there are variables in that normalization. -/
theorem exists_prime_chain_at_max_of_finite_poly
    {B : Type*} [CommRing B] [IsDomain B] [Algebra ℂ B]
    {n : ℕ} (f : MvPolynomial (Fin n) ℂ →ₐ[ℂ] B)
    (hf : f.Finite) (hfi : Function.Injective f)
    (m : Ideal B) [m.IsMaximal] :
    ∃ p : LTSeries (PrimeSpectrum B), p.last.asIdeal = m ∧ p.length = n := by
  let A := MvPolynomial (Fin n) ℂ
  letI : Algebra A B := f.toRingHom.toAlgebra
  letI : IsScalarTower ℂ A B := IsScalarTower.of_algebraMap_eq fun c => (f.commutes c).symm
  letI : Module.Finite A B := hf
  letI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hfi
  letI : Algebra.HasGoingDown A B := hasGoingDown_of_finite_normal_base A B
  have hm : (m.under A).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal m
  obtain ⟨x, hx⟩ := (isMaximal_iff_eq_vanishingIdeal_singleton (m.under A)).mp hm
  have heq : m.under A = RingHom.ker (MvPolynomial.eval x) := by
    rw [hx]
    ext r
    exact mem_vanishingIdeal_singleton_iff x r
  obtain ⟨s, hsl, hsn⟩ := exists_polynomial_eval_prime_chain x
  let q : PrimeSpectrum B := ⟨m, inferInstance⟩
  have hq : PrimeSpectrum.comap (algebraMap A B) q = s.last :=
    PrimeSpectrum.ext (heq.trans hsl.symm)
  obtain ⟨p, hp, hpn⟩ := exists_prime_chain_of_goingDown s q hq
  exact ⟨p, congrArg PrimeSpectrum.asIdeal hp, hpn.trans (hsn.trans (Fintype.card_fin n))⟩


/-- A normalized prime affine complex set has a finite curve through each
point after fewer equations than the normalization dimension have been
imposed. The curve's ideal contains the original prime and all the cuts. -/
theorem exists_finite_curve_at_prime_affine_after_equations
    {σ : Type*} [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) [I.IsPrime]
    {n : ℕ} (f : MvPolynomial (Fin n) ℂ →ₐ[ℂ] (MvPolynomial σ ℂ ⧸ I))
    (hf : f.Finite) (hfi : Function.Injective f) (x : zeroLocus I)
    (s : Finset (MvPolynomial σ ℂ)) (hs : ∀ g ∈ s, eval x.val g = 0)
    (hn : s.card < n) :
    ∃ Q : Ideal (MvPolynomial σ ℂ), I ≤ Q ∧ Q ≤ RingHom.ker (eval x.val) ∧
      Q.IsPrime ∧ (∀ g ∈ s, g ∈ Q) ∧
      ∃ φ : Polynomial ℂ →ₐ[ℂ] (MvPolynomial σ ℂ ⧸ Q),
        φ.Finite ∧ Function.Injective φ ∧
        ∃ t : MvPolynomial σ ℂ, Ideal.Quotient.mk Q t = φ Polynomial.X := by
  classical
  let B := MvPolynomial σ ℂ ⧸ I
  let k : MvPolynomial σ ℂ →+* B := Ideal.Quotient.mk I
  let ε : B →ₐ[ℂ] ℂ := Ideal.Quotient.liftₐ I (aeval x.val) (fun g hg => x.property g hg)
  let m : Ideal B := RingHom.ker ε
  have hε : Function.Surjective ε := fun c => ⟨algebraMap ℂ B c, ε.commutes c⟩
  letI : m.IsMaximal := RingHom.ker_isMaximal_of_surjective ε hε
  obtain ⟨chain, hcl, hcn⟩ := exists_prime_chain_at_max_of_finite_poly f hf hfi m
  let S := s.image k
  have hS : ∀ g ∈ S, g ∈ chain.last.asIdeal := by
    intro g hg
    rw [hcl]
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hg
    exact hs e he
  have hbudget : S.card < chain.length := by
    rw [hcn]
    exact (Finset.card_image_le).trans_lt hn
  obtain ⟨p, hpm, hps⟩ := exists_prime_below_end_containing_finite_equations S chain hS hbudget
  let P := Ideal.comap k p.asIdeal
  letI : P.IsPrime := Ideal.comap_isPrime k _
  have hP : P < RingHom.ker (eval x.val) := by
    have hpm' : p.asIdeal < m := hcl ▸ hpm
    change p.asIdeal.comap k < m.comap k
    exact lt_of_le_of_ne (Ideal.comap_mono hpm'.le) (fun h =>
      (not_le_of_gt hpm') ((Ideal.comap_le_comap_iff_of_surjective k Ideal.Quotient.mk_surjective _ _).mp h.ge))
  obtain ⟨w, _, hw⟩ := SetLike.exists_of_lt hP
  obtain ⟨Q, hPQ, hQx, hQ, _, φ, hφ, hφi, t, ht⟩ :=
    exists_finite_affine_curve_from_prime_below_point x.val P hP w hw
  have hIP : I ≤ P := fun g hg => by
    change Ideal.Quotient.mk I g ∈ p.asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hg]
    exact Ideal.zero_mem _
  refine ⟨Q, hIP.trans hPQ, hQx, hQ, ?_, φ, hφ, hφi, t, ht⟩
  intro g hg
  exact hPQ (hps (Ideal.subset_span (show k g ∈ S from Finset.mem_image_of_mem k hg)))

end MOC
