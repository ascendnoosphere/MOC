import MOC.ConnectedContactStep
import MOC.FiniteCurveCofiniteImage
import MOC.FiniteCurvePrimitiveCoordinate

/-!
The contact transfer on an affine curve.

The contact-count strategy is from D. Zheng, *The Marcus–de Oliveira
conjecture for n = 4*, Theorem 3.6, DOI: 10.13140/RG.2.2.36790.25923.
Here the geometric input is a supplied prime finite affine slice. The
varying gap need not be a finite projection coordinate. Its cofinite image
gives a negative real value, and connectedness gives the contact point.
-/

open Matrix Set MvPolynomial
open scoped BigOperators

namespace MOC

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- On a prime finite affine slice, one varying matching gap is enough.
This theorem does not assume compactification, holomorphic lifts of
spectra, or that the varying gap provides the finite projection. -/
theorem StrictMatchingSupport.exists_more_contacts_on_affine_curve
    {U : Matrix ι ι ℂ} (hU : IsUnitary U) (w : StrictMatchingSupport U)
    {σ : Type*} [Fintype σ]
    (Q : Ideal (MvPolynomial σ ℂ)) [Q.IsPrime]
    (f : Polynomial ℂ →ₐ[ℂ] (MvPolynomial σ ℂ ⧸ Q))
    (hf : f.Finite) (hfi : Function.Injective f)
    (t : MvPolynomial σ ℂ) (ht : Ideal.Quotient.mk Q t = f Polynomial.X)
    (F : Equiv.Perm ι → MvPolynomial σ ℂ)
    (z₀ : zeroLocus Q)
    (hbase : (fun q => eval z₀.val (F q)) = matchingProduct w.a w.b)
    (hexact : ∀ z : zeroLocus Q, ∃ a b : ι → ℂ,
      matchingProduct a b = fun q => eval z.val (F q))
    (hold : ∀ z : zeroLocus Q, ∀ q ∈ w.contacts,
      (w.η * (eval z.val (F w.pivot) - eval z.val (F q))).re = 0)
    (hgap : ∀ z : zeroLocus Q,
      0 < (matchingProfileDetGap U w.η w.pivot (fun q => eval z.val (F q))).re)
    (hvar : ∃ q : Equiv.Perm ι, ∃ x y : zeroLocus Q,
      w.η * (eval x.val (F w.pivot) - eval x.val (F q)) ≠
        w.η * (eval y.val (F w.pivot) - eval y.val (F q))) :
    ∃ w' : StrictMatchingSupport U, w'.η = w.η ∧ w'.pivot = w.pivot ∧
      w.contacts ⊂ w'.contacts ∧
      ∃ z : zeroLocus Q, matchingProduct w'.a w'.b = fun q => eval z.val (F q) := by
  letI := connectedSpace_prime_finite_affine_curve Q f hf hfi t ht
  let P (z : zeroLocus Q) (q : Equiv.Perm ι) := eval z.val (F q)
  have hc (q : Equiv.Perm ι) :
      ContinuousOn (fun z => (w.η * (P z w.pivot - P z q)).re) univ := by
    have hp' (r : Equiv.Perm ι) : Continuous (fun z : zeroLocus Q => P z r) :=
      (F r).continuous_eval.comp continuous_subtype_val
    exact (Complex.continuous_re.comp (continuous_const.mul ((hp' w.pivot).sub (hp' q)))).continuousOn
  obtain ⟨q, x, y, hxy⟩ := hvar
  let g := C w.η * (F w.pivot - F q)
  have he (z : zeroLocus Q) :
      eval z.val g = w.η * (P z w.pivot - P z q) := by
    simp [g, P]
  obtain ⟨z, hz⟩ := exists_affine_point_with_negative_real_of_varying_coordinate
    Q f hf hfi t g ht ⟨x, y, by rw [he, he]; exact hxy⟩
  obtain ⟨v, hη, hp, hv, z', _, hz'⟩ := w.exists_more_contacts_on_connected_profiles
    hU isPreconnected_univ P (fun z _ => hexact z) hc (Set.mem_univ z₀) hbase
    (fun z _ => hold z) (fun z _ => hgap z) ⟨z, Set.mem_univ _, q, by rwa [he] at hz⟩
  exact ⟨v, hη, hp, hv, z', hz'⟩


/-- The affine slice need only have infinitely many exact profiles.
Fixing the old complex differences retains the old contacts. A
nonconstant gap follows from the translation obstruction. -/
theorem StrictMatchingSupport.exists_more_contacts_on_infinite_affine_curve
    {U : Matrix ι ι ℂ} (hU : IsUnitary U) (w : StrictMatchingSupport U)
    {σ : Type*} [Fintype σ]
    (Q : Ideal (MvPolynomial σ ℂ)) [Q.IsPrime]
    (f : Polynomial ℂ →ₐ[ℂ] (MvPolynomial σ ℂ ⧸ Q))
    (hf : f.Finite) (hfi : Function.Injective f)
    (t : MvPolynomial σ ℂ) (ht : Ideal.Quotient.mk Q t = f Polynomial.X)
    (F : Equiv.Perm ι → MvPolynomial σ ℂ)
    (z₀ : zeroLocus Q)
    (hbase : (fun q => eval z₀.val (F q)) = matchingProduct w.a w.b)
    (hexact : ∀ z : zeroLocus Q, ∃ a b : ι → ℂ,
      matchingProduct a b = fun q => eval z.val (F q))
    (hold : ∀ z : zeroLocus Q, ∀ q ∈ w.contacts,
      eval z.val (F w.pivot) - eval z.val (F q) =
        eval z₀.val (F w.pivot) - eval z₀.val (F q))
    (hgap : ∀ z : zeroLocus Q,
      matchingProfileDetGap U w.η w.pivot (fun q => eval z.val (F q)) =
        matchingProfileDetGap U w.η w.pivot (matchingProduct w.a w.b))
    (hinf : (Set.range fun z : zeroLocus Q => fun q => eval z.val (F q)).Infinite) :
    ∃ w' : StrictMatchingSupport U, w'.η = w.η ∧ w'.pivot = w.pivot ∧
      w.contacts ⊂ w'.contacts ∧
      ∃ z : zeroLocus Q, matchingProduct w'.a w'.b = fun q => eval z.val (F q) := by
  classical
  let P (z : zeroLocus Q) (q : Equiv.Perm ι) := eval z.val (F q)
  let J : Finset (Equiv.Perm ι) := w.contactsᶜ
  have hs (q) : 0 ≤ (w.η * (P z₀ w.pivot - P z₀ q)).re := by
    change 0 ≤ (w.η * ((fun r => eval z₀.val (F r)) w.pivot -
      (fun r => eval z₀.val (F r)) q)).re
    rw [hbase, mul_sub, Complex.sub_re]
    exact sub_nonneg.mpr (w.maximal q)
  have hg : 0 < (matchingProfileDetGap U w.η w.pivot (matchingProduct w.a w.b)).re := by
    rw [matchingProfileDetGap_matchingProduct w.a w.b U hU, mul_sub, Complex.sub_re]
    exact sub_pos.mpr w.strict
  have hv := exists_varying_matching_difference_of_infinite_profile_image
    (Set.mem_univ z₀) P U hU w.η w.pivot J (fun z _ => hexact z)
    (fun z _ q hq => hold z q (by simpa [J] using hq)) hs
    (by rwa [hgap z₀]) (by simpa only [Set.image_univ] using hinf)
  refine w.exists_more_contacts_on_affine_curve hU Q f hf hfi t ht F z₀ hbase hexact ?_ ?_ ?_
  · intro z q hq
    rw [hold z q hq]
    have hmatch := (Finset.mem_filter.mp hq).2
    change (w.η * ((fun r => eval z₀.val (F r)) w.pivot -
      (fun r => eval z₀.val (F r)) q)).re = 0
    rw [hbase, mul_sub, Complex.sub_re, hmatch, sub_self]
  · intro z
    rw [hgap z]
    exact hg
  · obtain ⟨q, _, x, _, y, _, hxy⟩ := hv
    exact ⟨q, x, y, hxy⟩



/-- The affine contact step with the fixed-gap conditions expressed as
ideal membership. A prime curve in this slice supplies the complex
equalities automatically at every point, including exceptional fibres. -/
theorem StrictMatchingSupport.exists_more_contacts_on_affine_constraints
    {U : Matrix ι ι ℂ} (hU : IsUnitary U) (w : StrictMatchingSupport U)
    {σ : Type*} [Fintype σ]
    (Q : Ideal (MvPolynomial σ ℂ)) [Q.IsPrime]
    (f : Polynomial ℂ →ₐ[ℂ] (MvPolynomial σ ℂ ⧸ Q))
    (hf : f.Finite) (hfi : Function.Injective f)
    (t : MvPolynomial σ ℂ) (ht : Ideal.Quotient.mk Q t = f Polynomial.X)
    (F : Equiv.Perm ι → MvPolynomial σ ℂ)
    (z₀ : zeroLocus Q)
    (hbase : (fun q => eval z₀.val (F q)) = matchingProduct w.a w.b)
    (hexact : ∀ z : zeroLocus Q, ∃ a b : ι → ℂ,
      matchingProduct a b = fun q => eval z.val (F q))
    (hold : ∀ q ∈ w.contacts, F w.pivot - F q -
      C (eval z₀.val (F w.pivot) - eval z₀.val (F q)) ∈ Q)
    (hgap : (∑ q, C (realSignedWeight U q : ℂ) *
        (C w.η * (F q - F w.pivot))) -
      C (matchingProfileDetGap U w.η w.pivot (matchingProduct w.a w.b)) ∈ Q)
    (hinf : (Set.range fun z : zeroLocus Q => fun q => eval z.val (F q)).Infinite) :
    ∃ w' : StrictMatchingSupport U, w'.η = w.η ∧ w'.pivot = w.pivot ∧
      w.contacts ⊂ w'.contacts ∧
      ∃ z : zeroLocus Q, matchingProduct w'.a w'.b = fun q => eval z.val (F q) := by
  refine w.exists_more_contacts_on_infinite_affine_curve hU Q f hf hfi t ht F z₀
    hbase hexact ?_ ?_ hinf
  · intro z q hq
    have he := z.property _ (hold q hq)
    simpa only [map_sub, eval_C, sub_eq_zero] using he
  · intro z
    have he := z.property _ hgap
    simpa only [map_sub, map_sum, map_mul, eval_C, sub_eq_zero, matchingProfileDetGap] using he


end MOC
