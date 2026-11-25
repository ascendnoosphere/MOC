import MOC.PolynomialFiberDimension
import Mathlib.RingTheory.Spectrum.Prime.Noetherian

/-! A polynomial fiber with fewer equations than coordinates has no
singleton irreducible component at the chosen point. -/

open BigOperators MvPolynomial

namespace MOC

noncomputable section

variable {K σ ι : Type*} [Field K] [IsAlgClosed K] [Fintype σ] [Fintype ι]

/-- Every minimal prime of the fiber ideal through the specified point is
strictly below the point ideal. A product of one separator per other
minimal prime would otherwise isolate this component on a principal open. -/
theorem minimalPrime_lt_of_polynomial_fiber
    (p : ι → MvPolynomial σ K) (z : σ → K)
    (hcard : Fintype.card ι < Fintype.card σ)
    (P : Ideal (MvPolynomial σ K))
    (hP : P ∈ (Ideal.span (Set.range fun i => p i - C (eval z (p i)))).minimalPrimes)
    (hle : P ≤ vanishingIdeal ({z} : Set (σ → K))) :
    P < vanishingIdeal ({z} : Set (σ → K)) := by
  classical
  let I := Ideal.span (Set.range fun i => p i - C (eval z (p i)))
  let Q := vanishingIdeal ({z} : Set (σ → K))
  change P < Q
  by_contra hlt
  have heq : P = Q := eq_of_le_of_not_lt hle hlt
  have hQ : Q ∈ I.minimalPrimes := heq ▸ hP
  let S := I.minimalPrimes \ ({Q} : Set (Ideal (MvPolynomial σ K)))
  have hmin : I.minimalPrimes.Finite :=
    Ideal.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial σ K) I
  have hS : S.Finite := hmin.subset Set.diff_subset
  have hQmin : Minimal (fun J : Ideal (MvPolynomial σ K) => J.IsPrime ∧ I ≤ J) Q := hQ
  letI : Fintype S := hS.fintype
  have hsep (R : S) : ∃ f, f ∈ R.val ∧ f ∉ Q := by
    have hRmin : Minimal (fun J : Ideal (MvPolynomial σ K) => J.IsPrime ∧ I ≤ J) R.val :=
      R.property.1
    have hnle : ¬ R.val ≤ Q := by
      intro hRQ
      have hQR : Q ≤ R.val := hQmin.le_of_le hRmin.prop hRQ
      exact R.property.2 (Set.mem_singleton_iff.mpr (le_antisymm hRQ hQR))
    apply Classical.byContradiction
    intro hsep
    apply hnle
    intro f hf
    apply Classical.byContradiction
    intro hfQ
    exact hsep ⟨f, hf, hfQ⟩
  choose f hfP hfQ using hsep
  let F := ∏ R : S, f R
  have hF : eval z F ≠ 0 := by
    change eval z (∏ R : S, f R) ≠ 0
    rw [map_prod]
    refine Finset.prod_ne_zero_iff.mpr fun R _ hR => hfQ R ?_
    exact (mem_vanishingIdeal_singleton_iff z (f R)).mpr hR
  obtain ⟨w, hw, hwF, hwp⟩ := exists_other_regular_point_of_polynomial_fiber p F z hF hcard
  let Qw := vanishingIdeal ({w} : Set (σ → K))
  have hIw : I ≤ Qw := by
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    exact (mem_vanishingIdeal_singleton_iff w _).mpr (by simp [hwp i])
  obtain ⟨R, hR, hRw⟩ := Ideal.exists_minimalPrimes_le hIw
  have hRQ : R = Q := by
    by_cases h : R = Q
    · exact h
    · let R' : S := ⟨R, ⟨hR, Set.not_mem_singleton_iff.mpr h⟩⟩
      have hfr : eval w (f R') = 0 :=
        (mem_vanishingIdeal_singleton_iff w (f R')).mp (hRw (hfP R'))
      exfalso
      apply hwF
      change eval w (∏ T : S, f T) = 0
      rw [map_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ R') hfr
  apply hw
  funext j
  have hx : X j - C (z j) ∈ Q :=
    (mem_vanishingIdeal_singleton_iff z _).mpr (by simp)
  have h := (mem_vanishingIdeal_singleton_iff w _).mp (hRw (hRQ.symm ▸ hx))
  exact sub_eq_zero.mp (by simpa only [map_sub, eval_X, eval_C] using h)

/-- There is a prime strictly below the starting point that contains every
equation of the fiber. -/
theorem exists_prime_lt_of_polynomial_fiber
    (p : ι → MvPolynomial σ K) (z : σ → K)
    (hcard : Fintype.card ι < Fintype.card σ) :
    ∃ P : Ideal (MvPolynomial σ K), P.IsPrime ∧
      (∀ i, p i - C (eval z (p i)) ∈ P) ∧ P < vanishingIdeal ({z} : Set (σ → K)) := by
  let I := Ideal.span (Set.range fun i => p i - C (eval z (p i)))
  have hIQ : I ≤ vanishingIdeal ({z} : Set (σ → K)) := by
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    exact (mem_vanishingIdeal_singleton_iff z _).mpr (by simp)
  obtain ⟨P, hP, hPQ⟩ := Ideal.exists_minimalPrimes_le hIQ
  have hPmin : Minimal (fun J : Ideal (MvPolynomial σ K) => J.IsPrime ∧ I ≤ J) P := hP
  refine ⟨P, Ideal.minimalPrimes_isPrime hP, ?_,
    minimalPrime_lt_of_polynomial_fiber p z hcard P hP hPQ⟩
  intro i
  exact hPmin.prop.2 (Ideal.subset_span ⟨i, rfl⟩)

end

end MOC
