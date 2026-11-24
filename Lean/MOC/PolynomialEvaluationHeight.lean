import MOC.KrullHeightChain
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Data.Complex.Basic

/-! Each coordinate specialization contributes one strict edge to a chain
ending at the evaluation ideal. -/

namespace MOC
open MvPolynomial

section
variable {σ K : Type*} [Field K] [DecidableEq σ]

private noncomputable def partialEval (z : σ → K) (s : Finset σ) :
    MvPolynomial σ K →+* MvPolynomial σ K :=
  eval₂Hom C fun i => if i ∈ s then C (z i) else X i

private noncomputable def partialEvalPrime (z : σ → K) (s : Finset σ) :
    PrimeSpectrum (MvPolynomial σ K) :=
  ⟨RingHom.ker (partialEval z s), RingHom.ker_isPrime _⟩

private theorem partialEvalPrime_lt (z : σ → K) {s t : Finset σ}
    (hst : s ⊆ t) (i : σ) (his : i ∉ s) (hit : i ∈ t) :
    partialEvalPrime z s < partialEvalPrime z t := by
  have hcomp : (partialEval z t).comp (partialEval z s) = partialEval z t := by
    unfold partialEval
    rw [comp_eval₂Hom]
    congr 1
    · ext x
      simp
    · funext j
      by_cases hj : j ∈ s
      · simp [hj, hst hj]
      · simp [hj, eval₂Hom_X']
  refine lt_of_le_of_ne (fun p hp => ?_) (fun he => ?_)
  · change partialEval z t p = 0
    change partialEval z s p = 0 at hp
    exact (RingHom.congr_fun hcomp p).symm.trans (by simp [RingHom.comp_apply, hp])
  · let p : MvPolynomial σ K := X i - C (z i)
    have ht : p ∈ (partialEvalPrime z t).asIdeal := by
      change partialEval z t p = 0
      simp [partialEval, p, hit]
    have hs : p ∈ (partialEvalPrime z s).asIdeal := he ▸ ht
    change partialEval z s p = 0 at hs
    have heq : (X i : MvPolynomial σ K) = C (z i) := by
      exact sub_eq_zero.mp (by simpa [partialEval, p, his] using hs)
    have hf := congrArg (eval fun _ : σ => z i + 1) heq
    simp at hf

private theorem exists_partialEvalPrime_chain (z : σ → K) (s : Finset σ) :
    ∃ p : LTSeries (PrimeSpectrum (MvPolynomial σ K)),
      p.last = partialEvalPrime z s ∧ p.length = s.card := by
  induction s using Finset.induction_on with
  | empty => exact ⟨RelSeries.singleton (· < ·) _, rfl, rfl⟩
  | @insert i s hi ih =>
    obtain ⟨p, hp, hn⟩ := ih
    have he : p.last < partialEvalPrime z (insert i s) := by
      rw [hp]
      exact partialEvalPrime_lt z (Finset.subset_insert _ _) i hi (Finset.mem_insert_self _ _)
    exact ⟨p.snoc _ he, by simp, by simp [hn, hi]⟩

/-- A coordinate-by-coordinate chain of exact length equal to the number
of variables ends at the kernel of polynomial evaluation. -/
theorem exists_polynomial_eval_prime_chain [Fintype σ] (z : σ → K) :
    ∃ p : LTSeries (PrimeSpectrum (MvPolynomial σ K)),
      p.last.asIdeal = RingHom.ker (eval z) ∧ p.length = Fintype.card σ := by
  obtain ⟨p, hp, hn⟩ := exists_partialEvalPrime_chain z Finset.univ
  refine ⟨p, ?_, by simpa using hn⟩
  rw [hp]
  ext q
  change partialEval z Finset.univ q = 0 ↔ eval z q = 0
  have he : partialEval z Finset.univ = C.comp (eval z) := by
    unfold partialEval eval
    rw [comp_eval₂Hom]
    congr 1
    funext i; simp
  rw [he, RingHom.comp_apply]
  exact ⟨fun h => C_injective σ K (h.trans C.map_zero.symm), fun h => h ▸ C.map_zero⟩

/-- Fewer equations than variables, all vanishing at the given point,
lie in a prime strictly below its evaluation ideal. -/
theorem exists_prime_lt_polynomial_eval_of_few_equations [Fintype σ] (z : σ → K)
    (s : Finset (MvPolynomial σ K)) (hs : ∀ f ∈ s, eval z f = 0)
    (hbudget : s.card < Fintype.card σ) :
    ∃ q : PrimeSpectrum (MvPolynomial σ K),
      q.asIdeal < RingHom.ker (eval z) ∧ Ideal.span (s : Set (MvPolynomial σ K)) ≤ q.asIdeal := by
  obtain ⟨p, hp, hn⟩ := exists_polynomial_eval_prime_chain z
  have hmem (f : MvPolynomial σ K) (hf : f ∈ s) : f ∈ p.last.asIdeal :=
    hp ▸ hs f hf
  obtain ⟨q, hq, hs⟩ := exists_prime_below_end_containing_finite_equations s p hmem (hn ▸ hbudget)
  exact ⟨q, hp ▸ hq, hs⟩

end
end MOC
