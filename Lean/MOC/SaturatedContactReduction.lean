import MOC.ContactChartIteration
import MOC.FiniteCurveAtPinnedPrime
import MOC.PolynomialContactSlice

/-! Contact raising inside the nonzero normalized chart. The fixed-gap
contact strategy follows Zheng, Theorem 3.6, DOI: 10.13140/RG.2.2.36790.25923.
The dimension, curve, and transfer arguments here hold in every finite order. -/

open Matrix MvPolynomial

namespace MOC

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Below the contact threshold, a strict witness with no zero matching
product acquires another contact for the same mixer. No matching
product vanishes at the new witness, so the step can be iterated. -/
theorem StrictMatchingSupport.exists_more_contacts_nonzero
    {U : Matrix ι ι ℂ} (hU : IsUnitary U) (w : StrictMatchingSupport U)
    (hnz : ∀ q, matchingProduct w.a w.b q ≠ 0)
    (hk : w.contacts.card < 2 * Fintype.card ι - 2) :
    ∃ v : StrictMatchingSupport U, w.contacts ⊂ v.contacts ∧
      ∀ q, matchingProduct v.a v.b q ≠ 0 := by
  classical
  have hNonempty : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨o⟩ := hNonempty
  obtain ⟨i₀, j₀, z, I, hi, hz, hI, hspan⟩ :=
    PolynomialContactChart.exists_initial_prime_contact_slice hU w o hnz hk
  obtain ⟨g, _, hg⟩ := SetLike.exists_of_lt hI
  obtain ⟨Q, hIQ, hQz, hQprime, _, f, hf, hfi, t, ht⟩ :=
    @exists_finite_affine_curve_from_prime_below_point
      (PolynomialContactChart.VarLocalized o i₀) inferInstance z I.asIdeal I.isPrime hI g hg
  letI : Q.IsPrime := hQprime
  let z₀ : zeroLocus Q := ⟨z, fun p hp => hQz hp⟩
  have hS := hspan.trans hIQ
  have hcurve : Infinite (zeroLocus Q) := Infinite.of_surjective _
    (surjective_finite_affine_projection Q f hf hfi t ht)
  letI := hcurve
  have hins := PolynomialContactChart.localProfile_on_slice hi w Q hS
  have hr (q) (hq : q ∈ w.contacts) :
      PolynomialContactChart.liftedProfile o i₀ w.pivot -
        PolynomialContactChart.liftedProfile o i₀ q -
        C (eval z₀.val (PolynomialContactChart.liftedProfile o i₀ w.pivot) -
          eval z₀.val (PolynomialContactChart.liftedProfile o i₀ q)) ∈ Q := by
    rw [PolynomialContactChart.eval_liftedProfile, PolynomialContactChart.eval_liftedProfile]
    change _ - C (PolynomialContactChart.localProfile o i₀ z w.pivot -
      PolynomialContactChart.localProfile o i₀ z q) ∈ Q
    rw [hz]
    exact PolynomialContactChart.contact_mem_of_span_le o i₀ j₀ w Q hS q hq
  have hG : PolynomialContactChart.gapEquation o i₀ w ∈ Q :=
    hS (Ideal.subset_span (PolynomialContactChart.gap_mem_equations o i₀ j₀ w))
  obtain ⟨v, hv, y, hy⟩ := w.exists_more_contacts_on_affine_constraints
    hU Q f hf hfi t ht (PolynomialContactChart.liftedProfile o i₀) z₀ hz
    hins.1 hr hG (Set.infinite_range_of_injective hins.2)
  have hInv : PolynomialContactChart.inverseEquation o i₀ j₀ ∈ Q :=
    hS (Ideal.subset_span (PolynomialContactChart.inverse_mem_equations o i₀ j₀ w))
  refine ⟨v, hv, fun q => ?_⟩
  rw [hy]
  exact (PolynomialContactChart.permitted_of_inverse y.val (y.property _ hInv)).2 q

/-- Every nonzero matching profile at the contact threshold satisfies its
support inequality. This states the remaining terminal problem. -/
def ContactSaturatedBound (ι : Type*) [Fintype ι] [DecidableEq ι] : Prop :=
  ¬ ∃ (U : Matrix ι ι ℂ), IsUnitary U ∧
    ∃ w : StrictMatchingSupport U, 2 * Fintype.card ι - 2 ≤ w.contacts.card ∧
      ∀ q, matchingProduct w.a w.b q ≠ 0

/-- The full conjecture is equivalent to the terminal support bound.
A single strict witness in that bound refutes MOC. -/
theorem conjecture_iff_contact_saturated_bound :
    Conjecture ι ↔ ContactSaturatedBound ι :=
  conjecture_iff_no_nonzero_terminal_witness _ fun _ hU w hnz hk =>
    w.exists_more_contacts_nonzero hU hnz hk

end MOC
