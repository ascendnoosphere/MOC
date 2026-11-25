import MOC.ContactFibreIsolation

/-! Local isolation gives a derivative-free obstruction to a free spectral
entry: an active contact difference or the determinant gap must detect
every entry which changes the profile. -/

open Matrix MvPolynomial Set

namespace MOC

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Coefficient of the free partner entry in one matching product. -/
def matchingEntrySlope (a b : ι → ℂ) (j : ι) (q : Equiv.Perm ι) : ℂ :=
  ∏ k ∈ Finset.univ.erase j, (a (q k) + b k)

theorem matchingProduct_update_partner (a b : ι → ℂ) (j : ι) (z : ℂ) (q : Equiv.Perm ι) :
    matchingProduct a (Function.update b j z) q =
      (a (q j) + z) * matchingEntrySlope a b j q := by
  unfold matchingProduct matchingEntrySlope
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j), Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  rw [Function.update_of_ne (Finset.mem_erase.mp hk).1]

/-- At a contact-maximal witness, every nonconstant free-entry pencil
changes some old complex pivot difference or the full complex gap.
This is an exact statement about slopes, not a generic Jacobian test. -/
theorem StrictMatchingSupport.contact_or_gap_detects_partner_entry
    {U : Matrix ι ι ℂ} (hU : IsUnitary U) (w : StrictMatchingSupport U)
    (hmax : ∀ v : StrictMatchingSupport U, v.contacts.card ≤ w.contacts.card)
    (j : ι) :
    (∃ q ∈ w.contacts, matchingEntrySlope w.a w.b j w.pivot ≠
      matchingEntrySlope w.a w.b j q) ∨
      matchingProfileDetGap U w.η w.pivot (matchingEntrySlope w.a w.b j) ≠ 0 := by
  classical
  let s := matchingEntrySlope w.a w.b j
  let f (z : ℂ) := matchingProduct w.a (Function.update w.b j z)
  have hbase : f (w.b j) = matchingProduct w.a w.b := by simp [f]
  have hchange : ∃ q, s q ≠ 0 := by
    have hprod : ∃ q, matchingProduct w.a w.b q ≠ 0 := by
      by_contra! hzero
      have hdet := real_signed_determinant w.a w.b U hU
      simp only [hzero, mul_zero, Finset.sum_const_zero] at hdet
      have hbad := w.strict
      rw [← hdet, hzero] at hbad
      simpa using hbad
    obtain ⟨q, hq⟩ := hprod
    refine ⟨q, ?_⟩
    intro hzero
    apply hq
    rw [← congrFun hbase q]
    change matchingProduct w.a (Function.update w.b j (w.b j)) q = 0
    rw [matchingProduct_update_partner, show matchingEntrySlope w.a w.b j q = 0 from hzero, mul_zero]
  have hline (z : ℂ) (q : Equiv.Perm ι) :
      f z q = matchingProduct w.a w.b q + (z - w.b j) * s q := by
    have h₀ := congrFun hbase q
    simp only [f, matchingProduct_update_partner] at h₀ ⊢
    rw [← h₀]
    dsimp only [s]
    ring
  by_cases hc : ∃ q ∈ w.contacts, s w.pivot ≠ s q
  · exact Or.inl hc
  refine Or.inr ?_
  intro hg
  have hs (q : Equiv.Perm ι) (hq : q ∈ w.contacts) : s w.pivot = s q :=
    not_not.mp (fun hne => hc ⟨q, hq, hne⟩)
  have hfibre (z : ℂ) : f z ∈ zeroLocus w.contactFibreIdeal := by
    refine (w.mem_contactFibre_iff _).mpr ⟨?_, ?_, ?_⟩
    · rw [← profileIdeal_exact]
      exact ⟨w.a, Function.update w.b j z, rfl⟩
    · intro q hq
      rw [hline z w.pivot, hline z q, hs q hq]
      ring
    · have h :
          matchingProfileDetGap U w.η w.pivot (f z) -
            matchingProfileDetGap U w.η w.pivot (matchingProduct w.a w.b) =
            (z - w.b j) * matchingProfileDetGap U w.η w.pivot s := by
        simp only [matchingProfileDetGap]
        rw [← Finset.sum_sub_distrib, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q _
        rw [hline z w.pivot, hline z q]
        ring
      rw [hg, mul_zero, sub_eq_zero] at h
      exact h
  obtain ⟨O, hO, hz, hOnly⟩ := w.exists_isolating_open_of_max_contacts hU hmax
  have hcont : Continuous f := continuous_pi fun q => by
    simp_rw [hline]
    fun_prop
  have hopen := hO.preimage hcont
  have hz' : w.b j ∈ f ⁻¹' O := by
    change f (w.b j) ∈ O
    rwa [hbase]
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen (w.b j) hz'
  let z := w.b j + ((ε / 2 : ℝ) : ℂ)
  have hzb : z ∈ Metric.ball (w.b j) ε := by
    rw [Metric.mem_ball, dist_eq_norm]
    dsimp only [z]
    rw [add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    linarith
  have hzm : f z ∈ O ∩ zeroLocus w.contactFibreIdeal := ⟨hball hzb, hfibre z⟩
  have he : f z = matchingProduct w.a w.b := by
    rw [hOnly] at hzm
    exact Set.mem_singleton_iff.mp hzm
  obtain ⟨q, hq⟩ := hchange
  have hzero : (z - w.b j) * s q = 0 := by
    have h := hline z q
    rw [he] at h
    exact add_eq_left.mp h.symm
  apply hq ((mul_eq_zero.mp hzero).resolve_left ?_)
  dsimp only [z]
  rw [add_sub_cancel_left]
  exact Complex.ofReal_ne_zero.mpr (by positivity)

end MOC
