import MOC.KrullPrincipalRelative
import Mathlib.Order.RelSeries
import Mathlib.RingTheory.Spectrum.Prime.Basic

/-! Generator bounds from the relative principal ideal theorem.
A cut shortens a specified prime chain by at most one edge. -/

namespace MOC

variable {R : Type*} [CommRing R] [IsNoetherianRing R]

private theorem exists_prime_between_containing
    (x : R) (p q t : PrimeSpectrum R) (hpq : p < q) (hqt : q < t)
    (ht : x ∈ t.asIdeal) (hq : x ∉ q.asIdeal) :
    ∃ r : PrimeSpectrum R, p < r ∧ r < t ∧ x ∈ r.asIdeal := by
  let I := p.asIdeal ⊔ Ideal.span ({x} : Set R)
  have htI : I ≤ t.asIdeal := sup_le (hpq.trans hqt).le
    (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ht))
  obtain ⟨J, hJI, hJt⟩ := Ideal.exists_minimalPrimes_le htI
  let r : PrimeSpectrum R := ⟨J, hJI.1.1⟩
  have hxr : x ∈ r.asIdeal := hJI.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  have hpr : p < r := by
    apply lt_of_le_of_ne (le_sup_left.trans hJI.1.2)
    intro he
    exact hq (hpq.le (he.symm ▸ hxr))
  have hrt : r < t := by
    apply lt_of_le_of_ne hJt
    intro he
    have hm : t.asIdeal ∈ I.minimalPrimes := by
      rw [← he]
      exact hJI
    exact not_prime_between_of_minimal_prime_sup_principal x p.asIdeal t.asIdeal q.asIdeal
      hm hpq hqt
  exact ⟨r, hpr, hrt, hxr⟩

/-- One equation through the endpoint of a prime chain can be imposed
throughout a new chain ending there, losing at most one strict edge.
The new head still dominates the old head. -/
theorem exists_prime_chain_after_one_equation
    (x : R) (p : LTSeries (PrimeSpectrum R)) (hx : x ∈ p.last.asIdeal) :
    ∃ q : LTSeries (PrimeSpectrum R), q.last = p.last ∧ p.head ≤ q.head ∧
      (∀ y ∈ q, x ∈ y.asIdeal) ∧ p.length ≤ q.length + 1 := by
  have H (n : ℕ) : ∀ p : LTSeries (PrimeSpectrum R), p.length = n →
      x ∈ p.last.asIdeal →
      ∃ q : LTSeries (PrimeSpectrum R), q.last = p.last ∧ p.head ≤ q.head ∧
        (∀ y ∈ q, x ∈ y.asIdeal) ∧ p.length ≤ q.length + 1 := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro p hlen hx
      by_cases hn : n ≤ 1
      · refine ⟨RelSeries.singleton (· < ·) p.last, rfl, p.head_le_last, ?_, ?_⟩
        · intro y hy
          obtain ⟨i, rfl⟩ := hy
          exact hx
        · simpa [hlen] using hn
      · let s := p.eraseLast
        have hslen : s.length = n - 1 := by simp [s, hlen]
        have hslt : s.last < p.last := p.eraseLast_last_rel_last (by omega)
        by_cases hsx : x ∈ s.last.asIdeal
        · obtain ⟨r, hlast, hhead, hmem, hrlen⟩ := ih s.length (by omega) s rfl hsx
          have hlt : r.last < p.last := hlast ▸ hslt
          refine ⟨r.snoc p.last hlt, by simp, ?_, ?_, ?_⟩
          · simpa [s] using hhead
          · intro y hy
            rcases RelSeries.mem_snoc.mp hy with hy | rfl
            · exact hmem y hy
            · exact hx
          · simp only [RelSeries.snoc_length]
            omega
        · let t := s.eraseLast
          have htlen : t.length = n - 2 := by simp [t, hslen]; omega
          have hts : t.last < s.last := s.eraseLast_last_rel_last (by omega)
          obtain ⟨z, htz, hzp, hzx⟩ := exists_prime_between_containing x t.last s.last p.last
            hts hslt hx hsx
          let u := t.snoc z htz
          have hulen : u.length = n - 1 := by simp [u, htlen]; omega
          have hux : x ∈ u.last.asIdeal := by simpa [u] using hzx
          obtain ⟨r, hlast, hhead, hmem, hrlen⟩ := ih u.length (by omega) u rfl hux
          have hlt : r.last < p.last := by rw [hlast, RelSeries.last_snoc]; exact hzp
          refine ⟨r.snoc p.last hlt, by simp, ?_, ?_, ?_⟩
          · simpa [u, t, s] using hhead
          · intro y hy
            rcases RelSeries.mem_snoc.mp hy with hy | rfl
            · exact hmem y hy
            · exact hx
          · simp only [RelSeries.snoc_length]
            omega
  exact H p.length p rfl hx

/-- A set of equations through the endpoint of a prime chain costs at most
its cardinality in strict edges. -/
theorem exists_prime_chain_after_finite_equations
    (s : Finset R) (p : LTSeries (PrimeSpectrum R)) (hs : ∀ x ∈ s, x ∈ p.last.asIdeal) :
    ∃ q : LTSeries (PrimeSpectrum R), q.last = p.last ∧ p.head ≤ q.head ∧
      (∀ y ∈ q, ∀ x ∈ s, x ∈ y.asIdeal) ∧ p.length ≤ q.length + s.card := by
  classical
  induction s using Finset.induction_on generalizing p with
  | empty => exact ⟨p, rfl, le_rfl, by simp, by simp⟩
  | insert x s hxs ih =>
    obtain ⟨q, hq₁, hq₂, hq₃, hq₄⟩ := ih p (fun y hy => hs y (Finset.mem_insert_of_mem hy))
    have hx : x ∈ q.last.asIdeal := hq₁.symm ▸ hs x (Finset.mem_insert_self x s)
    obtain ⟨r, hr₁, hr₂, hr₃, hr₄⟩ := exists_prime_chain_after_one_equation x q hx
    refine ⟨r, hr₁.trans hq₁, hq₂.trans hr₂, ?_, ?_⟩
    · intro y hy z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hr₃ y hy
      · obtain ⟨i, rfl⟩ := hy
        have hle : r.head ≤ r i := r.monotone (Fin.zero_le _)
        exact (hr₂.trans hle) (hq₃ q.head ⟨0, rfl⟩ z hz)
    · rw [Finset.card_insert_of_not_mem hxs]
      omega

/-- A chain with more edges than equations supplies a strictly smaller
prime through the pinned endpoint on which every equation vanishes. -/
theorem exists_prime_below_end_containing_finite_equations
    (s : Finset R) (p : LTSeries (PrimeSpectrum R)) (hs : ∀ x ∈ s, x ∈ p.last.asIdeal)
    (hbudget : s.card < p.length) :
    ∃ q : PrimeSpectrum R, q < p.last ∧ Ideal.span (s : Set R) ≤ q.asIdeal := by
  obtain ⟨r, hr₁, _, hr₃, hr₄⟩ := exists_prime_chain_after_finite_equations s p hs
  have hrlen : r.length ≠ 0 := by omega
  have hlt : r.eraseLast.last < r.last := r.eraseLast_last_rel_last hrlen
  refine ⟨r.eraseLast.last, hlt.trans_eq hr₁, Ideal.span_le.mpr ?_⟩
  have hm : r.eraseLast.last ∈ r := by
    rw [RelSeries.last_eraseLast]
    exact ⟨_, rfl⟩
  exact fun x hx => hr₃ _ hm x hx

end MOC
