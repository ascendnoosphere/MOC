import MOC.KrullPrincipalLocal
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization

/-! A principal equation removes at most one edge from a prime interval. -/
namespace MOC

private theorem prime_eq_bot_of_lt_minimal_principal
    {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (x : R) (p q : Ideal R) [p.IsPrime] [q.IsPrime]
    (hq : q ∈ (Ideal.span ({x} : Set R)).minimalPrimes) (hpq : p < q) : p = ⊥ := by
  let S := Localization.AtPrime q
  let l := algebraMap R S
  let m := IsLocalRing.maximalIdeal S
  let T : Ideal R := Ideal.span ({x} : Set R)
  letI : IsNoetherianRing S := IsLocalization.isNoetherianRing q.primeCompl S inferInstance
  have hmax : m ∈ (T.map l).minimalPrimes := by
    change IsLocalRing.maximalIdeal (Localization.AtPrime q) ∈
      (T.map (algebraMap R (Localization.AtPrime q))).minimalPrimes
    rw [IsLocalization.minimalPrimes_map q.primeCompl (Localization.AtPrime q) T]
    change (IsLocalRing.maximalIdeal (Localization.AtPrime q)).comap
      (algebraMap R (Localization.AtPrime q)) ∈ T.minimalPrimes
    rwa [Localization.AtPrime.comap_maximalIdeal]
  have hradM : (T.map l).radical = m := by
    apply le_antisymm (hmax.1.1.radical_le_iff.mpr hmax.1.2)
    rw [Ideal.radical_eq_sInf, le_sInf_iff]
    rintro Q ⟨hQ, hprime⟩
    exact hmax.2 ⟨hprime,hQ⟩ (IsLocalRing.le_maximalIdeal hprime.ne_top)
  have hrad : (Ideal.span ({l x} : Set S)).radical = m := by
    simpa only [T, Ideal.map_span, Set.image_singleton] using hradM
  have hdis : Disjoint (q.primeCompl : Set R) (p : Set R) :=
    Set.disjoint_left.mpr fun _ ha hb => ha (hpq.le hb)
  letI : (p.map l).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint q.primeCompl S p inferInstance hdis
  have hmp : (p.map l).comap l = p :=
    IsLocalization.comap_map_of_isPrime_disjoint q.primeCompl S p inferInstance hdis
  have hmq : m.comap l = q := Localization.AtPrime.comap_maximalIdeal (I := q)
  have hlt : p.map l < m := by
    apply lt_of_le_of_ne (IsLocalRing.le_maximalIdeal (inferInstance : (p.map l).IsPrime).ne_top)
    intro h
    exact (ne_of_lt hpq) (hmp.symm.trans ((congrArg (Ideal.comap l) h).trans hmq))
  have hz := prime_eq_bot_of_lt_maximal_of_radical_principal (l x) hrad (p.map l) hlt
  apply le_antisymm _ bot_le
  intro y hy
  have hly : l y = 0 := Ideal.mem_bot.mp (hz ▸ Ideal.mem_map_of_mem l hy)
  exact Ideal.mem_bot.mpr ((IsLocalization.injective S q.primeCompl_le_nonZeroDivisors)
    (hly.trans l.map_zero.symm))

/-- If q is minimal over the prime ideal p plus one equation, no
prime ideal lies strictly between p and q. -/
theorem not_prime_between_of_minimal_prime_sup_principal
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    (x : R) (p q r : Ideal R) [p.IsPrime] [q.IsPrime] [r.IsPrime]
    (hq : q ∈ (p ⊔ Ideal.span ({x} : Set R)).minimalPrimes) (hpr : p < r) (hrq : r < q) :
    False := by
  let S := R ⧸ p
  let g := Ideal.Quotient.mk p
  have hg : Function.Surjective g := Ideal.Quotient.mk_surjective
  have hker : RingHom.ker g = p := Ideal.mk_ker
  have hqker : RingHom.ker g ≤ q := hker.trans_le (hpr.le.trans hrq.le)
  have hrker : RingHom.ker g ≤ r := hker.trans_le hpr.le
  letI : (q.map g).IsPrime := Ideal.map_isPrime_of_surjective hg hqker
  letI : (r.map g).IsPrime := Ideal.map_isPrime_of_surjective hg hrker
  have hqcomap : (q.map g).comap g = q := by
    rw [Ideal.comap_map_of_surjective _ hg, ← RingHom.ker_eq_comap_bot, hker,
      sup_eq_left.mpr (hpr.le.trans hrq.le)]
  have hrcomap : (r.map g).comap g = r := by
    rw [Ideal.comap_map_of_surjective _ hg, ← RingHom.ker_eq_comap_bot, hker, sup_eq_left.mpr hpr.le]
  have hmin : q.map g ∈ (Ideal.span ({g x} : Set S)).minimalPrimes := by
    have hxq : x ∈ q := hq.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    refine ⟨⟨inferInstance, Ideal.span_le.mpr (Set.singleton_subset_iff.mpr
      (Ideal.mem_map_of_mem g hxq))⟩, ?_⟩
    intro J hJ hle
    have hpx : p ⊔ Ideal.span ({x} : Set R) ≤ J.comap g := by
      apply sup_le
      · exact hker.symm.trans_le (Ideal.ker_le_comap g)
      · exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (hJ.2 (Ideal.mem_span_singleton_self _)))
    have hqj : q ≤ J.comap g :=
      hq.2 ⟨hJ.1.comap g, hpx⟩ ((Ideal.comap_mono hle).trans_eq hqcomap)
    exact Ideal.map_le_iff_le_comap.mpr hqj
  have hlt : r.map g < q.map g := by
    apply lt_of_le_of_ne (Ideal.map_mono hrq.le)
    intro he
    exact (ne_of_lt hrq) (hrcomap.symm.trans ((congrArg (Ideal.comap g) he).trans hqcomap))
  have hz := prime_eq_bot_of_lt_minimal_principal (g x) (r.map g) (q.map g) hmin hlt
  exact (ne_of_lt hpr) (hker.symm.trans ((congrArg (Ideal.comap g) hz).symm.trans hrcomap))

end MOC
