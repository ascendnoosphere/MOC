import MOC.ContactCurveStep
import MOC.FiniteCurveClosure

/-! A connected space of exact profiles gives the contact step by a
real intermediate value argument. It need not be a complex manifold. -/

open Matrix Set Polynomial

namespace MOC

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Keep the old contacts and a strict determinant gap along a connected
family. A negative matching gap anywhere in the family then forces an
additional contact, with the mixer unchanged. -/
theorem StrictMatchingSupport.exists_more_contacts_on_connected_profiles
    {U : Matrix ι ι ℂ} (hU : IsUnitary U) (w : StrictMatchingSupport U)
    {X : Type*} [TopologicalSpace X] {S : Set X} (hconn : IsPreconnected S)
    (P : X → Equiv.Perm ι → ℂ)
    (hexact : ∀ x ∈ S, ∃ a b : ι → ℂ, matchingProduct a b = P x)
    (hc : ∀ q, ContinuousOn (fun x => (w.η * (P x w.pivot - P x q)).re) S)
    {x₀ : X} (hx₀ : x₀ ∈ S) (hbase : P x₀ = matchingProduct w.a w.b)
    (hold : ∀ x ∈ S, ∀ q ∈ w.contacts, (w.η * (P x w.pivot - P x q)).re = 0)
    (hgap : ∀ x ∈ S, 0 < (matchingProfileDetGap U w.η w.pivot (P x)).re)
    (hneg : ∃ x ∈ S, ∃ q, (w.η * (P x w.pivot - P x q)).re < 0) :
    ∃ w' : StrictMatchingSupport U, w.contacts ⊂ w'.contacts ∧
      ∃ z ∈ S, matchingProduct w'.a w'.b = P z := by
  classical
  let J : Finset (Equiv.Perm ι) := w.contactsᶜ
  let H (q : Equiv.Perm ι) (x : X) := (w.η * (P x w.pivot - P x q)).re
  obtain ⟨y, hy, q, hq⟩ := hneg
  have hqJ : q ∈ J := Finset.mem_compl.mpr fun h =>
    (not_lt_of_ge (hold y hy q h).ge) hq
  let jn : J.Nonempty := ⟨q, hqJ⟩
  let m (x : X) := J.inf' jn (fun q => H q x)
  have hm : ContinuousOn m S :=
    ContinuousOn.finset_inf'_apply (f := H) jn fun q _ => hc q
  have hm0 : 0 < m x₀ := by
    apply (Finset.lt_inf'_iff jn).mpr
    intro q hq
    change 0 < H q x₀
    dsimp only [H]
    rw [hbase, mul_sub, Complex.sub_re]
    apply sub_pos.mpr
    refine lt_of_le_of_ne (w.maximal q) ?_
    intro he
    exact (Finset.mem_compl.mp hq) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩)
  have hmy : m y < 0 := (Finset.inf'_lt_iff jn).mpr ⟨q, hqJ, hq⟩
  obtain ⟨z, hz, hmz⟩ := (hconn.image _ hm).Icc_subset
    ⟨y, hy, rfl⟩ ⟨x₀, hx₀, rfl⟩ ⟨hmy.le, hm0.le⟩
  obtain ⟨a, b, he⟩ := hexact z hz
  have hH (q) : H q z =
      (w.η * matchingProduct a b w.pivot).re - (w.η * matchingProduct a b q).re := by
    simp [H, ← he, mul_sub, Complex.sub_re]
  have hmax (q) : (w.η * matchingProduct a b q).re ≤
      (w.η * matchingProduct a b w.pivot).re := by
    apply sub_nonneg.mp
    rw [← hH]
    by_cases hq : q ∈ w.contacts
    · exact (hold z hz q hq).ge
    · exact (Finset.le_inf'_iff jn (fun q => H q z)).mp hmz.ge q (Finset.mem_compl.mpr hq)
  have hg := hgap z hz
  rw [← he, matchingProfileDetGap_matchingProduct a b U hU, mul_sub, Complex.sub_re] at hg
  let w' : StrictMatchingSupport U := ⟨a, b, w.η, w.pivot, hmax, sub_pos.mp hg⟩
  have hmem (q) (hq : H q z = 0) : q ∈ w'.contacts :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, (sub_eq_zero.mp ((hH q).symm.trans hq)).symm⟩
  obtain ⟨j, hj, hj0⟩ := Finset.exists_mem_eq_inf' jn (fun q => H q z)
  have hj' := hmem j (hj0.symm.trans hmz)
  refine ⟨w', Finset.ssubset_iff_subset_ne.mpr
    ⟨fun q hq => hmem q (hold z hz q hq), ?_⟩, z, hz, he⟩
  intro heq
  exact Finset.mem_compl.mp hj (heq ▸ hj')

/-- The contact step without recording the point on the profile family. -/
theorem StrictMatchingSupport.exists_more_contacts_of_connected_profiles
    {U : Matrix ι ι ℂ} (hU : IsUnitary U) (w : StrictMatchingSupport U)
    {X : Type*} [TopologicalSpace X] {S : Set X} (hconn : IsPreconnected S)
    (P : X → Equiv.Perm ι → ℂ)
    (hexact : ∀ x ∈ S, ∃ a b : ι → ℂ, matchingProduct a b = P x)
    (hc : ∀ q, ContinuousOn (fun x => (w.η * (P x w.pivot - P x q)).re) S)
    {x₀ : X} (hx₀ : x₀ ∈ S) (hbase : P x₀ = matchingProduct w.a w.b)
    (hold : ∀ x ∈ S, ∀ q ∈ w.contacts, (w.η * (P x w.pivot - P x q)).re = 0)
    (hgap : ∀ x ∈ S, 0 < (matchingProfileDetGap U w.η w.pivot (P x)).re)
    (hneg : ∃ x ∈ S, ∃ q, (w.η * (P x w.pivot - P x q)).re < 0) :
    ∃ w' : StrictMatchingSupport U, w.contacts ⊂ w'.contacts := by
  obtain ⟨v, hv, -⟩ := w.exists_more_contacts_on_connected_profiles
    hU hconn P hexact hc hx₀ hbase hold hgap hneg
  exact ⟨v, hv⟩

/-- A monic irreducible plane model suffices when a varying gap is the base
coordinate. The proof applies even if the initial point is over an
exceptional fibre. The model and its exact profile map are supplied. -/
theorem StrictMatchingSupport.exists_more_contacts_of_plane_profiles
    {U : Matrix ι ι ℂ} (hU : IsUnitary U) (w : StrictMatchingSupport U)
    (Q : ℂ[X][X]) (hm : Q.Monic) (hirr : Irreducible Q)
    (P : ℂ × ℂ → Equiv.Perm ι → ℂ) (q : Equiv.Perm ι)
    (z₀ : ℂ × ℂ)
    (h₀ : (Q.map (evalRingHom z₀.1)).IsRoot z₀.2)
    (hbase : P z₀ = matchingProduct w.a w.b)
    (hexact : ∀ z, (Q.map (evalRingHom z.1)).IsRoot z.2 →
      ∃ a b : ι → ℂ, matchingProduct a b = P z)
    (hc : ∀ r, ContinuousOn (fun z => (w.η * (P z w.pivot - P z r)).re)
      {z : ℂ × ℂ | (Q.map (evalRingHom z.1)).IsRoot z.2})
    (hold : ∀ z, (Q.map (evalRingHom z.1)).IsRoot z.2 → ∀ r ∈ w.contacts,
      (w.η * (P z w.pivot - P z r)).re = 0)
    (hgap : ∀ z, (Q.map (evalRingHom z.1)).IsRoot z.2 →
      0 < (matchingProfileDetGap U w.η w.pivot (P z)).re)
    (hcoord : ∀ z, (Q.map (evalRingHom z.1)).IsRoot z.2 →
      w.η * (P z w.pivot - P z q) = z.1) :
    ∃ w' : StrictMatchingSupport U, w.contacts ⊂ w'.contacts := by
  apply w.exists_more_contacts_of_connected_profiles hU
    (isConnected_plane_curve_of_monic_irreducible Q hm hirr).isPreconnected
    P hexact hc h₀ hbase hold hgap
  let t : ℂ := -1
  let R := Q.map (evalRingHom t)
  have hm' : R.Monic := hm.map _
  have hd : R.degree ≠ 0 := by
    rw [degree_eq_natDegree hm'.ne_zero, hm.natDegree_map]
    exact fun h => hirr.not_isUnit ((hm.natDegree_eq_zero_iff_eq_one.mp (by exact_mod_cast h)) ▸
      isUnit_one)
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root R hd
  refine ⟨(t, y), hy, q, ?_⟩
  rw [hcoord (t, y) hy]
  simp [t]

end MOC
