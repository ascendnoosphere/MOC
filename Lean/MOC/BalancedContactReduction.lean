import MOC.GlobalContactSlice
import MOC.SpectralGap

/-! A terminal contact set can be retained while choosing a balanced witness
whose mixer maximizes support on its entire unitary orbit. The contact threshold
uses Zheng's fixed-gap strategy (DOI: 10.13140/RG.2.2.36790.25923), extended
to the exact profile locus by `MOC.global_reaches_contact_threshold`. -/

open BigOperators Matrix

namespace MOC

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Keep every existing contact, including its pivot, while choosing a
unit-energy trace- and cubic-balanced strict witness at a unitary support
maximum with a nonnormal sum. There is no nonzero-product premise. -/
theorem StrictMatchingSupport.exists_balanced_orbit_maximizer [Nonempty ι]
    {U₀ : Matrix ι ι ℂ} (hU₀ : IsUnitary U₀) (w : StrictMatchingSupport U₀) :
    ∃ (U : Matrix ι ι ℂ), IsUnitary U ∧ ∃ v : StrictMatchingSupport U,
      w.contacts ⊆ v.contacts ∧ v.pivot = w.pivot ∧
      spectralEnergy v.a v.b = 1 ∧ Complex.normSq v.η = 1 ∧
      (∑ i, v.a i) = (∑ i, v.b i) ∧
      (∑ i, (Complex.normSq (v.a i) : ℂ) * v.a i) =
        (∑ i, (Complex.normSq (v.b i) : ℂ) * v.b i) ∧
      ¬ IsStarNormal (diagonal v.a + U * diagonal v.b * Uᴴ) ∧
      ∀ V : Matrix ι ι ℂ, IsUnitary V →
        (v.η * determinantValue v.a v.b V).re ≤ (v.η * determinantValue v.a v.b U).re := by
  classical
  obtain ⟨a₀,b₀,k₀,hE₀,hk₀,hsep,hS₀⟩ := w.exists_normalized_retaining_contacts
  obtain ⟨a,b,U,η,g,hU,he,hη,hg,hS,ht,hc,hn,hgap,_,hsupp⟩ :=
    exists_balanced_support_gap_maximizer_with_contacts w.contacts a₀ b₀ U₀ k₀ hU₀ hE₀
      hk₀ hsep hS₀
  have hp : w.pivot ∈ w.contacts := by simp [StrictMatchingSupport.contacts]
  have hstrict : (η * matchingProduct a b w.pivot).re < (η * determinantValue a b U).re := by
    have h := hg.trans_le (hgap w.pivot)
    rwa [mul_sub, Complex.sub_re, sub_pos] at h
  let v : StrictMatchingSupport U := ⟨a,b,η,w.pivot,hS w.pivot hp,hstrict⟩
  refine ⟨U,hU,v,?_,rfl,he,hη,ht,hc,hn,hsupp⟩
  intro q hq
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ q,
    le_antisymm (hS w.pivot hp q) (hS q hq w.pivot)⟩

/-- The unrestricted conjecture is equivalent to ruling out terminal
witnesses that are simultaneously balanced and orbit-maximal. -/
theorem conjecture_iff_balanced_global_contact_bound [Nonempty ι] :
    Conjecture ι ↔ ¬ ∃ (U : Matrix ι ι ℂ), IsUnitary U ∧ ∃ v : StrictMatchingSupport U,
      2 * Fintype.card ι - 2 ≤ v.contacts.card ∧
      spectralEnergy v.a v.b = 1 ∧ Complex.normSq v.η = 1 ∧
      (∑ i, v.a i) = (∑ i, v.b i) ∧
      (∑ i, (Complex.normSq (v.a i) : ℂ) * v.a i) =
        (∑ i, (Complex.normSq (v.b i) : ℂ) * v.b i) ∧
      ¬ IsStarNormal (diagonal v.a + U * diagonal v.b * Uᴴ) ∧
      ∀ V : Matrix ι ι ℂ, IsUnitary V →
        (v.η * determinantValue v.a v.b V).re ≤ (v.η * determinantValue v.a v.b U).re := by
  rw [conjecture_iff_global_contact_bound]
  constructor
  · rintro h ⟨U, hU, v, hcard, _⟩
    exact h ⟨U, hU, v, hcard⟩
  · rintro h ⟨U, hU, w, hcard⟩
    obtain ⟨V,hV,v,hsub,_,hunit,hη,htrace,hcubic,hn,hsup⟩ := w.exists_balanced_orbit_maximizer hU
    exact h ⟨V,hV,v,hcard.trans (Finset.card_le_card hsub),hunit,hη,htrace,hcubic,hn,hsup⟩

end MOC
