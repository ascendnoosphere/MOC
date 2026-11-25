import MOC.MobiusSecondOrder

/-! The centered Möbius moment test can be imposed on a strict witness
while retaining every prescribed contact and the original pivot. -/

open BigOperators Matrix

namespace MOC

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The quartic spectral constraint from the centered second variation. -/
def MobiusMomentBound (a b : ι → ℂ) : Prop :=
  let x : ι ⊕ ι → ℂ := Sum.elim a (fun i => - b i)
  let n := Fintype.card ι
  ‖(2 * (n : ℂ)) * (∑ j, (Complex.normSq (x j) : ℂ) * x j ^ 2) - ∑ j, x j ^ 2‖ ≤
    (n : ℝ) * (∑ j, Complex.normSq (x j) ^ 2) - Complex.normSq (∑ j, x j ^ 2) / 2

/-- Keep all existing contacts and their pivot while selecting a balanced,
moment-tested strict witness at a global unitary support maximum. -/
theorem StrictMatchingSupport.exists_moment_tested_orbit_maximizer
    {U₀ : Matrix ι ι ℂ} (hU₀ : IsUnitary U₀) (w : StrictMatchingSupport U₀) :
    ∃ (U : Matrix ι ι ℂ), IsUnitary U ∧ ∃ v : StrictMatchingSupport U,
      w.contacts ⊆ v.contacts ∧ v.pivot = w.pivot ∧
      spectralEnergy v.a v.b = 1 ∧ Complex.normSq v.η = 1 ∧
      (∑ i, v.a i) = (∑ i, v.b i) ∧
      (∑ i, (Complex.normSq (v.a i) : ℂ) * v.a i) =
        (∑ i, (Complex.normSq (v.b i) : ℂ) * v.b i) ∧
      ¬ IsStarNormal (diagonal v.a + U * diagonal v.b * Uᴴ) ∧
      (∀ V : Matrix ι ι ℂ, IsUnitary V →
        (v.η * determinantValue v.a v.b V).re ≤ (v.η * determinantValue v.a v.b U).re) ∧
      MobiusMomentBound v.a v.b := by
  classical
  obtain ⟨a₀,b₀,k₀,hE₀,hk₀,hsep,hS₀⟩ := w.exists_normalized_retaining_contacts
  obtain ⟨a,b,U,η,g,hU,he,hη,hg,hS,ht,hc,hn,hgap,hmax,hsupp⟩ :=
    exists_balanced_support_gap_maximizer_with_contacts w.contacts a₀ b₀ U₀ k₀ hU₀ hE₀
      hk₀ hsep hS₀
  have hp : w.pivot ∈ w.contacts := by simp [StrictMatchingSupport.contacts]
  have hstrict : (η * matchingProduct a b w.pivot).re < (η * determinantValue a b U).re := by
    have h := hg.trans_le (hgap w.pivot)
    rwa [mul_sub, Complex.sub_re, sub_pos] at h
  let v : StrictMatchingSupport U := ⟨a,b,η,w.pivot,hS w.pivot hp,hstrict⟩
  refine ⟨U,hU,v,?_,rfl,he,hη,ht,hc,hn,hsupp,?_⟩
  · intro q hq
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ q,
      le_antisymm (hS w.pivot hp q) (hS q hq w.pivot)⟩
  · exact spectral_mobius_moment_test_of_contact_gap_maximum w.contacts a b U hU η hη hg
      hS he ht hc hgap (fun c d k hE hk hs => hmax c d U k hE hU hk hs)

end MOC
