import MOC.ContactIteration
import MOC.GeneralContactReduction

/-! A supplied fixed-gap curve gives the strict increase used in finite
contact iteration. No existence of the geometric curve is assumed globally. -/

open Matrix Set
open scoped Manifold

namespace MOC

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Increase the number of contacts, keeping the same mixer, on any
supplied infinite profile curve with the old differences and determinant
gap fixed. The curve need not provide holomorphic lifts of the spectra. -/
theorem StrictMatchingSupport.exists_more_contacts_of_curve
    {U : Matrix ι ι ℂ} (hU : IsUnitary U) (w : StrictMatchingSupport U)
    {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) 1 X] [CompactSpace X] [ConnectedSpace X]
    {S : Set X} (hS : S.Finite) (hconn : IsPreconnected Sᶜ)
    (P : X → Equiv.Perm ι → ℂ)
    (hexact : ∀ x ∈ Sᶜ, ∃ a b : ι → ℂ, matchingProduct a b = P x)
    (hhol : ∀ σ, MDifferentiableOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
      (fun x => w.η * (P x w.pivot - P x σ)) Sᶜ)
    {x₀ : X} (hx₀ : x₀ ∈ Sᶜ) (hbase : P x₀ = matchingProduct w.a w.b)
    (hold : ∀ x ∈ Sᶜ, ∀ σ ∈ w.contacts,
      P x w.pivot - P x σ = P x₀ w.pivot - P x₀ σ)
    (hgap : ∀ x ∈ Sᶜ, matchingProfileDetGap U w.η w.pivot (P x) =
      matchingProfileDetGap U w.η w.pivot (P x₀))
    (hinf : (P '' Sᶜ).Infinite) :
    ∃ w' : StrictMatchingSupport U, w.contacts ⊂ w'.contacts := by
  classical
  let J : Finset (Equiv.Perm ι) := w.contactsᶜ
  have hold' (x) (hx : x ∈ Sᶜ) (σ) (hσ : σ ∉ J) :
      P x w.pivot - P x σ = P x₀ w.pivot - P x₀ σ :=
    hold x hx σ (by simpa [J] using hσ)
  have htime (σ) :
      (w.η * (P x₀ w.pivot - P x₀ σ)).re =
      (w.η * matchingProduct w.a w.b w.pivot).re -
        (w.η * matchingProduct w.a w.b σ).re := by
    rw [hbase, mul_sub, Complex.sub_re]
  have hzero (σ) (hσ : σ ∉ J) : (w.η * (P x₀ w.pivot - P x₀ σ)).re = 0 := by
    have hc : σ ∈ w.contacts := by simpa [J] using hσ
    rw [htime, sub_eq_zero]
    exact (Finset.mem_filter.mp hc).2.symm
  have hstart (σ) (hσ : σ ∈ J) : 0 < (w.η * (P x₀ w.pivot - P x₀ σ)).re := by
    rw [htime]
    apply sub_pos.mpr
    refine lt_of_le_of_ne (w.maximal σ) ?_
    intro he
    exact (Finset.mem_compl.mp hσ) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩)
  have hstrict : 0 < (matchingProfileDetGap U w.η w.pivot (P x₀)).re := by
    rw [hbase, matchingProfileDetGap_matchingProduct w.a w.b U hU, mul_sub, Complex.sub_re]
    exact sub_pos.mpr w.strict
  obtain ⟨z, _, a, b, _, hnonneg, hzero', ⟨j, hj, hj0⟩, hviolate⟩ :=
    exists_strictly_violating_profile_with_more_contacts_of_infinite_image hS hconn P
      U hU w.η w.pivot J hexact (fun σ _ => hhol σ) hx₀ hold' hzero hgap hstrict hstart hinf
  let w' : StrictMatchingSupport U := ⟨a, b, w.η, w.pivot,
    fun σ => sub_nonneg.mp (hnonneg σ), hviolate w.pivot⟩
  have heq (σ) (hσ : matchingGap a b w.η w.pivot σ = 0) : σ ∈ w'.contacts := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    exact (sub_eq_zero.mp hσ).symm
  refine ⟨w', Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩⟩
  · intro σ hσ
    exact heq σ (hzero' σ (by simpa [J] using hσ))
  · intro he
    exact (Finset.mem_compl.mp hj) (he ▸ heq j hj0)

end MOC
