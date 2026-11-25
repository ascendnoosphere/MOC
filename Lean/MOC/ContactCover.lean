import MOC.Support
import Mathlib.Analysis.NormedSpace.Connected
import Mathlib.Data.Complex.FiniteDimensional
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Lattice

/-! A contact transfer when one complex gap is a covering projection off
finitely many exceptional values. Path lifting keeps the deformation in the
component of the supplied violation, independently of the curve's genus. -/

open Set

namespace MOC

variable {ι X : Type*} [TopologicalSpace X]

/-- One covering gap reaches negative real part along a path from the
initial point. The minimum real gap therefore vanishes somewhere on that path. -/
theorem exists_new_contact_on_covering (J : Finset ι)
    (H : ι → X → ℂ) (hcont : ∀ j ∈ J, Continuous (H j))
    {i : ι} (hi : i ∈ J) {S : Set ℂ} (hS : S.Finite) (hgood : ∀ x, H i x ∈ Sᶜ)
    (hcover : IsCoveringMap (fun x : X => (⟨H i x, hgood x⟩ : ↥Sᶜ)))
    (x₀ : X) (hstart : ∀ j ∈ J, 0 < (H j x₀).re) :
    ∃ z, (∀ j ∈ J, 0 ≤ (H j z).re) ∧ ∃ j ∈ J, (H j z).re = 0 := by
  obtain ⟨l, hl⟩ := (hS.image Complex.re).bddBelow
  let w : ℂ := ((min l 0 - 1 : ℝ) : ℂ)
  have hwre : w.re < 0 := by
    change min l 0 - 1 < 0
    linarith only [min_le_right l 0]
  have hw : w ∈ Sᶜ := by
    intro h
    have hle : l ≤ w.re := hl ⟨w, h, rfl⟩
    change l ≤ min l 0 - 1 at hle
    linarith only [hle, min_le_left l 0]
  have hrank : 1 < Module.rank ℝ ℂ := by rw [Complex.rank_real_complex]; norm_num
  letI : PathConnectedSpace ↥Sᶜ := isPathConnected_iff_pathConnectedSpace.mp
    (hS.countable.isPathConnected_compl_of_one_lt_rank hrank)
  let p (x : X) : ↥Sᶜ := ⟨H i x, hgood x⟩
  let γ := PathConnectedSpace.somePath (p x₀) (⟨w, hw⟩ : ↥Sᶜ)
  obtain ⟨Γ, hΓ, hΓ₀⟩ := hcover.exists_path_lifts γ.toContinuousMap x₀ γ.source
  have hΓ₁ : H i (Γ 1) = w := by
    have he : p (Γ 1) = (⟨w, hw⟩ : ↥Sᶜ) := (congrFun hΓ (1 : unitInterval)).trans γ.target
    exact congrArg (fun z : ↥Sᶜ => (z : ℂ)) he
  let Jne : J.Nonempty := ⟨i, hi⟩
  let m (z : X) : ℝ := J.inf' Jne (fun j => (H j z).re)
  have hm : Continuous m :=
    Continuous.finset_inf'_apply (f := fun j z => (H j z).re) Jne
      (fun j hj => Complex.continuous_re.comp (hcont j hj))
  have hm₀ : 0 < m (Γ 0) := by
    rw [hΓ₀]
    exact (Finset.lt_inf'_iff Jne).2 hstart
  have hm₁ : m (Γ 1) < 0 :=
    (Finset.inf'_lt_iff Jne).2 ⟨i, hi, by rw [hΓ₁]; exact hwre⟩
  have hconn : IsPreconnected (Set.range Γ) := (isConnected_range Γ.continuous).isPreconnected
  have hz : (0 : ℝ) ∈ m '' (Set.range Γ) :=
    (hconn.image m hm.continuousOn).Icc_subset
      ⟨Γ 1, ⟨1, rfl⟩, rfl⟩ ⟨Γ 0, ⟨0, rfl⟩, rfl⟩ ⟨hm₁.le, hm₀.le⟩
  obtain ⟨z, _, hmz⟩ := hz
  have hnonneg : ∀ j ∈ J, 0 ≤ (H j z).re :=
    (Finset.le_inf'_iff Jne (fun j => (H j z).re)).1 (show 0 ≤ m z from hmz.ge)
  obtain ⟨j, hj, he⟩ := Finset.exists_mem_eq_inf' Jne (fun j => (H j z).re)
  exact ⟨z, hnonneg, j, hj, he.symm.trans hmz⟩

/-- A covering projection given by an inactive matching gap adds a contact
while preserving all old contacts and the fixed determinant support gap. -/
theorem exists_new_matching_contact_on_covering [Fintype ι] [DecidableEq ι]
    (a b : X → ι → ℂ) (U : Matrix ι ι ℂ) (η : ℂ) (r : Equiv.Perm ι)
    (J : Finset (Equiv.Perm ι))
    (hcont : ∀ σ ∈ J, Continuous (fun x =>
      η * (matchingProduct (a x) (b x) r - matchingProduct (a x) (b x) σ)))
    {i : Equiv.Perm ι} (hi : i ∈ J) {S : Set ℂ} (hS : S.Finite)
    (hgood : ∀ x, η * (matchingProduct (a x) (b x) r - matchingProduct (a x) (b x) i) ∈ Sᶜ)
    (hcover : IsCoveringMap (fun x : X =>
      (⟨η * (matchingProduct (a x) (b x) r - matchingProduct (a x) (b x) i), hgood x⟩ : ↥Sᶜ)))
    (hold : ∀ x, ∀ σ ∉ J, matchingGap (a x) (b x) η r σ = 0)
    {g : ℝ} (hg : 0 < g)
    (hgap : ∀ x,
      (η * (determinantValue (a x) (b x) U - matchingProduct (a x) (b x) r)).re = g)
    (x₀ : X) (hstart : ∀ σ ∈ J, 0 < matchingGap (a x₀) (b x₀) η r σ) :
    ∃ z, (∀ σ, 0 ≤ matchingGap (a z) (b z) η r σ) ∧
      (∀ σ ∉ J, matchingGap (a z) (b z) η r σ = 0) ∧
      (∃ σ ∈ J, matchingGap (a z) (b z) η r σ = 0) ∧
      (η * determinantValue (a z) (b z) U).re - (η * matchingProduct (a z) (b z) r).re = g ∧
      ∀ σ, (η * matchingProduct (a z) (b z) σ).re < (η * determinantValue (a z) (b z) U).re := by
  let H (σ : Equiv.Perm ι) (x : X) :=
    η * (matchingProduct (a x) (b x) r - matchingProduct (a x) (b x) σ)
  have hH (σ : Equiv.Perm ι) (x : X) : (H σ x).re = matchingGap (a x) (b x) η r σ := by
    simp only [H, matchingGap, mul_sub, Complex.sub_re]
  obtain ⟨z, hnonneg, j, hj, hjz⟩ :=
    exists_new_contact_on_covering J H hcont hi hS hgood hcover x₀
      (by simpa only [hH] using hstart)
  have hall (σ : Equiv.Perm ι) : 0 ≤ matchingGap (a z) (b z) η r σ := by
    by_cases hσ : σ ∈ J
    · exact (hH σ z) ▸ hnonneg σ hσ
    · exact (hold z σ hσ).ge
  have hg' : (η * determinantValue (a z) (b z) U).re -
      (η * matchingProduct (a z) (b z) r).re = g := by
    simpa only [mul_sub, Complex.sub_re] using hgap z
  have hrlt : (η * matchingProduct (a z) (b z) r).re <
      (η * determinantValue (a z) (b z) U).re := by
    apply sub_pos.mp
    rwa [hg']
  exact ⟨z, hall, hold z, ⟨j, hj, (hH j z).symm.trans hjz⟩, hg',
    fun σ => (sub_nonneg.mp (hall σ)).trans_lt hrlt⟩

end MOC
