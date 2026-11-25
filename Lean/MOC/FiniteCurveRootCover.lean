import MOC.FiniteCurveRootBranches
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.Separable

/-! A separable fiber of a finite plane curve has disjoint local root sheets. -/

open Filter Polynomial
open scoped Topology

namespace MOC

/-- Every root of a separable fiber at which the leading coefficient is nonzero has a local
holomorphic branch. The branches remain distinct and exhaust all nearby
roots, because their number already equals the locally constant degree. -/
theorem exists_local_holomorphic_root_cover_of_leadingCoeff_ne_zero
    (P : Polynomial (Polynomial ℂ)) (z₀ : ℂ)
    (hLead : P.leadingCoeff.eval z₀ ≠ 0)
    (hsep : (P.map (Polynomial.evalRingHom z₀)).Separable) :
    let R := (P.map (Polynomial.evalRingHom z₀)).roots.toFinset
    ∃ g : (↑R : Type) → ℂ → ℂ,
      (∀ r, g r z₀ = r.val) ∧
      ∀ᶠ z in 𝓝 z₀,
        (∀ r, DifferentiableAt ℂ (g r) z) ∧
        Function.Injective (fun r => g r z) ∧
        ∀ w, (P.map (Polynomial.evalRingHom z)).IsRoot w ↔ ∃ r, g r z = w := by
  classical
  let Q (z : ℂ) := P.map (Polynomial.evalRingHom z)
  let R := (Q z₀).roots.toFinset
  change ∃ g : (↑R : Type) → ℂ → ℂ, _ ∧ _
  have hLead' : ∀ᶠ z in 𝓝 z₀, P.leadingCoeff.eval z ≠ 0 :=
    P.leadingCoeff.continuous.continuousAt.eventually_ne hLead
  have hne (z : ℂ) (hz : P.leadingCoeff.eval z ≠ 0) : Q z ≠ 0 := by
    intro h
    have he := congrArg (fun p : Polynomial ℂ => p.coeff P.natDegree) h
    exact hz (by simpa [Q, Polynomial.coeff_map, Polynomial.coeff_natDegree] using he)
  have hnd (z : ℂ) (hz : P.leadingCoeff.eval z ≠ 0) : (Q z).natDegree = P.natDegree :=
    Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ hz
  have hzr (r : (↑R : Type)) : (Q z₀).IsRoot r.val :=
    (mem_roots (hne z₀ hLead)).mp (Multiset.mem_toFinset.mp r.property)
  have hsimp (r : (↑R : Type)) : (Q z₀).derivative.eval r.val ≠ 0 := by
    intro h
    obtain ⟨A, B, hAB⟩ := (separable_def' _).mp hsep
    change A * Q z₀ + B * (Q z₀).derivative = 1 at hAB
    have hr0 : (Q z₀).eval r.val = 0 := hzr r
    have he := congrArg (Polynomial.eval r.val) hAB
    simp only [eval_add, eval_mul, hr0, mul_zero, h, add_zero, eval_one, zero_ne_one] at he
  have hb (r : (↑R : Type)) :
      ∃ g : ℂ → ℂ, g z₀ = r.val ∧ ∀ᶠ z in 𝓝 z₀,
        (Q z).IsRoot (g z) ∧ DifferentiableAt ℂ g z := by
    obtain ⟨g, hg, hnear, _⟩ := exists_local_holomorphic_simple_root P z₀ r.val (hzr r) (hsimp r)
    exact ⟨g, hg, hnear⟩
  choose g hval hnear using hb
  have hcont (r : (↑R : Type)) : ContinuousAt (g r) z₀ :=
    (hnear r).self_of_nhds.2.continuousAt
  have hdistinct (r s : (↑R : Type)) :
      ∀ᶠ z in 𝓝 z₀, r ≠ s → g r z ≠ g s z := by
    by_cases hr : r = s
    · exact Eventually.of_forall fun _ hc => False.elim (hc hr)
    · have hne : g r z₀ - g s z₀ ≠ 0 := by
        simpa only [hval, sub_ne_zero, Ne, Subtype.val_inj] using hr
      exact (((hcont r).sub (hcont s)).eventually_ne hne).mono
        fun _ hz _ => sub_ne_zero.mp hz
  have hN : ∀ᶠ z in 𝓝 z₀, ∀ r, (Q z).IsRoot (g r z) ∧ DifferentiableAt ℂ (g r) z :=
    Filter.eventually_all.mpr hnear
  have hD : ∀ᶠ z in 𝓝 z₀, ∀ r s, r ≠ s → g r z ≠ g s z :=
    Filter.eventually_all.mpr fun r => Filter.eventually_all.mpr (hdistinct r)
  refine ⟨g, hval, ?_⟩
  filter_upwards [hN, hD, hLead'] with z hz hdis hLz
  have hi : Function.Injective (fun r => g r z) :=
    fun r s h => not_ne_iff.mp (fun hn => hdis r s hn h)
  refine ⟨fun r => (hz r).2, hi, ?_⟩
  let T := Finset.univ.image (fun r => g r z)
  have hTR : T ⊆ (Q z).roots.toFinset := by
    intro w hw
    obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hw
    exact Multiset.mem_toFinset.mpr ((mem_roots (hne z hLz)).mpr (hz r).1)
  have hTcard : T.card = P.natDegree := by
    change (Finset.univ.image (fun r => g r z)).card = _
    rw [Finset.card_image_of_injective _ hi, Finset.card_univ, Fintype.card_coe]
    dsimp [R]
    rw [Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hsep),
      splits_iff_card_roots.mp (IsAlgClosed.splits (Q z₀)), hnd z₀ hLead]
  have hRcard : (Q z).roots.toFinset.card ≤ T.card := by
    rw [hTcard]
    exact ((Q z).roots.toFinset_card_le).trans
      ((card_roots' (Q z)).trans (hnd z hLz).le)
  have hsame := Finset.eq_of_subset_of_card_le hTR hRcard
  intro w
  rw [← mem_roots (hne z hLz), ← Multiset.mem_toFinset, ← hsame]
  change w ∈ Finset.univ.image (fun r => g r z) ↔ _
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor <;> rintro ⟨r, hr⟩ <;> exact ⟨r, hr⟩

/-- Every root of a separable fiber of a monic plane curve has a local
holomorphic branch. The branches remain distinct and exhaust all nearby
roots, because their number already equals the constant monic degree. -/
theorem exists_local_holomorphic_root_cover
    (P : Polynomial (Polynomial ℂ)) (hP : P.Monic) (z₀ : ℂ)
    (hsep : (P.map (Polynomial.evalRingHom z₀)).Separable) :
    let R := (P.map (Polynomial.evalRingHom z₀)).roots.toFinset
    ∃ g : (↑R : Type) → ℂ → ℂ,
      (∀ r, g r z₀ = r.val) ∧
      ∀ᶠ z in 𝓝 z₀,
        (∀ r, DifferentiableAt ℂ (g r) z) ∧
        Function.Injective (fun r => g r z) ∧
        ∀ w, (P.map (Polynomial.evalRingHom z)).IsRoot w ↔ ∃ r, g r z = w := by
  exact exists_local_holomorphic_root_cover_of_leadingCoeff_ne_zero P z₀
    (by simp [hP.leadingCoeff]) hsep

end MOC
