import MOC.ContactCover
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! A positive deficit with no new contact admits a lift over a right
half-plane that stays in the strict inactive-gap chamber. -/

open Set

namespace MOC

private theorem isPathConnected_positive_halfPlane_off_finite (S : Set ℂ) (hS : S.Finite) :
    IsPathConnected ({z : ℂ | 0 < z.re} ∩ Sᶜ) := by
  let e (z : ℂ) : ℂ := ⟨Real.exp z.re, z.im⟩
  have hinj : Function.Injective e := by
    intro x y h
    have hre := congrArg Complex.re h
    have him := congrArg Complex.im h
    change Real.exp x.re = Real.exp y.re at hre
    change x.im = y.im at him
    exact Complex.ext (Real.exp_injective hre) him
  have hc : Continuous e := by
    have he : e = fun z => Complex.ofReal (Real.exp z.re) + (z.im : ℂ) * Complex.I := by
      funext z
      apply Complex.ext <;> simp only [e, Complex.add_re, Complex.add_im, Complex.mul_re,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        mul_zero, mul_one, zero_mul, zero_sub, neg_zero, zero_add, add_zero]
    rw [he]
    exact (Complex.continuous_ofReal.comp (Real.continuous_exp.comp Complex.continuous_re)).add
      ((Complex.continuous_ofReal.comp Complex.continuous_im).mul continuous_const)
  have hrank : 1 < Module.rank ℝ ℂ := by rw [Complex.rank_real_complex]; norm_num
  have hpre : (e ⁻¹' S).Finite := hS.preimage hinj.injOn
  have himage : e '' (e ⁻¹' S)ᶜ = {z : ℂ | 0 < z.re} ∩ Sᶜ := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨Real.exp_pos _, hx⟩
    · rintro ⟨hz, hzs⟩
      let x : ℂ := ⟨Real.log z.re, z.im⟩
      have hx : e x = z := Complex.ext (Real.exp_log hz) rfl
      exact ⟨x, fun he => hzs (hx ▸ he), hx⟩
  rw [← himage]
  exact (hpre.countable.isPathConnected_compl_of_one_lt_rank hrank).image hc

/-- If the real deficit stays positive and no new contact is possible, a
deficit covering has a section over a right half-plane in the strict chamber. -/
theorem exists_deficit_halfPlane_section_of_no_new_contact
    {ι X : Type*} [TopologicalSpace X]
    (J : Finset ι) (hne : J.Nonempty) (H : ι → X → ℂ)
    (hcont : ∀ j ∈ J, Continuous (H j))
    (D : X → ℂ) {S : Set ℂ} (hS : S.Finite) (hgood : ∀ x, D x ∈ Sᶜ)
    (hcover : IsCoveringMap (fun x : X => (⟨D x, hgood x⟩ : ↥Sᶜ)))
    (x₀ : X) (hd₀ : 0 < (D x₀).re) (hstart : ∀ j ∈ J, 0 < (H j x₀).re)
    (hno : ∀ x, 0 < (D x).re → (∀ j ∈ J, 0 ≤ (H j x).re) →
      ∀ j ∈ J, (H j x).re ≠ 0) :
    ∃ R : ℝ, 0 ≤ R ∧ {z : ℂ | R < z.re} ⊆ Sᶜ ∧
      ∃ F : C(↥{z : ℂ | R < z.re}, X),
        (∀ z, D (F z) = z.val) ∧ ∀ z j, j ∈ J → 0 < (H j (F z)).re := by
  classical
  let p (x : X) : ↥Sᶜ := ⟨D x, hgood x⟩
  let B : Set ℂ := {z : ℂ | 0 < z.re} ∩ Sᶜ
  let m (x : X) : ℝ := J.inf' hne (fun j => (H j x).re)
  have hm : Continuous m :=
    Continuous.finset_inf'_apply (f := fun j x => (H j x).re) hne
      (fun j hj => Complex.continuous_re.comp (hcont j hj))
  have hkeep (A : Set X) (hA : IsPreconnected A)
      (hD : ∀ x ∈ A, 0 < (D x).re)
      (a : X) (ha : a ∈ A) (hma : 0 < m a) (x : X) (hx : x ∈ A) : 0 < m x := by
    by_contra! hle
    have hz : (0 : ℝ) ∈ m '' A :=
      (hA.image m hm.continuousOn).Icc_subset ⟨x, hx, rfl⟩ ⟨a, ha, rfl⟩ ⟨hle, hma.le⟩
    obtain ⟨u, hu, hmu⟩ := hz
    have hnonneg := (Finset.le_inf'_iff hne (fun j => (H j u).re)).mp hmu.ge
    obtain ⟨j, hj, he⟩ := Finset.exists_mem_eq_inf' hne (fun j => (H j u).re)
    exact hno u (hD u hu) hnonneg j hj (he.symm.trans hmu)
  obtain ⟨b, hb⟩ := (hS.image Complex.re).bddAbove
  let R := max b 0
  let W : Set ℂ := {z : ℂ | R < z.re}
  have hR : 0 ≤ R := le_max_right _ _
  have hW : IsOpen W := isOpen_lt continuous_const Complex.continuous_re
  have hWS : W ⊆ Sᶜ := by
    intro z hz hs
    change R < z.re at hz
    exact hz.not_le ((hb ⟨z, hs, rfl⟩).trans (le_max_left _ _))
  let w : ℂ := ((R + 1 : ℝ) : ℂ)
  have hw : w ∈ W := by simp [W, w]
  have hwB : w ∈ B := ⟨hR.trans_lt hw, hWS hw⟩
  letI : PathConnectedSpace B := isPathConnected_iff_pathConnectedSpace.mp
    (isPathConnected_positive_halfPlane_off_finite S hS)
  let inc : C(B, ↥Sᶜ) := ⟨fun z => ⟨z.val, z.property.2⟩,
    continuous_subtype_val.subtype_mk _⟩
  let γ := PathConnectedSpace.somePath (⟨D x₀, hd₀, hgood x₀⟩ : B) (⟨w, hwB⟩ : B)
  obtain ⟨Γ, hΓ, hΓ₀⟩ := hcover.exists_path_lifts (inc.comp γ.toContinuousMap) x₀
    (by change inc (γ 0) = p x₀; rw [γ.source]; rfl)
  have hΓD (t : unitInterval) : D (Γ t) = (γ t).val := by
    simpa only [p, inc, Function.comp_apply, ContinuousMap.comp_apply] using
      congrArg Subtype.val (congrFun hΓ t)
  let x₁ := Γ 1
  have hx₁ : D x₁ = w := by rw [show x₁ = Γ 1 from rfl, hΓD, γ.target]
  have hm₁ : 0 < m x₁ := by
    apply hkeep (Set.range Γ) (isConnected_range Γ.continuous).isPreconnected
      (fun x hx => ?_) (Γ 0) ⟨0, rfl⟩
      (by rw [hΓ₀]; exact (Finset.lt_inf'_iff hne).mpr hstart) x₁ ⟨1, rfl⟩
    obtain ⟨t, rfl⟩ := hx
    rw [hΓD]
    exact (γ t).property.1
  let incl : C(W, ↥Sᶜ) := ⟨fun z => ⟨z.val, hWS z.property⟩,
    continuous_subtype_val.subtype_mk _⟩
  letI : ContractibleSpace W := (convex_halfSpace_re_gt R).contractibleSpace ⟨w, hw⟩
  letI : LocPathConnectedSpace W := hW.isOpenEmbedding_subtypeVal.locPathConnectedSpace
  obtain ⟨F, ⟨hF₀, hF⟩, _⟩ := hcover.existsUnique_continuousMap_lifts incl
    (⟨w, hw⟩ : W) x₁ (by apply Subtype.ext; exact hx₁)
  have hFD (z : W) : D (F z) = z.val :=
    congrArg Subtype.val (congrFun hF z)
  refine ⟨R, hR, hWS, F, hFD, fun z j hj => ?_⟩
  have hmz : 0 < m (F z) := by
    apply hkeep (Set.range F) (isConnected_range F.continuous).isPreconnected
      (fun x hx => ?_) x₁ ⟨⟨w, hw⟩, hF₀⟩ hm₁ (F z) ⟨z, rfl⟩
    obtain ⟨t, rfl⟩ := hx
    rw [hFD]
    exact hR.trans_lt t.property
  exact (Finset.lt_inf'_iff (f := fun k => (H k (F z)).re) hne).mp hmz j hj

end MOC
