import MOC.AffineGapProper
import MOC.VaryingGapTerminal
import MOC.FiniteLocalHomeomorphCover
import Mathlib.Analysis.NormedSpace.Connected
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.FiniteDimensional

/-! Topological assembly of the affine continuation criterion.
The only unprovided input is the local analytic chart construction
for the new gap coordinate. -/

open Filter Set MvPolynomial
open scoped Topology

namespace MOC
noncomputable section

private def positiveReHomeomorph : ℂ ≃ₜ {z : ℂ // 0 < z.re} where
  toFun z := ⟨(Real.exp z.re : ℂ) + z.im • Complex.I, by
    simpa [Complex.real_smul, Complex.mul_re] using Real.exp_pos z.re⟩
  invFun z := (Real.log z.val.re : ℂ) + z.val.im • Complex.I
  left_inv z := by
    apply Complex.ext <;>
      simp only [Complex.real_smul, Complex.add_re, Complex.add_im, Complex.mul_re,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        mul_zero, zero_mul, sub_zero, add_zero, zero_add, mul_one, Real.log_exp]
  right_inv z := by
    apply Subtype.ext
    apply Complex.ext <;>
      simp [Complex.real_smul, Complex.mul_re, Complex.mul_im, Real.exp_log z.property]
  continuous_toFun := by
    apply Continuous.subtype_mk
    fun_prop
  continuous_invFun := by
    apply continuous_iff_continuousAt.mpr
    intro z
    have hg : ContinuousAt (fun y : {z : ℂ // 0 < z.re} => y.val.re) z :=
      (Complex.continuous_re.comp continuous_subtype_val).continuousAt
    have hc : ContinuousAt (fun y : {z : ℂ // 0 < z.re} => Real.log y.val.re) z :=
      Filter.Tendsto.comp (Real.continuousAt_log z.property.ne') hg
    exact (Complex.continuous_ofReal.continuousAt.comp hc).add
      ((Complex.continuous_im.comp continuous_subtype_val).continuousAt.smul continuousAt_const)

private theorem positive_base_pathConnected {B : Set ℂ} (hB : B.Finite) :
    IsPathConnected {z : (↑Bᶜ : Type) | 0 < z.val.re} := by
  let T : Set {z : ℂ // 0 < z.re} := Subtype.val ⁻¹' B
  have hfT : T.Finite := hB.preimage Subtype.val_injective.injOn
  have hf : (positiveReHomeomorph ⁻¹' T).Finite :=
    hfT.preimage positiveReHomeomorph.injective.injOn
  have hdim : 1 < Module.rank ℝ ℂ := by rw [Complex.rank_real_complex]; exact Nat.one_lt_ofNat
  have hconn := hf.countable.isPathConnected_compl_of_one_lt_rank hdim
  have hcon : IsPathConnected Tᶜ := by
    have he : positiveReHomeomorph '' (positiveReHomeomorph ⁻¹' T)ᶜ = Tᶜ := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact hx
      · intro hy
        exact ⟨positiveReHomeomorph.symm y, by simpa using hy, by simp⟩
    rw [← he]
    exact hconn.image positiveReHomeomorph.continuous
  let A : Set (↑Bᶜ : Type) := {z | 0 < z.val.re}
  let F : (↑Tᶜ : Type) → (↑Bᶜ : Type) := fun z => ⟨z.val.val,z.property⟩
  have hc : Continuous F :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  have he : Set.range F = A := by
    ext z
    constructor
    · rintro ⟨u,rfl⟩
      exact u.val.property
    · intro hz
      exact ⟨⟨⟨z.val,hz⟩,z.property⟩,rfl⟩
  letI : PathConnectedSpace (↑Tᶜ : Type) := isPathConnected_iff_pathConnectedSpace.mp hcon
  change IsPathConnected A
  rw [← he]
  exact isPathConnected_range hc

/-- The concrete chart input on a prime finite affine curve. The map is
the actual polynomial coordinate on actual affine points, not a model
that is only birational to the curve. -/
def AffineGapCharts (σ : Type*) [Fintype σ] : Prop :=
  ∀ (Q : Ideal (MvPolynomial σ ℂ)) [Q.IsPrime]
    (f : Polynomial ℂ →ₐ[ℂ] (MvPolynomial σ ℂ ⧸ Q)), f.Finite → Function.Injective f →
    ∀ (t g : MvPolynomial σ ℂ), Ideal.Quotient.mk Q t = f Polynomial.X →
    (∃ x y : zeroLocus Q, eval x.val g ≠ eval y.val g) →
    ∃ B : Set ℂ, B.Finite ∧
      let E := {x : zeroLocus Q | eval x.val g ∈ Bᶜ}
      let p : E → (↑Bᶜ : Type) := fun x => ⟨eval x.val.val g,x.property⟩
      IsCoveringMap p ∧ ∀ x i, ∃ h : ℂ → ℂ, DifferentiableAt ℂ h ((p x).val) ∧
        ∀ᶠ x' in 𝓝 x, x'.val.val i = h (p x').val

/-- Once the affine curve has the specified regular gap charts, the
existence of a half-plane sheet follows. Even an exceptional initial
point lies in the closure of a positive component containing a sheet. -/
theorem affineGapContinuation_of_charts {σ : Type*} [Fintype σ]
    (hcharts : AffineGapCharts σ) : AffineGapContinuation σ := by
  classical
  intro Q hQ F hF hFi t g ht hv x₀ hx₀
  obtain ⟨B, hB, hcov, hlocal⟩ := hcharts Q F hF hFi t g ht hv
  let E : Set (zeroLocus Q) := {x | eval x.val g ∈ Bᶜ}
  let p : E → (↑Bᶜ : Type) := fun x => ⟨eval x.val.val g,x.property⟩
  let A : Set (↑Bᶜ : Type) := {z | 0 < z.val.re}
  let H : Set E := p ⁻¹' A
  have hcA : IsPathConnected A := positive_base_pathConnected hB
  have hBbd : BddAbove (Complex.re '' B) := (hB.image _).bddAbove
  obtain ⟨c₀,hc₀⟩ := hBbd
  let c := max c₀ (0 : ℝ)
  have hc : 0 ≤ c := le_max_right _ _
  have hcb z (hz : z ∈ B) : z.re ≤ c := (hc₀ ⟨z,hz,rfl⟩).trans (le_max_left _ _)
  let D : Set ℂ := {z | 0 < z.re}
  have hshift (z : D) : (z.val + (c : ℂ)) ∈ Bᶜ := by
    intro h
    have hh := hcb _ h
    rw [Complex.add_re, Complex.ofReal_re] at hh
    have hp : 0 < z.val.re := z.property
    linarith only [hh,hp]
  let inc : C(D, (↑Bᶜ : Type)) := ⟨fun z => ⟨z.val + (c : ℂ),hshift z⟩,
    (continuous_subtype_val.add continuous_const).subtype_mk _⟩
  let z₀ : D := ⟨1, by simp [D]⟩
  have hz₀ : inc z₀ ∈ A := by
    change 0 < ((1 : ℂ) + (c : ℂ)).re
    rw [Complex.add_re, Complex.one_re, Complex.ofReal_re]
    exact add_pos_of_pos_of_nonneg zero_lt_one hc
  let I := {x : E // p x = inc z₀}
  have hIfin : Finite I := by
    have hfib := finite_points_over_varying_affine_coordinate Q F hF hFi t g ht hv (inc z₀).val
    letI : Finite {x : zeroLocus Q // eval x.val g = (inc z₀).val} := hfib.to_subtype
    let lift (x : I) : {x : zeroLocus Q // eval x.val g = (inc z₀).val} :=
      ⟨x.val.val, congrArg Subtype.val x.property⟩
    refine Finite.of_injective lift fun x y h => ?_
    have he : x.val.val = y.val.val :=
      congrArg (fun a : {x : zeroLocus Q // eval x.val g = (inc z₀).val} => a.val) h
    exact Subtype.ext (Subtype.ext he)
  let S (a : I) : Set (zeroLocus Q) := Subtype.val '' pathComponentIn a.val H
  have hS (a : I) : IsPreconnected (S a) := by
    have ha : a.val ∈ H := by change p a.val ∈ A; rw [a.property]; exact hz₀
    exact (isPathConnected_pathComponentIn ha).isConnected.isPreconnected.image _
      continuous_subtype_val.continuousOn
  have hpos (a : I) (x : zeroLocus Q) (hx : x ∈ S a) : 0 < (eval x.val g).re := by
    obtain ⟨y,hy,rfl⟩ := hx
    exact (show y ∈ H from pathComponentIn_subset hy)
  have hcover : {x : zeroLocus Q | x ∈ E ∧ 0 < (eval x.val g).re} ⊆ ⋃ a : I, S a := by
    intro x hx
    let y : E := ⟨x,hx.1⟩
    obtain ⟨γ,hγ⟩ := hcA.joinedIn (p y) hx.2 (inc z₀) hz₀
    obtain ⟨Γ, hΓ, hΓ0⟩ := hcov.exists_path_lifts γ.toContinuousMap y γ.source
    have hproj (j : unitInterval) : p (Γ j) = γ j := congrFun hΓ j
    let a : I := ⟨Γ 1,(hproj 1).trans γ.target⟩
    have hj : JoinedIn H y a.val := by
      refine ⟨⟨Γ,hΓ0,rfl⟩,fun j => ?_⟩
      change p (Γ j) ∈ A
      rw [hproj]
      exact hγ j
    exact mem_iUnion.mpr ⟨a, y, hj.symm, rfl⟩
  have hxclo : x₀ ∈ closure (⋃ a : I, S a) := by
    have hd : Dense E := dense_affine_varying_coordinate_off_finite Q F hF hFi t g ht hv hB
    have hG : Continuous (fun x : zeroLocus Q => (eval x.val g).re) :=
      Complex.continuous_re.comp (g.continuous_eval.comp continuous_subtype_val)
    apply closure_mono hcover
    exact mem_closure_iff_nhds.2 fun U hU => by
      obtain ⟨y,hy⟩ := hd.inter_open_nonempty
        (interior U ∩ {x : zeroLocus Q | 0 < (eval x.val g).re})
        (isOpen_interior.inter (isOpen_lt continuous_const hG))
        ⟨x₀, mem_interior_iff_mem_nhds.mpr hU,hx₀⟩
      exact ⟨y,interior_subset hy.1.1,hy.2,hy.1.2⟩
  rw [closure_iUnion_of_finite] at hxclo
  obtain ⟨a,ha⟩ := mem_iUnion.mp hxclo
  obtain ⟨s, hs₀, hs, R, hR, hhol⟩ :=
    exists_halfPlane_holomorphic_coordinates p hcov Subtype.val c D rfl inc (fun _ => rfl)
      z₀ a.val a.property (fun e => e.val.val) hlocal
  have hSsub (z : D) : (s z).val ∈ S a := by
    have hconv : Convex ℝ D := convex_halfSpace_gt Complex.reLm.isLinear 0
    letI : ContractibleSpace D := hconv.contractibleSpace ⟨z₀,z₀.property⟩
    letI : SimplyConnectedSpace D := SimplyConnectedSpace.ofContractible D
    have hp := (isPathConnected_range s.continuous).joinedIn _ ⟨z₀,rfl⟩ _ ⟨z,rfl⟩
    rw [hs₀] at hp
    have hm : range s ⊆ H := by
      rintro _ ⟨w,rfl⟩
      change p (s w) ∈ A
      rw [hs]
      change 0 < (w.val + (c : ℂ)).re
      rw [Complex.add_re, Complex.ofReal_re]
      exact add_pos_of_pos_of_nonneg w.property hc
    exact ⟨s z, hp.mono hm,rfl⟩
  let sh (z : ℂ) : zeroLocus Q := if hz : z ∈ D then (s ⟨z,hz⟩).val else x₀
  have hvsh z (hz : z ∈ D) : sh z = (s ⟨z,hz⟩).val := dif_pos hz
  refine ⟨S a, sh,c,ha,hS a,hpos a,fun z hz => ?_,fun z hz => ?_,fun j => ?_⟩
  · rw [hvsh z hz]
    exact hSsub ⟨z,hz⟩
  · rw [hvsh z hz]
    exact congrArg Subtype.val (hs ⟨z,hz⟩)
  · exact (hhol j).congr fun z hz => by rw [hvsh z hz, ← hR ⟨z,hz⟩]

end
end MOC
