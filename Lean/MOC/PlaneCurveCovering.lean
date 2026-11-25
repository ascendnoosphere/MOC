import MOC.FiniteCovering
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! The projection of the simple-root locus of a plane polynomial.
A local chart for `(x, y) ↦ (x, P(x, y))` restricts to an inverse
branch over the level `P(x, y) = 0`. -/

open Set Function Topology BigOperators Polynomial
open scoped Topology

namespace MOC

private theorem isLocalHomeomorph_level_projection
    {B F : Type*} [TopologicalSpace B] [TopologicalSpace F]
    (S : Set B) (Q : B × F → F) (c : F)
    (hlocal : ∀ z : {z : S × F // Q (z.1.val, z.2) = c},
      ∃ e : PartialHomeomorph (B × F) (B × F),
        (z.val.1.val, z.val.2) ∈ e.source ∧
          (e : B × F → B × F) = fun x => (x.1, Q x)) :
    IsLocalHomeomorph (fun z : {z : S × F // Q (z.1.val, z.2) = c} => z.val.1) := by
  classical
  let W := {z : S × F // Q (z.1.val, z.2) = c}
  let p (x : W) : S := x.val.1
  let ambient (x : W) : B × F := (x.val.1.val, x.val.2)
  have hambient : Continuous ambient :=
    (continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)).prodMk
      (continuous_snd.comp continuous_subtype_val)
  change IsLocalHomeomorph p
  rw [isLocalHomeomorph_iff_isOpenEmbedding_restrict]
  intro z
  obtain ⟨e, hz, he⟩ := hlocal z
  let V : Set W := ambient ⁻¹' e.source
  let U : Set S := (fun b => (b.val, c)) ⁻¹' e.target
  have hVopen : IsOpen V := e.open_source.preimage hambient
  have hUopen : IsOpen U := e.open_target.preimage (continuous_subtype_val.prodMk continuous_const)
  let u (b : U) : B × F := e.symm (b.val.val, c)
  have huEq (b : U) : (u b).1 = b.val.val ∧ Q (u b) = c := by
    have h : e (u b) = (b.val.val, c) := e.right_inv b.property
    rw [congrFun he (u b)] at h
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  let w (b : U) : W := ⟨(b.val, (u b).2), by
    change Q (b.val.val, (u b).2) = c
    rw [← (huEq b).1]
    exact (huEq b).2⟩
  have hwu (b : U) : ambient (w b) = u b := Prod.ext (huEq b).1.symm rfl
  let g (b : U) : V := ⟨w b, by
    change ambient (w b) ∈ e.source
    rw [hwu]
    exact e.map_target b.property⟩
  have hu : Continuous u :=
    e.continuousOn_invFun.comp_continuous
      ((continuous_subtype_val.comp continuous_subtype_val).prodMk continuous_const)
      (fun b => b.property)
  have hw : Continuous w :=
    (continuous_subtype_val.prodMk (continuous_snd.comp hu)).subtype_mk (fun b => (w b).property)
  have hg : Continuous g := hw.subtype_mk fun b => (g b).property
  have heval (x : W) : e (ambient x) = ((p x).val, c) := by
    rw [congrFun he (ambient x)]
    exact Prod.ext rfl x.property
  let h (x : V) : U := ⟨p x.val, by
    change ((p x.val).val, c) ∈ e.target
    rw [← heval x.val]
    exact e.map_source x.property⟩
  have hleft (x : V) : g (h x) = x := by
    apply Subtype.ext
    apply Subtype.ext
    change (p x.val, (e.symm ((p x.val).val, c)).2) = x.val.val
    rw [← heval x.val, e.left_inv x.property]
  have hright (b : U) : p (g b).val = b.val := rfl
  refine ⟨V, hVopen.mem_nhds hz, isOpenEmbedding_iff_continuous_injective_isOpenMap.mpr ⟨?_, ?_, ?_⟩⟩
  · exact continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val)
  · intro x y hxy
    have hxy' : h x = h y := Subtype.ext hxy
    exact (hleft x).symm.trans ((congrArg g hxy').trans (hleft y))
  · intro O hO
    have heq : (V.restrict p) '' O = Subtype.val '' (g ⁻¹' O) := by
      ext b
      constructor
      · rintro ⟨x, hx, rfl⟩
        refine ⟨h x, ?_, rfl⟩
        change g (h x) ∈ O
        rwa [hleft]
      · rintro ⟨b, hb, rfl⟩
        exact ⟨g b, hb, hright b⟩
    rw [heq]
    exact hUopen.isOpenMap_subtype_val _ (hO.preimage hg)

noncomputable section

/-- Specialization in the first coordinate of a polynomial in two variables. -/
def planePolynomialSpecialize (P : Polynomial ℂ[X]) (x : ℂ) : ℂ[X] :=
  P.map (Polynomial.evalRingHom x)

/-- Evaluation in both coordinates of a plane polynomial. -/
def planePolynomialEval (P : Polynomial ℂ[X]) (z : ℂ × ℂ) : ℂ :=
  (planePolynomialSpecialize P z.1).eval z.2

private theorem contDiff_eval_complex_polynomial (p : ℂ[X]) :
    ContDiff ℂ 1 (fun x : ℂ => p.eval x) := by
  have h : (fun x : ℂ => p.eval x) = fun x => ∑ i ∈ p.support, p.coeff i * x ^ i := by
    funext x
    rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  rw [h]
  exact ContDiff.sum fun i _ => contDiff_const.mul (contDiff_id.pow i)

private theorem contDiff_planePolynomialEval (P : Polynomial ℂ[X]) :
    ContDiff ℂ 1 (planePolynomialEval P) := by
  have h : planePolynomialEval P =
      fun z => ∑ i ∈ P.support, (P.coeff i).eval z.1 * z.2 ^ i := by
    funext z
    simp only [planePolynomialEval, planePolynomialSpecialize, Polynomial.eval_map,
      Polynomial.eval₂_eq_sum, Polynomial.sum_def, Polynomial.coe_evalRingHom]
  rw [h]
  exact ContDiff.sum fun i _ =>
    ((contDiff_eval_complex_polynomial (P.coeff i)).comp contDiff_fst).mul (contDiff_snd.pow i)

theorem continuous_planePolynomialEval (P : Polynomial ℂ[X]) :
    Continuous (planePolynomialEval P) := (contDiff_planePolynomialEval P).continuous

theorem differentiable_planePolynomialEval (P : Polynomial ℂ[X]) :
    Differentiable ℂ (planePolynomialEval P) := (contDiff_planePolynomialEval P).differentiable le_rfl

private theorem exists_planePolynomial_local_chart (P : Polynomial ℂ[X]) (z : ℂ × ℂ)
    (h : (planePolynomialSpecialize P z.1).derivative.eval z.2 ≠ 0) :
    ∃ e : PartialHomeomorph (ℂ × ℂ) (ℂ × ℂ), z ∈ e.source ∧
      (e : ℂ × ℂ → ℂ × ℂ) = (fun w => (w.1, planePolynomialEval P w)) ∧
      DifferentiableAt ℂ (e.symm : ℂ × ℂ → ℂ × ℂ) (z.1, planePolynomialEval P z) := by
  let D := fderiv ℂ (planePolynomialEval P) z
  have hD : HasFDerivAt (planePolynomialEval P) D z :=
    ((contDiff_planePolynomialEval P).contDiffAt.differentiableAt le_rfl).hasFDerivAt
  have hline : HasFDerivAt (fun y : ℂ => (z.1, y))
      (ContinuousLinearMap.inr ℂ ℂ ℂ) z.2 := hasFDerivAt_prodMk_right z.1 z.2
  have hpartial : HasDerivAt (fun y => planePolynomialEval P (z.1, y)) (D (0, 1)) z.2 := by
    simpa using (hD.comp z.2 hline).hasDerivAt
  have hDne : D (0, 1) ≠ 0 := by
    rw [hpartial.unique ((planePolynomialSpecialize P z.1).hasDerivAt z.2)]
    exact h
  let J : ℂ × ℂ →L[ℂ] ℂ × ℂ := (ContinuousLinearMap.fst ℂ ℂ ℂ).prod D
  have hJzero (x : ℂ × ℂ) (hx : J x = 0) : x = 0 := by
    have hx₁ : x.1 = 0 := congrArg Prod.fst hx
    have hDx : D x = 0 := congrArg Prod.snd hx
    have hxs : x = x.2 • ((0 : ℂ), (1 : ℂ)) := by
      apply Prod.ext <;> simp [hx₁, smul_eq_mul]
    rw [hxs, map_smul, smul_eq_mul] at hDx
    exact Prod.ext hx₁ ((mul_eq_zero.mp hDx).resolve_right hDne)
  have hJinj : Injective J := by
    intro x y hxy
    apply sub_eq_zero.mp
    exact hJzero (x - y) (by rw [map_sub, hxy, sub_self])
  let E := (LinearEquiv.ofBijective J.toLinearMap
    ⟨hJinj, LinearMap.injective_iff_surjective.mp hJinj⟩).toContinuousLinearEquiv
  have hE : (E : ℂ × ℂ →L[ℂ] ℂ × ℂ) = J := rfl
  let f (x : ℂ × ℂ) := (x.1, planePolynomialEval P x)
  have hf₁ : HasFDerivAt f (E : ℂ × ℂ →L[ℂ] ℂ × ℂ) z := by
    rw [hE]
    exact hasFDerivAt_fst.prodMk hD
  have hf₂ : ContDiffAt ℂ 1 f z := (contDiff_fst.prodMk (contDiff_planePolynomialEval P)).contDiffAt
  let hf := hf₂.hasStrictFDerivAt' hf₁ le_rfl
  exact ⟨hf.toPartialHomeomorph f, hf.mem_toPartialHomeomorph_source, rfl,
    hf.to_localInverse.differentiableAt⟩

/-- A continuous choice of a simple root of a plane polynomial is holomorphic. -/
theorem differentiableOn_of_continuous_planePolynomialRoot (P : Polynomial ℂ[X])
    {S : Set ℂ} (hS : IsOpen S) (y : ℂ → ℂ) (hy : ContinuousOn y S)
    (hroot : ∀ z ∈ S, planePolynomialEval P (z, y z) = 0)
    (hsep : ∀ z ∈ S, (planePolynomialSpecialize P z).Separable) :
    DifferentiableOn ℂ y S := by
  intro z hz
  have hs : (planePolynomialSpecialize P z).derivative.eval (y z) ≠ 0 :=
    (hsep z hz).eval₂_derivative_ne_zero (RingHom.id ℂ) (hroot z hz)
  obtain ⟨e, hez, he, hd⟩ := exists_planePolynomial_local_chart P (z, y z) hs
  have hd' : DifferentiableAt ℂ (e.symm : ℂ × ℂ → ℂ × ℂ) (z, 0) := by
    simpa only [hroot z hz] using hd
  have hline : DifferentiableAt ℂ (fun w : ℂ => (w, (0 : ℂ))) z :=
    differentiableAt_id.prodMk (differentiableAt_const _)
  have hy' : DifferentiableAt ℂ (fun w : ℂ => (e.symm (w, 0)).2) z := (hd'.comp z hline).snd
  have hcont : ContinuousAt (fun w : ℂ => (w, y w)) z :=
    continuousAt_id.prodMk (hy.continuousAt (hS.mem_nhds hz))
  have hnear : ∀ᶠ w in 𝓝 z, (w, y w) ∈ e.source :=
    hcont.eventually_mem (e.open_source.mem_nhds hez)
  apply (hy'.congr_of_eventuallyEq ?_).differentiableWithinAt
  filter_upwards [hnear, hS.mem_nhds hz] with w hw hwS
  have hew : e (w, y w) = (w, 0) := by
    rw [congrFun he (w, y w), hroot w hwS]
  rw [← hew, e.left_inv hw]

/-- The roots of the specialized plane polynomial over the allowed values. -/
abbrev PlanePolynomialRoots (P : Polynomial ℂ[X]) (S : Set ℂ) :=
  {z : S × ℂ // (planePolynomialSpecialize P z.1.val).eval z.2 = 0}

/-- Away from the values where degree drops or roots coincide, the first
coordinate of a plane curve is a covering map of the expected degree. -/
theorem isCoveringMap_planePolynomialRoots (P : Polynomial ℂ[X]) (S : Set ℂ)
    {d : ℕ} (hd : 0 < d)
    (hdeg : ∀ b : S, (planePolynomialSpecialize P b.val).natDegree = d)
    (hsep : ∀ b : S, (planePolynomialSpecialize P b.val).Separable) :
    IsCoveringMap (fun z : PlanePolynomialRoots P S => z.val.1) := by
  classical
  let p (z : PlanePolynomialRoots P S) : S := z.val.1
  refine isCoveringMap_of_localHomeomorph_finite_degree (p := p) ?_ hd ?_
  · apply isLocalHomeomorph_level_projection S (planePolynomialEval P) 0
    intro z
    obtain ⟨e, hez, he, _⟩ := exists_planePolynomial_local_chart P (z.val.1.val, z.val.2)
      ((hsep z.val.1).eval₂_derivative_ne_zero (RingHom.id ℂ) z.property)
    exact ⟨e, hez, he⟩
  · intro b
    let q := planePolynomialSpecialize P b.val
    have hq : q ≠ 0 := by
      intro hzero
      have hn : q.natDegree = d := hdeg b
      rw [hzero, Polynomial.natDegree_zero] at hn
      exact hd.ne' hn.symm
    have hcard : Fintype.card ↥q.roots.toFinset = d := by
      rw [Fintype.card_coe, Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots (hsep b))]
      have hs : q.natDegree = q.roots.card := by
        simpa only [Polynomial.map_id] using Polynomial.natDegree_eq_card_roots (IsAlgClosed.splits q)
      exact hs.symm.trans (hdeg b)
    have hroot (w : ℂ) : w ∈ q.roots.toFinset ↔ q.eval w = 0 := by
      simpa only [Multiset.mem_toFinset, Polynomial.IsRoot] using
        (Polynomial.mem_roots hq : w ∈ q.roots ↔ q.IsRoot w)
    let e : ↥q.roots.toFinset ≃ ↥(p ⁻¹' {b}) :=
      { toFun := fun w => ⟨⟨(b, w.val), (hroot w.val).1 w.property⟩, rfl⟩
        invFun := fun w => ⟨w.val.val.2, (hroot w.val.val.2).2 (by
          have hwb : w.val.val.1 = b := w.property
          exact (congrArg (fun t : S => (planePolynomialSpecialize P t.val).eval w.val.val.2)
            hwb).symm.trans w.val.property)⟩
        left_inv := fun w => Subtype.ext rfl
        right_inv := fun w => Subtype.ext (Subtype.ext (Prod.ext w.property.symm rfl)) }
    exact ⟨(Fintype.equivFinOfCardEq hcard).symm.trans e⟩

end

end MOC
