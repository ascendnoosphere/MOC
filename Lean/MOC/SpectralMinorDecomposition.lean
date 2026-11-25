import MOC.SubsetMarkerTest
import MOC.Support
import Mathlib.Data.Complex.FiniteDimensional
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-! Objective-preserving laws need not reproduce all squared minors. A single
free complex spectral entry is special: testing every scalar evaluation
already enforces a common law on the affine coefficient pair. -/

open BigOperators Matrix
open scoped Topology

namespace MOC

noncomputable section

private theorem complexFunctional (f : ℂ →L[ℝ] ℝ) (z : ℂ) :
    f z = (((f 1 : ℂ) - (f Complex.I : ℂ) * Complex.I) * z).re := by
  have hz : z.re • (1 : ℂ) + z.im • Complex.I = z := by
    simp [Complex.real_smul, Complex.re_add_im]
  calc
    f z = f (z.re • (1 : ℂ) + z.im • Complex.I) := congrArg f hz.symm
    _ = _ := by
      rw [map_add, map_smul, map_smul]
      simp [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, smul_eq_mul]
      ring

theorem productFunctional (f : (ℂ × ℂ) →L[ℝ] ℝ) :
    ∃ u v : ℂ, ∀ z : ℂ × ℂ, f z = (u * z.1 + v * z.2).re := by
  let f₀ : ℂ →L[ℝ] ℝ := f.comp ((ContinuousLinearMap.id ℝ ℂ).prod 0)
  let f₁ : ℂ →L[ℝ] ℝ := f.comp ((0 : ℂ →L[ℝ] ℂ).prod (ContinuousLinearMap.id ℝ ℂ))
  refine ⟨(f₀ 1 : ℂ) - (f₀ Complex.I : ℂ) * Complex.I,
    (f₁ 1 : ℂ) - (f₁ Complex.I : ℂ) * Complex.I, ?_⟩
  rintro ⟨z₀, z₁⟩
  simp only [Complex.add_re, ← complexFunctional]
  change f (z₀, z₁) = f (z₀, 0) + f (0, z₁)
  rw [← map_add]
  simp

private theorem affinePencil_strict_gap {P : Type*} [Fintype P] [Nonempty P]
    (s t : P → ℂ) (x y u v : ℂ)
    (h : ∀ p, (u * s p + v * t p).re < (u * x + v * y).re) :
    ∃ (z η : ℂ), ∀ p, (η * (s p + z * t p)).re < (η * (x + z * y)).re := by
  have main (a : ℂ) (ha : a ≠ 0)
      (hg : ∀ p, (a * s p + v * t p).re < (a * x + v * y).re) :
      ∃ (z η : ℂ), ∀ p, (η * (s p + z * t p)).re < (η * (x + z * y)).re := by
    refine ⟨v / a, a, fun p => ?_⟩
    have he : a * (v / a) = v := by field_simp
    simpa only [mul_add, ← mul_assoc a (v / a), he] using hg p
  by_cases hu : u = 0
  · subst u
    let O (p : P) : Set ℂ := {a | (a * s p + v * t p).re < (a * x + v * y).re}
    have hO (p : P) : IsOpen (O p) := by unfold O; apply isOpen_lt <;> fun_prop
    have hmem : (0 : ℂ) ∈ ⋂ p, O p := Set.mem_iInter.mpr h
    have hnear : (⋂ p, O p) ∈ 𝓝[≠] (0 : ℂ) :=
      nhdsWithin_le_nhds ((isOpen_iInter_of_finite hO).mem_nhds hmem)
    change (∀ᶠ a in 𝓝[≠] (0 : ℂ), a ∈ ⋂ p, O p) at hnear
    obtain ⟨a, ha, hane⟩ := (hnear.and self_mem_nhdsWithin).exists
    have hp : ∀ p, a ∈ O p := Set.mem_iInter.mp ha
    exact main a hane hp
  · exact main u hu h

/-- Every real support direction on an affine complex coefficient pair is an
evaluated support direction, or its limit. Hence there is no distinction
between pointwise and simultaneous convexity for an affine complex pencil. -/
theorem affinePencil_hull_iff_joint {P : Type*} [Fintype P] [Nonempty P]
    (s t : P → ℂ) (x y : ℂ) :
    (∀ z : ℂ, x + z * y ∈ convexHull ℝ (Set.range (fun p => s p + z * t p))) ↔
      (x, y) ∈ convexHull ℝ (Set.range (fun p => (s p, t p))) := by
  classical
  constructor
  · intro h
    by_contra hn
    have hc : IsClosed (convexHull ℝ (Set.range (fun p => (s p, t p)))) :=
      (Set.finite_range _).isClosed_convexHull
    obtain ⟨f, b, hb, hbx⟩ := geometric_hahn_banach_closed_point
      (convex_convexHull ℝ _) hc hn
    obtain ⟨u, v, hf⟩ := productFunctional f
    have hstrict (p : P) : (u * s p + v * t p).re < (u * x + v * y).re := by
      rw [← hf (s p, t p), ← hf (x, y)]
      exact (hb _ (subset_convexHull ℝ _ ⟨p, rfl⟩)).trans hbx
    obtain ⟨z, η, hz⟩ := affinePencil_strict_gap s t x y u v hstrict
    let g : ℂ →ₗ[ℝ] ℝ := Complex.reLm.comp (LinearMap.mulLeft ℝ η)
    have hm : ∃ p : P, ∀ q : P, g (s q + z * t q) ≤ g (s p + z * t p) := by
      obtain ⟨p, _, hp⟩ := Finset.exists_max_image Finset.univ
        (fun p : P => g (s p + z * t p)) Finset.univ_nonempty
      exact ⟨p, fun q => hp q (Finset.mem_univ q)⟩
    obtain ⟨p, hp⟩ := hm
    have he : g (x + z * y) ≤ g (s p + z * t p) := by
      apply convexHull_min ?_ (convex_halfSpace_le g.isLinear _) (h z)
      rintro _ ⟨q, rfl⟩
      exact hp q
    exact (not_le_of_gt (hz p)) he
  · intro h z
    let f : ℂ × ℂ →ₗ[ℝ] ℂ := LinearMap.fst ℝ ℂ ℂ +
      (LinearMap.mulLeft ℝ z).comp (LinearMap.snd ℝ ℂ ℂ)
    have hr : f '' Set.range (fun p => (s p, t p)) =
        Set.range (fun p => s p + z * t p) := by
      rw [← Set.range_comp]
      rfl
    change f (x, y) ∈ convexHull ℝ _
    rw [← hr, ← f.image_convexHull]
    exact ⟨_, h, rfl⟩

private theorem affinePencil_five_point_law {P : Type*} [Fintype P] [Nonempty P]
    (s t : P → ℂ) (x y : ℂ)
    (h : (x, y) ∈ convexHull ℝ (Set.range (fun p => (s p, t p)))) :
    ∃ k : ℕ, k ≤ 5 ∧ ∃ (p : Fin k → P) (w : Fin k → ℝ),
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧
      ∀ z : ℂ, (∑ i, (w i : ℂ) * (s (p i) + z * t (p i))) = x + z * y := by
  classical
  obtain ⟨κ, hκ, g, w, hg, hind, hw, hs, he⟩ := eq_pos_convex_span_of_mem_convexHull h
  letI : Fintype κ := hκ
  have hp (i : κ) : ∃ p : P, (s p, t p) = g i := hg ⟨i, rfl⟩
  choose p hp using hp
  have hc : Fintype.card κ ≤ 5 := by
    have hb := hind.card_le_finrank_succ.trans (Nat.add_le_add_right (Submodule.finrank_le _) 1)
    simpa [Module.finrank_prod, Complex.finrank_real_complex] using hb
  let e := (Fintype.equivFin κ).symm
  refine ⟨Fintype.card κ, hc, p ∘ e, w ∘ e, fun i => (hw _).le, ?_, ?_⟩
  · exact (Equiv.sum_comp e w).trans hs
  · intro z
    let f : ℂ × ℂ →ₗ[ℝ] ℂ := LinearMap.fst ℝ ℂ ℂ +
      (LinearMap.mulLeft ℝ z).comp (LinearMap.snd ℝ ℂ ℂ)
    have hf := congrArg f he
    simp only [map_sum, map_smul] at hf
    change (∑ i, (w (e i) : ℂ) * (s (p (e i)) + z * t (p (e i)))) = x + z * y
    rw [show (∑ i, (w (e i) : ℂ) * (s (p (e i)) + z * t (p (e i)))) =
        ∑ i, (w i : ℂ) * (s (p i) + z * t (p i)) from Equiv.sum_comp e (fun i => (w i : ℂ) * (s (p i) + z * t (p i)))]
    simpa only [← hp, f, LinearMap.add_apply, LinearMap.fst_apply, LinearMap.comp_apply,
      LinearMap.mulLeft_apply, LinearMap.snd_apply, Complex.real_smul] using hf

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- For one free complex partner entry, a common law on at most five
assignments exists if and only if each separate scalar hull test holds.
The law is allowed to depend on all the other spectral entries and on U. -/
theorem one_free_partner_entry_iff_common_law
    (a b : ι → ℂ) (j : ι) (U : Matrix ι ι ℂ) (hU : IsUnitary U) :
    (∀ z : ℂ, Holds a (Function.update b j z) U) ↔
      ∃ k : ℕ, k ≤ 5 ∧ ∃ (p : Fin k → Equiv.Perm ι) (w : Fin k → ℝ),
        (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧ ∀ z : ℂ,
          (∑ i, (w i : ℂ) * matchingProduct a (Function.update b j z) (p i)) =
            determinantValue a (Function.update b j z) U := by
  constructor
  · intro h
    let m (z : ℂ) (p : Equiv.Perm ι) := matchingProduct a (Function.update b j z) p
    let d (z : ℂ) := determinantValue a (Function.update b j z) U
    have hm (z : ℂ) (p : Equiv.Perm ι) : m z p = m 0 p + z * (m 1 p - m 0 p) := by
      simpa only [m, mul_comm z] using matching_update_interp a b j p z
    have hd (z : ℂ) : d z = d 0 + z * (d 1 - d 0) := by
      simpa only [d, mul_comm z] using determinant_update_interp a b j U hU z
    have hpair := (affinePencil_hull_iff_joint (m 0) (fun p => m 1 p - m 0 p)
      (d 0) (d 1 - d 0)).mp (fun z => by
        have hz : d z ∈ convexHull ℝ (Set.range (m z)) := h z
        rw [hd z, show m z = (fun p => m 0 p + z * (m 1 p - m 0 p)) from funext (hm z)] at hz
        exact hz)
    obtain ⟨k, hk, p, w, hw, hs, he⟩ :=
      affinePencil_five_point_law _ _ _ _ hpair
    refine ⟨k, hk, p, w, hw, hs, fun z => ?_⟩
    change (∑ i, (w i : ℂ) * m z (p i)) = d z
    simp only [hm z, hd z]
    exact he z
  · rintro ⟨k, _, p, w, hw, hs, he⟩ z
    unfold Holds
    refine mem_convexHull_of_exists_fintype w _ hw hs (fun i => ⟨p i, rfl⟩) ?_
    simpa only [Complex.real_smul] using he z

/-- A failure of the five-point pencil law yields an actual scalar spectral
counterexample, not merely a failed fixed-minor decomposition. -/
theorem one_free_partner_entry_counterexample_of_no_law
    (a b : ι → ℂ) (j : ι) (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (hn : ¬ ∃ k : ℕ, k ≤ 5 ∧ ∃ (p : Fin k → Equiv.Perm ι) (w : Fin k → ℝ),
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧ ∀ z : ℂ,
        (∑ i, (w i : ℂ) * matchingProduct a (Function.update b j z) (p i)) =
          determinantValue a (Function.update b j z) U) :
    ∃ z η : ℂ, ∀ σ : Equiv.Perm ι,
      (η * matchingProduct a (Function.update b j z) σ).re <
        (η * determinantValue a (Function.update b j z) U).re := by
  classical
  have he := mt (one_free_partner_entry_iff_common_law a b j U hU).mp hn
  obtain ⟨z, hz⟩ := not_forall.mp he
  rw [holds_iff_directional] at hz
  push_neg at hz
  exact ⟨z, hz⟩

/-- One subset-image event in the permutation convention used by the
Cauchy–Binet expansion. -/
def subsetImageEvent (I J : Finset ι) (σ : Equiv.Perm ι) : ℝ :=
  if J.map σ.toEmbedding = I then 1 else 0

/-- A linear combination of subset-image events evaluates on the actual
squared minors without matching the full table by positive weights. -/
theorem signed_expectation_subsetImageCombo {κ : Type*} [Fintype κ]
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) (I J : κ → Finset ι) (c : κ → ℝ) :
    (∑ σ : Equiv.Perm ι, realSignedWeight U σ *
        ∑ k, c k * subsetImageEvent (I k) (J k) σ) =
      ∑ k, c k * subsetMinorSq U (I k) (J k) := by
  classical
  have hm (k : κ) : (∑ σ ∈ Finset.univ.filter
      (fun σ : Equiv.Perm ι => (J k).map σ.toEmbedding = I k), realSignedWeight U σ) =
        subsetMinorSq U (I k) (J k) := by
    simpa only [realSignedWeight, Complex.re_sum, Complex.ofReal_re] using
      congrArg Complex.re (sum_signedWeight_image_eq_subsetMinorSq U hU (I k) (J k))
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp_rw [mul_left_comm (realSignedWeight U _) (c k)]
  rw [← Finset.mul_sum]
  congr 1
  simp_rw [subsetImageEvent, mul_ite, mul_one, mul_zero, ← Finset.sum_filter]
  exact hm k

omit [Fintype ι] in
/-- At a contact permutation, each subset event used with positive coefficient
in a nonnegative certificate must vanish. The statement is symbolic and can
prune generators without enumerating contact sets. -/
theorem subsetImageCertificate_zero_contact {κ : Type*} [Fintype κ]
    (I J : κ → Finset ι) (c : κ → ℝ) (hc : ∀ k, 0 ≤ c k)
    (σ : Equiv.Perm ι) (hzero : ∑ k, c k * subsetImageEvent (I k) (J k) σ = 0)
    {k : κ} (hk : 0 < c k) : (J k).map σ.toEmbedding ≠ I k := by
  classical
  intro he
  have hnon (l : κ) : 0 ≤ c l * subsetImageEvent (I l) (J l) σ := by
    apply mul_nonneg (hc l)
    unfold subsetImageEvent
    split <;> norm_num
  have hle : c k * subsetImageEvent (I k) (J k) σ ≤
      ∑ l, c l * subsetImageEvent (I l) (J l) σ :=
    Finset.single_le_sum (fun l _ => hnon l)
      (Finset.mem_univ k)
  rw [hzero] at hle
  have hle' : c k ≤ 0 := by simpa [subsetImageEvent, he] using hle
  exact (not_le_of_gt hk) hle'

/-- A support deficit can be certified on the smaller class of objectives
actually under study. Nonnegative subset coefficients plus a residual of
nonnegative signed expectation suffice. In particular, a minor-only
decomposition sets the residual to zero. -/
theorem spectral_support_of_subsetImage_certificate {κ : Type*} [Fintype κ]
    (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U) (η : ℂ) (bound : ℝ)
    (I J : κ → Finset ι) (c : κ → ℝ) (hc : ∀ k, 0 ≤ c k)
    (r : Equiv.Perm ι → ℝ) (hr : 0 ≤ ∑ σ, realSignedWeight U σ * r σ)
    (hcert : ∀ σ, bound - (η * matchingProduct a b σ).re =
      r σ + ∑ k, c k * subsetImageEvent (I k) (J k) σ) :
    (η * determinantValue a b U).re ≤ bound := by
  classical
  have hdet : ∑ σ : Equiv.Perm ι, realSignedWeight U σ * (η * matchingProduct a b σ).re =
      (η * determinantValue a b U).re := by
    have he := congrArg (fun z : ℂ => (η * z).re) (real_signed_determinant a b U hU)
    simp only [Finset.mul_sum, Complex.re_sum] at he
    calc
      _ = ∑ σ : Equiv.Perm ι, (η * ((realSignedWeight U σ : ℂ) * matchingProduct a b σ)).re := by
        apply Finset.sum_congr rfl
        intro σ _
        rw [mul_left_comm, Complex.mul_re]
        simp
      _ = _ := he
  apply sub_nonneg.mp
  calc
    0 ≤ (∑ σ, realSignedWeight U σ * r σ) +
        ∑ k, c k * subsetMinorSq U (I k) (J k) :=
      add_nonneg hr (Finset.sum_nonneg fun k _ => mul_nonneg (hc k) (subsetMinorSq_nonneg U _ _))
    _ = ∑ σ, realSignedWeight U σ * (bound - (η * matchingProduct a b σ).re) := by
      simp_rw [hcert, mul_add, Finset.sum_add_distrib, signed_expectation_subsetImageCombo U hU I J c]
    _ = bound - (η * determinantValue a b U).re := by
      simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, sum_realSignedWeight U hU, one_mul, hdet]

/-- For a *fixed* weight vector, retaining all real spectral objectives is
already as strong as retaining all complex determinant evaluations. Real
binary marker pairs isolate the squared minors. This does not assert a
common law exists: all real spectral instances can hold separately while
a proposed full minor law still fails. -/
theorem fixed_weight_eq_all_iff_real_spectral_objectives
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) (w : Equiv.Perm ι → ℝ) :
    (∀ a b : ι → ℂ, weightedMatchingValue a b w = determinantValue a b U) ↔
    (∀ a b : ι → ℝ,
      (weightedMatchingValue (fun i => (a i : ℂ)) (fun i => (b i : ℂ)) w).re =
      (determinantValue (fun i => (a i : ℂ)) (fun i => (b i : ℂ)) U).re) := by
  classical
  constructor
  · intro h a b
    exact congrArg Complex.re (h _ _)
  · intro h
    apply (weightedMatchingValue_eq_all_iff_subset_markers U hU w).mpr
    intro I J hc _
    have ha : (fun i : ι => ((if i ∈ I then 0 else 1 : ℝ) : ℂ)) =
        fun i => if i ∈ I then (0 : ℂ) else 1 := by
      funext i
      split <;> simp_all
    have hb : (fun i : ι => ((if i ∈ J then 1 else 0 : ℝ) : ℂ)) =
        fun i => if i ∈ J then (1 : ℂ) else 0 := by
      funext i
      split <;> simp_all
    have he := h (fun i => if i ∈ I then 0 else 1) (fun i => if i ∈ J then 1 else 0)
    rw [ha, hb, weightedMatchingValue_subset_marker w I J hc,
      determinantValue_subset_marker U hU I J hc, Complex.ofReal_re, Complex.ofReal_re] at he
    rw [weightedMatchingValue_subset_marker w I J hc, determinantValue_subset_marker U hU I J hc, he]

private def squareCoord (b : Bool) : ℝ := if b then 1 else -1

private def squareVertex (b : Bool × Bool) : ℂ :=
  (squareCoord b.1 : ℂ) + (squareCoord b.2 : ℂ) * Complex.I

private theorem mem_squareVertex_hull {z : ℂ} (h : ‖z‖ ≤ 1) :
    z ∈ convexHull ℝ (Set.range squareVertex) := by
  let K : Set ℝ := {-1, 1}
  let f : ℝ × ℝ →ₗ[ℝ] ℂ := Complex.equivRealProdCLM.symm.toLinearEquiv.toLinearMap
  have hcoord : Set.range squareCoord = K := by
    ext x
    constructor
    · rintro ⟨b, rfl⟩
      cases b <;> simp [squareCoord, K]
    · intro hx
      have he : x = -1 ∨ x = 1 := by simpa [K] using hx
      rcases he with rfl | rfl
      · exact ⟨false, rfl⟩
      · exact ⟨true, rfl⟩
  have hsq : Set.range squareVertex = f '' (K ×ˢ K) := by
    ext x
    constructor
    · rintro ⟨b, rfl⟩
      refine ⟨(squareCoord b.1, squareCoord b.2), ?_, ?_⟩
      · exact ⟨hcoord ▸ ⟨b.1, rfl⟩, hcoord ▸ ⟨b.2, rfl⟩⟩
      · exact Complex.equivRealProdCLM_symm_apply _
    · rintro ⟨⟨r, s⟩, ⟨hr, hs⟩, rfl⟩
      rw [← hcoord] at hr hs
      obtain ⟨a, rfl⟩ := hr
      obtain ⟨b, rfl⟩ := hs
      refine ⟨(a, b), ?_⟩
      change squareVertex (a, b) = Complex.equivRealProdCLM.symm (squareCoord a, squareCoord b)
      rw [Complex.equivRealProdCLM_symm_apply]
      rfl
  rw [hsq, ← f.image_convexHull, convexHull_prod]
  refine ⟨(z.re, z.im), ?_, ?_⟩
  · change z.re ∈ convexHull ℝ ({-1, 1} : Set ℝ) ∧
      z.im ∈ convexHull ℝ ({-1, 1} : Set ℝ)
    rw [convexHull_pair, segment_eq_Icc (by norm_num : (-1 : ℝ) ≤ 1)]
    exact ⟨abs_le.mp ((Complex.abs_re_le_norm z).trans h),
      abs_le.mp ((Complex.abs_im_le_norm z).trans h)⟩
  · change Complex.equivRealProdCLM.symm (z.re, z.im) = z
    rw [Complex.equivRealProdCLM_symm_apply, Complex.re_add_im]

/-- A fixed family of even quadratics. Its pointwise hulls contain the odd
linear evaluation, but an affine combination of the functions is still even. -/
noncomputable def evenQuadraticProfile : (Bool × Bool) ⊕ (Bool × Bool) → ℂ → ℂ
  | .inl b, _ => squareVertex b
  | .inr b, z => z ^ 2 * squareVertex b

theorem identity_mem_evenQuadratic_pointwise_hull (z : ℂ) :
    z ∈ convexHull ℝ (Set.range (fun p => evenQuadraticProfile p z)) := by
  by_cases h : ‖z‖ ≤ 1
  · apply convexHull_mono _ (mem_squareVertex_hull h)
    rintro _ ⟨b, rfl⟩
    exact ⟨.inl b, rfl⟩
  · have hnorm : 1 < ‖z‖ := lt_of_not_ge h
    have hz : z ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (lt_trans zero_lt_one hnorm))
    have hi : ‖z⁻¹‖ ≤ 1 := by
      rw [norm_inv]
      exact (inv_le_one₀ (zero_lt_one.trans hnorm)).mpr hnorm.le
    let f : ℂ →ₗ[ℝ] ℂ := LinearMap.mulLeft ℝ (z ^ 2)
    have hf : f z⁻¹ = z := by
      change z ^ 2 * z⁻¹ = z
      rw [pow_two, mul_assoc, mul_inv_cancel₀ hz, mul_one]
    have hid : f z⁻¹ ∈ convexHull ℝ (f '' Set.range squareVertex) := by
      rw [← f.image_convexHull]
      exact ⟨z⁻¹, mem_squareVertex_hull hi, rfl⟩
    have hid' : z ∈ convexHull ℝ (f '' Set.range squareVertex) := by rwa [← hf]
    apply convexHull_mono _ hid'
    rintro _ ⟨_, ⟨b, rfl⟩, rfl⟩
    exact ⟨.inr b, rfl⟩

/-- Failure of common weights in the quadratic example has nothing to do with
positivity: every fixed linear combination is even, while the target is odd.
This is a functional obstruction, not a numerical matrix counterexample. -/
theorem no_common_evenQuadratic_law {P : Type*} [Fintype P]
    (p : P → (Bool × Bool) ⊕ (Bool × Bool)) (w : P → ℝ) :
    ¬ ∀ z : ℂ, (∑ i, (w i : ℂ) * evenQuadraticProfile (p i) z) = z := by
  intro h
  have he (t : (Bool × Bool) ⊕ (Bool × Bool)) (z : ℂ) :
      evenQuadraticProfile t (-z) = evenQuadraticProfile t z := by
    cases t <;> simp [evenQuadraticProfile, neg_sq]
  have hneg := h (-1)
  simp only [he, h 1] at hneg
  norm_num at hneg

end

end MOC
