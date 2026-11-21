import MOC.Weights
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Topology.Instances.Matrix

open BigOperators Matrix
open scoped Topology

namespace MOC

noncomputable section

private theorem linearFunctional_eq (f : ℂ →L[ℝ] ℝ) (z : ℂ) :
    f z = (((f 1 : ℂ) - (f Complex.I : ℂ) * Complex.I) * z).re := by
  have hz : z.re • (1 : ℂ) + z.im • Complex.I = z := by
    simp [Complex.real_smul, Complex.re_add_im]
  calc
    f z = f (z.re • (1 : ℂ) + z.im • Complex.I) := congrArg f hz.symm
    _ = _ := by
      rw [map_add, map_smul, map_smul]
      simp [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, smul_eq_mul]
      ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
private theorem exists_matching_max (a b : ι → ℂ) (k : ℂ) :
    ∃ σ : Equiv.Perm ι, ∀ τ : Equiv.Perm ι,
      (k * matchingProduct a b τ).re ≤ (k * matchingProduct a b σ).re := by
  classical
  obtain ⟨σ, _, hσ⟩ := Finset.exists_max_image Finset.univ
    (fun τ : Equiv.Perm ι => (k * matchingProduct a b τ).re)
    ⟨Equiv.refl ι, Finset.mem_univ _⟩
  exact ⟨σ, fun τ => hσ τ (Finset.mem_univ _)⟩

/-- A point belongs to the matching hull exactly when every real projection is bounded
by a matching product. -/
theorem holds_iff_directional (a b : ι → ℂ) (U : Matrix ι ι ℂ) :
    Holds a b U ↔ ∀ k : ℂ, ∃ σ : Equiv.Perm ι,
      (k * determinantValue a b U).re ≤ (k * matchingProduct a b σ).re := by
  classical
  constructor
  · intro h k
    let f : ℂ →ₗ[ℝ] ℝ := Complex.reLm.comp (LinearMap.mulLeft ℝ k)
    obtain ⟨σ, hσ⟩ := exists_matching_max a b k
    refine ⟨σ, ?_⟩
    change f (determinantValue a b U) ≤ f (matchingProduct a b σ)
    apply convexHull_min ?_ (convex_halfSpace_le f.isLinear _) h
    rintro _ ⟨τ, rfl⟩
    exact hσ τ
  · intro h
    by_contra hn
    unfold Holds at hn
    have hc : IsClosed (convexHull ℝ (Set.range (matchingProduct a b))) :=
      Set.finite_range (matchingProduct a b) |>.isClosed_convexHull
    obtain ⟨f, t, ht, hd⟩ :=
      geometric_hahn_banach_closed_point (convex_convexHull ℝ _) hc hn
    obtain ⟨σ, hσ⟩ := h ((f 1 : ℂ) - (f Complex.I : ℂ) * Complex.I)
    rw [← linearFunctional_eq, ← linearFunctional_eq] at hσ
    exact (lt_irrefl _) ((ht _ (matchingProduct_mem_hull a b σ)).trans (hd.trans_le hσ))

omit [DecidableEq ι] in
theorem matchingProduct_scale (a b : ι → ℂ) (c : ℂ) (σ : Equiv.Perm ι) :
    matchingProduct (fun i => c * a i) (fun i => c * b i) σ =
      c ^ Fintype.card ι * matchingProduct a b σ := by
  unfold matchingProduct
  simp only [← mul_add, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]

theorem determinantValue_scale (a b : ι → ℂ) (U : Matrix ι ι ℂ) (c : ℂ) :
    determinantValue (fun i => c * a i) (fun i => c * b i) U =
      c ^ Fintype.card ι * determinantValue a b U := by
  have hd (v : ι → ℂ) : diagonal (fun i => c * v i) = c • diagonal v := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.diagonal_apply, h, smul_eq_mul]
  unfold determinantValue
  rw [hd a, hd b, Matrix.mul_smul, Matrix.smul_mul, ← smul_add, Matrix.det_smul]

/-- Scaling both spectra by an nth root absorbs the support direction in positive order. -/
theorem conjecture_iff_real_bound [Nonempty ι] : Conjecture ι ↔
    ∀ (a b : ι → ℂ) (U : Matrix ι ι ℂ), IsUnitary U →
      ∃ σ : Equiv.Perm ι, (determinantValue a b U).re ≤ (matchingProduct a b σ).re := by
  constructor
  · intro h a b U hU
    simpa using (holds_iff_directional a b U).mp (h a b U hU) 1
  · intro h a b U hU
    apply (holds_iff_directional a b U).mpr
    intro k
    let c : ℂ := k ^ ((Fintype.card ι : ℂ)⁻¹)
    have hc : c ^ Fintype.card ι = k := Complex.cpow_nat_inv_pow k Fintype.card_ne_zero
    obtain ⟨σ, hs⟩ := h (fun i => c * a i) (fun i => c * b i) U hU
    rw [determinantValue_scale, matchingProduct_scale, hc] at hs
    exact ⟨σ, hs⟩

/-- A common perturbation of the first spectrum avoids all opposite pairs while
preserving any strict support violation for the same relative basis. -/
theorem conjecture_iff_nonopposite : Conjecture ι ↔
    ∀ (a b : ι → ℂ) (U : Matrix ι ι ℂ), IsUnitary U →
      (∀ i j, a i + b j ≠ 0) → Holds a b U := by
  constructor
  · intro h a b U hU _
    exact h a b U hU
  · intro h a b U hU
    by_contra hfalse
    rw [holds_iff_directional, not_forall] at hfalse
    obtain ⟨k, hk⟩ := hfalse
    push_neg at hk
    let a' (t : ℝ) (i : ι) := a i + (t : ℂ)
    have hz : a' 0 = a := by ext i; simp [a']
    have hd : Continuous (fun t => (k * determinantValue (a' t) b U).re) := by
      have ha : Continuous a' := continuous_pi fun i => by
        dsimp [a']
        fun_prop
      unfold determinantValue
      fun_prop
    have hm (σ : Equiv.Perm ι) : Continuous (fun t => (k * matchingProduct (a' t) b σ).re) := by
      have hp : Continuous (fun t => matchingProduct (a' t) b σ) := by
        unfold matchingProduct
        apply continuous_finset_prod
        intro j _
        dsimp [a']
        fun_prop
      fun_prop
    have hsep : ∀ᶠ t in 𝓝[≠] (0 : ℝ), ∀ σ : Equiv.Perm ι,
        (k * matchingProduct (a' t) b σ).re < (k * determinantValue (a' t) b U).re := by
      apply Filter.eventually_all.mpr
      intro σ
      exact ((hm σ).continuousAt.eventually_lt hd.continuousAt
        (by simpa [hz] using hk σ)).filter_mono nhdsWithin_le_nhds
    have hreg : ∀ᶠ t in 𝓝[≠] (0 : ℝ), ∀ i j, a' t i + b j ≠ 0 := by
      apply Filter.eventually_all.mpr
      intro i
      apply Filter.eventually_all.mpr
      intro j
      by_cases hj : a i + b j = 0
      · filter_upwards [self_mem_nhdsWithin] with t ht
        have ht' : t ≠ 0 := ht
        have hs : a' t i + b j = (t : ℂ) := by
          dsimp [a']
          rw [add_right_comm, hj, zero_add]
        rw [hs]
        exact Complex.ofReal_ne_zero.mpr ht'
      · have hc : Continuous (fun t => a' t i + b j) := by
          dsimp [a']
          fun_prop
        exact (hc.continuousAt.eventually_ne (by simpa [hz] using hj)).filter_mono
          nhdsWithin_le_nhds
    obtain ⟨t, htsep, htreg⟩ := (hsep.and hreg).exists
    obtain ⟨σ, hσ⟩ := (holds_iff_directional (a' t) b U).mp (h (a' t) b U hU htreg) k
    exact (not_le_of_gt (htsep σ)) hσ

omit [DecidableEq ι] in
/-- Real difference between two matching products in a chosen support direction. -/
def matchingGap (a b : ι → ℂ) (k : ℂ) (r σ : Equiv.Perm ι) : ℝ :=
  (k * matchingProduct a b r).re - (k * matchingProduct a b σ).re

/-- The real support gap is the signed sum of the matching gaps. A maximizing permutation
gives nonnegative matching gaps even when the signed sum is negative. -/
theorem support_gap_eq (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U) (k : ℂ)
    (r : Equiv.Perm ι) :
    (k * matchingProduct a b r).re - (k * determinantValue a b U).re =
      ∑ σ, realSignedWeight U σ * matchingGap a b k r σ := by
  unfold matchingGap
  have hv := congrArg (fun z : ℂ => (k * z).re) (real_signed_determinant a b U hU)
  simp only [Finset.mul_sum, Complex.re_sum] at hv
  calc
    _ = (∑ σ, realSignedWeight U σ) * (k * matchingProduct a b r).re -
        ∑ σ, (k * ((realSignedWeight U σ : ℂ) * matchingProduct a b σ)).re := by
      rw [sum_realSignedWeight U hU, one_mul, hv]
    _ = _ := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro σ _
      rw [mul_sub, mul_left_comm k (realSignedWeight U σ : ℂ)]
      simp [Complex.mul_re]

/-- Unit total matching gap suffices. If every matching lies on the same support line,
the signed sum is zero. -/
theorem holds_iff_normalized_support_gaps (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U) :
    Holds a b U ↔ ∀ (k : ℂ) (r : Equiv.Perm ι),
      (∀ σ, 0 ≤ matchingGap a b k r σ) → (∑ σ, matchingGap a b k r σ) = 1 →
      0 ≤ ∑ σ, realSignedWeight U σ * matchingGap a b k r σ := by
  constructor
  · intro h k r hr _
    rw [← support_gap_eq a b U hU k r]
    obtain ⟨σ, hσ⟩ := (holds_iff_directional a b U).mp h k
    exact sub_nonneg.mpr (hσ.trans (sub_nonneg.mp (hr σ)))
  · intro h
    apply (holds_iff_directional a b U).mpr
    intro k
    obtain ⟨r, hr⟩ := exists_matching_max a b k
    refine ⟨r, sub_nonneg.mp ?_⟩
    rw [support_gap_eq a b U hU k r]
    let g := ∑ σ, matchingGap a b k r σ
    have hn (σ : Equiv.Perm ι) : 0 ≤ matchingGap a b k r σ := sub_nonneg.mpr (hr σ)
    by_cases hg : g = 0
    · have hz (σ : Equiv.Perm ι) : matchingGap a b k r σ = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg fun σ _ => hn σ).mp hg σ (Finset.mem_univ _)
      simp [hz]
    · have hgpos : 0 < g := lt_of_le_of_ne (Finset.sum_nonneg fun σ _ => hn σ) (Ne.symm hg)
      let c : ℂ := (g⁻¹ : ℝ)
      have hscale (σ : Equiv.Perm ι) :
          matchingGap a b (c * k) r σ = g⁻¹ * matchingGap a b k r σ := by
        simp [matchingGap, mul_assoc, Complex.mul_re, c, mul_sub]
      have hnorm : (∑ σ, matchingGap a b (c * k) r σ) = 1 := by
        simp_rw [hscale, ← Finset.mul_sum]
        exact inv_mul_cancel₀ hg
      have hscaled := h (c * k) r (fun σ => by
        rw [hscale]
        exact mul_nonneg (inv_nonneg.mpr hgpos.le) (hn σ)) hnorm
      simp_rw [hscale, mul_left_comm (realSignedWeight U _), ← Finset.mul_sum] at hscaled
      exact nonneg_of_mul_nonneg_right hscaled (inv_pos.mpr hgpos)

/-- When the matching hull spans the plane, a strict separator can be moved to a
direction with two distinct maximizing vertices, at fixed spectra and relative basis.
The displacement preserves the gap between the determinant and the original vertex. -/
theorem not_holds_two_contacts_or_collinear (a b : ι → ℂ) (U : Matrix ι ι ℂ)
    (h : ¬ Holds a b U) :
    (∃ (k : ℂ) (r s : Equiv.Perm ι), matchingProduct a b r ≠ matchingProduct a b s ∧
      matchingGap a b k r s = 0 ∧ (∀ σ, 0 ≤ matchingGap a b k r σ) ∧
      (k * matchingProduct a b r).re < (k * determinantValue a b U).re) ∨
    (∃ q : ℂ, q ≠ 0 ∧ ∃ r : Equiv.Perm ι, ∀ σ, matchingGap a b q r σ = 0) := by
  classical
  rw [holds_iff_directional, not_forall] at h
  obtain ⟨k, hk⟩ := h
  push_neg at hk
  obtain ⟨r, hr⟩ := exists_matching_max a b k
  let z := matchingProduct a b
  let d := determinantValue a b U
  let q : ℂ := Complex.I * star (d - z r)
  have hq : (q * (d - z r)).re = 0 := by
    rw [show q = Complex.I * star (d - z r) from rfl, mul_assoc, Complex.star_def,
      ← Complex.normSq_eq_conj_mul_self]
    simp [Complex.mul_re]
  by_cases hline : ∀ σ, matchingGap a b q r σ = 0
  · have hdr : d - z r ≠ 0 := sub_ne_zero.mpr (by
      intro e
      have hkr : (k * z r).re < (k * d).re := hk r
      rw [e] at hkr
      exact (lt_irrefl _) hkr)
    exact Or.inr ⟨q, mul_ne_zero Complex.I_ne_zero (star_ne_zero.mpr hdr), r, hline⟩
  · push_neg at hline
    obtain ⟨i, hi⟩ := hline
    have hneg (σ : Equiv.Perm ι) : matchingGap a b (-q) r σ = -matchingGap a b q r σ := by
      simp only [matchingGap, neg_mul, Complex.neg_re]
      ring
    have ⟨p, hp, hpi⟩ : ∃ p : ℂ, (p * (d - z r)).re = 0 ∧ matchingGap a b p r i < 0 := by
      rcases lt_or_gt_of_ne hi with hn | hn
      · exact ⟨q, hq, hn⟩
      · exact ⟨-q, by simp [neg_mul, Complex.neg_re, hq], by rw [hneg]; exact neg_lt_zero.mpr hn⟩
    let D := Finset.univ.filter (fun σ => matchingGap a b p r σ < 0)
    let t (σ : Equiv.Perm ι) := matchingGap a b k r σ / -matchingGap a b p r σ
    obtain ⟨s, hs, hmin⟩ := Finset.exists_min_image D t
      ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpi⟩⟩
    have hslope : matchingGap a b p r s < 0 := (Finset.mem_filter.mp hs).2
    have hn (σ : Equiv.Perm ι) : 0 ≤ matchingGap a b k r σ := sub_nonneg.mpr (hr σ)
    have hts : 0 ≤ t s := div_nonneg (hn s) (neg_nonneg.mpr hslope.le)
    have hstep (v : ℂ) : ((k + (t s : ℂ) * p) * v).re =
        (k * v).re + t s * (p * v).re := by
      simp only [add_mul, Complex.add_re, mul_assoc, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero]
    let k' := k + (t s : ℂ) * p
    have hgap (σ : Equiv.Perm ι) : matchingGap a b k' r σ =
        matchingGap a b k r σ + t s * matchingGap a b p r σ := by
      simp only [k', matchingGap]
      rw [hstep, hstep]
      ring
    refine Or.inl ⟨k', r, s, ?_, ?_, ?_, ?_⟩
    · intro eq
      simp [matchingGap, eq] at hslope
    · have hh := div_mul_cancel₀ (matchingGap a b k r s)
        (neg_ne_zero.mpr hslope.ne)
      rw [hgap]
      change t s * -matchingGap a b p r s = matchingGap a b k r s at hh
      linarith only [hh]
    · intro σ
      rw [hgap]
      by_cases hσ : matchingGap a b p r σ < 0
      · have hle : t s * -matchingGap a b p r σ ≤ matchingGap a b k r σ :=
          (le_div_iff₀ (neg_pos.mpr hσ)).mp
            (hmin σ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hσ⟩))
        linarith only [hle]
      · exact add_nonneg (hn σ) (mul_nonneg hts (le_of_not_gt hσ))
    · change (k' * z r).re < (k' * d).re
      have hkGap : 0 < (k * (d - z r)).re := by
        simpa only [mul_sub, Complex.sub_re, sub_pos] using hk r
      rw [← sub_pos, ← Complex.sub_re, ← mul_sub, show k' = k + (t s : ℂ) * p from rfl,
        hstep, hp, mul_zero, add_zero]
      exact hkGap

/-- For a noncollinear hull, the normals from ordered pairs of matching products
give a finite support test. Reversing a pair tests the opposite orientation. -/
theorem holds_iff_pair_normals (a b : ι → ℂ) (U : Matrix ι ι ℂ)
    (hnonline : ¬ ∃ q : ℂ, q ≠ 0 ∧ ∃ r : Equiv.Perm ι, ∀ σ, matchingGap a b q r σ = 0) :
    Holds a b U ↔ ∀ r s : Equiv.Perm ι,
      let q := Complex.I * star (matchingProduct a b r - matchingProduct a b s)
      ∃ σ : Equiv.Perm ι, (q * determinantValue a b U).re ≤ (q * matchingProduct a b σ).re := by
  constructor
  · intro h r s
    exact (holds_iff_directional a b U).mp h _
  · intro h
    by_contra hf
    obtain ⟨k, r, s, hne, hz, hmax, hviol⟩ :=
      (not_holds_two_contacts_or_collinear a b U hf).resolve_right hnonline
    let z := matchingProduct a b
    let d := determinantValue a b U
    let v := z r - z s
    let q := Complex.I * star v
    have hv : v ≠ 0 := sub_ne_zero.mpr hne
    have hr : (k * v).re = 0 := by
      change (k * (z r - z s)).re = 0
      rw [mul_sub, Complex.sub_re]
      exact hz
    let c := (k * v).im / Complex.normSq v
    have hc : k = (c : ℂ) * q := by
      apply mul_right_cancel₀ hv
      calc
        k * v = ((k * v).im : ℂ) * Complex.I := by
          simpa [hr] using (Complex.re_add_im (k * v)).symm
        _ = ((c : ℂ) * (Complex.normSq v : ℂ)) * Complex.I := by
          rw [← Complex.ofReal_mul, div_mul_cancel₀ _ (Complex.normSq_pos.mpr hv).ne']
        _ = ((c : ℂ) * q) * v := by
          have hq : q * v = Complex.I * (Complex.normSq v : ℂ) := by
            rw [show q = Complex.I * star v from rfl, mul_assoc, Complex.star_def,
              ← Complex.normSq_eq_conj_mul_self]
          rw [mul_assoc _ q v, hq]
          ring
    have hcne : c ≠ 0 := by
      intro hcz
      simp [hcz] at hc
      simp [hc] at hviol
    have forbid (p : ℂ) (x : ℝ) (hx : 0 < x) (hk : k = (x : ℂ) * p) :
        ¬ ∃ σ : Equiv.Perm ι, (p * d).re ≤ (p * z σ).re := by
      rintro ⟨σ, hs⟩
      have hbad : (k * z σ).re < (k * d).re := (sub_nonneg.mp (hmax σ)).trans_lt hviol
      rw [hk] at hbad
      have hstrict : x * (p * z σ).re < x * (p * d).re := by
        simpa only [mul_assoc, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          zero_mul, sub_zero] using hbad
      exact (not_le_of_gt ((mul_lt_mul_left hx).mp hstrict)) hs
    rcases lt_or_gt_of_ne hcne with hcn | hcp
    · have hrev : Complex.I * star (z s - z r) = -q := by
        rw [show z s - z r = -v from (neg_sub _ _).symm, star_neg, mul_neg]
      have hk : k = ((-c : ℝ) : ℂ) * (-q) := by simpa using hc
      have hs := h s r
      change ∃ σ, ((Complex.I * star (z s - z r)) * d).re ≤
        ((Complex.I * star (z s - z r)) * z σ).re at hs
      rw [hrev] at hs
      exact forbid (-q) (-c) (neg_pos.mpr hcn) hk hs
    · exact forbid q c hcp hc (h r s)

private theorem holds_of_collinear_axes (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (hline : ∃ q : ℂ, q ≠ 0 ∧ ∃ r : Equiv.Perm ι, ∀ σ, matchingGap a b q r σ = 0)
    (haxes : ∀ k : ℂ, (k = 1 ∨ k = -1 ∨ k = Complex.I ∨ k = -Complex.I) →
      ∃ σ : Equiv.Perm ι, (k * determinantValue a b U).re ≤ (k * matchingProduct a b σ).re) :
    Holds a b U := by
  obtain ⟨q, hq, r, hflat⟩ := hline
  by_contra hfalse
  rw [holds_iff_directional, not_forall] at hfalse
  obtain ⟨k, hk⟩ := hfalse
  push_neg at hk
  let z := matchingProduct a b
  let d := determinantValue a b U
  have hdet : (q * d).re = (q * z r).re := by
    have hgap := support_gap_eq a b U hU q r
    simp only [hflat, mul_zero, Finset.sum_const_zero] at hgap
    exact (sub_eq_zero.mp hgap).symm
  have hline' (σ : Equiv.Perm ι) :
      q.re * (d.re - (z σ).re) = q.im * (d.im - (z σ).im) := by
    have hp : (q * z r).re = (q * z σ).re := sub_eq_zero.mp (hflat σ)
    have h := hdet.trans hp
    simp only [Complex.mul_re] at h
    linarith only [h]
  have hex : ∃ (p : ℂ) (c : ℝ), (p = 1 ∨ p = Complex.I) ∧
      ∀ σ : Equiv.Perm ι, (k * d).re - (k * z σ).re = c * ((p * d).re - (p * z σ).re) := by
    by_cases hi : q.im = 0
    · have hr : q.re ≠ 0 := by
        intro e
        exact hq (Complex.ext (by simp [e]) (by simp [hi]))
      refine ⟨Complex.I, k.im, Or.inr rfl, fun σ => ?_⟩
      have hx := hline' σ
      rw [hi, zero_mul] at hx
      have hre : d.re = (z σ).re := sub_eq_zero.mp ((mul_eq_zero.mp hx).resolve_left hr)
      simp only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub, hre]
      ring
    · refine ⟨1, k.re - k.im * (q.re / q.im), Or.inl rfl, fun σ => ?_⟩
      have him : d.im - (z σ).im = q.re * (d.re - (z σ).re) / q.im := by
        apply (eq_div_iff hi).mpr
        rw [mul_comm _ q.im]
        exact (hline' σ).symm
      simp only [one_mul, Complex.mul_re]
      calc
        _ = k.re * (d.re - (z σ).re) - k.im * (d.im - (z σ).im) := by ring
        _ = _ := by rw [him]; simp only [div_eq_mul_inv]; ring
  obtain ⟨p, c, hp, he⟩ := hex
  by_cases hc : 0 ≤ c
  · obtain ⟨σ, hs⟩ := haxes p (hp.elim Or.inl (fun e => Or.inr (Or.inr (Or.inl e))))
    have hm := mul_nonpos_of_nonneg_of_nonpos hc (sub_nonpos.mpr hs)
    have hstrict : 0 < (k * d).re - (k * z σ).re := sub_pos.mpr (hk σ)
    rw [he σ] at hstrict
    exact (not_lt_of_ge hm) hstrict
  · have hn : -p = 1 ∨ -p = -1 ∨ -p = Complex.I ∨ -p = -Complex.I := by
      rcases hp with hp | hp <;> simp [hp]
    obtain ⟨σ, hs⟩ := haxes (-p) hn
    have hs' : (p * z σ).re ≤ (p * d).re := by
      simpa only [neg_mul, Complex.neg_re, neg_le_neg_iff] using hs
    have hm := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hc) (sub_nonneg.mpr hs')
    have hstrict : 0 < (k * d).re - (k * z σ).re := sub_pos.mpr (hk σ)
    rw [he σ] at hstrict
    exact (not_lt_of_ge hm) hstrict

/-- A finite support criterion valid even for collinear and singleton matching hulls.
There are at most four axis directions and one normal per ordered pair. -/
theorem holds_iff_axes_and_pair_normals (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U) :
    Holds a b U ↔
      (∀ k : ℂ, (k = 1 ∨ k = -1 ∨ k = Complex.I ∨ k = -Complex.I) →
        ∃ σ : Equiv.Perm ι, (k * determinantValue a b U).re ≤ (k * matchingProduct a b σ).re) ∧
      (∀ r s : Equiv.Perm ι,
        let k := Complex.I * star (matchingProduct a b r - matchingProduct a b s)
        ∃ σ : Equiv.Perm ι, (k * determinantValue a b U).re ≤ (k * matchingProduct a b σ).re) := by
  constructor
  · intro h
    have h' := (holds_iff_directional a b U).mp h
    exact ⟨fun k _ => h' k, fun _ _ => h' _⟩
  · rintro ⟨haxes, hnormals⟩
    by_cases hline : ∃ q : ℂ, q ≠ 0 ∧ ∃ r : Equiv.Perm ι, ∀ σ, matchingGap a b q r σ = 0
    · exact holds_of_collinear_axes a b U hU hline haxes
    · exact (holds_iff_pair_normals a b U hline).mpr hnormals

end

end MOC
