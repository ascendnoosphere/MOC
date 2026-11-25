import MOC.GeneralContactReduction
import MOC.MatchingProfileClosed
import MOC.CollinearKernelSupport

/-! Both limits in the varying-gap contact argument are impossible. The
common profile coordinate either converges after division by the gap,
or dominates it. In the latter case the tangent at the constant
profile, rather than the profile itself, supplies the comparison. -/

open BigOperators Filter Matrix Set
open scoped Topology

namespace MOC

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem profile_gap_nonpos_of_singleton_expansion
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) (η : ℂ) (r : Equiv.Perm ι)
    (d : Equiv.Perm ι → ℂ) (c : ℂ) (Q : ι → ι → ℂ)
    (hd : ∀ q, d q = c + ∑ j, Q j (q j))
    (hr : ∀ q, 0 ≤ (η * (d r - d q)).re) :
    (matchingProfileDetGap U η r d).re ≤ 0 := by
  have heval (w : Equiv.Perm ι → ℂ) (hs : ∑ σ, w σ = 1) :
      ∑ σ, w σ * d σ = c + ∑ j, ∑ i, marginal w i j * Q j i := by
    simp_rw [hd, mul_add, Finset.mul_sum]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, hs, one_mul, Finset.sum_comm]
    simp_rw [sum_weighted_evaluation]
  obtain ⟨w, hw, hs, hm⟩ := exists_singleton_weights U hU
  let v (q : Equiv.Perm ι) : ℂ := realSignedWeight U q
  have hvs : ∑ q, v q = 1 := by
    dsimp only [v]
    exact_mod_cast sum_realSignedWeight U hU
  have hws : ∑ q, (w q : ℂ) = 1 := by exact_mod_cast hs
  have hvm (i j : ι) : marginal v i j = (Complex.normSq (U i j) : ℂ) := by
    have hh := congrArg (fun t : ℝ => (t : ℂ)) (marginal_realSignedWeight U hU i j)
    simpa only [marginal, Complex.ofReal_sum, apply_ite, Complex.ofReal_zero, v] using hh
  have hsame : ∑ q, v q * d q = ∑ q, (w q : ℂ) * d q := by
    rw [heval v hvs, heval _ hws]
    simp_rw [hvm, hm]
  have hG (f : Equiv.Perm ι → ℂ) (hf : ∑ q, f q = 1) :
      ∑ q, f q * (η * (d q - d r)) = η * ((∑ q, f q * d q) - d r) := by
    simp_rw [← mul_left_comm η, ← Finset.mul_sum, mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hf, one_mul]
    ring
  have he : matchingProfileDetGap U η r d = ∑ q, (w q : ℂ) * (η * (d q - d r)) := by
    rw [matchingProfileDetGap, hG v hvs, hsame, hG _ hws]
  rw [he, Complex.re_sum]
  refine Finset.sum_nonpos fun q _ => ?_
  rw [Complex.re_ofReal_mul]
  have hh := hr q
  rw [mul_sub, Complex.sub_re] at hh ⊢
  exact mul_nonpos_of_nonneg_of_nonpos (hw q) (sub_nonpos.mpr (sub_nonneg.mp hh))

omit [DecidableEq ι] in
private theorem normalized_profile_is_exact [Nonempty ι]
    {p : Equiv.Perm ι → ℂ} (hp : ∃ a b : ι → ℂ, matchingProduct a b = p)
    (k : ℂ) :
    ∃ a b : ι → ℂ, matchingProduct a b = fun q => k * p q := by
  obtain ⟨a,b,rfl⟩ := hp
  obtain ⟨z,hz⟩ := IsAlgClosed.exists_pow_nat_eq k (Fintype.card_pos (α := ι))
  refine ⟨fun i => z * a i, fun i => z * b i, ?_⟩
  funext q
  rw [matchingProduct_scale, hz]

private theorem profile_gap_nonpos_of_collinear_profile
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) (η : ℂ) (hη : η ≠ 0) (r : Equiv.Perm ι)
    (a b : ι → ℂ)
    (hline : ∀ q, (η * (matchingProduct a b r - matchingProduct a b q)).im = 0)
    (hmax : ∀ q, 0 ≤ (η * (matchingProduct a b r - matchingProduct a b q)).re) :
    (matchingProfileDetGap U η r (matchingProduct a b)).re ≤ 0 := by
  let k := Complex.I * η
  have hk : k ≠ 0 := mul_ne_zero Complex.I_ne_zero hη
  have hhold : Holds a b U := by
    apply holds_of_collinear_matching_profile a b k hk (k * matchingProduct a b r).re
      (U := U) (hU := hU)
    intro σ
    have h := hline σ
    rw [mul_sub, Complex.sub_im, sub_eq_zero] at h
    simpa only [k, mul_assoc, Complex.mul_re, Complex.I_re, Complex.I_im,
      zero_mul, one_mul, zero_sub] using congrArg Neg.neg h.symm
  obtain ⟨q,hq⟩ := (holds_iff_directional _ _ _).mp hhold η
  have hq' := hmax q
  rw [matchingProfileDetGap_matchingProduct _ _ _ hU, mul_sub, Complex.sub_re]
  rw [mul_sub, Complex.sub_re] at hq'
  linarith

/-- A would-be limit at a pole of a varying strict determinant gap is
impossible if all gap-normalized contact differences approach real
nonnegative values. The final hypothesis is the dichotomy for the
common coordinate: it either converges, or its reciprocal tends to zero. -/
theorem not_profile_gap_asymptotic [Nonempty ι]
    {α : Type*} {l : Filter α} [l.NeBot]
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) (η : ℂ) (hη : η ≠ 0) (r : Equiv.Perm ι)
    (P : α → Equiv.Perm ι → ℂ)
    (hex : ∀ᶠ t in l, ∃ a b : ι → ℂ, matchingProduct a b = P t)
    (d : Equiv.Perm ι → ℂ)
    (hlim : ∀ q, Tendsto (fun t => (P t q - P t r) / matchingProfileDetGap U η r (P t)) l (𝓝 (d q)))
    (hgap : ∀ᶠ t in l, matchingProfileDetGap U η r (P t) ≠ 0)
    (hreal : ∀ q, (η * (d r - d q)).im = 0)
    (hpos : ∀ q, 0 ≤ (η * (d r - d q)).re)
    (hcommon :
      (∃ c, Tendsto (fun t => P t r / matchingProfileDetGap U η r (P t)) l (𝓝 c)) ∨
      (Tendsto (fun t => matchingProfileDetGap U η r (P t) / P t r) l (𝓝 0) ∧
        ∀ᶠ t in l, P t r ≠ 0)) : False := by
  let g (t : α) := matchingProfileDetGap U η r (P t)
  let v (t : α) (q : Equiv.Perm ι) := (P t q - P t r) / g t
  have hgaplim :
      Tendsto (fun t => matchingProfileDetGap U η r (v t)) l
        (𝓝 (matchingProfileDetGap U η r d)) := by
    unfold matchingProfileDetGap
    exact tendsto_finset_sum _ fun q _ =>
      tendsto_const_nhds.mul (tendsto_const_nhds.mul ((hlim q).sub (hlim r)))
  have hgap1 : matchingProfileDetGap U η r d = 1 := by
    apply tendsto_nhds_unique_of_eventuallyEq hgaplim tendsto_const_nhds
    filter_upwards [hgap] with t ht
    calc
      _ = g t / g t := by
        dsimp only [matchingProfileDetGap, g, v]
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl fun _ _ => by ring
      _ = 1 := div_self ht
  rcases hcommon with ⟨c,hc⟩ | ⟨he,hp⟩
  · let D (q : Equiv.Perm ι) := d q + c
    have hcon :
        Tendsto (fun t q => (g t)⁻¹ * P t q) l (𝓝 D) := by
      apply tendsto_pi_nhds.mpr
      intro q
      have hh := (hlim q).add hc
      apply hh.congr'
      exact Eventually.of_forall fun t => by dsimp [g]; ring
    have hclosed := isClosed_additive_matching_profiles (ι := ι)
    have hD := hclosed.mem_of_tendsto hcon (hex.mono fun t ht => normalized_profile_is_exact ht _)
    obtain ⟨a,b,hab⟩ := hD
    have heq (q : Equiv.Perm ι) :
        matchingProduct a b r - matchingProduct a b q = d r - d q := by
      rw [congrFun hab r, congrFun hab q]
      dsimp [D]
      ring
    have hh := profile_gap_nonpos_of_collinear_profile U hU η hη r a b
      (fun q => by rw [heq]; exact hreal q) (fun q => by rw [heq]; exact hpos q)
    have hgD : matchingProfileDetGap U η r (matchingProduct a b) = matchingProfileDetGap U η r d := by
      simp only [matchingProfileDetGap, ← neg_sub (matchingProduct a b r), ← neg_sub (d r), heq]
    rw [hgD, hgap1, Complex.one_re] at hh
    exact (not_le_of_gt zero_lt_one) hh
  · let ε (t : α) := g t / P t r
    have hne : ∀ᶠ t in l, ε t ≠ 0 := by
      filter_upwards [hgap,hp] with t hg hr
      exact div_ne_zero hg hr
    have hex' : ∀ᶠ t in l, ∃ a b : ι → ℂ, matchingProduct a b = fun q => 1 + ε t * v t q := by
      filter_upwards [hex,hgap,hp] with t ht hg hr
      obtain ⟨a,b,hab⟩ := normalized_profile_is_exact ht (P t r)⁻¹
      refine ⟨a,b,hab.trans ?_⟩
      funext q
      dsimp [ε,v,g]
      field_simp [hg, hr]
      ring
    obtain ⟨c,Q,hQ⟩ := singleton_expansion_of_matching_profile_tangent_at_one ε he hne v d hlim hex'
    have hh := profile_gap_nonpos_of_singleton_expansion U hU η r d c Q hQ hpos
    rw [hgap1, Complex.one_re] at hh
    exact (not_le_of_gt zero_lt_one) hh

end MOC
