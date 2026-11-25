import MOC.Weights
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.LinearCombination

/-! At the constant matching profile, the first-order gaps are singleton
assignments. Their signed determinant evaluation obeys Birkhoff's bound. -/

open BigOperators Filter Matrix
open scoped Topology

namespace MOC

private theorem tendsto_product_deficit_div {α ι : Type*} [DecidableEq ι]
    (l : Filter α) (ε : α → ℂ) (F : ι → α → ℂ) (L : ι → ℂ)
    (hε : Tendsto ε l (𝓝 0)) (hnz : ∀ᶠ x in l, ε x ≠ 0)
    (hF : ∀ j, Tendsto (fun x => F j x / ε x) l (𝓝 (L j))) (s : Finset ι) :
    Tendsto (fun x => (1 - ∏ j ∈ s, (1 - F j x)) / ε x) l (𝓝 (∑ j ∈ s, L j)) := by
  have hF₀ (j : ι) : Tendsto (F j) l (𝓝 0) := by
    have h := hε.mul (hF j)
    rw [zero_mul] at h
    refine h.congr' ?_
    filter_upwards [hnz] with x hx
    exact mul_div_cancel₀ (F j x) hx
  induction s using Finset.induction_on with
  | empty => simpa using (tendsto_const_nhds : Tendsto (fun _ : α => (0 : ℂ)) l (𝓝 0))
  | @insert j s hjs ih =>
    have hconst : Tendsto (fun _ : α => (1 : ℂ)) l (𝓝 1) := tendsto_const_nhds
    have hOne : Tendsto (fun x => 1 - F j x) l (𝓝 1) := by
      simpa only [sub_zero] using hconst.sub (hF₀ j)
    have h := (hF j).add (hOne.mul ih)
    rw [one_mul] at h
    rw [Finset.sum_insert hjs]
    refine h.congr' ?_
    filter_upwards [hnz] with x hx
    rw [Finset.prod_insert hjs]
    field_simp [hx] <;> ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Ratios of two profiles converging to the same constant recover the
first-order cross-entry term of their anchored kernel. -/
theorem tendsto_entry_div_of_profile_ratio {α : Type*} (l : Filter α)
    (ε T A B : α → ℂ) (a b : ℂ)
    (hε : Tendsto ε l (𝓝 0)) (hnz : ∀ᶠ x in l, ε x ≠ 0)
    (hA : Tendsto A l (𝓝 a)) (hB : Tendsto B l (𝓝 b))
    (hratio : ∀ᶠ x in l, 1 - T x = (1 - ε x * A x) / (1 - ε x * B x)) :
    Tendsto (fun x => T x / ε x) l (𝓝 (a - b)) := by
  have hconst : Tendsto (fun _ : α => (1 : ℂ)) l (𝓝 1) := tendsto_const_nhds
  have hden : Tendsto (fun x => 1 - ε x * B x) l (𝓝 1) := by
    simpa only [zero_mul, sub_zero] using hconst.sub (hε.mul hB)
  have hlim := (hA.sub hB).div hden one_ne_zero
  rw [div_one] at hlim
  refine hlim.congr' ?_
  filter_upwards [hden.eventually_ne one_ne_zero, hnz, hratio] with x hb hne hx
  change (A x - B x) / (1 - ε x * B x) = T x / ε x
  have hprod := (eq_div_iff hb).mp hx
  have hr : T x * (1 - ε x * B x) = ε x * (A x - B x) := by
    linear_combination -hprod
  apply (div_eq_div_iff hb hne).2
  calc
    (A x - B x) * ε x = ε x * (A x - B x) := mul_comm _ _
    _ = T x * (1 - ε x * B x) := hr.symm

/-- An entrywise first-order perturbation of the all-ones kernel gives an
additive singleton expression for each normalized profile gap. -/
theorem tendsto_constant_profile_gap {α : Type*} (l : Filter α) (ε : α → ℂ)
    (T : α → ι → ι → ℂ) (L : ι → ι → ℂ)
    (hε : Tendsto ε l (𝓝 0)) (hnz : ∀ᶠ x in l, ε x ≠ 0)
    (hT : ∀ i j, Tendsto (fun x => T x i j / ε x) l (𝓝 (L i j)))
    (r σ : Equiv.Perm ι) :
    let P (τ : Equiv.Perm ι) (x : α) := ∏ j, (1 - T x (τ j) j)
    Tendsto (fun x => (P r x - P σ x) / (ε x * P r x)) l
      (𝓝 ((∑ j, L (σ j) j) - ∑ j, L (r j) j)) := by
  intro P
  have hdef (τ : Equiv.Perm ι) :
      Tendsto (fun x => (1 - P τ x) / ε x) l (𝓝 (∑ j, L (τ j) j)) :=
    tendsto_product_deficit_div l ε (fun j x => T x (τ j) j) (fun j => L (τ j) j)
      hε hnz (fun j => hT (τ j) j) Finset.univ
  have hP : Tendsto (P r) l (𝓝 1) := by
    have hconst : Tendsto (fun _ : α => (1 : ℂ)) l (𝓝 1) := tendsto_const_nhds
    have h := hconst.sub (hε.mul (hdef r))
    rw [zero_mul, sub_zero] at h
    refine h.congr' ?_
    filter_upwards [hnz] with x hx
    change 1 - ε x * ((1 - P r x) / ε x) = P r x
    rw [mul_div_cancel₀ _ hx, sub_sub_cancel]
  have h := ((hdef σ).sub (hdef r)).div hP one_ne_zero
  rw [div_one] at h
  refine h.congr' (Filter.Eventually.of_forall fun x => ?_)
  change ((1 - P σ x) / ε x - (1 - P r x) / ε x) / P r x =
    (P r x - P σ x) / (ε x * P r x)
  rw [← sub_div, div_div]
  rw [show (1 - P σ x) - (1 - P r x) = P r x - P σ x by ring]

/-- A limiting assignment gap that is nonnegative at every permutation
has nonnegative signed evaluation at every unitary. -/
theorem nonneg_signed_assignment_gap (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (L : ι → ι → ℝ) (r : Equiv.Perm ι)
    (hg : ∀ σ : Equiv.Perm ι, (∑ j, L (r j) j) ≤ ∑ j, L (σ j) j) :
    0 ≤ (∑ σ, signedWeight U σ *
      ((∑ j, (L (σ j) j : ℂ)) - ∑ j, (L (r j) j : ℂ))).re := by
  let f (j i : ι) : ℂ := L i j
  let c := ∑ j, f j (r j)
  have hEval (w : Equiv.Perm ι → ℂ) (hw : ∑ σ, w σ = 1) :
      (∑ σ, w σ * ((∑ j, f j (σ j)) - c)) =
        (∑ j, ∑ i, marginal w i j * f j i) - c := by
    simp_rw [mul_sub, Finset.mul_sum]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hw, one_mul, Finset.sum_comm]
    simp_rw [sum_weighted_evaluation]
  obtain ⟨w, hw, hw₁, hm⟩ := exists_singleton_weights U hU
  let v (σ : Equiv.Perm ι) : ℂ := w σ
  have hv : ∑ σ, v σ = 1 := by
    simpa only [v, Complex.ofReal_sum, Complex.ofReal_one] using
      congrArg (fun t : ℝ => (t : ℂ)) hw₁
  have he : (∑ σ, signedWeight U σ * ((∑ j, f j (σ j)) - c)) =
      ∑ σ, v σ * ((∑ j, f j (σ j)) - c) := by
    rw [hEval (signedWeight U) (sum_signedWeight U (det_ne_zero_of_unitary hU)), hEval v hv]
    simp only [marginal_signedWeight U hU, show ∀ i j,
      marginal v i j = (Complex.normSq (U i j) : ℂ) from hm]
  change 0 ≤ (∑ σ, signedWeight U σ * ((∑ j, f j (σ j)) - c)).re
  rw [he, Complex.re_sum]
  refine Finset.sum_nonneg fun σ _ => ?_
  simpa only [v, f, c, Complex.re_ofReal_mul, Complex.sub_re, Complex.re_sum,
    Complex.ofReal_re] using mul_nonneg (hw σ) (sub_nonneg.mpr (hg σ))

/-- A signed deficit normalized to one cannot have a nonnegative
singleton assignment gap as its limit. -/
theorem no_positive_deficit_of_assignment_gap_limits {α : Type*} (l : Filter α) [NeBot l]
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) (L : ι → ι → ℝ)
    (r : Equiv.Perm ι) (G : Equiv.Perm ι → α → ℂ)
    (hg : ∀ σ : Equiv.Perm ι, (∑ j, L (r j) j) ≤ ∑ j, L (σ j) j)
    (hlim : ∀ σ : Equiv.Perm ι, Tendsto (G σ) l
      (𝓝 ((∑ j, (L (σ j) j : ℂ)) - ∑ j, (L (r j) j : ℂ))))
    (hn : ∀ᶠ t in l, (∑ σ, signedWeight U σ * G σ t) = -1) : False := by
  have hsum := tendsto_finset_sum Finset.univ (fun σ _ => (hlim σ).const_mul (signedWeight U σ))
  have hconst : Tendsto (fun t => ∑ σ, signedWeight U σ * G σ t) l (𝓝 (-1 : ℂ)) :=
    tendsto_const_nhds.congr' (hn.mono fun _ hx => hx.symm)
  have hbad := nonneg_signed_assignment_gap U hU L r hg
  rw [tendsto_nhds_unique hsum hconst, Complex.neg_re, Complex.one_re] at hbad
  exact (not_le_of_gt (neg_lt_zero.mpr zero_lt_one)) hbad

/-- The divergent common-product limit is impossible when each anchored
kernel entry is recovered from a quotient of two matching products. -/
theorem no_positive_deficit_of_divergent_profile_limit {α : Type*} (l : Filter α) [NeBot l]
    (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (r : Equiv.Perm ι) (ε : α → ℂ) (T : α → ι → ι → ℂ)
    (G : Equiv.Perm ι → α → ℂ) (c : Equiv.Perm ι → ℝ)
    (hε : Tendsto ε l (𝓝 0)) (hnz : ∀ᶠ x in l, ε x ≠ 0)
    (hc : ∀ σ, 0 ≤ c σ) (hlim : ∀ σ, Tendsto (G σ) l (𝓝 (c σ : ℂ)))
    (hratio : ∀ i j, ∃ π τ : Equiv.Perm ι, ∀ᶠ x in l,
      1 - T x i j = (1 - ε x * G π x) / (1 - ε x * G τ x))
    (hG : ∀ σ, ∀ᶠ x in l, G σ x =
      ((∏ j, (1 - T x (r j) j)) - ∏ j, (1 - T x (σ j) j)) /
        (ε x * ∏ j, (1 - T x (r j) j)))
    (hn : ∀ᶠ t in l, (∑ σ, signedWeight U σ * G σ t) = -1) : False := by
  classical
  choose π τ hπ using hratio
  let L (i j : ι) : ℝ := c (π i j) - c (τ i j)
  have hentry (i j : ι) : Tendsto (fun x => T x i j / ε x) l (𝓝 (L i j : ℂ)) := by
    simpa only [L, Complex.ofReal_sub] using
      tendsto_entry_div_of_profile_ratio l ε (fun x => T x i j) (G (π i j)) (G (τ i j))
        (c (π i j)) (c (τ i j)) hε hnz (hlim _) (hlim _) (hπ i j)
  have hnormalized (σ : Equiv.Perm ι) : Tendsto (G σ) l
      (𝓝 ((∑ j, (L (σ j) j : ℂ)) - ∑ j, (L (r j) j : ℂ))) :=
    (tendsto_constant_profile_gap l ε T (fun i j => (L i j : ℂ)) hε hnz hentry r σ).congr'
      ((hG σ).mono fun _ hx => hx.symm)
  refine no_positive_deficit_of_assignment_gap_limits l U hU L r G ?_ hnormalized hn
  intro σ
  apply sub_nonneg.mp
  have he := congrArg Complex.re (tendsto_nhds_unique (hlim σ) (hnormalized σ))
  simp only [Complex.sub_re, Complex.re_sum, Complex.ofReal_re] at he
  rw [← he]
  exact hc σ

end MOC
