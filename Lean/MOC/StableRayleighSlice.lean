import MOC.SpectralTranslationRigidity

/-! A bivariate slice that stays nonzero in the open upper half-planes
has a nonnegative Rayleigh difference at a real boundary value. -/

open BigOperators Filter Set Finset
open scoped Topology

namespace MOC

private theorem negative_bilinear_root_im (A B C D : ℝ) :
    ((-((A : ℂ) + (B : ℂ) * Complex.I)) /
      ((C : ℂ) + (D : ℂ) * Complex.I)).im =
      (A * D - B * C) / (C^2 + D^2) := by
  have hr : ((C : ℂ) + (D : ℂ) * Complex.I).re = C := by
    simp [Complex.add_re, Complex.mul_re]
  have hi : ((C : ℂ) + (D : ℂ) * Complex.I).im = D := by
    simp [Complex.add_im, Complex.mul_im]
  have ha : (-((A : ℂ) + (B : ℂ) * Complex.I)).re = -A := by
    simp [Complex.add_re, Complex.mul_re]
  have hb : (-((A : ℂ) + (B : ℂ) * Complex.I)).im = -B := by
    simp [Complex.add_im, Complex.mul_im]
  have hnorm : Complex.normSq ((C : ℂ) + (D : ℂ) * Complex.I) = C ^ 2 + D ^ 2 := by
    rw [Complex.normSq_apply, hr, hi]
    ring
  rw [Complex.div_im, hnorm, hr, hi, ha, hb]
  ring

/-- A continuous family of bivariate multi-affine polynomials cannot
approach real boundary coefficients with negative Rayleigh difference.
The proof uses the explicit root in the second variable. -/
theorem rayleigh_nonneg_of_stable_bilinear_boundary
    (A B C D : ℝ → ℂ) (a b c d : ℝ)
    (hA : ContinuousAt A 0) (hB : ContinuousAt B 0)
    (hC : ContinuousAt C 0) (hD : ContinuousAt D 0)
    (ha : A 0 = a) (hb : B 0 = b) (hc : C 0 = c) (hd : D 0 = d)
    (hstable : ∀ ε : ℝ, 0 < ε → ∀ z w : ℂ, 0 < z.im → 0 < w.im →
      A ε + B ε * z + C ε * w + D ε * z * w ≠ 0) :
    0 ≤ b * c - a * d := by
  by_contra! hneg
  have hpos : 0 < a * d - b * c := by linarith only [hneg]
  have hcd : 0 < c^2 + d^2 := by
    by_cases h : c = 0
    · have hn : d ≠ 0 := by
        intro he
        simp only [h, he, mul_zero, sub_self, lt_self_iff_false] at hpos
      rw [h, zero_pow two_ne_zero, zero_add]
      exact sq_pos_of_ne_zero hn
    · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero h) (sq_nonneg _)
  let den (ε : ℝ) := C ε + D ε * Complex.I
  let w (ε : ℝ) := -(A ε + B ε * Complex.I) / den ε
  have hden : den 0 ≠ 0 := by
    intro he
    have hr := congrArg Complex.re he
    have hi := congrArg Complex.im he
    simp [den, hc, hd, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im] at hr hi
    rw [hr, hi] at hcd
    norm_num at hcd
  have hwpos : 0 < (w 0).im := by
    dsimp only [w, den]
    rw [ha, hb, hc, hd, negative_bilinear_root_im]
    exact div_pos hpos hcd
  have hcontDen : ContinuousAt den 0 := hC.add (hD.mul continuousAt_const)
  have hcontW : ContinuousAt w 0 := (hA.add (hB.mul continuousAt_const)).neg.div hcontDen hden
  have hi : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < (w ε).im :=
    (Complex.continuous_im.continuousAt.comp hcontW).eventually (Ioi_mem_nhds hwpos)
  have hdne : ∀ᶠ ε in 𝓝 (0 : ℝ), den ε ≠ 0 :=
    hcontDen.eventually (isOpen_ne.mem_nhds hden)
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Ioi (0 : ℝ) ∧ 0 < (w ε).im ∧ den ε ≠ 0 :=
    self_mem_nhdsWithin.and ((hi.and hdne).filter_mono nhdsWithin_le_nhds)
  obtain ⟨ε, hε, hw, hne⟩ := hev.exists
  have hz : den ε * w ε = -(A ε + B ε * Complex.I) := by
    dsimp only [w]
    rw [mul_comm (den ε), div_mul_cancel₀ _ hne]
  apply hstable ε hε Complex.I (w ε) (by rw [Complex.I_im]; exact zero_lt_one) hw
  dsimp only [den] at hz
  linear_combination hz

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The coefficient of the right-subset monomial, after the left
variables are evaluated at `a`. -/
def spectralRightCoefficient (c : SquarefreeClass ι) (a : ι → ℂ) (J : Finset ι) : ℂ :=
  ∑ I : Finset ι, if Iᶜ.card = J.card then c I J * ∏ i ∈ I, a i else 0

private theorem spectralValue_eq_rightCoefficient_sum (c : SquarefreeClass ι) (a b : ι → ℂ) :
    squarefreeSpectralValue c a b =
      ∑ J : Finset ι, spectralRightCoefficient c a J * ∏ j ∈ J, b j := by
  rw [squarefreeSpectralValue, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro J _
  rw [spectralRightCoefficient, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro I _
  by_cases h : Iᶜ.card = J.card <;>
    simp only [squarefreeDividedDivisor, h, if_true, if_false, mul_zero, zero_mul, mul_assoc]

private def pairSpectralInput (j l : ι) (z w : ℂ) (i : ι) : ℂ :=
  if i = j then z else if i = l then w else 0

private theorem powerset_two_right (j l : ι) :
    ({j, l} : Finset ι).powerset = {∅, {j}, {l}, {j, l}} := by
  have hs : ({l} : Finset ι).powerset = {∅, {l}} := by
    rw [← Finset.insert_empty_eq, Finset.powerset_insert, Finset.powerset_empty]
    ext T
    simp [or_comm]
  change (insert j ({l} : Finset ι)).powerset = _
  rw [Finset.powerset_insert, hs]
  ext T
  simp [or_assoc, or_left_comm, or_comm]

private theorem spectral_pair_slice (c : SquarefreeClass ι) (a : ι → ℂ)
    (j l : ι) (hjl : j ≠ l) (z w : ℂ) :
    squarefreeSpectralValue c a (pairSpectralInput j l z w) =
      spectralRightCoefficient c a ∅ + spectralRightCoefficient c a {j} * z +
      spectralRightCoefficient c a {l} * w + spectralRightCoefficient c a {j, l} * z * w := by
  classical
  rw [spectralValue_eq_rightCoefficient_sum]
  let f (J : Finset ι) := spectralRightCoefficient c a J * ∏ i ∈ J, pairSpectralInput j l z w i
  have hs : (∑ J ∈ ({j, l} : Finset ι).powerset, f J) = ∑ J, f J := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro J _ hJ
    obtain ⟨i, hiJ, hi⟩ := Finset.not_subset.mp (fun hm => hJ (Finset.mem_powerset.mpr hm))
    have h₁ : i ≠ j := fun h => hi (by simp [h])
    have h₂ : i ≠ l := fun h => hi (by simp [h])
    have hz : pairSpectralInput j l z w i = 0 := by
      simp only [pairSpectralInput, h₁, h₂, if_false]
    rw [f, Finset.prod_eq_zero hiJ hz, mul_zero]
  have h₀ : (∅ : Finset ι) ∉ ({({j} : Finset ι), {l}, {j, l}} : Finset (Finset ι)) := by
    simp
  have hj : ({j} : Finset ι) ∉ ({({l} : Finset ι), {j, l}} : Finset (Finset ι)) := by
    have hn : ({j} : Finset ι) ≠ {j, l} := fun h => hjl (by
      have hm : l ∈ ({j} : Finset ι) := h.symm ▸ (by simp)
      exact (Finset.mem_singleton.mp hm).symm)
    simp [hjl, hn]
  have hl : ({l} : Finset ι) ≠ {j, l} := fun h => hjl (by
    have hm : j ∈ ({l} : Finset ι) := h.symm ▸ (by simp)
    exact Finset.mem_singleton.mp hm)
  change (∑ J, f J) = _
  rw [← hs, powerset_two_right, Finset.sum_insert h₀, Finset.sum_insert hj, Finset.sum_pair hl]
  simp only [f, Finset.prod_empty, Finset.prod_singleton, Finset.prod_pair hjl, mul_one,
    pairSpectralInput, if_pos rfl, if_neg hjl.symm]
  ring

private theorem continuous_spectralRightCoefficient (c : SquarefreeClass ι)
    (a : ι → ℝ) (J : Finset ι) :
    Continuous fun ε : ℝ => spectralRightCoefficient c (fun i => (a i : ℂ) + 2 * ε * Complex.I) J := by
  unfold spectralRightCoefficient
  apply continuous_finset_sum _ fun I _ => ?_
  by_cases h : Iᶜ.card = J.card
  · simp only [h, if_true]
    apply continuous_const.mul
    apply continuous_finset_prod _ fun i _ => ?_
    exact continuous_const.add
      ((continuous_const.mul Complex.continuous_ofReal).mul continuous_const)
  · simp only [h, if_false]
    exact continuous_const

/-- With two chosen right labels, the boundary Rayleigh inequality
holds for the four coefficients of the corresponding bilinear slice. -/
theorem IsMinimumNormalizedSpectralValue.right_rayleigh {c : SquarefreeClass ι}
    (hc : IsMinimumNormalizedSpectralValue c) (a : ι → ℝ) (j l : ι) (hjl : j ≠ l) :
    let A (J : Finset ι) := (spectralRightCoefficient c (fun i => (a i : ℂ)) J).re
    0 ≤ A {j} * A {l} - A ∅ * A {j, l} := by
  let F (J : Finset ι) (ε : ℝ) :=
    spectralRightCoefficient c (fun i => (a i : ℂ) + 2 * ε * Complex.I) J
  have hcont (J : Finset ι) : ContinuousAt (F J) 0 := (continuous_spectralRightCoefficient c a J).continuousAt
  have hzero (J : Finset ι) : F J 0 = ((spectralRightCoefficient c (fun i => (a i : ℂ)) J).re : ℂ) := by
    simp only [F, Complex.ofReal_zero, mul_zero, zero_mul, add_zero, spectralRightCoefficient,
      Complex.re_sum, Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro I _
    by_cases hIJ : Iᶜ.card = J.card
    · simp only [hIJ, if_true]
      have hI : ((c I J).re : ℂ) = c I J := by
        apply Complex.ext
        · exact Complex.ofReal_re _
        · rw [Complex.ofReal_im, (hc.nonnegative I J hIJ).1]
      have hval : c I J * (∏ i ∈ I, (a i : ℂ)) =
          (((c I J).re * ∏ i ∈ I, a i : ℝ) : ℂ) := by
        rw [Complex.ofReal_mul, Complex.ofReal_prod, hI]
      rw [hval, Complex.ofReal_re]
    · simp only [hIJ, if_false, Complex.zero_re, Complex.ofReal_zero]
  have H := rayleigh_nonneg_of_stable_bilinear_boundary (F ∅) (F {j}) (F {l}) (F {j, l})
    _ _ _ _ (hcont _) (hcont _) (hcont _) (hcont _) (hzero _) (hzero _) (hzero _) (hzero _)
  apply H
  intro ε hε z w hz hw
  let a₀ (i : ι) : ℂ := (a i : ℂ) - 1 + (ε : ℂ) * Complex.I
  let b₀ (i : ι) : ℂ := 1 + (ε : ℂ) * Complex.I + pairSpectralInput j l z w i
  have ha (i : ι) : 0 < (a₀ i).im := by
    simpa [a₀, Complex.add_im, Complex.sub_im, Complex.mul_im] using hε
  have hb (i : ι) : 0 < (b₀ i).im := by
    have hp : 0 ≤ (pairSpectralInput j l z w i).im := by
      unfold pairSpectralInput
      split
      · exact hz.le
      · split
        · exact hw.le
        · exact le_rfl
    simpa [b₀, Complex.add_im, Complex.mul_im] using add_pos_of_pos_of_nonneg hε hp
  have ht := hc.opposite_translation a₀ b₀ (1 + (ε : ℂ) * Complex.I)
  have haa : (fun i => a₀ i + (1 + (ε : ℂ) * Complex.I)) =
      fun i => (a i : ℂ) + 2 * ε * Complex.I := by
    funext i
    unfold a₀
    ring
  have hbb : (fun i => b₀ i - (1 + (ε : ℂ) * Complex.I)) = pairSpectralInput j l z w := by
    funext i
    dsimp only [b₀]
    ring
  rw [haa, hbb, spectral_pair_slice c _ j l hjl] at ht
  rw [show F ∅ ε + F {j} ε * z + F {l} ε * w + F {j, l} ε * z * w =
    squarefreeSpectralValue c a₀ b₀ from ht]
  exact hc.stable a₀ b₀ ha hb

/-- The homogeneous right moment uses the left labels removed in the
balanced monomial. Its degree equals the size of the right subset. -/
def spectralRightMoment (c : SquarefreeClass ι) (J : Finset ι) (x : ι → ℝ) : ℝ :=
  ∑ I : Finset ι, if Iᶜ.card = J.card then (c I J).re * ∏ i ∈ Iᶜ, x i else 0

private theorem spectralRightMoment_empty {c : SquarefreeClass ι}
    (hc : IsMinimumNormalizedSpectralValue c) (x : ι → ℝ) :
    spectralRightMoment c ∅ x = 1 := by
  rw [spectralRightMoment, Finset.sum_eq_single_of_mem univ (Finset.mem_univ _)]
  · simp only [compl_univ, if_true, Finset.prod_empty, mul_one, hc.leftEndpoint, Complex.one_re]
  · intro I _ hI
    apply if_neg
    intro h
    have hempty : Iᶜ = ∅ := Finset.card_eq_zero.mp (by simpa only [Finset.card_empty] using h)
    exact hI (by rw [← compl_compl I, hempty, compl_empty])

private theorem spectralRightCoefficient_inverse (c : SquarefreeClass ι) (J : Finset ι)
    (x : ι → ℝ) (hx : ∀ i, x i ≠ 0) :
    (spectralRightCoefficient c (fun i => ((x i)⁻¹ : ℝ)) J).re =
      (∏ i, (x i)⁻¹) * spectralRightMoment c J x := by
  rw [spectralRightCoefficient, spectralRightMoment, Complex.re_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I _
  by_cases h : Iᶜ.card = J.card
  · simp only [h, if_true, ← Complex.ofReal_prod, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
    have hp : (∏ i ∈ I, (x i)⁻¹) =
        (∏ i, (x i)⁻¹) * ∏ i ∈ Iᶜ, x i := by
      rw [← Finset.prod_mul_prod_compl I (fun i => (x i)⁻¹), mul_assoc, ← Finset.prod_mul_distrib]
      simp only [inv_mul_cancel₀ (hx _), Finset.prod_const_one, mul_one]
    rw [hp]
    ring
  · simp only [h, if_false, Complex.zero_re, mul_zero]

private theorem continuous_spectralRightMoment (c : SquarefreeClass ι) (J : Finset ι) :
    Continuous (spectralRightMoment c J) := by
  unfold spectralRightMoment
  apply continuous_finset_sum _ fun I _ => ?_
  by_cases h : Iᶜ.card = J.card
  · simp only [h, if_true]
    exact continuous_const.mul (continuous_finset_prod _ fun i _ => continuous_apply i)
  · simp only [h, if_false]
    exact continuous_const

/-- The column-pair Rayleigh quadratic form is nonnegative on every
real vector, including vectors with zero coordinates. -/
theorem IsMinimumNormalizedSpectralValue.right_moment_rayleigh {c : SquarefreeClass ι}
    (hc : IsMinimumNormalizedSpectralValue c) (j l : ι) (hjl : j ≠ l) (x : ι → ℝ) :
    0 ≤ spectralRightMoment c {j} x * spectralRightMoment c {l} x -
      spectralRightMoment c {j, l} x := by
  let good : Set (ι → ℝ) := {x | 0 ≤ spectralRightMoment c {j} x *
    spectralRightMoment c {l} x - spectralRightMoment c {j, l} x}
  have hcgood : IsClosed good := isClosed_le continuous_const
    (((continuous_spectralRightMoment c {j}).mul (continuous_spectralRightMoment c {l})).sub
      (continuous_spectralRightMoment c {j, l}))
  let nz : Set (ι → ℝ) := Set.pi Set.univ fun _ => ({0} : Set ℝ)ᶜ
  have hd : Dense nz := dense_pi Set.univ fun _ _ => dense_compl_singleton (0 : ℝ)
  have hin : nz ⊆ good := by
    intro y hy
    have hy' (i : ι) : y i ≠ 0 := by
      have hi := Set.mem_pi.mp hy i (Set.mem_univ i)
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hi
    let p : ℝ := ∏ i, (y i)⁻¹
    have hp : p ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => inv_ne_zero (hy' i))
    have H := hc.right_rayleigh (fun i => (y i)⁻¹) j l hjl
    simp only [spectralRightCoefficient_inverse c _ y hy', spectralRightMoment_empty hc y,
      mul_one] at H
    change 0 ≤ spectralRightMoment c {j} y * spectralRightMoment c {l} y -
      spectralRightMoment c {j, l} y
    apply (mul_nonneg_iff_of_pos_left (sq_pos_of_ne_zero hp)).mp
    convert H using 1 <;> ring
  exact (closure_minimal hin hcgood) (hd x)

end

end MOC
