import MOC.FourCoincidence
import MOC.CollinearKernelSupport
import MOC.SpectralHessian
import MOC.SpectralPerturbation
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! A common active edge allows a spectral deformation to another contact. -/

open BigOperators Filter Matrix Polynomial
open scoped ComplexConjugate Topology

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private def partialInverse (a : ι → ℂ) (i : ι) (k : ι) : ℂ :=
  if k = i then 0 else (a k)⁻¹

private def denominatorCoordinate (a : ι → ℂ) (i : ι) (k : ι) : ℂ :=
  if k = i then 1 else a k

private theorem mixedCoefficient_eq_inverse_matching (a b : ι → ℂ) (i j : ι)
    (ha : ∀ k, k ≠ i → a k ≠ 0) (hb : ∀ k, k ≠ j → b k ≠ 0) (σ : Equiv.Perm ι) :
    let d := (∏ k, denominatorCoordinate a i k) * ∏ k, denominatorCoordinate b j k
    matchingMixedCoefficient a b i j σ =
      d * matchingProduct (partialInverse a i) (partialInverse b j) σ := by
  dsimp only
  let g (k : ι) : ℂ :=
    if k = j then if σ k = i then 0 else 1
    else if σ k = i then 1 else a (σ k) + b k
  have hfactor (k : ι) :
      denominatorCoordinate a i (σ k) * denominatorCoordinate b j k *
        (partialInverse a i (σ k) + partialInverse b j k) = g k := by
    by_cases hj : k = j <;> by_cases hi : σ k = i
    · subst k
      simp [denominatorCoordinate, partialInverse, g, hi]
    · subst k
      simp [denominatorCoordinate, partialInverse, g, hi, ha (σ j) hi]
    · simp [denominatorCoordinate, partialInverse, g, hj, hi, hb k hj]
    · simp only [denominatorCoordinate, partialInverse, g, if_neg hj, if_neg hi]
      field_simp [ha (σ k) hi, hb k hj] <;> ring
  have hprod : (∏ k, g k) =
      ((∏ k, denominatorCoordinate a i k) * ∏ k, denominatorCoordinate b j k) *
        matchingProduct (partialInverse a i) (partialInverse b j) σ := by
    simp_rw [← hfactor]
    simp only [Finset.prod_mul_distrib, Equiv.prod_comp σ (denominatorCoordinate a i),
      matchingProduct]
  rw [← hprod]
  by_cases h : σ j = i
  · simp only [matchingMixedCoefficient, if_pos h]
    exact (Finset.prod_eq_zero (Finset.mem_univ j) (by simp [g, h])).symm
  · let k := σ.symm i
    have hk : k ≠ j := fun e => h (e ▸ σ.apply_symm_apply i)
    have hσk : σ k = i := σ.apply_symm_apply i
    have hjval : g j = 1 := by simp [g, h]
    have hkval : g k = 1 := by simp [g, hk, hσk]
    rw [← Finset.prod_erase Finset.univ hjval,
      ← Finset.prod_erase (Finset.univ.erase j) hkval]
    simp only [matchingMixedCoefficient, if_neg h]
    apply Finset.prod_congr rfl
    intro l hl
    obtain ⟨hlk, hlj⟩ := Finset.mem_erase.mp hl
    have hil : σ l ≠ i := fun e => hlk (σ.injective (e.trans hσk.symm))
    simp only [g, if_neg hil, if_neg (Finset.mem_erase.mp hlj).1]

private theorem matchingMixedCoefficient_shift (a b : ι → ℂ) (i j : ι)
    (z : ℂ) (σ : Equiv.Perm ι) :
    matchingMixedCoefficient (fun k => a k + z) (fun k => b k - z) i j σ =
      matchingMixedCoefficient a b i j σ := by
  unfold matchingMixedCoefficient
  split_ifs
  · rfl
  · apply Finset.prod_congr rfl
    intro k _
    ring

private theorem mixedCoefficient_mem_matchingHull_of_reciprocal
    (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U) (i j : ι)
    (hrec : ∀ (u v : ι → ℂ) (e : ℂ), e ≠ 0 → u i + v j = 0 →
      (∀ σ, matchingMixedCoefficient a b i j σ = e * matchingProduct u v σ) → Holds u v U) :
    determinantMixedCoefficient a b U i j ∈
      convexHull ℝ (Set.range (matchingMixedCoefficient a b i j)) := by
  let bad : Set ℂ := Set.range (fun k => -a k) ∪ Set.range b
  have hbad : bad.Finite := (Set.finite_range _).union (Set.finite_range _)
  obtain ⟨z, hz⟩ := hbad.exists_not_mem
  let c (k : ι) := a k + z
  let d (k : ι) := b k - z
  have hc (k : ι) : c k ≠ 0 := by
    intro h
    exact hz (Or.inl ⟨k, by dsimp only [c] at h; linear_combination -h⟩)
  have hd (k : ι) : d k ≠ 0 := by
    intro h
    exact hz (Or.inr ⟨k, by dsimp only [d] at h; linear_combination h⟩)
  let u := partialInverse c i
  let v := partialInverse d j
  let e := (∏ k, denominatorCoordinate c i k) * ∏ k, denominatorCoordinate d j k
  have hσ (σ : Equiv.Perm ι) :
      matchingMixedCoefficient a b i j σ = e * matchingProduct u v σ := by
    rw [← matchingMixedCoefficient_shift a b i j z σ]
    exact mixedCoefficient_eq_inverse_matching c d i j (fun k _ => hc k) (fun k _ => hd k) σ
  have he : determinantMixedCoefficient a b U i j = e * determinantValue u v U := by
    rw [determinantMixedCoefficient, ← signed_determinant u v U hU, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    rw [hσ]
    ring
  have huv : u i + v j = 0 := by simp [u, v, partialInverse]
  have hene : e ≠ 0 := by
    apply mul_ne_zero <;> apply Finset.prod_ne_zero_iff.mpr <;> intro k _
    · by_cases hk : k = i <;> simp [denominatorCoordinate, hk, hc k]
    · by_cases hk : k = j <;> simp [denominatorCoordinate, hk, hd k]
  exact hull_of_common_factor he hσ (hrec u v e hene huv hσ)

/-- Partial inversion sends the selected coordinates to the opposite pair
covered by the order-four coincidence theorem. -/
theorem four_mixedCoefficient_mem_matchingHull
    (a b : Fin 4 → ℂ) (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) (i j : Fin 4) :
    determinantMixedCoefficient a b U i j ∈
      convexHull ℝ (Set.range (matchingMixedCoefficient a b i j)) :=
  mixedCoefficient_mem_matchingHull_of_reciprocal a b U hU i j
    (fun u v _ _ hzero _ => holds_four_of_opposite_entries u v U hU hzero)

/-- In every order a collinear mixed matching profile contains the determinant's
mixed coefficient in its convex hull. The mixed profile always contains zero. -/
theorem mixedCoefficient_mem_matchingHull_of_collinear
    (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U) (i j : ι)
    (q : ℂ) (hq : q ≠ 0)
    (hline : ∀ σ, (q * matchingMixedCoefficient a b i j σ).re = 0) :
    determinantMixedCoefficient a b U i j ∈
      convexHull ℝ (Set.range (matchingMixedCoefficient a b i j)) := by
  letI : Nonempty ι := ⟨i⟩
  apply mixedCoefficient_mem_matchingHull_of_reciprocal a b U hU i j
  intro u v e he _ hσ
  exact holds_of_matching_line_through_origin u v (q * e) (mul_ne_zero hq he)
    (fun σ => by rw [mul_assoc, ← hσ]; exact hline σ) U hU

private theorem exists_positive_quadratic_phase (η v : ℂ) (hn : η * v ≠ 0) :
    ∃ p : ℂ, 0 < -(η * p ^ 2 * v).re := by
  obtain ⟨p, hp⟩ := IsAlgClosed.exists_pow_nat_eq (-conj (η * v)) (n := 2) zero_lt_two
  refine ⟨p, ?_⟩
  rw [hp, show η * -conj (η * v) * v = -((η * v) * conj (η * v)) by ring,
    Complex.mul_conj, Complex.neg_re, Complex.ofReal_re, neg_neg]
  exact Complex.normSq_pos.mpr hn

/-- Whenever some mixed matching coefficient is nonzero, a complex direction
increases its quadratic term and also the determinant's, unless the latter
vanishes identically. A failure would force a collinear mixed profile. -/
theorem exists_positive_mixed_quadratic_phase
    (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U) (i j : ι)
    (η : ℂ) (hη : η ≠ 0) (hM : ∃ σ, matchingMixedCoefficient a b i j σ ≠ 0) :
    let D := determinantMixedCoefficient a b U i j
    ∃ (p : ℂ) (σ : Equiv.Perm ι),
      (D = 0 ∨ 0 < -(η * p ^ 2 * D).re) ∧
      0 < -(η * p ^ 2 * matchingMixedCoefficient a b i j σ).re := by
  let D := determinantMixedCoefficient a b U i j
  let M := matchingMixedCoefficient a b i j
  by_cases hD : D = 0
  · obtain ⟨σ, hσ⟩ := hM
    obtain ⟨p, hp⟩ := exists_positive_quadratic_phase η (M σ) (mul_ne_zero hη hσ)
    exact ⟨p, σ, Or.inl hD, hp⟩
  have hpos : ∃ (q : ℂ) (σ : Equiv.Perm ι), 0 < (q * D).re ∧ 0 < (q * M σ).re := by
    by_contra hnone
    let q₀ := conj D
    have hq₀ : q₀ ≠ 0 := by
      dsimp only [q₀]
      exact star_ne_zero.mpr hD
    have hd₀ : 0 < (q₀ * D).re := by
      change 0 < (conj D * D).re
      rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
      exact Complex.normSq_pos.mpr hD
    have hdi : (q₀ * D).im = 0 := by
      change (conj D * D).im = 0
      rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_im]
    let q (t : ℝ) := (1 + (t : ℂ) * Complex.I) * q₀
    have hproj (t : ℝ) (z : ℂ) : (q t * z).re = (q₀ * z).re - t * (q₀ * z).im := by
      dsimp only [q]
      rw [mul_assoc]
      simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
        Complex.one_re, Complex.one_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
      ring
    have hline (σ : Equiv.Perm ι) : (q₀ * M σ).im = 0 := by
      by_contra hne
      let t := ((q₀ * M σ).re - 1) / (q₀ * M σ).im
      have ht : t * (q₀ * M σ).im = (q₀ * M σ).re - 1 := div_mul_cancel₀ _ hne
      apply hnone
      refine ⟨q t, σ, ?_, ?_⟩
      · rwa [hproj, hdi, mul_zero, sub_zero]
      · rw [hproj, ht]
        ring_nf <;> norm_num
    let q₁ := -Complex.I * q₀
    have hq₁ : q₁ ≠ 0 := mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hq₀
    have hreal (σ : Equiv.Perm ι) : (q₁ * M σ).re = 0 := by
      change ((-Complex.I * q₀) * M σ).re = 0
      rw [mul_assoc, neg_mul, Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        hline, zero_mul, mul_zero, sub_zero, neg_zero]
    let f : ℂ →ₗ[ℝ] ℝ := Complex.reLm.comp (LinearMap.mulLeft ℝ q₀)
    have hs : Set.range M ⊆ {z : ℂ | f z ≤ 0} := by
      rintro _ ⟨σ, rfl⟩
      exact le_of_not_gt fun h => hnone ⟨q₀, σ, hd₀, h⟩
    have hle : f D ≤ 0 := convexHull_min hs (convex_halfSpace_le f.isLinear 0)
      (mixedCoefficient_mem_matchingHull_of_collinear a b U hU i j q₁ hq₁ hreal)
    exact (not_le_of_gt hd₀) hle
  obtain ⟨q, σ, hqD, hqσ⟩ := hpos
  obtain ⟨p, hp⟩ := IsAlgClosed.exists_pow_nat_eq (-q / η) (n := 2) zero_lt_two
  have he : -(η * p ^ 2) = q := by
    rw [hp]
    field_simp [hη] <;> ring
  have hrotate (z : ℂ) : -(η * p ^ 2 * z).re = (q * z).re := by
    rw [← Complex.neg_re, ← neg_mul, he]
  exact ⟨p, σ, Or.inr (by simpa only [hrotate] using hqD),
    by simpa only [hrotate] using hqσ⟩

private theorem exists_ray_avoiding_finite (W B : Set ℂ) (hW : IsOpen W) (hB : B.Finite)
    (p₀ : ℂ) (hp : p₀ ∈ W) (hp₀ : p₀ ≠ 0) :
    ∃ p ∈ W, ∀ t : ℝ, t ≠ 0 → (t : ℂ) * p ∉ B := by
  let v (r : ℝ) := p₀ * (1 + (r : ℂ) * Complex.I)
  let q (z : ℂ) := (z / p₀).im / (z / p₀).re
  let B' := q '' B
  have hB' : B'.Finite := hB.image q
  have hv : Continuous v :=
    continuous_const.mul (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))
  have hv₀ : v 0 = p₀ := by simp [v]
  have hpv : v 0 ∈ W := by simpa only [hv₀] using hp
  have hnear : ∀ᶠ r in 𝓝[≠] (0 : ℝ), v r ∈ W :=
    (hv.continuousAt.eventually_mem (hW.mem_nhds hpv)).filter_mono nhdsWithin_le_nhds
  have hopen : IsOpen ((B' \ {0})ᶜ : Set ℝ) := hB'.diff.isClosed.isOpen_compl
  have havoid : ∀ᶠ r in 𝓝[≠] (0 : ℝ), r ∉ B' := by
    have hmem : (0 : ℝ) ∈ (B' \ {0})ᶜ := by simp
    have hnear' : ∀ᶠ r in 𝓝 (0 : ℝ), r ∈ (B' \ {0})ᶜ := hopen.mem_nhds hmem
    filter_upwards [hnear'.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with r hr hr₀
    exact fun he => (show r ∉ B' \ {0} from hr) ⟨he, hr₀⟩
  obtain ⟨r, hr, hbad⟩ := (hnear.and havoid).exists
  refine ⟨v r, hr, fun t ht hb => hbad ⟨_, hb, ?_⟩⟩
  have hdiv : ((t : ℂ) * v r) / p₀ = (t : ℂ) * (1 + (r : ℂ) * Complex.I) := by
    dsimp only [v]
    field_simp [hp₀] <;> ring
  dsimp only [q]
  rw [hdiv,
    show ((t : ℂ) * (1 + (r : ℂ) * Complex.I)).re = t by
      simp [Complex.mul_re],
    show ((t : ℂ) * (1 + (r : ℂ) * Complex.I)).im = r * t by
      simp [Complex.mul_im, Complex.mul_re, mul_comm],
    mul_div_cancel_right₀ _ ht]

private theorem exists_contact_ray [Nontrivial ι]
    (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U) (i j : ι)
    (η L : ℂ) (hη : η ≠ 0) (hreg : ∀ k l, a k + b l ≠ 0) (B : Set ℂ) (hB : B.Finite) :
    ∃ (p : ℂ) (σ : Equiv.Perm ι), σ j ≠ i ∧ 0 ≤ (η * p * L).re ∧
      0 ≤ -(η * p ^ 2 * determinantMixedCoefficient a b U i j).re ∧
      0 < -(η * p ^ 2 * matchingMixedCoefficient a b i j σ).re ∧
      ∀ t : ℝ, t ≠ 0 → (t : ℂ) * p ∉ B := by
  let D := determinantMixedCoefficient a b U i j
  let M := matchingMixedCoefficient a b i j
  obtain ⟨k, hk⟩ := exists_ne i
  let τ := Equiv.swap j k
  have hτ : τ j ≠ i := by simpa only [τ, Equiv.swap_apply_left] using hk
  have hM : M τ ≠ 0 := by
    simp only [M, matchingMixedCoefficient, if_neg hτ]
    exact Finset.prod_ne_zero_iff.mpr fun l _ => hreg (τ l) l
  obtain ⟨p₀, σ, hD₀, hσ₀⟩ := exists_positive_mixed_quadratic_phase a b U hU i j η hη ⟨τ, hM⟩
  have hne : σ j ≠ i := by
    intro he
    simp only [matchingMixedCoefficient, if_pos he, mul_zero, Complex.zero_re,
      neg_zero, lt_irrefl] at hσ₀
  let W : Set ℂ := {p | (D = 0 ∨ 0 < -(η * p ^ 2 * D).re) ∧ 0 < -(η * p ^ 2 * M σ).re}
  have hMopen : IsOpen {p : ℂ | 0 < -(η * p ^ 2 * M σ).re} :=
    isOpen_lt continuous_const (by fun_prop)
  have hW : IsOpen W := by
    by_cases h : D = 0
    · simpa only [W, h, eq_self, true_or, true_and] using hMopen
    · have hDopen : IsOpen {p : ℂ | 0 < -(η * p ^ 2 * D).re} :=
        isOpen_lt continuous_const (by fun_prop)
      simpa only [W, h, false_or, Set.setOf_and] using hDopen.inter hMopen
  have hp₀ : p₀ ≠ 0 := by
    intro h
    simp [h] at hσ₀
  obtain ⟨p, hWmem, hAvoid⟩ := exists_ray_avoiding_finite W B hW hB p₀ ⟨hD₀, hσ₀⟩ hp₀
  have hσ : 0 < -(η * p ^ 2 * M σ).re := hWmem.2
  have hD : 0 ≤ -(η * p ^ 2 * D).re := by
    rcases hWmem.1 with h | h
    · simp [h]
    · exact h.le
  by_cases hL : 0 ≤ (η * p * L).re
  · exact ⟨p, σ, hne, hL, hD, hσ, hAvoid⟩
  · refine ⟨-p, σ, hne, ?_, ?_, ?_, ?_⟩
    · simpa only [mul_neg, neg_mul, Complex.neg_re, neg_nonneg] using (lt_of_not_ge hL).le
    · simpa only [neg_sq] using hD
    · simpa only [neg_sq] using hσ
    · intro t ht
      simpa only [Complex.ofReal_neg, neg_mul, mul_neg] using hAvoid (-t) (neg_ne_zero.mpr ht)

private theorem projected_quadratic_ray (f : ℂ → ℂ) (m η p : ℂ)
    (hf : ∀ z, f z = f 0 + z * (f 1 - f 0 + m) - z ^ 2 * m) (t : ℝ) :
    (η * f ((t : ℂ) * p)).re = (η * f 0).re +
      t * (η * p * (f 1 - f 0 + m)).re + t ^ 2 * (-(η * p ^ 2 * m).re) := by
  let L := f 1 - f 0 + m
  have hlinear : η * (((t : ℂ) * p) * L) = (t : ℂ) * (η * p * L) := by ring
  have hquad : η * (((t : ℂ) * p) ^ 2 * m) =
      ((t ^ 2 : ℝ) : ℂ) * (η * p ^ 2 * m) := by
    push_cast
    ring
  have he := hf ((t : ℂ) * p)
  change f ((t : ℂ) * p) = f 0 + ((t : ℂ) * p) * L - ((t : ℂ) * p) ^ 2 * m at he
  rw [he, mul_sub, mul_add, hlinear, hquad, Complex.sub_re, Complex.add_re,
    Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  simp only [L, mul_neg, sub_eq_add_neg]

private theorem exists_crossing_of_positive_quadratic (A B C h : ℝ) (hC : 0 < C) :
    ∃ t : ℝ, 0 < t ∧ h < A + t * B + t ^ 2 * C := by
  let t := (|h - A| + |B| + 1) / C + 1
  have hdiv : 0 ≤ (|h - A| + |B| + 1) / C := by positivity
  have ht₁ : 1 ≤ t := by dsimp only [t]; linarith only [hdiv]
  have hCt : C * t = |h - A| + |B| + 1 + C := by
    dsimp only [t]
    rw [mul_add, ← mul_div_assoc, mul_comm C (|h - A| + |B| + 1),
      mul_div_cancel_right₀ _ hC.ne', mul_one]
  have hCB : |h - A| + 1 ≤ C * t + B := by
    rw [hCt]
    linarith only [hC, neg_abs_le B]
  have hp : 0 ≤ C * t + B := (by positivity : 0 ≤ |h - A| + 1).trans hCB
  refine ⟨t, zero_lt_one.trans_le ht₁, ?_⟩
  calc
    h < A + (|h - A| + 1) := by linarith only [le_abs_self (h - A)]
    _ ≤ A + (C * t + B) := add_le_add_left hCB _
    _ ≤ A + t * (C * t + B) := by
      exact add_le_add_left (by simpa only [one_mul] using mul_le_mul_of_nonneg_right ht₁ hp) _
    _ = _ := by ring

/-- If all support maximizers share edge `(i,j)`, opposite shifts
of those entries reach the first new contact without lowering the determinant
support or changing the previous contact products. Nonzero cross sums and distinct matching
products are preserved. -/
theorem exists_first_new_contact_of_common_edge_of_regular [Nontrivial ι]
    (a b : ι → ℂ) (U : Matrix (ι) (ι) ℂ) (hU : IsUnitary U)
    (η : ℂ) (hη : η ≠ 0) (H : ℝ) (i j : ι)
    (hreg : ∀ k l, a k + b l ≠ 0)
    (hmax : ∀ σ : Equiv.Perm (ι), (η * matchingProduct a b σ).re ≤ H)
    (hedge : ∀ σ : Equiv.Perm (ι), (η * matchingProduct a b σ).re = H → σ j = i) :
    ∃ (p : ℂ) (t : ℝ) (τ : Equiv.Perm (ι)), 0 < t ∧ τ j ≠ i ∧
      let c := shiftCoordinate a i ((t : ℂ) * p)
      let d := shiftCoordinate b j (-((t : ℂ) * p))
      (η * matchingProduct c d τ).re = H ∧
      (∀ σ : Equiv.Perm (ι), (η * matchingProduct c d σ).re ≤ H) ∧
      (∀ σ : Equiv.Perm (ι), (η * matchingProduct a b σ).re = H →
        matchingProduct c d σ = matchingProduct a b σ) ∧
      (η * determinantValue a b U).re ≤ (η * determinantValue c d U).re ∧
      (∀ k l, c k + d l ≠ 0) ∧
      (∀ π τ : Equiv.Perm (ι), matchingProduct a b π ≠ matchingProduct a b τ →
        matchingProduct c d π ≠ matchingProduct c d τ) ∧
      (∀ r ∈ Set.Ico (0 : ℝ) t, ∀ σ : Equiv.Perm (ι), σ j ≠ i →
        (η * matchingProduct (shiftCoordinate a i ((r : ℂ) * p))
          (shiftCoordinate b j (-((r : ℂ) * p))) σ).re < H) := by
  classical
  let f (z : ℂ) := determinantValue (shiftCoordinate a i z) (shiftCoordinate b j (-z)) U
  let P (σ : Equiv.Perm (ι)) (z : ℂ) :=
    matchingProduct (shiftCoordinate a i z) (shiftCoordinate b j (-z)) σ
  let M := matchingMixedCoefficient a b i j
  let D := determinantMixedCoefficient a b U i j
  let L := f 1 - f 0 + D
  let E : Set ℂ := ⋃ π : Equiv.Perm (ι), ⋃ τ : Equiv.Perm (ι),
    {z | P π 0 ≠ P τ 0 ∧ P π z = P τ z}
  have hE : E.Finite := by
    refine Set.finite_iUnion fun π => Set.finite_iUnion fun τ => ?_
    by_cases h : P π 0 = P τ 0
    · simp [h]
    · let L (σ : Equiv.Perm (ι)) := P σ 1 - P σ 0 + M σ
      let q : ℂ[X] := C (P π 0 - P τ 0) + X * C (L π - L τ) - X ^ 2 * C (M π - M τ)
      have hq : q ≠ 0 := by
        intro he
        apply h
        simpa [q, sub_eq_zero] using congrArg (fun R : ℂ[X] => R.eval (0 : ℂ)) he
      refine (Polynomial.finite_setOf_isRoot hq).subset ?_
      intro z hz
      obtain ⟨_, hz'⟩ := hz
      change q.eval z = 0
      simp only [q, eval_add, eval_sub, eval_C, eval_mul, eval_X, eval_pow]
      have hπ : P π z = P π 0 + z * L π - z ^ 2 * M π :=
        matchingProduct_oppositeShift_quadratic a b i j π z
      have hτ : P τ z = P τ 0 + z * L τ - z ^ 2 * M τ :=
        matchingProduct_oppositeShift_quadratic a b i j τ z
      linear_combination hz' - hπ + hτ
  let Z : Set ℂ := ⋃ k : ι, ⋃ l : ι,
    {z | shiftCoordinate a i z k + shiftCoordinate b j (-z) l = 0}
  have hZ : Z.Finite := by
    refine Set.finite_iUnion fun k => Set.finite_iUnion fun l => ?_
    by_cases hk : k = i <;> by_cases hl : l = j
    · have he (z : ℂ) : a k + z + (b l + -z) = a k + b l := by ring
      simp only [shiftCoordinate, if_pos hk, if_pos hl, he, hreg k l, Set.setOf_false,
        Set.finite_empty]
    · refine (Set.finite_singleton (-(a k + b l))).subset ?_
      intro z hz
      change shiftCoordinate a i z k + shiftCoordinate b j (-z) l = 0 at hz
      simp only [shiftCoordinate, if_pos hk, if_neg hl] at hz
      apply Set.mem_singleton_iff.mpr
      linear_combination hz
    · refine (Set.finite_singleton (a k + b l)).subset ?_
      intro z hz
      change shiftCoordinate a i z k + shiftCoordinate b j (-z) l = 0 at hz
      simp only [shiftCoordinate, if_neg hk, if_pos hl] at hz
      apply Set.mem_singleton_iff.mpr
      linear_combination -hz
    · simp only [shiftCoordinate, if_neg hk, if_neg hl, hreg k l, Set.setOf_false,
        Set.finite_empty]
  obtain ⟨p, σ, hσedge, hL, hD, hM, hAvoid⟩ :=
    exists_contact_ray a b U hU i j η L hη hreg (E ∪ Z) (hE.union hZ)
  let F (σ : Equiv.Perm (ι)) (r : ℝ) := (η * P σ ((r : ℂ) * p)).re
  have hF (σ : Equiv.Perm (ι)) (r : ℝ) :
      F σ r = (η * P σ 0).re + r * (η * p * (P σ 1 - P σ 0 + M σ)).re +
        r ^ 2 * (-(η * p ^ 2 * M σ).re) :=
    projected_quadratic_ray (P σ) (M σ) η p
      (fun z => matchingProduct_oppositeShift_quadratic a b i j σ z) r
  have hdet (r : ℝ) (hr : 0 ≤ r) : (η * f 0).re ≤ (η * f ((r : ℂ) * p)).re := by
    rw [projected_quadratic_ray f D η p
      (fun z => determinantValue_oppositeShift_quadratic a b U hU i j z) r]
    exact (le_add_of_nonneg_right (mul_nonneg hr hL)).trans
      (le_add_of_nonneg_right (mul_nonneg (sq_nonneg r) hD))
  let S := Finset.univ.filter (fun σ : Equiv.Perm (ι) => σ j ≠ i)
  have hσS : σ ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ σ, hσedge⟩
  have hS : S.Nonempty := ⟨σ, hσS⟩
  let G (r : ℝ) := S.sup' hS (fun σ => F σ r)
  have hG (σ : Equiv.Perm (ι)) (hσ : σ ∈ S) (r : ℝ) : F σ r ≤ G r :=
    Finset.le_sup' (fun σ => F σ r) hσ
  have hcont : Continuous G := by
    apply Continuous.finset_sup'_apply hS
    intro σ _
    rw [show F σ = _ from funext (hF σ)]
    fun_prop
  have hG₀ : G 0 < H := by
    obtain ⟨π, hπS, hπ⟩ := Finset.exists_mem_eq_sup' hS (fun σ => F σ 0)
    change G 0 = F π 0 at hπ
    rw [hπ]
    have hπ₀ : F π 0 = (η * matchingProduct a b π).re := by simp [F, P]
    rw [hπ₀]
    exact lt_of_le_of_ne (hmax π) fun h => (Finset.mem_filter.mp hπS).2 (hedge π h)
  obtain ⟨T, hT, hcross⟩ := exists_crossing_of_positive_quadratic (η * P σ 0).re
    (η * p * (P σ 1 - P σ 0 + M σ)).re (-(η * p ^ 2 * M σ).re) H hM
  have hGT : H < G T := (hcross.trans_eq (hF σ T).symm).trans_le (hG σ hσS T)
  let K : Set ℝ := Set.Icc 0 T ∩ G ⁻¹' {H}
  have hK : IsCompact K := isCompact_Icc.inter_right (isClosed_singleton.preimage hcont)
  have hKne : K.Nonempty := by
    obtain ⟨r, hr, he⟩ := intermediate_value_Icc hT.le hcont.continuousOn
      (show H ∈ Set.Icc (G 0) (G T) from ⟨hG₀.le, hGT.le⟩)
    exact ⟨r, hr, he⟩
  obtain ⟨t, htK, hmin⟩ := hK.exists_isMinOn hKne continuous_id.continuousOn
  have ht : 0 ≤ t := htK.1.1
  have htcontact : G t = H := htK.2
  have htpos : 0 < t := lt_of_le_of_ne ht (fun ht₀ => hG₀.ne (by
    simpa only [← ht₀] using htcontact))
  have hfirst (r : ℝ) (hr : r ∈ Set.Ico (0 : ℝ) t) : G r < H := by
    by_contra h
    have hNH : H ≤ G r := le_of_not_gt h
    obtain ⟨s, hs, he⟩ := intermediate_value_Icc hr.1 hcont.continuousOn
      (show H ∈ Set.Icc (G 0) (G r) from ⟨hG₀.le, hNH⟩)
    have hsK : s ∈ K :=
      ⟨⟨hs.1, hs.2.trans (hr.2.le.trans htK.1.2)⟩, he⟩
    exact (not_lt_of_ge (hmin hsK)) (hs.2.trans_lt hr.2)
  obtain ⟨τ, hτS, hτ⟩ := Finset.exists_mem_eq_sup' hS (fun σ => F σ t)
  change G t = F τ t at hτ
  let c := shiftCoordinate a i ((t : ℂ) * p)
  let d := shiftCoordinate b j (-((t : ℂ) * p))
  have hnew (σ : Equiv.Perm (ι)) : (η * matchingProduct c d σ).re ≤ H := by
    by_cases he : σ j = i
    · rw [matchingProduct_shift_of_edge a b i j σ he]
      exact hmax σ
    · exact (hG σ (Finset.mem_filter.mpr ⟨Finset.mem_univ σ, he⟩) t).trans_eq htcontact
  have hdetnew : (η * determinantValue a b U).re ≤ (η * determinantValue c d U).re := by
    simpa only [f, neg_zero, shiftCoordinate_zero, c, d] using hdet t ht
  refine ⟨p, t, τ, htpos, (Finset.mem_filter.mp hτS).2, hτ.symm.trans htcontact,
    hnew, fun σ hσ => matchingProduct_shift_of_edge a b i j σ (hedge σ hσ) _,
    hdetnew, ?_, ?_, ?_⟩
  · intro k l h
    exact hAvoid t htpos.ne' (Or.inr (Set.mem_iUnion.mpr
      ⟨k, Set.mem_iUnion.mpr ⟨l, h⟩⟩))
  · intro π τ h₀ he
    apply hAvoid t htpos.ne'
    refine Or.inl (Set.mem_iUnion.mpr ⟨π, Set.mem_iUnion.mpr ⟨τ, ?_⟩⟩)
    refine ⟨?_, he⟩
    simpa only [P, neg_zero, shiftCoordinate_zero] using h₀
  · intro r hr π hπ
    exact (hG π (Finset.mem_filter.mpr ⟨Finset.mem_univ π, hπ⟩) r).trans_lt (hfirst r hr)

theorem exists_first_new_contact_of_common_edge
    (a b : Fin 4 → ℂ) (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U)
    (η : ℂ) (H : ℝ) (i j : Fin 4)
    (hmax : ∀ σ : Equiv.Perm (Fin 4), (η * matchingProduct a b σ).re ≤ H)
    (hattain : ∃ σ : Equiv.Perm (Fin 4), (η * matchingProduct a b σ).re = H)
    (hgap : H < (η * determinantValue a b U).re)
    (hedge : ∀ σ : Equiv.Perm (Fin 4), (η * matchingProduct a b σ).re = H → σ j = i) :
    ∃ (p : ℂ) (t : ℝ) (τ : Equiv.Perm (Fin 4)), 0 < t ∧ τ j ≠ i ∧
      let c := shiftCoordinate a i ((t : ℂ) * p)
      let d := shiftCoordinate b j (-((t : ℂ) * p))
      (η * matchingProduct c d τ).re = H ∧
      (∀ σ : Equiv.Perm (Fin 4), (η * matchingProduct c d σ).re ≤ H) ∧
      (∀ σ : Equiv.Perm (Fin 4), (η * matchingProduct a b σ).re = H →
        matchingProduct c d σ = matchingProduct a b σ) ∧
      (η * determinantValue a b U).re ≤ (η * determinantValue c d U).re ∧
      (∀ k l, c k + d l ≠ 0) ∧
      (∀ π τ : Equiv.Perm (Fin 4), matchingProduct a b π ≠ matchingProduct a b τ →
        matchingProduct c d π ≠ matchingProduct c d τ) ∧
      (∀ r ∈ Set.Ico (0 : ℝ) t, ∀ σ : Equiv.Perm (Fin 4), σ j ≠ i →
        (η * matchingProduct (shiftCoordinate a i ((r : ℂ) * p))
          (shiftCoordinate b j (-((r : ℂ) * p))) σ).re < H) := by
  have hη : η ≠ 0 := by
    intro h
    obtain ⟨σ, hσ⟩ := hattain
    simp only [h, zero_mul, Complex.zero_re] at hσ hgap
    linarith only [hσ, hgap]
  have hreg (k l : Fin 4) : a k + b l ≠ 0 := by
    intro h
    obtain ⟨σ, hσ⟩ := (holds_iff_directional a b U).mp
      (holds_four_of_opposite_entries a b U hU h) η
    exact (not_le_of_gt hgap) (hσ.trans (hmax σ))
  exact exists_first_new_contact_of_common_edge_of_regular a b U hU η hη H i j hreg hmax hedge

/-- Without decreasing the determinant projection or changing any previous
contact product, regular spectra can be moved to a support face whose active
matchings share no edge. -/
theorem exists_no_common_active_edge_of_regular_support [Nontrivial ι]
    (a b : ι → ℂ) (U : Matrix (ι) (ι) ℂ) (hU : IsUnitary U)
    (η : ℂ) (hη : η ≠ 0) (H : ℝ)
    (hreg : ∀ k l, a k + b l ≠ 0)
    (hmax : ∀ σ : Equiv.Perm (ι), (η * matchingProduct a b σ).re ≤ H) :
    ∃ c d : ι → ℂ,
      (η * determinantValue a b U).re ≤ (η * determinantValue c d U).re ∧
      (∀ σ : Equiv.Perm (ι), (η * matchingProduct c d σ).re ≤ H) ∧
      (∀ σ : Equiv.Perm (ι), (η * matchingProduct a b σ).re = H →
        matchingProduct c d σ = matchingProduct a b σ) ∧
      (∀ π τ : Equiv.Perm (ι), matchingProduct a b π ≠ matchingProduct a b τ →
        matchingProduct c d π ≠ matchingProduct c d τ) ∧
      (∀ k l, c k + d l ≠ 0) ∧
      ∀ i j : ι, ∃ σ : Equiv.Perm (ι), (η * matchingProduct c d σ).re = H ∧ σ j ≠ i := by
  classical
  let A (c d : ι → ℂ) :=
    Finset.univ.filter (fun σ : Equiv.Perm (ι) => (η * matchingProduct c d σ).re = H)
  have hA (c d : ι → ℂ) (σ : Equiv.Perm (ι)) :
      σ ∈ A c d ↔ (η * matchingProduct c d σ).re = H := by
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
  let K : Set (Finset (Equiv.Perm (ι))) := {S | ∃ c d : ι → ℂ,
    S = A c d ∧ (∀ k l, c k + d l ≠ 0) ∧
    (∀ σ : Equiv.Perm (ι), (η * matchingProduct c d σ).re ≤ H) ∧
    (η * determinantValue a b U).re ≤ (η * determinantValue c d U).re ∧
    (∀ σ : Equiv.Perm (ι), σ ∈ A a b → matchingProduct c d σ = matchingProduct a b σ) ∧
    ∀ π τ : Equiv.Perm (ι), matchingProduct a b π ≠ matchingProduct a b τ →
      matchingProduct c d π ≠ matchingProduct c d τ}
  have hK : K.Nonempty := ⟨A a b, a, b, rfl, hreg, hmax, le_rfl, fun _ _ => rfl, fun _ _ h => h⟩
  obtain ⟨T, hT, hmaximal⟩ := (Set.toFinite K).exists_maximal_wrt id K hK
  obtain ⟨c, d, rfl, hcReg, hc, hd, hp, hinj⟩ := hT
  refine ⟨c, d, hd, hc, fun σ h => hp σ ((hA a b σ).mpr h), hinj, hcReg, ?_⟩
  intro i j
  by_contra hn
  have hcommon (σ : Equiv.Perm (ι)) (hσ : (η * matchingProduct c d σ).re = H) :
      σ j = i := by
    by_contra he
    exact hn ⟨σ, hσ, he⟩
  obtain ⟨p, t, τ, _, hτedge, hτ, hupper, hpres, hdet, hreg', hinj', _⟩ :=
    exists_first_new_contact_of_common_edge_of_regular c d U hU η hη H i j hcReg hc hcommon
  let c' := shiftCoordinate c i ((t : ℂ) * p)
  let d' := shiftCoordinate d j (-((t : ℂ) * p))
  have hsubset : A c d ⊆ A c' d' := by
    intro σ hσ
    have h := (hA c d σ).mp hσ
    apply (hA c' d' σ).mpr
    rw [hpres σ h]
    exact h
  have hK' : A c' d' ∈ K := by
    refine ⟨c', d', rfl, hreg', hupper, hd.trans hdet, fun σ h => ?_,
      fun π τ h => hinj' π τ (hinj π τ h)⟩
    have hcd := hp σ h
    have hcontact : (η * matchingProduct c d σ).re = H := by
      rw [hcd]
      exact (hA a b σ).mp h
    exact (hpres σ hcontact).trans hcd
  have he : A c d = A c' d' := hmaximal _ hK' hsubset
  have hm : τ ∈ A c' d' := (hA c' d' τ).mpr hτ
  rw [← he] at hm
  exact hτedge (hcommon τ ((hA c d τ).mp hm))

/-- An order-four violation can retain all its active products at the same
support level while reaching a contact set with no shared matching edge. -/
theorem exists_no_common_active_edge_of_four_violation
    (a b : Fin 4 → ℂ) (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U)
    (η : ℂ) (H : ℝ)
    (hmax : ∀ σ : Equiv.Perm (Fin 4), (η * matchingProduct a b σ).re ≤ H)
    (hattain : ∃ σ : Equiv.Perm (Fin 4), (η * matchingProduct a b σ).re = H)
    (hgap : H < (η * determinantValue a b U).re) :
    ∃ c d : Fin 4 → ℂ,
      (η * determinantValue a b U).re ≤ (η * determinantValue c d U).re ∧
      (∀ σ : Equiv.Perm (Fin 4), (η * matchingProduct c d σ).re ≤ H) ∧
      (∀ σ : Equiv.Perm (Fin 4), (η * matchingProduct a b σ).re = H →
        matchingProduct c d σ = matchingProduct a b σ) ∧
      (∀ π τ : Equiv.Perm (Fin 4), matchingProduct a b π ≠ matchingProduct a b τ →
        matchingProduct c d π ≠ matchingProduct c d τ) ∧
      ∀ i j : Fin 4, ∃ σ : Equiv.Perm (Fin 4), (η * matchingProduct c d σ).re = H ∧ σ j ≠ i := by
  have hη : η ≠ 0 := by
    intro h
    obtain ⟨σ, hσ⟩ := hattain
    simp only [h, zero_mul, Complex.zero_re] at hσ hgap
    linarith only [hσ, hgap]
  have hreg (k l : Fin 4) : a k + b l ≠ 0 := by
    intro h
    obtain ⟨σ, hσ⟩ := (holds_iff_directional a b U).mp
      (holds_four_of_opposite_entries a b U hU h) η
    exact (not_le_of_gt hgap) (hσ.trans (hmax σ))
  obtain ⟨c, d, hd, hm, hp, hi, _, he⟩ :=
    exists_no_common_active_edge_of_regular_support a b U hU η hη H hreg hmax
  exact ⟨c, d, hd, hm, hp, hi, he⟩

/-- The all-order conjecture reduces to regular supports where every edge is
omitted by some maximizing matching. -/
theorem conjecture_iff_support_without_common_active_edge [Nontrivial ι] :
    Conjecture ι ↔ ∀ (a b : ι → ℂ) (U : Matrix ι ι ℂ), IsUnitary U →
      (∀ i j, a i + b j ≠ 0) → Function.Injective (matchingProduct a b) →
      ∀ (η : ℂ) (H : ℝ),
        (∀ σ : Equiv.Perm ι, (η * matchingProduct a b σ).re ≤ H) →
        (∀ i j, ∃ σ : Equiv.Perm ι, (η * matchingProduct a b σ).re = H ∧ σ j ≠ i) →
        (η * determinantValue a b U).re ≤ H := by
  constructor
  · intro h a b U hU _ _ η H hm _
    obtain ⟨σ, hσ⟩ := (holds_iff_directional a b U).mp (h a b U hU) η
    exact hσ.trans (hm σ)
  · intro h
    apply conjecture_iff_regular_matching_products.mpr
    intro a b U hU hreg hinj
    apply (holds_iff_directional a b U).mpr
    intro η
    by_cases hη : η = 0
    · exact ⟨1, by simp [hη]⟩
    obtain ⟨r, _, hr⟩ := Finset.exists_max_image Finset.univ
      (fun σ : Equiv.Perm ι => (η * matchingProduct a b σ).re) ⟨1, Finset.mem_univ _⟩
    let H := (η * matchingProduct a b r).re
    obtain ⟨c, d, hd, hm, _, hdistinct, hreg', hnoedge⟩ :=
      exists_no_common_active_edge_of_regular_support a b U hU η hη H hreg
        (fun σ => hr σ (Finset.mem_univ _))
    have hinj' : Function.Injective (matchingProduct c d) := by
      intro σ τ he
      by_contra hne
      exact hdistinct σ τ (hinj.ne hne) he
    exact ⟨r, hd.trans (h c d U hU hreg' hinj' η H hm hnoedge)⟩

end

end MOC
