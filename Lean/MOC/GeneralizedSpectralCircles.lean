import MOC.CircleSpectra
import MOC.OneOffLine
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.LinearCombination

/-! Common projective changes of the two signed spectra preserve the determinant
hull inclusion. A pole on a circle sends that circle to a real affine line. -/

open Matrix
open scoped Polynomial ComplexConjugate

namespace MOC

private def circleValue (q u v c : ℝ) (z : ℂ) : ℝ :=
  q * Complex.normSq z - 2 * (u * z.re + v * z.im) + c

/-- The spectrum lies on a circle, a point circle, or an affine line. -/
def SpectrumOnGeneralizedCircle {ι : Type*} (f : ι → ℂ) : Prop :=
  ∃ q u v c : ℝ, (q ≠ 0 ∨ u ≠ 0 ∨ v ≠ 0) ∧ ∀ i, circleValue q u v c (f i) = 0

theorem spectrumOnGeneralizedCircle_of_circle {ι : Type*} (a : ι → ℂ) (o : ℂ) (r : ℝ)
    (ha : ∀ i, Complex.normSq (a i - o) = r) : SpectrumOnGeneralizedCircle a := by
  refine ⟨1, o.re, o.im, Complex.normSq o - r, Or.inl one_ne_zero, fun i => ?_⟩
  have hi := ha i
  simp only [Complex.normSq_sub, Complex.mul_re, Complex.conj_re, Complex.conj_im] at hi
  unfold circleValue
  linear_combination hi

theorem spectrumOnGeneralizedCircle_of_line {ι : Type*} (a : ι → ℂ) (u v c : ℝ)
    (huv : u ≠ 0 ∨ v ≠ 0) (ha : ∀ i, u * (a i).re + v * (a i).im = c) :
    SpectrumOnGeneralizedCircle a := by
  refine ⟨0, u, v, 2 * c, Or.inr huv, fun i => ?_⟩
  simp only [circleValue, zero_mul, zero_sub, ha i, neg_add_cancel]

theorem spectrumOnGeneralizedCircle_neg {ι : Type*} {a : ι → ℂ}
    (ha : SpectrumOnGeneralizedCircle a) : SpectrumOnGeneralizedCircle (fun i => -a i) := by
  obtain ⟨q, u, v, c, h, ha⟩ := ha
  refine ⟨q, -u, -v, c, by simpa only [neg_ne_zero] using h, fun i => ?_⟩
  simpa only [circleValue, Complex.normSq_neg, Complex.neg_re, Complex.neg_im,
    neg_mul, mul_neg, neg_neg] using ha i

section RealChart

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem holds_affine_chart_iff (a b : ι → ℂ) (U : Matrix ι ι ℂ)
    (hU : IsUnitary U) (d t : ℂ) (hd : d ≠ 0) :
    Holds (fun i => d * a i + t) (fun i => d * b i - t) U ↔ Holds a b U :=
  (holds_shift_iff _ _ hU t).trans
    (hull_common_factor_iff (pow_ne_zero _ hd) (determinantValue_scale a b U d)
      (matchingProduct_scale a b d))

private theorem exists_real_affine_chart (a b : ι → ℂ) (U : Matrix ι ι ℂ)
    (hU : IsUnitary U) (d : ℂ) (hd : d ≠ 0) (s : ℝ) :
    ∃ (x : ι → ℂ) (f : ℂ → ℂ),
      (∀ i, (d * a i).re = s → (x i).im = 0) ∧
      (∀ i, (d * (-b i)).re = s → (f (b i)).im = 0) ∧
      (Holds x (f ∘ b) U ↔ Holds a b U) := by
  let k := -Complex.I * d
  let t : ℂ := (s : ℂ) * Complex.I
  have hk : k ≠ 0 := mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hd
  have him (z : ℂ) : (k * z + t).im = s - (d * z).re := by
    rw [show k * z = -(Complex.I * (d * z)) by simp [k, mul_assoc]]
    simp [t, Complex.I_mul_im, Complex.mul_im, sub_eq_add_neg, add_comm]
  refine ⟨fun i => k * a i + t, fun z => k * z - t, ?_, ?_,
    holds_affine_chart_iff a b U hU k t hk⟩
  · intro i hi
    rw [him, hi, sub_self]
  · intro i hi
    change (k * b i - t).im = 0
    rw [show k * b i - t = -(k * (-b i) + t) by ring, Complex.neg_im, him, hi,
      sub_self, neg_zero]

private theorem exists_real_circle_chart (a b : ι → ℂ) (U : Matrix ι ι ℂ)
    (hU : IsUnitary U) (o : ℂ) (r : ℝ) (ha : ∀ i, Complex.normSq (a i - o) = r) :
    ∃ (x : ι → ℂ) (f : ℂ → ℂ),
      (∀ i, (x i).im = 0) ∧
      (∀ i, Complex.normSq (-b i - o) = r → (f (b i)).im = 0) ∧
      (Holds x (f ∘ b) U ↔ Holds a b U) := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · letI := hι
    exact ⟨a, id, fun i => isEmptyElim i, fun i => isEmptyElim i, Iff.rfl⟩
  by_cases hr : r = 0
  · refine ⟨fun i => a i + -o, fun z => z - -o, ?_, ?_, holds_shift_iff a b hU (-o)⟩
    · intro i
      have hz := Complex.normSq_eq_zero.mp ((ha i).trans hr)
      simp [← sub_eq_add_neg, hz]
    · intro i hi
      have hz := Complex.normSq_eq_zero.mp (hi.trans hr)
      change (b i - -o).im = 0
      rw [show b i - -o = -(-b i - o) by ring, hz, neg_zero, Complex.zero_im]
  obtain ⟨i₀⟩ := hι
  let d := a i₀ - o
  have hd : d ≠ 0 := by
    intro hz
    exact hr ((ha i₀).symm.trans (by simp [show a i₀ - o = 0 from hz]))
  let p : ℝ → ℂ := fun t => o + d * circleRotation t
  have hpinj : Function.Injective p := by
    intro s t h
    change o + d * circleRotation s = o + d * circleRotation t at h
    exact circleRotation_injective (mul_left_cancel₀ hd (add_left_cancel h))
  obtain ⟨_, ⟨t, rfl⟩, ht⟩ := (Set.infinite_range_of_injective hpinj).exists_not_mem_finset
    ((Finset.univ.image a) ∪ (Finset.univ.image fun i => -b i))
  have hap (i : ι) : a i - p t ≠ 0 := fun hz => ht
    (Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, sub_eq_zero.mp hz⟩)))
  have hbp (i : ι) : -b i - p t ≠ 0 := fun hz => ht
    (Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, sub_eq_zero.mp hz⟩)))
  have hp : Complex.normSq (p t - o) = r := by
    simp only [p, add_sub_cancel_left, Complex.normSq_mul, circleRotation_normSq, mul_one]
    exact ha i₀
  let u := o - p t
  have hu : Complex.normSq u = r := by
    rw [show u = -(p t - o) by dsimp [u]; ring, Complex.normSq_neg, hp]
  have hune : u ≠ 0 := fun h => hr (hu.symm.trans (by simp [h]))
  let A (i : ι) := (a i - p t)⁻¹
  let B (i : ι) := -(-b i - p t)⁻¹
  have hline (z : ℂ) (hz : z - p t ≠ 0) (hc : Complex.normSq (z - o) = r) :
      (u * (z - p t)⁻¹).re = 1 / 2 := by
    apply re_mul_inv_of_circle u (z - p t) hz
    rw [show z - p t - u = z - o by dsimp [u]; ring, hc, hu]
  obtain ⟨x, f, hx, hy, hxy⟩ := exists_real_affine_chart A B U hU u hune (1 / 2)
  refine ⟨x, fun z => f (-(-z - p t)⁻¹), fun i => hx i (hline _ (hap i) (ha i)), ?_, ?_⟩
  · intro i hi
    exact hy i (by simpa only [B, neg_neg] using hline _ (hbp i) hi)
  · have hinv := holds_inv_iff (fun i => a i - p t) (fun i => -b i - p t) U hU hap hbp
    exact hxy.trans (hinv.trans (by
      simpa only [sub_eq_add_neg, neg_add, neg_neg] using holds_shift_iff a b hU (-(p t))))

private theorem exists_real_generalized_circle_chart (a b : ι → ℂ) (U : Matrix ι ι ℂ)
    (hU : IsUnitary U) (q u v c : ℝ) (h : q ≠ 0 ∨ u ≠ 0 ∨ v ≠ 0)
    (ha : ∀ i, circleValue q u v c (a i) = 0) :
    ∃ (x : ι → ℂ) (f : ℂ → ℂ),
      (∀ i, (x i).im = 0) ∧
      (∀ i, circleValue q u v c (-b i) = 0 → (f (b i)).im = 0) ∧
      (Holds x (f ∘ b) U ↔ Holds a b U) := by
  by_cases hq : q = 0
  · let d : ℂ := ⟨u, -v⟩
    have hd : d ≠ 0 := by
      intro hd
      have hu : u = 0 := congrArg Complex.re hd
      have hv : v = 0 := by simpa [d] using congrArg Complex.im hd
      simp [hq, hu, hv] at h
    have hline (z : ℂ) (hz : circleValue q u v c z = 0) : (d * z).re = c / 2 := by
      simp only [circleValue, hq, zero_mul, zero_sub] at hz
      change u * z.re - -v * z.im = c / 2
      linarith
    obtain ⟨x, y, hx, hy, hxy⟩ := exists_real_affine_chart a b U hU d hd (c / 2)
    exact ⟨x, y, fun i => hx i (hline _ (ha i)), fun i hi => hy i (hline _ hi), hxy⟩
  · let o : ℂ := ⟨u / q, v / q⟩
    let r := Complex.normSq o - c / q
    have hcircle (z : ℂ) (hz : circleValue q u v c z = 0) : Complex.normSq (z - o) = r := by
      have hnorm : Complex.normSq z = (2 * (u * z.re + v * z.im) - c) / q := by
        apply (eq_div_iff hq).mpr
        unfold circleValue at hz
        linarith
      have hdot : (z * conj o).re = (u * z.re + v * z.im) / q := by
        change z.re * (u / q) - z.im * (-(v / q)) = _
        field_simp [hq] <;> ring
      rw [Complex.normSq_sub, hnorm, hdot]
      dsimp only [r]
      ring
    obtain ⟨x, y, hx, hy, hxy⟩ := exists_real_circle_chart a b U hU o r (fun i => hcircle _ (ha i))
    exact ⟨x, y, hx, fun i hi => hy i (hcircle _ hi), hxy⟩

private theorem ofReal_re_of_im_zero (z : ℂ) (hz : z.im = 0) : (z.re : ℂ) = z :=
  Complex.ext rfl hz.symm

/-- A common generalized circle makes the first spectrum and the specified
entries of the second spectrum real. One function transforms the partner values. -/
theorem exists_real_chart_of_common_generalized_circle (a b : ι → ℂ) (p : ι → Prop)
    (ha : SpectrumOnGeneralizedCircle (Sum.elim a (fun i : {i // p i} => -b i.val)))
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) :
    ∃ (x : ι → ℝ) (f : ℂ → ℂ), (∀ i, p i → (f (b i)).im = 0) ∧
      (Holds (fun i => (x i : ℂ)) (f ∘ b) U ↔ Holds a b U) := by
  obtain ⟨q, u, v, c, h, hs⟩ := ha
  obtain ⟨x, f, hx, hf, hxf⟩ :=
    exists_real_generalized_circle_chart a b U hU q u v c h (fun i => hs (Sum.inl i))
  have hleft : (fun i => ((x i).re : ℂ)) = x :=
    funext fun i => ofReal_re_of_im_zero _ (hx i)
  refine ⟨fun i => (x i).re, f, fun i hi => hf i (hs (Sum.inr ⟨i, hi⟩)), ?_⟩
  rwa [hleft]

/-- A single spectrum on a circle or line can be made real, while the other
spectrum remains arbitrary. The relative unitary is unchanged. -/
theorem exists_real_spectrum_of_generalized_circle (a b : ι → ℂ)
    (ha : SpectrumOnGeneralizedCircle a) (U : Matrix ι ι ℂ) (hU : IsUnitary U) :
    ∃ (x : ι → ℝ) (y : ι → ℂ), Holds (fun i => (x i : ℂ)) y U ↔ Holds a b U := by
  obtain ⟨q, u, v, c, h, ha⟩ := ha
  obtain ⟨x, y, hx, _, hxy⟩ := exists_real_generalized_circle_chart a b U hU q u v c h ha
  have hleft : (fun i => ((x i).re : ℂ)) = x :=
    funext fun i => ofReal_re_of_im_zero _ (hx i)
  exact ⟨fun i => (x i).re, y ∘ b, by simpa only [hleft] using hxy⟩

/-- If the first spectrum and all but one entry of the reflected second spectrum
lie on the same generalized circle, inclusion holds in every finite dimension. -/
theorem holds_of_common_circle_with_one_outlier (a b : ι → ℂ) (j : ι)
    (hcircle : SpectrumOnGeneralizedCircle
      (Sum.elim a (fun i : {i // i ≠ j} => -b i.val)))
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) : Holds a b U := by
  obtain ⟨x, f, hy, hxy⟩ :=
    exists_real_chart_of_common_generalized_circle a b (fun i => i ≠ j) hcircle U hU
  let y := f ∘ b
  have hright : Function.update (fun i => ((y i).re : ℂ)) j (y j) = y := by
    funext i
    by_cases hi : i = j
    · subst i
      exact Function.update_self j _ _
    · rw [Function.update_of_ne hi]
      exact ofReal_re_of_im_zero _ (hy i hi)
  apply hxy.mp
  simpa only [hright] using
    holds_of_one_complex_entry x (fun i => (y i).re) j (y j) U hU

end RealChart

private noncomputable def circlePolynomial (q u v c : ℝ) : ℝ[X] :=
  Polynomial.C q * Polynomial.X ^ 4 + Polynomial.C (q - 2 * v) * Polynomial.X ^ 2 -
    Polynomial.C (2 * u) * Polynomial.X + Polynomial.C c

private theorem circlePolynomial_eval (q u v c t : ℝ) :
    (circlePolynomial q u v c).eval t = circleValue q u v c ⟨t, t ^ 2⟩ := by
  simp [circlePolynomial, circleValue, Complex.normSq_apply] <;> ring

private theorem circlePolynomial_ne_zero (q u v c : ℝ) (h : q ≠ 0 ∨ u ≠ 0 ∨ v ≠ 0) :
    circlePolynomial q u v c ≠ 0 := by
  intro hz
  have hq : q = 0 := by
    have he := congrArg (fun f : ℝ[X] => f.coeff 4) hz
    simp only [circlePolynomial, Polynomial.coeff_add, Polynomial.coeff_sub,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X, Polynomial.coeff_C,
      Polynomial.coeff_zero] at he
    norm_num at he
    exact he
  have hu : u = 0 := by
    have he := congrArg (fun f : ℝ[X] => f.coeff 1) hz
    simp only [circlePolynomial, Polynomial.coeff_add, Polynomial.coeff_sub,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X, Polynomial.coeff_C,
      Polynomial.coeff_zero] at he
    norm_num at he
    linarith only [he]
  have hv : v = 0 := by
    have he := congrArg (fun f : ℝ[X] => f.coeff 2) hz
    simp only [circlePolynomial, hq, Polynomial.coeff_add, Polynomial.coeff_sub,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X, Polynomial.coeff_C,
      Polynomial.coeff_zero] at he
    norm_num at he
    linarith only [he]
  simp [hq, hu, hv] at h

private theorem exists_inversion_pole (q u v c Q U V C : ℝ)
    (h : q ≠ 0 ∨ u ≠ 0 ∨ v ≠ 0) (h' : Q ≠ 0 ∨ U ≠ 0 ∨ V ≠ 0) :
    ∃ p : ℂ, circleValue q u v c p ≠ 0 ∧ circleValue Q U V C p ≠ 0 := by
  let f := circlePolynomial q u v c
  let g := circlePolynomial Q U V C
  obtain ⟨r, hr⟩ := Polynomial.exists_max_root (f * g)
    (mul_ne_zero (circlePolynomial_ne_zero _ _ _ _ h) (circlePolynomial_ne_zero _ _ _ _ h'))
  let t := r + 1
  have ht : f.eval t * g.eval t ≠ 0 := by
    intro hz
    have ht' := hr t (by simpa only [Polynomial.IsRoot, Polynomial.eval_mul] using hz)
    dsimp only [t] at ht'
    linarith
  have ha : f.eval t ≠ 0 := fun hf => ht (by rw [hf, zero_mul])
  have hb : g.eval t ≠ 0 := fun hg => ht (by rw [hg, mul_zero])
  exact ⟨⟨t, t ^ 2⟩, by simpa only [f, circlePolynomial_eval] using ha,
    by simpa only [g, circlePolynomial_eval] using hb⟩

private theorem inversion_circle (q u v c : ℝ) (p : ℂ) (hp : circleValue q u v c p ≠ 0) :
    ∃ (o : ℂ) (r : ℝ), ∀ z, circleValue q u v c z = 0 →
      z - p ≠ 0 ∧ Complex.normSq ((z - p)⁻¹ - o) = r := by
  let d := circleValue q u v c p
  let o : ℂ := ⟨(u - q * p.re) / d, -(v - q * p.im) / d⟩
  have hd : d ≠ 0 := hp
  refine ⟨o, Complex.normSq o - q / d, fun z hz => ?_⟩
  let x := z - p
  have hx : x ≠ 0 := fun h => hp (sub_eq_zero.mp h ▸ hz)
  have hnx := (Complex.normSq_pos.mpr hx).ne'
  refine ⟨hx, ?_⟩
  change Complex.normSq (x⁻¹ - o) = _
  have htranslated : q * Complex.normSq x -
      2 * ((u - q * p.re) * x.re + (v - q * p.im) * x.im) + d = 0 := by
    dsimp only [x, d, circleValue] at hz ⊢
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im] at hz ⊢
    linear_combination hz
  have hinv : d * Complex.normSq x⁻¹ -
      2 * ((u - q * p.re) * (x⁻¹).re - (v - q * p.im) * (x⁻¹).im) + q = 0 := by
    rw [Complex.normSq_inv, Complex.inv_re, Complex.inv_im]
    field_simp [hnx] <;> linear_combination htranslated
  have hdot : (x⁻¹ * conj o).re =
      ((u - q * p.re) * (x⁻¹).re - (v - q * p.im) * (x⁻¹).im) / d := by
    simp only [o, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    field_simp [hd]
    ring
  let t := (u - q * p.re) * (x⁻¹).re - (v - q * p.im) * (x⁻¹).im
  have hscaled : (Complex.normSq x⁻¹ - 2 * t / d) * d = -q := by
    rw [sub_mul, div_mul_cancel₀ _ hd]
    dsimp only [t]
    linarith only [hinv]
  have he := (eq_div_iff hd).mpr hscaled
  rw [neg_div] at he
  rw [Complex.normSq_sub, hdot, ← mul_div_assoc]
  change Complex.normSq x⁻¹ + Complex.normSq o - 2 * t / d = Complex.normSq o - q / d
  linarith only [he]

/-- Inclusion for ordinary circles transfers to spectral lines and circles. -/
theorem holds_of_generalized_circular_spectra_of_circular {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℂ) (ha : SpectrumOnGeneralizedCircle a)
    (hb : SpectrumOnGeneralizedCircle (fun i => -b i)) (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (hcircles : ∀ (e f : ι → ℂ) (o p : ℂ) (r s : ℝ),
      (∀ i, Complex.normSq (e i - o) = r) → (∀ i, Complex.normSq (-f i - p) = s) → Holds e f U) :
    Holds a b U := by
  obtain ⟨q, u, v, c, hq, ha⟩ := ha
  obtain ⟨Q, S, T, C, hQ, hb⟩ := hb
  obtain ⟨p, hp, hp'⟩ := exists_inversion_pole q u v c Q S T C hq hQ
  obtain ⟨o, r, ha'⟩ := inversion_circle q u v c p hp
  obtain ⟨o', r', hb'⟩ := inversion_circle Q S T C p hp'
  let e (i : ι) := a i - p
  let f (i : ι) := -b i - p
  have hcircle : Holds (fun i => (e i)⁻¹) (fun i => -(f i)⁻¹) U := by
    apply hcircles _ _ o o' r r' (fun i => (ha' (a i) (ha i)).2)
    intro i
    simpa only [f, neg_neg] using (hb' (-b i) (hb i)).2
  have hshift := (holds_inv_iff e f U hU (fun i => (ha' (a i) (ha i)).1)
    (fun i => (hb' (-b i) (hb i)).1)).mp hcircle
  apply (holds_shift_iff a b hU (-p)).mp
  simpa only [e, f, sub_eq_add_neg, neg_add, neg_neg] using hshift

/-- Any spectrum with at most three distinct values lies on a generalized circle. -/
theorem spectrumOnGeneralizedCircle_of_card_range_le_three {ι : Type*} [Fintype ι]
    (a : ι → ℂ) (ha : Nat.card (Set.range a) ≤ 3) : SpectrumOnGeneralizedCircle a := by
  classical
  by_cases hi : Nonempty ι
  · letI : Fintype (Set.range a) := Fintype.ofFinite _
    let L : (Fin 4 → ℝ) →ₗ[ℝ] (Set.range a → ℝ) :=
      { toFun := fun x z => circleValue (x 0) (x 1) (x 2) (x 3) z.val
        map_add' := by intro x y; ext z; simp [circleValue] <;> ring
        map_smul' := by intro r x; ext z; simp [circleValue] <;> ring }
    have hdim : Module.finrank ℝ (Set.range a → ℝ) < Module.finrank ℝ (Fin 4 → ℝ) := by
      rw [Module.finrank_pi, Module.finrank_pi, Fintype.card_fin]
      rw [Nat.card_eq_fintype_card] at ha
      omega
    obtain ⟨x, hx, hx₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (L.ker_ne_bot_of_finrank_lt hdim)
    have hL (i : ι) : circleValue (x 0) (x 1) (x 2) (x 3) (a i) = 0 :=
      congrFun (LinearMap.mem_ker.mp hx) (⟨a i, ⟨i, rfl⟩⟩ : Set.range a)
    refine ⟨x 0, x 1, x 2, x 3, ?_, hL⟩
    by_contra! hzero
    obtain ⟨h0, h1, h2⟩ := hzero
    obtain ⟨i⟩ := hi
    have h3 : x 3 = 0 := by simpa [circleValue, h0, h1, h2] using hL i
    apply hx₀
    funext j
    fin_cases j <;> assumption
  · exact ⟨1, 0, 0, 0, Or.inl one_ne_zero, fun i => (hi ⟨i⟩).elim⟩

end MOC
