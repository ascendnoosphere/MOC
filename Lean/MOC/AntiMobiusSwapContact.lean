import MOC.TwoSpectralCircles
import MOC.ContactCrossRatios

/-! A nonzero-height clique of swap contacts cannot realize a noncircular
anti-fractional correspondence between its two spectral label lists. For
background on the four-point circle criterion, see DOI: 10.1093/imrn/rnag094. -/

open scoped ComplexConjugate

namespace MOC

private theorem real_affine_norm_form_forces_circle_or_coefficients
    {ι : Type*} [Nonempty ι] (A : ι → ℂ) (r s u v : ℂ)
    (h : ∀ i, (u * (Complex.normSq (A i) : ℂ) + v * A i - r * conj (A i) - s).im = 0) :
    SpectrumOnGeneralizedCircle A ∨
      (u.im = 0 ∧ s.im = 0 ∧ r.im = v.im ∧ r.re = -v.re) := by
  by_cases hn : u.im ≠ 0 ∨ (v.im - r.im) ≠ 0 ∨ (v.re + r.re) ≠ 0
  · left
    refine ⟨u.im, -(v.im - r.im) / 2, -(v.re + r.re) / 2, -s.im, ?_, ?_⟩
    · rcases hn with h0 | h0 | h0
      · exact Or.inl h0
      · exact Or.inr (Or.inl (div_ne_zero (neg_ne_zero.mpr h0) (by norm_num)))
      · exact Or.inr (Or.inr (div_ne_zero (neg_ne_zero.mpr h0) (by norm_num)))
    · intro i
      change u.im * Complex.normSq (A i) -
        2 * ((-(v.im - r.im) / 2) * (A i).re + (-(v.re + r.re) / 2) * (A i).im) -
        s.im = 0
      have hi := h i
      simp only [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_im,
        Complex.ofReal_re, Complex.conj_re, Complex.conj_im, mul_zero, zero_add] at hi
      linear_combination hi
  · right
    push_neg at hn
    obtain ⟨hu, hrim, hrre⟩ := hn
    have hs : s.im = 0 := by
      have hi := h (Classical.choice (inferInstance : Nonempty ι))
      simp only [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_im,
        Complex.ofReal_re, Complex.conj_re, Complex.conj_im, mul_zero, zero_add] at hi
      linear_combination -hi + Complex.normSq (A (Classical.choice inferInstance)) * hu +
        (A (Classical.choice inferInstance)).re * hrim + (A (Classical.choice inferInstance)).im * hrre
    have hrim' : r.im = v.im := (sub_eq_zero.mp hrim).symm
    have hrre' : r.re = -v.re := by linarith
    exact ⟨hu, hs, hrim', hrre'⟩

/-- The algebraic step for the anti-Möbius alternative. The only
graph condition is that any pair has a third label available; all its
swap tests are imposed. The conclusion concerns the entire supplied set
of labels, not the rest of a spectrum. -/
theorem generalizedCircle_of_antiMobius_swap_contacts
    {ι : Type*} [Nonempty ι] (A B : ι → ℂ) (r s u v z : ℂ)
    (hA : Function.Injective A) (hthird : ∀ i j : ι, i ≠ j → ∃ k, k ≠ i ∧ k ≠ j)
    (hpair : ∃ i j : ι, i ≠ j)
    (hden : ∀ i, u * conj (A i) + v ≠ 0)
    (hAB : ∀ i, A i - B i ≠ 0)
    (hB : ∀ i, B i = (r * conj (A i) + s) / (u * conj (A i) + v))
    (hdet : r * v - s * u ≠ 0) (hz : z.re ≠ 0)
    (hgap : ∀ i j, i ≠ j →
      (z * ((A i - A j) * (B i - B j) / ((A i - B i) * (A j - B j)))).re = 0) :
    SpectrumOnGeneralizedCircle A := by
  classical
  let d (i : ι) := u * conj (A i) + v
  let L (i : ι) := (A i - B i) * d i
  let D := r * v - s * u
  have hL (i : ι) : L i ≠ 0 := mul_ne_zero (hAB i) (hden i)
  have hLform (i : ι) : L i =
      u * (Complex.normSq (A i) : ℂ) + v * A i - r * conj (A i) - s := by
    change (A i - B i) * d i = _
    rw [sub_mul, hB i]
    change A i * d i - ((r * conj (A i) + s) / d i) * d i = _
    rw [div_mul_cancel₀ _ (hden i)]
    dsimp only [d]
    rw [mul_add, ← mul_left_comm, Complex.mul_conj]
    ring
  have hz' : z ≠ 0 := by
    intro h
    exact hz (by simp [h])
  let W (i j : ι) := z * D / (L i * L j)
  have hW (i j : ι) : W i j ≠ 0 := div_ne_zero (mul_ne_zero hz' hdet) (mul_ne_zero (hL i) (hL j))
  have hWre (i j : ι) (hij : i ≠ j) : (W i j).re = 0 := by
    have hdiff : B i - B j = D * conj (A i - A j) / (d i * d j) := by
      rw [hB i, hB j]
      change (r * conj (A i) + s) / d i - (r * conj (A j) + s) / d j = _
      dsimp only [D, d]
      simp only [map_sub]
      field_simp [hden i, hden j]
      ring
    have heq : z * ((A i - A j) * (B i - B j) / ((A i - B i) * (A j - B j))) =
        (Complex.normSq (A i - A j) : ℂ) * W i j := by
      rw [hdiff]
      dsimp only [W, L]
      rw [← Complex.mul_conj]
      field_simp [hAB i, hAB j, hden i, hden j]
      ring
    have h := hgap i j hij
    rw [heq, Complex.re_ofReal_mul] at h
    exact (mul_eq_zero.mp h).resolve_left (Complex.normSq_pos.mpr (sub_ne_zero.mpr (hA.ne hij))).ne'
  have hLratio (i j : ι) : (L i / L j).im = 0 := by
    by_cases hij : i = j
    · subst j
      simp [hL i]
    · obtain ⟨k, hki, hkj⟩ := hthird i j hij
      have heq : L i / L j = W j k / W i k := by
        dsimp only [W]
        rw [div_div_div_comm, div_self (mul_ne_zero hz' hdet), one_div, inv_div,
          mul_div_mul_right _ _ (hL k)]
      rw [heq, Complex.div_im, hWre j k hkj.symm, hWre i k hki.symm]
      simp
  let i₀ : ι := Classical.choice inferInstance
  let lam := L i₀
  have hlam : lam ≠ 0 := hL i₀
  let rr := r / lam
  let ss := s / lam
  let uu := u / lam
  let vv := v / lam
  have hscaled (i : ι) :
      uu * (Complex.normSq (A i) : ℂ) + vv * A i - rr * conj (A i) - ss = L i / lam := by
    rw [hLform]
    dsimp only [rr, ss, uu, vv]
    field_simp [hlam]
  rcases real_affine_norm_form_forces_circle_or_coefficients A rr ss uu vv
    (fun i => (congrArg Complex.im (hscaled i)).trans (hLratio i i₀)) with h | ⟨hui, hsi, hri, hrr⟩
  · exact h
  have h : (rr * vv - ss * uu).im = 0 := by
    simp [Complex.sub_im, Complex.mul_im, hui, hsi, hri, hrr, mul_comm]
  exfalso
  obtain ⟨i, j, hij⟩ := hpair
  have hscaledDet : rr * vv - ss * uu = D / (lam * lam) := by
    dsimp only [rr, ss, uu, vv, D]
    field_simp [hlam]
  let R := (rr * vv - ss * uu) / ((L i / lam) * (L j / lam))
  have hRim : R.im = 0 := by
    dsimp only [R]
    rw [Complex.div_im, h, Complex.mul_im, hLratio i i₀, hLratio j i₀]
    simp
  have hRne : R ≠ 0 := by
    dsimp only [R]
    rw [hscaledDet]
    exact div_ne_zero (div_ne_zero hdet (mul_ne_zero hlam hlam))
      (mul_ne_zero (div_ne_zero (hL i) hlam) (div_ne_zero (hL j) hlam))
  have hRre : R.re ≠ 0 := fun hr => hRne (Complex.ext (by simpa using hr) (by simpa using hRim))
  have heq : W i j = z * R := by
    dsimp only [W, R]
    rw [hscaledDet]
    field_simp [hlam, hL i, hL j]
  have hw := hWre i j hij
  rw [heq, Complex.mul_re, hRim, mul_zero, sub_zero] at hw
  exact hz ((mul_eq_zero.mp hw).resolve_right hRre)


/-- A real product and a real complementary product force two complex
cross ratios to be both real or complex conjugate. -/
theorem both_real_or_conj_of_real_products (x y : ℂ)
    (hxy : (x * y).im = 0) (hc : ((1 - x) * (1 - y)).im = 0) :
    (x.im = 0 ∧ y.im = 0) ∨ y = conj x := by
  have hs : y.im = -x.im := by
    simp only [Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.one_re,
      Complex.one_im] at hc hxy
    linear_combination hxy - hc
  by_cases hx : x.im = 0
  · exact Or.inl ⟨hx, by simp [hs, hx]⟩
  · right
    apply Complex.ext
    · simp only [Complex.mul_im, hs] at hxy
      have h : (y.re - x.re) * x.im = 0 := by linear_combination hxy
      exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hx)
    · simpa using hs

/-- The imaginary part of an anchored fractional coordinate gives a
generalized-circle equation after multiplication by the squared norm of
its denominator. Here the cleared equation also applies at the pole. -/
theorem spectrumOnGeneralizedCircle_of_cleared_anchor_reality
    {ι : Type*} [Nonempty ι] (A : ι → ℂ) (p r k : ℂ)
    (hpr : p ≠ r) (hk : k ≠ 0)
    (h : ∀ i, (k * (A i - p) * conj (A i - r)).im = 0) :
    SpectrumOnGeneralizedCircle A := by
  have hh (i : ι) :
      (k * (Complex.normSq (A i) : ℂ) + (-k * conj r) * A i -
        (k * p) * conj (A i) - (-k * p * conj r)).im = 0 := by
    have he : k * (Complex.normSq (A i) : ℂ) + (-k * conj r) * A i -
        (k * p) * conj (A i) - (-k * p * conj r) =
        k * (A i - p) * conj (A i - r) := by
      rw [← Complex.mul_conj, map_sub]
      ring
    rw [he]
    exact h i
  rcases real_affine_norm_form_forces_circle_or_coefficients A (k * p) (-k * p * conj r)
      k (-k * conj r) hh with h | ⟨hki, _, hrim, hrre⟩
  · exact h
  · exfalso
    apply hpr
    apply mul_left_cancel₀ hk
    apply Complex.ext
    · simp [Complex.mul_re, hki] at hrre ⊢
      exact hrre
    · simp [Complex.mul_im, hki, mul_comm] at hrim ⊢
      exact hrim

/-- Two cleared anchored coordinates matched by conjugation reconstruct
a single anti-Möbius correspondence, also at their pole labels. -/
theorem exists_antiMobius_of_cleared_anchor_correspondence
    {ι : Type*} (A B : ι → ℂ) (pA rA kA pB rB kB : ℂ)
    (hA : pA ≠ rA) (hB : pB ≠ rB) (hkA : kA ≠ 0) (hkB : kB ≠ 0)
    (h : ∀ i, kB * (B i - pB) * (conj (A i) - conj rA) =
      conj kA * (conj (A i) - conj pA) * (B i - rB)) :
    ∃ r s u v : ℂ, r * v - s * u ≠ 0 ∧ (∀ i, u * conj (A i) + v ≠ 0) ∧
      ∀ i, B i = (r * conj (A i) + s) / (u * conj (A i) + v) := by
  let r := kB * pB - conj kA * rB
  let s := -(kB * pB * conj rA) + conj kA * rB * conj pA
  let u := kB - conj kA
  let v := -(kB * conj rA) + conj kA * conj pA
  have hdet : r * v - s * u ≠ 0 := by
    have he : r * v - s * u = kB * conj kA * (pB - rB) * (conj pA - conj rA) := by
      dsimp only [r, s, u, v]
      ring
    rw [he]
    have hk : conj kA ≠ 0 := (map_ne_zero (starRingEnd ℂ)).mpr hkA
    have ha : conj pA - conj rA ≠ 0 := by
      rw [← map_sub]
      exact (map_ne_zero (starRingEnd ℂ)).mpr (sub_ne_zero.mpr hA)
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hkB hk) (sub_ne_zero.mpr hB)) ha
  have he (i : ι) : B i * (u * conj (A i) + v) = r * conj (A i) + s := by
    dsimp only [r, s, u, v]
    linear_combination h i
  have hdn (i : ι) : u * conj (A i) + v ≠ 0 := by
    intro hzero
    have hn : r * conj (A i) + s = 0 := by
      rw [← he i, hzero, mul_zero]
    apply hdet
    linear_combination r * hzero - u * hn
  exact ⟨r, s, u, v, hdet, hdn, fun i => (eq_div_iff (hdn i)).mpr (he i)⟩


private noncomputable def anchorCR {ι : Type*} (A : ι → ℂ) (i j k l : ι) : ℂ :=
  ((A i - A j) * (A k - A l)) / ((A i - A k) * (A j - A l))

private theorem anchorCR_compl {ι : Type*} (A : ι → ℂ)
    (i j k l : ι) (h₁ : A i ≠ A k) (h₂ : A j ≠ A l) :
    1 - anchorCR A i j k l = anchorCR A i l k j := by
  have h : A l ≠ A j := h₂.symm
  unfold anchorCR
  field_simp [sub_ne_zero.mpr h₁, sub_ne_zero.mpr h₂, sub_ne_zero.mpr h]
  ring

private theorem anchorCR_product_reality_of_contacts {ι : Type*}
    (A B : ι → ℂ) (z : ℂ) (hz : z ≠ 0)
    (hq : ∀ i, A i - B i ≠ 0)
    (i j k l : ι) (hij : i ≠ j) (hkl : k ≠ l) (hik : i ≠ k) (hjl : j ≠ l)
    (hgap : ∀ i j, i ≠ j →
      (z * ((A i - A j) * (B i - B j) / ((A i - B i) * (A j - B j)))).re = 0) :
    (anchorCR A i j k l * anchorCR B i j k l).im = 0 := by
  let C (i : ι) := A i - B i
  let D (i j : ι) := (A i - A j) * (B i - B j)
  let G (i j : ι) := z * (D i j / (C i * C j))
  let S := z ^ 2 / ((C i * C j) * (C k * C l))
  have hS : S ≠ 0 := div_ne_zero (pow_ne_zero _ hz)
    (mul_ne_zero (mul_ne_zero (hq i) (hq j)) (mul_ne_zero (hq k) (hq l)))
  have hprod (u v x y : ι) (h : (C u * C v) * (C x * C y) = (C i * C j) * (C k * C l)) :
      G u v * G x y = S * (D u v * D x y) := by
    unfold G
    rw [mul_mul_mul_comm, div_mul_div_comm, h]
    dsimp only [S]
    simp only [div_eq_mul_inv]
    ring
  have hr : (G i j * G k l / (G i k * G j l)).im = 0 := by
    have hre (u v : ι) (hne : u ≠ v) : (G u v).re = 0 := hgap u v hne
    simp only [Complex.div_im, Complex.mul_im, hre i j hij, hre k l hkl, hre i k hik,
      hre j l hjl, zero_mul, mul_zero, add_zero, sub_zero, zero_sub, neg_zero, zero_div]
  rw [hprod i j k l rfl, hprod i k j l (by ring), mul_div_mul_left _ _ hS] at hr
  have heq : anchorCR A i j k l * anchorCR B i j k l = D i j * D k l / (D i k * D j l) := by
    unfold anchorCR D
    rw [div_mul_div_comm]
    congr 1 <;> ring
  rw [heq]
  exact hr

private theorem anchorCR_eq_scaled {ι : Type*} (A : ι → ℂ) (i j k l : ι) :
    anchorCR A i j k l =
      ((A i - A j) / (A i - A k)) * (A l - A k) / (A l - A j) := by
  unfold anchorCR
  rw [div_mul_eq_mul_div, div_div, show A l - A k = -(A k - A l) by ring,
    show A l - A j = -(A j - A l) by ring, mul_neg, mul_neg, neg_div_neg_eq]

private theorem anchor_real_implies_circle (A : Fin 4 → ℂ) (hA : Function.Injective A)
    (hCR : (anchorCR A 0 1 2 3).im = 0) : SpectrumOnGeneralizedCircle A := by
  let K := (A 0 - A 1) / (A 0 - A 2)
  have h01 : A 0 - A 1 ≠ 0 := sub_ne_zero.mpr (hA.ne (by decide))
  have h02 : A 0 - A 2 ≠ 0 := sub_ne_zero.mpr (hA.ne (by decide))
  have h31 : A 3 - A 1 ≠ 0 := sub_ne_zero.mpr (hA.ne (by decide))
  have hK : K ≠ 0 := div_ne_zero h01 h02
  apply spectrumOnGeneralizedCircle_of_cleared_anchor_reality A (A 2) (A 1) K
    (hA.ne (by decide)) hK
  intro i
  fin_cases i
  · have he : K * (A 0 - A 2) = A 0 - A 1 := div_mul_cancel₀ _ h02
    change (K * (A 0 - A 2) * conj (A 0 - A 1)).im = 0
    rw [he, Complex.mul_conj, Complex.ofReal_im]
  · simp
  · simp
  · rw [anchorCR_eq_scaled] at hCR
    change (K * (A 3 - A 2) / (A 3 - A 1)).im = 0 at hCR
    have he : K * (A 3 - A 2) * conj (A 3 - A 1) =
        (Complex.normSq (A 3 - A 1) : ℂ) * (K * (A 3 - A 2) / (A 3 - A 1)) := by
      rw [← Complex.mul_conj]
      field_simp [h31]
      ring
    change (K * (A 3 - A 2) * conj (A 3 - A 1)).im = 0
    rw [he, Complex.im_ofReal_mul, hCR, mul_zero]

private theorem exists_antiMobius_of_anchorCR_conj (A B : Fin 4 → ℂ)
    (hA : Function.Injective A) (hB : Function.Injective B)
    (hCR : anchorCR B 0 1 2 3 = conj (anchorCR A 0 1 2 3)) :
    ∃ r s u v : ℂ, r * v - s * u ≠ 0 ∧ (∀ i, u * conj (A i) + v ≠ 0) ∧
      ∀ i, B i = (r * conj (A i) + s) / (u * conj (A i) + v) := by
  let KA := (A 0 - A 1) / (A 0 - A 2)
  let KB := (B 0 - B 1) / (B 0 - B 2)
  have hA02 : A 0 - A 2 ≠ 0 := sub_ne_zero.mpr (hA.ne (by decide))
  have hB02 : B 0 - B 2 ≠ 0 := sub_ne_zero.mpr (hB.ne (by decide))
  have hA31 : A 3 - A 1 ≠ 0 := sub_ne_zero.mpr (hA.ne (by decide))
  have hA31' : conj (A 3) - conj (A 1) ≠ 0 := by
    rw [← map_sub]
    exact (map_ne_zero (starRingEnd ℂ)).mpr hA31
  have hB31 : B 3 - B 1 ≠ 0 := sub_ne_zero.mpr (hB.ne (by decide))
  apply exists_antiMobius_of_cleared_anchor_correspondence A B (A 2) (A 1) KA (B 2) (B 1) KB
    (hA.ne (by decide)) (hB.ne (by decide))
    (div_ne_zero (sub_ne_zero.mpr (hA.ne (by decide))) hA02)
    (div_ne_zero (sub_ne_zero.mpr (hB.ne (by decide))) hB02)
  intro i
  fin_cases i
  · have heA : conj KA * (conj (A 0) - conj (A 2)) = conj (A 0) - conj (A 1) := by
      rw [← map_sub, ← map_mul, div_mul_cancel₀ _ hA02, map_sub]
    have heB : KB * (B 0 - B 2) = B 0 - B 1 := div_mul_cancel₀ _ hB02
    change KB * (B 0 - B 2) * (conj (A 0) - conj (A 1)) =
      conj KA * (conj (A 0) - conj (A 2)) * (B 0 - B 1)
    rw [heA, heB, mul_comm]
  · simp
  · simp
  · have he : KB * (B 3 - B 2) / (B 3 - B 1) =
        conj (KA * (A 3 - A 2) / (A 3 - A 1)) := by
      simpa only [anchorCR_eq_scaled] using hCR
    rw [map_div₀, map_mul, map_sub, map_sub] at he
    exact (div_eq_div_iff hB31 hA31').mp he

/-- Four simple spectral labels with all six exchange deficits purely
imaginary at a nonzero support height lie on separate generalized
circles. This is a local clique theorem; it does not count contacts. -/
theorem generalizedCircles_of_four_swap_contacts (A B : Fin 4 → ℂ) (z : ℂ)
    (hA : Function.Injective A) (hB : Function.Injective B)
    (hq : ∀ i, A i - B i ≠ 0) (hz : z.re ≠ 0)
    (hgap : ∀ i j, i ≠ j →
      (z * ((A i - A j) * (B i - B j) / ((A i - B i) * (A j - B j)))).re = 0) :
    SpectrumOnGeneralizedCircle A ∧ SpectrumOnGeneralizedCircle B := by
  have hzz : z ≠ 0 := fun he => hz (by simp [he])
  have h (A' B' : Fin 4 → ℂ) (hA' : Function.Injective A') (hB' : Function.Injective B')
      (hq' : ∀ i, A' i - B' i ≠ 0)
      (hgap' : ∀ i j, i ≠ j →
        (z * ((A' i - A' j) * (B' i - B' j) / ((A' i - B' i) * (A' j - B' j)))).re = 0) :
      SpectrumOnGeneralizedCircle A' := by
    let x := anchorCR A' 0 1 2 3
    let y := anchorCR B' 0 1 2 3
    have hx : (x * y).im = 0 := anchorCR_product_reality_of_contacts A' B' z hzz hq'
      0 1 2 3 (by decide) (by decide) (by decide) (by decide) hgap'
    have hy : ((1 - x) * (1 - y)).im = 0 := by
      dsimp only [x, y]
      rw [anchorCR_compl _ _ _ _ _ (hA'.ne (by decide)) (hA'.ne (by decide)),
        anchorCR_compl _ _ _ _ _ (hB'.ne (by decide)) (hB'.ne (by decide))]
      exact anchorCR_product_reality_of_contacts A' B' z hzz hq'
        0 3 2 1 (by decide) (by decide) (by decide) (by decide) hgap'
    rcases both_real_or_conj_of_real_products x y hx hy with ⟨hr, _⟩ | hc
    · exact anchor_real_implies_circle A' hA' hr
    · obtain ⟨r, s, u, v, hdet, hden, hB''⟩ := exists_antiMobius_of_anchorCR_conj A' B' hA' hB' hc
      apply generalizedCircle_of_antiMobius_swap_contacts A' B' r s u v z hA' _
        ⟨0,1,by decide⟩ hden hq' hB'' hdet hz hgap'
      intro i j hij
      let S : Finset (Fin 4) := Finset.univ.erase i |>.erase j
      have hj : j ∈ (Finset.univ : Finset (Fin 4)).erase i :=
        Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ _⟩
      have hS : S.card = 2 := by
        dsimp only [S]
        rw [Finset.card_erase_of_mem hj, Finset.card_erase_of_mem (Finset.mem_univ i),
          Finset.card_univ, Fintype.card_fin]
      obtain ⟨k, hk⟩ := Finset.card_pos.mp (by rw [hS]; decide : 0 < S.card)
      exact ⟨k, (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1, (Finset.mem_erase.mp hk).1⟩
  refine ⟨h A B hA hB hq hgap, h B A hB hA (fun i => sub_ne_zero.mpr (sub_ne_zero.mp (hq i)).symm) ?_⟩
  intro i j hij
  rw [show B i - A i = -(A i - B i) by ring,
    show B j - A j = -(A j - B j) by ring, neg_mul_neg,
    mul_comm (B i - B j) (A i - A j)]
  exact hgap i j hij


/-- An active four-clique of transpositions gives two circular spectral
quartets. The pivot may be any permutation and no other products need
be nonzero or distinct. -/
theorem matchingProduct_generalizedCircles_of_four_swap_contacts
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℂ) (r : Equiv.Perm ι) (η : ℂ) (e : Fin 4 ↪ ι)
    (ha : Function.Injective a) (hb : Function.Injective b)
    (hz : (η * matchingProduct a b r).re ≠ 0)
    (ht : ∀ i j : Fin 4, i ≠ j →
      (η * matchingProduct a b (r * Equiv.swap (e i) (e j))).re =
        (η * matchingProduct a b r).re) :
    SpectrumOnGeneralizedCircle (fun i => a (r (e i))) ∧
      SpectrumOnGeneralizedCircle (fun i => -b (e i)) := by
  let A (i : Fin 4) := a (r (e i))
  let B (i : Fin 4) := -b (e i)
  let z := η * matchingProduct a b r
  have hnon : matchingProduct a b r ≠ 0 := fun he => hz (by simp [he])
  have hqa (i : Fin 4) : A i - B i ≠ 0 := by
    simpa [A, B, sub_neg_eq_add] using
      (Finset.prod_ne_zero_iff.mp hnon (e i) (Finset.mem_univ (e i)))
  apply generalizedCircles_of_four_swap_contacts A B z
    (ha.comp (r.injective.comp e.injective))
    (neg_injective.comp (hb.comp e.injective)) hqa hz
  intro i j hij
  have hgap : (η * (matchingProduct a b r -
      matchingProduct a b (r * Equiv.swap (e i) (e j)))).re = 0 := by
    rw [mul_sub, Complex.sub_re, ht i j hij, sub_self]
  rw [matchingProduct_right_swap_gap_ratio a b r hnon (e i) (e j) (e.injective.ne hij)] at hgap
  simp only [A, B, sub_neg_eq_add, z, mul_assoc]
  convert hgap using 2; ring

/-- In order four, the full swap clique at nonzero height is settled for
every unitary by the independent two-spectral-circles theorem. -/
theorem holds_of_fin_four_swap_clique
    (a b : Fin 4 → ℂ) (r : Equiv.Perm (Fin 4)) (η : ℂ)
    (ha : Function.Injective a) (hb : Function.Injective b)
    (hz : (η * matchingProduct a b r).re ≠ 0)
    (ht : ∀ i j : Fin 4, i ≠ j →
      (η * matchingProduct a b (r * Equiv.swap i j)).re =
        (η * matchingProduct a b r).re)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) : Holds a b U := by
  obtain ⟨hA, hB⟩ := matchingProduct_generalizedCircles_of_four_swap_contacts a b r η
    (Function.Embedding.refl (Fin 4)) ha hb hz ht
  apply holds_of_generalized_circular_spectra a b _ hB U hU
  simpa using hA.comp r.symm

end MOC
