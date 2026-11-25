import MOC.MatchingChartPolynomial
import MOC.HighContact
import MOC.SpectralPerturbation
import MOC.Support

/-! In order four, fixing the right coordinates of the anchored matching chart
makes the matching products linear in four complex coefficients. A single
complex quadratic equation restores the common spectral realization. -/

open BigOperators

namespace MOC

noncomputable section

/-- The four coefficients stand for the products of the common scale with
`1`, the two free left coordinates, and their product. -/
def fourBilinearMatchingProduct (y w : Fin 4 → ℂ) (σ : Equiv.Perm (Fin 4)) : ℂ :=
  let b := y (σ.symm 2)
  let c := y (σ.symm 3)
  (1 - y (σ.symm 1)) * (w 0 - b * w 1 - c * w 2 + b * c * w 3)

/-- The linear expression agrees with the product in the anchored chart. -/
theorem fourBilinearMatchingProduct_eq_anchored (y : Fin 4 → ℂ) (t u v : ℂ)
    (σ : Equiv.Perm (Fin 4)) :
    fourBilinearMatchingProduct y ![t, t * u, t * v, t * u * v] σ =
      anchoredMatchingCoordinate t ![0, 1, u, v] y σ := by
  let x : Fin 4 → ℂ := ![0, 1, u, v]
  let f (j : Fin 4) := 1 - x (σ j) * y j
  have hp : (∏ j, f j) = ∏ i, f (σ.symm i) :=
    (Equiv.prod_comp σ.symm f).symm
  unfold fourBilinearMatchingProduct
  change (1 - y (σ.symm 1)) *
      (t - y (σ.symm 2) * (t * u) - y (σ.symm 3) * (t * v) +
        y (σ.symm 2) * y (σ.symm 3) * (t * u * v)) = t * ∏ j, f j
  rw [hp]
  have h0 : x 0 = 0 := rfl
  have h1 : x 1 = 1 := rfl
  have h2 : x 2 = u := rfl
  have h3 : x 3 = v := rfl
  simp only [Fin.prod_univ_four, f, Equiv.apply_symm_apply, h0, h1, h2, h3,
    zero_mul, sub_zero, one_mul]
  ring

/-- A nonzero first coefficient and the vanishing two-by-two determinant
realize all matching coordinates with the same pair of spectra. -/
theorem exists_spectra_of_fourBilinearMatchingProduct (y w : Fin 4 → ℂ)
    (hw : w 0 ≠ 0) (h : w 0 * w 3 = w 1 * w 2) :
    ∃ a b : Fin 4 → ℂ, ∀ σ, matchingProduct a b σ = fourBilinearMatchingProduct y w σ := by
  let u := w 1 / w 0
  let v := w 2 / w 0
  have hu : w 0 * u = w 1 := by
    rw [mul_comm, show u = w 1 / w 0 from rfl, div_mul_cancel₀ _ hw]
  have hv : w 0 * v = w 2 := by
    rw [mul_comm, show v = w 2 / w 0 from rfl, div_mul_cancel₀ _ hw]
  have huv : w 0 * u * v = w 3 := by
    apply mul_left_cancel₀ hw
    calc
      w 0 * (w 0 * u * v) = (w 0 * u) * (w 0 * v) := by ring
      _ = w 0 * w 3 := by rw [hu, hv, h]
  obtain ⟨a, b, hp⟩ := exists_spectra_of_anchoredMatchingCoordinate
    (w 0) (![0, 1, u, v] : Fin 4 → ℂ) y
  have hw' : (![w 0, w 0 * u, w 0 * v, w 0 * u * v] : Fin 4 → ℂ) = w := by
    funext i
    fin_cases i
    · rfl
    · exact hu
    · exact hv
    · exact huv
  refine ⟨a, b, fun σ => ?_⟩
  rw [hp σ, ← fourBilinearMatchingProduct_eq_anchored, hw']

/-- Every regular input has such a common coefficient vector, including the
chosen support direction in its complex scale. -/
theorem exists_fourBilinearMatchingProduct_of_nonopposite (a b : Fin 4 → ℂ)
    (η : ℂ) (hη : η ≠ 0) (hnz : ∀ i j, a i + b j ≠ 0)
    (ha : a 1 ≠ a 0) (hb : b 1 ≠ b 0) :
    ∃ y w : Fin 4 → ℂ, y 0 = 0 ∧ w 0 ≠ 0 ∧ w 0 * w 3 = w 1 * w 2 ∧
      ∀ σ, fourBilinearMatchingProduct y w σ = η * matchingProduct a b σ := by
  obtain ⟨z, _, hn, hp⟩ := exists_matchingChartCoordinate_of_nonopposite
    (n := 2) a b hnz ha hb
  let c := z (.inl ())
  let u := z (.inr (.inl 0))
  let v := z (.inr (.inl 1))
  let y := matchingChartRight z
  let t := η * c
  have hc : c ≠ 0 := by
    intro hz
    apply hn 1
    change c * _ = 0
    rw [hz, zero_mul]
  have hx : matchingChartLeft z = (![0, 1, u, v] : Fin 4 → ℂ) := by
    funext i
    fin_cases i <;> rfl
  refine ⟨y, ![t, t * u, t * v, t * u * v], rfl, mul_ne_zero hη hc, ?_, ?_⟩
  · change t * (t * u * v) = (t * u) * (t * v)
    ring
  · intro σ
    rw [fourBilinearMatchingProduct_eq_anchored, hp σ]
    change t * (∏ j, (1 - (![0, 1, u, v] : Fin 4 → ℂ) (σ j) * y j)) =
      η * (c * ∏ j, (1 - matchingChartLeft z (σ j) * y j))
    rw [hx, ← mul_assoc]

/-- After the support direction enters the scale, every contact equation
and the signed support gap is linear in the real and imaginary parts of
the four coefficients. -/
theorem fourBilinearMatchingProduct_support_gap (a b y w : Fin 4 → ℂ) (η : ℂ)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U)
    (h : ∀ σ, fourBilinearMatchingProduct y w σ = η * matchingProduct a b σ)
    (r : Equiv.Perm (Fin 4)) :
    (fourBilinearMatchingProduct y w r).re - (η * determinantValue a b U).re =
      ∑ σ, realSignedWeight U σ *
        ((fourBilinearMatchingProduct y w r).re - (fourBilinearMatchingProduct y w σ).re) := by
  simpa only [h, matchingGap] using support_gap_eq a b U hU η r

/-- Nonnegativity of the signed gap on the bilinear chart is equivalent
to order four. The quadratic equation ensures a common realization. -/
theorem conjecture_four_iff_bilinear_support :
    Conjecture (Fin 4) ↔ ∀ (U : Matrix (Fin 4) (Fin 4) ℂ) (y w : Fin 4 → ℂ),
      IsUnitary U → y 0 = 0 → w 0 ≠ 0 → w 0 * w 3 = w 1 * w 2 →
      ∀ r : Equiv.Perm (Fin 4),
        (∀ σ, (fourBilinearMatchingProduct y w σ).re ≤ (fourBilinearMatchingProduct y w r).re) →
        0 ≤ ∑ σ, realSignedWeight U σ *
          ((fourBilinearMatchingProduct y w r).re - (fourBilinearMatchingProduct y w σ).re) := by
  classical
  constructor
  · intro h U y w hU _ hw hquad r hr
    obtain ⟨a, b, hp⟩ := exists_spectra_of_fourBilinearMatchingProduct y w hw hquad
    have hprod (σ : Equiv.Perm (Fin 4)) :
        fourBilinearMatchingProduct y w σ = 1 * matchingProduct a b σ := by
      rw [one_mul, hp σ]
    obtain ⟨σ, hσ⟩ := (holds_iff_directional a b U).mp (h a b U hU) 1
    rw [← fourBilinearMatchingProduct_support_gap a b y w 1 U hU hprod r]
    exact sub_nonneg.mpr (hσ.trans (by simpa only [hprod] using hr σ))
  · intro h
    apply conjecture_iff_regular_matching_products.mpr
    intro a b U hU hnz hinj
    apply (holds_iff_directional a b U).mpr
    intro η
    by_cases hη : η = 0
    · exact ⟨1, by simp only [hη, zero_mul, le_refl]⟩
    obtain ⟨ha, hb⟩ := injective_spectra_of_matchingProduct_injective hinj
    obtain ⟨y, w, hy, hw, hquad, hprod⟩ :=
      exists_fourBilinearMatchingProduct_of_nonopposite a b η hη hnz
        (ha.ne (by decide)) (hb.ne (by decide))
    obtain ⟨r, _, hr⟩ := Finset.exists_max_image Finset.univ
      (fun σ : Equiv.Perm (Fin 4) => (fourBilinearMatchingProduct y w σ).re)
      ⟨1, Finset.mem_univ _⟩
    have hgap := h U y w hU hy hw hquad r (fun σ => hr σ (Finset.mem_univ _))
    rw [← fourBilinearMatchingProduct_support_gap a b y w η U hU hprod r, hprod r] at hgap
    exact ⟨r, sub_nonneg.mp hgap⟩

end

end MOC
