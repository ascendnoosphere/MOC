import MOC.MobiusMomentWitness
import MOC.Hermitian

/-! Geometric rigidity from the centered Möbius fourth-moment bound.
The deficit in the signed spectra's quadratic moment controls the
variation of their radii and their distance to an antipodal pair. -/

open BigOperators
open Matrix
open scoped ComplexConjugate

namespace MOC

noncomputable section

variable {J : Type*} [Fintype J]

/-- Vanishing squared-norm-weighted mean prevents any one entry from
carrying more than half the unit energy. -/
theorem normSq_le_half_of_cubic_balance (x : J → ℂ)
    (henergy : ∑ j, Complex.normSq (x j) = 1)
    (hcubic : ∑ j, (Complex.normSq (x j) : ℂ) * x j = 0) (i : J) :
    Complex.normSq (x i) ≤ 1 / 2 := by
  classical
  by_contra! hbig
  let S : Finset J := Finset.univ.erase i
  let w (j : J) := Complex.normSq (x j)
  let c (j : J) := (w j : ℂ) * x j
  have hw (j : J) : 0 ≤ w j := Complex.normSq_nonneg _
  have hweight : ∑ j ∈ S, w j = 1 - w i := by
    have he := Finset.sum_erase_add Finset.univ w (Finset.mem_univ i)
    change (∑ j ∈ S, w j) + w i = ∑ j, w j at he
    rw [henergy] at he
    linarith
  have hcenter : c i = -(∑ j ∈ S, c j) := by
    have he := Finset.sum_erase_add Finset.univ c (Finset.mem_univ i)
    change (∑ j ∈ S, c j) + c i = ∑ j, c j at he
    rw [hcubic] at he
    linear_combination he
  have hle (j : J) (hj : j ∈ S) : ‖x j‖ ≤ ‖x i‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    have h := Finset.single_le_sum (fun k (_ : k ∈ S) => hw k) hj
    rw [hweight] at h
    change 1 / 2 < w i at hbig
    change w j ≤ w i
    linarith only [h, hbig]
  have hn (j : J) : ‖c j‖ = w j * ‖x j‖ := by
    rw [show c j = (w j : ℂ) * x j from rfl, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (hw j)]
  have hb : w i * ‖x i‖ ≤ (1 - w i) * ‖x i‖ := calc
    _ = ‖c i‖ := (hn i).symm
    _ = ‖∑ j ∈ S, c j‖ := by rw [hcenter, norm_neg]
    _ ≤ ∑ j ∈ S, ‖c j‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ S, w j * ‖x i‖ :=
      Finset.sum_le_sum fun j hj => by
        rw [hn]
        exact mul_le_mul_of_nonneg_left (hle j hj) (hw j)
    _ = _ := by rw [← Finset.sum_mul, hweight]
  have hpos : 0 < ‖x i‖ :=
    norm_pos_iff.mpr (Complex.normSq_pos.mp (by linarith only [hbig]))
  have hi := le_of_mul_le_mul_right hb hpos
  change 1 / 2 < w i at hbig
  linarith only [hbig, hi]

private theorem exists_unit_quadratic_rotation (z : ℂ) :
    ∃ p : ℂ, Complex.normSq p = 1 ∧ p ^ 2 * z = (‖z‖ : ℂ) := by
  by_cases hz : z = 0
  · exact ⟨1, by simp, by simp [hz]⟩
  have hpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  obtain ⟨p, hp⟩ := IsAlgClosed.exists_pow_nat_eq (conj z / (‖z‖ : ℂ)) (n := 2) two_pos
  have hp' := congrArg Complex.normSq hp
  rw [map_pow, map_div₀, Complex.normSq_conj, Complex.normSq_ofReal,
    Complex.normSq_eq_norm_sq z, ← sq, div_self (pow_ne_zero _ hpos.ne')] at hp'
  have hn : Complex.normSq p = 1 := (sq_eq_sq₀ (Complex.normSq_nonneg _) zero_le_one).mp
    (by rwa [one_pow])
  refine ⟨p, hn, ?_⟩
  rw [hp, div_mul_eq_mul_div, mul_comm (conj z) z, Complex.mul_conj,
    Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  field_simp [Complex.ofReal_ne_zero.mpr hpos.ne']
  ring

private theorem sum_normSq_sub_re_sq (y : J → ℂ) :
    (∑ j, Complex.normSq (y j)) - (∑ j, y j ^ 2).re =
      2 * ∑ j, (y j).im ^ 2 := by
  rw [Complex.re_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by
    rw [pow_two (y j), Complex.mul_re, Complex.normSq_apply]
    ring

private theorem sum_radial_defect (y : J → ℂ) (M : ℝ)
    (hM : ∀ j, Complex.normSq (y j) ≤ M) :
    (∑ j, Complex.normSq (y j) ^ 2) -
      (∑ j, (Complex.normSq (y j) : ℂ) * y j ^ 2).re ≤
      M * ((∑ j, Complex.normSq (y j)) - (∑ j, y j ^ 2).re) := by
  rw [Complex.re_sum, Complex.re_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  rw [Complex.re_ofReal_mul, pow_two (Complex.normSq (y j)), ← mul_sub]
  apply mul_le_mul_of_nonneg_right (hM j)
  rw [pow_two (y j), Complex.mul_re, Complex.normSq_apply]
  nlinarith only [sq_nonneg (y j).im]

/-- The fourth-moment bound controls radial variance through the angular
deficit `1 - ‖∑ x_j²‖`. The sharper coefficient uses any admissible cap
`M` on the individual squared magnitudes. -/
theorem fourth_moment_radial_variance (n : ℕ) (hn : 0 < n) (x : J → ℂ)
    (henergy : ∑ j, Complex.normSq (x j) = 1) (M : ℝ)
    (hM : ∀ j, Complex.normSq (x j) ≤ M)
    (hmoment :
      ‖(2 * (n : ℂ)) * (∑ j, (Complex.normSq (x j) : ℂ) * x j ^ 2) - ∑ j, x j ^ 2‖ ≤
        (n : ℝ) * (∑ j, Complex.normSq (x j) ^ 2) - Complex.normSq (∑ j, x j ^ 2) / 2) :
    let d := 1 - ‖∑ j, x j ^ 2‖
    (∑ j, Complex.normSq (x j) ^ 2) - 1 / (2 * (n : ℝ)) ≤
      2 * M * d - d ^ 2 / (2 * (n : ℝ)) := by
  intro d
  let m : ℂ := ∑ j, x j ^ 2
  let k : ℂ := ∑ j, (Complex.normSq (x j) : ℂ) * x j ^ 2
  let q : ℝ := ∑ j, Complex.normSq (x j) ^ 2
  obtain ⟨p, hp, hpm⟩ := exists_unit_quadratic_rotation m
  let y (j : J) := p * x j
  have hy (j : J) : Complex.normSq (y j) = Complex.normSq (x j) := by
    rw [show y j = p * x j from rfl, Complex.normSq_mul, hp, one_mul]
  have hmy : ∑ j, y j ^ 2 = p ^ 2 * m := by
    simp only [y, mul_pow, m, Finset.mul_sum]
  have hky : ∑ j, (Complex.normSq (y j) : ℂ) * y j ^ 2 = p ^ 2 * k := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [hy, show y j = p * x j from rfl, mul_pow]; ring
  have hdef := sum_radial_defect y M (fun j => hy j ▸ hM j)
  rw [hky, hmy, hpm, Complex.ofReal_re] at hdef
  have hrot := Complex.re_le_norm (p ^ 2 * ((2 * (n : ℂ)) * k - m))
  have hpn : ‖p‖ = 1 := (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
    (by simpa only [← Complex.normSq_eq_norm_sq, one_pow] using hp)
  have hleft :
      (p ^ 2 * ((2 * (n : ℂ)) * k - m)).re =
        (2 * (n : ℝ)) * (p ^ 2 * k).re - ‖m‖ := by
    rw [mul_sub, Complex.sub_re, hpm, Complex.ofReal_re]
    rw [show p ^ 2 * (2 * (n : ℂ) * k) = ((2 * (n : ℝ) : ℝ) : ℂ) * (p ^ 2 * k) by
      push_cast; ring, Complex.re_ofReal_mul]
  rw [hleft, norm_mul, norm_pow, hpn, one_pow, one_mul] at hrot
  have hh := hrot.trans hmoment
  rw [Complex.normSq_eq_norm_sq] at hh
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hb : q - (p ^ 2 * k).re ≤ M * d := by
    simpa only [hy, henergy, q, d] using hdef
  change q - 1 / (2 * (n : ℝ)) ≤ _
  apply (mul_le_mul_left hnR).mp
  have hprod := mul_le_mul_of_nonneg_left hb (show 0 ≤ 2 * (n : ℝ) by positivity)
  change (2 * (n : ℝ)) * (p ^ 2 * k).re - ‖m‖ ≤ (n : ℝ) * q - ‖m‖ ^ 2 / 2 at hh
  have hcancel₁ : (n : ℝ) * (1 / (2 * (n : ℝ))) = 1 / 2 := by
    field_simp [hnR.ne']
    ring
  have hcancel₂ : (n : ℝ) * (d ^ 2 / (2 * (n : ℝ))) = d ^ 2 / 2 := by
    field_simp [hnR.ne']
    ring
  rw [mul_sub, mul_sub, hcancel₁, hcancel₂]
  dsimp only [d] at *
  nlinarith only [hprod, hh]


private theorem normSq_sub_signed_radius_le (z : ℂ) (r : ℝ) (hr : 0 < r) :
    let s := if 0 ≤ z.re then r else -r
    Complex.normSq (z - (s : ℂ)) ≤
      2 * ((Complex.normSq z - r ^ 2) ^ 2 / r ^ 2) + 3 * z.im ^ 2 := by
  intro s
  let c : ℝ := ‖z‖
  let u : ℝ := |z.re|
  have huc : u ≤ c := Complex.abs_re_le_norm z
  have hu : 0 ≤ u := abs_nonneg _
  have hc : 0 ≤ c := norm_nonneg _
  have hwi : c ^ 2 = u ^ 2 + z.im ^ 2 := by
    rw [show c ^ 2 = Complex.normSq z from (Complex.normSq_eq_norm_sq _).symm,
      show u ^ 2 = z.re ^ 2 from sq_abs _, Complex.normSq_apply]
    ring
  have hs :
      Complex.normSq (z - (s : ℂ)) = c ^ 2 + r ^ 2 - 2 * r * u := by
    dsimp only [s]
    by_cases h : 0 ≤ z.re
    · rw [if_pos h]
      simp only [u, abs_of_nonneg h, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
        Complex.ofReal_re, Complex.ofReal_im, sub_zero] at hwi ⊢
      nlinarith only [hwi]
    · rw [if_neg h]
      simp only [u, abs_of_neg (lt_of_not_ge h), Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
        Complex.ofReal_re, Complex.ofReal_im, sub_zero] at hwi ⊢
      nlinarith only [hwi]
  have hcross : 2 * r * (c - u) ≤ 2 * c * (c - u) + (r - c) ^ 2 + (c - u) ^ 2 := by
    nlinarith only [sq_nonneg ((r - c) - (c - u))]
  have hang : 2 * c * (c - u) + (c - u) ^ 2 ≤ 3 * z.im ^ 2 := by
    nlinarith only [hwi, mul_nonneg hu (sub_nonneg.mpr huc)]
  have hrle : (c - r) ^ 2 ≤ (c ^ 2 - r ^ 2) ^ 2 / r ^ 2 := by
    apply (le_div_iff₀ (pow_pos hr _)).mpr
    have hm := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hr.le (show r ≤ c + r by linarith only [hc]) 2)
      (sq_nonneg (c - r))
    have he : (c - r) ^ 2 * (c + r) ^ 2 = (c ^ 2 - r ^ 2) ^ 2 := by ring
    rwa [he] at hm
  rw [hs, show Complex.normSq z = c ^ 2 from Complex.normSq_eq_norm_sq _]
  linarith only [hcross, hang, hrle, show c ^ 2 + r ^ 2 - 2 * r * u =
    (c - r) ^ 2 + 2 * r * (c - u) by ring,
    show (r - c) ^ 2 = (c - r) ^ 2 by ring]

private theorem norm_sum_sq_le_unit (x : J → ℂ)
    (henergy : ∑ j, Complex.normSq (x j) = 1) :
    ‖∑ j, x j ^ 2‖ ≤ 1 := calc
  _ ≤ ∑ j, ‖x j ^ 2‖ := norm_sum_le _ _
  _ = 1 := by simpa only [norm_pow, ← Complex.normSq_eq_norm_sq] using henergy

/-- A unit-energy signed spectrum satisfying the balanced fourth-moment
bound is within a quantitative squared distance of an antipodal pair.
The direction is chosen by its quadratic moment, not by a fitted line. -/
theorem exists_antipodal_approximation_of_fourth_moment
    (n : ℕ) (hn : 0 < n) (hcard : Fintype.card J = 2 * n) (x : J → ℂ)
    (henergy : ∑ j, Complex.normSq (x j) = 1)
    (hcubic : ∑ j, (Complex.normSq (x j) : ℂ) * x j = 0)
    (hmoment :
      ‖(2 * (n : ℂ)) * (∑ j, (Complex.normSq (x j) : ℂ) * x j ^ 2) - ∑ j, x j ^ 2‖ ≤
        (n : ℝ) * (∑ j, Complex.normSq (x j) ^ 2) - Complex.normSq (∑ j, x j ^ 2) / 2) :
    let d := 1 - ‖∑ j, x j ^ 2‖
    let r := Real.sqrt (1 / (2 * (n : ℝ)))
    ∃ (p : ℂ) (s : J → ℝ), Complex.normSq p = 1 ∧
      (∀ j, s j = r ∨ s j = -r) ∧
      (∑ j, (p * x j).im ^ 2) = d / 2 ∧
      (∑ j, Complex.normSq (p * x j - (s j : ℂ))) ≤ (4 * (n : ℝ) + 3 / 2) * d - 2 * d ^ 2 := by
  intro d r
  let m : ℂ := ∑ j, x j ^ 2
  let q : ℝ := ∑ j, Complex.normSq (x j) ^ 2
  let N : ℝ := 2 * (n : ℝ)
  have hN : 0 < N := by dsimp [N]; positivity
  have hr : 0 < r := Real.sqrt_pos_of_pos (one_div_pos.mpr hN)
  have hr2 : r ^ 2 = 1 / N := Real.sq_sqrt (one_div_nonneg.mpr hN.le)
  obtain ⟨p, hp, hpm⟩ := exists_unit_quadratic_rotation m
  let y (j : J) := p * x j
  let s (j : J) := if 0 ≤ (y j).re then r else -r
  have hy (j : J) : Complex.normSq (y j) = Complex.normSq (x j) := by
    rw [show y j = p * x j from rfl, Complex.normSq_mul, hp, one_mul]
  have hmy : ∑ j, y j ^ 2 = (‖m‖ : ℂ) := by
    rw [← hpm]
    simp only [y, m, mul_pow, Finset.mul_sum]
  have him : ∑ j, (y j).im ^ 2 = d / 2 := by
    have he := sum_normSq_sub_re_sq y
    rw [hmy, Complex.ofReal_re] at he
    simp only [hy, henergy] at he
    change ∑ j, (y j).im ^ 2 = (1 - ‖m‖) / 2
    linarith only [he]
  have hvar := fourth_moment_radial_variance n hn x henergy (1 / 2)
    (normSq_le_half_of_cubic_balance x henergy hcubic) hmoment
  change q - 1 / N ≤ 2 * (1 / 2 : ℝ) * d - d ^ 2 / N at hvar
  have hsVar :
      ∑ j, (Complex.normSq (y j) - 1 / N) ^ 2 = q - 1 / N := by
    have hp' (v : ℝ) : (v - 1 / N) ^ 2 =
        v ^ 2 - (2 / N) * v + (1 / N) ^ 2 := by ring
    simp_rw [hy, hp']
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, henergy,
      Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
    push_cast
    change q - 2 / N * 1 + N * (1 / N) ^ 2 = q - 1 / N
    field_simp [hN.ne']
    ring
  have hpoint (j : J) : Complex.normSq (y j - (s j : ℂ)) ≤
      (2 * N) * (Complex.normSq (y j) - 1 / N) ^ 2 + 3 * (y j).im ^ 2 := by
    have he := normSq_sub_signed_radius_le (y j) r hr
    dsimp only at he
    rw [hr2] at he
    simpa only [div_div_eq_mul_div, div_one, ← mul_assoc, mul_comm _ N] using he
  refine ⟨p,s,hp,fun j => ?_,him,?_⟩
  · dsimp [s]; split <;> simp
  · have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hpoint j)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hsVar, him] at hsum
    have hm := mul_le_mul_of_nonneg_left hvar (show 0 ≤ 2 * N by positivity)
    have hcancel : (2 * N) * (2 * (1 / 2 : ℝ) * d - d ^ 2 / N) = 2 * N * d - 2 * d ^ 2 := by
      field_simp [hN.ne']
      ring
    rw [hcancel] at hm
    change ∑ j, Complex.normSq (y j - (s j : ℂ)) ≤ _
    dsimp only [N] at hm hsum
    linarith only [hsum, hm]


variable {ι : Type*} [Fintype ι]

private theorem signed_spectral_energy (a b : ι → ℂ) :
    ∑ j : ι ⊕ ι, Complex.normSq (Sum.elim a (fun i => -b i) j) = spectralEnergy a b := by
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Complex.normSq_neg,
    spectralEnergy]

/-- The antipodal approximation applies directly to the signed spectrum
at a rank-and-moment terminal optimizer. -/
theorem MobiusMomentBound.exists_antipodal_approximation [Nonempty ι] {a b : ι → ℂ}
    (hmoment : MobiusMomentBound a b) (hE : spectralEnergy a b = 1)
    (hC : (∑ i, (Complex.normSq (a i) : ℂ) * a i) =
      ∑ i, (Complex.normSq (b i) : ℂ) * b i) :
    let x : ι ⊕ ι → ℂ := Sum.elim a (fun i => -b i)
    let n := Fintype.card ι
    let d := 1 - ‖∑ j, x j ^ 2‖
    let r := Real.sqrt (1 / (2 * (n : ℝ)))
    ∃ (p : ℂ) (s : (ι ⊕ ι) → ℝ), Complex.normSq p = 1 ∧
      (∀ j, s j = r ∨ s j = -r) ∧
      (∑ j, (p * x j).im ^ 2) = d / 2 ∧
      (∑ j, Complex.normSq (p * x j - (s j : ℂ))) ≤ (4 * (n : ℝ) + 3 / 2) * d - 2 * d ^ 2 := by
  intro x n d r
  exact exists_antipodal_approximation_of_fourth_moment n Fintype.card_pos
    (by simp [n, Fintype.card_sum, two_mul]) x
    ((signed_spectral_energy a b).trans hE)
    (by simp [x, Fintype.sum_sum_type, Finset.sum_neg_distrib, hC]) hmoment

/-- A strict witness of unit energy has positive angular deficit. At zero
deficit its two spectra rotate to the real line, where inclusion holds.
The fourth-moment bound is not required for this endpoint exclusion. -/
theorem StrictMatchingSupport.angular_deficit_pos [DecidableEq ι]
    {U : Matrix ι ι ℂ} (hU : IsUnitary U) (w : StrictMatchingSupport U)
    (hE : spectralEnergy w.a w.b = 1) :
    let x : ι ⊕ ι → ℂ := Sum.elim w.a (fun i => -w.b i)
    0 < 1 - ‖∑ j, x j ^ 2‖ := by
  intro x
  let m : ℂ := ∑ j, x j ^ 2
  have hEx : ∑ j, Complex.normSq (x j) = 1 := (signed_spectral_energy w.a w.b).trans hE
  have hm : ‖m‖ ≤ 1 := norm_sum_sq_le_unit x hEx
  by_contra! hbad
  have hm1 : ‖m‖ = 1 := le_antisymm hm (by linarith only [hbad])
  obtain ⟨p, hp, hpm⟩ := exists_unit_quadratic_rotation m
  have hp₀ : p ≠ 0 := Complex.normSq_pos.mp (by rw [hp]; exact zero_lt_one)
  let y (j : ι ⊕ ι) := p * x j
  have hy (j : ι ⊕ ι) : Complex.normSq (y j) = Complex.normSq (x j) := by
    rw [show y j = p * x j from rfl, Complex.normSq_mul, hp, one_mul]
  have hmy : ∑ j, y j ^ 2 = (‖m‖ : ℂ) := by
    rw [← hpm]
    simp only [y, m, mul_pow, Finset.mul_sum]
  have him : (∑ j, (y j).im ^ 2) = 0 := by
    have he := sum_normSq_sub_re_sq y
    rw [hmy, Complex.ofReal_re, hm1] at he
    simp only [hy, hEx] at he
    linarith only [he]
  have him₀ (j : ι ⊕ ι) : (y j).im = 0 := by
    have hs := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg (y k).im)).mp him
    exact pow_eq_zero (hs j (Finset.mem_univ _))
  have ha : (fun i => ((p * w.a i).re : ℂ)) = fun i => p * w.a i := by
    funext i
    exact Complex.ext (by simp) (by simpa [y, x] using (him₀ (.inl i)).symm)
  have hb : (fun i => ((p * w.b i).re : ℂ)) = fun i => p * w.b i := by
    funext i
    have hb₀ : (p * w.b i).im = 0 := by
      simpa only [y, x, Sum.elim_inr, mul_neg, Complex.neg_im, neg_eq_zero] using him₀ (.inr i)
    exact Complex.ext (by simp) (by simp [hb₀])
  have hhold := holds_of_real_spectra (fun i => (p * w.a i).re)
    (fun i => (p * w.b i).re) U hU
  rw [ha, hb] at hhold
  have horig : Holds w.a w.b U :=
    (hull_common_factor_iff (pow_ne_zero _ hp₀) (determinantValue_scale w.a w.b U p)
      (matchingProduct_scale w.a w.b p)).mp hhold
  exact w.not_holds horig

end

end MOC
